"""Type inference and utility mixin for WasmContext."""

from __future__ import annotations

from typing import ClassVar, TypeVar

from vera import ast, naming
from vera.monomorphize import (
    resolve_fn_type_alias,
    substitute_type_vars,
)
from vera.slots import (
    family_fallback_name,
    type_expr_slot_name,
)
from vera.types import (
    NAT,
    AdtType,
    FunctionType,
    RefinedType,
    Type,
    base_type,
    erases_to_unit,
    value_type_name,
    value_width,
)
from vera.types import TypeVar as TypeVariable
from vera.wasm.helpers import _INLINE_I32_TYPES, _strip_future, state_type_arg

#: A node code generation builds after the check (:meth:`InferenceMixin._built`).
_N = TypeVar("_N", bound=ast.Node)

#: A built-in data type whose instances take any number of arguments: its
#: registered type-parameter count is not an arity (`Tuple<Int, Bool>` is an
#: instance of the 0-parameter registration).  `Tuple` is reserved in the data
#: namespace (E158, #1397), so no declaration shares the name.
_VARIADIC_ADTS = frozenset({"Tuple"})

# `substitute_type_vars` was relocated to `vera.monomorphize` (the codegen-free
# shared monomorphizer, #732) so the verifier can reuse it without importing the
# WASM backend.  Re-exported here so the existing
# `from vera.wasm.inference import substitute_type_vars` call sites
# (codegen/core.py, codegen/registration.py, codegen/contracts.py)
# keep working.  (wasm/calls.py now imports `resolve_fn_type_alias`
# from `vera.monomorphize` directly instead — PR #880.)
__all__ = ["InferenceMixin", "substitute_type_vars"]


class InferenceMixin:
    """Mixin providing type reads and type-mapping utilities.

    Every type code generation lowers by is the checker's, read off the
    typed program (#1525): :meth:`_type_of` for a node, :meth:`_expr_width`
    for the WAT value it is held in, :meth:`_type_name_of` for the name its
    layout, conversion and equality are keyed by.  The remaining methods
    map a type expression the program writes (a parameter's, a binding's)
    to its representation.
    """

    # -----------------------------------------------------------------
    # Binary operators
    # -----------------------------------------------------------------

    # Arithmetic: i64 ops (default for Int/Nat)
    _ARITH_OPS: ClassVar[dict[ast.BinOp, str]] = {
        ast.BinOp.ADD: "i64.add",
        ast.BinOp.SUB: "i64.sub",
        ast.BinOp.MUL: "i64.mul",
        ast.BinOp.DIV: "i64.div_s",
        ast.BinOp.MOD: "i64.rem_s",
    }

    # Arithmetic: f64 ops (Float64)
    _ARITH_OPS_F64: ClassVar[dict[ast.BinOp, str]] = {
        ast.BinOp.ADD: "f64.add",
        ast.BinOp.SUB: "f64.sub",
        ast.BinOp.MUL: "f64.mul",
        ast.BinOp.DIV: "f64.div",
        # MOD: handled by _translate_f64_mod() — WASM has no f64.rem
    }

    # Comparison: i64 → i32 (default)
    _CMP_OPS: ClassVar[dict[ast.BinOp, str]] = {
        ast.BinOp.EQ: "i64.eq",
        ast.BinOp.NEQ: "i64.ne",
        ast.BinOp.LT: "i64.lt_s",
        ast.BinOp.GT: "i64.gt_s",
        ast.BinOp.LE: "i64.le_s",
        ast.BinOp.GE: "i64.ge_s",
    }

    # Comparison: f64 → i32 (Float64)
    _CMP_OPS_F64: ClassVar[dict[ast.BinOp, str]] = {
        ast.BinOp.EQ: "f64.eq",
        ast.BinOp.NEQ: "f64.ne",
        ast.BinOp.LT: "f64.lt",
        ast.BinOp.GT: "f64.gt",
        ast.BinOp.LE: "f64.le",
        ast.BinOp.GE: "f64.ge",
    }

    def _type_of(self, node: ast.Node) -> Type | None:
        """The checker's type of *node* (#1525): the typed program's table,
        by the node's identity, a clone's node included, or the type a node
        code generation built after the check was built at
        (:meth:`_built`).  ``None`` for a node with neither: a pattern, or
        a node a test builds into a bare context.

        Code generation derives no type of its own: every width, every
        element, key and value type, every scrutinee's and every closure's
        type it lowers by is this one, the type the program was checked
        and verified against."""
        key = node.node_id
        if key is None:
            return None
        ty = self._expr_semantic_types.get(key)
        if ty is None:
            ty = self._built_types.get(key)
        return ty

    def _built(self, node: _N, ty: Type) -> _N:
        """*node*, which code generation builds after the check to stand
        for a computation the program writes (an interpolation's
        conversions, a desugared `compare`), with the type it is built at
        recorded under its identity, so :meth:`_type_of` answers for it as
        for a checked node."""
        if node.node_id is None:
            object.__setattr__(node, "node_id", ast.fresh_node_id())
        assert node.node_id is not None  # noqa: S101
        self._built_types[node.node_id] = ty
        return node

    def _width_of(self, ty: Type | None) -> str | None:
        """The WAT value a value of *ty* is held in
        (:func:`vera.types.value_width`), with this namespace's own data
        declarations first: a ``data Array`` or ``data Future`` declared
        here is a pointer, whatever the built-in of its name is held as
        (spec §8.4.1, #1321).

        A type variable is held as a pointer.  Only a generic's template
        holds one, which code generation compiles beside its instances'
        clones and nothing calls (every call reaches its instance's clone,
        #1679), and it lays a `T` element or field out as the pointer its
        own type expressions name."""
        if isinstance(ty, RefinedType):
            ty = base_type(ty)
        if isinstance(ty, TypeVariable):
            return "i32"
        if (isinstance(ty, AdtType) and ty.name in ("Array", "Future")
                and self._declares_adt(ty.name, len(ty.type_args))):
            return "i32"
        if (isinstance(ty, AdtType) and ty.name == "Future"
                and len(ty.type_args) == 1):
            return self._width_of(ty.type_args[0])
        return value_width(ty)

    def _expr_width(self, expr: ast.Expr) -> str | None:
        """The WAT value *expr*'s value is held in: the width of the type
        the checker gave it.  ``None`` for a value that holds nothing
        (`Unit`, a `throw`'s `Never`) and for a node with no type.

        An `if`, a `match` and a `handle` take their block's result from
        here, the join the checker typed, not from an arm: an arm that
        always throws has no width, and a join whose arms code generation
        could not type left a value on the stack of a result-less block
        (#1276, and #1525's line from the program generator)."""
        return self._width_of(self._type_of(expr))

    def _declared_width(self, node: ast.Node) -> str | None:
        """The WAT value a value declared at *node*, a type expression or a
        pattern, is held in: the width of the type the checker resolved the
        type expression to, or the type the pattern matches (#1525).
        ``"unit"`` for a type that holds nothing (`Unit`, a `Future` of
        one), which is stored nowhere; ``None`` for a node the check did not
        type, and for a bare type variable, which only a generic's template
        declares a value at: nothing calls the template (every call reaches
        an instance's clone, #1679), and a value with no width drops it, as
        the variable's spelling did.

        A parameterised alias is its target under its arguments (`Id<Nat>`
        is a `Nat`, `W<Int>` under `type W<T> = String` a `String`), which a
        width read off the type's spelling had none for, and so dropped the
        function, or read as one word where the value is a pair."""
        ty = self._type_of(node)
        if ty is None or isinstance(base_type(ty), TypeVariable):
            return None
        if erases_to_unit(ty):
            return "unit"
        return self._width_of(ty)

    @staticmethod
    def _is_nat_type(ty: Type | None) -> bool:
        """Whether *ty*, a refinement read as its base, is `Nat`."""
        return ty is not None and base_type(ty) == NAT

    def _holds_pointer(self, ty: Type | None) -> bool:
        """Whether a value of *ty* is held in an ``i32`` that addresses the
        heap (or names a host handle), so a binding of it is a GC root: a
        pair's pointer half is one, and so is any other ``i32`` but an
        inline scalar's (`Bool`, `Byte`), a `Future` of one included."""
        width = self._width_of(ty)
        if width == "i32_pair":
            return True
        while isinstance(ty, (RefinedType, AdtType)) and (
                isinstance(ty, RefinedType)
                or (ty.name == "Future" and len(ty.type_args) == 1
                    and not self._declares_adt("Future", 1))):
            ty = ty.base if isinstance(ty, RefinedType) else ty.type_args[0]
        return width == "i32" and value_type_name(ty) not in _INLINE_I32_TYPES

    def _type_name_of(self, expr: ast.Expr) -> str | None:
        """The name of the type the checker gave *expr*
        (:func:`vera.types.value_type_name`), by which code generation picks
        a value's layout as an element, its conversion to `String`, its
        equality and its container tags.  ``None`` for a node with no type.

        It replaces a walker over the expression's syntax that answered a
        name of its own: the bare head of a constructed or returned data
        type (``Option`` for an ``Option<Int>``), ``Int`` for a value the
        checker types ``Nat`` or ``Byte``, nothing for a closure or a call
        it had no arm for, and so a dropped function, a module that does
        not load or a wrong value where its answer and the checker's
        differed (#1525)."""
        return value_type_name(self._type_of(expr))

    def _type_arg_name_of(self, expr: ast.Expr, *path: int) -> str | None:
        """The name of an argument of *expr*'s checked type, reached by
        argument positions: an `Array`'s element is ``(0,)``, a `Map`'s key
        ``(0,)`` and value ``(1,)``, a `Set`'s member ``(0,)``, the element
        of an `Array<Array<T>>`'s element ``(0, 0)``.  ``None`` for a type
        with no such argument."""
        ty = self._type_of(expr)
        for index in path:
            ty = base_type(ty) if ty is not None else None
            if not (isinstance(ty, AdtType) and len(ty.type_args) > index):
                return None
            ty = ty.type_args[index]
        return value_type_name(ty)

    def _return_name_of(self, closure: ast.Expr) -> str | None:
        """The name of the return type of the function type the checker
        gave *closure*, whatever its shape.  ``None`` for a value the
        checker did not type as a function."""
        ty = self._type_of(closure)
        ty = base_type(ty) if ty is not None else None
        if isinstance(ty, FunctionType):
            return value_type_name(ty.return_type)
        return None

    @staticmethod
    def _format_named_type(te: ast.NamedType) -> str:
        """Format a NamedType as a full type name including type args.

        Note: duplicated in Monomorphizer._format_type_name
        (vera/monomorphize.py). Both must remain in sync.
        """
        if not te.type_args:
            return te.name
        arg_names = []
        for ta in te.type_args:
            if isinstance(ta, ast.NamedType):
                arg_names.append(
                    InferenceMixin._format_named_type(ta))
            else:
                return te.name
        return f"{te.name}<{', '.join(arg_names)}>"

    def _canonical_named_type(
        self,
        te: ast.TypeExpr,
        alias_map: dict[str, ast.TypeExpr] | None = None,
    ) -> ast.NamedType | None:
        """Walk a TypeExpr to its canonical `NamedType` form.

        The single canonicalisation walker that consolidates the
        `RefinementType` unwrap + alias-chain follow + generic
        substitution shape replicated across many sites in this
        module pre-#630.  Each ad-hoc walk handled a subset of the
        concerns and missed the rest, accumulating ten distinct
        triggers of the #602 i32_pair-into-i64 mismatch bug class
        across `f()` baseline, type aliases over String, single
        and nested `RefinementType` returns, refinement-over-alias,
        `apply_fn` over `FnType`-aliased / nested-refinement /
        inline-`AnonFn` arguments, and the parallel
        `IndexExpr`-of-`FnCall` path.  See [#630] for the full
        narrative.

        Iteratively (until fixed point or cycle):

        1. Unwraps `RefinementType` layers (any nesting depth).
        2. If `alias_map` is provided and the current `NamedType`'s
           name is in the map, substitutes the mapped type and
           re-loops.  (Used by generic FnType-alias resolution where
           the alias's type params bind concrete types from the
           call site.)
        3. Follows `NamedType` alias chains via `self._alias_env.aliases`
           one step per outer iteration, so any `RefinementType`
           wrapping the alias body is unwrapped on the next
           iteration.

        Returns the final `NamedType` — with `type_args` taken from
        the **terminal** `NamedType` reached during the walk — or
        `None` if the walk terminates at a non-`NamedType` (`FnType`,
        refinement-over-non-`NamedType` base, alias body that is
        itself a `FnType`, etc.).

        Type-args follow the *terminal* `NamedType` so that an alias
        whose body carries type_args propagates them through.
        Concrete cases:

          - `type IntList = Array<Int>` resolves
            `NamedType("IntList")` to `NamedType("Array", [Int])` —
            the alias body's `type_args` are preserved.
          - `alias_map["T"] = NamedType("Array", [Int])` resolves
            `NamedType("T")` to `NamedType("Array", [Int])` — the
            substituted type's `type_args` are preserved.
          - `type Str = String` resolves `NamedType("Str")` to
            `NamedType("String")` — neither has `type_args`,
            unchanged.

        Edge case: the outermost `NamedType` may carry `type_args`
        that the alias body discards (e.g. `NamedType("Box", [Int])`
        with a non-parameterised `type Box = Holder`).  Since
        non-parameterised aliases applied with type_args are
        ill-formed at the type-check level, we accept this
        information loss; parameterised-alias substitution proper
        (where `type Box<T> = Holder<T>` would push the outer `T`
        into the resolved body via per-alias type-param binding)
        is **out of scope** for #630 and remains a separate latent
        gap.
        """
        seen: set[str] = set()
        while True:
            # Unwrap RefinementType layers — any nesting depth.
            while isinstance(te, ast.RefinementType):
                te = te.base_type
            if not isinstance(te, ast.NamedType):
                return None
            # Unified cycle guard for both `alias_map` substitution
            # and `_alias_env.aliases` chain following.  Without this, an
            # alias_map self-reference (`{T: NamedType("T")}`) or a
            # cyclic chain through a mix of substitutions and follows
            # would loop forever.
            if te.name in seen:
                break
            seen.add(te.name)
            # alias_map substitution (generic type-param binding).
            # Checked before alias-chain follow so generic params
            # take precedence over any same-named type alias.
            if alias_map is not None and te.name in alias_map:
                te = alias_map[te.name]
                continue
            # Follow NamedType alias chain — one step per iteration so
            # any RefinementType wrapping the alias body is unwrapped
            # on the next pass.  When the alias is parameterised
            # (`type Box<T> = Array<T>` etc.), substitute the alias's
            # type params with the concrete `te.type_args` *before*
            # continuing — otherwise the alias body's type variables
            # leak into the returned NamedType.
            alias = self._alias_env.aliases.get(te.name)
            if alias is None:
                break
            if isinstance(alias, (ast.NamedType, ast.RefinementType)):
                alias_params = self._alias_env.alias_params.get(te.name)
                if (alias_params and te.type_args
                        and len(alias_params) == len(te.type_args)):
                    local_subst = dict(zip(alias_params, te.type_args))
                    alias = self._substitute_type_vars(alias, local_subst)
                te = alias
                continue
            # FnType-bodied alias or other non-resolvable shape.
            return None
        # `te` is the terminal NamedType; preserve its type_args.
        return ast.NamedType(name=te.name, type_args=te.type_args)

    def _substitute_type_vars(
        self,
        te: ast.TypeExpr,
        subst: dict[str, ast.TypeExpr],
    ) -> ast.TypeExpr:
        """Instance-method wrapper around the module-level
        `substitute_type_vars` so existing call sites on
        `InferenceMixin` keep working.  See the free function for
        full documentation of the substitution contract.
        """
        return substitute_type_vars(te, subst)

    def _canonical_wasm_type(
        self,
        te: ast.TypeExpr,
        alias_map: dict[str, ast.TypeExpr] | None = None,
    ) -> str | None:
        """Walk a TypeExpr to its canonical WASM-type string.

        Same walk as `_canonical_named_type` but maps the resolved
        name to the WASM representation:

          - `"i32_pair"` for `String` / `Array` (two-i32 layout).
          - `"i64"` for `Int` / `Nat`.
          - `"f64"` for `Float64`.
          - `"i32"` for `Bool` / `Byte` / ADTs / pointer types.
          - `None` for `Unit` (no WASM representation — caller
            usually omits the result clause entirely).
          - `"i64"` as the safe default when the walker can't reach
            a `NamedType` (matches the pre-#630 fallthroughs at
            every WASM-type-walk site).

        Note that the `Unit → None` and `unreachable-NamedType →
        "i64"` cases are intentionally distinct: `None` says "no
        WASM type, omit the slot"; `"i64"` says "we couldn't infer,
        default to the i64 word size".  Callers handling `None` for
        Unit must not conflate the two.

        `Future<T>` is treated as transparent (same WASM
        representation as `T`), parallel to `_slot_name_to_wasm_type`'s
        `Future<...>` strip-and-recurse handling.  Without this, a
        `Future<String>` return at an `apply_fn` / FnType-alias
        position would canonicalise to `NamedType("Future", [String])`
        and `_named_type_to_wasm("Future")` would default to `"i32"`
        — producing a `call_indirect` sig mismatch against the
        actual `i32_pair` emit.
        """
        canonical = self._canonical_named_type(te, alias_map)
        if canonical is None:
            # Walker bailed without reaching a NamedType.  The most
            # common reachable case is a `FnType` (or an alias chain
            # terminating in `FnType`) at a closure-pointer return
            # position — e.g. `type Outer = fn(Int -> Inner)
            # effects(pure)` where `Inner` is itself a `FnType`
            # alias.  Higher-order returns must use the `i32`
            # closure-pointer ABI; defaulting to `"i64"` mismatches
            # the call_indirect sig vs the actual emit and traps at
            # WASM validation.  Symmetric to the explicit FnType
            # branch in `_type_expr_to_wasm_type` (codegen/core.py).
            if self._reaches_fn_type(te, alias_map):
                return "i32"
            return "i64"
        # #1321/#1331: a DECLARED ADT of this namespace beats every built-in
        # reading of its name — the same precedence `classify_named` gives it.
        if self._declares_adt(canonical.name):
            return "i32"
        # Future<T> is transparent — recurse on the inner type.
        if (canonical.name == "Future" and canonical.type_args
                and len(canonical.type_args) == 1):
            return self._canonical_wasm_type(
                canonical.type_args[0], alias_map)
        if canonical.name in ("String", "Array"):
            return "i32_pair"
        return self._named_type_to_wasm(canonical.name)

    def _reaches_fn_type(
        self,
        te: ast.TypeExpr,
        alias_map: dict[str, ast.TypeExpr] | None = None,
    ) -> bool:
        """True if walking `te` through `RefinementType` /
        `alias_map` / `_alias_env.aliases` lands on a `FnType`.

        Used by `_canonical_wasm_type` to distinguish the
        FnType-return case (closure-pointer ABI, `"i32"`) from
        other walker-bail cases (default `"i64"`).  Mirrors the
        traversal logic in `_canonical_named_type` but with a
        different terminal classification — needed because the
        walker collapses both terminal kinds into `None` for the
        NamedType-returning contract, losing the FnType signal.
        """
        seen: set[str] = set()
        while True:
            while isinstance(te, ast.RefinementType):
                te = te.base_type
            if isinstance(te, ast.FnType):
                return True
            if not isinstance(te, ast.NamedType):
                return False
            if te.name in seen:
                return False
            seen.add(te.name)
            if alias_map is not None and te.name in alias_map:
                te = alias_map[te.name]
                continue
            alias = self._alias_env.aliases.get(te.name)
            if alias is None:
                return False
            if isinstance(alias, ast.FnType):
                return True
            if isinstance(alias, (ast.NamedType, ast.RefinementType)):
                te = alias
                continue
            return False


    def _resolve_i32_pair_ret_te(
        self, ret_te: ast.TypeExpr | None,
    ) -> str | None:
        """Canonicalise a fn's return TypeExpr for `i32_pair` lookup.

        Several shapes can appear at user-fn return positions for
        `String` / `Array<T>` (i32_pair) returns:

          - `NamedType("String")` — bare type, common case.
          - `NamedType("MyAlias")` where the alias resolves to String —
            `_resolve_base_type_name` follows the chain to `"String"`.
          - `RefinementType(base_type=NamedType("String"), ...)` — the
            inline `@{ @String | predicate }` form.  `_register_fn`
            stores the literal AST, so the registry holds a
            `RefinementType` directly.
          - **Nested refinements** (`@{ @{ @String | p1 } | p2 }`) —
            the grammar admits `refinement_type` over any `type_expr`,
            so refinements can wrap refinements.  Empirically reachable
            via valid Vera (the type checker accepts the nested form
            at fn return positions).  The unwrap below loops to handle
            arbitrary nesting depth.

        Without unwrapping these shapes, a fn declared with any of the
        wrapper forms reproduces the original #602 trap inside
        interpolation — `_fn_ret_type_exprs.get(name)` returns the
        un-canonical AST, the downstream consumer's `vera_type ==
        "String"` check fails, and `_translate_interpolated_string`
        falls through to `to_string(...)` over an `i32_pair` value
        (`expected i64, found i32` at WASM validation).

        See [#626](https://github.com/aallan/vera/issues/626) — every
        `return None` here is an instance of the broader silent-skip
        pattern.  The downstream `to_string` fallback at
        `vera/wasm/operators.py` carries the matching commentary.

        Returns the canonical Vera type name (`"String"` / `"Array"` /
        etc.), or None for shapes the unwrap can't reduce to a
        `NamedType` (e.g. `FnType`, or a `RefinementType` whose
        innermost base is non-`NamedType`).  None-returns are
        currently triggered for cross-module imports too (the
        registry isn't populated cross-module — see #628).

        Post-#630: thin delegate over `_canonical_named_type`, the
        single canonicalisation walker.  The bare-name return
        (without `type_args`) matches both consumers' expectations
        — they compare against `"String"` / `"Array"` and ignore
        parameterisation.
        """
        if ret_te is None:
            return None
        canonical = self._canonical_named_type(ret_te)
        return canonical.name if canonical is not None else None

    def _ctor_to_adt_name(self, ctor_name: str) -> str | None:
        """Find the ADT type name for a constructor name."""
        # ctor-owner-exempt: the flat ownership projection itself
        return self._ctor_to_adt.get(ctor_name)

    def _strip_future_scoped(self, name: str) -> str:
        """:func:`~vera.wasm.helpers._strip_future`, asked in this namespace.

        The free function is a textual ``startswith("Future<")`` peel with no
        namespace to consult, so it ran BEFORE the declared-ADT branch and
        unwrapped a user ``data Future`` as if it were the transparent
        built-in wrapper (PR #1372 review) — the mechanism behind the
        ``data Future`` residue.  A declaration shadows every built-in
        reading of its name (§8.4.1), so the peel asks the spine first and
        declines for a name this namespace declares.
        """
        if self._declares_adt(name):
            return name
        return _strip_future(name)

    def _resolve_element_name(self, elem_type: str) -> str:
        """An array element's type name, resolved the way the spine resolves
        one: through the alias chain, with ``Future<…>`` stripped.

        The four size/load/store/type deciders below and
        :meth:`_is_pair_element_type` must all read the SAME name, or an
        alias-spelled element takes the primitive table in one and the
        built-in reading in another (PR #1372 review).
        """
        name, _ = self._canonicalize_alias_slot_name(elem_type)
        return self._resolve_base_type_name(self._strip_future_scoped(name))

    def _is_pair_element_type(self, elem_type: str) -> bool:
        """Check if an array element type is a pair type (ptr, len).

        String and Array<T> elements are represented as two consecutive
        i32 values (pointer + length), requiring 8 bytes of storage.
        Bare "Array" (without type args) also matches, since the element
        type name from _infer_vera_type may not include type parameters.

        ``Future<…>`` is stripped first (#1045): a ``Future<String>`` /
        ``Future<Array<T>>`` element is a pair exactly like its payload.

        A METHOD, and on this mixin, because the answer depends on the
        NAMESPACE (PR #1372 review).  It used to be a module-level free
        function over a bare ``str`` — no ``self``, no ``AliasEnv``, no ADT
        table — so it could not be asked the question the spine answers, and
        it kept saying "pair" for ``Array`` after `_is_pair_type_name` had
        learned to say "declared ADT".  The two halves then disagreed: with
        ``private data Array { … }`` the SCRUTINEE side stopped refusing
        while the ELEMENT side still laid the value out as an 8-byte
        two-word pair, so an element operation over ``@Array<Array>``
        compiled at rc 0 with ZERO diagnostics to a `.wasm` no runtime can
        load — strictly worse than the loud `[E602]` refusal it replaced.
        Its four derived deciders below all funnel through it, so routing
        this one routes the element side entirely.
        """
        # ALIAS first, then the declared ADT, then the built-in reading —
        # the spine's order, which this decider could not follow while it was
        # a free function.  Under `type Array = Int;` the name is the alias's
        # target, an 8-byte i64 loaded with `i64.load`; answering "pair" for
        # it returned `None` from `_element_load_op`, which the callers read
        # as "two loads".  The same walk `_is_pair_type_name` uses, so the
        # element side and the scrutinee side resolve identically.
        elem_type, _ = self._canonicalize_alias_slot_name(elem_type)
        elem_type = self._resolve_base_type_name(
            self._strip_future_scoped(elem_type))
        # #1321/#1331: a DECLARED ADT of this namespace beats every built-in
        # reading of its name, here exactly as at every other decider.
        if self._declares_adt(elem_type):
            return False
        return elem_type == "String" or elem_type == "Array" or elem_type.startswith("Array<")

    def _element_mem_size(self, elem_type: str) -> int | None:
        """Get memory size in bytes for an array element type.

        Primitive types have fixed sizes.  Pair types (String, Array<T>)
        use 8 bytes (ptr + len).  All other compound types (ADTs) use
        4 bytes (i32 heap pointer).

        ``Future<…>`` is stripped first (#1045) so the payload's size is
        used — e.g. ``Future<Int>`` is an 8-byte i64, not a 4-byte i32.
        """
        elem_type = self._resolve_element_name(elem_type)
        sizes = {
            "Int": 8,
            "Nat": 8,
            "Float64": 8,
            "Bool": 1,
            "Byte": 1,
        }
        size = sizes.get(elem_type)
        if size is not None:
            return size
        # Pair types: (ptr, len) = 8 bytes
        if self._is_pair_element_type(elem_type):
            return 8
        # ADT / other compound types: i32 heap pointer = 4 bytes
        return 4


    def _element_load_op(self, elem_type: str) -> str | None:
        """Get the WASM load instruction for an array element type.

        Returns None for pair types (String, Array<T>) which require
        special two-load handling in the caller.

        ``Future<…>`` is stripped first (#1045) so the payload's load op is
        used — e.g. ``Future<Int>`` loads with ``i64.load``, not ``i32.load``.
        """
        elem_type = self._resolve_element_name(elem_type)
        ops = {
            "Int": "i64.load",
            "Nat": "i64.load",
            "Float64": "f64.load",
            "Bool": "i32.load8_u",
            "Byte": "i32.load8_u",
        }
        op = ops.get(elem_type)
        if op is not None:
            return op
        # Pair types need two loads — caller must handle specially
        if self._is_pair_element_type(elem_type):
            return None
        # ADT / other compound types: single i32 load
        return "i32.load"


    def _element_store_op(self, elem_type: str) -> str | None:
        """Get the WASM store instruction for an array element type.

        Returns None for pair types (String, Array<T>) which require
        special two-store handling in the caller.

        ``Future<…>`` is stripped first (#1045) so the payload's store op is
        used — e.g. ``Future<Int>`` stores with ``i64.store``, not
        ``i32.store``, and ``Future<String>`` returns None (pair, two stores).
        """
        elem_type = self._resolve_element_name(elem_type)
        ops = {
            "Int": "i64.store",
            "Nat": "i64.store",
            "Float64": "f64.store",
            "Bool": "i32.store8",
            "Byte": "i32.store8",
        }
        op = ops.get(elem_type)
        if op is not None:
            return op
        # Pair types need two stores — caller must handle specially
        if self._is_pair_element_type(elem_type):
            return None
        # ADT / other compound types: single i32 store
        return "i32.store"


    def _element_wasm_type(self, elem_type: str) -> str | None:
        """Get the WASM value type for an array element type.

        Returns "i32_pair" for pair types (String, Array<T>),
        "i32" for ADT/compound types, or the native type for primitives.

        ``Future<…>`` is stripped first (#1045) so the payload's value type
        is used — e.g. ``Future<Int>`` is ``i64``, not ``i32``.
        """
        elem_type = self._resolve_element_name(elem_type)
        types = {
            "Int": "i64",
            "Nat": "i64",
            "Float64": "f64",
            "Bool": "i32",
            "Byte": "i32",
        }
        wt = types.get(elem_type)
        if wt is not None:
            return wt
        # Pair types: (ptr, len) represented as i32_pair
        if self._is_pair_element_type(elem_type):
            return "i32_pair"
        # ADT / other compound types: i32 heap pointer
        return "i32"

    def _is_pair_type_name(
        self, type_name: str, _seen: frozenset[str] = frozenset(),
    ) -> bool:
        """Check if a slot type name is a pair type (ptr, len).

        String and Array<T> are represented as two consecutive i32 locals.
        Bare "Array" also matches — monomorphization may produce slot
        references with type_name="Array" (no type args in the name).

        An alias is canonicalized to its target's FULL compound spelling
        first (the shared :meth:`_canonicalize_alias_slot_name` walk, #1046):
        the name-only ``_resolve_base_type_name`` hop drops type arguments,
        so ``type FS = Future<String>`` resolved to bare ``"Future"``, missed
        the Future arm below, and the let binding E602-skipped its enclosing
        function on a check+verify-green program — the pair-payload sibling
        of the #1037 scalar-alias fix, which wired the canonicalizer into
        ``_slot_name_to_wasm_type`` but not into this predicate.

        Resolves type aliases first so `type Row = Array<Bool>` compiles
        identically to writing `Array<Bool>` directly: a SlotRef with
        type_name "Row" must emit `(local.get ptr; local.get len)` like
        any other Array slot, not just the ptr (#583).

        `Future<T>` is representation-transparent (#841): a `Future<String>`
        / `Future<Array<T>>` has the SAME `i32_pair` layout as its payload,
        so it binds and reads as two locals exactly like a bare String /
        Array.  The transparency is to the PAYLOAD's representation — a
        scalar payload (`Future<Int>` → i64) or a pointer payload
        (`Future<Box>` → i32) is NOT a pair.  Mirrors the string-form
        strip-and-recurse in `_slot_name_to_wasm_type`'s Future arm, and
        covers both composite-string sites in the let path — the binding
        (`translate_block`) and the read emit (`_translate_slot_ref`).
        Without it a `let @Future<String>` fell to the scalar branch, where
        `_slot_name_to_wasm_type` recursed through the wrapper to a pair
        inner and returned None, and the whole function was dropped with the
        [E602] loud skip on a check/verify-green program (#1039).
        """
        type_name, _seen = self._canonicalize_alias_slot_name(type_name, _seen)
        resolved = self._resolve_base_type_name(type_name)
        # #1321/#1331: a DECLARED ADT of this namespace beats every built-in
        # reading of its name, exactly as in the checker's spine
        # (`vera.naming.classify_named`).  `data Array { Mk(Int) }` is a
        # one-word heap pointer, and answering "pair" for it made the match
        # over it a pair scrutinee — refused with a located E602 whose text
        # describes `String` / `Array<T>`, its callers dropped behind E620,
        # and the module shipped with no exports at all.  Ahead of the
        # `Future` strip too: a user `data Future` carries no transparent
        # payload.
        if self._declares_adt(resolved):
            return False
        if resolved.startswith("Future<") and resolved.endswith(">"):
            return self._is_pair_type_name(resolved[7:-1], _seen)
        return (resolved == "String"
                or resolved == "Array"
                or resolved.startswith("Array<"))


    def _closure_arg_return_type(
        self, closure_arg: ast.Expr,
    ) -> ast.TypeExpr | None:
        """Declared return TypeExpr of the closure an ``apply_fn`` applies.

        The mixin-side shape dispatch shared by both inference consultors
        (``_infer_apply_fn_return_type`` — the ``call_indirect`` signature
        — and ``_infer_fncall_vera_type``'s ``apply_fn`` arm — the
        Vera-type inference).  A ``SlotRef`` is resolved through the shared
        :func:`resolve_fn_type_alias`, which follows the alias chain
        **transitively** to the terminal ``FnType`` (``type Fetcher =
        InnerFetcher;`` — #867) and substitutes any generic alias's type
        params from the slot's bound type args; an inline ``AnonFn`` yields
        its declared return type directly.  Any other shape yields
        ``None``.

        This is the same resolution the fused-await classifier's
        ``_apply_fn_closure_ret_type`` (``vera/wasm/async_fusion.py``)
        performs — both route the ``SlotRef`` through
        :func:`resolve_fn_type_alias`, so the signature this builds and
        the classification that gates the runtime fused-handle check can
        never consult a differently-resolved return type.
        """
        if isinstance(closure_arg, ast.SlotRef):
            fn_type = resolve_fn_type_alias(
                ast.NamedType(
                    name=closure_arg.type_name,
                    type_args=closure_arg.type_args,
                ),
                self._alias_env.aliases,
                self._alias_env.alias_params,
            )
            return fn_type.return_type if fn_type is not None else None
        if isinstance(closure_arg, ast.AnonFn):
            return closure_arg.return_type
        return None


    def _type_expr_base_is_nat(self, te: ast.TypeExpr) -> bool:
        """True iff *te* resolves (through aliases) to ``@Nat`` (#984).
        Alias-aware
        (`type Count = Nat`), so a closure return declared with a @Nat alias is
        guarded like a bare @Nat.  A refinement over @Nat also resolves to
        ``Nat`` here; the closure-return narrow gate additionally excludes
        refinements (`_refinement_guard_parts`), leaving them to the refinement
        boundary path, exactly as the top-level narrow-return gate does."""
        name = self._type_expr_to_slot_name(te)
        if name is None:
            return False
        return self._resolve_base_type_name(name) == "Nat"

    def _closure_return_width(self, closure_arg: ast.Expr) -> str | None:
        """The WAT value a closure application returns: the width of the
        return type of the function type the checker gave *closure_arg*,
        whatever its shape (a closure literal, a slot, a call that returns
        one, a cell read, #1516).  ``None`` for a `Unit` return, and for an
        argument the checker did not type as a function."""
        ty = self._type_of(closure_arg)
        if isinstance(ty, RefinedType):
            ty = base_type(ty)
        if not isinstance(ty, FunctionType):
            return None
        return self._width_of(ty.return_type)


    def _declares_adt(self, type_name: str, arity: int | None = None) -> bool:
        """Is *type_name* a ``data`` declaration of the namespace compiling?

        The wasm layer's arm of the resolution spine's DECLARED-ADT branch
        (:func:`vera.naming.classify_named`), asked over slot-name STRINGS
        rather than type expressions — which is the currency here.  Spec
        §8.4.1 lets a declaration take a name a built-in container or the
        prelude already uses, and the declaration wins, so every derivation
        that would otherwise answer the built-in's representation asks this
        first (#1321, #1331).

        ``_adt_type_names`` is the namespace-scoped set the same
        ``AliasEnv.data_types`` this context's ``_alias_env`` carries — so a
        sibling module's ADT, or the entry file's, is NOT an ADT here.

        A parameterised spelling (``Box<Int>``) asks about its head, and is
        an instance of the declaration only with as many arguments as the
        declaration takes (#1539).  The spelling is a VALUE's type as often
        as a name this namespace wrote: an array literal's ``Array<Int>``
        beside a ``data Array { … }`` is the container's, which the head
        alone cannot say, and reading it as the one-word declaration walked
        its ``(ptr, len)`` pair as a pointer.  A name this namespace writes
        always carries the declaration's arity (the checker refuses any
        other, E135), so the count separates the two exactly when they
        differ.  When they agree — a built-in ``Decimal`` beside
        ``data Decimal`` — the checker gives both one type, and so does
        this.  A bare spelling is the declaration's, as the #772 bare head
        of a generic declaration's value is.  *arity* is the argument count
        of a caller that has the name without its arguments.
        """
        masked = naming.mask_refinements(type_name)
        if "<" in masked:
            base = type_name[:masked.index("<")]
            if arity is None:
                arity = len(self._split_type_args(type_name))
        else:
            base = type_name
        if base not in self._adt_type_names:
            return False
        if not arity or base in _VARIADIC_ADTS:
            return True
        declared = self._adt_tp_counts.get(base)
        return declared is None or declared == arity

    def _value_adt_key(self, ptype: str) -> str | None:
        """The data type a VALUE's type names: its layout key, or ``None``
        for a built-in or primitive (#1534, #1539).

        This namespace's own reading first, arity-aware
        (:meth:`_declares_adt`); then any user declaration's layout key,
        which after the #1317 renames names one data type in every
        namespace (``_value_data_types``).  The second is what a value made
        elsewhere needs: ``favourite``'s ``Colour`` is a data type in the
        entry file that imported ``favourite`` alone, and asking the entry's
        membership dropped every ``show`` / ``hash`` of it (E602).
        """
        base = ptype.split("<", 1)[0] if "<" in ptype else ptype
        if self._declares_adt(ptype):
            return base
        if base in self._value_data_types:
            return base
        return None

    @staticmethod
    def _split_type_args(type_name: str) -> list[str]:
        """The top-level argument spellings of ``Head<A, B<C>>``, a
        refinement's predicate read as one atom (#1674)."""
        masked = naming.mask_refinements(type_name)
        lt = masked.index("<") + 1
        inner, shape = type_name[lt:], masked[lt:]
        if shape.endswith(">"):
            inner, shape = inner[:-1], shape[:-1]
        out: list[str] = []
        depth = 0
        cur = ""
        for ch, sh in zip(inner, shape):
            if sh == "<":
                depth += 1
            elif sh == ">":
                depth -= 1
            if sh == "," and depth == 0:
                out.append(cur.strip())
                cur = ""
            else:
                cur += ch
        if cur.strip():
            out.append(cur.strip())
        return out

    @staticmethod
    def _named_type_to_wasm(name: str) -> str | None:
        """Map a concrete type name to its WASM representation."""
        if name in ("Int", "Nat"):
            return "i64"
        if name == "Float64":
            return "f64"
        if name == "Bool":
            return "i32"
        if name == "Unit":
            return None
        return "i32"  # ADT or other pointer type

    def _fn_type_return_wasm(self, fn_type: ast.FnType) -> str | None:
        """Get the WASM return type from a FnType AST node.

        Post-#630: thin delegate over `_canonical_wasm_type`.  The
        pre-#630 ad-hoc `while`-loop + alias-resolve + i32_pair
        check has been folded into the centralised walker; see its
        docstring for the full canonicalisation contract.
        """
        return self._canonical_wasm_type(fn_type.return_type)

    def _fn_type_param_wasm_types(
        self, fn_type: ast.FnType,
    ) -> list[str]:
        """Get WASM parameter types from a FnType AST node."""
        types: list[str] = []
        for p in fn_type.params:
            if isinstance(p, ast.NamedType):
                name = p.name
                if name in ("Int", "Nat"):
                    types.append("i64")
                elif name == "Float64":
                    types.append("f64")
                elif name == "Bool":
                    types.append("i32")
                elif name == "Unit":
                    pass  # skip Unit params
                else:
                    types.append("i32")  # ADT pointer
            else:  # pragma: no cover
                types.append("i64")  # default
        return types

    def _type_expr_name(self, te: ast.TypeExpr) -> str | None:
        """Extract a simple type name from a TypeExpr.

        Delegates to :func:`vera.naming.slot_name` (#1208) so a closure's
        parameter-count keys (`param_type_counts`) use the same name that
        `_translate_slot_ref` / `_collect_free_vars` resolve against — and that
        the checker bound the slot under.
        """
        return naming.slot_name_or_none(te, self._alias_env)

    def _type_name_to_wasm(self, type_name: str) -> str:
        """Map a Vera type name string to a WASM type string."""
        if type_name in ("Int", "Nat"):
            return "i64"
        if type_name == "Float64":
            return "f64"
        if type_name in ("Bool", "Byte"):
            return "i32"
        if type_name == "Unit":  # pragma: no cover
            return "i32"  # shouldn't appear, safe fallback
        # ADT or function type alias → i32 pointer
        return "i32"

    def _type_expr_to_slot_name(self, te: ast.TypeExpr) -> str | None:
        """The slot-binding name of *te*, as the checker binds it (#1208).

        Delegates to :func:`vera.naming.slot_name` against this context's
        alias environment: syntactic head, RESOLVED type arguments, so a
        parameter written ``@Option<Cnt>`` keys the ``Option<Int>`` stack the
        checker created and the reference side (``naming.slot_ref_key``)
        looks up.  Nested composites stay fully qualified (#914 finding 2).
        """
        return naming.slot_name_or_none(te, self._alias_env)

    def _family_name(self, te: ast.TypeExpr) -> str:
        """The ``State<T>``/``Exn<E>`` host-import/tag FAMILY name for a
        type argument (#1209) — :func:`vera.naming.family_name` over this
        context's alias environment, so the family names the CELL the
        checker typed.  Every spelling that resolves to one cell (a scalar
        alias, #1205; a composite or parameterised alias, #1209) is one
        import and one tag; only :func:`vera.slots.family_fallback_name`'s
        residue stays syntactic.  The env is the DECLARING module's
        (``set_alias_env``), so a name means what it meant where it was
        written."""
        return naming.family_name(
            te, self._alias_env, family_fallback_name(te))

    def _family_base(self, te: ast.TypeExpr) -> str:
        """The same cell's REPRESENTATION name (#1218).

        :func:`vera.naming.family_base_name` over this context's alias
        environment: the family with its refinements stripped, which is what
        decides i32/i64/f64/pair, pointer-ness for the GC shadow stack, and
        which #1203 write guard applies.  A refined cell has its OWN family
        (that is #1218) and its BASE's representation, so the two names are
        derived side by side at every handle site and never substituted for
        each other — this one is never a symbol and never compared against
        another cell's."""
        return naming.family_base_name(
            te, self._alias_env, family_fallback_name(te))

    def _boundary_base(self, te: ast.TypeExpr) -> str:
        """The REPRESENTATION base name of a declared WRITE boundary (#1256).

        ONE derivation for every #1212 marking site that holds a type
        expression — the named and closure RETURN, the ``apply_fn``
        argument, the ``throw`` payload.  Composes the two hops each site
        used to spell for itself: :meth:`_family_base` resolves the type
        expression to its representation (an alias chased, a refinement
        stripped), and :meth:`_resolve_base_type_name` chases the one
        residue that can survive it — :func:`vera.slots.family_fallback_name`
        returns a syntactic name when the resolution reaches a function or
        unknown type.  ``_translate_handle_exn`` already wrote exactly this
        composition; the return boundary wrote a different one (slot name
        then resolve), which is two derivations of one fact and the shape
        #1213 is about.

        Never a cell IDENTITY: a refined boundary and its base share a
        width and share this answer, which is the whole point.
        """
        return self._resolve_base_type_name(self._family_base(te))

    def _state_effect_family(self, effect_ref: ast.EffectRefNode) -> str:
        """The cell FAMILY named by a ``State<T>`` effect REFERENCE (#1209).

        The one derivation behind ``old(State<T>)`` and ``new(State<T>)``:
        the snapshot map (``_collect_old_types``) and the import registry
        (``_state_types``) are keyed by the family, so a read that named the
        reference any other way misses a registered entry and the
        ``old(State<T>)`` lowering raises (#914 finding 1).  Naming it here,
        once, is what keeps the three call sites from re-deriving it three
        ways.  Shape validation belongs to
        :func:`~vera.wasm.helpers.state_type_arg`, which raises for anything
        that is not a one-argument ``State``.
        """
        return self._family_name(state_type_arg(effect_ref))

    def _state_effect_family_base(
        self, effect_ref: ast.EffectRefNode,
    ) -> str:
        """The REPRESENTATION name of the cell a ``State<T>`` effect
        reference denotes (#1218) — :meth:`_state_effect_family`'s twin over
        :meth:`_family_base`, for the width decisions rather than the
        registry lookups."""
        return self._family_base(state_type_arg(effect_ref))

    def _resolve_base_type_name(
        self,
        name: str,
        _seen: frozenset[str] = frozenset(),
        _root_name: str | None = None,
    ) -> str:
        """Resolve a type alias to its base type name.

        Follows alias chains through refinement types to the underlying
        primitive or ADT name.  E.g. "PosInt" -> "Int".

        ``_seen`` is an internal cycle-detection accumulator — when the
        same name is encountered twice along an alias chain (cyclic
        aliases such as ``type A = B; type B = A``), the recursion is
        cut and the **caller's original** name is returned via the
        threaded ``_root_name``.  This matters for prefix-chain cycles
        like ``{A: B, B: C, C: B}`` (A leads into a B↔C cycle that
        doesn't include A): the caller asked about ``A``, so the
        return must be ``A``, not the revisited-cycle node ``B``.
        Cyclic aliases are user errors caught by the type checker's
        ``_check_alias_cycles`` pass which emits ``[E132]`` (closed
        in #648); this guard is defence-in-depth so a future
        regression in the upstream check cannot turn into a
        ``RecursionError`` inside codegen.  Closes #633 — the sibling
        walker ``_canonical_named_type`` (PR #631) already has this
        guard; this restores consistency.

        ``_root_name`` defaults to ``None`` on the public-entry call;
        the first recursion sets it to the original ``name`` so all
        deeper calls share the same caller-visible identity.
        """
        if _root_name is None:
            _root_name = name
        if name in _seen:
            # Cycle — return the caller's original name unchanged
            # (treat as opaque, no resolution available).
            return _root_name
        if name not in self._alias_env.aliases:
            # Not an alias — this is the underlying base name.
            return name
        _seen = _seen | {name}
        alias = self._alias_env.aliases[name]
        if isinstance(alias, ast.RefinementType):
            if isinstance(alias.base_type, ast.NamedType):
                return self._resolve_base_type_name(
                    alias.base_type.name, _seen, _root_name,
                )
        if isinstance(alias, ast.NamedType):
            return self._resolve_base_type_name(
                alias.name, _seen, _root_name,
            )
        return name

    def _ref_type_name_wasm_type(
        self,
        type_name: str,
        type_args: tuple[ast.TypeExpr, ...] | None = None,
        _seen: frozenset[str] = frozenset(),
    ) -> str | None:
        """Map a slot/result ref's ``type_name`` to its WAT stack type.

        The result-value type of a ``SlotRef`` or ``ResultRef``: ``"i64"`` for
        Int/Nat, ``"f64"`` for Float64, ``"i32"`` for Bool/Byte and pointer-
        represented types (ADTs, Decimal/Map/Set handles, closure pointers),
        ``"i32_pair"`` for the two-word String/Array representation, or ``None``
        for Unit / unknown.

        Shared by the ``SlotRef`` and ``ResultRef`` arms of
        :meth:`_expr_width` so a monomorphized clone's
        ``@T.result`` and ``@T.0`` — which carry the *same* concrete
        ``type_name`` after substitution — agree on their WAT type.  Before
        #891 the ResultRef arm inferred only the scalar primitives, so an
        ADT-bound return defaulted to ``None`` and the postcondition equality
        compared two i32 heap pointers with ``i64.eq`` (a WASM validation
        trap).

        An alias is canonicalized to its target's FULL compound spelling
        first (the shared :meth:`_canonicalize_alias_slot_name` walk,
        #1054): the name-only ``_resolve_base_type_name`` hop drops type
        arguments, so ``type FA = Future<Option<Int>>`` resolved to bare
        ``"Future"`` and — since an alias-spelled slot ref carries no AST
        ``type_args`` — missed the Future arm below, E602-skipping the
        scrutinee and constructor-argument sites the direct spelling
        compiles.  The string-form Future arm below handles the
        canonicalized compound spelling, mirroring
        ``_slot_name_to_wasm_type``; the alias analog of #1046, in the last
        mapper of the family without the canonicalizer."""
        type_name, _seen = self._canonicalize_alias_slot_name(type_name, _seen)
        resolved = self._resolve_base_type_name(type_name)
        if resolved in ("Int", "Nat"):
            return "i64"
        if resolved == "Float64":
            return "f64"
        if resolved in ("Bool", "Byte"):
            return "i32"
        # #1321/#1331: this namespace's own `data` declaration beats every
        # built-in reading of the name — a heap pointer, whatever the
        # container of that name would have been.  The `_adt_type_names`
        # test at the bottom of this chain used to sit BELOW the pair,
        # Future and Map/Set/Decimal arms, so only the names no built-in
        # claimed ever reached it.
        if self._declares_adt(resolved):
            return "i32"
        if self._is_pair_type_name(resolved):
            return "i32_pair"
        # Future<T> is WASM-transparent — same representation as its single type
        # argument.  Mirrors `_slot_name_to_wasm_type`'s string-form Future arm
        # and `_named_type_to_wasm`'s canonical-walk Future arm; this SlotRef /
        # ResultRef mapper was the odd one out that lacked it, so a
        # `match await(@Future<T>.0) { ... }` scrutinee — whose `await` FnCall
        # arm of `_expr_width` delegates to this mapper on the
        # `@Future<T>` slot ref — inferred None and E602-skipped the enclosing
        # function on a check/verify-green program (#1038).  Delegating to
        # `_canonical_wasm_type` lowers the inner type through the same walk the
        # let-binding path uses, so a scalar inner (Future<Int> -> i64), an ADT
        # inner (Future<Option<Int>>, Future<UserADT> -> i32), and a pair inner
        # (Future<String> -> i32_pair) all map correctly here.  (A Future<String>
        # *scrutinee* stays blocked upstream by the separate `let @Future<String>`
        # pair-binding gap, so this mapper fix alone doesn't reach it end-to-end.)
        if resolved == "Future" and type_args and len(type_args) == 1:
            return self._canonical_wasm_type(type_args[0])
        # String-form dual of the arm above (#1054): an alias-canonicalized
        # spelling arrives as the full compound STRING ("Future<Option<Int>>")
        # with no AST type_args — strip the wrapper and recurse on the payload
        # spelling, exactly like _slot_name_to_wasm_type's Future arm.
        if resolved.startswith("Future<") and resolved.endswith(">"):
            return self._ref_type_name_wasm_type(resolved[7:-1], None, _seen)
        base = resolved.split("<")[0] if "<" in resolved else resolved
        # Declared ADT before the built-in handles, uniformly (#1321/#1331).
        # Unreachable for a declared ADT — the `_declares_adt` guard above
        # answers first — and ordered this way so the chain reads the same
        # everywhere rather than relying on that guard staying put.
        if self._declares_adt(resolved):
            return "i32"
        # Opaque handle types — i32 handles managed by host runtime
        if base in ("Decimal", "Map", "Set"):
            return "i32"
        # Function type aliases → i32 (closure pointer).  Resolved through the
        # shared transitive resolver so an alias chain (`type MyFn = InnerFn;`,
        # #867 / PR #880) classifies the same as a direct FnType alias — the
        # depth-1 behaviour is unchanged (a direct alias resolves in one hop).
        if resolve_fn_type_alias(
            ast.NamedType(name=type_name, type_args=type_args),
            self._alias_env.aliases,
            self._alias_env.alias_params,
        ) is not None:
            return "i32"
        return None

    def _canonicalize_alias_slot_name(
        self, name: str, _seen: frozenset[str] = frozenset(),
    ) -> tuple[str, frozenset[str]]:
        """Resolve an alias slot name to its target's FULL compound spelling.

        Hop by hop through alias-of-alias chains (``FUB -> FUA ->
        Future<UA>``), keeping type arguments intact — unlike
        ``_resolve_base_type_name``, which recurses on the target's NAME only
        and drops them (``type FU = Future<Unit>`` resolved to ``"Future"`` —
        PR #1035 review; ``type FI = Future<Int>`` likewise — #1037).  The
        shared walk under ``_slot_name_erases_to_unit`` and
        ``_slot_name_to_wasm_type``, so the zero-size test and the WAT-type
        mapper canonicalize identically: an alias behaves exactly like
        writing its target's spelling directly.

        After the top-level hops, an alias sitting INSIDE a transparent
        ``Future<…>`` payload is canonicalized too (``Future<FlagA>`` ->
        ``Future<Bool>``, #1074) — the hop-by-hop walk resolves only the
        outer NAME, so the four array-element-type deciders that route the
        result to the module-level element-size / store-op helpers
        (``_infer_concat_elem_type``, ``_translate_array_lit``, the
        ``array_flatten`` inner walk, ``_infer_index_element_type``) get a
        payload the size dict can key on, not a bare alias that falls to the
        4-byte i32 default.

        Returns the canonical name plus the accumulated seen-set; callers
        whose own recursion re-enters this walk (the transparent
        ``Future<...>`` payload peel) thread it through so a self-referential
        type argument (``type F = Future<F>``) terminates.  Alias cycles are
        a user-facing E132 upstream — the cut here is defence-in-depth,
        matching ``_resolve_base_type_name``.  A non-alias name, or an alias
        whose target has no nameable slot form, is returned unchanged for
        the caller's own fallthrough handling.
        """
        while name in self._alias_env.aliases and name not in _seen:
            target = type_expr_slot_name(self._alias_env.aliases[name])
            if target is None or target == name:
                break
            _seen = _seen | {name}
            name = target
        # #1074: recurse into a representation-transparent ``Future<…>``
        # payload so an alias sitting INSIDE the wrapper is canonicalized
        # too (``Future<FlagA>`` -> ``Future<Bool>``, ``type BigF =
        # Future<Big>`` -> ``Future<Int>``).  The hop-by-hop walk above
        # resolves only a top-level alias NAME (or an alias chain landing
        # on a ``Future<…>`` compound); the payload spelling it terminates
        # on is left verbatim.  An aliased payload therefore reached the
        # module-level element-size / store-op deciders unresolved (they
        # ``_strip_future`` the wrapper and hand the bare alias to a
        # name-keyed size dict with no alias table) and fell to the 4-byte
        # i32 default — a 4-byte stride over 1-byte-packed Bool/Byte
        # (silent-wrong values) or an ``i32.store`` of an i64/pair payload
        # (a WASM-validation trap behind an exit-0 compile).  Thread
        # ``_seen`` through so a self-referential payload (``type F =
        # Future<F>``) still terminates.
        if name.startswith("Future<") and name.endswith(">"):
            inner = name[len("Future<"):-1]
            inner, _seen = self._canonicalize_alias_slot_name(inner, _seen)
            name = f"Future<{inner}>"
        return name, _seen

    def _slot_name_to_wasm_type(
        self, name: str, _seen: frozenset[str] = frozenset(),
    ) -> str | None:
        """Map a slot type name to a WAT type string.

        An alias is canonicalized to its target's full compound spelling
        first (the shared :meth:`_canonicalize_alias_slot_name` walk): the
        prior name-only ``_resolve_base_type_name`` hop dropped type
        arguments, so an alias TO a compound transparent wrapper (``type FI
        = Future<Int>``) resolved to bare ``"Future"``, matched no branch,
        and returned ``None`` — E602-skipping the enclosing function of a
        destructure / match / let binding on a check+verify-green program
        (#1037; the zero-size dual of the same disease was PR #1035's
        review finding), while the direct ``Future<Int>`` spelling
        compiled.  Canonicalizing makes an alias map exactly like its
        target written directly.
        """
        name, _seen = self._canonicalize_alias_slot_name(name, _seen)
        name = self._resolve_base_type_name(name)
        if name in ("Int", "Nat"):
            return "i64"
        if name == "Float64":
            return "f64"
        if name in ("Bool", "Byte"):
            return "i32"
        # ADT types are heap pointers.  #1321/#1331: a DECLARED ADT is tested
        # BEFORE the built-in container names, matching the checker's spine
        # (`vera.naming.classify_named`) — below them, only a name no built-in
        # claimed reached this branch, so `data Array` / `data Future` were
        # measured as the container instead of as the declaration.
        if self._declares_adt(name):
            return "i32"
        # Future<T> is WASM-transparent — same representation as T
        if name.startswith("Future<") and name.endswith(">"):
            inner = name[7:-1]
            return self._slot_name_to_wasm_type(inner, _seen)
        # Map/Set/Decimal are opaque host-import handles (i32).  A clone is
        # named after a container's bare head (#772), so `option_unwrap_or$Set`
        # binds a bare `Set`: it is the same handle.
        if (name.startswith("Map<") or name.startswith("Set<")
                or name in ("Map", "Set", "Decimal")):
            return "i32"
        base = name.split("<")[0] if "<" in name else name
        # Function type aliases are closure pointers (i32) — resolved
        # **transitively** through the shared resolver (#867 / PR #880
        # 4th site) so a refinement-wrapped (`type Foo = { @fn(...) | p }`)
        # or chained-through-a-refinement fn alias classifies as a
        # closure, not `None`.  Without this the let/param binding is
        # rejected with `CodegenSkip` and its whole function is dropped
        # ("has no WASM representation"), on a check/verify-green program.
        # A plain `NamedType` chain (`type Foo = Bar;` where `Bar` is a
        # bare `FnType`) is already collapsed to `Bar` by the
        # `_resolve_base_type_name` call above; the resolver additionally
        # covers the refinement-peeling and generic-alias hops that walk
        # cannot.  The `name` string may carry type args for a generic
        # alias (`Mapper<Int>`); the resolver keys on `base` and
        # substitutes at each hop.
        if resolve_fn_type_alias(
            ast.NamedType(name=base, type_args=None),
            self._alias_env.aliases,
            self._alias_env.alias_params,
        ) is not None:
            return "i32"
        # Bare "Fn" for anonymous function types
        if name == "Fn":
            return "i32"
        return None

    def _slot_name_erases_to_unit(
        self, name: str, _seen: frozenset[str] = frozenset(),
    ) -> bool:
        """True if a slot type name is *zero-size* — no WASM representation.

        Zero-size means ``Unit``, or a transparent ``Future<…>`` whose payload
        is itself zero-size (``Future<Unit>``, ``Future<Future<Unit>>``, …).
        This is the slot-name mirror of :func:`vera.types.erases_to_unit` and
        codegen's ``_type_expr_to_wasm_type`` (``Future<T>`` is
        representation-identical to ``T`` — #841), and it follows the same
        ``Future<…>`` recursion as :meth:`_slot_name_to_wasm_type`.

        An alias is canonicalized to its target's **full compound spelling**
        first (the shared :meth:`_canonicalize_alias_slot_name` walk, hop by
        hop for chains, cycle-cut by ``_seen``) — NOT through
        ``_resolve_base_type_name``, which recurses on the target's name only
        and drops type arguments (``type FU = Future<Unit>`` resolved to
        ``"Future"``, missed the ``Future<…>`` branch, and E602-skipped the
        function on a check+verify-green program; PR #1035 review).  The
        seen-set threads through the ``Future<…>`` recursion so a
        self-referential type argument also terminates, and the
        ``_resolve_base_type_name`` fallthrough still handles what the
        canonicalizer cannot name (a no-op for non-aliases).

        Distinct from ``_slot_name_to_wasm_type(name) is None``: that predicate
        ALSO fires for genuinely unrepresentable types (an unknown ADT, a bare
        type variable), which are a real codegen gap that must still ``CodegenSkip``
        rather than silently erase.  The declaration-position guards need to tell
        "erase this zero-size field" apart from "skip — cannot represent", so
        they key on THIS check, not on ``_slot_name_to_wasm_type`` being ``None``
        (#1031: the guards previously compared the bare string ``"Unit"``, so a
        ``Future<Unit>`` component missed the zero-size branch and skipped the
        whole function on a check-green program).
        """
        name, _seen = self._canonicalize_alias_slot_name(name, _seen)
        name = self._resolve_base_type_name(name)
        if name == "Unit":
            return True
        if name.startswith("Future<") and name.endswith(">"):
            return self._slot_name_erases_to_unit(name[7:-1], _seen)
        return False
