"""Mixin for function calls, constructor calls, and qualified/module calls.

Extracted from ``core.py`` so that call-checking logic lives in its
own file while the main :class:`TypeChecker` stays focused on
orchestration.
"""

from __future__ import annotations

from collections import Counter
from collections.abc import Callable

from vera import ast, narrowing
from vera.slots import bare_call_denotes_user_fn
from vera.checker.sql import (
    count_placeholders,
    resolve_array_len,
    resolve_literal_string,
)
from vera.environment import (
    DB_SQL_OP_NAMES,
    STRING,
    AdtInfo,
    ConstructorInfo,
    FunctionInfo,
    OpInfo,
)
from vera.types import (
    ORDERABLE_TYPES,
    AdtType,
    ConcreteEffectRow,
    FunctionType,
    PureEffectRow,
    RefinedType,
    Type,
    TypeVar,
    UnknownType,
    base_type,
    contains_fresh_typevar,
    contains_literal_hole,
    contains_typevar,
    erases_to_unit,
    is_effect_subtype,
    is_subtype,
    pretty_effect,
    pretty_type,
    pretty_inferred_type,
    strip_builtin_typevar_marker,
    substitute,
    types_equal,
)


def _compatible_modulo_typevars(
        a: Type, b: Type, rigid: frozenset[str]) -> bool:
    """Structural compatibility treating UNRESOLVED TypeVars as wildcards
    (#993).

    Used only when a subtype check between two types has failed AND at
    least one side still carries unresolved type variables — i.e. the
    call's instantiation could not be pinned down (every argument is
    itself polymorphic, e.g. `option_unwrap_or(nothing(()), None)`).
    An unresolved var on either side matches anything: there EXISTS an
    instantiation making the two sides agree, so rejecting would be a
    false E202.  Unresolved means a fresh `T$n`, a `#b`-marked builtin
    var, or a callee forall var leaked raw from an uninferrable call —
    everything EXCEPT the enclosing function's own declared forall params
    (*rigid*, passed by name from `env.type_params`).  A rigid var is NOT
    a wildcard — inside its own body it is an opaque, already-quantified
    type, so `Option<T>` passed where `Option<Int>` is required must stay
    E202 (the body must be valid for EVERY `T`, PR #1009 review); two
    rigid vars agree only by name.  (A callee var leaked under a
    same-named enclosing forall is conservatively treated as rigid —
    the safe direction.)  Concrete structure must still line up —
    `Option<...>` never matches `Result<...>`, a function's effect row
    must still be permitted by the parameter's (`<IO>` never satisfies
    `pure`), and a genuinely concrete leaf mismatch (`Int` vs `String`)
    is rejected via the subtype fallback.
    """
    a = base_type(a)
    b = base_type(b)
    if isinstance(a, UnknownType) or isinstance(b, UnknownType):
        return True
    if isinstance(a, TypeVar) or isinstance(b, TypeVar):
        a_rigid = (isinstance(a, TypeVar)
                   and "$" not in a.name and a.name in rigid)
        b_rigid = (isinstance(b, TypeVar)
                   and "$" not in b.name and b.name in rigid)
        if isinstance(a, TypeVar) and not a_rigid:
            return True
        if isinstance(b, TypeVar) and not b_rigid:
            return True
        # Every TypeVar side is rigid here: only the same var matches.
        return (isinstance(a, TypeVar) and isinstance(b, TypeVar)
                and a.name == b.name)
    if isinstance(a, AdtType) and isinstance(b, AdtType):
        return (a.name == b.name
                and len(a.type_args) == len(b.type_args)
                and all(_compatible_modulo_typevars(x, y, rigid)
                        for x, y in zip(a.type_args, b.type_args)))
    if isinstance(a, FunctionType) and isinstance(b, FunctionType):
        return (len(a.params) == len(b.params)
                and all(_compatible_modulo_typevars(x, y, rigid)
                        for x, y in zip(a.params, b.params))
                and _compatible_modulo_typevars(
                    a.return_type, b.return_type, rigid)
                and is_effect_subtype(a.effect, b.effect))
    # Leaves (primitives): the instantiation direction is unknown, so
    # accept a subtype relationship either way (Nat vs Int).
    return is_subtype(a, b) or is_subtype(b, a)



def _type_var_occurrences(ty: Type, out: Counter[str]) -> None:
    """Count into *out* every occurrence of a type variable in *ty*, at any
    depth: through type arguments, a function type's parameters, result and
    effect row, and a refinement's base."""
    if isinstance(ty, TypeVar):
        out[ty.name] += 1
    elif isinstance(ty, AdtType):
        for arg in ty.type_args:
            _type_var_occurrences(arg, out)
    elif isinstance(ty, FunctionType):
        for param in ty.params:
            _type_var_occurrences(param, out)
        _type_var_occurrences(ty.return_type, out)
        _effect_type_var_occurrences(ty.effect, out)
    elif isinstance(ty, RefinedType):
        _type_var_occurrences(ty.base, out)


def _effect_type_var_occurrences(row: object, out: Counter[str]) -> None:
    """:func:`_type_var_occurrences` over an effect row's type arguments."""
    if isinstance(row, ConcreteEffectRow):
        for inst in row.effects:
            for arg in inst.type_args:
                _type_var_occurrences(arg, out)


def _instantiation_ends_at_formal(fn_info: FunctionInfo, index: int) -> bool:
    """Whether the instantiation a call infers from argument *index* types
    nothing but that argument: every type variable formal *index* mentions
    occurs exactly once in *fn_info*'s whole signature — so in no other
    parameter (a callback's parameters and result included), not in the
    result or the effect row, and not twice in the formal itself.

    Read off the signature's structure, so every callee is answered the
    same way: `array_length(@Array<T>)` qualifies; `array_any(@Array<T>,
    fn(T -> Bool))`, whose callback reads the elements at `T`, does not."""
    counts: Counter[str] = Counter()
    for param in fn_info.param_types:
        _type_var_occurrences(param, counts)
    _type_var_occurrences(fn_info.return_type, counts)
    _effect_type_var_occurrences(fn_info.effect, counts)
    formal: Counter[str] = Counter()
    _type_var_occurrences(fn_info.param_types[index], formal)
    return bool(formal) and all(counts[var] == 1 for var in formal)


def _names(name: str) -> Callable[[str], bool]:
    """The constructor-name test a pattern of constructor *name* makes."""
    def matches(ctor_name: str) -> bool:
        return ctor_name == name
    return matches

class CallsMixin:
    """Methods for checking function calls, constructors, and qualified calls."""

    # -----------------------------------------------------------------
    # Function calls
    # -----------------------------------------------------------------

    def _check_fn_call(self, expr: ast.FnCall, *,
                       expected: Type | None = None) -> Type | None:
        """Type-check a function call.

        *expected* is the type the call's result is checked against, where
        the context supplies one: a generic callee's type arguments that
        only literals would fix take it (#1541).
        """
        return self._check_call_with_args(expr.name, expr.args, expr,
                                          expected=expected)

    def _check_call_with_args(self, name: str, args: tuple[ast.Expr, ...],
                              node: ast.Node, *,
                              expected: Type | None = None) -> Type | None:
        """Check a call to function `name` with given arguments."""
        # apply_fn is a checker special form (#854): it is variadic and
        # effect-polymorphic — its arity, argument types, result type,
        # and effect row all come from the applied value's fn type — so
        # it cannot be a fixed-signature registry built-in.  Intercept
        # before any lookup: codegen translates the name unconditionally
        # to call_indirect (vera/wasm/calls.py), and E151 rejects user
        # redefinitions, so this is the name's single canonical meaning.
        if name == "apply_fn":
            return self._check_apply_fn(args, node)

        # Look up function — lexically (#991): the nearest same-named
        # where-helper in the enclosing scope stack wins over the flat
        # last-wins registry, so a diamond of same-named helpers with
        # DIFFERENT signatures checks each parent against its OWN helper
        # (the flat lookup falsely E121'd a valid program).
        #
        # #1284: user-fn-FIRST is not an implementation detail of this
        # function, it is the language's bare-call ownership rule (spec
        # §7.4: a bare op resolves only for a name no declaration occupies),
        # and codegen has to lower every such call site the way this
        # resolution read it.  Asking through the shared predicate is what
        # makes the checker's answer and codegen's the same rule over two
        # tables rather than two rules that happened to agree: the two
        # codegen legs used to disagree, and a `fn get` called under a
        # `handle[State<T>]` lowered to the host cell intrinsic — a silently
        # wrong value, a module WASM validation rejected, or a spurious
        # [E602] naming a State operation the user never wrote.
        if bare_call_denotes_user_fn(name, self._user_fn_names):
            fn_info = self._lookup_function_scoped(name)
            if fn_info is not None:
                return self._check_fn_call_with_info(fn_info, args, node,
                                                     expected=expected)

        # Maybe it's an effect operation
        op_info = self.env.lookup_effect_op(name)
        if op_info:
            self._effect_ops_used.add(op_info.parent_effect)
            # #1148: a BARE (unqualified) op call is codegen-routable only for
            # the built-in State/Exn ops get/put/throw (which route to host
            # cells / a host tag even unhandled) or when the effect is handled by
            # an enclosing `handle` block (rewritten to the clause).  Every other
            # bare op — IO / DB / Http / Inference / Random and user effects —
            # fails `vera compile` with a confusing "Function '<op>' is not
            # defined".  Reject it at check time (E217, the safe direction of a
            # check<->codegen disagreement).
            #
            # The carve-out keys on BOTH the effect name AND the op name, not the
            # effect name alone: codegen bare-routes only get/put (State) and
            # throw (Exn) — not an arbitrary op of an effect that merely happens
            # to be named State/Exn.  Keying on the effect name alone let a user
            # `effect State<T> { op sneak(...) }` / `effect Exn<E> { op boom }`
            # shadow's bare op pass check and then hard-fail compile (#1147
            # adversarial workflow), the exact desync E217 exists to close.
            # Such a shadow is itself rejected since #1149 (E152); the op-name
            # keying stays as defence in depth behind that gate.
            bare_routable_builtin = (op_info.parent_effect, op_info.name) in (
                ("State", "get"), ("State", "put"), ("Exn", "throw"),
            )
            if (
                not bare_routable_builtin
                and op_info.parent_effect not in self._handled_effects
            ):
                self._error(
                    node,
                    f"Effect operation '{name}' cannot be called bare here; it "
                    f"must be called qualified as "
                    f"'{op_info.parent_effect}.{name}(...)' or performed inside "
                    f"an enclosing 'handle[{op_info.parent_effect}]' block.",
                    rationale=(
                        "A bare (unqualified) op call is lowered to a handler "
                        "clause of an enclosing 'handle' block; with no such "
                        "block in scope, only the built-in State/Exn ops "
                        "(get/put/throw) have a bare host route, so any other "
                        "bare op call has no code to emit and fails compilation."
                    ),
                    fix=(
                        f"Write '{op_info.parent_effect}.{name}(...)' — a host "
                        "effect routes by qualifier — or perform the op inside a "
                        f"'handle[{op_info.parent_effect}] {{ ... }} in {{ ... }}'"
                        " block."
                    ),
                    spec_ref='Chapter 7, Section 7.4 "Performing Effects"',
                    error_code="E217",
                )
            return self._check_op_call(op_info, args, node)

        # Maybe it's an ability operation
        ab_op = self.env.lookup_ability_op(name)
        if ab_op:
            return self._check_ability_op_call(ab_op, args, node)

        # #1307: the name resolves to nothing HERE, but the program does
        # declare it — as a `where` helper of another declaration, which
        # spec §5.8 makes local to its parent.  Reported as its own error
        # rather than E200's warning: E200's instruction ("define it in
        # this file") is false for a name the file already declares, and
        # codegen has no target for the call either way, so accepting the
        # program would be a check-green module that cannot be built.
        owners = self._where_helper_parents.get(name)
        if owners:
            # Each owner arrives ready to read: "'holder'" for a helper of
            # this file, "'phost' in module 'hlib'" for an imported one.
            owner_list = ", ".join(sorted(owners))
            plural = "s" if len(owners) > 1 else ""
            # The two fixes differ in kind, not just in wording: a caller
            # in this file can move into the parent's body, and a caller in
            # another file cannot — its repair is to call the parent it
            # already imports, or to have the module export the helper.
            imported = any("in module" in o for o in owners)
            parents_only = ", ".join(
                sorted(o.split(" in module ")[0] for o in owners)
            )
            if imported:
                repair = (
                    f"Call {parents_only} instead — a module reaches its "
                    f"helpers, an importer reaches the module's public "
                    f"declarations — or, if '{name}' is meant to be shared, "
                    f"lift it out of the `where` block{plural} to a "
                    f"top-level 'public fn {name}(...)' in that module and "
                    f"import it."
                )
            else:
                repair = (
                    f"Call {parents_only} instead, move this call into the "
                    f"body of {parents_only}, or — if '{name}' is meant to "
                    f"be shared — lift it out of the `where` block{plural} "
                    f"to a top-level 'private fn {name}(...)'."
                )
            self._error(
                node,
                f"'{name}' is a where-helper of {owner_list} and is not in "
                f"scope here.",
                rationale="A function declared in a `where` block is local "
                          "to the function that declares it: it is visible "
                          "to that function's body and to its sibling "
                          "helpers, and to nothing else — not to another "
                          "declaration in the same file, and not to a file "
                          "that imports its parent's module.",
                fix=repair,
                spec_ref='Chapter 5, Section 5.8 "Function Visibility"',
                error_code="E178",
            )
            for arg in args:
                self._synth_expr(arg)
            return UnknownType()

        if name in self._ambiguous_import_fn_names:
            # #1304: two imports supply this name, so it denotes none of
            # their declarations, and the E155 at the import is the one
            # error the program owes.  A second error here would only
            # restate it, and could name no remedy of its own: qualifying
            # the call does not lift an E155 (§8.5.2.2).
            for arg in args:
                self._synth_expr(arg)
            return UnknownType()

        # Unresolved — an error (#1513): a call to nothing has no body to
        # compile, so a warning here let `vera check` pass a program code
        # generation then refused.  Name the module when one this file can
        # see declares the function, which is the fix a reader needs.
        # Sorted: a module checker's `_resolved_modules` is built by walking
        # a set of import paths, so its order follows the hash seed.
        declaring = sorted(
            mod.path for mod in self._resolved_modules
            if name in self._module_functions.get(mod.path, {})
        )
        if declaring:
            fix = ("Import it from the module that declares it: "
                   + " or ".join(self._import_line(m, name)
                                 for m in declaring)
                   + ".  A module reached only through another module's "
                     "imports is not visible to this file until it is "
                     "imported here.")
        else:
            fix = (f"Define 'fn {name}(...)' in this file, or import it from "
                   f"the module that declares it with "
                   f"'import <module>({name});' (replace <module> with that "
                   f"module's path, e.g. 'vera.math'); check the spelling "
                   f"too.")
        self._error(
            node,
            f"Unresolved function '{name}'.",
            rationale="A bare call must resolve to a function, effect "
                      "operation, or ability operation in scope; no "
                      "declaration named this could be found, so there is "
                      "no body to call and the program cannot compile.",
            fix=fix,
            spec_ref='Chapter 8, Section 8.5.1 "Bare Calls"',
            error_code="E200",
        )
        # Still synth arg types to find errors within them
        for arg in args:
            self._synth_expr(arg)
        return UnknownType()

    def _check_fn_call_with_info(self, fn_info: FunctionInfo,
                                 args: tuple[ast.Expr, ...],
                                 node: ast.Node, *,
                                 expected: Type | None = None,
                                 ) -> Type | None:
        """Check a call against a known function signature."""
        # Synth arg types.  For non-generic functions pass the declared
        # param type as *expected* so that nested constructors can resolve
        # TypeVars from context (fixes #243).
        arg_types: list[Type | None] = []
        for i, arg in enumerate(args):
            exp: Type | None = None
            if (not fn_info.forall_vars
                    and i < len(fn_info.param_types)):
                pt = fn_info.param_types[i]
                if not contains_typevar(pt):
                    exp = pt
            arg_types.append(self._synth_expr(arg, expected=exp))

        # Arity check
        if len(args) != len(fn_info.param_types):
            self._error(
                node,
                f"Function '{fn_info.name}' expects {len(fn_info.param_types)}"
                f" argument(s), got {len(args)}.",
                rationale="A call must supply exactly one argument per "
                          "declared parameter; the arity does not match the "
                          "function signature.",
                fix=f"Call '{fn_info.name}' with exactly "
                    f"{len(fn_info.param_types)} argument(s) matching its "
                    f"declared parameter types.",
                spec_ref='Chapter 5, Section 5.2 "Function Declaration Syntax"',
                error_code="E201",
            )
            return fn_info.return_type

        # Generic inference
        param_types = fn_info.param_types
        return_type = fn_info.return_type
        type_arg_conflict = False
        if fn_info.forall_vars:
            conflicts: set[str] = set()
            # #1541/#1565: an argument's literals take their type from the
            # call's other arguments, then from the type the result is
            # expected at, and only then from their own values.
            mapping, soft_mapping = self._infer_type_args_in_context(
                fn_info.forall_vars, fn_info.param_types, arg_types, args,
                result_type=fn_info.return_type, expected=expected,
                conflicts=conflicts)
            self._record_literal_soft_result(
                node, substitute(fn_info.return_type, soft_mapping))
            if conflicts:
                # #898: two arguments pinned the same type parameter to
                # different, irreconcilable types (`eq2(MkOk("x"), MkOk(5))`
                # fixes `A` to both `String` and `Int`).  Report the conflict
                # directly — a clear E205 — rather than the misleading
                # "expected Res<String, ...>, got Res<Int, ...>" E202 the
                # partial merge would otherwise emit for one arm.
                type_arg_conflict = True
                # #970 (PR #982 review): ``conflicts`` holds raw callee
                # forall-var names; for a built-in generic these carry the
                # internal namespacing marker (``T#b``).  Strip it so the
                # user-facing message names the parameter as ``T``.
                conflict_names = ", ".join(
                    strip_builtin_typevar_marker(c) for c in sorted(conflicts)
                )
                self._error(
                    node,
                    f"Cannot infer a consistent type for the type "
                    f"parameter(s) {conflict_names} of "
                    f"'{fn_info.name}': different arguments require "
                    f"incompatible types.",
                    rationale="A generic call binds each type parameter to one "
                              "type; when several arguments determine the same "
                              "parameter, they must agree (a sparse "
                              "multi-parameter ADT built from different "
                              "constructors must still name one consistent "
                              "instantiation).",
                    fix="Make the arguments agree on the conflicting type "
                        "parameter, or annotate the intended instantiation "
                        "with a typed slot binding.",
                    spec_ref='Chapter 5, Section 5.2 "Function Declaration Syntax"',
                    error_code="E205",
                )
            # #900: reject instantiating a generic type parameter at the
            # zero-size `Unit` type *when the generic's body reads it*.  Unit
            # is 0 bytes with no WASM representation (spec §11.2.2 / §11.3.1:
            # Unit-returning fns have no result type, and `UnitLit` compiles to
            # nothing), so a monomorphized `forall<T>` body's `@T.n` slot READ
            # lowers to a `local.get` with no local — the dangling-slot codegen
            # invariant (E699).  This closes the inferred (arg-pinned) case at
            # check time rather than letting it crash in codegen, per DESIGN.md
            # principle 1 (checkability over correctness).
            #
            # Narrowed to declarations that actually MATERIALIZE `@T` (a `@T.n`
            # SlotRef read — direct return, match scrutinee, or a `requires` /
            # `ensures` clause, all of which lower to a `local.get`; #939).  A
            # `@T` parameter never read — in the body OR a contract — erases
            # cleanly from the ABI, so `firstInt(@T, @Int){ @Int.0 }` and
            # `ignore(@T){ 0 }` run fine at `T = Unit` and must NOT be rejected
            # (`fn_info.forall_vars_read` is the per-declaration set of forall
            # vars read anywhere that lowers to WASM).
            #
            # Keyed to any type with NO WASM representation — bare `Unit` OR a
            # `Future` transparently wrapping one (`Future<Unit>`; #939 review),
            # via `erases_to_unit` (which mirrors codegen's zero-size erasure).
            # A boxed `Option<Unit>` (tag + pointer) and a `Future<Int>` (i32)
            # both erase to a real local, so both are valid, non-zero-size type
            # arguments.  A genuine built-in generic
            # (`async`, `await`, collection/prelude combinators) has hand-written
            # codegen and an EMPTY `forall_vars_read`, so it never contributes a
            # unit var (`async(IO.print(...))`, a valid `Future<Unit>`, is not an
            # over-reject) — while a USER override of a prelude name that DOES read
            # `@T` (`forall<T> option_map`) is correctly caught, which the old
            # name-based exclusion wrongly skipped.  Skipped when a type-argument
            # conflict already reported E205 (the merged mapping is arbitrary
            # there — mirrors the E202 per-argument loop skip).
            unit_vars = (
                sorted(
                    tv for tv in fn_info.forall_vars
                    if tv in fn_info.forall_vars_read
                    and (b := mapping.get(tv)) is not None
                    and erases_to_unit(b)
                )
                if not type_arg_conflict
                else []
            )
            if unit_vars:
                joined = ", ".join(unit_vars)
                self._error(
                    node,
                    f"Cannot instantiate the type parameter(s) {joined} of "
                    f"'{fn_info.name}' at the zero-size type Unit.",
                    rationale="Unit is a zero-size type with no runtime "
                              "representation (a Unit value occupies 0 bytes "
                              "and compiles to no WASM value), so a generic "
                              "function specialised at Unit has a parameter "
                              "slot that refers to no runtime local — the "
                              "monomorphized function cannot be generated.",
                    fix="Do not pass a Unit-typed value where a generic "
                        "parameter is inferred. If you need to thread a unit "
                        "result through, wrap it in a boxed type (e.g. "
                        "Option<Unit>) or restructure so the generic is "
                        "instantiated at a type with a runtime representation.",
                    spec_ref='Chapter 11, Section 11.2.2 "Unit as Void"',
                    error_code="E206",
                )
                # Return the *substituted* result type so the enclosing
                # context (e.g. `let @Unit = idt(...)`) sees the concrete
                # `Unit` rather than a leaked `@T`, avoiding a misleading
                # cascade error on top of the actionable E206.
                return substitute(return_type, mapping)
            if mapping:
                param_types = tuple(
                    substitute(p, mapping) for p in param_types)
                return_type = substitute(return_type, mapping)
                # #747: the initial synth used expected=None for generic
                # calls, and an @Int argument flowing into a formal fixed
                # to @Nat by inference (`pick(@Nat.0, @Int.0)` with
                # `pick<T>(@T, @T)`) skips the re-synth at the subtype
                # check (Int <: Nat holds).  Record the instantiated
                # formal as each argument's target now, so the verifier's
                # @Nat narrowing walker can obligate it.
                #
                # #1503: except a COMPOSITE argument carrying a pure-literal
                # subtraction at a formal whose instantiation types nothing
                # else in the callee's signature.  `array_length([0 - 1, 5])`
                # infers `T = Nat` from the literal itself, because the
                # checker types `0 - 1` bottom-up as `Nat`; recorded as the
                # literal's target, it has the construction-position element
                # leg (#1440) obligate and guard -1 against it — E503 and a
                # trap on a program whose value is 2.  That instantiation
                # ends at this call: nothing past it is typed by it, so
                # declining it declines no fact anything downstream reads.
                # A formal whose variables reach anything else keeps its
                # target, as a scalar argument does since #747: the result
                # (`array_reverse`, `id`), where the instantiation leaves
                # through the call and is read as a declaration (#1541);
                # and another parameter, which the callee reads at the same
                # instantiation — `array_any`'s callback takes each element
                # as its `@Nat`, so -1 arrived there as 18446744073709551615
                # in a program that verified clean.
                if self.expr_target_types is not None:
                    for index, (c_arg, c_pt) in enumerate(
                            zip(args, param_types)):
                        key = ast.span_key(c_arg)
                        if key is None or contains_typevar(c_pt):
                            continue
                        if (_instantiation_ends_at_formal(fn_info, index)
                                and narrowing.carries_literal_subtraction(
                                    c_arg)
                                and not narrowing.holds_literal_subtraction(
                                    c_arg)):
                            continue
                        self.expr_target_types[key] = c_pt

        # Check each argument.  When a type-argument conflict was already
        # reported (#898), skip the per-argument subtype check: the merged
        # parameter type is one arbitrary arm of the conflict, so re-checking
        # would pile a misleading E202 on top of the clear E205.
        for i, (arg_ty, param_ty) in enumerate(zip(arg_types, param_types)):
            if type_arg_conflict:
                break
            if arg_ty is None or isinstance(arg_ty, UnknownType):
                continue
            if isinstance(param_ty, (TypeVar, UnknownType)):
                continue
            # Re-synth if arg still has unresolved TypeVars (bidirectional)
            if contains_typevar(arg_ty) and not contains_typevar(param_ty):
                arg_ty = self._synth_expr(args[i], expected=param_ty)
                if arg_ty is None or isinstance(arg_ty, UnknownType):
                    continue
                arg_types[i] = arg_ty
            # Re-synth with expected type when subtype check would fail —
            # enables bidirectional coercion (e.g. IntLit → Byte).
            if (not is_subtype(arg_ty, param_ty)
                    and not contains_typevar(param_ty)):
                re = self._synth_expr(args[i], expected=param_ty)
                if re is not None and not isinstance(re, UnknownType):
                    if is_subtype(re, param_ty):
                        arg_ty = re
                        arg_types[i] = re
            # #1541: an argument whose literals the instantiation typed
            # differently from their own values is checked AGAINST that
            # instantiation, so each literal meets the type it now has —
            # a negative one in a `Nat` position is the narrowing it is
            # (E503), and a nested generic call or constructor takes the
            # instantiation as its own context.
            elif (fn_info.forall_vars
                    and not contains_typevar(param_ty)
                    and not types_equal(arg_ty, param_ty)
                    and contains_literal_hole(
                        self._literal_soft_type(args[i], arg_ty)
                        or arg_ty)):
                re = self._synth_expr(args[i], expected=param_ty)
                if (re is not None and not isinstance(re, UnknownType)
                        and is_subtype(re, param_ty)):
                    arg_ty = re
                    arg_types[i] = re
            # #1010: a constructor argument against a PARTIALLY-generic
            # param (`MkPair(0 - 5, None)` as `@Pair<Nat, T>`) was never
            # re-synthesized — every re-synth above is gated on the WHOLE
            # param being typevar-free — so the concrete `Nat` component's
            # narrowing target went unrecorded and the E503 obligation was
            # silently lost (the fully-concrete analogue obligates).
            # Re-synth ctor expressions against the instantiated param:
            # the #971 fill adopts component-wise, typevar components stay
            # unconstrained, and the ctor check records each field's
            # target exactly as on the concrete path.
            if (contains_typevar(param_ty)
                    and isinstance(param_ty, AdtType)
                    and isinstance(args[i], (
                        ast.ConstructorCall, ast.NullaryConstructor))):
                re = self._synth_expr(args[i], expected=param_ty)
                if re is not None and not isinstance(re, UnknownType):
                    arg_ty = re
                    arg_types[i] = re
            if not is_subtype(arg_ty, param_ty):
                # #993: when unresolved variables remain on either side
                # (e.g. `option_unwrap_or(nothing(()), None)` — the callee's
                # instantiation never resolves because every argument is
                # itself polymorphic), a structural match treating type
                # variables as wildcards means the call is satisfiable at
                # SOME instantiation — rejecting it is a false E202.  Fully
                # concrete mismatches are unaffected.
                if ((contains_typevar(arg_ty) or contains_typevar(param_ty))
                        and _compatible_modulo_typevars(
                            arg_ty, param_ty,
                            frozenset(self.env.type_params))):
                    continue
                self._error(
                    args[i],
                    f"Argument {i} of '{fn_info.name}' has type "
                    f"{pretty_inferred_type(arg_ty)}, expected "
                    f"{pretty_type(param_ty)}.",
                    rationale="Each argument's type must be a subtype of the "
                              "corresponding declared parameter type.",
                    fix=f"Pass a value of type {pretty_type(param_ty)} for "
                        f"argument {i}, or convert the current value (e.g. "
                        f"int_to_nat(...), int_to_float(...)) to "
                        f"{pretty_type(param_ty)}.",
                    spec_ref='Chapter 5, Section 5.2 "Function Declaration Syntax"',
                    error_code="E202",
                )

        # Track effects
        if not isinstance(fn_info.effect, PureEffectRow):
            if isinstance(fn_info.effect, ConcreteEffectRow):
                for ei in fn_info.effect.effects:
                    self._effect_ops_used.add(ei.name)

        # #841: concurrency-eligibility warning for async().  The runtime
        # only makes async(e) concurrent when e's effect row stays within
        # the commutative whitelist; anything else evaluates eagerly, and
        # the checker says so rather than letting the program imply
        # concurrency it does not get.
        if fn_info.name == "async" and len(args) == 1:
            self._warn_non_commutative_async(args[0], node)

        # Call-site effect check: callee's effects must be permitted
        # by the caller's context (Spec §7.8 subeffecting).
        if self.env.current_effect_row is not None:
            if not is_effect_subtype(fn_info.effect,
                                     self.env.current_effect_row):
                self._error(
                    node,
                    f"Function '{fn_info.name}' requires "
                    f"{pretty_effect(fn_info.effect)} but call site only "
                    f"allows {pretty_effect(self.env.current_effect_row)}.",
                    rationale="A function can only be called from a context "
                              "that permits all of its declared effects "
                              "(subeffecting).",
                    fix="Either add the missing effects to the calling "
                        "function's effects clause, or handle the effects "
                        "with a handler.",
                    spec_ref='Chapter 7, Section 7.8 "Effect Subtyping"',
                    error_code="E125",
                )

        return return_type

    def _check_apply_fn(self, args: tuple[ast.Expr, ...],
                        node: ast.Node) -> Type | None:
        """Check the apply_fn special form: apply_fn(f, a0, ..., an) (#854).

        Types the call structurally against ``f``'s ``FunctionType`` —
        mirroring :meth:`_check_fn_call_with_info` for a callee whose
        "signature" is the applied value's fn type: arity (E201),
        argument subtyping with bidirectional re-synthesis (E202), and
        the fn type's effect row joining the caller's used effects and
        being checked against the caller's declared row (E122 via
        ``_effect_ops_used`` / E125 here), exactly as a named call with
        that row would.  The call's result is ``f``'s return type.

        A bare-``TypeVar`` first argument (a ``forall``-var-typed value
        with no structural fn type) is unpicked here — the remaining
        arguments are still synthesised for errors within them and the
        call types as ``UnknownType`` (permissive, like other
        unresolvable-generic sites).
        """
        if not args:
            self._error(
                node,
                "apply_fn expects a function value as its first "
                "argument, got no arguments.",
                rationale="apply_fn applies a stored function value: its "
                          "first argument is the function to apply and the "
                          "remaining arguments are passed to it, so a bare "
                          "apply_fn() has nothing to apply.",
                fix="Pass a function value first, then its arguments, "
                    "e.g. apply_fn(@IntToInt.0, 5).",
                spec_ref='Chapter 11, Section 11.10.5 "Closure Invocation (apply_fn)"',
                error_code="E201",
            )
            return UnknownType()

        fn_arg, rest = args[0], args[1:]
        fn_ty_raw = self._synth_expr(fn_arg)

        # Error recovery / unresolvable-generic first argument: synth
        # the remaining arguments (to surface errors inside them) and
        # give up on structural checking.
        fn_ty = base_type(fn_ty_raw) if fn_ty_raw is not None else None
        if fn_ty is None or isinstance(fn_ty, (UnknownType, TypeVar)):
            for arg in rest:
                self._synth_expr(arg)
            return UnknownType()

        if not isinstance(fn_ty, FunctionType):
            self._error(
                fn_arg,
                f"Argument 0 of 'apply_fn' has type "
                f"{pretty_inferred_type(fn_ty_raw or fn_ty)}, expected a function "
                f"value (a fn(...) type).",
                rationale="apply_fn invokes a stored function value via "
                          "call_indirect; a non-function first argument "
                          "has no signature to call.",
                fix="Pass a value of a fn type — a parameter or let "
                    "binding declared with a fn(...) effects(...) type, "
                    "e.g. apply_fn(@IntToInt.0, 5).",
                spec_ref='Chapter 11, Section 11.10.5 "Closure Invocation (apply_fn)"',
                error_code="E202",
            )
            for arg in rest:
                self._synth_expr(arg)
            return UnknownType()

        # Synth applied args against the fn type's formals — bidirectional
        # where the formal is concrete, mirroring plain non-generic calls
        # (this also records the #747 narrowing target for each argument).
        arg_types: list[Type | None] = []
        for i, arg in enumerate(rest):
            exp: Type | None = None
            if i < len(fn_ty.params):
                pt = fn_ty.params[i]
                if not contains_typevar(pt):
                    exp = pt
            arg_types.append(self._synth_expr(arg, expected=exp))

        # Arity: every argument after the function value maps to one
        # parameter of the applied fn type.
        if len(rest) != len(fn_ty.params):
            self._error(
                node,
                f"apply_fn: function value of type {pretty_type(fn_ty)} "
                f"expects {len(fn_ty.params)} argument(s), "
                f"got {len(rest)}.",
                rationale="apply_fn passes every argument after the "
                          "function value to it; the count must match the "
                          "applied function type's parameters.",
                fix=f"Call apply_fn with the function value plus exactly "
                    f"{len(fn_ty.params)} argument(s) matching "
                    f"{pretty_type(fn_ty)}.",
                spec_ref='Chapter 11, Section 11.10.5 "Closure Invocation (apply_fn)"',
                error_code="E201",
            )
            return fn_ty.return_type

        # Check each applied argument (same discipline as named calls:
        # skip unresolved, re-synth for bidirectional coercion).
        for i, (arg_ty, param_ty) in enumerate(zip(arg_types,
                                                   fn_ty.params)):
            if arg_ty is None or isinstance(arg_ty, UnknownType):
                continue
            if isinstance(param_ty, (TypeVar, UnknownType)):
                continue
            # Re-synth if arg still has unresolved TypeVars (bidirectional)
            if contains_typevar(arg_ty) and not contains_typevar(param_ty):
                arg_ty = self._synth_expr(rest[i], expected=param_ty)
                if arg_ty is None or isinstance(arg_ty, UnknownType):
                    continue
                arg_types[i] = arg_ty
            # Re-synth with expected type when subtype check would fail —
            # enables bidirectional coercion (e.g. IntLit → Byte).
            if (not is_subtype(arg_ty, param_ty)
                    and not contains_typevar(param_ty)):
                re = self._synth_expr(rest[i], expected=param_ty)
                if re is not None and not isinstance(re, UnknownType):
                    if is_subtype(re, param_ty):
                        arg_ty = re
                        arg_types[i] = re
            if not is_subtype(arg_ty, param_ty):
                self._error(
                    rest[i],
                    f"Argument {i + 1} of 'apply_fn' has type "
                    f"{pretty_inferred_type(arg_ty)}, expected "
                    f"{pretty_type(param_ty)}.",
                    rationale="Each argument after the function value must "
                              "be a subtype of the corresponding parameter "
                              "of the applied function type.",
                    fix=f"Pass a value of type {pretty_type(param_ty)}, "
                        f"or convert the current value (e.g. "
                        f"int_to_nat(...), int_to_float(...)) to "
                        f"{pretty_type(param_ty)}.",
                    spec_ref='Chapter 11, Section 11.10.5 "Closure Invocation (apply_fn)"',
                    error_code="E202",
                )

        # The applied row joins the caller's used effects and must be
        # permitted by the caller's declared row — exactly as a named
        # call with this row (E122 via _effect_ops_used; E125 here).
        if isinstance(fn_ty.effect, ConcreteEffectRow):
            for ei in fn_ty.effect.effects:
                self._effect_ops_used.add(ei.name)
        if self.env.current_effect_row is not None:
            if not is_effect_subtype(fn_ty.effect,
                                     self.env.current_effect_row):
                self._error(
                    node,
                    f"apply_fn: applied function value requires "
                    f"{pretty_effect(fn_ty.effect)} but call site only "
                    f"allows "
                    f"{pretty_effect(self.env.current_effect_row)}.",
                    rationale="Applying a function value performs its "
                              "type's declared effects; the call site must "
                              "permit all of them (subeffecting), exactly "
                              "as for a named function call.",
                    fix="Add the missing effects to the calling "
                        "function's effects clause, or apply a function "
                        "value whose type is pure.",
                    spec_ref='Chapter 7, Section 7.8 "Effect Subtyping"',
                    error_code="E125",
                )

        return fn_ty.return_type

    # Effects whose operations are value-confluent — reordering their
    # completions cannot change any observable output — so async() may run
    # them concurrently (#841).  ``Async`` itself is a marker effect with
    # no operations, so it cannot order anything either.
    _ASYNC_COMMUTATIVE: frozenset[str] = frozenset({"Http", "Async"})

    def _warn_non_commutative_async(self, arg: ast.Expr,
                                    node: ast.Node) -> None:
        """Warn (W002) when async()'s argument performs effects outside
        the commutative whitelist — such futures evaluate eagerly."""
        found: set[str] = set()
        self._collect_expr_effects(arg, found)
        outside = sorted(found - self._ASYNC_COMMUTATIVE)
        if outside:
            self._error(
                node,
                f"async argument performs {', '.join(outside)} effects, "
                f"which are outside the commutative set "
                f"({', '.join(sorted(self._ASYNC_COMMUTATIVE - {'Async'}))}); "
                f"it evaluates eagerly (sequentially) at the async() site.",
                rationale="Concurrent evaluation is only observably "
                          "equivalent to eager evaluation when the "
                          "argument's effects commute; for any other "
                          "effect row the implementation preserves program "
                          "order by evaluating eagerly, and warns so the "
                          "program does not imply concurrency it does not "
                          "get.",
                fix="Restrict the async argument to commutative effects "
                    "(e.g. a direct Http.get/Http.post call), or drop the "
                    "async() wrapper if eager evaluation is intended.",
                spec_ref='Chapter 9, Section 9.5.4 "Async"',
                severity="warning",
                error_code="W002",
            )

    def _collect_expr_effects(self, node: ast.Node,
                              acc: set[str]) -> None:
        """Conservatively collect the effect names an expression may
        perform: effect-op calls contribute their parent effect, function
        calls contribute the callee's declared row, and anything that
        cannot be resolved contributes an opaque marker (never silently
        commutative)."""
        import dataclasses as _dc

        if isinstance(node, ast.QualifiedCall):
            if self.env.lookup_effect(node.qualifier) is not None:
                acc.add(node.qualifier)
            else:
                # Cross-module function call — its row is not resolvable
                # from this mixin; conservatively non-commutative.
                acc.add(f"<{node.qualifier}.{node.name}>")
        elif isinstance(node, ast.FnCall):
            # #991: resolve lexically like the call checker above, so a
            # same-named helper in a sibling tree can't contribute the
            # WRONG effect row to the commutativity analysis.
            #
            # #1284: and DECLARATIONS FIRST, which is the rest of what "like
            # the call checker above" means — this walk asked
            # `lookup_effect_op` first, so a user function named after a
            # built-in operation contributed the OPERATION's parent effect
            # instead of its own declared row.  Wrong in both directions and
            # both measured: a PURE `fn get` in a program containing no
            # State at all drew `[W002] async argument performs State
            # effects`, and a `fn get` performing IO under a row naming
            # `Http` first drew NO warning, because `Http` is inside the
            # commutative whitelist and the operation is what the walk
            # thought it had found.  Same predicate as the resolution at the
            # top of this file, so the analysis reasons about the row the
            # checker actually bound.
            fn_info = (
                self._lookup_function_scoped(node.name)
                if bare_call_denotes_user_fn(node.name, self._user_fn_names)
                else None
            )
            op_info = (
                self.env.lookup_effect_op(node.name)
                if fn_info is None else None
            )
            if op_info is not None:
                acc.add(op_info.parent_effect)
            elif fn_info is None:
                acc.add(f"<{node.name}>")
            elif isinstance(fn_info.effect, ConcreteEffectRow):
                for ei in fn_info.effect.effects:
                    acc.add(ei.name)
            elif not isinstance(fn_info.effect, PureEffectRow):
                acc.add(f"<{node.name}>")
        for field in _dc.fields(node):
            value = getattr(node, field.name)
            if isinstance(value, ast.Node):
                self._collect_expr_effects(value, acc)
            elif isinstance(value, tuple):
                for item in value:
                    if isinstance(item, ast.Node):
                        self._collect_expr_effects(item, acc)

    def _check_op_call(self, op_info: OpInfo,
                       args: tuple[ast.Expr, ...],
                       node: ast.Node) -> Type | None:
        """Check a call to an effect operation."""
        # Resolve type params from the current effect context first, so
        # each argument is synthesised against its *instantiated* formal.
        # That records the @Nat target for an ``E<Nat>.op(@Int.0)``
        # narrowing in the #747 side-table (uniform with plain calls and
        # constructor fields) rather than leaving it unchecked.
        mapping = self._effect_type_mapping(op_info.parent_effect)
        param_types = tuple(substitute(p, mapping) for p in op_info.param_types)
        return_type = substitute(op_info.return_type, mapping)

        arg_types: list[Type | None] = []
        for i, arg in enumerate(args):
            exp = param_types[i] if i < len(param_types) else None
            arg_types.append(self._synth_expr(arg, expected=exp))

        if len(args) != len(param_types):
            self._error(
                node,
                f"Effect operation '{op_info.name}' expects "
                f"{len(param_types)} argument(s), got {len(args)}.",
                rationale="An effect operation is called like a function and "
                          "must receive exactly the number of arguments "
                          "declared in its 'op' signature.",
                fix=f"Call '{op_info.name}' with exactly {len(param_types)} "
                    f"argument(s) matching the 'op' declaration in its "
                    f"effect.",
                spec_ref='Chapter 7, Section 7.4 "Performing Effects"',
                error_code="E203",
            )
            return return_type

        for i, (arg_ty, param_ty) in enumerate(zip(arg_types, param_types)):
            if arg_ty is None or isinstance(arg_ty, UnknownType):
                continue
            if isinstance(param_ty, (TypeVar, UnknownType)):
                continue
            if not is_subtype(arg_ty, param_ty):
                self._error(
                    args[i],
                    f"Argument {i} of '{op_info.name}' has type "
                    f"{pretty_inferred_type(arg_ty)}, expected "
                    f"{pretty_type(param_ty)}.",
                    rationale="Each argument to an effect operation must be a "
                              "subtype of the parameter type declared in its "
                              "'op' signature.",
                    fix=f"Pass a value of type {pretty_type(param_ty)} for "
                        f"argument {i} of '{op_info.name}', or convert the "
                        f"current value to {pretty_type(param_ty)}.",
                    spec_ref='Chapter 7, Section 7.4 "Performing Effects"',
                    error_code="E204",
                )

        # #309: for a DB SQL op (``DB.query`` / ``DB.execute``), the SQL (first)
        # argument must be literal-provenance (E207), use only anonymous ``?``
        # placeholders (E209), and match a statically-sized params array (E208).
        # ``is_db_sql_op`` matches on ``parent_effect == "DB"`` + the op name —
        # the SAME axis codegen routes to the host database on — NOT built-in
        # OpInfo identity.
        #
        # Historically that distinction decided WHERE a user ``effect DB``
        # shadow was caught: one declaring ``query`` was gated here, while one
        # declaring only some other op failed op resolution and was gated by
        # the spelling fallback in ``_check_qualified_call`` (Cortex #1147
        # Finding 1).  Since #1149 no shadow enters the registry at all (E152),
        # so every ``DB.query`` / ``DB.execute`` resolves against the built-in
        # and arrives here; the fallback is retained only as defence in depth
        # should the registry ever fail to resolve one.  The routing-axis key
        # is likewise kept rather than narrowed to the built-in ``OpInfo``: the
        # gate must cover exactly what codegen emits on its own terms, without
        # depending on E152 to be complete.
        #
        # The gate runs on the codegen routing axis ALONE — it does NOT also
        # require the arg's static type to be ``String``.  Codegen marshals the
        # first arg to the sqlite host by qualifier name whatever its type, so an
        # ``is_subtype(arg, String)`` guard was a soundness hole (#1147
        # adversarial workflow): a runtime SQL string laundered through a generic
        # ``@T`` slot has arg type ``TypeVar`` (SEVERE — attacker SQL executed),
        # and a user ``effect DB`` shadow with a non-``String`` param (``Int`` /
        # ``Array``) type-checks clean yet still reaches the host (a check-clean
        # program emitting invalid WASM).  The provenance walker is
        # conservative-reject, so it correctly rejects a slot / non-literal arg of
        # ANY type.  The one thing we skip is pure E204 cascade: a call whose
        # DECLARED first param is exactly ``String`` already rejected a concrete
        # non-``String`` arg with E204, so a second E207 there is noise.  A
        # ``TypeVar`` param (generic ``DB<T>``) or a user non-``String`` param
        # does NOT fire E204, so those still gate.  (Both shadow shapes in that
        # paragraph are the pre-#1149 world: the block is now E152, so a
        # non-``String`` SQL argument is a plain E204 against the built-in's
        # ``String`` parameter.)
        if (
            self.env.is_db_sql_op(op_info) and args
            and arg_types and arg_types[0] is not None
            and not isinstance(arg_types[0], UnknownType)
        ):
            arg0 = arg_types[0]
            param0 = param_types[0] if param_types else None
            param_is_string = (
                param0 is not None
                and is_subtype(param0, STRING)
                and is_subtype(STRING, param0)
            )
            e204_cascade = param_is_string and not is_subtype(arg0, STRING)
            if not e204_cascade:
                self._check_sql_provenance(op_info.name, args, node)

        return return_type

    def _check_sql_provenance(
        self, op_name: str, args: tuple[ast.Expr, ...], node: ast.Node,
    ) -> None:
        """#309 — reject a non-literal SQL string (E207); numbered/named
        placeholders Vera does not support (E209); and a placeholder/param
        arity mismatch when both are statically sized (E208).

        ``op_name`` is the operation spelling (``query`` / ``execute``) used only
        in diagnostics — a string, not an ``OpInfo``, so the unresolved-spelling
        path (``_check_qualified_call``, Cortex #1147 Finding 1) can gate a
        ``DB.<op>`` call that codegen routes to the host even though a user
        ``effect DB`` never declared the op."""
        if not args:
            return
        sql = resolve_literal_string(args[0], self.env, self._slot_ref_key)
        if sql is None:
            self._error(
                args[0],
                f"The SQL argument to '{op_name}' must be a string "
                "literal or a concatenation of literals, not a runtime-derived "
                "value.",
                rationale=(
                    "A SQL string assembled from a runtime value — a slot, a "
                    "function result, or a \\(expr) interpolation — is the SQL "
                    "injection vector.  Vera makes it a compile-time error: the "
                    "query text is fixed at compile time and all runtime data "
                    "flows through the ? placeholders and the params array."
                ),
                fix=(
                    "Put the runtime value in the params array and reference "
                    "it with a ? placeholder, e.g. "
                    'DB.query("SELECT ... WHERE x = ?", [Some(value)]).'
                ),
                spec_ref='Chapter 9, Section 9.5.7 "DB"',
                error_code="E207",
            )
            return

        # SQL is literal.  ``count_placeholders`` returns None when the SQL uses
        # a numbered (``?NNN``) or named (``:name`` / ``@name`` / ``$name``)
        # placeholder.  Vera's params argument is a POSITIONAL ``Array``, so only
        # anonymous ``?`` has a well-defined binding; the others fail against a
        # positional sequence at run time.  Reject them at compile time (E209)
        # for one canonical placeholder form, rather than defer to a runtime
        # error.
        want = count_placeholders(sql)
        if want is None:
            self._error(
                node,
                f"The SQL passed to '{op_name}' uses a numbered (?NNN) or named "
                "(:name / @name / $name) placeholder; Vera supports only "
                "anonymous '?' placeholders.",
                rationale=(
                    "Parameters bind positionally through the "
                    "Array<Option<String>> params argument, so only anonymous "
                    "'?' placeholders have a well-defined binding; numbered and "
                    "named forms fail against a positional sequence at run time."
                ),
                fix=(
                    "Use anonymous '?' placeholders in order, e.g. "
                    'DB.query("SELECT ... WHERE a = ? AND b = ?", '
                    "[Some(a), Some(b)])."
                ),
                spec_ref='Chapter 9, Section 9.5.7 "DB"',
                error_code="E209",
            )
            return

        # Anonymous ? only: arity-check against a statically-sized params array.
        # ``resolve_array_len`` follows a ``let`` chain (#1160), so a params
        # array written literally is checked whether it is inline at the call
        # site or bound to a slot first.  It returns None when the length is not
        # statically known, deferring the count to the sqlite3 host.
        got = (resolve_array_len(args[1], self.env, self._slot_ref_key)
               if len(args) >= 2 else None)
        if got is not None:
            if want != got:
                self._error(
                    node,
                    f"The SQL has {want} '?' placeholder(s) but "
                    f"{got} parameter(s) were supplied to '{op_name}'.",
                    rationale=(
                        "Each ? placeholder binds one positional parameter, so "
                        "the number of placeholders must equal the length of "
                        "the params array; a mismatch fails at run time."
                    ),
                    fix=(
                        f"Supply exactly {want} parameter(s) to match the "
                        f"{want} placeholder(s), or adjust the SQL's ? count."
                    ),
                    spec_ref='Chapter 9, Section 9.5.7 "DB"',
                    error_code="E208",
                )

    def _effect_type_mapping(self, effect_name: str) -> dict[str, Type]:
        """Get the type argument mapping for an effect — innermost enclosing
        HANDLER first (#1203 determinism: an op inside nested same-name
        handlers resolves against the governing handler's instantiation,
        §7.5.2), then the current effect row IN SOURCE ORDER.

        The row leg used to iterate the row's ``frozenset`` on the premise
        that a declared row cannot meaningfully carry two instantiations of
        one effect.  Spec §7.3.3 says otherwise — ``effects(<State<Int>,
        State<Bool>>)`` is two independent cells — and such a row made a bare
        ``get``'s type a function of PYTHONHASHSEED: the same source checked
        clean on some interpreter starts and failed E121 (`body has type Bool,
        expected Int`) on others.  It now walks `ordered_effect_row()`, the
        same ordered candidate list bare op-NAME resolution uses (#1215), so
        the first instantiation written in the row governs."""
        eff_info = self.env.lookup_effect(effect_name)
        if eff_info is None or not eff_info.type_params:
            return {}
        for inst in reversed(self._handled_effect_insts):
            if inst.name == effect_name and inst.type_args:
                return dict(zip(eff_info.type_params, inst.type_args))
        for ei in self.env.ordered_effect_row():
            if ei.name == effect_name and ei.type_args:
                return dict(zip(eff_info.type_params, ei.type_args))
        return {}

    # -----------------------------------------------------------------
    # Ability operations
    # -----------------------------------------------------------------

    def _check_ability_op_call(self, op_info: OpInfo,
                               args: tuple[ast.Expr, ...],
                               node: ast.Node) -> Type | None:
        """Check a call to an ability operation."""
        arg_types: list[Type | None] = []
        for arg in args:
            arg_types.append(self._synth_expr(arg))

        # Build type mapping from ability params → concrete types
        mapping = self._ability_type_mapping(op_info, arg_types)
        param_types = tuple(
            substitute(p, mapping) for p in op_info.param_types)
        return_type = substitute(op_info.return_type, mapping)

        if len(args) != len(param_types):
            self._error(
                node,
                f"Ability operation '{op_info.name}' expects "
                f"{len(param_types)} argument(s), got {len(args)}.",
                rationale="An ability operation is called like a function and "
                          "must receive exactly the number of arguments "
                          "declared in its 'op' signature.",
                fix=f"Call '{op_info.name}' with exactly {len(param_types)} "
                    f"argument(s) matching the 'op' declaration in its "
                    f"ability.",
                spec_ref='Chapter 9, Section 9.8 "Abilities"',
                error_code="E240",
            )
            return return_type

        for i, (arg_ty, param_ty) in enumerate(
                zip(arg_types, param_types)):
            if arg_ty is None or isinstance(arg_ty, UnknownType):
                continue
            if isinstance(param_ty, (TypeVar, UnknownType)):
                continue
            if not is_subtype(arg_ty, param_ty):
                # #993: the args were synthesized with no expected type, so
                # a bare constructor argument (`eq(x, None)`) minted a fresh
                # ctor var that never met the parameter type.  Re-synth the
                # ctor argument against the resolved param so the #971
                # bidirectional fill can adopt it (works for concrete AND
                # rigid-forall-var parameter args).  Restricted to
                # constructor expressions — re-synthesizing an arbitrary
                # expression could re-emit its own diagnostics — and to a
                # fresh-FREE param: a param still carrying a `$` hole
                # (`eq(None, None)`) is not a resolved type to adopt, and
                # adopting it would let an unresolvable comparison through.
                if (contains_typevar(arg_ty)
                        and not contains_fresh_typevar(param_ty)
                        and isinstance(args[i], (
                            ast.ConstructorCall, ast.NullaryConstructor))):
                    resynth = self._synth_expr(args[i], expected=param_ty)
                    if (resynth is not None
                            and not isinstance(resynth, UnknownType)):
                        arg_ty = resynth
                        arg_types[i] = resynth
                        if is_subtype(arg_ty, param_ty):
                            continue
                self._error(
                    args[i],
                    f"Argument {i} of '{op_info.name}' has type "
                    f"{pretty_inferred_type(arg_ty)}, expected "
                    f"{pretty_type(param_ty)}.",
                    rationale="Each argument to an ability operation must be a "
                              "subtype of the parameter type declared in its "
                              "'op' signature, after the ability's type "
                              "variable is instantiated.",
                    fix=f"Pass a value of type {pretty_type(param_ty)} for "
                        f"argument {i} of '{op_info.name}', or ensure the "
                        f"ability's type variable resolves to a type that "
                        f"accepts {pretty_inferred_type(arg_ty)}.",
                    spec_ref='Chapter 9, Section 9.8 "Abilities"',
                    error_code="E241",
                )

        # #921: `Ord`'s `compare` is the ability spelling of the three-way
        # `Ordering` if-chain `a < b ? Less : (a == b ? Equal : Greater)`
        # (§6.4).  Ordering (`<`/`>`/`<=`/`>=`) is defined ONLY on the
        # orderable primitives — Int, Nat, Float64, Byte, String (§4.5) — and
        # `Ord`'s "Satisfied by:" set is exactly those (§9.8.1); ADTs are NOT
        # Ord-derivable in v0.1.0 (unlike Eq/Hash/Show, whose "Satisfied by:"
        # clauses list composite types).  Without this gate, `compare` on a
        # user ADT type-checks (its `op` param is a bare type variable), then
        # codegen lowers `<` to a scalar `i32.lt_s` on the boxed heap pointers
        # — a SILENT WRONG RESULT — and the verifier raw-`<`es two Z3
        # datatypes and crashes.  Rejecting here, the single gate both codegen
        # and the verifier trust, keeps all three in agreement (checkability
        # over silent miscompilation; DESIGN.md §"Checkability").  The direct
        # `MkBox(1) < MkBox(2)` form is already rejected with E143.
        if op_info.parent_effect == "Ord":
            for i, arg_ty in enumerate(arg_types):
                if arg_ty is None or isinstance(arg_ty, UnknownType):
                    continue
                arg_base = base_type(arg_ty)
                # A bare type variable is deferred: inside a
                # `forall<T where Ord<T>>` body the `Ord<T>` constraint
                # promises orderability, and the monomorphizer's E613 constraint
                # gate re-checks each concrete instantiation against the
                # orderable set (`_ORD_TYPES` in codegen/monomorphize.py).  Any
                # non-Ord instantiation — a user ADT OR `Bool` (§4.5 orders
                # neither) — trips E613 there, so deferring here can never
                # silently miscompile.  (PR #929 review closed a hole: `Bool`
                # was wrongly IN `_ORD_TYPES`, so `Ord<Bool>` satisfied the gate
                # and the clone lowered `compare` on two Bool i32s to a signed
                # `i32.lt_s` — a silent order.  Bool is now out of that set.)
                # Rejecting the TypeVar here would break the legitimate
                # constrained-generic form (ch09_abilities `cmp_sign`).
                if isinstance(arg_base, TypeVar):
                    continue
                if arg_base not in ORDERABLE_TYPES:
                    self._error(
                        args[i],
                        f"'{op_info.name}' requires an orderable operand, "
                        f"found {pretty_inferred_type(arg_ty)}.",
                        rationale=(
                            "The Ord ability's 'compare' operation is the "
                            "three-way spelling of the ordering operators "
                            "(<, >, <=, >=), which are defined only on the "
                            "orderable types — Int, Nat, Float64, Byte, and "
                            "String. A user-defined ADT is not Ord-derivable, "
                            "so it has no total order to compare by."
                        ),
                        fix=(
                            f"Apply '{op_info.name}' to an orderable value "
                            "(e.g. Int, Nat, Float64, Byte, String); reduce a "
                            "non-orderable type to an orderable key first, or "
                            "use 'eq' for structural equality on an ADT."
                        ),
                        spec_ref='Chapter 9, Section 9.8.1 "Built-in Abilities"',
                        error_code="E242",
                    )

        # #928: `Eq`'s `eq` is the ability spelling of `==` (§9.8.1), so it
        # inherits the same Eq-derivability requirement.  Without this gate the
        # `eq(fn, fn)` / `eq(map_composite, map_composite)` forms type-check
        # (the `op` params are bare type variables) and then codegen silently
        # pointer-compares them — the exact silent miscompile the `==` binop
        # gate (`_check_eq_ability`) closes, reached through the ability-op
        # surface instead.  Route both through the one predicate so the checker
        # rejects exactly what codegen cannot derive (the #928 differential).
        if op_info.parent_effect == "Eq":
            for i, arg_ty in enumerate(arg_types):
                if arg_ty is None or isinstance(arg_ty, UnknownType):
                    continue
                # A bare/nested type variable is deferred to the caller's
                # `Eq<T>` constraint + the codegen E613 instantiation gate,
                # exactly as the Ord arm above and the `==` binop gate do —
                # `_check_eq_ability` short-circuits on `contains_typevar`.
                self._check_eq_ability(args[i], arg_ty, arg_ty)

        return return_type

    def _ability_type_mapping(
        self, op_info: OpInfo,
        arg_types: list[Type | None],
    ) -> dict[str, Type]:
        """Infer ability type parameter mapping from argument types.

        For ``ability Eq<A>`` with ``op eq(A, A -> Bool)``, if called as
        ``eq(x, y)`` where ``x: Int``, maps ``A → Int``.
        """
        ab_info = self.env.abilities.get(op_info.parent_effect)
        if not ab_info or not ab_info.type_params:
            return {}
        mapping: dict[str, Type] = {}
        for param_ty, arg_ty in zip(op_info.param_types, arg_types):
            if arg_ty is None or isinstance(arg_ty, UnknownType):
                continue
            if (isinstance(param_ty, TypeVar)
                    and param_ty.name in ab_info.type_params):
                # #993 (PR #1009 review): first-arg-wins locked the mapping
                # onto a bare ctor's fresh var — `eq(None, Some(5))` bound
                # A := Option<T$1> and the concrete second argument could
                # never re-anchor it.  A later fresh-FREE candidate
                # overrides a fresh-containing tentative one (the #293
                # precedence); `eq(None, None)` keeps its fresh binding and
                # stays rejected.
                existing = mapping.get(param_ty.name)
                if existing is None or (
                        contains_fresh_typevar(existing)
                        and not contains_fresh_typevar(arg_ty)):
                    mapping[param_ty.name] = arg_ty
        return mapping

    # -----------------------------------------------------------------
    # Constructors
    # -----------------------------------------------------------------

    def _import_line(self, mod_path: tuple[str, ...], name: str) -> str:
        """The import line that brings *name* in from *mod_path* (#1513).

        When this file already imports that module selectively, the line
        is that import with *name* added to its list, so following the fix
        leaves one import of the module rather than a second declaration
        beside the first.
        """
        label = ".".join(mod_path)
        existing = self._import_names.get(mod_path)
        names = sorted(existing | {name}) if existing else [name]
        return f"'import {label}({', '.join(names)});'"

    def _stranger_constructor(
        self, name: str,
    ) -> tuple[list[tuple[tuple[str, ...], ConstructorInfo]],
               ConstructorInfo | None]:
        """Resolve a constructor of a type this file does not import (#1513).

        Importing a data type is what brings its constructors into scope
        (§8.3.3, §8.4.2), so a constructor whose type reaches this file only
        through another declaration's signature — `paint(Green)`, with
        `Colour` imported by `paint`'s module and not by this file — is not
        in the environment.  It still denotes exactly one declaration when
        one module's PUBLIC type declares it, and code generation compiles
        it (`_namespace_ctor_projection`'s fallback class, which asks the
        same question of the same modules).

        Returns every module whose public types declare *name*, sorted by
        path, and the one constructor the name denotes, or
        ``None`` when it denotes no single declaration.  It denotes one only
        when exactly one module declares it and its type is one
        `_stranger_data_type` resolves: a value of it is typed by the bare
        type name, so a second meaning of that name would let one value pass
        for another type's.

        A construction and a pattern resolve through here alike, so a
        pattern is typed by the same declaration: its fields bind at their
        declared types, and its match is judged against that type's
        constructors.
        """
        # Sorted by path: a module checker's `_resolved_modules` is built by
        # walking a set of import paths, so its order follows the hash seed.
        candidates = sorted(
            ((mod.path, self._module_constructors[mod.path][name])
             for mod in self._resolved_modules
             if name in self._module_constructors.get(mod.path, {})),
            key=lambda pair: pair[0],
        )
        if len(candidates) != 1:
            return candidates, None
        ci = candidates[0][1]
        if self._stranger_data_type(ci.parent_type) is None:
            return candidates, None
        return candidates, ci

    def _stranger_data_type(self, type_name: str) -> AdtInfo | None:
        """The declaration a data type name this file does not import
        denotes (#1513), or ``None``.

        A value of such a type reaches the file through an imported
        signature (`pick(1)` returning `mb`'s `Colour`), typed by the bare
        name.  The name denotes one declaration only when no data type of
        that name is declared or imported here — the prelude's own does not
        count (#1559) — and exactly one module this file can see declares a
        type of that name, public or private: two would give one bare name
        two types.  The pattern rules
        read it for such a value: which constructors a match on it must
        cover, and which ones can match it at all.
        """
        # A type the file declares or imports bars it; the prelude's own
        # type of the name does not (#1559).  Every file holds `Json`,
        # `Request` and the prelude's other types, so counting them refused
        # every constructor of a module's type named like one: `mk(1)`,
        # returning `a`'s `Json`, was accepted while `MyK(1)`, building the
        # same value, was an error.  Such a value meets the prelude's type
        # by the bare name in this file whichever way it arrives (#1560), so
        # barring the construction guarded nothing.
        bound = self.env.data_types.get(type_name)
        if (bound is not None
                and bound is not self._builtin_data_types.get(type_name)):
            return None
        declared = [
            types[type_name]
            for _path, types in sorted(self._module_all_data_types.items())
            if type_name in types
        ]
        if len(declared) != 1:
            return None
        return declared[0]

    def _unknown_ctor_fix(
        self, name: str,
        candidates: list[tuple[tuple[str, ...], ConstructorInfo]],
    ) -> str:
        """The fix for a constructor name that denotes no declaration here."""
        if not candidates:
            return (f"Declare '{name}' as a constructor of a 'data' type in "
                    f"this file, or import the data type that declares it "
                    f"with 'import <module>(<Type>);' — importing a data "
                    f"type is what makes its constructors available (check "
                    f"the spelling and capitalisation too).")
        imports = " or ".join(
            self._import_line(path, ci.parent_type)
            for path, ci in candidates
        )
        return (f"Import the data type that declares '{name}': {imports}.  "
                f"Importing a data type is what makes its constructors "
                f"available; if more than one module declares '{name}', "
                f"import the type of the one you mean.")

    # The stranger-constructor warning's text (#1513), shared by E210 and
    # E214 in a construction and E320 and E322 in a pattern, whose `_error`
    # calls each carry their code as a literal so the warning-site scans
    # (`check_diagnostic_fields.py`, the doc gate's plant table,
    # `test_warning_severity_1513.py`) can read it.
    _STRANGER_CTOR_RATIONALE = (
        "Importing a data type is what brings its constructors into scope.  "
        "This one reaches the file only through another declaration's "
        "signature; the name denotes exactly one declaration, so the program "
        "compiles, but the file does not say where it comes from."
    )

    def _stranger_ctor_message(
        self, name: str, ci: ConstructorInfo,
        candidates: list[tuple[tuple[str, ...], ConstructorInfo]],
    ) -> tuple[str, str]:
        """The description and fix of the stranger-constructor warning."""
        mod_path = candidates[0][0]
        mod_label = ".".join(mod_path)
        line = self._import_line(mod_path, ci.parent_type)
        if self._import_names.get(mod_path):
            fix = (f"Add '{ci.parent_type}' to this file's import of "
                   f"'{mod_label}': {line}.")
        else:
            fix = f"Add the import: {line}."
        return (
            f"Constructor '{name}' belongs to data type '{ci.parent_type}' "
            f"of module '{mod_label}', which this file does not import.",
            fix,
        )

    def _check_constructor_call(self, expr: ast.ConstructorCall, *,
                                expected: Type | None = None) -> Type | None:
        """Type-check a constructor call: Ctor(args)."""
        # Tuple is a variadic built-in constructor — handle specially
        if expr.name == "Tuple":
            return self._check_tuple_constructor(expr)

        ci = self.env.lookup_constructor(expr.name)
        if ci is None and expr.name in self._refused_ctor_names:
            # #1497: a constructor of a declaration refused as E158, whose
            # E158 is the one error the program owes.
            for arg in expr.args:
                self._synth_expr(arg)
            return UnknownType()
        if ci is None:
            candidates, ci = self._stranger_constructor(expr.name)
            if ci is not None:
                message, fix = self._stranger_ctor_message(
                    expr.name, ci, candidates)
                self._error(
                    expr, message,
                    rationale=self._STRANGER_CTOR_RATIONALE,
                    fix=fix,
                    severity="warning",
                    spec_ref='Chapter 8, Section 8.5.4 '
                             '"Constructor Resolution"',
                    error_code="E210",
                )
        if ci is None:
            self._error(
                expr,
                f"Unknown constructor '{expr.name}'.",
                rationale="A constructor call must name a constructor declared "
                          "by a 'data' type in scope; no such constructor is "
                          "defined or imported, so the call has no value to "
                          "build and the program cannot compile.",
                fix=self._unknown_ctor_fix(expr.name, candidates),
                spec_ref='Chapter 2, Section 2.4 "Algebraic Data Types (ADTs)"',
                error_code="E210",
            )
            for arg in expr.args:
                self._synth_expr(arg)
            return UnknownType()

        # Build expected-type mapping for bidirectional inference
        expected_mapping: dict[str, Type] = {}
        if (isinstance(expected, AdtType)
                and ci.parent_type_params
                and expected.name == ci.parent_type
                and len(expected.type_args) == len(ci.parent_type_params)):
            for tv, exp_arg in zip(ci.parent_type_params,
                                   expected.type_args):
                if not isinstance(exp_arg, TypeVar):
                    expected_mapping[tv] = exp_arg

        # Compute field types with expected-type substitution so we can
        # pass them as expected to nested constructor args (e.g. Some(None))
        field_types_for_expected: tuple[Type, ...] | None = None
        if ci.field_types is not None and expected_mapping:
            field_types_for_expected = tuple(
                substitute(ft, expected_mapping) for ft in ci.field_types)

        # Synth arg types, passing resolved field type as expected
        arg_types: list[Type | None] = []
        for i, arg in enumerate(expr.args):
            field_expected: Type | None = None
            if field_types_for_expected and i < len(field_types_for_expected):
                ft = field_types_for_expected[i]
                if not contains_typevar(ft):
                    field_expected = ft
                elif isinstance(
                    arg, (ast.ConstructorCall, ast.NullaryConstructor)
                ):
                    # #979: a NESTED constructor argument whose expected field
                    # type still carries the declared forall var (`Some(None)`
                    # where the field resolves to `Option<T>`) must receive that
                    # expected type so its OWN bidirectional fill can adopt the
                    # declared var — otherwise the inner ctor mints an unrelated
                    # `T$n` and the well-typed program is rejected (E121/E170/
                    # E302).  Feeding a typevar-bearing expected is safe ONLY
                    # into a nested constructor: `_ctor_result_type`'s per-level
                    # `expected.name == ci.parent_type` guard means the inner
                    # ctor adopts a var solely from ITS OWN parent's declared
                    # position, so two ADTs sharing a param name still cannot
                    # cross-contaminate (an inner ctor of a different parent
                    # sees a name mismatch, mints fresh, and the field-type
                    # check then rejects the genuinely ill-typed nesting).
                    field_expected = ft
            arg_types.append(self._synth_expr(arg, expected=field_expected))

        if ci.field_types is None:
            if expr.args:
                self._error(
                    expr,
                    f"Constructor '{expr.name}' is nullary but was given "
                    f"{len(expr.args)} argument(s).",
                    rationale="A constructor declared with no fields takes no "
                              "arguments and must be used as a bare name.",
                    fix=f"Use the constructor without parentheses: "
                        f"'{expr.name}' instead of '{expr.name}(...)'.",
                    spec_ref='Chapter 2, Section 2.4 "Algebraic Data Types (ADTs)"',
                    error_code="E211",
                )
            return self._ctor_result_type(ci, arg_types, expected=expected,
                                          args=expr.args)

        if len(expr.args) != len(ci.field_types):
            self._error(
                expr,
                f"Constructor '{expr.name}' expects "
                f"{len(ci.field_types)} field(s), got {len(expr.args)}.",
                rationale="A constructor call must supply exactly one argument "
                          "per declared field; the count does not match the "
                          "'data' declaration.",
                fix=f"Call '{expr.name}' with exactly {len(ci.field_types)} "
                    f"argument(s), one per field in its 'data' declaration.",
                spec_ref=(
                    'Chapter 2, Section 2.4 "Algebraic Data Types (ADTs)"'
                ),
                error_code="E212",
            )
            return self._ctor_result_type(ci, arg_types, expected=expected,
                                          args=expr.args)

        # Infer type args for parameterised ADTs from arg types — a
        # literal argument taking its type from the other fields, then from
        # the expected type, then from its own value (#1541).
        soft: dict[str, Type] = {}
        mapping = self._infer_ctor_type_args(ci, arg_types, args=expr.args,
                                             expected=expected, soft_out=soft)
        self._record_literal_soft_result(expr, AdtType(ci.parent_type, tuple(
            soft.get(tv, TypeVar(tv))
            for tv in ci.parent_type_params or ())))

        # Merge expected-type mapping for unresolved vars
        for tv, exp_ty in expected_mapping.items():
            if tv not in mapping:
                mapping[tv] = exp_ty

        field_types = ci.field_types
        if mapping:
            field_types = tuple(substitute(ft, mapping) for ft in field_types)

        # #747, at the constructor door: record each argument's INSTANTIATED
        # field type as its target, whatever the expected type came from.
        # The generic FUNCTION call has recorded this since #747 and the
        # constructor never did, so a field type the checker knows only after
        # inference was invisible to the verifier's narrowing walk, which
        # consults this table whenever the DECLARED field type is a TypeVar.
        #
        # Two shapes measured silent because of it, both with the guard
        # emitted and nothing on the record:
        #
        # * `match Some(0 - 5) { Some(@Nat) -> … }` — the checker infers
        #   `T = Nat` from the argument (`0 - 5` is two non-negative literals,
        #   so `Nat - Nat`), types the construction `Option<Nat>`, and the
        #   narrowing into that `@Nat` field had no target to be read from;
        # * `MkBox([0 - 5])` into an `Array<Pos>` field — a CONCRETE field
        #   type, which the expected-type threading above reaches only when
        #   the constructor is parameterised and the caller supplied an
        #   `expected`, so a monomorphic constructor's field was never a
        #   target either.
        #
        # Recording only — the `expected` threaded to `_synth_expr` above is
        # untouched, so no inference decision and no checker diagnostic moves.
        # A field type still carrying a TypeVar is not recorded, exactly as at
        # the function door: an uninstantiated target is not a target.
        # Filling a GAP, never displacing: an entry already here came from the
        # `expected` the enclosing context forced, which is the instantiation
        # the caller requires and is strictly more authoritative than one
        # inferred from the arguments.  `wrap_opt(@Int -> @Option<Nat>)`
        # returning `Some(@Int.0)` is the case that measures the difference —
        # `_infer_ctor_type_args` reads `T = Int` off the argument and never
        # consults the return, so overwriting lost the `nat_bind` that
        # conformance program exists to pin (the one corpus mover on the
        # first shape of this change).
        #
        # #1503: except where the instantiation is the argument's OWN
        # bottom-up type and that type is the one the shared classifier
        # refutes.  `W(0 - 3)` infers `A = Nat` because `0 - 3` is two
        # non-negative literals; recording that `Nat` as the argument's
        # target turned a store of -3 into a field of its own type into a
        # narrowing — E503 at verify and a trapping guard at run time, on a
        # program that reads the field back at `@Int` and was valid on
        # `main`.  A target the context forced is untouched (it was recorded
        # above, through `expected`), and so is an inferred one whose
        # argument carries no pure-literal subtraction, where the checker's
        # type is the value's type.  The narrowing such a value can meet is
        # obligated where a pattern binds it at a scalar position, by the
        # legs that know the type it is bound at (`vera.narrowing`); a
        # pattern that binds it within a COMPOSITE is the context of the
        # construction instead (`_register_pattern_reads`).
        if self.expr_target_types is not None:
            for c_arg, c_ft, declared_ft in zip(
                    expr.args, field_types, ci.field_types):
                key = ast.span_key(c_arg)
                if key is None or contains_typevar(c_ft):
                    continue
                if (contains_typevar(substitute(declared_ft,
                                                expected_mapping))
                        and narrowing.carries_literal_subtraction(c_arg)):
                    continue
                recorded = self.expr_target_types.setdefault(key, c_ft)
                if (isinstance(c_arg, ast.ConstructorCall)
                        and c_arg.name != "Tuple"):
                    self._record_nested_ctor_targets(c_arg, recorded)

        for i, (arg_ty, field_ty) in enumerate(zip(arg_types, field_types)):
            if arg_ty is None or isinstance(arg_ty, UnknownType):
                continue
            if isinstance(field_ty, (TypeVar, UnknownType)):
                continue
            # Re-synth if arg still has unresolved TypeVars and the
            # subtype check would fail (e.g. List<T$2> vs List<Option<Int>>).
            if contains_typevar(arg_ty) and not is_subtype(arg_ty, field_ty):
                arg_ty = self._synth_expr(expr.args[i], expected=field_ty)
                if arg_ty is None or isinstance(arg_ty, UnknownType):
                    continue
                arg_types[i] = arg_ty
            # #1541: a field whose literals the field type types
            # differently from their own values is checked against it —
            # the function-call door's rule, at the constructor door, for a
            # declared field (`MkBox(Some(0 - 5))` into `Option<Pos>`) as
            # for an instantiated one.  Not where the enclosing context
            # already gave the field its type: the argument was synthesized
            # against that type above, and it is the more authoritative
            # target (`Some(Tuple(x, 5))` returned as an
            # `Option<Tuple<PosInt, Int>>` keeps its `PosInt`).  And only for
            # an argument the field already admits: the re-check places each
            # literal at the type it now has, and must not turn a refusal
            # into an acceptance (a literal in a `@Byte` field stays E213).
            elif (not contains_typevar(field_ty)
                    and is_subtype(arg_ty, field_ty)
                    and not (field_types_for_expected
                             and i < len(field_types_for_expected)
                             and not contains_typevar(
                                 field_types_for_expected[i]))
                    and not types_equal(arg_ty, field_ty)
                    and contains_literal_hole(
                        self._literal_soft_type(expr.args[i], arg_ty)
                        or arg_ty)):
                re = self._synth_expr(expr.args[i], expected=field_ty)
                if (re is not None and not isinstance(re, UnknownType)
                        and is_subtype(re, field_ty)):
                    arg_ty = re
                    arg_types[i] = re
            if not is_subtype(arg_ty, field_ty):
                self._error(
                    expr.args[i],
                    f"Constructor '{expr.name}' field {i} has type "
                    f"{pretty_inferred_type(arg_ty)}, expected "
                    f"{pretty_type(field_ty)}.",
                    rationale="Each constructor argument's type must be a "
                              "subtype of the corresponding field type in the "
                              "'data' declaration.",
                    fix=f"Pass a value of type {pretty_type(field_ty)} for "
                        f"field {i}, or convert the current value to "
                        f"{pretty_type(field_ty)}.",
                    spec_ref=(
                        'Chapter 2, Section 2.4 "Algebraic Data Types (ADTs)"'
                    ),
                    error_code="E213",
                )

        return self._ctor_result_type(ci, arg_types, expected=expected,
                                      args=expr.args)

    def _register_arm_pattern_reads(
        self, scrutinee: ast.Expr, pattern: ast.Pattern,
    ) -> None:
        """:py:meth:`_register_pattern_reads` for one `match` arm: a
        constructor pattern reads the scrutinee's components; a binding
        pattern at a composite type binds the whole scrutinee there, which
        is then the context of every construction the scrutinee's value
        flows from."""
        if isinstance(pattern, ast.ConstructorPattern):
            self._register_pattern_reads(
                scrutinee, list(pattern.sub_patterns), _names(pattern.name),
            )
        elif isinstance(pattern, ast.BindingPattern):
            ty = self._pattern_binding_type(pattern.type_expr)
            if ty is None or not isinstance(base_type(ty), AdtType):
                return
            for leaf in narrowing.value_leaves(scrutinee):
                key = ast.span_key(leaf)
                if key is not None:
                    self._pattern_arg_targets.setdefault(key, ty)

    def _register_pattern_reads(
        self,
        source: ast.Expr,
        fields: list[ast.Pattern | ast.TypeExpr],
        ctor_matches: Callable[[str], bool],
    ) -> None:
        """Record the COMPOSITE types a pattern binds the constructor
        arguments its *source* builds at, BEFORE the source is synthesized
        (#1503).

        *fields* are the pattern's positions — a destructure's binding
        types, or a constructor pattern's sub-patterns — and each one's
        argument sources are found the way the pattern's legs find them
        (:func:`vera.narrowing.component_sources`), through nested
        constructor patterns.  An argument bound at a scalar position is
        classified where it is bound, by the pattern's own legs.  One bound
        at a composite type — `W(@Array<Nat>)`, a `@Wrap<Nat>` component —
        is classified by nothing downstream (a composite binding obligates
        no component), and the constructor door records no type it inferred
        from a literal subtraction; so the binding's type is the
        construction's context (``_pattern_arg_targets``, threaded as its
        expected type by ``_synth_expr``).  `match W([0 - 3]) {
        W(@Array<Nat>) -> … }` obligates the `0 - 3` it stores in a `Nat`
        array, and `W(@Array<Int>)` does not."""
        for index, field in enumerate(fields):
            for source_ in narrowing.component_sources(
                    source, index, ctor_matches):
                if not source_.is_argument:
                    continue
                arg = source_.expr
                key = ast.span_key(arg)
                if key is None:
                    continue
                if isinstance(field, ast.ConstructorPattern):
                    self._register_pattern_reads(
                        arg, list(field.sub_patterns),
                        _names(field.name),
                    )
                    continue
                te = (field.type_expr if isinstance(field, ast.BindingPattern)
                      else field if isinstance(field, ast.TypeExpr) else None)
                ty = self._pattern_binding_type(te) if te is not None else None
                if ty is not None and isinstance(base_type(ty), AdtType):
                    self._pattern_arg_targets.setdefault(key, ty)

    def _pattern_binding_type(self, te: ast.TypeExpr) -> Type | None:
        """A pattern binding's type, resolved without reporting: the
        pattern is checked, and its diagnostics raised, where it is bound;
        this looks ahead to it.

        Resolution reports through state that outlives the diagnostic:
        `_error`'s duplicate collapse (`_seen_diag_keys`) and the one-shot
        E154 and removed-alias sets.  Kept while only the diagnostic is
        dropped, that state would deduplicate the binding's own resolution
        away — `match W([()]) { W(@Array<Unit>) -> 1 }` would lose its
        E135, pass `vera check` and `vera verify`, and fail to compile — so
        all of it is restored."""
        before = len(self.errors)
        seen = set(self._seen_diag_keys)
        aliases = set(self._reported_alias_errors)
        reserved = set(self._reported_reserved_type_refs)
        try:
            return self._resolve_type(te)
        finally:
            del self.errors[before:]
            self._seen_diag_keys = seen
            self._reported_alias_errors = aliases
            self._reported_reserved_type_refs = reserved

    def _record_nested_ctor_targets(
        self, ctor: ast.ConstructorCall, target: Type,
    ) -> None:
        """Carry a target recorded for a constructor application DOWN to
        its own arguments (#1503).

        A constructor argument is synthesized before its parent records the
        field type it is placed in, so a nested application —
        `MkBox(Some(0 - 5))` into a declared `Option<Pos>` field — instantiated
        its type parameters from its own argument alone.  The gap fill above
        now declines to record such an instantiation when the argument holds
        a pure-literal subtraction (the checker's `Nat` for it is the claim
        the shared classifier refutes), and the parent's field type is the
        instantiation the value is in fact placed at, so it is recorded here
        instead: `0 - 5` is obligated against `Pos`, where it goes.  A gap is
        filled, never displaced — an entry already present came from the
        argument's own expected type or its own inference, and stays.  A
        `Tuple` carrier is left alone: its readers take a component's target
        from the tuple's own node, which the parent has just recorded.
        """
        if self.expr_target_types is None:
            return
        info = self.env.lookup_constructor(ctor.name)
        base = base_type(target)
        if (info is None or not info.parent_type_params
                or info.field_types is None
                or not isinstance(base, AdtType)
                or base.name != info.parent_type
                or len(base.type_args) != len(info.parent_type_params)):
            return
        mapping = dict(zip(info.parent_type_params, base.type_args))
        for arg, field_ty in zip(ctor.args, info.field_types):
            instantiated = substitute(field_ty, mapping)
            key = ast.span_key(arg)
            if key is None or contains_typevar(instantiated):
                continue
            recorded = self.expr_target_types.setdefault(key, instantiated)
            if isinstance(arg, ast.ConstructorCall) and arg.name != "Tuple":
                self._record_nested_ctor_targets(arg, recorded)

    def _check_tuple_constructor(
        self, expr: ast.ConstructorCall
    ) -> Type | None:
        """Type-check a variadic Tuple constructor: Tuple(a, b, ...)."""
        if not expr.args:
            self._error(
                expr,
                "Tuple constructor requires at least one field.",
                rationale="A tuple is a heterogeneous product of one or more "
                          "components; the empty tuple is not a valid tuple "
                          "type.",
                fix="Provide at least one element, e.g. Tuple(@Int.0), or use "
                    "the unit value () if no payload is needed.",
                spec_ref='Chapter 2, Section 2.3.1 "Tuple Types"',
                error_code="E216",
            )
            return UnknownType()
        arg_types: list[Type] = []
        for arg in expr.args:
            t = self._synth_expr(arg)
            if t is not None and not isinstance(t, UnknownType):
                arg_types.append(t)
            else:
                arg_types.append(UnknownType())
        return AdtType("Tuple", tuple(arg_types))

    def _check_nullary_constructor(self, expr: ast.NullaryConstructor, *,
                                    expected: Type | None = None) -> Type | None:
        """Type-check a nullary constructor: None, Nil, etc."""
        ci = self.env.lookup_constructor(expr.name)
        if ci is None and expr.name in self._refused_ctor_names:
            return UnknownType()  # #1497: see `_check_constructor_call`
        if ci is None:
            candidates, ci = self._stranger_constructor(expr.name)
            if ci is not None:
                message, fix = self._stranger_ctor_message(
                    expr.name, ci, candidates)
                self._error(
                    expr, message,
                    rationale=self._STRANGER_CTOR_RATIONALE,
                    fix=fix,
                    severity="warning",
                    spec_ref='Chapter 8, Section 8.5.4 '
                             '"Constructor Resolution"',
                    error_code="E214",
                )
        if ci is None:
            self._error(
                expr,
                f"Unknown constructor '{expr.name}'.",
                rationale="A nullary constructor reference must name a "
                          "constructor declared by a 'data' type in scope; "
                          "no such constructor is defined or imported, so "
                          "the name has no value and the program cannot "
                          "compile.",
                fix=self._unknown_ctor_fix(expr.name, candidates),
                spec_ref=(
                    'Chapter 2, Section 2.4 "Algebraic Data Types (ADTs)"'
                ),
                error_code="E214",
            )
            return UnknownType()

        if ci.field_types is not None:
            self._error(
                expr,
                f"Constructor '{expr.name}' requires "
                f"{len(ci.field_types)} field(s) but was used as nullary.",
                rationale="A constructor declared with fields must be applied "
                          "to arguments; it cannot be used as a bare name.",
                fix=f"Apply '{expr.name}' to {len(ci.field_types)} "
                    f"argument(s): {expr.name}(...).",
                spec_ref=(
                    'Chapter 2, Section 2.4 "Algebraic Data Types (ADTs)"'
                ),
                error_code="E215",
            )

        return self._ctor_result_type(ci, [], expected=expected)

    def _fresh_typevar(self, name: str) -> TypeVar:
        """Return a TypeVar with a unique name derived from *name*.

        Fresh names prevent self-referential mappings when constructors
        from different ADTs share a type parameter name (e.g. both
        Option<T> and List<T> use ``T``).
        """
        self._fresh_id += 1
        return TypeVar(f"{name}${self._fresh_id}")

    def _ctor_result_type(self, ci: ConstructorInfo,
                          arg_types: list[Type | None], *,
                          expected: Type | None = None,
                          args: tuple[ast.Expr, ...] | None = None) -> Type:
        """Compute the result type of a constructor call.

        When *expected* is an AdtType with the same parent name, unresolved
        TypeVars are filled from the expected type args (bidirectional).
        Remaining unresolved TypeVars are freshened to avoid collisions.
        """
        if ci.parent_type_params:
            # Try to infer type args from argument types
            mapping = self._infer_ctor_type_args(
                ci, arg_types, args=args, expected=expected)

            # Fill unresolved TypeVars from expected type (bidirectional).
            # The same-ADT guard (expected.name == ci.parent_type) means every
            # exp_arg here is the type the surrounding declaration names for
            # THIS constructor's parent, so adopting it can never pull in
            # another ADT's parameter.  #971: adopt exp_arg even when it is a
            # TypeVar — under `forall<T> ... -> @Option<T>` the declared arg is
            # the forall var itself, and mapping the fresh ctor var to it is
            # exactly the var-to-var unification the expected-type fill
            # otherwise lacks for a nullary constructor (the argument-driven
            # path in _unify_for_inference does record forall-to-forall
            # mappings, but a nullary ctor has no arguments to drive it);
            # without it a bare `None` mints an unrelated `T$n` and the program
            # is rejected against a type that unifies trivially (E121/E170/E302).
            if (isinstance(expected, AdtType)
                    and expected.name == ci.parent_type
                    and len(expected.type_args) == len(ci.parent_type_params)):
                for tv, exp_arg in zip(ci.parent_type_params,
                                       expected.type_args):
                    # #993: a binding whose value is a bare FRESH var is a
                    # tentative non-answer (a nested nullary ctor leaked its
                    # own placeholder, e.g. MkA(None) binding A's param to
                    # None's T$n) — the declared expected arg overrides it,
                    # exactly the #293 fresh-is-tentative precedence
                    # `_unify_for_inference` applies between arguments.
                    existing = mapping.get(tv)
                    if existing is None or (
                            isinstance(existing, TypeVar)
                            and "$" in existing.name):
                        mapping[tv] = exp_arg

            # Use fresh TypeVars for any that remain unresolved — prevents
            # self-referential mappings when different ADTs share a param
            # name (e.g. both Option<T> and List<T> use "T").
            type_args = tuple(
                mapping.get(tv, self._fresh_typevar(tv))
                for tv in ci.parent_type_params
            )
            return AdtType(ci.parent_type, type_args)
        return AdtType(ci.parent_type, ())

    def _infer_ctor_type_args(self, ci: ConstructorInfo,
                              arg_types: list[Type | None], *,
                              args: tuple[ast.Expr, ...] | None = None,
                              expected: Type | None = None,
                              soft_out: dict[str, Type] | None = None,
                              ) -> dict[str, Type]:
        """Infer type arguments for a parameterised constructor.

        With the argument expressions in hand (*args*), a literal field
        takes its type from its context exactly as at a generic call
        (#1541): the other fields, then *expected*, then its own value —
        see ``ResolutionMixin._infer_type_args_in_context``.
        """
        if not ci.parent_type_params or not ci.field_types:
            return {}
        if args is None or len(args) != len(arg_types):
            mapping: dict[str, Type] = {}
            for field_ty, arg_ty in zip(ci.field_types, arg_types):
                if arg_ty is None or isinstance(arg_ty, UnknownType):
                    continue
                self._unify_for_inference(field_ty, arg_ty, mapping)
            return mapping
        result_pattern = AdtType(ci.parent_type, tuple(
            TypeVar(tv) for tv in ci.parent_type_params))
        mapping, soft = self._infer_type_args_in_context(
            ci.parent_type_params, ci.field_types, arg_types, args,
            result_type=result_pattern,
            expected=(expected if isinstance(expected, AdtType)
                      and expected.name == ci.parent_type else None),
            callee_vars_opaque=False)
        if soft_out is not None:
            soft_out.update(soft)
        return mapping

    # -----------------------------------------------------------------
    # Qualified / module calls
    # -----------------------------------------------------------------

    def _check_qualified_call(self, expr: ast.QualifiedCall) -> Type | None:
        """Type-check a qualified call: Effect.op(args)."""
        # Try as effect operation
        op_info = self.env.lookup_effect_op(expr.name, expr.qualifier)
        if op_info:
            self._effect_ops_used.add(op_info.parent_effect)
            return self._check_op_call(op_info, expr.args, expr)

        # #309 (Cortex #1147 Finding 1): op resolution failed, but codegen
        # routes a ``DB.query`` / ``DB.execute`` SPELLING to the host database
        # (``$vera.db_<op>``) by qualifier NAME regardless of resolution — e.g. a
        # user ``effect DB`` that declares only some other op.  So the
        # literal-provenance gate MUST fire on the spelling here too, or a
        # runtime SQL string reaches the host ungated.  (A resolved DB SQL op is
        # gated in ``_check_op_call``; this covers the unresolved spelling.)
        #
        # Since #1149 no Vera source reaches this branch: a user ``effect DB``
        # block is rejected (E152) and never registered, so ``DB.query`` /
        # ``DB.execute`` always resolve against the built-in.  Kept as defence
        # in depth — it holds whatever the registry does, and the gate must not
        # depend on E152 to be complete.
        if (
            expr.qualifier == "DB"
            and expr.name in DB_SQL_OP_NAMES
            and expr.args
        ):
            self._check_sql_provenance(expr.name, tuple(expr.args), expr)

        # Unresolved — an error (#1513): code generation has no operation
        # to call, and used to fail in the WAT assembler instead.
        self._error(
            expr,
            f"Unresolved qualified call '{expr.qualifier}.{expr.name}'.",
            rationale="A qualified call 'Effect.op' must name an operation of "
                      "an effect that is in scope; no effect named "
                      f"'{expr.qualifier}' declares an op '{expr.name}', so "
                      "there is no operation to perform and the program "
                      "cannot compile.",
            fix=f"Add '{expr.qualifier}' to the function's effects clause and "
                f"declare 'op {expr.name}(...)' in that effect, or correct "
                f"the qualifier or operation name.  A module function is "
                f"called with '::' ('module::fn(...)'), not '.'.",
            spec_ref='Chapter 7, Section 7.4 "Performing Effects"',
            error_code="E220",
        )
        for arg in expr.args:
            self._synth_expr(arg)
        return UnknownType()

    def _check_module_call(self, expr: ast.ModuleCall, *,
                           expected: Type | None = None) -> Type | None:
        """Type-check a module-qualified call: path.to.fn(args).

        Lookup order:
        1. Module not resolved → the file's own path (#1558) or an error.
        2. Name not in selective import list → error.
        2.5. C7c: function is private → error.
        3. Function found (public) → delegate to ``_check_fn_call_with_info``.
        4. Function not found in module → error with available list.
        """
        mod_path = tuple(expr.path)
        fn_name = expr.name
        mod_label = ".".join(expr.path)

        # 1. Module not resolved
        if mod_path not in self._resolved_module_paths:
            if mod_path == self._own_module_path:
                return self._check_own_module_call(expr, expected=expected)
            self._error(
                expr,
                f"Module '{mod_label}' not found. "
                f"Cannot resolve call to '{fn_name}'.",
                rationale=(
                    "No module matching this path is imported by this file, "
                    "and the path does not name the file itself: a file's "
                    "own path is the one its 'module' declaration gives, "
                    "and only where the program reaches the file by that "
                    "path.  So the call names no function and the program "
                    "cannot compile.  A module reached only through another "
                    "module's imports is not visible here."
                ),
                fix=self._unresolved_module_fix(mod_path, fn_name),
                spec_ref='Chapter 8, Section 8.6.5 "Resolution Errors"',
                error_code="E230",
            )
            for arg in expr.args:
                self._synth_expr(arg)
            return UnknownType()

        # 2. Selective import filter
        import_filter = self._import_names.get(mod_path)
        if import_filter is not None and fn_name not in import_filter:
            self._error(
                expr,
                f"'{fn_name}' is not imported from module "
                f"'{mod_label}'. "
                f"Imported names: {sorted(import_filter)}.",
                rationale=(
                    "The import declaration uses selective imports. "
                    "Add the name to the import list to use it."
                ),
                fix=(
                    f"Change the import to include '{fn_name}': "
                    f"import {mod_label}"
                    f"({', '.join(sorted(import_filter | {fn_name}))});"
                ),
                spec_ref='Chapter 8, Section 8.3.2 "Selective Import"',
                error_code="E231",
            )
            for arg in expr.args:
                self._synth_expr(arg)
            return UnknownType()

        # 2.5 C7c: visibility check — is the function private?
        all_fns = self._module_all_functions.get(mod_path, {})
        fn_all = all_fns.get(fn_name)
        if fn_all is not None and not self._is_public(fn_all.visibility):
            self._error(
                expr,
                f"Function '{fn_name}' in module '{mod_label}' is "
                f"private and cannot be accessed from outside "
                f"its module.",
                rationale=(
                    "Only functions marked 'public' can be called "
                    "from other modules."
                ),
                fix=(
                    f"Mark the function as public in the module: "
                    f"public fn {fn_name}(...)"
                ),
                spec_ref=(
                    'Chapter 8, Section 8.4 "Visibility"'
                ),
                error_code="E232",
            )
            for arg in expr.args:
                self._synth_expr(arg)
            return UnknownType()

        # 3. Look up function in module's registered declarations
        mod_fns = self._module_functions.get(mod_path, {})
        fn_info = mod_fns.get(fn_name)
        if fn_info is not None:
            return self._check_fn_call_with_info(fn_info, expr.args, expr,
                                                 expected=expected)

        # 4. Function not found in module
        available = sorted(mod_fns.keys())
        self._error(
            expr,
            f"Function '{fn_name}' not found in module "
            f"'{mod_label}'."
            + (f" Available functions: {available}." if available else ""),
            rationale="A module-qualified call must name a public function "
                      "declared in the target module; the module was resolved "
                      "but declares no such function, so the program cannot "
                      "compile.",
            fix=f"Define 'public fn {fn_name}(...)' in module '{mod_label}', "
                f"or correct the name to one the module exports"
            + (f" (e.g. {available[0]})." if available else "."),
            spec_ref='Chapter 8, Section 8.5.3 "Module-Qualified Calls"',
            error_code="E233",
        )
        for arg in expr.args:
            self._synth_expr(arg)
        return UnknownType()

    def _check_own_module_call(self, expr: ast.ModuleCall, *,
                               expected: Type | None = None,
                               ) -> Type | None:
        """A module-qualified call to the file's OWN path (#1558).

        `ma::two(3)` inside `module ma;` calls the file's own top-level
        `two`: the path names the module (§8.5.3), and this module is the
        one the path names.  Its private functions are reachable too, since
        the call is inside the module that declares them (§8.4.1).  It is
        checked as the bare call to that top-level function is, with one
        difference that is the point of writing it: a `where` helper of the
        same name does not shadow it, as nothing local shadows a
        module-qualified call — so it reads the top-level table, never the
        lexical helper chain a bare call reads first.
        """
        fn_name = expr.name
        fn_info = self._top_level_fn_infos.get(fn_name)
        if fn_info is not None:
            return self._check_fn_call_with_info(fn_info, expr.args, expr,
                                                 expected=expected)
        if fn_name in self._own_fn_names:
            # A declaration registration refused (E151, E153): its own error
            # is the one the program owes, and this use restates it.
            for arg in expr.args:
                self._synth_expr(arg)
            return UnknownType()
        mod_label = ".".join(expr.path)
        declared = sorted(self._top_level_fn_infos)
        # This file's own helpers only: the index spans every module the
        # file resolves, and another module's helper is no function of this
        # one either way.
        helper_of = sorted(
            parent for parent in self._where_helper_parents.get(fn_name, set())
            if " in module " not in parent)
        if helper_of:
            fix = (f"'{fn_name}' is a 'where' helper of {', '.join(helper_of)}, "
                   f"local to the function that declares it: call it by its "
                   f"bare name from inside that function, or lift it to a "
                   f"top-level function of module '{mod_label}'.")
        else:
            fix = (f"Define 'fn {fn_name}(...)' at the top level of this "
                   f"file, or correct the name to one it declares"
                   + (f" (e.g. {declared[0]})." if declared else "."))
        self._error(
            expr,
            f"Function '{fn_name}' not found in module '{mod_label}', which "
            f"is this file."
            + (f" Its functions: {declared}." if declared else ""),
            rationale="A module-qualified call to the path this file's "
                      "'module' declaration gives names one of the file's "
                      "own top-level functions; the file declares none by "
                      "this name, so the program cannot compile.",
            fix=fix,
            spec_ref='Chapter 8, Section 8.5.3 "Module-Qualified Calls"',
            error_code="E233",
        )
        for arg in expr.args:
            self._synth_expr(arg)
        return UnknownType()

    def _unresolved_module_fix(
        self, mod_path: tuple[str, ...], fn_name: str,
    ) -> str:
        """E230's fix: import the module — unless the path is this file's.

        A file imported as `ma` that declares no path, or declares another,
        has no path of its own (#1558), and adding `import ma;` inside it
        would import the file into itself.  The remedy there is the
        declaration.
        """
        label = ".".join(mod_path)
        resolved = self._resolved_as
        if resolved is not None and mod_path in (
                resolved, self._declared_module_path):
            here = ".".join(resolved)
            if self._declared_module_path is None:
                declares = "declares no module path"
            else:
                declares = ("declares 'module "
                            f"{'.'.join(self._declared_module_path)};'")
            return (f"This file is imported as '{here}' but {declares}, so "
                    f"no path names it.  Declare 'module {here};' at the "
                    f"top of the file and call its own function as "
                    f"'{here}::{fn_name}(...)', or call it by its bare name, "
                    f"'{fn_name}(...)'.")
        return (f"Add 'import {label};' and create the file "
                f"'{label.replace('.', '/')}.vera' relative to the importing "
                f"file or project root.")
