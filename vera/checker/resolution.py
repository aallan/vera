"""Type resolution mixin — AST TypeExpr to semantic Type conversion.

Provides _resolve_type, _resolve_named_type, _resolve_effect_row,
_resolve_effect_ref, _slot_type_name, _infer_type_args, and
_unify_for_inference methods extracted from TypeChecker.
"""

from __future__ import annotations

from vera import ast, naming
from vera.lexical import blank_comments
from vera.checker.registration import (
    _RESERVED_TYPE_PREFIX_RE,
    builtin_effect_names,
)
from vera.types import (
    LITERAL_HOLE,
    NEGATIVE_LITERAL_HOLE,
    PRIMITIVES,
    REMOVED_ALIASES,
    AdtType,
    ConcreteEffectRow,
    EffectInstance,
    EffectRowType,
    FunctionType,
    PrimitiveType,
    PureEffectRow,
    RefinedType,
    Type,
    TypeVar,
    UnknownType,
    contains_literal_hole,
    default_literal_holes,
    erases_to_unit,
    fill_literal_holes,
    is_literal_hole,
    join_literal_holes,
    merge_inferred_types,
    pretty_type,
    substitute,
)

#: The arithmetic operators a literal-only expression may combine literals
#: with.
_LITERAL_ARITH = (ast.BinOp.ADD, ast.BinOp.SUB, ast.BinOp.MUL,
                  ast.BinOp.DIV, ast.BinOp.MOD)


def is_literal_only(expr: ast.Expr) -> bool:
    """True iff *expr* is an integer literal, or arithmetic and negation
    over nothing but integer literals (`0 - 3`, `-3`, `(1 - 4) * 2`).

    Such an expression has no declared type anywhere in it, so the type it
    has is the one its context gives it (spec §4.2) — see
    :meth:`ResolutionMixin._literal_soft_type`.
    """
    if isinstance(expr, ast.IntLit):
        return True
    if isinstance(expr, ast.UnaryExpr):
        return expr.op == ast.UnaryOp.NEG and is_literal_only(expr.operand)
    if isinstance(expr, ast.BinaryExpr) and expr.op in _LITERAL_ARITH:
        return is_literal_only(expr.left) and is_literal_only(expr.right)
    return False


def literal_only_is_int(expr: ast.Expr) -> bool:
    """Whether the checker types the literal-only expression *expr* `Int`
    rather than `Nat`: a negation, an operand that is `Int`, or a negative
    value (`ExpressionsMixin._check_binary` / `_check_unary`)."""
    if isinstance(expr, ast.UnaryExpr):
        return True
    if isinstance(expr, ast.BinaryExpr):
        if (literal_only_is_int(expr.left)
                or literal_only_is_int(expr.right)):
            return True
        value = literal_int_value(expr)
        return value is not None and value < 0
    return False


def literal_int_value(expr: ast.Expr) -> int | None:
    """The value of a literal-only integer expression, or ``None`` when
    *expr* is not one or has no value (a division by zero).

    Division truncates toward zero and the remainder takes the dividend's
    sign, as at run time (spec §4.4).
    """
    if isinstance(expr, ast.IntLit):
        return expr.value
    if isinstance(expr, ast.UnaryExpr):
        if expr.op != ast.UnaryOp.NEG:
            return None
        v = literal_int_value(expr.operand)
        return None if v is None else -v
    if isinstance(expr, ast.BinaryExpr) and expr.op in _LITERAL_ARITH:
        left = literal_int_value(expr.left)
        right = literal_int_value(expr.right)
        if left is None or right is None:
            return None
        if expr.op == ast.BinOp.ADD:
            return left + right
        if expr.op == ast.BinOp.SUB:
            return left - right
        if expr.op == ast.BinOp.MUL:
            return left * right
        if right == 0:
            return None
        quotient = abs(left) // abs(right)
        if (left < 0) != (right < 0):
            quotient = -quotient
        if expr.op == ast.BinOp.DIV:
            return quotient
        return left - right * quotient
    return None


class ResolutionMixin:
    """Methods for resolving AST type expressions into semantic types."""

    # -----------------------------------------------------------------
    # Type resolution: AST TypeExpr -> semantic Type
    # -----------------------------------------------------------------

    def _resolve_type(self, te: ast.TypeExpr) -> Type:
        """Convert an AST TypeExpr into a resolved semantic Type."""
        if isinstance(te, ast.NamedType):
            return self._resolve_named_type(te)
        if isinstance(te, ast.FnType):
            params = tuple(self._resolve_type(p) for p in te.params)
            ret = self._resolve_type(te.return_type)
            eff = self._resolve_effect_row(te.effect)
            return FunctionType(params, ret, eff)
        if isinstance(te, ast.RefinementType):
            base = self._resolve_type(te.base_type)
            return RefinedType(base, te.predicate)
        return UnknownType()

    def _resolve_named_type(self, te: ast.NamedType) -> Type:
        """Resolve a named type (possibly parameterised)."""
        name = te.name

        # Type variable?
        if name in self.env.type_params:
            return self.env.type_params[name]

        # Primitive?
        if name in PRIMITIVES and not te.type_args:
            return PRIMITIVES[name]

        # Type alias?
        alias = self.env.type_aliases.get(name)
        if alias:
            # #660 — validate type-argument arity against the alias's
            # declared type parameters.  Pre-fix the `zip` below
            # silently truncated on length mismatch, producing a
            # substitution where some alias-local names stayed
            # unsubstituted; downstream codegen then leaked literal
            # alias-local names into mono suffixes (`option_map$Int_B`)
            # and the call site referenced a non-existent
            # function-table entry → `unknown table 0: table index
            # out of bounds` at runtime.  The arity mismatch is a
            # user error that the type checker is the right place
            # to surface.
            n_supplied = len(te.type_args) if te.type_args else 0
            n_expected = (
                len(alias.type_params) if alias.type_params else 0
            )
            if n_supplied != n_expected:
                params_phrase = (
                    f"`<{', '.join(alias.type_params)}>`"
                    if alias.type_params
                    else "no type parameters"
                )
                self._error(
                    te,
                    f"Type alias `{name}` expects {n_expected} type "
                    f"argument(s) but {n_supplied} supplied.",
                    rationale=(
                        f"`{name}` is declared with {params_phrase}.  "
                        f"Each use of the alias must supply exactly "
                        f"{n_expected} type argument(s) so the alias "
                        f"body can be fully instantiated.  Without "
                        f"complete arguments, downstream code "
                        f"generation cannot bind the alias-local "
                        f"type variables and may leak them into "
                        f"mangled symbol names — see #660."
                    ),
                    fix=(
                        f"Supply the missing type argument(s) at "
                        f"every use site of `{name}`, e.g. "
                        f"`{name}<Int" + (", Int" * max(0, n_expected - 1)) + ">`."
                        if n_supplied < n_expected
                        else f"Remove the extra type argument(s) "
                             f"so that `{name}` is given exactly "
                             f"{n_expected}."
                    ),
                    spec_ref='Chapter 2, Section 2.6.3 "Type Aliases with Refinements"',
                    error_code="E133",
                )
                return UnknownType()
            if te.type_args and alias.type_params:
                args = tuple(self._resolve_type(a) for a in te.type_args)
                mapping = dict(zip(alias.type_params, args))
                return substitute(alias.resolved_type, mapping)
            return alias.resolved_type

        # ADT or parameterised built-in?
        adt = self.env.data_types.get(name)
        if adt is not None:
            if te.type_args and not (adt.type_params or ()):
                # #1372 fix round: a declared ADT applied to type arguments it
                # does not declare.  Refused HERE, at check, because a
                # declaration shadows every built-in reading of its name
                # (§8.4.1) — so under `private data Array { MkArr(Int) }` the
                # head of `Array<Array>` is that declaration, which takes no
                # arguments, and there is no container left for the arguments
                # to belong to.  Accepting it built an `AdtType("Array",
                # (…,))` that no constructor can produce, and every codegen
                # path that met it went wrong differently: the index emit
                # refused it, while `array_length` / `array_map` /
                # `array_fold` passed one word where the built-in pops a
                # (ptr, len) pair and shipped a `.wasm` that fails to load at
                # rc 0 with no diagnostic.  One rule at the resolution spine
                # closes all seven element shapes at once, and no codegen path
                # can reach any of them.
                #
                # Only the ZERO-arity direction is refused.  Under-application
                # of a parameterised ADT (`@Option` for `Option<T>`) is a
                # separate question with its own inference story, and widening
                # this to full arity equality would refuse programs that
                # compile correctly today.
                self._error(
                    te,
                    f"'{name}' is declared with no type parameters, so it "
                    f"cannot be applied to type arguments.",
                    rationale=(
                        f"A `data` declaration shadows every built-in "
                        f"reading of its name (Chapter 8, Section 8.4.1), so "
                        f"'{name}' here is this namespace's own declaration "
                        f"and not any built-in container of that name.  It "
                        f"declares no type parameters, so there is nothing "
                        f"for the type arguments to bind to."
                    ),
                    fix=(
                        f"Write '{name}' with no type arguments, or rename "
                        f"the declaration if you meant the built-in type of "
                        f"that name — a declaration in scope always wins."
                    ),
                    spec_ref='Chapter 8, Section 8.4.1 "Visibility Rules"',
                    error_code="E135",
                )
                # Report, then resolve EXACTLY as before.  The program is
                # already refused, so the type only has to stay consistent
                # with what `vera.naming._resolve_named` produces for the
                # same expression — and dropping the arguments here made the
                # checker and the renderer disagree about
                # `Option<Decimal<Int>>`, which is the very divergence class
                # this PR exists to close (`test_slot_naming_differential`
                # caught it).
                return AdtType(
                    name, tuple(self._resolve_type(a) for a in te.type_args))
            if te.type_args:
                args = tuple(self._resolve_type(a) for a in te.type_args)
                return AdtType(name, args)
            return AdtType(name, ())

        # Decimal is a non-parameterised built-in opaque type
        if name == "Decimal":
            if te.type_args:
                self._error(
                    te, "Decimal does not accept type arguments.",
                    rationale=(
                        "`Decimal` is a non-parameterised, opaque "
                        "built-in type, so it takes no type "
                        "arguments.  Writing it with a `<...>` "
                        "argument list applies it as if it were a "
                        "generic type, which the type system does "
                        "not permit."
                    ),
                    fix="Write `Decimal` with no type arguments.",
                    spec_ref='Chapter 9, Section 9.7.2 "Decimal"',
                    error_code="E134",
                )
            return AdtType(name, ())

        # Array, Tuple, Map, Set (built-in parameterised types)
        if name in ("Array", "Tuple", "Map", "Set"):
            if te.type_args:
                args = tuple(self._resolve_type(a) for a in te.type_args)
                # #945: an `Array<T>` whose element erases to a zero-size type
                # (`Unit`, or a `Future` transparently wrapping one) has no
                # valid WASM element layout — the element store/load would act
                # on a slot that holds no value, so the array compiles to
                # INVALID WASM (rejected by wasmtime at load) on a check-green +
                # verify-green program.  Reject at check: the element is
                # degenerate (`Array<Unit>` is isomorphic to a `Nat` count).
                # Same principle as the `@T`-at-zero-size family (#900/#939/#943).
                if (name == "Array" and len(args) == 1
                        and erases_to_unit(args[0])):
                    self._error(
                        te,
                        f"'Array' of a zero-size element type "
                        f"'{pretty_type(args[0])}' is not supported.",
                        rationale="A zero-size type (`Unit`, or a `Future` "
                        "wrapping one) occupies 0 bytes and has no runtime "
                        "value, so an array element of that type has no WASM "
                        "representation to store or load — the array would "
                        "compile to invalid WASM.",
                        fix="Use `Nat` for a count of zero-size items, or give "
                        "the element type a runtime value (e.g. `Array<Int>`, "
                        "or a boxed `Array<Option<Unit>>`).",
                        spec_ref='Chapter 2, Section 2.2 "Primitive Types"',
                        error_code="E135",
                    )
                # #1075: the Map/Set siblings of the Array gate above.  Map
                # keys/values and Set elements are raw host-serialized values
                # at a tag-determined width — exactly the Array-element
                # representation case, not the boxed-ADT-field case
                # (`Box<Unit>` / `Option<Unit>` fields live inside a heap
                # layout with a real representation and stay legal).  Without
                # this gate, `Map<String, Unit>` / `Set<Unit>` checked clean
                # and compiled exit-0 to INVALID WASM ("expected i32 but
                # nothing on stack" — the zero-size value pushes nothing where
                # the host import expects an i32 operand).
                if name == "Map" and len(args) == 2:
                    for role, arg in (("key", args[0]), ("value", args[1])):
                        if erases_to_unit(arg):
                            fix = (
                                "Use `Set<K>` if only key membership "
                                "matters, or give the value type a runtime "
                                "value (e.g. `Map<String, Int>`, or a boxed "
                                "`Map<String, Option<Unit>>`)."
                            ) if role == "value" else (
                                "Give the key type a runtime value "
                                "(e.g. `Map<String, ...>`)."
                            )
                            self._error(
                                te,
                                f"'Map' with a zero-size {role} type "
                                f"'{pretty_type(arg)}' is not supported.",
                                rationale="A zero-size type (`Unit`, or a "
                                "`Future` wrapping one) occupies 0 bytes and "
                                f"has no runtime value, so a Map {role} of "
                                "that type has no WASM representation to "
                                "store or load — the map operations would "
                                "compile to invalid WASM.",
                                fix=fix,
                                spec_ref='Chapter 2, Section 2.2 '
                                '"Primitive Types"',
                                error_code="E135",
                            )
                if (name == "Set" and len(args) == 1
                        and erases_to_unit(args[0])):
                    self._error(
                        te,
                        f"'Set' of a zero-size element type "
                        f"'{pretty_type(args[0])}' is not supported.",
                        rationale="A zero-size type (`Unit`, or a `Future` "
                        "wrapping one) occupies 0 bytes and has no runtime "
                        "value, so a Set element of that type has no WASM "
                        "representation to store or load — the set "
                        "operations would compile to invalid WASM.",
                        fix="Use `Bool` for a present/absent flag, or give "
                        "the element type a runtime value (e.g. `Set<Int>`).",
                        spec_ref='Chapter 2, Section 2.2 "Primitive Types"',
                        error_code="E135",
                    )
                return AdtType(name, args)
            return AdtType(name, ())

        # Removed alias? — produce a helpful "did you mean" error.
        canonical = REMOVED_ALIASES.get(name)
        if canonical is not None:
            if name not in self._reported_alias_errors:
                self._reported_alias_errors.add(name)
                self._error(
                    te,
                    f"'{name}' is not a type. Did you mean '{canonical}'?",
                    rationale=(f"'{name}' was removed; "
                               f"use '{canonical}' instead."),
                    fix=f"Replace '{name}' with '{canonical}'.",
                    spec_ref='Chapter 2, Section 2.2 "Primitive Types"',
                )
            return UnknownType()

        # Reserved prelude namespace? — the reference half of E154 (#1221).
        # Reaching here means nothing the checker knows carries this name, so
        # it would become an opaque head.  Codegen knows better: the prelude
        # injects its closure-parameter aliases under exactly these names, at
        # codegen and at the verifier's mono discovery but never at check, so
        # a `VeraOptionMapFn<Int, Bool>` parameter is one stack here and a
        # resolved function type there — codegen merges parameters this
        # binding table keeps apart and the export reads the wrong one.  The
        # declaration gate alone cannot close that: it stops a user DEFINING
        # a reserved name, not MENTIONING one the prelude defines.  Anchored
        # on the same regex the declaration gate uses, so the two halves of
        # the reservation cannot drift apart.
        if _RESERVED_TYPE_PREFIX_RE.match(name):
            if name not in self._reported_reserved_type_refs:
                self._reported_reserved_type_refs.add(name)
                self._error(
                    te,
                    f"Type '{name}' is reserved for the prelude.",
                    rationale=(
                        "Names beginning with 'Vera' followed by an "
                        "uppercase letter or digit are the prelude's "
                        "internal namespace — the declarations its "
                        "combinators resolve through, injected at code "
                        "generation and never visible to the type checker. "
                        "A user program that mentions one names a type this "
                        "checker cannot see and code generation can: the two "
                        "then partition a function's parameters differently, "
                        "and the compiled export reads a parameter the "
                        "binding table assigns to a different slot."
                    ),
                    fix=(
                        "Write out the type this name stands for — a "
                        "function type is spelled `fn(A -> B) "
                        "effects(pure)` — or declare your own alias for it "
                        "under a name outside the reserved namespace: any "
                        "name that does not start with 'Vera' followed by "
                        "an uppercase letter or digit. Stripping the prefix "
                        "is not a fix by itself; the reserved name is not a "
                        "declaration this program can reach under any "
                        "spelling."
                    ),
                    spec_ref='Chapter 8, Section 8.4.1 "Visibility Rules"',
                    error_code="E154",
                )
            return UnknownType()

        # Nothing in scope declares the name (#1489).  One arrival here is
        # legitimate: a FORWARD reference met during registration — a
        # signature naming a `data` or `type` this namespace declares further
        # down, which `_register_all` has not reached yet.  Its placeholder
        # is the type the declaration registers under, so nothing changes
        # once registration reaches it.  Every other name denotes no type,
        # and code generation — which has no representation for it — used to
        # drop each function that needed one, on a check-green program.
        #
        # What reached here as "a type from an unresolved import" no longer
        # can: every namespace registers its imports' data types before its
        # own signatures, the per-module registration included
        # (`ModulesMixin._module_registrations`).  An import whose module did
        # not resolve is already an E011/E012/E013, and a name it lists is
        # reported here with an instruction naming that import.
        #
        # The type after the report is the opaque placeholder this branch
        # always returned — the E135 posture above: the program is already
        # refused, and `vera.naming._resolve_named` renders the placeholder
        # for the same expression, so the checker and the renderer stay
        # byte-identical (`tests/test_slot_naming_differential.py`).
        placeholder = AdtType(name, tuple(
            self._resolve_type(a) for a in te.type_args
        ) if te.type_args else ())
        if name not in self._forward_type_names:
            self._report_unknown_type(te)
        return placeholder

    def _report_unknown_type(self, te: ast.NamedType) -> None:
        """E136: a type name that resolves to no declaration in scope."""
        name = te.name
        why, fix = self._unknown_type_advice(name)
        self._error(
            te,
            f"Unknown type '{name}': nothing in scope declares it.",
            rationale=(
                "A type name must resolve where it is written: to a type "
                "parameter in scope, a primitive, a built-in or prelude "
                "type, a `data` or `type` declaration of this module, or a "
                "public data type this module imports.  A name that "
                "resolves to none of them names no type, and code "
                "generation has no representation for it." + why
            ),
            fix=fix,
            spec_ref='Chapter 2, Section 2.10 "Type Names"',
            error_code="E136",
        )

    def _unknown_type_advice(self, name: str) -> tuple[str, str]:
        """(rationale suffix, fix) for an unknown type name (E136).

        The instruction depends on WHY the name is unknown here, and six
        causes have a better answer than "declare it or import it": the
        ``Fn`` a function-typed slot is referenced by, a clash between two
        imports, an import that did not resolve, a module that declares the
        type (privately, or without this file importing it), a module that
        declares it as an ALIAS, which no import can reach (§8.4.1), and an
        import list naming a type its module does not declare.
        """
        if name == "Fn":
            # The one spelling a program has seen without writing it: a
            # function-typed binding's slot is REFERENCED as `@Fn.0`
            # (spec §3.7), which invites writing `@Fn` where a type goes.
            return (
                "  'Fn' is how a function-typed binding's slot is "
                "referenced (`@Fn.0`); it is not a type.",
                "Write the function type itself — e.g. "
                "'@fn(Int -> Int) effects(pure)' — or a type alias for it.",
            )
        if name in self._ambiguous_import_type_names:
            return (
                "  Here two imports both supply it, so it names no one "
                "declaration (E156, at the import that completes the clash).",
                f"Resolve the E156 clash: import at most one supplier of "
                f"'{name}', or declare '{name}' in this file.",
            )
        for path, names in self._unresolved_imports.items():
            if names is None or name in names:
                label = ".".join(path)
                return (
                    f"  It is imported from module '{label}', which did not "
                    f"resolve.",
                    f"Fix the import of '{label}' first (see the diagnostic "
                    f"at that import); '{name}' is in scope once the module "
                    f"resolves and declares it public.",
                )
        for mod in self._resolved_modules:
            for tld in mod.program.declarations:
                decl = tld.decl
                if not (isinstance(decl, ast.DataDecl) and decl.name == name):
                    continue
                label = ".".join(mod.path)
                if (tld.visibility or "private") != "public":
                    return (
                        f"  Module '{label}' declares a data type '{name}', "
                        f"but privately, so only that module can name it.",
                        f"Make '{name}' public in module '{label}' and import "
                        f"it with 'import {label}({name});', or declare a "
                        f"type of your own.",
                    )
                return (
                    f"  Module '{label}' declares it, but this file does not "
                    f"import it: a value of the type can reach a file "
                    f"through a function it imports, and naming the type "
                    f"takes an import of its own.",
                    f"Import it where it is declared: "
                    f"'import {label}({name});' (or add '{name}' to an "
                    f"existing import of '{label}').",
                )
        for mod in self._resolved_modules:
            for tld in mod.program.declarations:
                decl = tld.decl
                if not (isinstance(decl, ast.TypeAliasDecl)
                        and decl.name == name):
                    continue
                label = ".".join(mod.path)
                text = _declaration_text(mod.source, decl) or (
                    f"type {name} = ...;")
                return (
                    f"  Module '{label}' declares a type alias '{name}', and "
                    f"an alias is module-local (Chapter 8, Section 8.4.1): "
                    f"no other file can import it.",
                    f"Declare your own copy of the alias in this file — "
                    f"'{text}' — or write the type it stands for.",
                )
        for path, names in self._import_names.items():
            if names is not None and name in names:
                label = ".".join(path)
                return (
                    f"  'import {label}(...)' lists it, but module '{label}' "
                    f"declares no data type of that name.",
                    f"Correct '{name}' in the import of '{label}' and here "
                    f"to a data type that module declares public, or "
                    f"declare '{name}' in this file.",
                )
        return (
            "",
            f"Declare it in this file ('data {name} {{ ... }}' or "
            f"'type {name} = ...;'), import it from the module that declares "
            f"it with 'import <module>({name});' (replace <module> with that "
            f"module's path), or correct the spelling.",
        )

    def _resolve_effect_row(self, er: ast.EffectRow) -> EffectRowType:
        """Convert an AST EffectRow into a semantic EffectRowType."""
        return self._resolve_effect_row_ordered(er)[0]

    def _resolve_effect_row_ordered(
        self, er: ast.EffectRow,
    ) -> tuple[EffectRowType, tuple[EffectInstance, ...]]:
        """Resolve an AST EffectRow to its row type AND its SOURCE order.

        One derivation, two views (#1215).  The row type carries a
        ``frozenset`` — the shape subeffect containment wants — which loses
        the declaration order a bare op name needs to resolve deterministically
        when two effects in the row declare it.  The second element is that
        order: the ``ast.EffectSet``'s own sequence, minus the row variable,
        with each instance resolved exactly once here so the two views can
        never describe different effects.
        """
        if isinstance(er, ast.PureEffect):
            return PureEffectRow(), ()
        if isinstance(er, ast.EffectSet):
            instances = []
            row_var = None
            for ref in er.effects:
                if isinstance(ref, ast.EffectRef):
                    # Check if it's a type variable (effect polymorphism)
                    if ref.name in self.env.type_params:
                        row_var = ref.name
                        continue
                    args = tuple(
                        self._resolve_type(a) for a in ref.type_args
                    ) if ref.type_args else ()
                    # #1489: the row's twin of E136.  A declaration further
                    # down this namespace is a forward reference, not an
                    # unknown name.  The instance is built exactly as before,
                    # for the renderer's sake (see `_resolve_named_type`).
                    if (self.env.lookup_effect(ref.name) is None
                            and ref.name not in self._forward_effect_names):
                        self._report_unknown_row_effect(ref)
                    instances.append(EffectInstance(ref.name, args))
                elif isinstance(ref, ast.QualifiedEffectRef):
                    args = tuple(
                        self._resolve_type(a) for a in ref.type_args
                    ) if ref.type_args else ()
                    # No effect has a qualified name: a declaration takes a
                    # single identifier and is module-local (§8.4.1), so this
                    # reference names nothing — and code generation dropped
                    # a function whose row carried one without a word.
                    self._report_unknown_row_effect(ref)
                    instances.append(
                        EffectInstance(f"{ref.module}.{ref.name}", args))
            return (ConcreteEffectRow(frozenset(instances), row_var),
                    tuple(instances))
        return PureEffectRow(), ()

    def _report_unknown_row_effect(
        self, ref: ast.EffectRef | ast.QualifiedEffectRef,
    ) -> None:
        """E338: an effect row names an effect nothing in scope declares."""
        rationale = (
            "An effect row lists the effects a function may perform, and "
            "each name must resolve where it is written: to a built-in "
            "effect, an effect this module declares, or an effect variable "
            "of the enclosing 'forall'.  An effect declaration is "
            "module-local and not importable (Chapter 8, Section 8.4.1), and "
            "a name that denotes no effect gives code generation nothing to "
            "lower."
        )
        if isinstance(ref, ast.QualifiedEffectRef):
            self._error(
                ref,
                f"Effect reference '{ref.module}.{ref.name}' is qualified, "
                f"and no effect has a qualified name.",
                rationale=rationale + (
                    "  An effect declaration takes a single unqualified "
                    "name, so a qualified reference names nothing."
                ),
                fix=(
                    f"Name the effect unqualified — 'effects(<{ref.name}>)' "
                    f"— and declare 'effect {ref.name} {{ ... }}' in this "
                    f"module if it is not a built-in effect."
                ),
                spec_ref='Chapter 7, Section 7.3.1 "Syntax"',
                error_code="E338",
            )
            return
        name = ref.name
        owners = sorted(
            ".".join(mod.path) for mod in self._resolved_modules
            if any(isinstance(tld.decl, ast.EffectDecl)
                   and tld.decl.name == name
                   for tld in mod.program.declarations)
        )
        if owners:
            fix = (
                f"Declare 'effect {name} {{ ... }}' in this module: module "
                f"'{owners[0]}' declares an effect of that name, but an "
                f"effect is module-local, so each module whose effect rows "
                f"name it declares its own copy."
            )
        else:
            builtin = ", ".join(sorted(builtin_effect_names()))
            fix = (
                f"Declare 'effect {name} {{ op ...; }}' in this module, add "
                f"'{name}' to the enclosing 'forall' as an effect variable, "
                f"or correct the spelling (the built-in effects are "
                f"{builtin})."
            )
        self._error(
            ref,
            f"Unknown effect '{name}' in an effect row: nothing in scope "
            f"declares it.",
            rationale=rationale,
            fix=fix,
            spec_ref='Chapter 7, Section 7.3.1 "Syntax"',
            error_code="E338",
        )

    def _resolve_effect_ref(self, ref: ast.EffectRefNode) -> EffectInstance | None:
        """Resolve a single effect reference."""
        if isinstance(ref, ast.EffectRef):
            args = tuple(
                self._resolve_type(a) for a in ref.type_args
            ) if ref.type_args else ()
            return EffectInstance(ref.name, args)
        if isinstance(ref, ast.QualifiedEffectRef):
            args = tuple(
                self._resolve_type(a) for a in ref.type_args
            ) if ref.type_args else ()
            return EffectInstance(f"{ref.module}.{ref.name}", args)
        return None

    # -----------------------------------------------------------------
    # Canonical type name for slot references
    # -----------------------------------------------------------------

    def _naming_env(self) -> naming.AliasEnv:
        """The naming environment for the checker's CURRENT state.

        Rebuilt per call rather than cached: ``env.type_aliases`` grows
        through registration and ``env.type_params`` changes on entering and
        leaving every ``forall`` scope, so a cached env would render a
        ``forall<T>`` parameter against the wrong shadowing set.  The build is
        a copy of the module's alias table (user aliases only — no built-in
        seeds the table), which is small enough that the full suite shows no
        measurable cost.
        """
        return naming.alias_env_from_environment(self.env)

    def _check_slot_name_args(self, te: ast.TypeExpr) -> None:
        """Resolve a slot name's type ARGUMENTS for their diagnostics.

        The naming composition that used to live in the checker got E133 /
        E134 / E135 / removed-alias reporting for free, because it rendered
        each argument by RESOLVING it — and at a slot REFERENCE
        (``@Option<Box>.0`` for a parameterised ``Box``) that incidental
        report is the only one there is.  :mod:`vera.naming` is total and
        silent by design, so delegating the rendering to it would drop those
        diagnostics; this walk keeps them, following exactly the traversal
        the old composition took (refinement bases unwrapped, a function type
        naming nothing).  It is a reporting pass only — the name itself comes
        from the module.
        """
        while isinstance(te, ast.RefinementType):
            te = te.base_type
        if isinstance(te, ast.NamedType) and te.type_args:
            for arg in te.type_args:
                self._resolve_type(arg)

    def _slot_type_name(self, type_name: str,
                        type_args: tuple[ast.TypeExpr, ...] | None) -> str:
        """Form the canonical type name for slot reference matching.

        Delegates to :func:`vera.naming.slot_name` (#1208): the head is
        syntactic and the arguments resolve, which is what the binding side
        does too, so a reference and its binding cannot be keyed differently.
        """
        te = ast.NamedType(name=type_name, type_args=type_args)
        self._check_slot_name_args(te)
        return naming.slot_name(te, self._naming_env())

    def _slot_ref_key(self, ref: ast.SlotRef) -> str:
        """Binding-table key for a ``SlotRef``, keyed as ``bind()`` keys it.

        The #309 / #1160 provenance resolvers in :mod:`vera.checker.sql` need
        to look bindings up, and must do it with the CHECKER's renderer, not
        the syntactic one in :mod:`vera.slots`.  Binding keys resolve their
        type arguments (``_type_expr_to_slot_name`` →
        :func:`vera.naming.slot_name`: a syntactic head over resolved
        arguments, since #1208 routed both sides through the one renderer),
        so a syntactic render of ``@Array<Option<Txt>>``
        where ``type Txt = String`` yields ``Array<Option<Txt>>`` and matches
        the ``Array<Option<String>>`` key not at all.  A miss reads as "not
        statically known", so the check would silently do nothing — the exact
        failure #1160 fixed one level up.
        """
        return self._slot_type_name(ref.type_name, ref.type_args)

    # -----------------------------------------------------------------
    # Type inference helpers
    # -----------------------------------------------------------------

    def _literal_soft_type(self, expr: ast.Expr, ty: Type | None,
                           ) -> Type | None:
        """*ty*, the type synthesized for *expr*, with every position a
        LITERAL decided replaced by :data:`~vera.types.LITERAL_HOLE`
        (#1541, #1565).

        A position is a literal's when its `Int` or `Nat` came from integer
        literals alone: a literal-only expression (`0`, `0 - 3`), an `if`,
        `match` or block whose every result is one, an array literal's
        element whose every element is one, a tuple or constructor field,
        an index into such an array, and a generic call's result where its
        own literals decided the instantiation.  Anything a declaration
        typed — a slot, a closure's parameters, a non-generic call — is
        left as synthesized.
        """
        if ty is None or isinstance(ty, UnknownType):
            return ty
        if isinstance(ty, PrimitiveType) and ty.name in ("Int", "Nat"):
            if is_literal_only(expr):
                # The hole's fallback is the type rule 1 gives the
                # expression itself (PR #1583 review): `-0` and
                # `(0 - 3) + 4` are `Int` although their values are not
                # negative, so they fall back to `Int` as they did.
                if literal_only_is_int(expr):
                    return NEGATIVE_LITERAL_HOLE
                return LITERAL_HOLE
        if isinstance(expr, ast.Block):
            return self._literal_soft_type(expr.expr, ty)
        if isinstance(expr, ast.IfExpr):
            return _meet_literal_holes(
                (self._literal_soft_type(expr.then_branch, ty),
                 self._literal_soft_type(expr.else_branch, ty)), ty)
        if isinstance(expr, ast.MatchExpr) and expr.arms:
            return _meet_literal_holes(
                tuple(self._literal_soft_type(arm.body, ty)
                      for arm in expr.arms), ty)
        if (isinstance(expr, ast.ArrayLit) and expr.elements
                and isinstance(ty, AdtType) and ty.name == "Array"
                and len(ty.type_args) == 1):
            elem = ty.type_args[0]
            return AdtType("Array", (_meet_literal_holes(
                tuple(self._literal_soft_type(e, elem)
                      for e in expr.elements), elem),))
        if isinstance(expr, ast.IndexExpr):
            coll = self._literal_soft_type(
                expr.collection, AdtType("Array", (ty,)))
            if (isinstance(coll, AdtType) and coll.name == "Array"
                    and coll.type_args):
                return coll.type_args[0]
            return ty
        if (isinstance(expr, ast.ConstructorCall) and expr.name == "Tuple"
                and isinstance(ty, AdtType) and ty.name == "Tuple"
                and len(ty.type_args) == len(expr.args)):
            return AdtType("Tuple", tuple(
                self._literal_soft_type(a, t) or t
                for a, t in zip(expr.args, ty.type_args)))
        if isinstance(expr, (ast.ConstructorCall, ast.FnCall,
                             ast.ModuleCall)):
            recorded = self._literal_soft_results.get(ast.span_key(expr))
            if recorded is not None:
                return _overlay_literal_holes(recorded, ty)
        return ty

    def _record_literal_soft_result(self, node: ast.Node, soft: Type,
                                    ) -> None:
        """Record which parts of *node*'s result its literals decided
        (read back by :meth:`_literal_soft_type`); a result they decided
        no part of clears any earlier record, since a call is synthesized
        again whenever its context changes."""
        key = ast.span_key(node)
        if key is None:
            return
        if contains_literal_hole(soft):
            self._literal_soft_results[key] = soft
        else:
            self._literal_soft_results.pop(key, None)

    def _infer_type_args_in_context(
        self,
        forall_vars: tuple[str, ...],
        param_types: tuple[Type, ...],
        arg_types: list[Type | None],
        args: tuple[ast.Expr, ...],
        *,
        result_type: Type | None = None,
        expected: Type | None = None,
        conflicts: set[str] | None = None,
        callee_vars_opaque: bool = True,
    ) -> tuple[dict[str, Type], dict[str, Type]]:
        """Infer a call's type arguments, a literal taking its type from
        its context (spec §4.2; #1541, #1565).

        Three sources, in order of authority:

        1. every argument, each literal position a hole
           (:meth:`_literal_soft_type`) that any declared sibling fills —
           the closure `fn(@Int, @Int -> @Int)` fixes `array_fold`'s `U`
           before the accumulator literal `0` can;
        2. the type the call's result is expected at, which fills a hole
           still open (`let @Int = id(5)` is `id` at `Int`);
        3. the literals' own types by value, joined — `Nat` when every
           literal at the position is non-negative, `Int` otherwise.

        Returns ``(mapping, soft)``.  *soft* is the same mapping with the
        positions step 3 decided still holes, so a caller can record which
        parts of its result a literal decided and an enclosing call can
        treat them as literal in turn.

        *callee_vars_opaque* is the function door's rule that an argument
        type still carrying the callee's own variables binds nothing
        (``_unify_for_inference``); the constructor door never applied it.
        """
        forall_set: set[str] | None = (
            set(forall_vars) if callee_vars_opaque else None)
        mapping: dict[str, Type] = {}
        for param_ty, arg, arg_ty in zip(param_types, args, arg_types):
            if arg_ty is None or isinstance(arg_ty, UnknownType):
                continue
            soft_ty = self._literal_soft_type(arg, arg_ty)
            if soft_ty is None:
                continue
            self._unify_for_inference(param_ty, soft_ty, mapping,
                                      forall_set, conflicts)
        holed = [tv for tv, b in mapping.items() if contains_literal_hole(b)]
        if not holed:
            return mapping, dict(mapping)
        if (expected is not None and result_type is not None
                and not isinstance(expected, UnknownType)):
            from_expected: dict[str, Type] = {}
            self._unify_for_inference(result_type, expected, from_expected,
                                      forall_set)
            for tv in holed:
                mapping[tv] = fill_literal_holes(
                    mapping[tv], from_expected.get(tv))
        soft = dict(mapping)
        for tv in holed:
            mapping[tv] = default_literal_holes(mapping[tv])
        return mapping, soft

    def _infer_type_args(self, forall_vars: tuple[str, ...],
                         param_types: tuple[Type, ...],
                         arg_types: list[Type | None],
                         conflicts: set[str] | None = None,
                         ) -> dict[str, Type]:
        """Infer type variable bindings by matching args against params.

        When a forall var is bound by several arguments whose types share a
        parameterised head but each pin a *different* type parameter (a sparse
        multi-parameter ADT, `data Res<A, B> { MkOk(A), MkErr(B) }` reached via
        `eq2(MkErr(5), MkOk("x"))`), the per-argument bindings are MERGED
        position-wise so the fully-determined `Res<String, Int>` is recovered
        rather than the first-argument-wins `Res<?, Int>` (#898).  A genuine
        per-position CONFLICT (two arguments fixing the same parameter to
        different concrete types) records the var in *conflicts* so the caller
        emits a clear conflict diagnostic instead of a wrong-type E202.
        """
        mapping: dict[str, Type] = {}
        forall_set = set(forall_vars)
        for param_ty, arg_ty in zip(param_types, arg_types):
            if arg_ty is None or isinstance(arg_ty, UnknownType):
                continue
            self._unify_for_inference(param_ty, arg_ty, mapping, forall_set,
                                      conflicts)
        return mapping

    def _unify_for_inference(self, pattern: Type, concrete: Type,
                             mapping: dict[str, Type],
                             forall_vars: set[str] | None = None,
                             conflicts: set[str] | None = None,
                             ) -> None:
        """Simple unification for type argument inference."""
        # Skip when the concrete type has TypeVars matching the callee's
        # own forall vars (e.g. map_new() returns Map<K, V> where K, V
        # are the callee's forall vars — not yet resolved from args).
        # Other TypeVars (e.g. E$6 from constructor inference, or U from
        # an enclosing forall scope) are fine to unify with.
        if (forall_vars
                and isinstance(concrete, AdtType)
                and concrete.type_args
                and any(isinstance(a, TypeVar) and a.name in forall_vars
                        for a in concrete.type_args)):
            return
        if isinstance(pattern, TypeVar):
            # Prefer concrete resolutions over fresh TypeVars (those named
            # with '$', e.g. T$1 from _fresh_typevar).
            #
            # Fresh TypeVars are unresolved placeholders produced when a
            # nullary constructor like None or Ok(x) can't fill all type
            # parameters from its own args.  Recording A→T$1 from None's
            # inferred Option<T$1> is fine as a first approximation, but must
            # be overwritten when a later argument provides a concrete answer
            # (e.g. the fn(@Int->@Int) callback in option_map(None, ...)).
            #
            # Overwrite iff the existing mapping is a fresh TypeVar AND the
            # new concrete type is not itself a fresh TypeVar (#293).
            # Forall-to-forall mappings (e.g. T→U when wrap<U> calls identity,
            # where U has no '$') are recorded and kept as-is.
            existing = mapping.get(pattern.name)
            is_fresh = isinstance(concrete, TypeVar) and '$' in concrete.name
            if existing is None:
                mapping[pattern.name] = concrete
            elif (isinstance(existing, TypeVar)
                  and '$' in existing.name
                  and not is_fresh
                  and not (is_literal_hole(existing)
                           and isinstance(concrete, TypeVar))):
                # Overwrite a tentative fresh-TypeVar mapping with a concrete
                # (or forall-var) resolution.  Not a literal's hole with a
                # type variable (#1541, PR #1583 review): a literal cannot
                # have a rigid `T` — inside its own body `T` is opaque — nor
                # a variable leaked unresolved from a nested call, so that
                # meeting is `merge_inferred_types`'s, which keeps the hole
                # in either argument order.
                mapping[pattern.name] = concrete
            elif (isinstance(existing, TypeVar)
                  and not isinstance(concrete, TypeVar)):
                # #970 (dual): the existing binding is a bare type variable that
                # leaked UNRESOLVED from a nested generic call — e.g., given a
                # user-defined `forall<T> fn nothing(@Unit -> @Option<T>)`, the
                # call `option_unwrap_or(nothing(()), 11)`, where `nothing(())`
                # returns `@Option<T>`, binds `option_unwrap_or`'s param to
                # `nothing`'s escaped `T` before the concrete `11` arrives.  A
                # later argument that pins a CONCRETE type resolves it, exactly
                # as a fresh `$` placeholder would.  (Pre-rename a name
                # coincidence between the leaked var and the built-in's internal
                # var made the skip-guard fire and hide this; the #970 registry
                # rename removed the coincidence, so the concrete-wins rule must
                # be explicit — not a weakening, the same downstream subtype
                # check runs unchanged.)  A literal's hole (#1541) meeting
                # such a variable is settled by `merge_inferred_types`, below.
                mapping[pattern.name] = concrete
            else:
                # #898: both the existing binding and the new one are (partly)
                # concrete.  Merge them position-wise so two sparse constructor
                # arguments each pinning a different type parameter combine into
                # one fully-determined type (`Res<?, Int>` ⊔ `Res<String, ?>` =
                # `Res<String, Int>`); a genuine per-position conflict is
                # recorded so the caller can report it clearly.
                merged, conflict = merge_inferred_types(existing, concrete)
                if conflict and conflicts is not None:
                    conflicts.add(pattern.name)
                mapping[pattern.name] = merged
            return

        if isinstance(pattern, AdtType) and isinstance(concrete, AdtType):
            if pattern.name == concrete.name:
                for p_arg, c_arg in zip(pattern.type_args, concrete.type_args):
                    self._unify_for_inference(
                        p_arg, c_arg, mapping, forall_vars, conflicts)

        if isinstance(pattern, FunctionType) and isinstance(concrete, FunctionType):
            for p_param, c_param in zip(pattern.params, concrete.params):
                self._unify_for_inference(
                    p_param, c_param, mapping, forall_vars, conflicts)
            self._unify_for_inference(
                pattern.return_type, concrete.return_type,
                mapping, forall_vars, conflicts)


def _meet_literal_holes(parts: tuple[Type | None, ...], ty: Type) -> Type:
    """The positions of *ty* that are a literal's in EVERY one of *parts*
    (the branches of an `if` or `match`, an array literal's elements) are
    holes; every other position is *ty*'s own."""
    known = [p for p in parts if p is not None]
    if len(known) != len(parts):
        return ty
    if all(is_literal_hole(p) for p in known):
        hole: Type = LITERAL_HOLE
        for p in known:
            hole = join_literal_holes(hole, p)
        return hole
    adts = [p for p in known if isinstance(p, AdtType)
            and isinstance(ty, AdtType) and p.name == ty.name
            and len(p.type_args) == len(ty.type_args)]
    if isinstance(ty, AdtType) and len(adts) == len(known):
        return AdtType(ty.name, tuple(
            _meet_literal_holes(tuple(p.type_args[i] for p in adts), arg)
            for i, arg in enumerate(ty.type_args)))
    return ty


def _overlay_literal_holes(soft: Type, ty: Type) -> Type:
    """*ty* with a hole wherever *soft* has one at an `Int` or `Nat`
    position of *ty*."""
    if is_literal_hole(soft):
        if isinstance(ty, PrimitiveType) and ty.name in ("Int", "Nat"):
            return soft
        return ty
    if (isinstance(soft, AdtType) and isinstance(ty, AdtType)
            and soft.name == ty.name
            and len(soft.type_args) == len(ty.type_args)):
        return AdtType(ty.name, tuple(
            _overlay_literal_holes(a, b)
            for a, b in zip(soft.type_args, ty.type_args)))
    return ty


def _declaration_text(source: str, decl: ast.Node) -> str | None:
    """*decl*'s source text on one line, or ``None`` without a span.

    Read with its comments blanked: joined onto one line, a ``--`` comment
    inside a declaration written across lines would swallow the rest of it
    (PR #1508 review).  :func:`~vera.lexical.blank_comments` shares the
    parser's scanner, so a ``--`` inside a string literal stays.
    """
    span = decl.span
    if span is None:
        return None
    lines = blank_comments(source).splitlines()[span.line - 1:span.end_line]
    if not lines:
        return None
    if len(lines) == 1:
        return lines[0][span.column - 1:span.end_column - 1].strip() or None
    lines[0] = lines[0][span.column - 1:]
    lines[-1] = lines[-1][:span.end_column - 1]
    return " ".join(line.strip() for line in lines if line.strip()) or None
