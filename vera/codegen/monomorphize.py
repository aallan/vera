"""Mixin for generic function monomorphization (Pass 1.5).

Drives the shared :class:`~vera.monomorphize.Monomorphizer` (instantiation
discovery + AST substitution) to produce monomorphized ``FnDecl`` copies for
WASM emission, and additionally checks ability-constraint satisfaction (E613) —
the one part of monomorphization that is layout-specific and so stays in
codegen.

The discovery + substitution logic itself lives in :mod:`vera.monomorphize` so
the verifier (#732) can reuse the *exact* same code: the verifier must check
precisely the instantiation set this pass emits, or a missed instantiation
becomes a false Tier-1.  Codegen owns the *orchestration* here — the seed walk
plus the transitive worklist, with constraint-failing instances filtered out
(and their subtrees pruned) so the emitted set matches today's behaviour.
"""

from __future__ import annotations

from vera import ast
from vera.monomorphize import MonoContext, Monomorphizer

# Types that satisfy the built-in abilities.  #773: `Eq` is structural, so a
# field of ANY of these — String included (compared by content) — is
# Eq-derivable; the scalar-only carve-out that excluded String is gone.
_EQ_TYPES: frozenset[str] = frozenset({
    "Int", "Nat", "Bool", "Float64", "String", "Byte", "Unit",
})
_ORD_TYPES: frozenset[str] = frozenset({
    "Int", "Nat", "Bool", "Float64", "String", "Byte",
})
_HASH_TYPES: frozenset[str] = frozenset({
    "Int", "Nat", "Bool", "Float64", "String", "Byte", "Unit",
})
_SHOW_TYPES: frozenset[str] = frozenset({
    "Int", "Nat", "Bool", "Float64", "String", "Byte", "Unit",
})

# Maps ability name → (type set, error description fragment).
_ABILITY_TYPE_SETS: dict[str, tuple[frozenset[str], str]] = {
    "Eq": (_EQ_TYPES, "primitive types (Int, Bool, Float64, String, Byte, Nat, Unit) and ADTs whose fields are themselves Eq (structural derivation)"),
    "Ord": (_ORD_TYPES, "primitive types (Int, Nat, Bool, Float64, String, Byte)"),
    "Hash": (_HASH_TYPES, "primitive types (Int, Nat, Bool, Float64, String, Byte, Unit)"),
    "Show": (_SHOW_TYPES, "primitive types (Int, Nat, Bool, Float64, String, Byte, Unit)"),
}

# Maps a WAT scalar return type to the Vera type name the old
# `_infer_fncall_vera_type_simple` returned for it.  Used to populate
# `MonoContext.fn_ret_types` from `_fn_sigs`, reproducing that behaviour
# exactly (other WAT types — i32_pair, None — yield no entry → `None`).
_WT_TO_VERA: dict[str | None, str] = {
    "i64": "Int",
    "i32": "Bool",
    "f64": "Float64",
}


class MonomorphizationMixin:
    """Methods for monomorphizing generic functions."""

    def _build_mono_context(
        self,
        generic_decls: dict[str, ast.FnDecl],
        ctor_to_adt: dict[str, str],
    ) -> MonoContext:
        """Pack codegen registration state into a shared MonoContext.

        ``fn_ret_types`` is derived from the WAT signatures so the shared
        ``_infer_fncall_vera_type_simple`` returns the same Vera type names the
        old codegen-local version did (i64→Int, i32→Bool, f64→Float64).
        """
        fn_ret_types: dict[str, str] = {}
        for name, sig in self._fn_sigs.items():
            ret_vera = _WT_TO_VERA.get(sig[1])
            if ret_vera is not None:
                fn_ret_types[name] = ret_vera
        return MonoContext(
            generic_decls=generic_decls,
            ctor_to_adt=ctor_to_adt,
            ctor_tp_indices=getattr(self, "_ctor_adt_tp_indices", {}),
            adt_tp_counts=getattr(self, "_adt_tp_counts", {}),
            type_aliases=getattr(self, "_type_aliases", {}),
            type_alias_params=getattr(self, "_type_alias_params", {}),
            fn_ret_types=fn_ret_types,
        )

    def _monomorphize(
        self, program: ast.Program,
    ) -> list[ast.FnDecl]:
        """Monomorphize generic functions for all concrete call sites.

        Returns a list of new FnDecl nodes with type variables replaced
        by concrete types and names mangled.
        """
        # Identify generic function declarations
        generic_decls: dict[str, ast.FnDecl] = {}
        for tld in program.declarations:
            decl = tld.decl
            if isinstance(decl, ast.FnDecl) and decl.forall_vars:
                generic_decls[decl.name] = decl

        if not generic_decls:
            return []

        # Build constructor → ADT name mapping
        ctor_to_adt: dict[str, str] = {}
        for adt_name in self._adt_layouts:
            for ctor_name in self._adt_layouts[adt_name]:
                ctor_to_adt[ctor_name] = adt_name

        mono = Monomorphizer(
            self._build_mono_context(generic_decls, ctor_to_adt),
        )

        # Record of every (generic name, concrete types) actually emitted —
        # i.e. that passed constraint checks.  Consumed by the #732 differential
        # soundness test, which asserts the verifier discovers a superset of
        # this set; harmless to WAT output (a plain bookkeeping set).
        self._emitted_instances: set[tuple[str, tuple[str, ...]]] = set()

        # Collect concrete instantiations from non-generic function bodies
        instances: dict[str, set[tuple[str, ...]]] = {
            name: set() for name in generic_decls
        }
        for tld in program.declarations:
            decl = tld.decl
            if isinstance(decl, ast.FnDecl) and not decl.forall_vars:
                mono.collect_calls_in_node(
                    decl, generic_decls, ctor_to_adt, instances,
                )

        # Generate monomorphized FnDecls with transitive closure.
        # After generating the first round, scan the monomorphized bodies
        # for further generic calls and generate those too.  This handles
        # cases like array_map calling array_map_go (both generic).
        # Constraint-failing instances are skipped here (and their subtrees
        # pruned), so the emitted set excludes anything that wouldn't compile.
        seen: set[tuple[str, tuple[str, ...]]] = set()
        mono_decls: list[ast.FnDecl] = []
        # Sort each per-name instantiation set so the worklist seed — and hence
        # the order clones are appended to `mono_decls` and emitted to WAT — is
        # deterministic across runs.  Without this, `set` iteration order varies
        # with PYTHONHASHSEED and `vera compile --wat` is not byte-stable (clone
        # bodies are identical; only their order differs), breaking reproducible
        # builds (PR #767 review).
        worklist: list[tuple[str, tuple[str, ...]]] = [
            (fn_name, ct)
            for fn_name, type_arg_set in instances.items()
            for ct in sorted(type_arg_set)
        ]
        while worklist:
            fn_name, concrete_types = worklist.pop()
            key = (fn_name, concrete_types)
            if key in seen:
                continue
            seen.add(key)
            if fn_name not in generic_decls:
                continue
            decl = generic_decls[fn_name]
            if not self._check_constraints(decl, concrete_types):
                continue  # constraint violation — error emitted
            mono_fn = mono.monomorphize_fn(decl, concrete_types)
            mono_decls.append(mono_fn)
            self._emitted_instances.add((fn_name, concrete_types))
            # Scan the monomorphized body for further generic calls
            transitive: dict[str, set[tuple[str, ...]]] = {
                name: set() for name in generic_decls
            }
            mono.collect_calls_in_node(
                mono_fn, generic_decls, ctor_to_adt, transitive,
            )
            for t_name, t_types in transitive.items():
                for t_ct in sorted(t_types):  # deterministic order (see seed)
                    if (t_name, t_ct) not in seen:
                        worklist.append((t_name, t_ct))

        # Store generic fn info for call rewriting in wasm.py
        self._generic_fn_info: dict[
            str, tuple[tuple[str, ...], tuple[ast.TypeExpr, ...]]
        ] = {}
        for name, decl in generic_decls.items():
            assert decl.forall_vars is not None  # noqa: S101
            self._generic_fn_info[name] = (decl.forall_vars, decl.params)

        return mono_decls

    def _check_constraints(
        self,
        decl: ast.FnDecl,
        concrete_types: tuple[str, ...],
    ) -> bool:
        """Verify all ability constraints are satisfied for an instantiation.

        Returns True if all constraints are satisfied, False otherwise
        (after emitting diagnostics).
        """
        if not decl.forall_constraints or not decl.forall_vars:
            return True

        from vera.errors import Diagnostic, SourceLocation

        mapping = dict(zip(decl.forall_vars, concrete_types))
        ok = True
        for constraint in decl.forall_constraints:
            concrete = mapping.get(constraint.type_var)
            if concrete is None:
                continue
            entry = _ABILITY_TYPE_SETS.get(constraint.ability_name)
            if entry is not None:
                type_set, desc = entry
                # For Eq, also check ADT auto-derivation.
                if concrete in type_set:
                    continue
                if (constraint.ability_name == "Eq"
                        and self._adt_satisfies_eq(concrete)):
                    continue
                # Vera has no `derive` construct — for Eq the actionable fix
                # is structural: make every constructor field itself Eq.
                if constraint.ability_name == "Eq":
                    fix_text = (
                        f"Instantiate the generic with a type that supports "
                        f"'Eq'. An ADT derives Eq structurally when every "
                        f"constructor field is itself Eq — restructure "
                        f"'{concrete}' so its fields are Eq primitives or Eq "
                        f"ADTs (Array/Map/handle fields are not Eq)."
                    )
                else:
                    fix_text = (
                        f"Instantiate the generic with a type that supports "
                        f"'{constraint.ability_name}'."
                    )
                self.diagnostics.append(Diagnostic(
                    description=(
                        f"Type '{concrete}' does not satisfy ability "
                        f"'{constraint.ability_name}'. Only {desc} "
                        f"support {constraint.ability_name}."
                    ),
                    location=SourceLocation(file=self.file),
                    rationale=(
                        "A monomorphized generic instantiates each type "
                        "parameter with a concrete type that must satisfy the "
                        "parameter's ability bounds; this type does not."
                    ),
                    fix=fix_text,
                    spec_ref='Chapter 9, Section 9.8 "Abilities"',
                    severity="error",
                    error_code="E613",
                ))
                ok = False
            else:
                self.diagnostics.append(Diagnostic(
                    description=(
                        f"Ability '{constraint.ability_name}' is not yet "
                        f"supported for code generation."
                    ),
                    location=SourceLocation(file=self.file),
                    rationale=(
                        "Code generation implements a fixed set of built-in "
                        "abilities; this ability has no compilation support."
                    ),
                    fix=(
                        "Constrain the type parameter with a built-in ability "
                        "(Eq, Ord, Hash, or Show) instead."
                    ),
                    spec_ref='Chapter 9, Section 9.8 "Abilities"',
                    severity="error",
                    error_code="E613",
                ))
                ok = False
        return ok

    def _adt_satisfies_eq(
        self, type_name: str, _seen: frozenset[str] = frozenset(),
    ) -> bool:
        """Check if an ADT type satisfies Eq via *structural* auto-derivation.

        An ADT satisfies Eq iff every constructor field's type does (§9.8).  A
        field is Eq iff it is an Eq primitive (Int/Nat/Bool/Float64/Byte/Unit
        **or String**, which compares by content) or a nested ADT that itself
        satisfies Eq (checked recursively).  A field with no Eq semantics —
        Array, Map, a host handle, a function — is *not* derivable and the ADT
        is rejected (E613).  Simple enums (all constructors zero-field) always
        satisfy Eq.

        This must agree exactly with codegen's structural-Eq generator
        (`OperatorsMixin._generate_adt_eq_fn`): a program the gate accepts must
        never hit the generator's loud "no Eq comparison" invariant, and vice
        versa — the checker↔codegen lockstep #732 relies on (differential-
        tested by ``test_structural_eq_gate_matches_codegen``).

        `_adt_layouts` is keyed by the bare ADT name (`Box`), so a
        parameterized name (`Box<String>`) is split into base + args; a
        TYPE-PARAMETER field's Eq-ness is its concrete type ARGUMENT's (per
        `_ctor_adt_tp_indices`), while a concrete field's is its declared type's
        (per `field_types`).  #773 lifted this from the old scalar-WASM-rep
        basis (which false-rejected String fields and false-accepted nested-ADT
        / Map pointer fields).
        """
        from vera.monomorphize import Monomorphizer, substitute_type_param_names

        parsed = Monomorphizer._parse_type_name(type_name)
        base = parsed.name
        args = [
            Monomorphizer._format_type_name(a)
            for a in (parsed.type_args or ())
            if isinstance(a, ast.NamedType)
        ]
        layouts = self._adt_layouts.get(base)
        if layouts is None:
            return False
        if type_name in _seen:        # recursive ADT (e.g. List<T>) — break cycle
            return True
        seen = _seen | {type_name}
        # Param-NAME → concrete-arg mapping, for params nested inside a
        # parameterized declared field type (`List<T>` under `List<Int>`) —
        # the same substitution codegen's generator applies, keeping the two
        # in lockstep.
        tp_names = self._adt_tp_param_names.get(base, ())
        tp_mapping = dict(zip(tp_names, args))
        for ctor_name, layout in layouts.items():
            tp_indices = self._ctor_adt_tp_indices.get(ctor_name)
            for i, (_offset, wasm_type) in enumerate(layout.field_offsets):
                tp_i = (
                    tp_indices[i]
                    if tp_indices is not None and i < len(tp_indices)
                    else None
                )
                if tp_i is not None:
                    # Type-parameter field — its Eq-ness is the concrete type
                    # argument's.
                    if tp_i >= len(args):
                        # No concrete type argument for this parameter (the
                        # #772 residue: a `ConstructorCall` monomorphizes to the
                        # bare ADT name `Box`, dropping `<String>`).  Codegen's
                        # structural generator cannot resolve the field's type
                        # either, so — to stay in lockstep — the gate reports it
                        # NOT derivable (a clean E613) rather than accepting it
                        # and letting codegen hit its loud invariant.  #772
                        # tracks recovering the lost type argument so this path
                        # derives instead of rejecting.
                        return False
                    if not self._type_eq_derivable(args[tp_i], seen):
                        return False
                elif layout.field_types:
                    # Concrete field — dispatch on its DECLARED Vera type,
                    # with nested type params substituted (`List<T>` →
                    # `List<Int>` under a `List<Int>` check, so the recursive
                    # tail hits the `_seen` cycle-break instead of failing on
                    # an unresolved `T`).
                    resolved = substitute_type_param_names(
                        layout.field_types[i], tp_mapping,
                    )
                    if not self._type_eq_derivable(resolved, seen):
                        return False
                elif wasm_type not in ("i64", "i32", "f64"):
                    # Built-in layout without field-type metadata: fall back to
                    # the scalar-rep basis (a non-scalar field is not derivable).
                    return False
        return True

    def _type_eq_derivable(self, name: str, seen: frozenset[str]) -> bool:
        """Is ``name`` Eq-derivable as an ADT field?

        True for an Eq primitive (Int/Nat/Bool/Float64/Byte/Unit **or String**,
        compared by content) or a recursively-Eq ADT.  False for Array / Map /
        host handles / functions — those have no auto-derived Eq.
        """
        base = name.split("<", 1)[0]
        if base in _EQ_TYPES:           # includes String (content comparison)
            return True
        if base in self._adt_layouts:
            return self._adt_satisfies_eq(name, seen)
        return False
