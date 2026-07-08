"""Vera SMT translation layer — AST to Z3 bridge.

Translates Vera AST expressions into Z3 formulas for contract
verification.  Manages solver context, variable declarations,
De Bruijn slot resolution, and counterexample extraction.

See spec/06-contracts.md, Section 6.4 "Verification Conditions".
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from typing import TYPE_CHECKING, Any, Callable

import z3

from vera import ast
from vera.monomorphize import mangle_type_name, unmangle_type_name
from vera.slots import slot_ref_name, type_expr_slot_name
from vera.types import (
    AdtType,
    PRIMITIVES,
    PrimitiveType,
    RefinedType,
    Type,
    TypeVar,
    BOOL,
    FLOAT64,
    INT,
    NAT,
    STRING,
)

if TYPE_CHECKING:
    from vera.environment import AdtInfo


# IEEE-754 binary64 (double): 11 exponent bits, 53 significand bits (#797).
# `@Float64` maps to this FloatingPoint sort so Tier-1 verification respects the
# real machine semantics — NaN, +/-Inf, signed zero, and round-nearest-ties-to-
# even rounding — instead of Z3's exact, unbounded `Real` (which proved
# contracts the runtime then rejected).  Z3's overloaded operators on FP terms
# default to RNE, so `_translate_binary` needs no rounding-mode change.
_FLOAT64_SORT = z3.FPSort(11, 53)

# i64 range — the codegen target width for @Int and the trap boundary for
# float_to_int's `i64.trunc_f64_s` (#807).
_I64_MIN = -(2**63)
_I64_MAX = 2**63 - 1


def _wasm_fp_max(a: z3.FPRef, b: z3.FPRef) -> z3.FPRef:
    """Z3 model of WASM ``f64.max`` (#807).

    Z3's own ``z3.fpMax`` does NOT match WASM: SMT-LIB ``fp.max`` returns the
    *other* operand when one is NaN and leaves the ±0 case implementation-
    defined, whereas WASM ``f64.max`` PROPAGATES NaN and returns ``+0`` for any
    ``max(±0, ∓0)``.  Modeling ``float_clamp`` with ``z3.fpMax`` would therefore
    be unsound (it would prove ``!float_is_nan(clamp(NaN, …))``).  This builds
    the faithful WASM semantics explicitly:

      - either operand NaN → NaN;
      - strictly greater operand wins;
      - on a tie (includes ±0 and equal values): both ±0 → ``+0`` unless BOTH
        are ``-0`` (in which case ``-0``); otherwise the (equal) operand.
    """
    return z3.If(
        z3.Or(z3.fpIsNaN(a), z3.fpIsNaN(b)),
        z3.fpNaN(_FLOAT64_SORT),
        z3.If(
            z3.fpGT(a, b),
            a,
            z3.If(
                z3.fpGT(b, a),
                b,
                z3.If(
                    z3.And(z3.fpIsZero(a), z3.fpIsZero(b)),
                    z3.If(
                        z3.And(z3.fpIsNegative(a), z3.fpIsNegative(b)),
                        z3.fpMinusZero(_FLOAT64_SORT),
                        z3.fpPlusZero(_FLOAT64_SORT),
                    ),
                    a,
                ),
            ),
        ),
    )


def _wasm_fp_min(a: z3.FPRef, b: z3.FPRef) -> z3.FPRef:
    """Z3 model of WASM ``f64.min`` (#807) — the ``min`` dual of
    :func:`_wasm_fp_max`.  NaN propagates; on a ±0 tie WASM returns ``-0`` if
    EITHER operand is ``-0`` (otherwise ``+0``)."""
    return z3.If(
        z3.Or(z3.fpIsNaN(a), z3.fpIsNaN(b)),
        z3.fpNaN(_FLOAT64_SORT),
        z3.If(
            z3.fpLT(a, b),
            a,
            z3.If(
                z3.fpLT(b, a),
                b,
                z3.If(
                    z3.And(z3.fpIsZero(a), z3.fpIsZero(b)),
                    z3.If(
                        z3.Or(z3.fpIsNegative(a), z3.fpIsNegative(b)),
                        z3.fpMinusZero(_FLOAT64_SORT),
                        z3.fpPlusZero(_FLOAT64_SORT),
                    ),
                    a,
                ),
            ),
        ),
    )


# =====================================================================
# Slot environment — De Bruijn → Z3 variable mapping
# =====================================================================

@dataclass
class SlotEnv:
    """Maps Vera typed De Bruijn indices to Z3 variables.

    Maintains a stack per type name.  Index 0 = most recent binding
    (last element in the list), matching De Bruijn convention.
    """

    _stacks: dict[str, list[z3.ExprRef]] = field(default_factory=dict)

    def resolve(self, type_name: str, index: int) -> z3.ExprRef | None:
        """Look up @Type.index in the current scope."""
        stack = self._stacks.get(type_name, [])
        pos = len(stack) - 1 - index
        if 0 <= pos < len(stack):
            return stack[pos]
        return None

    def push(self, type_name: str, expr: z3.ExprRef) -> SlotEnv:
        """Return a new environment with *expr* pushed for *type_name*."""
        new_stacks = {k: list(v) for k, v in self._stacks.items()}
        new_stacks.setdefault(type_name, []).append(expr)
        return SlotEnv(new_stacks)


# =====================================================================
# SMT result
# =====================================================================

@dataclass
class SmtResult:
    """Outcome of a Z3 validity check."""

    status: str  # "verified" | "violated" | "unknown" | "unsupported"
    counterexample: dict[str, str] | None = None  # slot_name → value


@dataclass
class CallViolation:
    """Records a call site where a callee's precondition may not hold."""

    callee_name: str
    call_node: ast.FnCall | ast.ModuleCall
    precondition: ast.Requires
    counterexample: dict[str, str] | None = None


@dataclass
class CallDemotion:
    """Records a call site whose precondition obligation cannot be checked
    statically (#882).

    Emitted when a callee has a non-trivial ``requires`` but the call cannot
    be translated to Z3 — an argument or the precondition itself uses a
    construct outside the decidable fragment (e.g. an ADT field of a
    host-handle type like ``Map``).  The verifier turns this into a LOUD
    Tier-3 obligation (E532) rather than letting the precondition obligation
    silently not exist: DESIGN.md degrades loudly, and the runtime guard
    still enforces the contract.
    """

    callee_name: str
    call_node: ast.FnCall | ast.ModuleCall
    precondition: ast.Requires


# =====================================================================
# SMT context — solver and translation
# =====================================================================

# Z3 operator mapping for binary expressions
_ARITH_OPS: dict[ast.BinOp, str] = {
    ast.BinOp.ADD: "+",
    ast.BinOp.SUB: "-",
    ast.BinOp.MUL: "*",
    ast.BinOp.DIV: "/",
    ast.BinOp.MOD: "%",
}

_CMP_OPS: dict[ast.BinOp, str] = {
    ast.BinOp.EQ: "==",
    ast.BinOp.NEQ: "!=",
    ast.BinOp.LT: "<",
    ast.BinOp.GT: ">",
    ast.BinOp.LE: "<=",
    ast.BinOp.GE: ">=",
}

_BOOL_OPS: set[ast.BinOp] = {ast.BinOp.AND, ast.BinOp.OR, ast.BinOp.IMPLIES}


# =====================================================================
# ADT type helpers
# =====================================================================

def _adt_sort_key(adt_name: str, type_args: tuple[Type, ...]) -> str:
    """Build a canonical key for an ADT sort, e.g. ``List<Int>``."""
    if not type_args:
        return adt_name
    arg_strs = []
    for a in type_args:
        if isinstance(a, PrimitiveType):
            arg_strs.append(a.name)
        elif isinstance(a, AdtType):
            arg_strs.append(_adt_sort_key(a.name, a.type_args))
        else:
            arg_strs.append("?")
    return f"{adt_name}<{', '.join(arg_strs)}>"


def _normalize_int_nat_sort_key(key: str) -> str:
    """Canonicalise an ``_adt_sort_key`` for ``Nat``<->``Int`` carrier equality
    (#918).

    ``Int`` and ``Nat`` share a Z3 carrier (both translate to ``IntSort``); the
    distinction is a refinement (``Nat = {n : Int | n >= 0}``), not a different
    materialised datatype-argument sort's *carrier*.  But post-#884 the ADT
    datatype-sort mangling is injective, so ``Option<Int>`` and ``Option<Nat>``
    are DISTINCT Z3 sorts.  When a constructor argument's type is recovered from
    its Z3 sort the ``Nat`` reads back as ``Int`` (the shared carrier is all the
    sort carries), so a pin can name ``Option<Int>`` where the context built
    ``Option<Nat>``.  Mapping every whole-word ``Nat`` to ``Int`` lets such keys
    compare equal, so the pin selects the already-cached ``Nat`` instantiation
    instead of a fresh mismatched ``Int`` one.  The word boundary is regex-based
    so a user ADT literally named ``Nat...`` (e.g. ``NatBox``) is untouched.
    """
    return re.sub(r"(?<![A-Za-z0-9_])Nat(?![A-Za-z0-9_])", "Int", key)


def _z3_sort_name(key: str) -> str:
    """Derive a Z3-legal datatype name from a canonical sort key (#881, #884).

    Single choke point for the ``key -> z3.Datatype`` name transformation that
    was previously inlined at each ``z3.Datatype(...)`` site (#881, centralised
    so mutually-recursive group members and tuples name themselves
    identically).  The transform MUST be **injective** in the type key: Z3's
    per-context datatype cache conflates same-named sorts (last ``create()``
    wins and retroactively mutates earlier ones), so a lossy collision (e.g.
    ``Box<Int>`` and a flat user ADT ``Box_Int`` both sanitizing to
    ``Box_Int``) makes one sort adopt the other's constructors — a false E500
    counterexample on valid code (#884).  Route through the injective #775
    mangler rather than the old lossy ``<``/``>``/``", "`` replacement.
    """
    return mangle_type_name(key)


def _substitute_type(ty: Type, subst: dict[str, Type]) -> Type:
    """Substitute ``TypeVar`` names in *ty* using *subst*."""
    if isinstance(ty, TypeVar):
        return subst.get(ty.name, ty)
    if isinstance(ty, AdtType):
        new_args = tuple(_substitute_type(a, subst) for a in ty.type_args)
        return AdtType(ty.name, new_args)
    return ty


class SmtContext:
    """Z3 solver context with AST-to-Z3 expression translation."""

    def __init__(
        self,
        timeout_ms: int = 10_000,
        fn_lookup: Callable[[str], Any] | None = None,
        module_fn_lookup: (
            Callable[[tuple[str, ...], str], Any] | None
        ) = None,
    ) -> None:
        self.solver = z3.Solver()
        self.solver.set("timeout", timeout_ms)
        # Retained so reset() can re-apply it on warm-session reuse.
        self._timeout_ms = timeout_ms
        self._vars: dict[str, z3.ExprRef] = {}
        self._result_var: z3.ExprRef | None = None
        # Uninterpreted functions for length (constrained >= 0)
        # Keyed by domain sort — supports both Int and ADT domains
        self._length_fns: dict[str, z3.FuncDeclRef] = {
            "Int": z3.Function("length", z3.IntSort(), z3.IntSort()),
        }
        # Uninterpreted index functions for `arr[i]` translation
        # (#667).  Keyed by array sort name so each (Array<T>)
        # gets its own typed signature `Array_<T> × Int → <T>`.
        self._index_fns: dict[str, z3.FuncDeclRef] = {}
        # Reverse map from array-sort-name → element sort, populated
        # whenever an Array_<T> sort is created.  Avoids fragile
        # string-parsing recovery (#667 follow-up): for ADT element
        # types, the Z3 sort name has `<`/`>` stripped (via the
        # transformation in `_get_or_create_adt_sort`) so a naive
        # `str(elt_sort)` round-trip doesn't recover the canonical
        # `_adt_sort_key` form used by `_z3_sorts`.  Storing the
        # element sort at creation time is the durable fix.
        self._array_element_sorts: dict[str, z3.SortRef] = {}
        # Callee contract verification
        self._fn_lookup = fn_lookup
        self._module_fn_lookup = module_fn_lookup
        self._call_violations: list[CallViolation] = []
        # #882: call sites whose precondition obligation cannot be checked
        # statically (untranslatable ADT-argument, etc.) — demoted to a loud
        # Tier-3 by the verifier rather than silently dropped.
        self._call_demotions: list[CallDemotion] = []
        self._fresh_counter: int = 0
        # Path conditions accumulated from if/match branches so that
        # call-site precondition checks can see which branch is active.
        self._path_conditions: list[z3.ExprRef] = []
        # Optional hook (injected by the verifier) returning the source-type
        # facts a constructor pattern's refined / @Nat sub-pattern bindings
        # carry, so a match arm body's call PRECONDITIONS see them (CR
        # PR-review).  Signature: (scrutinee_ast, scrutinee_z3, pattern, smt)
        # -> list[z3 fact].  None when no verifier is driving (pure-SMT tests).
        self._subpattern_fact_hook: Any = None
        # ADT support
        self._adt_registry: dict[str, AdtInfo] = {}
        self._ctor_to_adt: dict[str, str] = {}  # ctor name → ADT name
        self._z3_sorts: dict[str, z3.SortRef] = {}  # "List<Int>" → Z3 sort

    # -----------------------------------------------------------------
    # Variable management
    # -----------------------------------------------------------------

    def declare_int(self, name: str) -> z3.ArithRef:
        """Declare a Z3 integer variable."""
        v = z3.Int(name)
        self._vars[name] = v
        return v

    def declare_bool(self, name: str) -> z3.BoolRef:
        """Declare a Z3 boolean variable."""
        v = z3.Bool(name)
        self._vars[name] = v
        return v

    def declare_nat(self, name: str) -> z3.ArithRef:
        """Declare a Z3 integer variable constrained >= 0 (for Nat)."""
        v = z3.Int(name)
        self._vars[name] = v
        self.solver.add(v >= 0)
        return v

    def declare_string(self, name: str) -> z3.SeqRef:
        """Declare a Z3 string variable (sequence sort)."""
        v = z3.String(name)
        self._vars[name] = v
        return v

    def declare_float64(self, name: str) -> z3.FPRef:
        """Declare a Z3 FloatingPoint variable (IEEE-754 binary64, #797)."""
        v = z3.FP(name, _FLOAT64_SORT)
        self._vars[name] = v
        return v

    # -----------------------------------------------------------------
    # Array support (#667 — IndexExpr / ArrayLit / Float64 contract
    # predicates).  Pre-#667 `Array<T>` parameters fell through to
    # `declare_int` and the Array-element/Index/Lit constructs in
    # contracts returned None from `translate_expr`, dropping every
    # affected predicate to Tier 3 (runtime check).  The model here
    # is the same uninterpreted-function shape the existing `length`
    # function uses: an `Array<T>` slot is a constant of a fresh
    # `Array_<elt>` uninterpreted sort; `arr[i]` is `index_<elt>(arr,
    # i)`.  Sound but partial — the verifier can prove relational
    # facts ("if `i < length(arr)` and `arr[i] > 0` then ...") but
    # not anything that requires knowing element structure (e.g.
    # "for all valid i, arr[i] > 0").  Quantified contracts are
    # tracked separately as part of #427 (Tier 2 verification).
    # -----------------------------------------------------------------

    def _get_array_sort(self, element_sort: z3.SortRef) -> z3.SortRef:
        """Get-or-create an uninterpreted ``Array_<elt>`` sort
        keyed by the element sort's string name.

        Also populates ``_array_element_sorts`` with the
        element-sort association, so the reverse lookup in
        ``_get_element_sort_for_array`` can recover the element
        sort by direct map lookup rather than by parsing the
        Z3 sort name string."""
        key = f"Array_{element_sort}"
        if key in self._z3_sorts:
            return self._z3_sorts[key]
        sort = z3.DeclareSort(key)
        self._z3_sorts[key] = sort
        # Record the (array-sort-name → element-sort) association
        # for `_get_element_sort_for_array`'s reverse lookup.
        self._array_element_sorts[str(sort)] = element_sort
        return sort

    def _get_index_fn(
        self, array_sort: z3.SortRef, element_sort: z3.SortRef,
    ) -> z3.FuncDeclRef:
        """Get-or-create the uninterpreted ``index_<sort>(arr, idx)
        → elt`` function for the given (array, element) pair."""
        key = f"index_{array_sort}"
        if key not in self._index_fns:
            self._index_fns[key] = z3.Function(
                key, array_sort, z3.IntSort(), element_sort,
            )
        return self._index_fns[key]

    def declare_array_var(
        self, name: str, element_sort: z3.SortRef,
    ) -> z3.ExprRef:
        """Declare an Array-typed Z3 constant.  The constant lives
        in the ``Array_<elt>`` uninterpreted sort created by
        ``_get_array_sort``; this matches the rest of the SMT
        layer's pattern of opaque carrier sorts + uninterpreted
        observer functions (length, index)."""
        array_sort = self._get_array_sort(element_sort)
        v = z3.Const(name, array_sort)
        self._vars[name] = v
        return v

    def set_result_var(self, var: z3.ExprRef | None) -> None:
        """Set the variable used for @T.result references."""
        self._result_var = var

    def get_var(self, name: str) -> z3.ExprRef | None:
        """Look up a declared variable by name."""
        return self._vars.get(name)

    def _fresh_name(self, prefix: str) -> str:
        """Generate a unique Z3 variable name."""
        self._fresh_counter += 1
        return f"_call_{prefix}_{self._fresh_counter}"

    def drain_call_violations(self) -> list[CallViolation]:
        """Return accumulated call-site violations and clear the list."""
        violations = list(self._call_violations)
        self._call_violations.clear()
        return violations

    def drain_call_demotions(self) -> list[CallDemotion]:
        """Return accumulated call-site Tier-3 demotions and clear the list
        (#882)."""
        demotions = list(self._call_demotions)
        self._call_demotions.clear()
        return demotions

    def _record_call_demotion(
        self,
        callee_info: Any,
        callee_name: str,
        call_node: ast.FnCall | ast.ModuleCall,
    ) -> None:
        """Record a Tier-3 demotion for an untranslatable call argument (#882).

        The representative precondition is the callee's first non-trivial
        ``requires`` — its expression text and the call-site span locate the
        obligation.  A guard on ``has_nontrivial_pre`` at the call site
        guarantees one exists.
        """
        contract = next(
            (
                c for c in callee_info.contracts
                if isinstance(c, ast.Requires)
                and not (isinstance(c.expr, ast.BoolLit) and c.expr.value)
            ),
            None,
        )
        if contract is None:  # pragma: no cover — guarded by has_nontrivial_pre
            return
        self._record_call_demotion_for(callee_name, call_node, contract)

    def _record_call_demotion_for(
        self,
        callee_name: str,
        call_node: ast.FnCall | ast.ModuleCall,
        contract: ast.Requires,
    ) -> None:
        """Record one Tier-3 call-pre demotion, deduped by (precondition,
        call-site span) exactly like :class:`CallViolation` (#882).

        The same call site is translated more than once per function (the
        primitive-op / @Nat walkers re-translate RHSes and operands), so this
        keeps a single demotion per site regardless of how many passes visit
        it.  A demoted site must also not double-count as a violation, so the
        two lists share the same span key.
        """
        already = any(
            d.precondition is contract
            and (
                d.call_node.span == call_node.span
                if (
                    d.call_node.span is not None
                    and call_node.span is not None
                )
                else d.call_node is call_node
            )
            for d in self._call_demotions
        )
        if not already:
            self._call_demotions.append(CallDemotion(
                callee_name=callee_name,
                call_node=call_node,
                precondition=contract,
            ))

    # -----------------------------------------------------------------
    # ADT support
    # -----------------------------------------------------------------

    def register_adt(self, adt_info: AdtInfo) -> None:
        """Register an ADT definition for Z3 sort creation."""
        self._adt_registry[adt_info.name] = adt_info
        for ctor_name in adt_info.constructors:
            self._ctor_to_adt[ctor_name] = adt_info.name

    def declare_adt(
        self, name: str, ty: Type,
    ) -> z3.ExprRef | None:
        """Declare a Z3 constant of an ADT sort.

        Unwraps a refinement OVER an ADT base (`{ @Box | P }`) to its base
        sort, so a refined-ADT param/return is declared with the ADT sort
        rather than falling to ``declare_int`` (which would make a
        pattern-match / projection see an Int term — a false Tier-3 or a Z3
        sort failure; CR d338946).  Mirrors the array path's internal unwrap."""
        if isinstance(ty, RefinedType):
            ty = ty.base
        z3_sort = self._vera_type_to_z3_sort(ty)
        if z3_sort is None:
            return None
        v = z3.Const(name, z3_sort)
        self._vars[name] = v
        return v

    def _vera_type_to_z3_sort(
        self,
        ty: Type,
        *,
        builders: dict[str, z3.Datatype] | None = None,
    ) -> z3.SortRef | None:
        """Map a Vera Type to a Z3 sort.

        Returns None for unsupported types (Unit, TypeVar, function types).
        String maps to z3.StringSort(); Float64 maps to z3.FPSort(11, 53) (#797).

        *builders* holds the in-progress ``z3.Datatype`` objects for every ADT
        instantiation currently being constructed together as one mutually-
        recursive group (#881).  A field whose type is one of those keys
        resolves to its builder — Z3 stitches the forward reference at
        ``CreateDatatypes`` time.  The self-recursive case (``Cons(Int, Self)``)
        is just the singleton-group instance of this; before #881 it was a
        dedicated ``self_ref_key``/``self_ref_dt`` pair that could not span two
        types, so a mutual pair (``A`` field ``B``, ``B`` field ``A``) recursed
        unboundedly into fresh sort creation and raised a raw ``RecursionError``
        on a check-green program.
        """
        if isinstance(ty, RefinedType):
            # A refinement's Z3 SORT is its base's sort — the predicate
            # constrains values, not the carrier set, and is enforced
            # separately (as an assumption / obligation).  Unwrap HERE, not only
            # at the `declare_adt` call site, so a refined type nested as a
            # tuple component or constructor field (`Tuple<PosInt, Int>`,
            # `Box(PosInt)`) resolves to its base sort instead of None — which
            # would otherwise fail the enclosing tuple / datatype sort creation
            # and silently degrade the whole structure to a weaker model (CR
            # PR-review).
            ty = ty.base
        if isinstance(ty, PrimitiveType):
            if ty.name in ("Int", "Nat"):
                return z3.IntSort()
            if ty.name == "Bool":
                return z3.BoolSort()
            if ty.name == "String":
                return z3.StringSort()
            if ty.name == "Float64":
                return _FLOAT64_SORT
            return None
        if isinstance(ty, AdtType):
            key = _adt_sort_key(ty.name, ty.type_args)
            # In-progress member of the current mutually-recursive group:
            # hand back its builder so Z3 resolves the forward reference.
            if builders is not None and key in builders:
                return builders[key]
            return self._get_or_create_adt_sort(ty.name, ty.type_args)
        return None

    def _collect_adt_group(
        self, root_name: str, root_args: tuple[Type, ...],
    ) -> dict[str, list[tuple[str, tuple[Type, ...] | None]]] | None:
        """Collect every datatype instantiation reachable from the root via
        constructor-field types, skipping ones already cached (#881).

        This is the closure that must be handed to ``z3.CreateDatatypes`` as a
        single group so mutually-recursive datatypes (``A`` references ``B``,
        ``B`` references ``A``) are declared together.  Returns an insertion-
        ordered map ``key -> [(ctor_name, concrete_field_types), ...]``, or
        ``None`` if the root itself is not a registered ADT.  Each member's
        field types are already concrete (type params substituted), so
        construction can resolve them against the shared builder map directly.

        A ``Tuple`` instantiation whose components carry a back-reference to a
        group member (``data C { MkC(Tuple<C, Int>) }``, or a pair ``A``/``B``
        cross-referencing through a ``Tuple`` field) is itself a member of the
        group — modelled as a single-constructor ``Tuple`` datatype whose
        fields are its concrete components.  Building it *inside* the group
        rather than via a fresh ``_get_or_create_adt_sort`` call is what lets
        the back-reference stitch to the in-progress builder; the fresh call
        re-entered sort creation for the still-uncached member and recursed
        unboundedly into the same raw ``RecursionError`` #881 exists to
        eliminate.
        """
        root_info = self._adt_registry.get(root_name)
        if root_info is None:
            return None
        group: dict[str, list[tuple[str, tuple[Type, ...] | None]]] = {}
        worklist: list[tuple[str, tuple[Type, ...]]] = [(root_name, root_args)]
        while worklist:
            name, args = worklist.pop()
            key = _adt_sort_key(name, args)
            if key in group or key in self._z3_sorts:
                continue
            info = self._adt_registry.get(name)
            if info is None:
                if name == "Tuple" and args:
                    # A Tuple reachable through a member's field is itself a
                    # group member: a single ``Tuple`` constructor whose fields
                    # are its (already-concrete) components.  Enqueue those
                    # components so any ADT back-reference they carry joins the
                    # group and stitches to a shared builder at create time.
                    group[key] = [("Tuple", args)]
                    for a in args:
                        self._enqueue_adt_types(a, worklist)
                    continue
                # Any other non-registered type (e.g. a nested type arg):
                # its own sort is built independently; only its type args may
                # carry further group members, enqueued below.
                for a in args:
                    self._enqueue_adt_types(a, worklist)
                continue
            subst: dict[str, Type] = {}
            if info.type_params:
                if len(args) != len(info.type_params):  # pragma: no cover
                    return None
                subst = dict(zip(info.type_params, args))
            ctors: list[tuple[str, tuple[Type, ...] | None]] = []
            for ctor_name, ctor_info in info.constructors.items():
                if ctor_info.field_types is None:
                    ctors.append((ctor_name, None))
                    continue
                concrete = tuple(
                    _substitute_type(ft, subst)
                    for ft in ctor_info.field_types
                )
                ctors.append((ctor_name, concrete))
                for ft in concrete:
                    self._enqueue_adt_types(ft, worklist)
            group[key] = ctors
        return group

    @staticmethod
    def _enqueue_adt_types(
        ty: Type, worklist: list[tuple[str, tuple[Type, ...]]],
    ) -> None:
        """Push every ``AdtType`` occurring in *ty* (itself and nested type
        args) onto *worklist* for group discovery (#881)."""
        if isinstance(ty, RefinedType):
            SmtContext._enqueue_adt_types(ty.base, worklist)
        elif isinstance(ty, AdtType):
            worklist.append((ty.name, ty.type_args))
            for a in ty.type_args:
                SmtContext._enqueue_adt_types(a, worklist)

    def _get_or_create_adt_sort(
        self,
        adt_name: str,
        type_args: tuple[Type, ...],
    ) -> z3.SortRef | None:
        """Lazily create a Z3 ADT sort for a concrete type instantiation.

        Datatypes reachable from *adt_name* through constructor fields are
        declared together via ``z3.CreateDatatypes`` (#881), so a mutually-
        recursive group (``A`` referencing ``B`` and vice versa) resolves in a
        single pass instead of recursing unboundedly into fresh sort creation.
        A self-recursive datatype is the singleton-group case.
        """
        key = _adt_sort_key(adt_name, type_args)
        if key in self._z3_sorts:
            return self._z3_sorts[key]

        adt_info = self._adt_registry.get(adt_name)
        if adt_info is None:
            # #747: Tuple is variadic and never registered as an ADT, so it
            # would otherwise fall back to a scalar Int.  Synthesise a
            # single-constructor datatype on demand so its components are
            # projectable (non-literal tuple-destructure obligations).
            if adt_name == "Tuple" and type_args:
                return self._get_or_create_tuple_sort(key, type_args)
            return None

        group = self._collect_adt_group(adt_name, type_args)
        if group is None:  # pragma: no cover — guarded by adt_info check above
            return None

        # One builder per group member, all referenceable while resolving
        # fields so cross-references (mutual or self, direct or Tuple-mediated)
        # stitch at create time (#881).  Each builder's Z3-visible name comes
        # from `_z3_sort_name`, which is injective in the type key (#884): a
        # lossy collision (e.g. `Box<Int>` vs a flat `Box_Int`) would make Z3's
        # per-context datatype cache conflate the two sorts and adopt one's
        # constructors for the other — a false E500 on valid code.
        builders: dict[str, z3.Datatype] = {
            member_key: z3.Datatype(_z3_sort_name(member_key))
            for member_key in group
        }
        for member_key, ctors in group.items():
            dt = builders[member_key]
            for ctor_name, field_types in ctors:
                if field_types is None:
                    dt.declare(ctor_name)
                    continue
                fields: list[tuple[str, Any]] = []
                for i, ft in enumerate(field_types):
                    z3_sort = self._vera_type_to_z3_sort(
                        ft, builders=builders)
                    if z3_sort is None:
                        # A field's sort is unsupported: abandon the whole
                        # group uncached (matches the pre-#881 single-sort
                        # None return; a later obligation may retry).
                        return None
                    fields.append((f"{ctor_name}_{i}", z3_sort))
                dt.declare(ctor_name, *fields)

        ordered_keys = list(group)
        created = z3.CreateDatatypes(*(builders[k] for k in ordered_keys))
        # CreateDatatypes returns one sort per builder, in the same order.
        for member_key, sort in zip(ordered_keys, created):
            self._z3_sorts[member_key] = sort
        return self._z3_sorts[key]

    def _get_or_create_tuple_sort(
        self, key: str, type_args: tuple[Type, ...],
    ) -> z3.SortRef | None:
        """#747: synthesise a Z3 datatype for a concrete ``Tuple`` instance.

        The variadic ``Tuple`` type is never in the ADT registry, so without
        this it falls back to a scalar ``Int``.  One ``Tuple`` constructor
        with a field per component makes the components projectable via
        accessors — needed for non-literal tuple-destructure narrowing
        obligations.  Cached like any other ADT sort.
        """
        dt = z3.Datatype(_z3_sort_name(key))
        fields: list[tuple[str, Any]] = []
        for i, ft in enumerate(type_args):
            z3_sort = self._vera_type_to_z3_sort(ft, builders={key: dt})
            if z3_sort is None:
                return None
            fields.append((f"Tuple_{i}", z3_sort))
        dt.declare("Tuple", *fields)
        sort = dt.create()
        self._z3_sorts[key] = sort
        return sort

    def _get_length_fn(self, sort: z3.SortRef) -> z3.FuncDeclRef:
        """Get or create a length function for the given domain sort."""
        key = str(sort)
        if key not in self._length_fns:  # pragma: no cover
            fn_name = f"length_{key}"
            self._length_fns[key] = z3.Function(
                fn_name, sort, z3.IntSort(),
            )
        return self._length_fns[key]

    def get_rank_fn(self, sort: z3.SortRef) -> z3.FuncDeclRef | None:
        """Get or create a rank function for structural ordering on an ADT.

        Adds axioms: ``rank(x) >= 0`` and for each constructor with
        recursive fields, ``is_Ctor(x) ==> rank(field_i(x)) < rank(x)``.

        Returns None if the sort is not a Z3 DatatypeSortRef.
        """
        if not isinstance(sort, z3.DatatypeSortRef):  # pragma: no cover
            return None
        key = f"_rank_{sort}"
        if key in self._length_fns:  # pragma: no cover
            return self._length_fns[key]
        rank = z3.Function(key, sort, z3.IntSort())
        self._length_fns[key] = rank
        # Add axioms via a universally-quantified variable
        x = z3.Const("_rank_x", sort)
        self.solver.add(z3.ForAll([x], rank(x) >= 0))
        # For each constructor, add structural decrease axioms
        for i in range(sort.num_constructors()):
            ctor = sort.constructor(i)
            recognizer = sort.recognizer(i)
            for j in range(ctor.arity()):
                accessor = sort.accessor(i, j)
                if accessor.range() == sort:
                    # Recursive field: rank(field) < rank(parent)
                    self.solver.add(z3.ForAll(
                        [x],
                        z3.Implies(
                            recognizer(x),
                            rank(accessor(x)) < rank(x),
                        ),
                    ))
        return rank

    # -----------------------------------------------------------------
    # Expression translation
    # -----------------------------------------------------------------

    def translate_expr(
        self, expr: ast.Expr, env: SlotEnv
    ) -> z3.ExprRef | None:
        """Translate a Vera AST expression to a Z3 formula.

        Returns None if the expression contains unsupported constructs
        (triggers Tier 3 fallback).

        # WALKER_COVERAGE: (#597 — every Expr subclass below has a
        # disposition; check_walker_coverage.py enforces completeness.
        # SMT translation is intentionally narrow — contracts permit
        # a subset of expression shapes — so most Expr subclasses are
        # either "Cannot occur in contract context" or "deliberately
        # unsupported pending issue-tracked expansion".)
        #
        # Handled (explicit isinstance branch):
        #   IntLit            → z3.IntVal
        #   BoolLit           → z3.BoolVal
        #   StringLit         → z3.StringVal
        #   FloatLit          → z3.FPVal (Float64 → FloatingPoint sort, #797)
        #   SlotRef           → bound Z3 variable
        #   ResultRef         → @Result substitution variable
        #   BinaryExpr        → translated by op family
        #   UnaryExpr         → translated by op family
        #   IfExpr            → If(cond, then, else)
        #   FnCall            → user-fn uninterpreted function or
        #                       built-in axiomatised translation
        #   ModuleCall        → cross-module fn lookup
        #   Block             → trailing-expr translation
        #   MatchExpr         → arm dispatch
        #   ConstructorCall   → ADT constructor application
        #   NullaryConstructor → ADT nullary tag
        #   QualifiedCall     → effect op; NOT Z3-translated (returns None),
        #                       but its args are walked for the E501
        #                       precondition side effect (#776)
        #   IndexExpr         → uninterpreted `index_<sort>(arr, i)`
        #                       function call (#667)
        #   ArrayLit          → fresh Array constant with asserted
        #                       length and per-element values (#667)
        #
        # Intentionally ignored (returns None → Tier 3 fallback;
        # listed in the inline comment after the dispatch chain):
        #   AnonFn            → lambdas not in contract grammar
        #   HandleExpr        → handle-effect not in contract grammar
        #   ForallExpr        → quantifier translation deferred (#427)
        #   ExistsExpr        → quantifier translation deferred (#427)
        #   OldExpr           → contract operator; Tier 3 fallback
        #   NewExpr           → contract operator; Tier 3 fallback
        #   AssertExpr        → statement-like; not a predicate
        #   AssumeExpr        → statement-like; not a predicate
        #   UnitLit           → predicates are Bool, not Unit
        #
        # Cannot occur (rejected at check time or not in contracts):
        #   InterpolatedString → not in contract predicates
        #   HoleExpr          → check time rejects
        """
        if isinstance(expr, ast.IntLit):
            return z3.IntVal(expr.value)

        if isinstance(expr, ast.BoolLit):
            return z3.BoolVal(expr.value)

        if isinstance(expr, ast.StringLit):
            # #802: Z3's string sort cannot faithfully model two kinds of code
            # point, so a literal containing either defers to Tier 3 (return
            # None) rather than be reasoned over as a corrupted term.  For both,
            # the Python binding silently stores the code point's *escape text*
            # instead of the character (e.g. z3.StringVal("\U00030000") holds
            # "\u{5c}u{30000}" — the backslash itself becomes "\u{5c}"), so
            # Contains/PrefixOf/SuffixOf match phantom ASCII bytes the runtime
            # never sees, proving false contracts.  The two cases:
            #   - above the alphabet (> U+2FFFF); and
            #   - a lone surrogate (U+D800..U+DFFF), which additionally has no
            #     UTF-8 encoding at all (see string_length below).
            # We must return None *before* z3.StringVal sees either.  (string_length
            # models a literal via its UTF-8 byte count, not z3.StringVal, so it
            # is unaffected by the alphabet limit — but it too must guard the
            # surrogate case, below, where the byte encoding genuinely fails.)
            if any(ord(ch) > 0x2FFFF or 0xD800 <= ord(ch) <= 0xDFFF
                   for ch in expr.value):
                return None
            return z3.StringVal(expr.value)

        if isinstance(expr, ast.FloatLit):
            # #797: Float64 maps to Z3's IEEE-754 binary64 FloatingPoint sort, so
            # a literal is an FPVal at that sort (the source decimal is rounded to
            # the nearest double on construction, exactly as the runtime does).
            return z3.FPVal(expr.value, _FLOAT64_SORT)

        if isinstance(expr, ast.IndexExpr):
            # #667: `arr[i]` translates to `index_<sort>(arr, i)`
            # where `index_<sort>` is an uninterpreted function
            # specific to the array's sort.  Sound — the verifier
            # can reason that two references to `arr[i]` with the
            # same `i` produce the same value (function congruence)
            # — but doesn't know element structure beyond what
            # explicit predicates assert.
            return self._translate_index_expr(expr, env)

        if isinstance(expr, ast.ArrayLit):
            # #667: `[a, b, c]` translates to a fresh constant of
            # the appropriate Array sort, with `length(lit) == N`
            # and `index(lit, i) == translate(elem_i)` asserted to
            # the solver for each known position.  Element types
            # that can't be sorted (e.g. function-typed elements)
            # fail the translation cleanly via None.
            return self._translate_array_lit(expr, env)

        if isinstance(expr, ast.SlotRef):
            return self._translate_slot_ref(expr, env)

        if isinstance(expr, ast.ResultRef):
            return self._result_var

        if isinstance(expr, ast.BinaryExpr):
            return self._translate_binary(expr, env)

        if isinstance(expr, ast.UnaryExpr):
            return self._translate_unary(expr, env)

        if isinstance(expr, ast.IfExpr):
            return self._translate_if(expr, env)

        if isinstance(expr, ast.FnCall):
            return self._translate_call(expr, env)

        if isinstance(expr, ast.ModuleCall):
            return self._translate_module_call(expr, env)

        if isinstance(expr, ast.Block):
            return self._translate_block(expr, env)

        if isinstance(expr, ast.MatchExpr):
            return self._translate_match(expr, env)

        if isinstance(expr, ast.NullaryConstructor):
            return self._translate_nullary_ctor(expr)

        if isinstance(expr, ast.ConstructorCall):
            return self._translate_ctor_call(expr, env)

        if isinstance(expr, ast.QualifiedCall):
            # #776: an effect op (e.g. IO.print(...)) is itself untranslatable
            # (effects in contracts violate purity — Z3-translating it would be
            # unsound), but its ARGUMENTS may contain a call whose precondition
            # must still be statically checked (E501).  Mirror the #730 ExprStmt
            # handling: walk each arg for the precondition side effect, dropping
            # the value, then return None so the effect op itself never becomes a
            # Z3 term.  The #727 span-keyed dedup keeps re-translation
            # duplicate-free.
            #
            # The walk runs inside `solver.push()` / `pop()`, and that scoping is
            # load-bearing, not tidiness.  Translating a `FnCall` argument does
            # more than record its E501: `_translate_call_with_info` ASSUMES the
            # callee's `ensures` via a bare `self.solver.add(z3_post)`, which
            # lands on the solver's BASE assertion stack.  `_path_conditions` are
            # folded in by `check_valid` around the *goal* only, so an assumed
            # postcondition otherwise escapes the `if` branch it was translated
            # under and becomes an unconditional fact about the CALLER's slots
            # (`_build_callee_env` binds the callee's params to the caller's
            # terms).  It is even circular: `dec5 requires(@Nat.0 >= 5)
            # ensures(@Nat.result == @Nat.0 - 5)` injects `ret == @Nat.0 - 5`,
            # which with `@Nat`'s implicit `ret >= 0` entails `@Nat.0 >= 5` — the
            # very precondition that licensed the assumption.  A caller's false
            # `ensures(@Nat.0 >= 5)` then proves at Tier 1, no runtime check is
            # emitted, and `vera run` violates the contract.
            #
            # Push/pop keeps the assumption scoped to the argument expression
            # that earned it (so a nested `show(mag(x))` still discharges `show`'s
            # precondition from `mag`'s postcondition) while discarding it before
            # the caller's own obligations are checked.  Obligations and
            # diagnostics are recorded in Python state, so `pop()` cannot erase
            # them.  Discarding a fact can only make a later goal *less* provable
            # — the fail-closed direction.  (PR #953 review.  The same unguarded
            # assumption is reachable on `main` through the #730 statement-position
            # walk and is tracked separately; this branch must not widen it.)
            self.solver.push()
            try:
                for arg in expr.args:
                    self.translate_expr(arg, env)
            finally:
                self.solver.pop()
            return None

        # Unsupported: handle, lambdas, quantifiers,
        # old/new, assert/assume, etc.
        return None

    def _translate_slot_ref(
        self, ref: ast.SlotRef, env: SlotEnv
    ) -> z3.ExprRef | None:
        """Translate @Type.n to the corresponding Z3 variable."""
        # Shared recursive builder (#914 finding 2) — fully-qualified nested
        # type args, matching the env-key side and the checker so the
        # verifier resolves the SAME slot the checker did (a one-level name
        # collided distinct nested composites like `Option<Tuple<Int, Int>>`
        # vs `Option<Tuple<Bool, Bool>>` into one `Option<Tuple>` stack).
        type_name = slot_ref_name(ref)
        if type_name is None:  # pragma: no cover — complex type arg
            return None
        return env.resolve(type_name, ref.index)

    def _translate_binary(
        self, expr: ast.BinaryExpr, env: SlotEnv
    ) -> z3.ExprRef | None:
        """Translate binary operators."""
        # Pipe: a |> f(x, y) → f(a, x, y)
        if expr.op == ast.BinOp.PIPE:
            if isinstance(expr.right, ast.FnCall):
                desugared = ast.FnCall(
                    name=expr.right.name,
                    args=(expr.left,) + expr.right.args,
                    span=expr.span,
                )
                return self._translate_call(desugared, env)
            if isinstance(expr.right, ast.ModuleCall):
                desugared_mc = ast.ModuleCall(
                    path=expr.right.path,
                    name=expr.right.name,
                    args=(expr.left,) + expr.right.args,
                    span=expr.span,
                )
                return self._translate_module_call(desugared_mc, env)
            return None  # unsupported RHS  # pragma: no cover

        left = self.translate_expr(expr.left, env)
        right = self.translate_expr(expr.right, env)
        if left is None or right is None:
            return None
        # #797 defense-in-depth: a binary op mixing an FP operand with a non-FP
        # one would raise a Z3 sort mismatch (there is no Int<->FP coercion).
        # The checker rejects mixed Float64/Int arithmetic (E141), equality
        # (E142), and ordering (E142), so this is unreachable on well-typed
        # input — but degrade to Tier 3 rather than crash if a checker gap ever
        # lets one through.
        if isinstance(left, z3.FPRef) != isinstance(right, z3.FPRef):
            return None

        op = expr.op

        # Arithmetic
        if op == ast.BinOp.ADD:
            return left + right
        if op == ast.BinOp.SUB:
            return left - right
        if op == ast.BinOp.MUL:
            return left * right
        if op == ast.BinOp.DIV:
            # #799: Vera `/` is `i64.div_s` (truncates toward zero); Z3's
            # integer `/` is Euclidean (floors), so they disagree on a negative
            # dividend.  Use a sign-aware truncated encoding for integer
            # operands; Float64 (FP) division is unaffected.
            if left.sort() == z3.IntSort() and right.sort() == z3.IntSort():
                return self._trunc_div(left, right)
            return left / right
        if op == ast.BinOp.MOD:
            # #799: Vera `%` is `i64.rem_s` (remainder takes the dividend's
            # sign); Z3's integer `%` is Euclidean (non-negative remainder).
            if left.sort() == z3.IntSort() and right.sort() == z3.IntSort():
                return self._trunc_mod(left, right)
            if isinstance(left, z3.FPRef):
                # #797: Float64 `%` is the WASM codegen's truncated remainder
                # (`a - trunc(a/b)*b`; see vera/wasm/operators.py
                # `_translate_f64_mod`) — the *naive* form, which is NOT bit-exact
                # C fmod for large `a/b`, but matching codegen (not ideal fmod) is
                # what keeps Tier 1 in lockstep with the runtime — NOT Z3's `fp.rem`
                # (the IEEE round-to-nearest remainder that Python `%` emits).
                # They diverge whenever frac(a/b) >= 0.5 (`5.0 % 3.0` is fmod
                # `2.0` but fp.rem `-1.0`).  Model the exact codegen formula so
                # Tier 1 matches the runtime instead of proving a false value.
                rne = z3.RoundNearestTiesToEven()
                quotient = z3.fpRoundToIntegral(
                    z3.RoundTowardZero(), z3.fpDiv(rne, left, right))
                return z3.fpSub(rne, left, z3.fpMul(rne, quotient, right))
            return left % right

        # Comparison
        if op == ast.BinOp.EQ:
            # #797: Float64 `==` is IEEE equality (WASM `f64.eq`): `NaN != NaN`
            # and `+0.0 == -0.0`.  That is Z3's `fpEQ`, NOT the structural SMT
            # `=` that Python `==` emits on FP terms (under which `NaN = NaN` is
            # true — which would re-introduce the #797 unsoundness).  Ordering
            # ops (`<`/`>`/`<=`/`>=`) already lower to the IEEE `fp.*` predicates
            # via Z3's operator overloads; only `==`/`!=` need this.  #871: an
            # FP value nested in a datatype is a datatype term, so datatype
            # equality routes through `_datatype_value_eq` (per-field `fpEQ`
            # decomposition) instead of structural `=`.  Non-FP equality stays
            # structural.
            if isinstance(left, z3.FPRef):
                return z3.fpEQ(left, right)
            if isinstance(left.sort(), z3.DatatypeSortRef):
                return self._datatype_value_eq(left, right)
            return left == right
        if op == ast.BinOp.NEQ:
            if isinstance(left, z3.FPRef):
                return z3.fpNEQ(left, right)
            if isinstance(left.sort(), z3.DatatypeSortRef):
                eq = self._datatype_value_eq(left, right)
                if eq is None:
                    return None
                return z3.Not(eq)
            return left != right
        if op in (ast.BinOp.LT, ast.BinOp.GT, ast.BinOp.LE, ast.BinOp.GE):
            # #921 defense-in-depth: ordering (`<`/`>`/`<=`/`>=`) is defined
            # only on the orderable primitives (§4.5); a non-orderable operand is
            # a Z3 `DatatypeRef` (ADT) or `BoolRef` (Bool), on which Python's `<`
            # raises `TypeError` — a hard traceback out of the verifier.  The
            # checker rejects `compare` / `<` on a non-orderable type at check
            # time (E242 / E143), but that gate is NOT a backstop here: the
            # verifier monomorphizes generics *minus* the E613 constraint filter
            # (verifier.py), so a `forall<T where Ord<T>>` `compare(@T, @T)`
            # instantiated at `Bool` reaches this point with two `BoolRef`
            # operands — and the direct `verify()` API skips the checker gate
            # entirely.  Both ADT and Bool operands are therefore genuinely
            # reachable here; degrade the ordering to Tier 3 rather than crash.
            # (EQ/NEQ route datatypes through `_datatype_value_eq`; ordering has
            # no structural counterpart, so there is nothing to translate.)
            if (isinstance(left.sort(), (z3.DatatypeSortRef, z3.BoolSortRef))
                    or isinstance(right.sort(), (z3.DatatypeSortRef, z3.BoolSortRef))):
                return None
            if op == ast.BinOp.LT:
                return left < right
            if op == ast.BinOp.GT:
                return left > right
            if op == ast.BinOp.LE:
                return left <= right
            return left >= right
        # Boolean
        if op == ast.BinOp.AND:
            return z3.And(left, right)
        if op == ast.BinOp.OR:
            return z3.Or(left, right)
        if op == ast.BinOp.IMPLIES:
            return z3.Implies(left, right)

        return None  # pragma: no cover

    @staticmethod
    def _trunc_div(a: z3.ExprRef, b: z3.ExprRef) -> z3.ExprRef:
        """Truncated (round-toward-zero) integer division — Vera's ``i64.div_s``.

        Z3's ``a / b`` on ``IntSort`` is Euclidean (floors for ``b > 0``); Vera's
        ``/`` truncates toward zero, so they diverge on a negative dividend
        (``-7 / 2`` is ``-3``, not ``-4``).  Compute the magnitude with Euclidean
        division on absolute values — where the two agree — and reapply the
        sign: the quotient is negative iff exactly one operand is negative
        (#799).  ``b == 0`` stays uninterpreted, exactly as before, so the
        ``div_zero`` obligation (#680) remains the trap guard.
        """
        abs_a = z3.If(a >= 0, a, -a)
        abs_b = z3.If(b >= 0, b, -b)
        mag = abs_a / abs_b
        return z3.If(z3.Xor(a < 0, b < 0), -mag, mag)

    @staticmethod
    def _trunc_mod(a: z3.ExprRef, b: z3.ExprRef) -> z3.ExprRef:
        """Truncated remainder — Vera's ``i64.rem_s``, where the remainder takes
        the dividend's sign (``-7 % 2`` is ``-1``, not Z3's Euclidean ``1``)
        (#799)."""
        abs_a = z3.If(a >= 0, a, -a)
        abs_b = z3.If(b >= 0, b, -b)
        r = abs_a % abs_b
        return z3.If(a < 0, -r, r)

    def _sort_contains_fp(
        self, sort: z3.SortRef, _seen: set[str] | None = None,
    ) -> bool:
        """True if *sort* is an FP sort or a datatype sort with a (transitively)
        FP-sorted field (#871).  Recursive datatypes terminate via *_seen*."""
        if isinstance(sort, z3.FPSortRef):
            return True
        if not isinstance(sort, z3.DatatypeSortRef):
            return False
        seen = _seen if _seen is not None else set()
        name = str(sort)
        if name in seen:
            return False
        seen.add(name)
        for i in range(sort.num_constructors()):
            ctor = sort.constructor(i)
            for j in range(ctor.arity()):
                if self._sort_contains_fp(sort.accessor(i, j).range(), seen):
                    return True
        return False

    def _datatype_value_eq(
        self,
        left: z3.ExprRef,
        right: z3.ExprRef,
        _expanding: frozenset[str] = frozenset(),
    ) -> z3.ExprRef | None:
        """Value equality for same-sorted terms, matching the runtime's ``==``.

        #871: Z3's structural datatype ``=`` agrees with the runtime's
        structural Eq (#870: tags first, then fields pairwise) EXCEPT on
        Float64 fields, where the runtime emits ``f64.eq`` (IEEE: ``NaN !=
        NaN``, ``+0.0 == -0.0``) but structural ``=`` is identity (``NaN =
        NaN``, ``+0.0 != -0.0``) — a false Tier-1 in both directions.  For a
        datatype sort that transitively contains FP, decompose per-field:
        same-constructor recognizers plus field-wise equality (``fpEQ`` for FP
        fields, recursing into nested FP-containing datatypes, structural ``=``
        for everything else — where it matches the runtime).  A RECURSIVE
        FP-containing datatype has no finite expansion; return None so the
        obligation demotes to an honest Tier-3 runtime check rather than a
        false proof (soundness over completeness — DESIGN.md tier row:
        "degrades gracefully where SMT is undecidable").
        """
        sort = left.sort()
        if isinstance(left, z3.FPRef):
            return z3.fpEQ(left, right)
        if (not isinstance(sort, z3.DatatypeSortRef)
                or not self._sort_contains_fp(sort)):
            return left == right
        name = str(sort)
        if name in _expanding:
            return None  # recursive FP-containing datatype: no finite expansion
        expanding = _expanding | {name}
        arms: list[z3.ExprRef] = []
        for i in range(sort.num_constructors()):
            ctor = sort.constructor(i)
            conj: list[z3.ExprRef] = [
                sort.recognizer(i)(left), sort.recognizer(i)(right),
            ]
            for j in range(ctor.arity()):
                acc = sort.accessor(i, j)
                field_eq = self._datatype_value_eq(
                    acc(left), acc(right), expanding)
                if field_eq is None:
                    return None
                conj.append(field_eq)
            arms.append(z3.And(*conj))
        return arms[0] if len(arms) == 1 else z3.Or(*arms)

    def _translate_index_expr(
        self, expr: ast.IndexExpr, env: SlotEnv,
    ) -> z3.ExprRef | None:
        """Translate `coll[idx]` to `index_<sort>(coll, idx)`
        where `index_<sort>` is an uninterpreted function
        specific to the collection's Z3 sort (#667).

        Returns None when either side fails to translate, when
        the collection's sort isn't a recognised Array sort, or
        when the element-sort can't be inferred from the
        collection's sort name.
        """
        coll = self.translate_expr(expr.collection, env)
        idx = self.translate_expr(expr.index, env)
        if coll is None or idx is None:
            return None
        coll_sort = coll.sort()
        # Only Array_<elt> uninterpreted sorts created by
        # `_get_array_sort` are recognised here.  Other sorts
        # (e.g. an Int-fallback Array from a path that hasn't
        # been migrated to `_is_array_type`) fail cleanly.
        sort_name = str(coll_sort)
        if not sort_name.startswith("Array_"):
            return None
        element_sort = self._get_element_sort_for_array(coll_sort)
        if element_sort is None:
            return None
        index_fn = self._get_index_fn(coll_sort, element_sort)
        return index_fn(coll, idx)

    def _get_element_sort_for_array(
        self, array_sort: z3.SortRef,
    ) -> z3.SortRef | None:
        """Reverse-lookup the element sort for an `Array_<elt>`
        uninterpreted sort.

        Three-tier lookup, in order of robustness:

        1. **`_array_element_sorts` direct map**: populated whenever
           `_get_array_sort` creates a new Array_<T> sort.  Works
           for every element type — primitive, ADT (incl. nested
           generic), and any future shape — because the
           association is recorded at creation time rather than
           reverse-engineered from the sort name string.

        2. **Primitive pattern match**: covers `Array_Int`,
           `Array_FPSort(11, 53)` (Float64), `Array_Bool`, `Array_String` for callers
           that obtain an array sort via a path that hasn't
           populated `_array_element_sorts` (defensive — every
           code path today populates it, but the fallback shields
           against future regressions).

        3. **`_z3_sorts` direct key lookup**: tries the raw
           stripped key (e.g. `MyAdt`) and the mangler-inverted
           key (e.g. `List_LInt_R` → `List<Int>`, since #884 routed
           ADT sort names through the injective `mangle_type_name`)
           as defensive last-ditch ADT-sort recovery.  Mostly
           redundant given (1) — every `Array_<T>` sort is
           created via `_get_array_sort` which populates
           `_array_element_sorts` at creation time — but kept as
           defence-in-depth against a future code path that
           bypasses `_get_array_sort`.
        """
        sort_name = str(array_sort)
        # 1. Direct map (populated at sort-creation time).
        mapped = self._array_element_sorts.get(sort_name)
        if mapped is not None:
            return mapped
        # 2. Primitive pattern match.
        if sort_name == "Array_Int":
            return z3.IntSort()
        if sort_name == f"Array_{_FLOAT64_SORT}":  # Array<Float64> (#797)
            return _FLOAT64_SORT
        if sort_name == "Array_Bool":
            return z3.BoolSort()
        if sort_name == "Array_String":
            return z3.StringSort()
        # 3. ADT-element fallback — recover the `_z3_sorts` key from the
        # mangled Array-element sort name.  `_z3_sorts` uses
        # `_adt_sort_key(name, type_args)` which produces `"List<Int>"`-style
        # keys with angle brackets, while the element sort's Z3 name is the
        # injective mangler output (`List<Int>` → `List_LInt_R`; #884 routed
        # ADT sort names through `mangle_type_name`).  Invert the mangler to
        # get the key back; a flat ADT name (no metacharacters) unmangles to
        # itself.  A stripped name that is not valid mangler output has no
        # ADT preimage — skip that candidate rather than guess.
        elt_key = sort_name[len("Array_"):]
        candidates = [elt_key]
        try:
            unmangled = unmangle_type_name(elt_key)
        except ValueError:
            unmangled = None
        if unmangled is not None and unmangled != elt_key:
            candidates.append(unmangled)
        for candidate in candidates:
            sort = self._z3_sorts.get(candidate)
            if sort is not None:
                return sort
        return None

    def _translate_array_lit(
        self, expr: ast.ArrayLit, env: SlotEnv,
    ) -> z3.ExprRef | None:
        """Translate `[a, b, c]` to a fresh Array constant with
        `length(lit) == N` and `index(lit, i) == translate(elem_i)`
        asserted to the solver for each position (#667).

        The literal's element type is inferred from the first
        successfully-translated element's sort; if the elements
        translate to inconsistent sorts (shouldn't happen post-
        typecheck, but defensive against future relaxations), the
        first sort wins and subsequent elements that don't match
        fail the translation.

        Returns None on empty arrays (no element sort available)
        or on element translation failure.
        """
        if not expr.elements:
            return None
        raw_elements = [self.translate_expr(e, env) for e in expr.elements]
        if any(e is None for e in raw_elements):
            return None
        # Narrowed: every element translated successfully.
        element_z3s: list[z3.ExprRef] = [e for e in raw_elements if e is not None]
        element_sort = element_z3s[0].sort()
        # Defensive sort-consistency check: the type checker should
        # have rejected heterogeneous-element array literals upstream,
        # but if we receive one (e.g. due to a future relaxation in
        # the checker), bail to None rather than letting Z3 raise an
        # uncaught `Z3Exception: sort mismatch` on the per-element
        # axiom below.  See pr-review-toolkit silent-failure-hunter
        # review on PR #670.
        if any(e.sort() != element_sort for e in element_z3s[1:]):
            return None
        array_sort = self._get_array_sort(element_sort)
        lit_name = self._fresh_name("array_lit")
        lit_const = z3.Const(lit_name, array_sort)
        self._vars[lit_name] = lit_const
        # Length axiom: `length(lit) == N`.
        length_fn = self._get_length_fn(array_sort)
        self.solver.add(length_fn(lit_const) == len(expr.elements))
        # Per-element axioms: `index(lit, i) == element_i`.
        index_fn = self._get_index_fn(array_sort, element_sort)
        for i, elt in enumerate(element_z3s):
            self.solver.add(index_fn(lit_const, z3.IntVal(i)) == elt)
        return lit_const

    def _translate_unary(
        self, expr: ast.UnaryExpr, env: SlotEnv
    ) -> z3.ExprRef | None:
        """Translate unary operators."""
        operand = self.translate_expr(expr.operand, env)
        if operand is None:
            return None

        if expr.op == ast.UnaryOp.NOT:
            return z3.Not(operand)
        if expr.op == ast.UnaryOp.NEG:
            return -operand
        return None  # pragma: no cover

    def _translate_if(
        self, expr: ast.IfExpr, env: SlotEnv
    ) -> z3.ExprRef | None:
        """Translate if-then-else to Z3 If.

        Tracks the branch condition in ``_path_conditions`` while
        translating each branch so that call-site precondition checks
        (via ``check_valid``) can see which branch is active.
        """
        cond = self.translate_expr(expr.condition, env)
        if cond is None:
            # Can't translate condition — no path condition available
            then = self.translate_expr(expr.then_branch, env)
            else_ = self.translate_expr(expr.else_branch, env)
            if then is None or else_ is None:  # pragma: no cover
                return None
            return None

        # Translate then-branch with cond as path condition
        self._path_conditions.append(cond)
        then = self.translate_expr(expr.then_branch, env)
        self._path_conditions.pop()

        # Translate else-branch with Not(cond) as path condition
        self._path_conditions.append(z3.Not(cond))
        else_ = self.translate_expr(expr.else_branch, env)
        self._path_conditions.pop()

        if then is None or else_ is None:
            return None
        return z3.If(cond, then, else_)

    def _is_user_fn(self, name: str) -> bool:
        """True if a user (or module) function of this name is registered.

        Mirrors codegen's ``expr.name not in self._fn_sigs`` gate on the
        ability-op rewrite (#874): a `where`-helper may legitimately shadow a
        built-in ability-op name, in which case the call is an ordinary
        user-function call, not the built-in `eq` / `compare`.
        """
        return self._fn_lookup is not None and self._fn_lookup(name) is not None

    @staticmethod
    def _desugar_compare(call: ast.FnCall) -> ast.Expr:
        """Desugar ``compare(a, b)`` to the canonical Ordering if-chain.

        Mirrors codegen's Pass 1.6 exactly (#874):
            if a < b then Less else if a == b then Equal else Greater
        so the verifier reasons over the SAME term the runtime produces.
        """
        left, right = call.args[0], call.args[1]
        return ast.IfExpr(
            condition=ast.BinaryExpr(
                left=left, op=ast.BinOp.LT, right=right, span=call.span,
            ),
            then_branch=ast.Block(
                statements=(), span=call.span,
                expr=ast.NullaryConstructor(name="Less", span=call.span),
            ),
            else_branch=ast.Block(
                statements=(), span=call.span,
                expr=ast.IfExpr(
                    condition=ast.BinaryExpr(
                        left=left, op=ast.BinOp.EQ, right=right,
                        span=call.span,
                    ),
                    then_branch=ast.Block(
                        statements=(), span=call.span,
                        expr=ast.NullaryConstructor(
                            name="Equal", span=call.span),
                    ),
                    else_branch=ast.Block(
                        statements=(), span=call.span,
                        expr=ast.NullaryConstructor(
                            name="Greater", span=call.span),
                    ),
                    span=call.span,
                ),
            ),
            span=call.span,
        )

    def _translate_call(
        self, call: ast.FnCall, env: SlotEnv
    ) -> z3.ExprRef | None:
        """Translate a function call via modular contract verification.

        For ``array_length()``, uses the built-in uninterpreted function.
        For user-defined functions, looks up the callee and delegates
        to ``_translate_call_with_info``.
        """
        # Built-in ability operations `eq` / `compare` (#874).  These are the
        # generic-programming spelling of `==` and the Ordering three-way
        # comparison (spec §9.8); a contract may use them directly
        # (`ensures(eq(@Int.result, 3))`).  They are semantically identical to
        # their operator form, so — one canonical form (#815) — desugar to the
        # SAME canonical AST node codegen's Pass 1.6 (`_rewrite_ability_ops`)
        # emits and re-translate, reusing this module's FP-correct `==` path
        # and the `Ordering` datatype encoding.  Without this the ability-op
        # `FnCall` matched no built-in, fell to the user-fn lookup (which has
        # no `eq` entry), returned None, and demoted the whole contract to
        # Tier 3 (E523) — a `vera check`-green postcondition never statically
        # proved.  Guard on absence from `_fn_sigs` so a user function that
        # legitimately shadows the name (permitted for `where`-helpers) is not
        # hijacked, mirroring codegen's `expr.name not in self._fn_sigs` gate.
        if (call.name == "eq" and len(call.args) == 2
                and not self._is_user_fn(call.name)):
            desugared: ast.Expr = ast.BinaryExpr(
                left=call.args[0], op=ast.BinOp.EQ, right=call.args[1],
                span=call.span,
            )
            return self.translate_expr(desugared, env)
        if (call.name == "compare" and len(call.args) == 2
                and not self._is_user_fn(call.name)):
            # The desugar produces `Ordering` nullary ctors (`Less` / `Equal`
            # / `Greater`).  When `compare` appears ONLY in a contract of a
            # function whose signature never mentions `Ordering`, that sort is
            # registered (`_adt_registry`) but never materialised in
            # `_z3_sorts` — nothing referenced the type — so the ctors would
            # translate to None and demote the predicate to Tier 3.  Force the
            # sort here, scoped to the desugar so general ADT-call modular
            # reasoning is untouched (a broad on-demand materialisation in
            # `_find_sort_for_ctor` regressed unrelated `ensures(true)`-return
            # ADT calls to false E500 — PR #887 review).
            if "Ordering" in self._adt_registry:
                self._get_or_create_adt_sort("Ordering", ())
            return self.translate_expr(
                self._desugar_compare(call), env)

        # Built-in: array_length()
        if call.name == "array_length" and len(call.args) == 1:
            arg = self.translate_expr(call.args[0], env)
            if arg is not None:
                length_fn = self._get_length_fn(arg.sort())
                result = length_fn(arg)
                self.solver.add(result >= 0)
                return result
            return None  # pragma: no cover

        # Built-in: map_size() — uninterpreted, result >= 0
        if call.name == "map_size" and len(call.args) == 1:
            arg = self.translate_expr(call.args[0], env)
            if arg is not None:
                size_fn = z3.Function(
                    "map_size", arg.sort(), z3.IntSort(),
                )
                result = size_fn(arg)
                self.solver.add(result >= 0)
                return result
            return None  # pragma: no cover

        # Built-in: map_contains() — returns Bool (uninterpreted)
        if call.name == "map_contains" and len(call.args) == 2:
            return None  # opaque to verifier

        # Built-in: set_size() — uninterpreted, result >= 0
        if call.name == "set_size" and len(call.args) == 1:
            arg = self.translate_expr(call.args[0], env)
            if arg is not None:
                size_fn = z3.Function(
                    "set_size", arg.sort(), z3.IntSort(),
                )
                result = size_fn(arg)
                self.solver.add(result >= 0)
                return result
            return None  # pragma: no cover

        # Built-in: set_contains() — returns Bool (uninterpreted)
        if call.name == "set_contains" and len(call.args) == 2:
            return None  # opaque to verifier

        # Built-in: abs()
        if call.name == "abs" and len(call.args) == 1:
            arg = self.translate_expr(call.args[0], env)
            if arg is not None:
                import z3 as z3mod
                return z3mod.If(arg >= 0, arg, -arg)
            return None  # pragma: no cover

        # Built-in: min()
        if call.name == "min" and len(call.args) == 2:
            a = self.translate_expr(call.args[0], env)
            b = self.translate_expr(call.args[1], env)
            if a is not None and b is not None:
                import z3 as z3mod
                return z3mod.If(a <= b, a, b)
            return None  # pragma: no cover

        # Built-in: max()
        if call.name == "max" and len(call.args) == 2:
            a = self.translate_expr(call.args[0], env)
            b = self.translate_expr(call.args[1], env)
            if a is not None and b is not None:
                import z3 as z3mod
                return z3mod.If(a >= b, a, b)
            return None  # pragma: no cover

        # Built-in: nat_to_int() — identity (both IntSort in Z3)
        if call.name == "nat_to_int" and len(call.args) == 1:
            return self.translate_expr(call.args[0], env)

        # Built-in: string_length() (#802).  Vera's runtime string_length counts
        # UTF-8 *bytes*, but Z3's Length over z3.String counts Unicode *code
        # points* — they disagree on every multibyte character (e.g. "é" is 1
        # code point but 2 bytes), so z3.Length proved false contracts at Tier 1.
        # A string LITERAL has a known exact byte length, so model it precisely;
        # for any non-literal argument no byte-length operator exists in Z3's
        # string theory, so defer to Tier 3 (return None), matching the
        # numeric-cast / quantifier / decimal precedent.
        if call.name == "string_length" and len(call.args) == 1:
            arg_node = call.args[0]
            if isinstance(arg_node, ast.StringLit):
                try:
                    byte_len = len(arg_node.value.encode("utf-8"))
                except UnicodeEncodeError:
                    # A lone surrogate (U+D800..U+DFFF) is not UTF-8-encodable;
                    # its byte length is undefined, so defer to Tier 3.
                    return None
                return z3.IntVal(byte_len)
            return None

        # Built-ins: string_contains / string_starts_with / string_ends_with
        # Z3's native string theory encodes these exactly.
        # string_contains(haystack, needle) → Contains(haystack, needle)
        # string_starts_with(s, prefix)     → PrefixOf(prefix, s)
        # string_ends_with(s, suffix)       → SuffixOf(suffix, s)
        if call.name == "string_contains" and len(call.args) == 2:
            haystack = self.translate_expr(call.args[0], env)
            needle = self.translate_expr(call.args[1], env)
            if haystack is not None and needle is not None:
                return z3.Contains(haystack, needle)
            return None  # pragma: no cover

        if call.name == "string_starts_with" and len(call.args) == 2:
            s = self.translate_expr(call.args[0], env)
            prefix = self.translate_expr(call.args[1], env)
            if s is not None and prefix is not None:
                return z3.PrefixOf(prefix, s)
            return None  # pragma: no cover

        if call.name == "string_ends_with" and len(call.args) == 2:
            s = self.translate_expr(call.args[0], env)
            suffix = self.translate_expr(call.args[1], env)
            if s is not None and suffix is not None:
                return z3.SuffixOf(suffix, s)
            return None  # pragma: no cover

        # Built-ins: float_is_nan / float_is_infinite — soundly modelled now that
        # Float64 is a FloatingPoint sort (#797), via fpIsNaN / fpIsInf.  (Pre-
        # #797, Float64 was Z3 Real, which has no NaN/Inf, so returning a Boolean
        # would have been unsound and these were deferred to Tier 3.)
        if call.name == "float_is_nan" and len(call.args) == 1:
            x = self.translate_expr(call.args[0], env)
            # Guard on FPRef, not just non-None: z3.fpIsNaN raises on a non-FP
            # term, which would bypass the Tier-3 fallback.  The checker types
            # the arg as @Float64 (so a non-FP term is currently unreachable),
            # but this mirrors the FP-vs-non-FP guard in _translate_binary so
            # any non-FP term degrades to Tier 3 rather than crashing.
            return z3.fpIsNaN(x) if isinstance(x, z3.FPRef) else None
        if call.name == "float_is_infinite" and len(call.args) == 1:
            x = self.translate_expr(call.args[0], env)
            return z3.fpIsInf(x) if isinstance(x, z3.FPRef) else None

        # Built-ins: nan() / infinity() — Float64 special-value constants, now
        # representable as FP literals (#797).  Uninterpreted under the old Real
        # model, so any contract reasoning over them dropped to Tier 3; with the
        # FP sort `float_is_nan(nan())` etc. discharge at Tier 1.
        if call.name == "nan" and len(call.args) == 0:
            return z3.fpNaN(_FLOAT64_SORT)
        if call.name == "infinity" and len(call.args) == 0:
            return z3.fpPlusInfinity(_FLOAT64_SORT)

        # Built-in: float_clamp(v, lo, hi) → f64.min(f64.max(v, lo), hi) (#807).
        # Pure Float64, so modeled unconditionally — Z3 reasons reliably over the
        # FP sort here (unlike the Int↔Float conversions below).  Must mirror the
        # codegen ORDER exactly: max-then-min, so that lo > hi clamps to hi (the
        # reverse, min-then-max, would clamp to lo).  Uses the faithful WASM
        # min/max helpers, NOT z3.fpMin/fpMax which diverge on NaN/±0.
        if call.name == "float_clamp" and len(call.args) == 3:
            v = self.translate_expr(call.args[0], env)
            lo = self.translate_expr(call.args[1], env)
            hi = self.translate_expr(call.args[2], env)
            if (isinstance(v, z3.FPRef)
                    and isinstance(lo, z3.FPRef)
                    and isinstance(hi, z3.FPRef)):
                return _wasm_fp_min(_wasm_fp_max(v, lo), hi)
            return None

        # Built-in: int_to_float(n) → f64.convert_i64_s (#807).  Modeled as
        # fpToFP(RNE, ToReal(n)) — round-nearest-ties-to-even, matching the
        # runtime conversion — but ONLY for a CONCRETE (constant-foldable)
        # argument.  Z3's symbolic Int↔Real↔FP reasoning is unreliable: it
        # returns spurious `sat` counterexamples that don't satisfy their own
        # constraints (non-deterministically across timeouts), so a symbolic
        # argument defers to a sound Tier 3 rather than risk a false
        # discharge/refutation.  (int_to_float is total — no trap — so no
        # obligation is needed; out-of-i64 n cannot occur at runtime, and the
        # over-approximation is sound for the concrete case we model.)
        if call.name == "int_to_float" and len(call.args) == 1:
            n = self.translate_expr(call.args[0], env)
            if not isinstance(n, z3.ArithRef) or n.sort() != z3.IntSort():
                return None
            ns = z3.simplify(n)
            if not z3.is_int_value(ns):
                return None  # symbolic → Tier 3
            return z3.simplify(
                z3.fpToFP(z3.RNE(), z3.ToReal(ns), _FLOAT64_SORT)
            )

        # Built-in: float_to_int(x) → i64.trunc_f64_s (#807).  Partial: traps on
        # NaN / ±Inf / out-of-i64-range, so the verifier ALSO emits a domain
        # obligation (E529) at each site.  Here we model only the VALUE, and only
        # for a CONCRETE, finite, in-range argument — computed exactly as the
        # truncated-toward-zero integer (Python int() on the exact rational of
        # the FP literal).  A symbolic argument (Z3's FP↔Real reasoning is
        # unreliable — see int_to_float above) or a NaN/Inf/out-of-range literal
        # (no integer value; the obligation flags it, the runtime traps) returns
        # None → Tier 3.
        if call.name == "float_to_int" and len(call.args) == 1:
            x = self.translate_expr(call.args[0], env)
            if not isinstance(x, z3.FPRef):
                return None
            xs = z3.simplify(x)
            if not z3.is_fp_value(xs):
                return None  # symbolic → Tier 3
            if (z3.is_true(z3.simplify(z3.fpIsNaN(xs)))
                    or z3.is_true(z3.simplify(z3.fpIsInf(xs)))):
                return None  # no integer value; obligation flags, runtime traps
            real = z3.simplify(z3.fpToReal(xs))
            if not z3.is_rational_value(real):
                return None  # pragma: no cover — finite FP → rational
            truncated = int(real.as_fraction())  # toward zero
            if not (_I64_MIN <= truncated <= _I64_MAX):
                return None  # out of range; obligation flags, runtime traps
            return z3.IntVal(truncated)

        # Built-in: byte_to_int() — identity (both IntSort in Z3)
        if call.name == "byte_to_int" and len(call.args) == 1:
            return self.translate_expr(call.args[0], env)

        # No function lookup → can't do modular verification
        if self._fn_lookup is None:
            return None

        callee_info = self._fn_lookup(call.name)
        if callee_info is None:
            return None

        return self._translate_call_with_info(
            callee_info, call.name, call.args, call, env,
        )

    def _translate_module_call(
        self, call: ast.ModuleCall, env: SlotEnv
    ) -> z3.ExprRef | None:
        """Translate a module-qualified call (C7d).

        Looks up the callee via the module function lookup callback,
        then delegates to the shared contract verification logic.
        """
        if self._module_fn_lookup is None:
            return None

        callee_info = self._module_fn_lookup(
            tuple(call.path), call.name,
        )
        if callee_info is None:
            return None

        return self._translate_call_with_info(
            callee_info, call.name, call.args, call, env,
        )

    def _translate_call_args(
        self, args: tuple[ast.Expr, ...], env: SlotEnv,
    ) -> list[z3.ExprRef] | None:
        """Translate every actual argument in the caller's env (#882 helper).

        Returns the Z3 argument list, or None if any argument uses a construct
        outside the decidable fragment.  Factored out so the call translator
        can attempt argument translation twice: once as-is (pre-#882
        behaviour) and once after forcing the callee's ADT sorts.
        """
        z3_args: list[z3.ExprRef] = []
        for arg_expr in args:
            z3_arg = self.translate_expr(arg_expr, env)
            if z3_arg is None:
                return None
            z3_args.append(z3_arg)
        return z3_args

    def _build_callee_env(
        self,
        callee_info: Any,
        z3_args: list[z3.ExprRef],
    ) -> SlotEnv | None:
        """Build the callee's SlotEnv by pushing each parameter's Z3 argument
        in declaration order (#882 helper).

        Returns None if a parameter type expression has no slot name (a shape
        the checker rules out; guarded for safety).
        """
        callee_env = SlotEnv()
        for param_te, z3_arg in zip(callee_info.param_type_exprs, z3_args):
            slot_name = self._type_expr_to_slot_name(param_te)
            if slot_name is None:  # pragma: no cover
                return None
            callee_env = callee_env.push(slot_name, z3_arg)
        return callee_env

    def _check_call_preconditions(
        self,
        callee_info: Any,
        callee_name: str,
        z3_args: list[z3.ExprRef],
        call_node: ast.FnCall | ast.ModuleCall,
    ) -> bool:
        """Check each of the callee's preconditions at this call site.

        Returns True when every non-trivial precondition is discharged (or the
        callee has none), False when one is violated (E501 recorded) or cannot
        be translated (E532 demotion recorded).  Shared by the modelled-return
        path and the #882 opaque-return path so both check the obligation with
        identical dedup semantics.
        """
        callee_env = self._build_callee_env(callee_info, z3_args)
        if callee_env is None:  # pragma: no cover
            return False

        for contract in callee_info.contracts:
            if not isinstance(contract, ast.Requires):
                continue
            # Skip trivial requires(true)
            if isinstance(contract.expr, ast.BoolLit) and contract.expr.value:
                continue
            z3_pre = self.translate_expr(contract.expr, callee_env)
            if z3_pre is None:
                # The precondition itself uses a construct outside the
                # decidable fragment.  Demote loudly to Tier-3 rather than
                # silently dropping the obligation (#882): the arguments
                # translated, so this is a real call-pre obligation we simply
                # can't discharge statically.
                self._record_call_demotion_for(
                    callee_name, call_node, contract,
                )
                return False
            # Check validity: solver state already has caller's assumptions
            result = self.check_valid(z3_pre, [])
            if result.status != "verified":
                # The same call site is translated more than once per
                # function (the @Nat-subtraction walker re-translates
                # let RHSes, branch conditions, and subtraction
                # operands to rebuild its state) — and for some sites,
                # e.g. inside an ExprStmt, the walker is the ONLY
                # translator.  Dedup keeps exactly one violation per
                # (call site, precondition) regardless of how many
                # passes visit it (#727).  The site is keyed by SPAN,
                # not node identity: pipe translation desugars to a
                # fresh synthetic FnCall on every pass, so the node
                # object differs while the span (copied from the pipe
                # expression) is stable.  Spanless nodes fall back to
                # object identity rather than colliding on None.
                already = any(
                    v.precondition is contract
                    and (
                        v.call_node.span == call_node.span
                        if (
                            v.call_node.span is not None
                            and call_node.span is not None
                        )
                        else v.call_node is call_node
                    )
                    for v in self._call_violations
                )
                if not already:
                    self._call_violations.append(CallViolation(
                        callee_name=callee_name,
                        call_node=call_node,
                        precondition=contract,
                        counterexample=result.counterexample,
                    ))
                return False
        return True

    def _translate_call_with_info(
        self,
        callee_info: Any,
        callee_name: str,
        args: tuple[ast.Expr, ...],
        call_node: ast.FnCall | ast.ModuleCall,
        env: SlotEnv,
    ) -> z3.ExprRef | None:
        """Core modular verification: check preconditions, assume postconditions.

          1. Check callee is non-generic with matching arity
          2. Translate actual arguments in the caller's env
          3. Check each callee precondition holds (solver has caller assumptions)
          4. Create a fresh return variable
          5. Assume callee postconditions about the return variable
          6. Return the fresh variable
        """
        # Generic functions can't be translated to Z3
        if callee_info.forall_vars:
            return None

        # Must have matching arity
        if len(args) != len(callee_info.param_type_exprs):
            return None

        # Does the callee carry a real (non-trivial) precondition?  A callee
        # with only `requires(true)` has no obligation to demote — a failed
        # arg translation there is correctly silent (#882).
        has_nontrivial_pre = any(
            isinstance(c, ast.Requires)
            and not (isinstance(c.expr, ast.BoolLit) and c.expr.value)
            for c in callee_info.contracts
        )

        # Translate actual arguments in the caller's env.  First WITHOUT
        # forcing any ADT sort — this is the exact pre-#882 attempt.  When it
        # succeeds the call is modelled as before (return value assumed from
        # the callee's ensures below), so no existing behaviour changes.
        z3_args = self._translate_call_args(args, env)

        # #882: a constructor-call argument (`MkP(1)`) only translates once the
        # callee's concrete ADT sort exists.  In a caller context that never
        # declared that ADT the sort is absent, so the pre-#882 attempt bails
        # and the call-site precondition obligation silently vanishes.  Force
        # the sorts from the callee's declared parameter types and retry — but
        # ONLY to CHECK the precondition, not to newly model the return value.
        if z3_args is None:
            self._ensure_call_arg_sorts(callee_info.param_type_exprs)
            forced_args = self._translate_call_args(args, env)
            if forced_args is not None:
                # Arguments now translate.  Check the call-site precondition
                # against them (records E501 / discharges), then return None so
                # the return value stays opaque exactly as pre-#882 — the
                # caller reasoned about this helper's result only through its
                # ensures before, and still does; the *only* new behaviour is
                # the precondition obligation.
                self._check_call_preconditions(
                    callee_info, callee_name, forced_args, call_node,
                )
                return None
            # Still untranslatable (a host-handle field like `Map`).  A real
            # precondition must demote LOUDLY to Tier-3 (#882); a trivial
            # `requires(true)` has no obligation and stays silent.
            if has_nontrivial_pre:
                self._record_call_demotion(callee_info, callee_name, call_node)
            return None

        # Check the callee's preconditions against the translated arguments.
        # On any failure (violation or demotion recorded) the call result is
        # opaque — return None so the enclosing postcondition demotes to
        # Tier-3, unchanged from before this refactor.
        if not self._check_call_preconditions(
            callee_info, callee_name, z3_args, call_node,
        ):
            return None

        # Rebuild the callee env for the ensures-assumption step below (the
        # postcondition may reference the callee's own parameters).
        callee_env = self._build_callee_env(callee_info, z3_args)
        if callee_env is None:  # pragma: no cover
            return None

        # Create fresh return variable
        from vera.types import RefinedType
        ret_type = callee_info.return_type
        base_ret = ret_type.base if isinstance(ret_type, RefinedType) else ret_type
        fresh = self._fresh_name(callee_name)
        # Mirror the parameter-declaration dispatch in
        # `vera/verifier.py::_verify_decl`: each Vera type gets a
        # typed Z3 variable.  Pre-#667 follow-up this branch only
        # handled NAT / BOOL / AdtType, falling back to
        # `declare_int` for String / Float64 / Array — so callers
        # couldn't reason about helper return values of those
        # types in postconditions.
        if base_ret == NAT:
            ret_var = self.declare_nat(fresh)
        elif base_ret == BOOL:
            ret_var = self.declare_bool(fresh)
        elif base_ret == STRING:
            ret_var = self.declare_string(fresh)
        elif base_ret == FLOAT64:
            ret_var = self.declare_float64(fresh)
        elif isinstance(base_ret, AdtType) and base_ret.name == "Array":
            # Array<T> return type — declare with a proper Array
            # sort so `result[i]` predicates on the call site can
            # reason about the result via `index_<T>`.
            element_sort: z3.SortRef | None = None
            if base_ret.type_args:
                element_sort = self._vera_type_to_z3_sort(base_ret.type_args[0])
            if element_sort is None:
                # Element type not representable in Z3 (e.g.
                # `Array<FnType<...>>`).  Signal Tier 3 cleanly
                # rather than silently type-erasing to Int — that
                # would let the caller's postcondition translate
                # against a wrong-typed result variable.  Pr-
                # review-toolkit follow-up on #670 flagged this
                # as the same silent-failure pattern #667 was
                # written to close.
                return None
            ret_var = self.declare_array_var(fresh, element_sort)
        elif isinstance(base_ret, AdtType):
            adt_var = self.declare_adt(fresh, base_ret)
            ret_var = adt_var if adt_var is not None else self.declare_int(fresh)
        else:
            ret_var = self.declare_int(fresh)

        # Assume callee postconditions about the return variable
        saved_result = self._result_var
        self._result_var = ret_var
        for contract in callee_info.contracts:
            if not isinstance(contract, ast.Ensures):
                continue
            if isinstance(contract.expr, ast.BoolLit) and contract.expr.value:
                continue
            z3_post = self.translate_expr(contract.expr, callee_env)
            if z3_post is not None:
                self.solver.add(z3_post)
        self._result_var = saved_result

        # #746: a refined return type is an implicit postcondition — assume
        # its predicate on the fresh call result so a caller can rely on a
        # verified refined return (the producing function discharges the
        # predicate at its return position).  Only the 5 statically-modelled
        # primitive bases (Int/Nat/Bool/Float64/String) have a substitutable
        # binder *and* a runtime-guarded producer; an unmodelled base such as
        # `@Byte` or `@Unit` must NOT let the caller assume the predicate (for
        # `@Unit` it isn't even runtime-guarded, so assuming e.g.
        # `always_false(@Unit.0)` would add `false` → UNSAT → vacuously
        # discharge the caller's own obligations).  The base-`@Nat` `>= 0` is
        # already carried by the `declare_nat` above, so the predicate alone
        # suffices here.
        if isinstance(ret_type, RefinedType) and ret_type.base in (
            INT,
            NAT,
            BOOL,
            FLOAT64,
            STRING,
        ):
            # Push the value under the predicate's ACTUAL binder name (alias-
            # aware: `@Age.0` for `type Age = Nat; { @Age | @Age.0 >= 18 }`),
            # not the resolved base name — otherwise the predicate's `@Age.0`
            # won't resolve against `Nat` and `z3_pred` is None, silently
            # dropping the refined-return fact so a caller can't rely on it (CR
            # PR-review — the SMT analogue of the verifier/codegen binder fix).
            binder = (ast.predicate_binder_name(ret_type.predicate)
                      or ret_type.base.name)
            inner_env = SlotEnv().push(binder, ret_var)
            z3_pred = self.translate_expr(ret_type.predicate, inner_env)
            if z3_pred is not None:
                self.solver.add(z3_pred)

        return ret_var

    def _translate_block(
        self, block: ast.Block, env: SlotEnv
    ) -> z3.ExprRef | None:
        """Translate a block expression: process statements then final expr."""
        current_env = env
        # #804: a bare assert/assume makes its predicate hold for LATER
        # statements, so a subsequent call's precondition — checked here during
        # translation (#730), one phase before the obligation walks — sees it.
        # Facts are pushed onto `_path_conditions` AFTER the statement
        # (forward-only) and dropped at block exit by the finally (branch-local);
        # `check_valid` folds `_path_conditions` into each call-precondition
        # check.  The finally also covers the early `return None` paths, so an
        # untranslatable statement after an assert never leaks the fact into the
        # post-translation walks.
        pc_depth = len(self._path_conditions)
        try:
            for stmt in block.statements:
                if isinstance(stmt, ast.LetStmt):
                    val = self.translate_expr(stmt.value, current_env)
                    if val is None:
                        return None
                    # Extract slot type name from the let binding
                    type_name = self._type_expr_to_slot_name(stmt.type_expr)
                    if type_name is None:  # pragma: no cover
                        return None
                    current_env = current_env.push(type_name, val)
                elif isinstance(stmt, ast.ExprStmt):
                    # #730: translate a statement-position expression for its side
                    # effect of checking call preconditions (E501) — a call whose
                    # result is discarded must still be checked against its
                    # requires(...).  The value is dropped: a statement
                    # contributes nothing to the block result and `current_env`
                    # is unchanged (an ExprStmt binds no slot).  An untranslatable
                    # statement (effect op, quantifier, anon fn) returns None,
                    # which we IGNORE — it must NOT abort the block's Tier-1
                    # verification of the surrounding decidable obligations.  The
                    # #727 dedup (keyed on the precondition's identity + the
                    # call's SPAN — not node identity) makes re-translation
                    # duplicate-free.
                    self.translate_expr(stmt.expr, current_env)
                    # #804: thread the assert/assume fact forward (see above).
                    if isinstance(stmt.expr, (ast.AssertExpr, ast.AssumeExpr)):
                        fact = self.translate_expr(stmt.expr.expr, current_env)
                        if fact is not None:
                            self._path_conditions.append(fact)
                else:
                    # LetDestruct or unknown statement type
                    return None  # pragma: no cover
            return self.translate_expr(block.expr, current_env)
        finally:
            del self._path_conditions[pc_depth:]

    # -----------------------------------------------------------------
    # Match and constructor translation
    # -----------------------------------------------------------------

    def _arm_source_facts(
        self, scrutinee_ast: ast.Expr, scrutinee_z3: z3.ExprRef,
        pattern: ast.Pattern,
    ) -> list[z3.ExprRef]:
        """Source-type facts to assume while translating *pattern*'s arm body —
        via the verifier-injected ``_subpattern_fact_hook`` — so a call
        precondition inside the arm sees a refined sub-pattern binding's
        invariant (CR PR-review).  Empty when no hook is set (pure-SMT tests)
        or the pattern is not a constructor pattern."""
        if (self._subpattern_fact_hook is None
                or not isinstance(pattern, ast.ConstructorPattern)):
            return []
        facts = self._subpattern_fact_hook(
            scrutinee_ast, scrutinee_z3, pattern, self)
        return list(facts) if facts else []

    def _translate_match(
        self, expr: ast.MatchExpr, env: SlotEnv
    ) -> z3.ExprRef | None:
        """Translate a match expression to a Z3 If-chain.

        Tracks pattern conditions in ``_path_conditions`` while
        translating each arm's body so that call-site precondition
        checks can see which arm is active.
        """
        scrutinee = self.translate_expr(expr.scrutinee, env)
        if scrutinee is None:
            return None

        # Build reverse If-chain: last arm is the default
        arms = list(expr.arms)
        if not arms:  # pragma: no cover
            return None

        # Collect preceding arm conditions for the default case
        preceding_conds: list[z3.ExprRef] = []
        for arm in arms[:-1]:
            pc = self._pattern_condition(scrutinee, arm.pattern)
            if pc is not None:
                preceding_conds.append(pc)

        # Translate last arm body (default case)
        last_env = self._bind_pattern(scrutinee, arms[-1].pattern, env)
        if last_env is None:
            return None

        # Default arm: none of the preceding patterns matched
        for pc in preceding_conds:
            self._path_conditions.append(z3.Not(pc))
        last_facts = self._arm_source_facts(
            expr.scrutinee, scrutinee, arms[-1].pattern)
        for f in last_facts:
            self._path_conditions.append(f)
            # Global implication: the fact holds whenever THIS (default) arm is
            # taken — i.e. no preceding pattern matched — so the refined-RETURN
            # goal (checked after this match translates, once path conditions
            # have popped) can use `arm-taken => fact`, not only the in-arm
            # precondition checks that read `_path_conditions` live (CR
            # PR-review).  Empty preceding ⇒ irrefutable arm ⇒ unconditional.
            if preceding_conds:
                self.solver.add(z3.Implies(
                    z3.And(*[z3.Not(pc) for pc in preceding_conds]), f))
            else:
                self.solver.add(f)
        result = self.translate_expr(arms[-1].body, last_env)
        for _ in last_facts:
            self._path_conditions.pop()
        for _ in preceding_conds:
            self._path_conditions.pop()

        if result is None:
            return None

        # Wrap preceding arms in z3.If(condition, body, previous)
        for arm in reversed(arms[:-1]):
            cond = self._pattern_condition(scrutinee, arm.pattern)
            if cond is None:  # pragma: no cover
                return None
            arm_env = self._bind_pattern(scrutinee, arm.pattern, env)
            if arm_env is None:  # pragma: no cover
                return None

            self._path_conditions.append(cond)
            arm_facts = self._arm_source_facts(
                expr.scrutinee, scrutinee, arm.pattern)
            for f in arm_facts:
                # Global implication `arm-matched => fact` (see the default-arm
                # note) so the refined-return goal sees it after the path
                # conditions pop, while the live `_path_conditions` push covers
                # in-arm precondition checks.
                self.solver.add(z3.Implies(cond, f))
                self._path_conditions.append(f)
            arm_body = self.translate_expr(arm.body, arm_env)
            for _ in arm_facts:
                self._path_conditions.pop()
            self._path_conditions.pop()

            if arm_body is None:  # pragma: no cover
                return None
            result = z3.If(cond, arm_body, result)

        return result

    def _find_ctor_index(
        self, sort: z3.SortRef, ctor_name: str,
    ) -> int | None:
        """Find the index of a constructor by name in a Z3 ADT sort."""
        if not isinstance(sort, z3.DatatypeSortRef):
            return None
        for i in range(sort.num_constructors()):
            if sort.constructor(i).name() == ctor_name:
                return i
        return None  # pragma: no cover

    def _pattern_condition(
        self, scrutinee: z3.ExprRef, pattern: ast.Pattern
    ) -> z3.ExprRef | None:
        """Return a Z3 Boolean for when *pattern* matches *scrutinee*."""
        if isinstance(pattern, ast.NullaryPattern):
            sort = scrutinee.sort()
            idx = self._find_ctor_index(sort, pattern.name)
            if idx is None:  # pragma: no cover
                return None
            return sort.recognizer(idx)(scrutinee)

        if isinstance(pattern, ast.ConstructorPattern):
            sort = scrutinee.sort()
            idx = self._find_ctor_index(sort, pattern.name)
            if idx is None:  # pragma: no cover
                return None
            return sort.recognizer(idx)(scrutinee)

        if isinstance(pattern, ast.WildcardPattern):  # pragma: no cover
            return z3.BoolVal(True)

        if isinstance(pattern, ast.BindingPattern):
            return z3.BoolVal(True)

        if isinstance(pattern, ast.IntPattern):
            return scrutinee == z3.IntVal(pattern.value)

        if isinstance(pattern, ast.BoolPattern):
            return scrutinee == z3.BoolVal(pattern.value)

        return None  # pragma: no cover

    def _bind_pattern(
        self,
        scrutinee: z3.ExprRef,
        pattern: ast.Pattern,
        env: SlotEnv,
    ) -> SlotEnv | None:
        """Extend *env* with bindings introduced by *pattern*."""
        if isinstance(pattern, (
            ast.NullaryPattern, ast.WildcardPattern,
            ast.IntPattern, ast.BoolPattern, ast.StringPattern,
        )):
            return env

        if isinstance(pattern, ast.BindingPattern):
            slot_name = self._type_expr_to_slot_name(pattern.type_expr)
            if slot_name is None:  # pragma: no cover
                return None
            return env.push(slot_name, scrutinee)

        if isinstance(pattern, ast.ConstructorPattern):
            sort = scrutinee.sort()
            idx = self._find_ctor_index(sort, pattern.name)
            if idx is None:  # pragma: no cover
                return None
            cur = env
            for i, sub_pat in enumerate(pattern.sub_patterns):
                accessor = sort.accessor(idx, i)
                field_val = accessor(scrutinee)
                bound = self._bind_pattern(field_val, sub_pat, cur)
                if bound is None:  # pragma: no cover
                    return None
                cur = bound
            return cur

        return None  # pragma: no cover

    def _find_sort_for_ctor(
        self, ctor_name: str, type_args: tuple[Type, ...] | None = None,
    ) -> z3.SortRef | None:
        """Find the Z3 sort for the ADT owning constructor *ctor_name*.

        When *type_args* pins the full instantiation (e.g. the caller has
        determined the outer ``Some`` in ``Some(Some(x))`` is
        ``Option<Option<Int>>`` — #918), materialise/select **that** sort by
        its exact ``_adt_sort_key``, not merely the first cached sort whose
        base name matches.  Two instantiations of the same generic
        (``Option<Int>`` and ``Option<Option<Int>>``) share a base name, so
        the old base-name-only scan returned whichever was cached first — a
        wrongly-sorted ``DatatypeRef`` that crashed Z3 (``Sort mismatch`` /
        ``'DatatypeSortRef' object has no attribute 'is_int'``) on same-ADT
        self-nesting.

        *type_args* ``None`` (nullary tags, or when the instantiation can't be
        determined) keeps the base-name scan — sound for the non-nested case
        where only one instantiation of the base ADT is ever cached.

        Pinning is applied ONLY when the owning ADT already has at least one
        cached instantiation — i.e. the base-name scan would already have found
        *a* sort and translation was going to succeed regardless.  This keeps
        the change strictly a *disambiguation among existing instantiations*
        and never *newly enables* a ctor that the old scan left untranslatable:
        a top-level ``Some(42)`` argument in a caller whose context never
        materialised ``Option`` must still return None (opaque, demoted at the
        call site — #882), exactly as before.  On-demand materialising it here
        would flip such a call from opaque-demote to a fresh unconstrained
        return value, regressing an unrelated ``ensures(true)``-returning ADT
        call to a false E500 (the trap the #887 review flagged for a broad
        materialisation in this method).

        The pinned instantiation is resolved by :func:`_resolve_pinned_sort`,
        which handles the ``Int``/``Nat`` carrier ambiguity: ``@Nat.0``
        translates to a Z3 ``IntSort`` value, so a ``Some(@Nat.0)`` argument
        recovers as ``Int`` and the pinned key is ``Option<Int>`` even when the
        surrounding context only materialised ``Option<Nat>`` (post-#884 these
        are DISTINCT injective Z3 datatype sorts).  Building the ``Option<Int>``
        key would then hand back a sort that never appears in the context, and
        comparing it against the context's ``Option<Nat>`` value crashes
        ``_datatype_value_eq`` with ``sort mismatch``.  So a cached
        instantiation equal to the pin **modulo ``Nat``<->``Int``** is preferred
        over freshly building the pinned key.  A pin with NO Int/Nat-equal
        cached match (a genuinely new instantiation, e.g. the
        ``Option<Option<Int>>`` a nested ctor literal needs when only
        ``Option<Int>`` is cached) is still materialised — that path is the
        #918 fix and must keep working.
        """
        adt_name = self._ctor_to_adt.get(ctor_name)
        if adt_name is None:
            return None
        if type_args is not None and self._has_cached_instantiation(adt_name):
            # Disambiguate among instantiations: prefer an already-cached one
            # equal modulo Int/Nat, else materialise the pinned key exactly.
            sort = self._resolve_pinned_sort(adt_name, type_args)
            if sort is not None and (
                self._find_ctor_index(sort, ctor_name) is not None
            ):
                return sort
            return None
        for key, sort in self._z3_sorts.items():
            base = key.split("<")[0] if "<" in key else key
            if base == adt_name:
                if self._find_ctor_index(sort, ctor_name) is not None:
                    return sort
        return None

    def _resolve_pinned_sort(
        self, adt_name: str, type_args: tuple[Type, ...],
    ) -> z3.SortRef | None:
        """Resolve the Z3 sort for a pinned ADT instantiation (#918).

        Precedence:

        1. the exact ``_adt_sort_key`` if already cached;
        2. any cached instantiation equal to the pin **modulo ``Nat``<->``Int``**
           — the carrier ambiguity (``@Nat.0`` reads back as ``Int``) means the
           pin can name ``Option<Int>`` where the context built ``Option<Nat>``;
           post-#884 those are distinct injective sorts, so selecting the cached
           one avoids handing back a sort the surrounding equality can't compare
           against (a ``sort mismatch`` crash);
        3. otherwise materialise the pinned key via ``_get_or_create_adt_sort``
           — a genuinely new instantiation the context has not built yet (e.g.
           the ``Option<Option<Int>>`` a nested ctor literal needs when only
           ``Option<Int>`` is cached), which is exactly the #918 nesting fix.

        Note the asymmetry: step 3 is only reached when NO Int/Nat-equal
        instantiation is cached, so it never rebuilds an ``Int`` twin of an
        existing ``Nat`` sort.
        """
        key = _adt_sort_key(adt_name, type_args)
        exact = self._z3_sorts.get(key)
        if exact is not None:
            return exact
        norm = _normalize_int_nat_sort_key(key)
        for cached_key, sort in self._z3_sorts.items():
            if _normalize_int_nat_sort_key(cached_key) == norm:
                return sort
        return self._get_or_create_adt_sort(adt_name, type_args)

    def _has_cached_instantiation(self, adt_name: str) -> bool:
        """Whether any instantiation of *adt_name* is already in ``_z3_sorts``
        (#918) — gates same-ADT ctor-sort disambiguation to the case where the
        base-name scan would already have succeeded, so pinning never newly
        enables an otherwise-untranslatable ctor (see ``_find_sort_for_ctor``).
        """
        for key in self._z3_sorts:
            base = key.split("<")[0] if "<" in key else key
            if base == adt_name:
                return True
        return False

    def _z3_sort_to_vera_type(self, sort: z3.SortRef) -> Type | None:
        """Recover a Vera :class:`Type` from a translated Z3 sort (#918).

        Used to reconstruct the *outer* instantiation of a nested same-ADT
        constructor bottom-up: once a constructor's arguments are translated,
        each argument's Z3 sort names the concrete Vera type of that field, so
        unifying those against the constructor's declared (``TypeVar``-bearing)
        field types pins the enclosing generic's type parameters.

        Primitives map by sort identity.  ``Int`` and ``Nat`` are BOTH
        recovered as ``Int`` here because they share a Z3 carrier sort
        (``IntSort``) — a bare ``IntSort`` value carries no witness of the
        ``>= 0`` refinement, so ``Nat`` is indistinguishable from ``Int`` at
        this point.  Crucially this recovery is NOT lossless for the *enclosing*
        instantiation: post-#884 the datatype-sort mangling is injective, so
        ``Option<Nat>`` (``Option_LNat_R``) and ``Option<Int>``
        (``Option_LInt_R``) are DISTINCT Z3 datatype sorts.  A ``Some(@Nat.0)``
        argument therefore pins the ``Int``-keyed instantiation even in an
        ``Option<Nat>`` context — the recovered type DOES affect which sort is
        selected downstream.  ``_find_sort_for_ctor`` compensates by selecting
        only among *already-cached* instantiations modulo ``Nat``<->``Int``
        (via :func:`_normalize_int_nat_sort_key`), never materialising a fresh
        ``Int``-keyed sort that would sort-mismatch the context's ``Nat`` one.

        A datatype sort is reverse-looked-up in ``_z3_sorts`` by sort identity
        and its canonical key parsed back into an :class:`AdtType`.  ``None``
        when the sort is one we can't name (an uninterpreted ``Array_<T>``, a
        sort absent from the cache) — the caller then falls back to the
        base-name scan.
        """
        if sort.eq(z3.IntSort()):
            return INT
        if sort.eq(z3.BoolSort()):
            return BOOL
        if sort.eq(z3.StringSort()):
            return STRING
        if sort.eq(_FLOAT64_SORT):
            return FLOAT64
        if isinstance(sort, z3.DatatypeSortRef):
            for key, cached in self._z3_sorts.items():
                if cached.eq(sort):
                    return self._parse_adt_sort_key(key)
        return None

    @staticmethod
    def _parse_adt_sort_key(key: str) -> Type | None:
        """Parse a canonical ``_adt_sort_key`` string back to a :class:`Type`
        (#918) — the inverse of :func:`_adt_sort_key`.

        Grammar mirrors the generator exactly: ``Name`` (primitive or nullary
        ADT) or ``Name<arg, arg, ...>`` where each *arg* is itself a key.
        A bare name that is a primitive resolves to that ``PrimitiveType``;
        otherwise it is a nullary ``AdtType``.  Returns ``None`` on a malformed
        key or one containing the ``?`` placeholder that ``_adt_sort_key``
        emits for an un-nameable type argument.
        """
        key = key.strip()
        if not key or "?" in key:
            return None
        lt = key.find("<")
        if lt == -1:
            prim = PRIMITIVES.get(key)
            if prim is not None:
                return prim
            return AdtType(key, ())
        if not key.endswith(">"):
            return None
        name = key[:lt].strip()
        inner = key[lt + 1:-1]
        args: list[Type] = []
        depth = 0
        start = 0
        for i, ch in enumerate(inner):
            if ch == "<":
                depth += 1
            elif ch == ">":
                depth -= 1
            elif ch == "," and depth == 0:
                arg = SmtContext._parse_adt_sort_key(inner[start:i])
                if arg is None:
                    return None
                args.append(arg)
                start = i + 1
        last = SmtContext._parse_adt_sort_key(inner[start:])
        if last is None:
            return None
        args.append(last)
        return AdtType(name, tuple(args))

    def _ctor_instantiation_from_args(
        self, ctor_name: str, arg_types: list[Type | None],
    ) -> tuple[Type, ...] | None:
        """Derive an ADT's full type-argument tuple by unifying a
        constructor's declared field types against its concrete argument
        types (#918).

        For ``Some(Some(Int))`` the outer ``Some`` argument recovers as
        ``Option<Int>``; unifying ``Option``'s ``Some`` field ``T`` against
        ``Option<Int>`` binds ``T = Option<Int>``, so the enclosing sort is
        ``Option<Option<Int>>``.  Returns the ordered type-argument tuple for
        the owning ADT, or ``None`` when the ADT is non-generic (no
        instantiation to pin), an argument type is unknown, or unification
        can't bind every parameter — in which case the caller keeps the
        base-name scan.
        """
        adt_name = self._ctor_to_adt.get(ctor_name)
        if adt_name is None:
            return None
        info = self._adt_registry.get(adt_name)
        if info is None or not info.type_params:
            return None
        ctor_info = info.constructors.get(ctor_name)
        if ctor_info is None or ctor_info.field_types is None:
            return None
        if len(ctor_info.field_types) != len(arg_types):
            return None
        subst: dict[str, Type] = {}
        for field_ty, arg_ty in zip(ctor_info.field_types, arg_types):
            if arg_ty is None:
                return None
            if not self._unify_type_var(field_ty, arg_ty, subst):
                return None
        try:
            return tuple(subst[p] for p in info.type_params)
        except KeyError:
            # A type parameter this constructor's fields don't mention — can't
            # be pinned from these arguments alone (e.g. `Left(T)` of an
            # `Either<T, U>`).  Fall back to the base-name scan.
            return None

    @staticmethod
    def _unify_type_var(
        field_ty: Type, arg_ty: Type, subst: dict[str, Type],
    ) -> bool:
        """One-directional structural match of a declared field type (which may
        contain ``TypeVar``s) against a concrete argument type, accumulating
        the ``TypeVar`` bindings in *subst* (#918).

        Returns ``False`` on a shape/name mismatch or a conflicting rebinding
        of a variable, so the caller demotes rather than build a wrong sort.
        """
        if isinstance(field_ty, RefinedType):
            return SmtContext._unify_type_var(field_ty.base, arg_ty, subst)
        if isinstance(arg_ty, RefinedType):
            return SmtContext._unify_type_var(field_ty, arg_ty.base, subst)
        if isinstance(field_ty, TypeVar):
            bound = subst.get(field_ty.name)
            if bound is not None:
                return bound == arg_ty
            subst[field_ty.name] = arg_ty
            return True
        if isinstance(field_ty, PrimitiveType):
            # Int/Nat share a Z3 sort, so a recovered `Int` legitimately
            # matches a declared `Nat` field (and vice versa) — the distinction
            # is a refinement, not a carrier-set difference.
            if isinstance(arg_ty, PrimitiveType):
                ints = {"Int", "Nat"}
                if field_ty.name in ints and arg_ty.name in ints:
                    return True
                return field_ty.name == arg_ty.name
            return False
        if isinstance(field_ty, AdtType) and isinstance(arg_ty, AdtType):
            if field_ty.name != arg_ty.name:
                return False
            if len(field_ty.type_args) != len(arg_ty.type_args):
                return False
            return all(
                SmtContext._unify_type_var(f, a, subst)
                for f, a in zip(field_ty.type_args, arg_ty.type_args)
            )
        return False

    def _translate_nullary_ctor(
        self, expr: ast.NullaryConstructor
    ) -> z3.ExprRef | None:
        """Translate a nullary constructor (e.g. ``Nil``) to Z3."""
        sort = self._find_sort_for_ctor(expr.name)
        if sort is None:
            return None
        idx = self._find_ctor_index(sort, expr.name)
        if idx is None:  # pragma: no cover
            return None
        return sort.constructor(idx)()

    def _translate_ctor_call(
        self, expr: ast.ConstructorCall, env: SlotEnv
    ) -> z3.ExprRef | None:
        """Translate a constructor call (e.g. ``Cons(1, Nil)``) to Z3.

        Arguments are translated **first**, then their Z3 sorts are recovered
        to Vera types and unified against the constructor's declared field
        types to pin the owning ADT's full instantiation (#918).  This picks
        the correct sort for a same-ADT self-nesting like ``Some(Some(x))`` —
        the outer ``Some`` must resolve to ``Option<Option<Int>>``, not
        whichever ``Option<...>`` happens to be cached first — so the
        ``constructor(idx)`` application receives a correctly-sorted argument
        instead of crashing Z3 with a sort mismatch.  When the instantiation
        can't be pinned (non-generic ADT, un-nameable argument sort) the sort
        is found by the base-name scan, unchanged from before.
        """
        # Translate arguments first so their sorts pin the instantiation.
        z3_args: list[z3.ExprRef] = []
        for arg in expr.args:
            z3_arg = self.translate_expr(arg, env)
            if z3_arg is None:
                return None
            z3_args.append(z3_arg)
        arg_types: list[Type | None] = [
            self._z3_sort_to_vera_type(a.sort()) for a in z3_args
        ]
        type_args = self._ctor_instantiation_from_args(expr.name, arg_types)
        sort = self._find_sort_for_ctor(expr.name, type_args)
        if sort is None:
            return None
        idx = self._find_ctor_index(sort, expr.name)
        if idx is None:  # pragma: no cover
            return None
        return sort.constructor(idx)(*z3_args)

    def _type_expr_to_adt_type(self, te: ast.TypeExpr) -> Type | None:
        """Resolve a parameter type expression naming a registered ADT to its
        concrete :class:`AdtType` (#882).

        Returns None for type expressions that don't name an ADT in the
        registry (primitives, type vars, function types, unknown names).
        Type arguments are resolved recursively so a nested generic
        instantiation (``Box<Inner>``) materialises with the right element
        sort.  A refinement unwraps to its base, mirroring
        ``_vera_type_to_z3_sort``.
        """
        if isinstance(te, ast.RefinementType):
            return self._type_expr_to_adt_type(te.base_type)
        if not isinstance(te, ast.NamedType):
            return None
        if te.name not in self._adt_registry:
            return None
        type_args: list[Type] = []
        if te.type_args:
            for a in te.type_args:
                arg_ty = self._type_expr_to_adt_type(a)
                if arg_ty is None:
                    arg_ty = self._named_type_expr_to_primitive(a)
                if arg_ty is None:
                    # An argument we can't resolve (function-typed, unknown)
                    # — leave the whole instantiation unmaterialised so the
                    # caller demotes loudly rather than building a wrong sort.
                    return None
                type_args.append(arg_ty)
        return AdtType(te.name, tuple(type_args))

    @staticmethod
    def _named_type_expr_to_primitive(te: ast.TypeExpr) -> Type | None:
        """Resolve a type expression naming a primitive to its ``Type``
        (#882 helper for ADT type-argument resolution)."""
        if isinstance(te, ast.RefinementType):
            return SmtContext._named_type_expr_to_primitive(te.base_type)
        if isinstance(te, ast.NamedType) and not te.type_args:
            return PRIMITIVES.get(te.name)
        return None

    def _ensure_call_arg_sorts(
        self, param_type_exprs: Any,
    ) -> None:
        """Materialise the Z3 ADT sort for each ADT-typed parameter (#882).

        A constructor-call argument (``MkP(1)``) only translates once the
        callee's concrete ADT sort exists in ``_z3_sorts`` — otherwise
        ``_find_sort_for_ctor`` returns None and the call-site precondition
        obligation silently vanishes.  In the caller's context the sort may
        never have been created (the caller has no parameter of that ADT), so
        force it here from the callee's declared parameter types before
        translating the arguments.  A type whose sort can't be built (a
        host-handle field like ``Map``) is left absent — the argument then
        fails to translate and the caller demotes loudly to Tier-3.
        """
        for pte in param_type_exprs:
            adt_ty = self._type_expr_to_adt_type(pte)
            if adt_ty is not None:
                self._vera_type_to_z3_sort(adt_ty)

    def _type_expr_to_slot_name(self, te: ast.TypeExpr) -> str | None:
        """Extract the slot name from a type expression.

        Delegates to the shared recursive :func:`vera.slots.type_expr_slot_name`
        so the verifier's slot-env keys are fully-qualified over nested
        composites and agree with the checker + codegen (#914 finding 2).
        """
        return type_expr_slot_name(te)

    # -----------------------------------------------------------------
    # Validity checking
    # -----------------------------------------------------------------

    def check_valid(
        self,
        goal: z3.ExprRef,
        assumptions: list[z3.ExprRef],
    ) -> SmtResult:
        """Check if assumptions ⟹ goal is valid.

        Uses refutation: assert assumptions and ¬goal.
        Also includes any accumulated ``_path_conditions`` from
        if/match branches so branch-guarded preconditions verify.
        - unsat → goal always holds (verified)
        - sat → counterexample found (violated)
        - unknown → solver timeout or incomplete (unknown)
        """
        self.solver.push()
        for a in assumptions:
            self.solver.add(a)
        for pc in self._path_conditions:
            self.solver.add(pc)
        self.solver.add(z3.Not(goal))

        result = self.solver.check()
        # Extract the model BEFORE popping: a Z3 model is only valid
        # while the assertions that produced it remain on the solver
        # stack.  Popping first leaves model() describing the base
        # context, so model_completion fills the now-unconstrained
        # slots with arbitrary defaults — yielding counterexamples that
        # don't witness the violation (e.g. `@Int.0 = 0` for the goal
        # `@Int.0 >= 0`).  Affects E502 / E503 / call-site precondition
        # diagnostics alike.
        ce: dict[str, str] | None = None
        if result == z3.sat:
            ce = self._extract_counterexample(self.solver.model())
        self.solver.pop()

        if result == z3.unsat:
            return SmtResult(status="verified")
        elif result == z3.sat:
            return SmtResult(status="violated", counterexample=ce)
        else:  # pragma: no cover
            return SmtResult(status="unknown")

    def _extract_counterexample(
        self, model: z3.ModelRef
    ) -> dict[str, str]:
        """Extract variable values from a Z3 model."""
        ce: dict[str, str] = {}
        for name, var in self._vars.items():
            val = model.evaluate(var, model_completion=True)
            ce[name] = str(val)
        return ce

    def reset(self) -> None:
        """Reset per-function state for warm-session reuse (#222 Phase A).

        Called by the warm verification path between functions so one
        ``z3.Solver`` serves a whole program.  Everything tied to the
        previous function's solver assertions must go; only the ADT
        registry (pure Python metadata, identical across functions of
        one program) persists.

        ``_length_fns`` / ``_index_fns`` MUST be cleared even though
        their ``FuncDeclRef`` objects stay valid across
        ``solver.reset()``: their side-effect axioms do not.
        ``get_rank_fn`` asserts its ``ForAll rank(x) >= 0`` axiom only
        at dict-miss, so a surviving cache entry would silently skip
        re-asserting the axiom into the reset solver and ADT-measure
        ``decreases`` checks would diverge from a fresh context (caught
        by the cold-vs-warm differential tests in test_obligations.py).
        """
        self.solver.reset()
        # solver.reset() drops assertions but keeps parameters; re-apply
        # the timeout anyway so reuse never depends on that detail.
        self.solver.set("timeout", self._timeout_ms)
        self._vars.clear()
        self._result_var = None
        self._call_violations.clear()
        self._call_demotions.clear()
        self._fresh_counter = 0
        self._path_conditions.clear()
        self._length_fns = {
            "Int": z3.Function("length", z3.IntSort(), z3.IntSort()),
        }
        self._index_fns.clear()
        self._array_element_sorts.clear()
        # Keep _adt_registry and _ctor_to_adt (they persist across functions)
        # but clear cached Z3 sorts (tied to solver state)
        self._z3_sorts.clear()
