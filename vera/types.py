"""Internal type representation for the Vera type checker.

These semantic types are distinct from the syntactic AST TypeExpr nodes.
AST types mirror what the user wrote; these represent resolved, canonical
types suitable for comparison, subtyping, and substitution.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from vera import ast as _ast


# =====================================================================
# Built-in generic type-variable namespacing (#970)
# =====================================================================

# The built-in function registry (``vera/environment.py`` ``_register_builtins``)
# names its internal generic vars ``T``/``U``/``A``/``B``/``E``/``K``/``V``.  The
# inference skip-guard in ``_unify_for_inference`` compares a concrete argument's
# type-args *by name* against the callee's ``forall_vars``; an identically-named
# user ``forall<T>`` var therefore aborted unification and produced a spurious
# E202 (#970).  Every built-in internal var name is alpha-renamed at registration
# by suffixing this marker, making it impossible to collide with a user type
# name.  ``#`` is deliberate: it is outside the ``UPPER_IDENT`` grammar
# (``[A-Z][A-Za-z0-9_]*`` — see ``vera/grammar.lark``) so no user-written type
# name can contain it, and it is distinct from ``$`` (reserved for fresh
# inference placeholders — ``_is_fresh_typevar``), so a renamed var is never
# mistaken for a fresh hole.  Stripped for user-facing display (``pretty_type``).
BUILTIN_TYPEVAR_MARKER = "#b"


def strip_builtin_typevar_marker(name: str) -> str:
    """Drop the #970 built-in-namespacing marker for user-facing display.

    ``"T#b"`` → ``"T"``.  A name without the marker is returned unchanged.
    """
    return name.removesuffix(BUILTIN_TYPEVAR_MARKER)


# =====================================================================
# Type hierarchy
# =====================================================================

@dataclass(frozen=True)
class Type:
    """Abstract base for all resolved types."""


@dataclass(frozen=True)
class PrimitiveType(Type):
    """A built-in primitive type (Int, Nat, Bool, Float64, ...)."""
    name: str


@dataclass(frozen=True)
class AdtType(Type):
    """A parameterised algebraic data type (Array<T>, Option<Int>, user ADTs)."""
    name: str
    type_args: tuple[Type, ...]  # () for non-parameterised


@dataclass(frozen=True)
class FunctionType(Type):
    """A function type: params -> return with effect row."""
    params: tuple[Type, ...]
    return_type: Type
    effect: EffectRowType


@dataclass(frozen=True)
class RefinedType(Type):
    """A refinement type.  Tracks the base type and preserves the predicate
    AST node.  For subtyping the type behaves as its base (predicate-implies
    checks are deferred to the verifier); the predicate is discharged at
    verification time at every narrowing site and refined return position
    (#746), generalising the @Nat ``>= 0`` machinery to an arbitrary
    translated predicate."""
    base: Type
    predicate: _ast.Expr  # discharged by the verifier (#746), not in subtyping


@dataclass(frozen=True)
class TypeVar(Type):
    """A universally-quantified type variable (from forall<T>)."""
    name: str


@dataclass(frozen=True)
class UnknownType(Type):
    """Placeholder for unresolved or error-recovery types.

    Any operation involving UnknownType silently propagates it,
    preventing cascading error messages."""


# =====================================================================
# Effect types
# =====================================================================

@dataclass(frozen=True)
class EffectRowType:
    """Abstract base for effect rows."""


@dataclass(frozen=True)
class PureEffectRow(EffectRowType):
    """The empty effect row (effects(pure))."""


@dataclass(frozen=True)
class EffectInstance:
    """A single effect instantiation, e.g. State<Int>."""
    name: str
    type_args: tuple[Type, ...]

    def __hash__(self) -> int:
        return hash((self.name, self.type_args))


@dataclass(frozen=True)
class ConcreteEffectRow(EffectRowType):
    """A set of concrete effects, possibly with an open row variable tail."""
    effects: frozenset[EffectInstance]
    row_var: str | None = None  # None = closed row; "E" = open variable


# =====================================================================
# Primitive constants
# =====================================================================

INT = PrimitiveType("Int")
NAT = PrimitiveType("Nat")
BOOL = PrimitiveType("Bool")
FLOAT64 = PrimitiveType("Float64")
STRING = PrimitiveType("String")
BYTE = PrimitiveType("Byte")
UNIT = PrimitiveType("Unit")
NEVER = PrimitiveType("Never")

PRIMITIVES: dict[str, Type] = {
    "Int": INT,
    "Nat": NAT,
    "Bool": BOOL,
    "Float64": FLOAT64,
    "String": STRING,
    "Byte": BYTE,
    "Unit": UNIT,
    "Never": NEVER,
}

# Removed aliases — used by the checker to produce helpful error messages
# when a user writes an old alias name instead of the canonical type.
REMOVED_ALIASES: dict[str, str] = {
    "Float": "Float64",
}

# Numeric types (for operator checking)
NUMERIC_TYPES: frozenset[Type] = frozenset({INT, NAT, FLOAT64})
ORDERABLE_TYPES: frozenset[Type] = frozenset({INT, NAT, FLOAT64, BYTE, STRING})

# The primitives a string interpolation can render, and the built-in that
# renders each (#1347).  ONE table, because it is one language rule asked
# by two subsystems: the checker decides whether `"\(e)"` is well-typed
# and code generation picks the conversion to emit.  They were separate
# copies — `ExpressionsMixin._TO_STRING_TYPES` and
# `OperatorsMixin._INTERP_TO_STRING`, the second carrying the comment
# "must match checker's map" — and a comment is not a mechanism: the two
# sides disagreed about what was interpolable at all, so a program the
# checker accepted was dropped by codegen with no diagnostic naming the
# rule.  `String` is absent deliberately: it needs no conversion, and both
# consumers test it before consulting this table.
#
# Membership is decided on the type's RESOLVED form, never its spelling:
# an alias and a refinement over one of these render exactly as the
# primitive they resolve to (`vera.monomorphize.resolve_type_alias` is the
# shared walker that answers that, unwrapping refinements and following
# alias chains).  A predicate constrains which values exist; it says
# nothing about how one prints.
TO_STRING_BUILTINS: dict[str, str] = {
    "Int": "to_string",
    "Nat": "nat_to_string",
    "Bool": "bool_to_string",
    "Byte": "byte_to_string",
    "Float64": "float_to_string",
}


# =====================================================================
# Utility functions
# =====================================================================

def canonical_type_name(type_name: str,
                        type_args: tuple[Type, ...] | None = None) -> str:
    """Form the canonical string used for slot reference matching.

    Type aliases are OPAQUE: @PosInt.0 and @Int.0 are separate namespaces.
    Parameterised types include args: "Option<Int>", "List<T>".
    """
    if not type_args:
        return type_name
    arg_strs = ", ".join(pretty_type(a) for a in type_args)
    return f"{type_name}<{arg_strs}>"


def pretty_type(ty: Type) -> str:
    """Human-readable type string for error messages."""
    if isinstance(ty, PrimitiveType):
        return ty.name
    if isinstance(ty, AdtType):
        if ty.type_args:
            args = ", ".join(pretty_type(a) for a in ty.type_args)
            return f"{ty.name}<{args}>"
        return ty.name
    if isinstance(ty, FunctionType):
        params = ", ".join(pretty_type(p) for p in ty.params)
        ret = pretty_type(ty.return_type)
        eff = pretty_effect(ty.effect)
        return f"fn({params} -> {ret}) {eff}"
    if isinstance(ty, RefinedType):
        return f"{{@{pretty_type(ty.base)} | ...}}"
    if isinstance(ty, TypeVar):
        return strip_builtin_typevar_marker(ty.name)
    if isinstance(ty, UnknownType):
        return "?"
    return str(ty)


def _is_leaked_placeholder_var(ty: Type) -> bool:
    """A type variable that is an INTERNAL placeholder leaked into a diagnostic.

    Two flavours, neither user-meaningful when it surfaces as an *inferred*
    (actual) type: a fresh inference hole (``A$1`` — the ``$`` convention of
    ``_is_fresh_typevar``) that inference never filled, and a namespaced
    built-in generic var (``V#b`` — the #970/#982 ``BUILTIN_TYPEVAR_MARKER``)
    that escaped unresolved because a built-in's result type could not be
    substituted (e.g. the element type of ``map_values(@M.0)[0]`` read through
    a refinement alias, #1069).  A genuine *user* ``forall`` var (plain ``T``,
    no marker) is NOT a leak — it is the spelling the programmer wrote — so it
    is left untouched.
    """
    return isinstance(ty, TypeVar) and (
        "$" in ty.name or BUILTIN_TYPEVAR_MARKER in ty.name
    )


def _leaked_placeholders_to_unknown(ty: Type) -> Type:
    """Replace every leaked placeholder var (``_is_leaked_placeholder_var``),
    at any nesting depth, with ``UnknownType`` so it renders as ``?``."""
    if _is_leaked_placeholder_var(ty):
        return UnknownType()
    if isinstance(ty, AdtType):
        return AdtType(
            ty.name,
            tuple(_leaked_placeholders_to_unknown(a) for a in ty.type_args),
        )
    if isinstance(ty, FunctionType):
        # The effect row scrubs too: ``pretty_effect`` renders each
        # ``EffectInstance.type_args``, so a leak inside e.g.
        # ``effects(<State<V#b>>)`` would surface exactly like a
        # parameter-position leak (PR #1088 review).
        effect = ty.effect
        if isinstance(effect, ConcreteEffectRow):
            effect = ConcreteEffectRow(
                frozenset(
                    EffectInstance(
                        e.name,
                        tuple(_leaked_placeholders_to_unknown(a)
                              for a in e.type_args),
                    )
                    for e in effect.effects
                ),
                effect.row_var,
            )
        return FunctionType(
            tuple(_leaked_placeholders_to_unknown(p) for p in ty.params),
            _leaked_placeholders_to_unknown(ty.return_type),
            effect,
        )
    if isinstance(ty, RefinedType):
        return RefinedType(
            _leaked_placeholders_to_unknown(ty.base), ty.predicate)
    return ty


def pretty_inferred_type(ty: Type) -> str:
    """``pretty_type`` for an INFERRED/actual type in a mismatch diagnostic.

    A leaked internal placeholder var (``_is_leaked_placeholder_var``) renders
    as the unknown marker ``?`` rather than a bare stripped letter that
    masquerades as a real, user-meaningful type (#1069: ``body has type V``,
    where ``V`` is ``map_values``'s unsubstituted element var).

    Use ONLY at the *actual*-type slot of a mismatch message ("body / value /
    field / argument … has type X"); the *expected*-type slot keeps
    ``pretty_type`` because a built-in's unsubstituted signature there
    (``Array<T>``, ``Map<K, V>``) IS meaningful and is deliberately pinned
    (``test_e202_expected_type_strips_marker``).
    """
    return pretty_type(_leaked_placeholders_to_unknown(ty))


def pretty_effect(eff: EffectRowType) -> str:
    """Human-readable effect row string."""
    if isinstance(eff, PureEffectRow):
        return "effects(pure)"
    if isinstance(eff, ConcreteEffectRow):
        parts = sorted(
            canonical_type_name(e.name, e.type_args if e.type_args else None)
            for e in eff.effects
        )
        if eff.row_var:
            parts.append(eff.row_var)
        return f"effects(<{', '.join(parts)}>)"
    return "effects(?)"


# =====================================================================
# Structural (DISCRIMINATING) type keys
# =====================================================================

def structural_type_key(ty: Type) -> str:
    """A rendering of *ty* that DISCRIMINATES, rather than one that reads well.

    :func:`vera.types.pretty_type` is a presentation renderer, and two of its
    choices are deliberate elisions: a `RefinedType` prints `{@Int | ...}`
    with its predicate replaced by an ellipsis, and a `TypeVar` prints with
    :data:`BUILTIN_TYPEVAR_MARKER` stripped (`T#b` → `T`).  Both are right for
    an error message and wrong for an ORDERING key — distinct types render
    identically, so they tie, and a stable `sorted` then falls back to the
    input's own order.  Fed from a `frozenset` that is the `PYTHONHASHSEED`
    dependence the ordering exists to remove.

    Deterministic by construction: every branch is a fixed-shape recursion
    over dataclass fields, and the only set this touches is a function type's
    effect row, which :func:`structural_effect_key` sorts on a key built the
    same structural way.

    The predicate is rendered by :func:`vera.formatter.format_expr_canonical` — the
    single-line canonical source form ``vera fmt`` emits.  Two properties
    make it the right renderer, and they are the reason it is not
    ``ast.Node.pretty`` (which this used first):

    * It DISCRIMINATES, because it is a left inverse of parsing.
      Parenthesisation is re-derived from precedence and associativity
      rather than copied, precisely so the text re-parses to the same
      expression — ``(a + b) + c`` renders ``a + b + c`` while
      ``a + (b + c)`` keeps its parentheses.  ``parse(format(e)) == e``
      therefore gives ``format(a) == format(b) => a == b``, and ``vera
      fmt``'s idempotence postcondition plus
      ``scripts/check_corpus_canonical.py`` exercise that round trip over
      the whole corpus on every commit.
    * It is LINEAR in the predicate's source length.  This key names a
      State/Exn cell FAMILY (:func:`vera.naming.family_name`), which is
      mangled into a WASM import name, and ``Node.pretty``'s
      newline-indented tree grows QUADRATICALLY in nesting depth: 44
      left-nested ``&&`` conjuncts rendered 56,604 characters there against
      646 here, and mangled that crossed wasmparser's 100,000-byte
      name-string cap.  Check, verify and compile all passed; ``vera run``
      then failed to parse the module it had just emitted, while the
      browser host ran the same bytes — a runtime divergence on a
      check-green program (PR #1238 review).
      ``vera/codegen/compilability.py``'s
      :data:`~vera.codegen.compilability.MAX_CELL_FAMILY_SYMBOL` backstops
      the residue loudly.

    One derivation, still: the checker's effect-row ordering and the cell
    family read the SAME key, so a predicate that discriminates two rows
    discriminates two cells, by construction rather than by agreement.
    """
    if isinstance(ty, RefinedType):
        # Imported here rather than at module scope: `vera.formatter` pulls
        # in the parser and the transformer, and `vera.types` is imported by
        # most of the compiler — a module-level edge would make every
        # importer of a semantic type pay for the grammar.  Nothing in the
        # formatter's own import closure reaches back here, so this is a
        # cost decision, not a cycle break.
        from vera.formatter import format_expr_canonical
        return (f"{{{structural_type_key(ty.base)}"
                f"|{format_expr_canonical(ty.predicate, structural=True)}}}")
    if isinstance(ty, TypeVar):
        # The raw name, marker included.
        return f"'{ty.name}"
    if isinstance(ty, AdtType):
        if not ty.type_args:
            return ty.name
        args = ", ".join(structural_type_key(a) for a in ty.type_args)
        return f"{ty.name}<{args}>"
    if isinstance(ty, FunctionType):
        params = ", ".join(structural_type_key(p) for p in ty.params)
        return (f"fn({params} -> {structural_type_key(ty.return_type)}) "
                f"{structural_effect_key(ty.effect)}")
    return pretty_type(ty)


def effect_sort_key(ei: EffectInstance) -> tuple[str, str]:
    """A STRUCTURAL total order on effect instances (#1215 / #1231).

    Used as the deterministic tiebreak for row members
    :attr:`TypeEnv.current_effect_order` does not mention.  Keying on the
    effect NAME alone is not a total order: spec §7.3.3 permits one effect
    twice with different type arguments (`effects(<State<Int>, State<Bool>>)`
    is two independent cells), so those two tie, and `sorted` — being stable —
    then preserves the `frozenset`'s own iteration order, reintroducing the
    exact `PYTHONHASHSEED` dependence the ordering exists to remove.
    Rendering the arguments makes the key discriminate them.

    The rendering is :func:`structural_type_key`, not `pretty_type` (round-5
    review): the human-readable renderer elides a refinement's predicate and
    a type variable's built-in marker, so `effects(<State<Pos>, State<Neg>>)`
    over two refinement aliases of one base tied on the key exactly as the
    name-only version tied `State<Int>` against `State<Bool>` — the same bug
    one level down, in the fix for it.
    """
    return (
        ei.name,
        ", ".join(structural_type_key(a) for a in ei.type_args),
    )


def structural_effect_key(eff: EffectRowType) -> str:
    """A rendering of an effect ROW that DISCRIMINATES (round-9 review).

    The type-argument tiebreak reaches an effect row whenever a type argument
    is a function type — `effects(<Cb<fn(@Int -> @Bool) effects(<State<Pos>>)>>)`
    — and that leg was rendered by :func:`vera.types.pretty_effect`, which
    renders each member through `pretty_type`.  So the two elisions
    :func:`structural_type_key` exists to avoid came back at the NESTED
    depth: two outer instances differing only inside a nested row (by a
    refinement's predicate, or by a type variable's built-in marker) rendered
    identically, tied, and a stable `sorted` handed back the `frozenset`'s own
    order — the `PYTHONHASHSEED` dependence, three levels into its own fix.

    Rendering members through :func:`effect_sort_key` closes it and makes the
    two mutually recursive, which is what "structural all the way down" means
    here: a nested row's own function-typed arguments recurse back through
    this.  Deterministic despite reading a `frozenset`, because the members
    are sorted on that structural key rather than on a presentation string —
    a total order, so the sort's stability is never consulted.  The open row
    variable is part of the row's identity, so it is rendered too.
    """
    if isinstance(eff, PureEffectRow):
        return "effects(pure)"
    if isinstance(eff, ConcreteEffectRow):
        parts = [
            f"{name}<{args}>" if args else name
            for name, args in sorted(effect_sort_key(e) for e in eff.effects)
        ]
        if eff.row_var:
            # `'`-prefixed, exactly as :func:`structural_type_key`'s
            # `TypeVar` branch marks a variable (PR #1238 review).  An open
            # ROW VARIABLE and a zero-argument effect MEMBER of the same
            # spelling both rendered bare `E`, so an open
            # `effects(<E>)` under `forall<E>` tied with a closed
            # `effects(<E>)` over a declared `effect E`.  This key names a
            # cell, so a tie is two cells sharing one host cell — the same
            # class as the elisions the key exists to avoid, one level out.
            parts.append(f"'{eff.row_var}")
        return f"effects(<{', '.join(parts)}>)"
    return "effects(?)"


def base_type(ty: Type) -> Type:
    """Strip refinement wrappers to get the underlying base type."""
    while isinstance(ty, RefinedType):
        ty = ty.base
    return ty


def erases_to_unit(ty: Type) -> bool:
    """True if ``ty`` has NO WASM representation — it erases to no runtime local.

    Mirrors codegen's ``_type_expr_to_wasm_type`` (``vera/codegen/core.py``),
    which returns ``None`` for ``Unit`` and recurses *transparently* through
    ``Future<T>`` (#841: a ``Future`` is representation-identical to its
    payload) and refinement wrappers.  ``Future<Unit>`` therefore erases to
    nothing exactly like bare ``Unit`` — reading such a value via a ``@T.n``
    slot lowers to a ``local.get`` on a local that does not exist (the
    dangling-slot codegen invariant behind E206 / E699).  Every other ADT is a
    heap pointer (i32), so it is NOT zero-size: ``Option<Unit>`` (tag + pointer)
    and ``Future<Int>`` (i32) both erase to a real local.  ``Future`` is the
    only transparent ADT wrapper, so it is the only recursion here.  Keep in
    sync with ``_type_expr_to_wasm_type`` (#939 review found the two had drifted:
    the discriminator keyed on bare ``Unit`` only, missing ``Future<Unit>``).
    """
    ty = base_type(ty)  # strip RefinedType wrappers (matches codegen's recurse)
    if ty == UNIT:
        return True
    if isinstance(ty, AdtType) and ty.name == "Future" and len(ty.type_args) == 1:
        return erases_to_unit(ty.type_args[0])
    return False


def is_subtype(sub: Type, sup: Type) -> bool:
    """Check if sub <: sup under the subtyping rules.

    Rules:
    1. Reflexivity: T <: T (including TypeVar("X") <: TypeVar("X"))
    2. Never <: T for all T
    3a. Nat <: Int (widening — always safe)
    3b. Int <: Nat (checker permits; verifier enforces non-negativity via Z3)
    4. ADT structural: same name + covariant subtyping on type args
    5. RefinedType(base, _) <: base
    6. RefinedType(base, _) <: T if base <: T
    7. T <: RefinedType(base, _) if T <: base (predicate enforced by verifier)
    8. UnknownType is compatible with everything (error recovery)
    9. FunctionType: params contravariant, return covariant, effects covariant

    TypeVar is NOT compatible with concrete types.  TypeVar equality is
    handled by reflexivity (rule 1).  At call sites, type inference
    substitutes TypeVars before subtype checks; unresolved TypeVars are
    skipped by the caller.
    """
    # Unknown propagates silently
    if isinstance(sub, UnknownType) or isinstance(sup, UnknownType):
        return True

    # Reflexivity (structural equality)
    if types_equal(sub, sup):
        return True

    # Never is bottom
    if isinstance(sub, PrimitiveType) and sub.name == "Never":
        return True

    # Nat <: Int (widening — always safe)
    # Int <: Nat (checker permits; verifier enforces >= 0 via Z3)
    if isinstance(sub, PrimitiveType) and isinstance(sup, PrimitiveType):
        if sub.name == "Nat" and sup.name == "Int":
            return True
        if sub.name == "Int" and sup.name == "Nat":
            return True

    # ADT with compatible type args (e.g. Option<T> <: Option<T>)
    if isinstance(sub, AdtType) and isinstance(sup, AdtType):
        if sub.name == sup.name and len(sub.type_args) == len(sup.type_args):
            return all(
                is_subtype(sa, pa) for sa, pa in
                zip(sub.type_args, sup.type_args)
            )

    # Refinement to base: { @T | P } <: T
    if isinstance(sub, RefinedType):
        return is_subtype(sub.base, sup)

    # Refinement on the sup side: T <: { @T | P } only if T <: base
    # (predicate enforced by the contract verifier, not the type checker)
    if isinstance(sup, RefinedType):
        return is_subtype(sub, sup.base)

    # FunctionType subtyping: params contravariant, return covariant,
    # effects covariant (Spec §7.8).
    if isinstance(sub, FunctionType) and isinstance(sup, FunctionType):
        if len(sub.params) != len(sup.params):
            return False
        # Params: contravariant (sup params <: sub params)
        if not all(is_subtype(sp, sbp)
                   for sp, sbp in zip(sup.params, sub.params)):
            return False
        # Return: covariant (sub return <: sup return)
        if not is_subtype(sub.return_type, sup.return_type):
            return False
        # Effects: covariant (sub effects <: sup effects)
        return is_effect_subtype(sub.effect, sup.effect)

    return False


def numeric_join(left: Type, right: Type) -> Type | None:
    """Least upper bound of two numeric bases under the *formal* lattice.

    Used to type mixed arithmetic (``left <op> right``).  The result is the
    LUB of the two operand types under the only formal primitive subtyping
    rule among numerics — ``Nat <: Int`` (``Nat`` is ``{ @Int | @Int.0 >= 0 }``,
    a refinement subtype of ``Int``; spec §2.2.1, §2.8 rule 3).  Concretely:

    - identical bases            → that base (``Int⊔Int=Int``, ``Nat⊔Nat=Nat``)
    - ``Int`` mixed with ``Nat`` → ``Int``  (the formal LUB, either operand order)
    - anything else (e.g. ``Int``/``Float64``) → ``None`` (incompatible)

    Returns ``None`` when the two are not both numeric or have no common
    numeric supertype, so the caller can emit the type-mismatch diagnostic.

    This deliberately does **not** consult :func:`is_subtype`, whose
    ``Int <: Nat`` clause is a verifier-mediated narrowing *relaxation* (spec
    §2.8 rule 5 implementation note), not a formal widening.  Relying on that
    bidirectionality typed ``Int <op> Nat`` as ``Nat`` (#755) — dishonestly
    asserting non-negativity with no verifier obligation, against §0.2.2
    ("no implicit behaviour").
    """
    lb = base_type(left)
    rb = base_type(right)
    if lb not in NUMERIC_TYPES or rb not in NUMERIC_TYPES:
        return None
    if types_equal(lb, rb):
        return lb
    # The only cross-type numeric pair with a formal LUB is {Int, Nat} → Int
    # (Nat <: Int).  Float64 is incomparable to both.
    if {lb, rb} == {INT, NAT}:
        return INT
    return None


def is_effect_subtype(sub: EffectRowType, sup: EffectRowType) -> bool:
    """Check if effect row *sub* <: *sup* (subeffecting).

    Rules (Spec Chapter 7, Section 7.8):
    1. Reflexivity: E <: E
    2. Pure is bottom: effects(pure) <: effects(<...>)
    3. Subset: effects(<A, B>) <: effects(<A, B, C>)
    4. Open rows: if *sub* has an unresolved row variable, be permissive
       (full row-variable unification is deferred to #55).
    """
    # Both pure
    if isinstance(sub, PureEffectRow) and isinstance(sup, PureEffectRow):
        return True

    # Pure is subtype of everything
    if isinstance(sub, PureEffectRow):
        return True

    # Concrete <: Pure only if the concrete row is empty
    if isinstance(sup, PureEffectRow):
        if isinstance(sub, ConcreteEffectRow):
            return len(sub.effects) == 0
        return False

    # Both concrete: sub.effects must be a subset of sup.effects
    if isinstance(sub, ConcreteEffectRow) and isinstance(sup, ConcreteEffectRow):
        # Unresolved row variable — be permissive until #55
        if sub.row_var is not None:
            return True
        # If sup has a row variable, the concrete effects must still subset
        return sub.effects.issubset(sup.effects)

    return False


def effects_equal(a: EffectRowType, b: EffectRowType) -> bool:
    """Structural equality for effect rows."""
    if isinstance(a, PureEffectRow) and isinstance(b, PureEffectRow):
        return True
    if isinstance(a, ConcreteEffectRow) and isinstance(b, ConcreteEffectRow):
        return a.effects == b.effects and a.row_var == b.row_var
    return False


def types_equal(a: Type, b: Type) -> bool:
    """Structural type equality."""
    if isinstance(a, UnknownType) or isinstance(b, UnknownType):
        return True
    if type(a) is not type(b):
        return False
    if isinstance(a, PrimitiveType) and isinstance(b, PrimitiveType):
        return a.name == b.name
    if isinstance(a, AdtType) and isinstance(b, AdtType):
        return (a.name == b.name
                and len(a.type_args) == len(b.type_args)
                and all(types_equal(x, y)
                        for x, y in zip(a.type_args, b.type_args)))
    if isinstance(a, FunctionType) and isinstance(b, FunctionType):
        return (len(a.params) == len(b.params)
                and all(types_equal(x, y)
                        for x, y in zip(a.params, b.params))
                and types_equal(a.return_type, b.return_type)
                and effects_equal(a.effect, b.effect))
    if isinstance(a, RefinedType) and isinstance(b, RefinedType):
        return types_equal(a.base, b.base)
    if isinstance(a, TypeVar) and isinstance(b, TypeVar):
        return a.name == b.name
    return a == b


def state_cell_decl_equal(cell: Type, declared: Type) -> bool:
    """The E336/E533 equality: does a handler state DECLARATION match the
    builtin State effect's resolved cell type?

    ``types_equal`` — deliberately NOT ``is_subtype``, which conflates
    ``Int``/``Nat`` (rule 3b) and erases refinements to their bases (rules
    5–7) — tightened for refined pairs: ``types_equal`` compares refined
    types by BASE only (predicates are the verifier's domain in
    subtyping), which would let a refined-vs-refined divergence lie
    (``@{... > 3}`` on ``State<{... < 10}>``).  Predicate AST ``==`` is
    structural and span-insensitive, so the same alias, two textually
    identical aliases, and identical literals all stay equal; only
    genuinely different predicates diverge.  Shared by the checker's
    concrete gate (E336) and the verifier's per-instantiation recheck
    (E533) so the two phases can never drift.
    """
    if not types_equal(cell, declared):
        return False
    return _refined_predicates_agree(cell, declared)


def _refined_predicates_agree(a: Type, b: Type) -> bool:
    """Structural predicate agreement at EVERY depth of two
    ``types_equal`` types — ``types_equal`` compares refined types by
    base only, at the top AND inside ADT type arguments, so
    ``Option<{@Int | P}>`` vs ``Option<{@Int | Q}>`` passed the
    round-3 top-level-only check (PR #1202 review round: E336 and E533
    silently accepted nested refined divergence)."""
    if isinstance(a, RefinedType) and isinstance(b, RefinedType):
        return (a.predicate == b.predicate
                and _refined_predicates_agree(a.base, b.base))
    if isinstance(a, RefinedType) or isinstance(b, RefinedType):
        # types_equal held, so a one-sided refinement means the pair
        # already diverges structurally — defensive False.
        return False
    if isinstance(a, AdtType) and isinstance(b, AdtType):
        return all(
            _refined_predicates_agree(x, y)
            for x, y in zip(a.type_args, b.type_args)
        )
    if isinstance(a, FunctionType) and isinstance(b, FunctionType):
        # A refined predicate inside a fn-typed position (param or
        # return) is a divergence surface too — `State<fn({@Int | P}
        # -> Int)>` with a `{@Int | Q}` declared param compiled
        # (round-9 review): recurse both.
        return (all(
            _refined_predicates_agree(x, y)
            for x, y in zip(a.params, b.params))
            and _refined_predicates_agree(a.return_type, b.return_type))
    return True


def contains_typevar(ty: Type) -> bool:
    """True if *ty* contains any TypeVar anywhere in its structure."""
    if isinstance(ty, TypeVar):
        return True
    if isinstance(ty, AdtType):
        return any(contains_typevar(a) for a in ty.type_args)
    if isinstance(ty, FunctionType):
        return (any(contains_typevar(p) for p in ty.params)
                or contains_typevar(ty.return_type))
    if isinstance(ty, RefinedType):
        return contains_typevar(ty.base)
    return False


def _is_fresh_typevar(ty: Type) -> bool:
    """A fresh, unresolved inference placeholder (`A$1` from _fresh_typevar).

    Distinct from a genuine callee forall var (`T`, no `$`): a fresh var is a
    "don't-know-yet" hole that a more-determined sibling binding should fill.
    """
    return isinstance(ty, TypeVar) and "$" in ty.name


def contains_fresh_typevar(ty: Type) -> bool:
    """True if *ty* contains a FRESH inference placeholder (`T$n`) anywhere.

    Distinct from :func:`contains_typevar`, which also matches rigid forall
    vars: a rigid `T` is a valid, fully-resolved type inside its own forall
    body, while a `$`-marked var is a hole inference has not filled (#993).
    """
    if isinstance(ty, TypeVar):
        return "$" in ty.name
    if isinstance(ty, AdtType):
        return any(contains_fresh_typevar(a) for a in ty.type_args)
    if isinstance(ty, FunctionType):
        return (any(contains_fresh_typevar(p) for p in ty.params)
                or contains_fresh_typevar(ty.return_type))
    if isinstance(ty, RefinedType):
        return contains_fresh_typevar(ty.base)
    return False


def merge_inferred_types(
    a: Type, b: Type, nested: bool = False,
) -> tuple[Type, bool]:
    """Merge two candidate inferred types for one type variable (#898).

    When a generic's type variable is bound by several constructor-literal
    arguments — a sparse multi-parameter ADT where each argument pins a
    *different* type parameter — the per-argument inferred types share a
    parameterised head but disagree on which positions are known:

        Res<?, Int>  ⊔  Res<String, ?>  =  Res<String, Int>

    (`?` is a fresh inference placeholder, `A$1`).  Returns ``(merged, conflict)``:

    - A fresh placeholder on either side yields to the other side (the
      more-determined binding wins), never a conflict.
    - Two same-named ``AdtType`` heads merge position-wise, recursively; a
      per-position conflict propagates.
    - Two ``Nat``/``Int`` primitives merge to their formal LUB (``Int``) — the
      only concrete-primitive subtyping relation — and are not a conflict.
    - Structurally-equal types merge to themselves.

    ``conflict`` is reported ONLY for an irreconcilable mismatch that occurs at
    a **nested type-argument position** of a shared parameterised head (the
    sparse-ADT case the merge exists for, `MkOk("x")` vs `MkOk(5)` → the `A`
    position disagrees `String` vs `Int`).  A **top-level** mismatch between two
    otherwise-unrelated candidate bindings (e.g. `set_add(@Set<Nat>.0, "oops")`
    binds `T` to `Nat` from the container and `String` from the element) is NOT
    a merge scenario — it is an ordinary argument-type mismatch — so the first
    binding is kept and ``conflict`` stays ``False``, letting the normal
    subtype check emit the precise "expected Nat" `E202`.  ``nested`` tracks
    whether we are already inside such a structural merge.
    """
    # A fresh placeholder is a hole — take the other (more-determined) side.
    if _is_fresh_typevar(a):
        return (b, False)
    if _is_fresh_typevar(b):
        return (a, False)
    # Already structurally identical — nothing to reconcile.
    if types_equal(a, b):
        return (a, False)
    # Same parameterised head — merge each type-argument position.  This is the
    # ONLY case that improves on first-argument-wins: two sparse constructor
    # arguments each pinning a different type parameter (`Res<?, Int>` and
    # `Res<String, ?>`).  Positions recurse as ``nested`` so a real disagreement
    # there is an E205 conflict.
    if (isinstance(a, AdtType) and isinstance(b, AdtType)
            and a.name == b.name and len(a.type_args) == len(b.type_args)):
        merged_args: list[Type] = []
        any_conflict = False
        for pa, pb in zip(a.type_args, b.type_args):
            m, c = merge_inferred_types(pa, pb, nested=True)
            merged_args.append(m)
            any_conflict = any_conflict or c
        return (AdtType(a.name, tuple(merged_args)), any_conflict)
    # A refinement merges as its base (subtyping treats it as the base).
    if isinstance(a, RefinedType) or isinstance(b, RefinedType):
        base_a = a.base if isinstance(a, RefinedType) else a
        base_b = b.base if isinstance(b, RefinedType) else b
        m, c = merge_inferred_types(base_a, base_b, nested=nested)
        return (m, c)
    # Nat/Int — the sole concrete-primitive subtyping pair — only when merging a
    # NESTED type-argument position (`Res<Nat, ?>` ⊔ `Res<Int, ?>` → the LUB
    # `Int`).  At the TOP LEVEL, keep the first binding (below) so an existing
    # `@Nat`↔`@Int` narrowing obligation on a sibling argument (#747:
    # `pick(@Nat.0, @Int.0)`) is preserved exactly as under first-argument-wins.
    if (nested
            and isinstance(a, PrimitiveType) and isinstance(b, PrimitiveType)
            and {a.name, b.name} == {"Nat", "Int"}):
        return (PrimitiveType("Int"), False)
    # Anything else: keep the first binding — identical to the pre-#898
    # first-argument-wins behaviour.  A TOP-LEVEL mismatch is an ordinary
    # argument-type error the caller's subtype check reports precisely (no
    # spurious E205); only a NESTED disagreement inside a shared parameterised
    # head is a genuine conflict.
    return (a, nested)


def substitute(ty: Type, mapping: dict[str, Type]) -> Type:
    """Apply a type-variable substitution."""
    if isinstance(ty, TypeVar):
        return mapping.get(ty.name, ty)
    if isinstance(ty, AdtType):
        new_args = tuple(substitute(a, mapping) for a in ty.type_args)
        return AdtType(ty.name, new_args)
    if isinstance(ty, FunctionType):
        new_params = tuple(substitute(p, mapping) for p in ty.params)
        new_ret = substitute(ty.return_type, mapping)
        return FunctionType(new_params, new_ret, ty.effect)
    if isinstance(ty, RefinedType):
        return RefinedType(substitute(ty.base, mapping), ty.predicate)
    # PrimitiveType, UnknownType — unchanged
    return ty


def substitute_effect(eff: EffectRowType,
                      mapping: dict[str, Type]) -> EffectRowType:
    """Apply a type-variable substitution to an effect row."""
    if isinstance(eff, ConcreteEffectRow):
        new_effects = frozenset(
            EffectInstance(e.name, tuple(substitute(a, mapping)
                                        for a in e.type_args))
            for e in eff.effects
        )
        return ConcreteEffectRow(new_effects, eff.row_var)
    return eff

# The span-keyed side-table shapes, spelled once (#987).  ``SpanKey`` is
# ``ast.span_key``'s tuple — (line, col, end_line, end_col) — and a
# ``SpanTypeTable`` maps it to the checker's recorded ``Type`` for that
# expression.  ``ModuleArtifacts`` maps a resolved module's path tuple to its
# own ``(expr_semantic_types, expr_target_types)`` table pair.
SpanKey = tuple[int, int, int, int]
SpanTypeTable = dict[SpanKey, Type]
ModuleArtifacts = dict[tuple[str, ...], tuple[SpanTypeTable, SpanTypeTable]]
