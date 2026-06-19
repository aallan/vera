# Chapter 2: Types

## 2.1 Overview

Vera's type system is the primary mechanism for constraining the space of valid programs. It combines:

- Primitive and compound types
- Algebraic data types (ADTs)
- Parametric polymorphism
- Refinement types (types with logical predicates)
- Function types with effect annotations

Every expression in a Vera program has a statically determined type. There is no type inference for top-level function signatures — all types must be explicitly declared. Local type inference is permitted within function bodies for let bindings.

## 2.2 Primitive Types

| Type | Description | Size | Range / Values |
|------|-------------|------|----------------|
| `Int` | Signed 64-bit integer | 8 bytes | -2^63 to 2^63 - 1 |
| `Nat` | Non-negative integer | 8 bytes | 0 to 2^63 - 1 |
| `Bool` | Boolean | 1 byte | `true`, `false` |
| `Float64` | IEEE 754 double | 8 bytes | Standard double-precision |
| `String` | UTF-8 string | Variable | Immutable, heap-allocated |
| `Byte` | Unsigned 8-bit integer | 1 byte | 0 to 255 |
| `Unit` | Unit type | 0 bytes | `()` |
| `Never` | Bottom type (no values) | — | Uninhabited |

`Nat` is a refinement of `Int`: it is equivalent to `{ @Int | @Int.0 >= 0 }`. The compiler recognises `Nat` as a built-in alias and optimises accordingly.

### 2.2.1 `Int` and `Nat` compatibility

`Int` and `Nat` interoperate in both directions, but the two directions sit at different layers of the type system:

- **`Nat <: Int` is a formal subtyping rule.** It follows from refinement subtyping (§2.6.2, §2.8 rule 3): `Nat` is `{ @Int | @Int.0 >= 0 }`, and a refined type is always a subtype of its base.  Widening is unconditionally safe — no proof obligation, no runtime check.  Use a `@Nat` anywhere `@Int` is expected.
- **`Int -> Nat` is not a formal subtyping rule** (it is explicitly excluded by §2.8 rule 5: "no other subtyping").  Instead, the type checker permits the flow as a **verifier-mediated relaxation**: the narrowing requires `@Int.0 >= 0`, and the type checker emits a verification obligation that the contract verifier (Tier 1) discharges via Z3 from the surrounding context (`requires`, `if` conditions, prior `assert`s).  If the obligation cannot be discharged statically, it falls to a runtime check (Tier 3).  The implementation note in §2.8 documents this relaxation alongside the formal rules.

The distinction matters because of §0.2.2 ("no implicit behaviour"): `Nat <: Int` is a true formal subtyping rule consistent with the principle (it's a logical consequence of refinement subtyping, not an implicit conversion); `Int -> Nat` is a verifier-mediated convenience that's syntactically silent but semantically verified — the verifier is the explicit check, not the syntax.

The practical implication for user code: do **not** insert `nat_to_int` defensively when calling a built-in that returns `@Int` (e.g. `array_length`) into a `@Nat` position.  The conversion is verifier-mediated and either statically discharged or guarded at runtime — `nat_to_int` is needed only when the value is genuinely allowed to be negative.

`Never` is the type of expressions that never produce a value (e.g., functions that always diverge or branches that are statically unreachable). `Never` is a subtype of every type.

## 2.3 Compound Types

### 2.3.1 Tuple Types

```
Tuple<Int, String, Bool>
```

Tuples are fixed-size, heterogeneous ordered collections. The empty tuple `Tuple<>` is equivalent to `Unit`.

Tuple elements are accessed by type-indexed slot references within the destructured binding (see Chapter 3).

### 2.3.2 Array Types

```
Array<Int>
```

Arrays are fixed-size, homogeneous, immutable ordered collections. Array length is known at runtime and accessible via the `array_length` built-in.

Array elements are accessed by integer index: `@Array<Int>.0[3]` accesses the element at index 3 of the nearest `Array<Int>` binding.

### 2.3.3 Option Type

```
Option<Int>
```

`Option<T>` is a built-in algebraic data type equivalent to:

```
public data Option<T> {
  Some(T),
  None
}
```

It represents a value that may or may not be present.

### 2.3.4 Result Type

```
Result<Int, String>
```

`Result<T, E>` is a built-in algebraic data type equivalent to:

```
public data Result<T, E> {
  Ok(T),
  Err(E)
}
```

It represents a computation that may succeed with a value of type `T` or fail with an error of type `E`.

## 2.4 Algebraic Data Types (ADTs)

User-defined algebraic data types are declared with the `data` keyword:

```
private data List<T> {
  Cons(T, List<T>),
  Nil
}
```

```
private data Tree<T> {
  Leaf(T),
  Node(Tree<T>, Tree<T>)
}
```

```
private data Color {
  Red,
  Green,
  Blue
}
```

Rules:

1. The type name MUST begin with an uppercase letter.
2. Constructor names MUST begin with an uppercase letter.
3. Constructor names MUST be unique within the data declaration.
4. ADTs may be recursive (a constructor may reference the type being defined).
5. ADTs may be parameterised by type variables.
6. Type parameters are introduced by `<A, B, ...>` after the type name.
7. Each constructor is a distinct variant. Constructors with fields carry positional data.
8. ADTs are immutable. There is no way to modify a value after construction.

### 2.4.1 ADT Invariants

> **Status: Not yet implemented.** The `invariant(...)` clause on `data` declarations is specified here but is not currently working in the reference compiler — every documented form fails with `[E130] no <DataName> bindings in scope`, because the slot environment for the invariant predicate is not yet wired up.  Tracked in [#686](https://github.com/aallan/vera/issues/686) (successor to the now-closed #560 — that earlier issue was about removing the broken spec examples; the feature implementation is the remaining work).  Until the implementation lands, refinement types (Section 2.6) are the working alternative for expressing constraints on data values.

An ADT may declare an invariant that all values must satisfy:

```
private data SortedList<T>
  invariant(is_sorted(@SortedList<T>.0))
{
  SCons(T, SortedList<T>),
  SNil
}
```

When implemented, the invariant will be checked by the contract verifier at every construction site.  At present (per the status callout above) the form is unparseable in the reference compiler, so no checking occurs and refinement types (§2.6) are the working alternative.

## 2.5 Function Types

Function types include parameter types, return type, and effect annotation:

```
Fn(@Int, @Int -> @Int) effects(pure)
```

```
Fn(@String -> @Unit) effects(<IO>)
```

```
Fn(@Array<T>, Fn(@T -> @Bool) effects(<E>) -> @Array<T>) effects(<E>)
```

A function type with no effects annotation defaults to `effects(pure)`.

Function types are first-class: functions can be passed as arguments, returned from functions, and stored in data structures.

## 2.6 Refinement Types

A refinement type constrains a base type with a logical predicate:

```
{ @Int | @Int.0 > 0 }
```

This denotes the type of integers greater than zero. The `@Int.0` in the predicate refers to the value being refined.

More examples:

```
{ @Int | @Int.0 >= 0 && @Int.0 < 100 }       -- integers in [0, 100)
{ @Array<Int> | array_length(@Array<Int>.0) > 0 }   -- non-empty integer arrays
{ @String | length(@String.0) <= 255 }         -- strings of at most 255 characters
```

### 2.6.1 The Decidable Fragment

Refinement predicates MUST be drawn from the following decidable logic fragment:

**Allowed in predicates:**
- Integer literals and slot references of numeric type
- Arithmetic: `+`, `-`, `*` (where at least one operand of `*` is a literal)
- Comparison: `==`, `!=`, `<`, `>`, `<=`, `>=`
- Boolean connectives: `&&`, `||`, `!`, `==>`  (where `==>` is logical implication)
- `array_length(@Array<T>.n)` — array length
- `length(@String.n)` — string length
- `true`, `false`
- Parenthesised sub-expressions

**Not allowed in predicates (static verification):**
- Function calls (except `length`)
- Non-linear arithmetic (e.g., `@Int.0 * @Int.1`)
- Quantifiers (`forall`, `exists`)
- Array element access
- String content inspection

This fragment corresponds to quantifier-free linear integer arithmetic (QF_LIA) extended with uninterpreted length functions. It is decidable, and Z3 handles it efficiently.

Predicates outside this fragment may appear in contracts (Chapter 6) where they are handled by Tier 2 (guided verification) or Tier 3 (runtime fallback).

### 2.6.2 Refinement Subtyping

A refined type `{ @T | P }` is a subtype of `{ @T | Q }` if and only if the implication `P ==> Q` is valid (holds for all values). This is checked by the SMT solver.

A refined type `{ @T | P }` is always a subtype of the base type `T` (since `P ==> true`).

The base type `T` is equivalent to `{ @T | true }`.

### 2.6.3 Type Aliases with Refinements

Type aliases can capture commonly used refinements:

```
type PosInt = { @Int | @Int.0 > 0 };
type NonEmptyArray<T> = { @Array<T> | array_length(@Array<T>.0) > 0 };
type Percentage = { @Int | @Int.0 >= 0 && @Int.0 <= 100 };
type Byte = { @Int | @Int.0 >= 0 && @Int.0 <= 255 };
```

Type aliases are transparent for refinement subtyping: `PosInt` and `{ @Int | @Int.0 > 0 }` are the same type for subtyping purposes.

However, type aliases create distinct namespaces for slot references (see Chapter 3): `@PosInt.0` counts only `PosInt` bindings, not `Int` bindings.

### 2.6.4 Predicate Verification

The type checker treats a refined type as its base for assignability (it permits a base value to flow into a refined slot) and **defers the predicate proof to verification**. The verifier discharges the predicate as a Tier-1 proof obligation at every site where a value narrows into a refined slot:

- `let @PosInt = ...` — let bindings
- `f(...)` where a formal is refined — call arguments
- `Ctor(...)` where a field is refined — constructor fields
- effect-operation arguments
- `match v { @PosInt -> ... }` — match bindings
- tuple destructure components
- the function's **return position** when the declared return type is refined

A refined **parameter** is, conversely, *assumed* to satisfy its predicate inside the body — sound precisely because every call site discharges the obligation. If the solver finds inputs violating the predicate, verification fails with error `E505` and a counterexample. A discharge proved from the surrounding `requires` clauses, path conditions, or an already-refined source carries no runtime cost.

An obligation drops to Tier 3 — reported as an `E506` warning rather than silently accepted — in two cases: (1) the predicate uses a construct outside the decidable fragment (§2.6.1); or (2) the refinement is over a non-primitive base, such as `{ @Array<Int> | array_length(...) > 0 }`, which the predicate translator does not lower — only primitive bases (`@Int`, `@Nat`, `@Bool`, `@Float64`, `@String`) have their binder substituted, so a non-primitive base is Tier 3 even when its predicate (here `array_length(...) > 0`) is itself in the fragment.

### 2.6.5 Runtime Guards

A refinement predicate is also guarded at **runtime**: the compiler emits a predicate check at every function boundary — a refined parameter is checked at entry and a refined return at exit — that traps (via the contract-failure channel) if the value violates the predicate. So even a program compiled *without* `vera verify` rejects a refinement-violating value rather than silently accepting it; for example, calling `clamp_percent(@Int)` whose body returns a value outside `0..100` traps with a refinement-violation diagnostic. This holds at a `public`/FFI entry point too, where an untrusted caller cannot bypass the callee's entry guard. A call argument is covered by that guard, so the boundary checks compose to cover every narrowing whose result is consumed across a boundary; a purely internal narrowing (a `let`, match bind, or destructure that never crosses a boundary) is Tier-3-static-only — surfaced as an `E506` warning, not silently accepted.

This covers refinements over a **non-primitive base** too (e.g. `{ @Array<Int> | array_length(@Array<Int>.0) > 0 }`): although the predicate translator does not lower the non-primitive `@Array` binder — so the predicate is Tier 3 *statically* (§2.6.4) even though `array_length(...) > 0` is itself in the decidable fragment — codegen compiles it directly to WebAssembly, so an empty array passed into a `@NonEmptyArray` parameter traps at run time.

The guard is *defense in depth* for the unverified path: a `vera verify`-clean program proves the predicate statically, so the runtime guard is never reached.

## 2.7 Parametric Polymorphism

Functions and data types may be parameterised by type variables:

```
private forall<A, B> fn swap(@Tuple<A, B> -> @Tuple<B, A>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Tuple(@B.0, @A.0)
}
```

Type variables:
- MUST be uppercase single letters or short uppercase identifiers: `A`, `B`, `T`, `Key`, `Val`
- Are introduced by `forall<...>` before the function keyword or in a data type declaration
- Are scoped to the declaration in which they appear
- Are universally quantified: the function must work for all types

### 2.7.1 Type Constraints

Type variables may be constrained using ability constraints:

```
private forall<T where Ord<T>> fn sort(@Array<T> -> @Array<T>)
```

Constraints are declared in the `forall` clause using `where`. Each constraint binds a type variable to an ability, requiring that any concrete type substituted for that variable satisfies the ability. See Section 9.8 for ability declarations and built-in abilities.

## 2.8 Subtyping Rules

Vera has minimal subtyping. The complete subtyping relation is:

1. **Reflexivity**: `T <: T` for all types `T`.
2. **Refinement subtyping**: `{ @T | P } <: { @T | Q }` if `P ==> Q` is valid.
3. **Refinement to base**: `{ @T | P } <: T`.
4. **Never subtyping**: `Never <: T` for all types `T`.
5. **No other subtyping**: there is no structural subtyping, no implicit numeric conversions, no covariance/contravariance on compound types.

> **Implementation note:** The type checker additionally permits `Int <: Nat` (the reverse of the `Nat <: Int` relationship in Section 2.2.1) to allow functions that compute a natural number from integer inputs without explicit conversion. Non-negativity is not enforced by the type checker alone — the contract verifier enforces the `>= 0` constraint via Z3. Code that passes `vera check` but fails `vera verify` on a `Nat` return type indicates that the verifier could not prove the result is non-negative.

This means `Array<PosInt>` is NOT a subtype of `Array<Int>`. Converting between them requires an explicit mapping.

## 2.9 Type Equality

Two types are equal if and only if they have the same structure after resolving type aliases. Refinement type equality uses logical equivalence: `{ @T | P }` equals `{ @T | Q }` if and only if `P <==> Q` is valid.
