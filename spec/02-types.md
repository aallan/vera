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

`Nat` is a refinement of `Int`: it is equivalent to `{ @Int | @Int.0 >= 0 }`. The compiler recognises `Nat` as a built-in alias and optimises accordingly, but semantically `Nat <: Int` via refinement subtyping.

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

Arrays are fixed-size, homogeneous, immutable ordered collections. Array length is known at runtime and accessible via the `length` built-in.

Array elements are accessed by integer index: `@Array<Int>.0[3]` accesses the element at index 3 of the nearest `Array<Int>` binding.

### 2.3.3 Option Type

```
Option<Int>
```

`Option<T>` is a built-in algebraic data type equivalent to:

```
data Option<T> {
  Some(@T),
  None,
}
```

It represents a value that may or may not be present.

### 2.3.4 Result Type

```
Result<Int, String>
```

`Result<T, E>` is a built-in algebraic data type equivalent to:

```
data Result<T, E> {
  Ok(@T),
  Err(@E),
}
```

It represents a computation that may succeed with a value of type `T` or fail with an error of type `E`.

## 2.4 Algebraic Data Types (ADTs)

User-defined algebraic data types are declared with the `data` keyword:

```
data List<T> {
  Cons(@T, @List<T>),
  Nil,
}
```

```
data Tree<T> {
  Leaf(@T),
  Node(@Tree<T>, @Tree<T>),
}
```

```
data Color {
  Red,
  Green,
  Blue,
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

An ADT may declare an invariant that all values must satisfy:

```
data SortedList<T>
  invariant(is_sorted(@SortedList<T>.0))
{
  SCons(@T, @SortedList<T>),
  SNil,
}
```

The invariant is checked by the contract verifier at every construction site.

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
{ @Array<Int> | length(@Array<Int>.0) > 0 }   -- non-empty integer arrays
{ @String | length(@String.0) <= 255 }         -- strings of at most 255 characters
```

### 2.6.1 The Decidable Fragment

Refinement predicates MUST be drawn from the following decidable logic fragment:

**Allowed in predicates:**
- Integer literals and slot references of numeric type
- Arithmetic: `+`, `-`, `*` (where at least one operand of `*` is a literal)
- Comparison: `==`, `!=`, `<`, `>`, `<=`, `>=`
- Boolean connectives: `&&`, `||`, `!`, `==>`  (where `==>` is logical implication)
- `length(@Array<T>.n)` — array length
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
type PosInt = { @Int | @Int.0 > 0 }
type NonEmptyArray<T> = { @Array<T> | length(@Array<T>.0) > 0 }
type Percentage = { @Int | @Int.0 >= 0 && @Int.0 <= 100 }
type Byte = { @Int | @Int.0 >= 0 && @Int.0 <= 255 }
```

Type aliases are transparent for refinement subtyping: `PosInt` and `{ @Int | @Int.0 > 0 }` are the same type for subtyping purposes.

However, type aliases create distinct namespaces for slot references (see Chapter 3): `@PosInt.0` counts only `PosInt` bindings, not `Int` bindings.

## 2.7 Parametric Polymorphism

Functions and data types may be parameterised by type variables:

```
forall<A, B> fn swap(@Tuple<A, B> -> @Tuple<B, A>)
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

Type variables may be constrained (future extension, not in v0.1):

```
forall<T where Ord<T>> fn sort(@Array<T> -> @Array<T>)
```

For v0.1, type variables are unconstrained.

## 2.8 Subtyping Rules

Vera has minimal subtyping. The complete subtyping relation is:

1. **Reflexivity**: `T <: T` for all types `T`.
2. **Refinement subtyping**: `{ @T | P } <: { @T | Q }` if `P ==> Q` is valid.
3. **Refinement to base**: `{ @T | P } <: T`.
4. **Never subtyping**: `Never <: T` for all types `T`.
5. **No other subtyping**: there is no structural subtyping, no implicit numeric conversions, no covariance/contravariance on compound types.

This means `Array<PosInt>` is NOT a subtype of `Array<Int>`. Converting between them requires an explicit mapping.

## 2.9 Type Equality

Two types are equal if and only if they have the same structure after resolving type aliases. Refinement type equality uses logical equivalence: `{ @T | P }` equals `{ @T | Q }` if and only if `P <==> Q` is valid.
