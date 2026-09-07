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

- **`Nat <: Int` is a formal subtyping rule** at the *type* level. It follows from refinement subtyping (§2.6.2, §2.8 rule 3): `Nat` is `{ @Int | @Int.0 >= 0 }`, and a refined type is always a subtype of its base.  Use a `@Nat` anywhere `@Int` is expected — no `nat_to_int` call, no source-level conversion.  At the *value* level the widening is **not** a no-op, however: `@Nat` is represented as an unsigned 64-bit integer (u64) and `@Int` as a signed one (i64), so a `@Nat` in `(i64.MAX, u64.MAX]` bit-reinterprets to a *negative* `@Int` when widened (`u64.MAX` → `-1`).  The compiler therefore emits a `<= i64.MAX` coercion obligation (**E530**) — the widening dual of the `Int -> Nat` narrowing relaxation below: discharged at Tier 1 when the value is provably in range, otherwise either guarded by a runtime trap (at the return, `let`, call-argument, concrete constructor-field, ADT sub-pattern, match-binding, array-element, tuple component, heterogeneous `if`/`match` arm, and closure argument/return sites) or — where code generation cannot guard the coercion (the generic-instantiated `@Int` *field* coercion, erased to i64 with no per-field metadata) — disclosed as an unguarded **E531** warning.
- **`Int -> Nat` is not a formal subtyping rule** (it is explicitly excluded by §2.8 rule 5: "no other subtyping").  Instead, the type checker permits the flow as a **verifier-mediated relaxation**: the narrowing requires `@Int.0 >= 0`, and the type checker emits a verification obligation that the contract verifier (Tier 1) discharges via Z3 from the surrounding context (`requires`, `if` conditions, prior `assert`s).  If the obligation cannot be discharged statically, it falls to a runtime check (Tier 3).  The implementation note in §2.8 documents this relaxation alongside the formal rules.

The distinction matters because of §0.2.2 ("no implicit behaviour"): `Nat <: Int` is a true formal subtyping rule consistent with the principle (it's a logical consequence of refinement subtyping, not an implicit conversion); `Int -> Nat` is a verifier-mediated convenience that's syntactically silent but semantically verified — the verifier is the explicit check, not the syntax.

The practical implication for user code: do **not** insert `nat_to_int` defensively when calling a built-in that returns `@Int` (e.g. `array_length`) into a `@Nat` position.  The conversion is verifier-mediated and either statically discharged, guarded at runtime, or (at the one generic-instantiated `@Int`-field component site code generation cannot guard) flagged by an `E531` warning — `nat_to_int` is needed only when the value is genuinely allowed to be negative.  Conversely, a `@Nat` whose value can exceed `i64.MAX` and is widened into an `@Int` position should be range-constrained (`requires(... <= 9223372036854775807)`) so the `E530` coercion obligation discharges at Tier 1 rather than relying on the runtime trap.

`Never` is the type of expressions that never produce a value (e.g., functions that always diverge or branches that are statically unreachable). `Never` is a subtype of every type.

### 2.2.2 Zero-size types are declaration-only

`Unit` is zero-size: a `Unit` value occupies no bytes and compiles to no runtime local. A `Unit`-typed binding may be **declared** — a `@Unit` function parameter or a handler clause's `@Unit` operation parameter erases cleanly from the ABI — but it cannot be **materialized**:

- Reading a zero-size slot (`@Unit.0`) is a checker error (**E182**) in every binding form — function parameters, handler-clause operation parameters, and closure parameters alike. The unit value has exactly one spelling: the literal `()`.
- A `let` binding of a zero-size type (`let @Unit = put(5);`) is a checker error (**E183**): the binding could never be read, and sequencing is the expression statement's job (`put(5);`).
- An array of a zero-size element type is a checker error (**E135**), as are a `Map` whose key or value type is zero-size and a `Set` of a zero-size element type — container entries are raw, unboxed values with no representation to store or load. Instantiating a type parameter that is *read* at `Unit` is a checker error (**E206**, §2.7).

These rules key on representation, not on the name `Unit`: a `Future` transparently wrapping a zero-size payload (`Future<Unit>`) is rejected the same way, while boxed shapes with a real runtime representation (`Option<Unit>` — tag plus pointer) are ordinary values.

The legal side of the line — a `@Unit` parameter declared and satisfied with the unit literal:

```vera
private fn poll(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  7
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  poll(())
}
```

`poll` declares a `@Unit` parameter (legal — it erases from the ABI) and the call site supplies the literal `()`; neither body ever reads a `@Unit` slot.

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
4. ADTs may be recursive (a constructor may reference the type being defined), but the recursion MUST be **regular**. In a declaration `N<P…>`, every occurrence of `N` — or of any type mutually recursive with it — MUST supply each type argument as either a **bare parameter of `N`**, or a type that does **not mention any parameter of `N`** at all. An argument that wraps a parameter inside another type constructor is rejected with **E129**.

    `data List<T> { Cons(T, List<T>), Nil }` passes the parameter along unchanged. `data Expr<T> { Lit(T), Add(Expr<Int>, Expr<Int>) }` uses a closed argument, and `data Decl { D(Body<Int>) }` with `data Body<T> { B(T, Decl) }` mixes the two across a mutually recursive pair — all regular. `data Nest<T> { N(Nest<Option<T>>), Z }` is not: `Option<T>` wraps the parameter, so each level's argument is larger than the last and the chain of instantiations — `Nest<Int>`, `Nest<Option<Int>>`, `Nest<Option<Option<Int>>>`, … — never repeats. Nothing that reasons over the type structurally can terminate on one: equality, code generation and verification each need the set of instantiations to be finite.

    An occurrence of the declaration's **own** name must additionally keep its parameters in their original positions: `data R<A, B> { CR(R<B, A>), ZR }` is rejected. A permutation does stay finite, but it multiplies — five parameters reach 610 distinct instantiations — and the rule this section states is reuse unchanged and in order. Across a mutually recursive pair there is no such ordering to keep, since each member's parameters are its own.

    The condition is on the *arguments*, so it applies wherever a group member occurs, including inside a carrier's type argument: `data Av<T> { CV(Array<Av<Option<T>>>), ZV }` is rejected, while `Array<Av<T>>` is regular.
5. ADTs may be parameterised by type variables.
6. Type parameters are introduced by `<A, B, ...>` after the type name.
7. Each constructor is a distinct variant. Constructors with fields carry positional data.
8. ADTs are immutable. There is no way to modify a value after construction.

### 2.4.1 ADT Invariants

> **Status: Not yet implemented.** The `invariant(...)` clause on `data` declarations is specified here but is not currently working in the reference compiler — every documented form fails with `[E130] no <DataName> bindings in scope`, because the slot environment for the invariant predicate is not yet wired up.  Tracked in [#686](https://github.com/aallan/vera/issues/686) (successor to the now-closed #560 — that earlier issue was about removing the broken spec examples; the feature implementation is the remaining work).  Until the implementation lands, refinement types (Section 2.6) are the working alternative for expressing constraints on data values.

An ADT may declare an invariant that all values must satisfy:

<!-- vera:skip-check category="INCOMPLETE" reason="is_sorted in SortedList invariant" -->
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

**Predicate well-formedness.** The predicate `P` is type-checked exactly like a contract predicate (Chapter 6): it MUST evaluate to `Bool`, and its operands are typed by the ordinary expression rules of Chapter 4. A predicate that is not `Bool` — a bare value such as `{ @Int | @Int.0 }` — is rejected with error `E126` (the refinement counterpart of `E123` for a non-`Bool` `requires()` and `E124` for a non-`Bool` `ensures()`), and an ill-typed predicate such as `{ @String | @String.0 < 3 }` is rejected by the offending operator's own rule (here `E142`, comparing a `String` with an `Int`). The predicate binder `@T.0` is the sole slot in scope, bound to the base type `T` — the predicate is checked in an isolated scope, so it cannot reference bindings from a surrounding function body or handler clause (any other slot reference is `E130`), regardless of where the refinement is written.

This rule applies at **every** position where a refinement type can be written: type-alias bodies, function and anonymous-function signatures, constructor fields, effect and ability operation signatures, `let` and destructure annotations, `match` binding patterns, `forall`/`exists` binder types, handler state and clause-parameter annotations, and `with`-clause state updates — including refinements nested inside type arguments (`Array<{ @Int | P }>`) or function-type components.

One rule is relaxed inside a refinement predicate over a `@Byte` base: an integer literal compared against a `Byte`-typed operand is typed against `Byte` rather than `Nat`, so `{ @Byte | @Byte.0 < 10 }` is well-typed. This is literal-typing-from-context (the same rule by which the literal `7` satisfies a `@Byte` parameter, §4.2), not an implicit numeric coercion (§0.2.2) — and the comparison has a defined `i32` runtime-guard lowering (§11). In a general expression a `@Byte`-versus-integer-literal comparison remains `E142`. The allowance is keyed to the predicate's **own base** (resolved through aliases): a `Byte`-typed operand inside an `@Int`-based refinement — e.g. `{ @Int | b(@Int.0) < 10 }` where `b` returns `@Byte` — is `E142`, and a predicate nested inside another (through a `forall`/`exists` binder type) uses its own base, not the enclosing predicate's. The allowance covers comparison only: `@Byte` arithmetic inside a predicate (`{ @Byte | @Byte.0 + 1 < 10 }`) is rejected with `E140`, exactly as in any other expression — `Byte` is excluded from arithmetic at type-check time.

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

However, at the **head** of a slot name a type alias creates a distinct namespace for slot references (see §3.8): `@PosInt.0` counts only `PosInt` bindings, not `Int` bindings. Inside a type **argument** the alias resolves instead, so under `type Cnt = Int` a parameter written `@Option<Cnt>` binds `Option<Int>` and is referenced `@Option<Int>.0` (§3.8.1).

A type alias MUST eventually resolve to a concrete type — the chain of alias definitions MUST be acyclic. The requirement is structural over every representation-expanding position of the definition: the target's own name, references nested inside type arguments at any depth (`type F = Future<F>`, `type L = Array<L>`, `type A = Future<Array<B>>`) — including arguments the generic alias does not use — and refinement bases. A cyclic alias is rejected with error `E132`. (Recursion *is* permitted where an indirection bounds the expansion: through an `ADT` declared via `data` — a heap pointer — and through function-type parameter or return positions — a function value is a table index, so `type FA = fn(FA -> Int) effects(pure);` is accepted.)

### 2.6.4 Predicate Verification

The type checker treats a refined type as its base for assignability (it permits a base value to flow into a refined slot) and **defers the predicate proof to verification**. The verifier discharges the predicate as a Tier-1 proof obligation at every site where a value narrows into a refined slot:

- `let @PosInt = ...` — let bindings
- `f(...)` where a formal is refined — call arguments
- a refinement written on a **component** of a type — an ADT payload, a tuple component — at every position that gives a value that type: a call argument, a closure argument (`apply_fn`), a `let` binder, a constructor field, a tuple component, an effect-operation argument, and the function's return position
- `Ctor(...)` where a field is refined — constructor fields
- effect-operation arguments
- `match v { @PosInt -> ... }` — match bindings
- tuple destructure components
- the function's **return position** when the declared return type is refined

A refined **parameter** is, conversely, *assumed* to satisfy its predicate inside the body — sound precisely because every call site discharges the obligation. If the solver finds inputs violating the predicate, verification fails with error `E505` and a counterexample. A discharge proved from the surrounding `requires` clauses, path conditions, or an already-refined source carries no runtime cost.

That assumption extends to refinements written *inside* the parameter's type: a `consume(@Option<PosInt>)` reasons about its payload as `> 0` without re-deriving it, and it is verified once for every caller, so the caller must establish the payload. The obligation is therefore raised at **every position that gives a value a type whose components are refined** — the argument (a closure's as well as a named call's), a `let` binder, a constructor field, a tuple component, an effect-operation argument, and the function's own return slot. Covering all of them is what makes the rule closed rather than local: a value cannot acquire the declared type anywhere without being asked for it, so no position can publish a component invariant it did not establish, and a chain of wrappers cannot launder one. The single exclusion is a value **constructed** here, whose own construction site carries the obligation; it holds only when every value-producing leaf constructs, since a branch join with one constructed arm establishes nothing about the other.

The discharge is a proof obligation like any other, never a comparison of declared types. A value declared `Option<PosInt>` may be assumed to carry that payload *because* every position above obligates it, so the source's own component invariants are legitimate premises — but the goal is still put to the solver, and a `verified` means it was discharged. Two cases have nothing to grant. A source type that does not carry the refinement at all — `Option<Int>`, which the checker accepts for an `Option<PosInt>` parameter, since a refinement is erased for compatibility (§2.6.2) — leaves the obligation to be proved or refuted on its merits. A source whose producer this run DISCLOSED (its own obligation for that type resolved neither proved nor guarded) had nothing established either, so the premise is withheld and a goal that holds only from it is reported Tier 3 rather than proved.

An obligation drops to Tier 3 — reported as an `E506` warning rather than silently accepted — whenever the verifier reaches no verdict. The warning names which of the following applies, because they call for different responses:

1. **The value being narrowed does not translate.** It uses a construct outside the decidable fragment (§2.6.1), so no term reaches the predicate. A value the verifier models only opaquely falls here too: an effect-operation result, a closure body (never entered), or a scrutinee or destructure source it cannot project to the field or component the predicate is about.
2. **The refinement's base is one the verifier does not model.** Only `@Int`, `@Nat`, `@Bool`, `@Float64` and `@String` have their binder substituted, so the predicate is never given a value to reason about. This is a property of the *base*, not of the predicate, which may be perfectly decidable: `{ @Array<Int> | array_length(...) > 0 }` is Tier 3 although `array_length(...) > 0` is in the fragment, and so is `{ @Byte | @Byte.0 < 10 }` although `@Byte` is a primitive (§2.1) and the comparison is well-typed by the literal-typing-from-context relaxation §2.6 states for a `@Byte` base (§4.2). Codegen lowers such a predicate regardless, so a boundary narrowing is still checked at run time (§2.6.5). A **concrete** narrowing is decided whatever the base, because a literal needs no model: the value is substituted into the predicate and evaluated, so narrowing `200` into `{ @Byte | @Byte.0 < 10 }` is an `E505` naming the value and narrowing `5` is a Tier-1 proof. Only a narrowing that does not reduce to a truth value falls to Tier 3 here — a symbolic value, or a predicate whose operands the verifier models by something other than evaluation.
3. **The predicate uses a construct outside the decidable fragment** (§2.6.1), over a base that is modelled.
4. **The solver returns no verdict** — it declines to decide, or its only countermodel ranges over an opaque effect-operation stand-in and therefore refutes nothing the effect can actually produce. Neither is a refutation, so neither reports `E505`.

### 2.6.5 Runtime Guards

A refinement predicate is also guarded at **runtime**: the compiler emits a predicate check at every function boundary — a refined parameter is checked at entry and a refined return at exit — that traps (via the contract-failure channel) if the value violates the predicate. So even a program compiled *without* `vera verify` rejects a refinement-violating value rather than silently accepting it; for example, calling `clamp_percent(@Int)` whose body returns a value outside `0..100` traps with a refinement-violation diagnostic. This holds at a `public`/FFI entry point too, where an untrusted caller cannot bypass the callee's entry guard. A call argument is covered by that guard, so the boundary checks compose to cover every narrowing whose result is consumed across a boundary; a purely internal narrowing (a `let`, match bind, destructure, constructor field, ADT sub-pattern bind, or a *user-declared* effect operation's argument that never crosses a boundary) is Tier-3-static-only — surfaced as an `E506` warning, not silently accepted.

The boundary guard decomposes the parameter's own refinement and its **tuple** components, and stops there — and only at a function boundary, so a constructor field, a tuple component at construction, and an effect operation's argument are guarded at none of it. So a refinement written on a tuple component — `@Tuple<PosInt, Int>` — is checked at entry like any other boundary predicate, while one written on an **ADT payload** (`@Option<PosInt>`) or an **array element** (`@Array<PosInt>`) is checked at no boundary at all. An undischarged §2.6.4 component obligation is therefore reported against what the guard actually covers: a guarded Tier 3 for a tuple component, and an unguarded `E506` — counted in no tier — for the payload and element positions.

The built-in `Exn` effect's `throw` payload is guarded, not internal. `throw(v)` narrows `v` into the `Exn<E>` payload and the value leaves the throwing function, but it crosses no *function* boundary on the way, so none of the composing checks above reaches it: the compiler emits the predicate check at the `throw` itself, and a violating payload traps there rather than arriving in a handler clause that has already assumed the predicate.

This covers refinements over **a base the verifier does not model** too — `{ @Array<Int> | array_length(@Array<Int>.0) > 0 }`, and equally `{ @Byte | @Byte.0 < 10 }`. The predicate translator does not substitute such a binder, so a *symbolic* narrowing is Tier 3 *statically* (§2.6.4, cause 2) even where the predicate is itself in the decidable fragment; codegen compiles it directly to WebAssembly regardless, so an empty array passed into a `@NonEmptyArray` parameter — or a `@Byte` computed at run time and passed into a `@SmallByte` one — traps at run time. A literal argument does not reach the guard: it is decided statically (§2.6.4, cause 2), so `small(200)` is rejected before it can run.

The guard is *defense in depth* for the unverified path: a `vera verify`-clean program proves the predicate statically, so the runtime guard is never reached.

## 2.7 Parametric Polymorphism

Functions and data types may be parameterised by type variables:

<!-- vera:skip-check category="INCOMPLETE" reason="forall<A,B> fn swap uses Tuple" -->
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

<!-- vera:skip-parse category="FUTURE" reason="forall<T where Ord<T>> fn sort" -->
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

![The complete subtyping relation: Never below everything, refinement subtyping when one predicate implies the other, refinement-to-base, reflexivity — and nothing else. The checker additionally permits Int where Nat is expected; the verifier enforces the non-negativity proof.](../assets/diagrams/subtyping-lattice.svg)

## 2.9 Type Equality

Two types are equal if and only if they have the same structure after resolving type aliases. Refinement type equality uses logical equivalence: `{ @T | P }` equals `{ @T | Q }` if and only if `P <==> Q` is valid.
