# Chapter 6: Contracts

## 6.1 Overview

Contracts are the mechanism by which Vera ensures that code is checkable. Every function declares what it requires from its callers and what it guarantees to them. The compiler verifies these contracts statically where possible and inserts runtime checks where it cannot.

Contracts serve as executable specifications. They are the source of truth about what a function does — the implementation must satisfy them.

## 6.2 Contract Forms

### 6.2.1 Preconditions (`requires`)

A precondition is a predicate that MUST hold when the function is called. It is the caller's responsibility to ensure preconditions are met.

```
public fn safe_divide(@Int, @Int -> @Int)
  requires(@Int.1 != 0)
  ensures(@Int.result == @Int.0 / @Int.1)
  effects(pure)
{
  @Int.0 / @Int.1
}
```

At every call site of `safe_divide`, the compiler verifies that the second argument is non-zero. If it cannot prove this statically, it inserts a runtime check.

### 6.2.2 Postconditions (`ensures`)

A postcondition is a predicate that MUST hold when the function returns. It is the function's responsibility to ensure postconditions are met.

```
public fn absolute_value(@Int -> @Nat)
  requires(true)
  ensures(@Nat.result >= 0)
  ensures(@Nat.result == @Int.0 || @Nat.result == -@Int.0)
  effects(pure)
{
  if @Int.0 >= 0 then {
    @Int.0
  } else {
    -@Int.0
  }
}
```

The special reference `@T.result` (where `T` is the return type) refers to the function's return value within `ensures` clauses.

### 6.2.3 Invariants (`invariant`)

An invariant is a predicate declared on a data type that MUST hold for all values of that type:

```
private data SortedArray
  invariant(is_sorted_impl(@SortedArray.0))
{
  Mk(Array<Int>)
}
```

The compiler verifies the invariant at every construction site. If a value of type `SortedArray` exists, the invariant holds.

Invariants on built-in types are expressed as refinement types (Chapter 2) rather than as `invariant` declarations.

### 6.2.4 Termination Measures (`decreases`)

A `decreases` clause specifies an expression that strictly decreases on each recursive call (see Chapter 5, Section 5.6.1):

```
private fn sum_to(@Nat -> @Nat)
  requires(true)
  ensures(@Nat.result == @Nat.0 * (@Nat.0 + 1) / 2)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 == 0 then {
    0
  } else {
    @Nat.0 + sum_to(@Nat.0 - 1)
  }
}
```

### 6.2.5 Assertions (`assert`)

An assertion is a predicate that MUST hold at the point where it appears in the function body:

```
fn(@Int, @Int -> @Int)
  requires(@Int.0 > 0 && @Int.1 > 0)
  ensures(@Int.result > @Int.0)
  effects(pure)
{
  let @Int = @Int.0 + @Int.1;
  assert(@Int.0 > @Int.1);     -- compiler verifies this holds
  @Int.0
}
```

Assertions serve two purposes:
1. They document intermediate invariants for human readers.
2. They provide "stepping stones" for the verifier, breaking complex proofs into smaller steps.

### 6.2.6 Assumptions (`assume`)

An assumption is a predicate that the compiler MUST accept as true without proof:

```
fn(@Int -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  let @Int = external_library_call(@Int.0);
  assume(@Int.0 > 0);   -- trust that the library returns positive
  @Int.0
}
```

The compiler MUST emit a warning for every `assume` statement:

```
WARNING: unverified assumption at line 7: @Int.0 > 0
```

`assume` is an escape hatch. It is unsound — if the assumption is false, the program may have undefined behaviour. It should be used only when interfacing with verified external code or when a proof is beyond the verifier's capability.

## 6.3 Contract Predicate Language

Contract predicates use the same expression syntax as Vera programs, with the following restrictions and extensions.

### 6.3.1 Allowed in All Contracts

Everything allowed in the decidable fragment (Chapter 2, Section 2.6.1):
- Integer literals and slot references
- Linear arithmetic (`+`, `-`, `*` with literal multiplier)
- Comparisons (`==`, `!=`, `<`, `>`, `<=`, `>=`)
- Boolean connectives (`&&`, `||`, `!`)
- `array_length()` on arrays, `string_length()` on strings
- Logical implication (`==>`)
- `true`, `false`

### 6.3.2 Additionally Allowed in Contracts (Tier 2)

> **Status: Not yet implemented.** Tier 2 (Z3-guided) is specified here but not implemented in the reference compiler. Tracked in [#427](https://github.com/aallan/vera/issues/427). Contracts using these constructs currently fall to Tier 3 (runtime check).

Beyond the decidable fragment, contracts may also use:
- Calls to `pure` functions that have their own contracts
- Quantified expressions (limited, see below)
- Array element access (`@Array<Int>.0[@Nat.0]`)
- The `@T.result` reference (in `ensures` only)
- Conditional expressions (`if ... then ... else ...`)

### 6.3.3 Quantified Expressions

Vera supports bounded quantification in contracts:

```
forall(@Nat, array_length(@Array<Int>.0), fn(@Nat -> @Bool) effects(pure) {
  @Array<Int>.0[@Nat.0] > 0
})
```

This reads: "for all `@Nat.0` in `[0, array_length(@Array<Int>.0))`, the array element at that index is positive."

The syntax is:

```
forall(@IndexType, @BoundExpr, @PredicateFn)
```

Where:
- `@IndexType` is the type of the bound variable (must be `Nat` or `Int`)
- `@BoundExpr` is the exclusive upper bound (inclusive lower bound is always 0)
- `@PredicateFn` is an anonymous function returning `Bool`

Bounded quantification is decidable for finite bounds and is handled by Z3 via finite unrolling for small bounds or inductive reasoning for symbolic bounds.

The `exists` quantifier uses the same syntax and asserts that at least one value in the range satisfies the predicate:

```
exists(@Nat, array_length(@Array<Int>.0), fn(@Nat -> @Bool) effects(pure) {
  @Array<Int>.0[@Nat.0] == 0
})
```

This reads: "there exists some `@Nat.0` in `[0, array_length(@Array<Int>.0))` such that the array element at that index is zero."

The syntax is:

```
exists(@IndexType, @BoundExpr, @PredicateFn)
```

Where the parameters have the same meaning as for `forall`. Bounded existential quantification is handled by Z3 via finite unrolling for small bounds or Skolemization for symbolic bounds.

## 6.4 Verification Architecture

### 6.4.1 Verification Condition (VC) Generation

For each function, the compiler generates verification conditions — logical formulas that, if valid, imply the function satisfies its contract.

The VC generation follows a weakest-precondition calculus:

1. Start with the postcondition.
2. Traverse the function body backward, computing the weakest precondition at each step.
3. At the function entry, check that the declared precondition implies the computed weakest precondition.

For each statement type:

| Statement | WP transformation |
|-----------|-------------------|
| `let @T = expr;` | Substitute `expr` for `@T.0` in the current WP |
| `if @Bool.0 then { e1 } else { e2 }` | `(@Bool.0 ==> WP(e1)) && (!@Bool.0 ==> WP(e2))` |
| `assert(P)` | `P && WP(rest)` |
| `assume(P)` | `P ==> WP(rest)` |
| Function call `f(args)` | Verify `f`'s precondition holds with `args`, then assume `f`'s postcondition |
| `match` | One VC per arm, conjoined |

### 6.4.2 Call Site Verification

At each call site, the compiler generates two VCs:

1. **Precondition check**: the caller's current context implies the callee's precondition (with actual arguments substituted).
2. **Postcondition assumption**: after the call, the callee's postcondition (with actual arguments and return value substituted) is assumed to hold.

This means the verifier is modular: each function is verified independently, assuming its callees satisfy their contracts.

### 6.4.3 SMT Solver Integration

VCs are translated to SMT-LIB format and solved by Z3:

1. **Tier 1 VCs** (decidable fragment): sent directly to Z3. Z3 returns `unsat` (VC is valid), `sat` (VC is invalid, with counterexample), or `unknown`.
2. **Tier 2 VCs** (with hints, not yet implemented — [#427](https://github.com/aallan/vera/issues/427)): the compiler provides additional axioms from `assert` statements and lemma functions. Z3 has a timeout of 10 seconds. Currently, contracts requiring hints fall to Tier 3.
3. **Tier 3 fallback**: if Z3 returns `unknown` or times out, the VC is compiled as a runtime check.

### 6.4.4 Counterexample Reporting

When Z3 finds a counterexample (a VC is invalid), the compiler reports the specific input values that violate the contract:

```
ERROR: Contract violation in function foo (line 5)

    private fn foo(@Int -> @Int)
      requires(true)
      ensures(@Int.result > @Int.0)
      ...

  Postcondition: @Int.result > @Int.0
  Counterexample:
    @Int.0 = 0
    @Int.result = 0

  The postcondition @Int.result > @Int.0 does not hold when @Int.0 = 0.
  Consider strengthening the precondition (e.g., requires(@Int.0 > 0))
  or weakening the postcondition (e.g., ensures(@Int.result >= @Int.0)).
```

## 6.5 Runtime Contract Checking

When a contract cannot be verified statically (Tier 3), the compiler inserts a runtime check:

```
-- For a requires clause:
if !precondition {
  trap("Precondition violation in function_name: requires(@Int.0 > 0)")
}

-- For an ensures clause:
let @ReturnType = body_result;
if !postcondition {
  trap("Postcondition violation in function_name: ensures(@Int.result > 0)")
}
@ReturnType.0
```

Runtime contract violations cause a WASM trap with a diagnostic message.

The compiler MUST emit a warning for each runtime-checked contract:

```
WARNING: Cannot statically verify contract at line 3: requires(@Int.0 > 0)
  Reason: Z3 timeout after 10s
  Inserting runtime check.
```

## 6.6 Lemma Functions

> **Status: Not yet implemented.** Lemma functions are part of Tier 2 verification ([#427](https://github.com/aallan/vera/issues/427)) and are not yet supported by the reference compiler.

A lemma function is a `pure` function whose sole purpose is to establish a fact for the verifier. Its body must type-check and its contract must verify, but it is never called at runtime:

```
private fn lemma_sum_positive(@Nat, @Nat -> @Unit)
  requires(@Nat.0 > 0 && @Nat.1 > 0)
  ensures(@Nat.0 + @Nat.1 > @Nat.0)
  effects(pure)
{
  ()
}
```

Lemma functions are declared with the same syntax as regular functions. The compiler recognises that a function whose body is `()` and whose return type is `Unit` with non-trivial contracts is a lemma, and does not emit code for it.

To use a lemma, call it in an `assert`:

```
assert(lemma_sum_positive(@Nat.0, @Nat.1) == ());
```

After this point, the verifier knows that `@Nat.0 + @Nat.1 > @Nat.0`.

## 6.7 Contract Inheritance

When a function type is used as a parameter, the caller can rely on the contracts of the concrete function passed:

```
type SafeDiv = fn(Int, { @Int | @Int.0 != 0 } -> Int) effects(pure);

private fn apply_div(@Int, @Int, @SafeDiv -> @Int)
  requires(@Int.1 != 0)
  ensures(true)
  effects(pure)
{
  @SafeDiv.0(@Int.0, @Int.1)
}
```

The refinement type on the function parameter's second argument serves as the contract. The compiler verifies at the call site that `@Int.1 != 0` (which follows from the precondition).

## 6.8 Summary of Verification Tiers

| Tier | Scope | Solver | Timeout | Failure mode |
|------|-------|--------|---------|--------------|
| 1 | Decidable fragment (QF_LIA + length + bool) | Z3 | None (decidable) | Compile error with counterexample |
| 2 | Extended (function calls, quantifiers, arrays) — [not yet implemented](https://github.com/aallan/vera/issues/427) | Z3 with hints | 10 seconds | Falls to Tier 3 |
| 3 | Runtime | None (checks emitted as code) | N/A | Runtime trap |

A fully Tier 1-verified program has the strongest guarantee: if it compiles, the contracts hold for all inputs. A program with Tier 3 contracts may fail at runtime if the contracts are violated.

The compiler reports a summary after compilation:

```
Verification summary:
  12 contracts verified statically (Tier 1)
   1 contract checked at runtime (Tier 3)
   0 assumptions (assume statements)
```
