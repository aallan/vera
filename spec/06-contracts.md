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

> **Status: Not yet implemented.** The `invariant(...)` clause on `data` declarations is specified here but is not currently working in the reference compiler — every documented form fails with `[E130] no <DataName> bindings in scope`, because the slot environment for the invariant predicate is not yet wired up.  Tracked in [#686](https://github.com/aallan/vera/issues/686) (successor to the now-closed #560 — that earlier issue was about removing the broken spec examples; the feature implementation is the remaining work).  Until the implementation lands, refinement types (Chapter 2, Section 2.6) are the working alternative for expressing constraints on data values.

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
- Float64 literals (`1.5`, `-0.5`) — Z3 Real sort, sound for relational properties (added [#667](https://github.com/aallan/vera/issues/667))
- String literals
- Linear arithmetic (`+`, `-`, `*` with literal multiplier)
- Comparisons (`==`, `!=`, `<`, `>`, `<=`, `>=`)
- Boolean connectives (`&&`, `||`, `!`)
- `array_length()` on arrays, `string_length()` on strings
- Array index expressions (`@Array<T>.0[i]`) — uninterpreted `index_<T>(arr, i)` function; sound for relational facts but doesn't reason about element structure beyond what explicit predicates assert (added [#667](https://github.com/aallan/vera/issues/667))
- Array literals (`[a, b, c]`) — fresh `Array_<T>` constant with `length(lit) == N` and per-element `index(lit, i) == elt_i` axioms asserted (added [#667](https://github.com/aallan/vera/issues/667))
- Logical implication (`==>`)
- `true`, `false`
- The `@T.result` reference (in `ensures` only)
- Conditional expressions (`if ... then ... else ...`)
- Calls to `pure` functions that have their own contracts — the verifier inlines the callee's contract at the call site

### 6.3.2 Additionally Allowed in Contracts (Tier 2)

> **Status: Not yet implemented.** Tier 2 (Z3-guided) is specified here but not implemented in the reference compiler. Tracked in [#427](https://github.com/aallan/vera/issues/427). Contracts using these constructs currently fall to Tier 3 (runtime check).

Beyond the decidable fragment, contracts may also use:
- Quantified expressions (limited, see below) — `forall` / `exists` fall to Tier 3 today

Note that array element access (`@Array<T>.0[i]`) and array literals (`[a, b, c]`) are NOT Tier 2 — both are Tier 1 with the uninterpreted-function encoding described in §6.3.1 (added [#667](https://github.com/aallan/vera/issues/667)).  Tier 2 is reserved for predicates that the decidable fragment can't decide on its own and need user-provided lemmas (#427).

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

Bounded quantification with concrete literal bounds is decidable via finite unrolling, and symbolic bounds are decidable via inductive reasoning — but **both reach the decidable fragment only via Tier 2 (Z3-guided)**, which is [not yet implemented](https://github.com/aallan/vera/issues/427). At present every `forall` / `exists` in a contract falls to Tier 3 (runtime check) regardless of whether its bound is a literal, a length expression, or symbolic.

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

Where the parameters have the same meaning as for `forall`. Like `forall`, bounded existential quantification reaches the decidable fragment only via Tier 2 (Z3 with finite unrolling for small bounds, or Skolemization for symbolic bounds), which is [not yet implemented](https://github.com/aallan/vera/issues/427). At present every `exists` in a contract falls to Tier 3 (runtime check).

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

A practical implication: if a function `bad` has an implementation that doesn't satisfy its own `ensures(...)` clause, the verifier reports E500 on `bad`'s body — but a caller `main` that uses `bad`'s declared contract is still verified.  The bug is contained to `bad`'s body-vs-contract mismatch; `main`'s reasoning is sound under the assumption that `bad` honours its declared postcondition.  This is intentional — it keeps verification compositional and bounded by per-function complexity, rather than requiring whole-program reasoning at every call site.  The cost is that an E500 on `bad` is a real failure that downstream consumers (`vera test`, `vera verify`) MUST surface; silently classifying `bad` as verified while `main` reads its contract would break the soundness chain.

### 6.4.3 Primitive Operation Safety

The verifier checks the contracts the programmer wrote, and **auto-synthesises** a proof obligation at every primitive operation whose well-definedness depends on operand values.  Each is discharged from the surrounding preconditions and path conditions exactly like a call-site precondition check (§6.4.2):

| Operation | Obligation | Code |
|---|---|---|
| `a - b` (Nat) | `a >= b` — no underflow | E502 |
| `@Int` value into a `@Nat` slot | `value >= 0` | E503 |
| `a / b`, `a % b` (Int / Nat) | `b != 0` | E526 |
| `arr[i]` (`Array<T>`) | `0 <= i < array_length(arr)` | E527 |

To discharge an operation obligation, the programmer encodes the constraint in a precondition (`requires(@Int.0 != 0)`), a guarding `if` (whose path condition holds in the relevant branch), or a refinement type (`{ @Int | @Int.0 != 0 }`).  A function that performs `@Int.1 / @Int.0` with `requires(true)` therefore no longer verifies cleanly: the unguarded divisor is a compile error (E526).

**Division and modulo** are Tier-1-decidable — the divisor is a concrete integer term — so an unguarded `a / b` the solver cannot prove non-zero is a compile error (E526).  (Float division is exempt: `f64.div` by zero yields inf/NaN, not a trap.)  **Array indexing** depends on `array_length`, which the SMT layer models as an *uninterpreted* function (§6.3.2), so bounds reasoning is in general beyond Tier 1.  The verifier therefore tiers the obligation honestly: it proves the bound at **Tier 1** when a literal length, refinement, precondition, or path condition pins the length; reports a compile error (**E527**) when the index provably exceeds a statically-known length (e.g. `[1, 2, 3][5]`); and otherwise — a dynamic, opaque length — degrades to a runtime-guarded **Tier 3** obligation (counted in `vera verify --json`, never a silent pass).  An index inside a closure, quantifier, or handler-clause body carries no static obligation at all — the walker does not recurse into those fresh-scope bodies — but the codegen bounds-check still traps at runtime; lifting such sites to a Tier-1 proof is the Tier 2 work in [#427](https://github.com/aallan/vera/issues/427), and walker coverage of them is tracked in [#779](https://github.com/aallan/vera/issues/779).  Indexing applies to `Array<T>` only; indexing a `String` is a type error (E161).

The `@Nat` obligations (E502 / E503) carry the most nuance, spanning many binding sites.  The verifier emits an E502 obligation `lhs >= rhs` at every `@Nat - @Nat` subtraction site (see [#520](https://github.com/aallan/vera/issues/520)), and an E503 obligation `value >= 0` where an `@Int` value narrows into a `@Nat` **binding** slot — `let`, call-argument, effect-operation-argument, constructor-field, top-level match-bind, and literal-tuple-destructure sites (see [#552](https://github.com/aallan/vera/issues/552)), plus the generic-instantiation, ADT sub-pattern, non-literal-destructure, and cross-module imported-constructor sites (see [#747](https://github.com/aallan/vera/issues/747)).  (A narrowing at a function **return** position, or a `@Nat` component of a tuple/constructor built in value position, is not yet obligated — see [#758](https://github.com/aallan/vera/issues/758).)  The codegen mirrors the subtraction obligation and the `@Nat` binding sites with runtime guards — every concrete site (`let`, destructure, match-bind, sub-pattern, concrete constructor field, concrete call-argument) plus **generic function-formal calls**, which guard on the monomorphised callee (the mangled instance `pick$Nat` carries concrete `@Nat` flags).  Two sites stay unguarded, both still obligated statically, so a Tier-3 narrowing the solver cannot discharge at either surfaces an E504 warning: the **effect-operation argument**, whose runtime guard is deferred (see [#754](https://github.com/aallan/vera/issues/754)), and the **generic-instantiated constructor field**, since constructor layouts carry no per-field `@Nat` metadata to monomorphise.  Division, modulo, and array indexing now follow the same auto-synthesis pattern ([#680](https://github.com/aallan/vera/issues/680)); lifting dynamic or closure-captured array bounds from a runtime-guarded Tier 3 to a Tier-1 proof is part of the Tier 2 verification work in [#427](https://github.com/aallan/vera/issues/427).

Runtime traps for unguarded primitives are Vera-native: each trap carries a kind label (`divide_by_zero`, `out_of_bounds`, etc.), a per-kind Fix paragraph naming the precondition that would have prevented it, and a source backtrace — so a missing static guarantee is still a recoverable signal.

### 6.4.4 SMT Solver Integration

VCs are translated to SMT-LIB format and solved by Z3:

1. **Tier 1 VCs** (decidable fragment): sent directly to Z3. Z3 returns `unsat` (VC is valid), `sat` (VC is invalid, with counterexample), or `unknown`. Each invocation is bounded to **10 seconds** by default to prevent pathological blowup on adversarially crafted contracts. Tier 1 contracts that time out fall to Tier 3.
2. **Tier 2 VCs** (with hints, not yet implemented — [#427](https://github.com/aallan/vera/issues/427)): the compiler provides additional axioms from `assert` statements and lemma functions. Z3 has a timeout of 10 seconds. Currently, contracts requiring hints fall to Tier 3.
3. **Tier 3 fallback**: if Z3 returns `unknown` or times out, the VC is compiled as a runtime check.

### 6.4.5 Counterexample Reporting

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
| 1 | Z3 quantifier-free decidable fragment: linear integer + real arithmetic, bool, strings (Z3 `String` sort), uninterpreted sorts/functions (length, **array literals and indexing via `index_<T>` functions** — #667).  No single SMT-LIB logic name covers all of these — QF_UFLIRA is the closest standard logic (integer + real + uninterpreted functions, without strings); strings are a Z3-specific extension. | Z3 | 10 seconds | Compile error with counterexample; falls to Tier 3 on unknown or timeout |
| 2 | Extended: quantifiers, lemma/assert hints — [not yet implemented](https://github.com/aallan/vera/issues/427) | Z3 with hints | 10 seconds | Falls to Tier 3 |
| 3 | Runtime | None (checks emitted as code) | N/A | Runtime trap |

A fully Tier 1-verified program has the strongest guarantee: if it compiles, the contracts hold for all inputs. A program with Tier 3 contracts may fail at runtime if the contracts are violated.

The compiler reports a summary after compilation:

```
Verification summary:
  12 contracts verified statically (Tier 1)
   1 contract checked at runtime (Tier 3)
   0 assumptions (assume statements)
```

## 6.9 Limitations

| Limitation | Issue |
|-----------|-------|
| Tier 2 verification (Z3-guided with `assert`/lemma hints) is specified in §6.3.2 and §6.6 but not implemented; contracts requiring hints fall to Tier 3 | [#427](https://github.com/aallan/vera/issues/427) |
| The `invariant(...)` clause on `data` declarations is specified in §6.2.3 but not implemented; every documented form fails with `[E130] no <DataName> bindings in scope`.  Use refinement types (Chapter 2, §2.6) for the same effect on constraint-bearing data values. | [#686](https://github.com/aallan/vera/issues/686) |
