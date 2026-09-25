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

At every call site of `safe_divide`, the compiler verifies that the first argument is non-zero — `@Int.1` is the first parameter under most-recent-first indexing (Chapter 3). If it cannot prove this statically, it inserts a runtime check.

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

Postconditions on stateful functions also have `old(State<T>)` and `new(State<T>)`, which name an effect's state before and after the call. Both are specified in Chapter 7, Section 7.9.2. Like `@T.result`, both are valid only inside `ensures` clauses.

### 6.2.3 Invariants (`invariant`)

> **Status: Not yet implemented.** The `invariant(...)` clause on `data` declarations is specified here but is not currently working in the reference compiler — every documented form fails with `[E130] no <DataName> bindings in scope`, because the slot environment for the invariant predicate is not yet wired up.  Tracked in [#686](https://github.com/aallan/vera/issues/686) (successor to the now-closed #560 — that earlier issue was about removing the broken spec examples; the feature implementation is the remaining work).  Until the implementation lands, refinement types (Chapter 2, Section 2.6) are the working alternative for expressing constraints on data values.

An invariant is a predicate declared on a data type that MUST hold for all values of that type:

<!-- vera:skip-check category="INCOMPLETE" reason="is_sorted_impl in SortedArray" -->
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

**Every obligation discharged inside a `match` arm** — an assertion, a call precondition, a `@Nat` narrowing, and each §6.4.3 primitive-operation safety obligation — is discharged against the facts that arm establishes, including the declared-type facts its constructor sub-pattern bindings carry ([#1403](https://github.com/aallan/vera/issues/1403)).  One arm establishes one set of facts and every obligation in it reads them: binding `Some(@Nat)` off an `Option<Nat>` proves `assert(nat_to_int(@Nat.0) >= 0)` at Tier 1, and binding `Some(@PosInt)` off an `Option<PosInt>` likewise discharges `100 / @PosInt.0` rather than reporting E526.

The rule of §6.4.2 applies to all of them, and it keys on whether the fact was ESTABLISHED rather than on any one way of failing to establish it: where the producer's own obligation left the fact unestablished — disclosed as unguarded, refuted, or undecided within the solver budget — the fact is withheld, the obligation falls to its runtime check, and the demotion is reported — **E535** for an assertion, whose guard is the §11.14.1 trap, and **E534** for a contract or a safety obligation, whose guard is the operation's own trap.  A demoted obligation is never silent: a `tier3` that no diagnostic surfaces would break the accounting `vera verify --json` documents.

The demotion says which of the three it was, because they ask the reader to do different things — raise the budget, fix the producer, or plant a guard.

An arm's **context is one derivation** for every obligation in it, which is what makes the rule above a rule rather than a property of a particular walk.  It follows that an arm's pattern binder shadows a same-named outer slot for *every* obligation in the arm — no obligation is discharged against the enclosing value a binder has taken the name of — and that where the scrutinee cannot be modelled at all, every binder the pattern declares stands for an unreadable value: an obligation over one is neither discharged nor refuted, but falls to its runtime guard.  Refusing such a value is as wrong as proving from it, because the counterexample names nothing the program can produce.

One boundary is worth stating, because the Tier-1 claim inherits whatever the producer's own obligation set does not cover: for a **nested** sub-pattern bind the codegen payload guard that backs the direct case is not yet emitted ([#765](https://github.com/aallan/vera/issues/765)), so the arm's nested fact rests on the producer's own construction obligation alone.

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

The compiler MUST emit a warning (**W003**) for every `assume` statement:

```
WARNING: unverified assumption at line 7: @Int.0 > 0
```

`assume` is an escape hatch. It is unsound — if the assumption is false, the program may have undefined behaviour. It should be used only when interfacing with verified external code or when a proof is beyond the verifier's capability.

## 6.3 Contract Predicate Language

Contract predicates use the same expression syntax as Vera programs, with the following restrictions and extensions.

### 6.3.1 Allowed in All Contracts

Everything allowed in the decidable fragment (Chapter 2, Section 2.6.1):
- Integer literals and slot references
- Float64 literals and values (`1.5`, `-0.5`) — Z3's IEEE-754 binary64 FloatingPoint sort (`FPSort(11, 53)`, round-nearest-ties-to-even), so Tier-1 proofs respect `NaN` / `±Inf` / signed zero / rounding and match the runtime; `==`/`!=` are IEEE `fpEQ`/`fpNEQ` and `%` is the truncated remainder (C `fmod`) (added [#667](https://github.com/aallan/vera/issues/667), made IEEE-sound in [#797](https://github.com/aallan/vera/issues/797)).  Equality on an ADT whose fields transitively include `Float64` decomposes per-field — same-constructor recognizers plus fieldwise `fpEQ` for Float64 fields, recursing into nested Float64-containing ADTs — so the Tier-1 model matches the runtime's structural per-field `f64.eq` (Chapter 9, Section 9.8.2) rather than Z3's structural datatype `=` (under which `NaN = NaN` holds and `+0.0 = -0.0` does not, both wrong at runtime); a *recursive* Float64-containing ADT has no finite decomposition, so its equality falls to Tier 3 ([#871](https://github.com/aallan/vera/issues/871))
- String literals
- Linear arithmetic (`+`, `-`, `*` with literal multiplier)
- Comparisons (`==`, `!=`, `<`, `>`, `<=`, `>=`)
- The `Eq` / `Ord` ability operations `eq(a, b)` and `compare(a, b)` (Chapter 9, Section 9.8) — the generic-programming spelling of `==` and the three-way `Ordering` comparison.  A contract predicate may use either form; `eq(a, b)` is verified and compiled *as* `a == b`, and `compare(a, b)` *as* the canonical `Ordering` if-chain (`if a < b then Less else if a == b then Equal else Greater`).  The two spellings are semantically identical and share one internal representation (one canonical form, Section 0.2.3), so a contract written with the ability op enjoys the same Tier-1 reasoning and runtime enforcement as its operator form ([#874](https://github.com/aallan/vera/issues/874))
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

The bound is an **integer count** — the quantified index runs over `0 .. bound-1`.  An `@Int`/`@Nat` (or a refinement over one) is required; any other domain type — an array, a string — is a check-time error (**E128**).  To quantify over an array's elements, pass `array_length(arr)` as the bound and index the array inside the predicate.

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

The precondition VC is discharged at **Tier 1** when the actual arguments and the callee's precondition both translate to the decidable fragment.  When an argument or the precondition uses a construct outside that fragment — an ADT field of a host-handle type such as `Map`, or a precondition over a non-modelled builtin — the obligation cannot be checked statically.  Rather than let it vanish (which would make `vera verify` overstate coverage), the verifier degrades it **loudly** to a runtime-guarded **Tier 3** obligation with an **E532** warning ([#882](https://github.com/aallan/vera/issues/882)), counted in `vera verify --json`; the codegen precondition guard still enforces the contract at runtime.  This holds for calls in every position — statement, `requires`, and `ensures` predicates alike.

A practical implication: if a function `bad` has an implementation that doesn't satisfy its own `ensures(...)` clause, the verifier reports E500 on `bad`'s body — but a caller `main` that uses `bad`'s declared contract is still verified.  The bug is contained to `bad`'s body-vs-contract mismatch; `main`'s reasoning is sound under the assumption that `bad` honours its declared postcondition.  This is intentional — it keeps verification compositional and bounded by per-function complexity, rather than requiring whole-program reasoning at every call site.  The cost is that an E500 on `bad` is a real failure that downstream consumers (`vera test`, `vera verify`) MUST surface; silently classifying `bad` as verified while `main` reads its contract would break the soundness chain.

**Opaque effect values.** A `let` whose value is an effect operation's result (`let @Int = random_int(0, 9);`) binds a fresh *opaque* constant of the value's type in the verification model, and translation of the body continues past it ([#764](https://github.com/aallan/vera/issues/764), [#1199](https://github.com/aallan/vera/issues/1199)); the same applies per-component to a tuple destructure whose source cannot be projected.  Two rules govern how obligations over an opaque value classify:

- **Preconditions stay strict where the body is translated.**  A user function's precondition that cannot be proven at a call the verifier checks as it translates the function body — a call whose enclosing expressions and earlier statements all translate, such as one at the top of a `let`'s body — because the argument is opaque, is reported (**E501**), exactly as for an opaque function result: establishing the precondition is the caller's obligation, and the repair is an `assert`/`assume` on the value, whose fact flows into the check ([#804](https://github.com/aallan/vera/issues/804)).  **Elsewhere a check is not refused on a value the verifier cannot state** ([#1480](https://github.com/aallan/vera/issues/1480)).  A built-in's declared domain at any call, and a user function's precondition in a `requires`, an `ensures`, a `decreases` measure or a refinement predicate, or at a call only the verifier's obligation walk reaches — in an argument of a built-in the verifier does not model, in an interpolated part, in a `handle` body, in a `match` arm under a scrutinee that does not translate, or after a `let` whose value the body's translation cannot bind at all, such as an array a closure returns — is a check the compiled program makes where it evaluates it.  A precondition there that is refuted only over a placeholder for such a value, one that some value of the placeholder satisfies, takes the **E532** Tier-3 demotion above, with that check behind it; one false for every value the placeholder could take is **E501**; and an `assume` about the value discharges either.  A call precondition over a binder of a closure, of a quantifier's predicate or of a handler clause, which the verifier reads without its value, is E532 as well, as an argument that does not translate is.  A value is unknown only as far as its binder's type leaves it: code generation guards the bind of a binder declared at a refinement type before anything in its scope runs (Section 2.6.5), so the verifier takes the binder's predicate as a fact about it, and a precondition that predicate entails is discharged — `need_pos(@Pos.0)` after `let @Pos = get(())`, or in a `Some(@Pos)` arm whether or not the scrutinee translates, verifies, and a violating value traps at the bind.  Under a scrutinee that translates, the binder would read the projection its own bind is obligated over, so it is bound to a fresh value equal to that projection, and only a goal that reads the fresh value is given the predicate: the bind's obligation stays the runtime guard.  The predicate is given on the runs where the bind runs — the arm's own pattern matched and no earlier arm's did, and the same of every arm and branch enclosing the `match` — and on no others: under an enclosing arm whose pattern is nested, whose condition the verifier reads by its outer constructor alone, or a branch whose condition does not translate, the binder is the projection and carries nothing.  A contract the verifier assumes rather than checks — a callee's `ensures` at the call, the function's own `requires` — states what it says about the projection itself.  A refinement over a refinement has no guard at the bind and carries no such fact, and at a call the function body's translation checks, neither does a binder under a nested constructor pattern, whose arm that translation reads by its outer constructor alone.
- **A goal that holds only from a disclosed fact is Tier 3, not Tier 1.**  A declared-type fact whose own obligation was reported as neither proved nor guarded is not a fact the run established.  A postcondition provable only once it is assumed is reported **E534** and checked at run time; a call precondition in the same position takes the E532 demotion rather than an E501 violation, since no violating model exists.  Disclosure is a property of the **value**, not of the expression that names it ([#1406](https://github.com/aallan/vera/issues/1406), [#1407](https://github.com/aallan/vera/issues/1407)): the demotion is the same whether the disclosed result reaches the goal directly, through a `let` binding or a chain of them, through a projection or a destructure, joined from a branch that discloses on one arm, or taken apart and rebuilt — a value CONSTRUCTED from a disclosed component is disclosed, because the component's fact is what the reconstruction rests on.  A function whose own result is such a value is itself disclosed for its callers, however many forwarding hops separate them — recorded against the function it belongs to, so a `where` helper's disclosure is scoped to its top-level owner and never reaches a same-named helper under a different one — so a wrapper, a pipe or a `where` helper carries the fact's provenance rather than laundering it.  The rule binds every reader of the fact, not only a `match` arm's bindings ([#1413](https://github.com/aallan/vera/issues/1413)): a projected value re-narrowing into a second refinement, and a `let`-destructure's component invariant, are each Tier 3 when the goal *depends* on a fact withheld because the value they read from was disclosed — and Tier 1 still when it does not, the withheld facts being offered back only after a proof without them fails, so a goal that never needed one keeps it.  This rule is **independent of module layout** ([#1399](https://github.com/aallan/vera/issues/1399)): a disclosure made in an imported module demotes its importer exactly as an in-module one does, and transitively along the import graph, so splitting a program across files never turns a Tier-3 truth into a Tier-1 proof.  A module's disclosed set is derived from that module's own verification — the same set `vera verify <module>` reports — and read by its importers; the importer's obligation stream stays its own.
- **An `assert` that is neither proved nor refuted says so.**  A body `assert(P)` the solver cannot settle falls to a runtime check and MUST be reported (**E535**), so the construct that moved the tier count is named — the same disclosure `requires` (E521), `ensures` (E522) and `decreases` (E525) already carry.
- **Refutations over opaque values are not violations.**  A postcondition, refined return, or primitive-operation obligation that *fails* to prove where the goal mentions an opaque constant demotes to a runtime-checked **Tier 3** obligation (`E522` for a postcondition) rather than reporting a definite violation — a countermodel over an unconstrained stand-in says nothing about the value the effect actually produces (`random_int(1, 9)` never returns `0`, but its stand-in would "witness" a zero divisor).  A proof that *succeeds* despite the opacity is kept at Tier 1: it holds for every value the constant could take.  The demotion is per-obligation, not per-function — a genuine violation elsewhere in the same body is still reported.  A value narrowed into a `@Nat` or refined slot is treated alike where it is, or embeds, a placeholder for a `match` binder under a scrutinee the verifier cannot translate, or for a `let` or a destructured component whose value it cannot translate inside a `requires`, an `ensures`, a measure or a predicate: refuted only over the placeholder, the narrowing is not refused — it is Tier 3 behind its guard, or disclosed (`E504`, `E506`) where code generation plants none — and refuted for every value the placeholder could take, it is a violation.  This holds at every narrowing: a binding, a constructor sub-pattern's field, and a payload a call argument's type refines (Section 6.4.3).

Distinct effect-op bindings are distinct constants — two `random_int` results are never provably equal.  The variadic `Tuple` pseudo-constructor participates in the decidable fragment: a tuple literal in expression position, and a destructured tuple's components, translate via an on-demand single-constructor datatype sort keyed on the component types ([#747](https://github.com/aallan/vera/issues/747)), so tuple construction and projection are Tier-1-decidable when every component's type and value translate to the decidable fragment (a component of an unsupported type — a function value, for instance — leaves the tuple unmodelled, and the enclosing obligations fall to Tier 3 as before).

### 6.4.3 Primitive Operation Safety

The verifier checks the contracts the programmer wrote, and **auto-synthesises** a proof obligation at every primitive operation whose well-definedness depends on operand values.  Each is discharged from the surrounding preconditions and path conditions exactly like a call-site precondition check (§6.4.2):

| Operation | Obligation | Code |
|---|---|---|
| `a - b` (Nat) | `a >= b` — no underflow | E502 |
| `@Int` value into a `@Nat` slot | `value >= 0` | E503 |
| `a / b`, `a % b` (Int / Nat) | `b != 0` | E526 |
| `arr[i]` (`Array<T>`) | `0 <= i < array_length(arr)` | E527 |
| `a + b`, `a * b` (Int / Nat); `a - b` (Int) | result within i64 / u64 range — no overflow | E528 |
| `float_to_int(x)`, `floor(x)`, `ceil(x)`, `round(x)` | `x` finite (not NaN / Inf) and its truncated, floored, ceiled or rounded value within i64 range | E529 |
| `float_to_string(x)`, and a `show` or string interpolation of a `@Float64` | `x` not finite, or its magnitude below 2^63 | E529 |
| `string_char_code(s, i)` | `0 <= i < string_length(s)`, the length in bytes — the built-in's declared `requires` (§9.6.14) | E501 |

**Where an operation is obligated.** An operation is obligated wherever the compiled program evaluates it, and discharged under the facts that hold at that point in the compiled code: a function body; each `requires`, under the clauses before it, which the compiled check has already passed; each `ensures`, after the body; the `decreases` measure, on entry and on a self-recursive tail call's arguments (§5.6.1); and a refinement predicate, once, at its declaration, under only its base type's facts (§2.6). The same holds for a call's precondition (§6.4.2) and for an `@Int` value narrowed into a `@Nat` slot, wherever either is evaluated. An `if` is a premise of its branches.  `&&` and `||` short-circuit (§4.6), which makes the left operand a premise of the right one, but the reference compiler currently evaluates both operands ([#1501](https://github.com/aallan/vera/issues/1501)), so until that is fixed the verifier does not take it as one. A built-in whose compiled translation traps outside a domain carries that domain: `string_char_code` declares it as a `requires`, obligated at each call like a user function's (`E501` where it is refuted, or `E532` where the string's byte length is not known statically or the refutation rests on a value the verifier cannot state, §6.4.2) and recorded when it is discharged too, since the check it stands for is made at the call rather than in a callee's prologue; the float-to-integer truncations carry `float_to_int`'s domain obligation below.

To discharge an operation obligation, the programmer encodes the constraint in a precondition (`requires(@Int.0 != 0)`), a guarding `if` (whose path condition holds in the relevant branch), or a refinement type (`{ @Int | @Int.0 != 0 }`).  A function that performs `@Int.1 / @Int.0` with `requires(true)` therefore does not verify cleanly: the unguarded divisor is a compile error (E526).

**Division and modulo** are Tier-1-decidable — the divisor is a concrete integer term — so an unguarded `a / b` whose Tier-1-translatable divisor admits a zero counterexample is a compile error (E526); a divisor beyond the translatable fragment (a fresh-scope slot in a closure or handler clause, an opaque effect result, a solver timeout) degrades to a runtime-guarded Tier-3 obligation instead, while a manifest zero divisor is E526 in any position.  (Float division is exempt: `f64.div` by zero yields inf/NaN, not a trap.)  **Array indexing** depends on `array_length`, which the SMT layer models as an *uninterpreted* function (§6.3.2), so bounds reasoning is in general beyond Tier 1.  The verifier therefore tiers the obligation honestly: it proves the bound at **Tier 1** when a literal length, refinement, precondition, or path condition pins the length; reports a compile error (**E527**) when the index provably exceeds a statically-known length (e.g. `[1, 2, 3][5]`); and otherwise — a dynamic, opaque length — degrades to a runtime-guarded **Tier 3** obligation (counted in `vera verify --json`, never a silent pass).  An index inside a closure body, quantifier predicate, or handler-clause body is walked under a fresh (empty) slot scope; one that depends on a captured length or fresh slot is reported as a runtime-guarded **Tier 3** obligation — beyond the fresh scope's decidable fragment, with the codegen bounds-check backing it — while a literal-only shape still classifies exactly (a manifest out-of-bounds literal is a loud E527) — while an index in a quantifier *domain* or a handler *body* (enclosing-scope positions) is tiered at full precision like any direct-position index; lifting the fresh-scope sites to a Tier-1 proof is the Tier 2 work in [#427](https://github.com/aallan/vera/issues/427).  Indexing applies to `Array<T>` only; indexing a `String` is a type error (E161).

The `@Nat` obligations (E502 / E503) carry the most nuance, spanning many binding sites.  The verifier emits an E502 obligation `lhs >= rhs` at every `@Nat - @Nat` subtraction site (see [#520](https://github.com/aallan/vera/issues/520)), and an E503 obligation `value >= 0` where an `@Int` value narrows into a `@Nat` **binding** slot — `let`, call-argument, effect-operation-argument, constructor-field, top-level match-bind, and literal-tuple-destructure sites (see [#552](https://github.com/aallan/vera/issues/552)), plus the generic-instantiation, ADT sub-pattern, non-literal-destructure, and cross-module imported-constructor sites (see [#747](https://github.com/aallan/vera/issues/747)), and the function **return** position — an `@Int` value (including an `if`/`match` tail) narrowing into a `@Nat` return is obligated `result >= 0` under the body's path conditions, the dual of the [#813](https://github.com/aallan/vera/issues/813) `@Nat -> @Int` widen-return obligation (see [#758](https://github.com/aallan/vera/issues/758)).  The codegen mirrors the subtraction obligation and the `@Nat` binding and return sites with runtime guards — every concrete site (`let`, destructure, match-bind, sub-pattern, concrete constructor field, concrete call-argument) plus **generic function-formal calls**, which guard on the monomorphised callee (the mangled instance `pick$Nat` carries concrete `@Nat` flags).  Every `@Nat` narrowing at a **pattern bind** (`let`, match bind, tuple destructure, constructor sub-pattern at any nesting depth) or at a **boundary** (call argument, closure argument / return, the function return position, a constructor field concrete or generic-instantiated, a tuple component at construction and at destructure, a BUILT-IN effect operation's argument) is runtime-guarded.  What stays unguarded is a **clamping builtin** — `string_slice`, whose `@Nat` index arguments code generation deliberately does not guard because the builtin CLAMPS them to `[0, len]` (#475), so a negative becomes a valid `0` and no invalid `@Nat` propagates — the disclosure is `E504` and the roster is `_NAT_ARG_UNGUARDED_BUILTINS` — and a **user-declared effect operation's argument**, whose enclosing function is dropped with `E603` so no run reaches it.  The **tuple component at construction** was the last BINDING site to be closed: the built-in `Tuple` carrier's layout has no per-field `@Nat` metadata, and the component's target type had been recovered from the threaded target-type table for the `@Nat` -> `@Int` *widening* guard ([#813](https://github.com/aallan/vera/issues/813)) but not for the narrowing one — the two directions now read that table alike ([#1416](https://github.com/aallan/vera/issues/1416)), as does the **tuple-destructure** component's widening for a non-literal source.  The **generic-instantiated constructor field** and the **effect-operation argument** are guarded: the field reads its instantiation from the argument's own recorded target — the same table `_nat_binding_target` consults to decide the obligation exists — and an operation reads its declared formals from the registry the checker typed the call against ([#757](https://github.com/aallan/vera/issues/757), [#754](https://github.com/aallan/vera/issues/754)).  A user-declared effect's operation argument is obligated and unguarded, but its enclosing function is an E603 codegen skip, so no run reaches it. A tuple is checked in BOTH directions since [#1416](https://github.com/aallan/vera/issues/1416) — on the way in at construction and on the way out at destructure.  Since [#1426](https://github.com/aallan/vera/issues/1426) the §2.6.5 PREDICATE is guarded at every construction-position component — a constructor field (concrete or generic-instantiated), a tuple component (including a nested tuple's own components), an array element, a `Map` value — by the same lowering the pattern binds use, read from the one site table both the verifier and code generation consult.  The guard is emitted for the refinement BASES the lowering can compare: a base that is itself a refinement, or one that erases at run time, is guarded nowhere and is disclosed `E506` instead (a function boundary refuses it outright with `E618`, since there the verifier would otherwise be promising a check).  The SIGN direction at an array element and a `Map` value joined it in [#1440](https://github.com/aallan/vera/issues/1440), and the predicate at the `State` write boundaries in [#1439](https://github.com/aallan/vera/issues/1439), so every construction position and every write boundary is now checked in both directions.  EVERY built-in effect operation's argument is guarded at its op-call site, from the declared formals the checker typed the call against (see [#754](https://github.com/aallan/vera/issues/754)) — the `State` write boundaries (see [#1203](https://github.com/aallan/vera/issues/1203)) and the `Exn` `throw` payload, which also carries the §2.6.5 refinement-predicate guard (see [#1268](https://github.com/aallan/vera/issues/1268)), included, not only those.  Division, modulo, and array indexing now follow the same auto-synthesis pattern ([#680](https://github.com/aallan/vera/issues/680)); lifting dynamic or closure-captured array bounds from a runtime-guarded Tier 3 to a Tier-1 proof is part of the Tier 2 verification work in [#427](https://github.com/aallan/vera/issues/427).

**Integer overflow** ([#798](https://github.com/aallan/vera/issues/798)).  `@Int` is a signed 64-bit machine integer and `@Nat` an unsigned one; `+` / `-` / `*` wrap at the i64 / u64 boundary.  Like `@Nat` underflow and signed-division `MIN / -1`, an overflowing operation is a *partial* operation that **traps** at runtime rather than silently wrapping, so each `@Int` / `@Nat` `+` / `-` / `*` carries an obligation that the result stays in range.  It is classified at the operands' **common (coerced) type** — `@Int` if either operand is `@Int` (since `@Nat <: @Int`), else `@Nat` — not one operand's self-type (a non-negative literal is `@Nat`, but `5 + @Int.0` is an i64 add) nor the possibly-narrowed result type (an `@Int.0 + 1` stored into a `@Nat` slot is still an i64 add).  A two-check mirrors array indexing: the result provably in range → **Tier 1**; provably out of range (e.g. a literal `u64.MAX + 1`, or `@Int.0 + 1` under `requires(@Int.0 == i64.MAX)`) → a compile error (**E528**); otherwise — dynamic operands — a runtime-guarded **Tier 3** trap.  `@Nat` subtraction is excluded — it is the underflow obligation (E502) above, never a high-overflow.

**String length** ([#802](https://github.com/aallan/vera/issues/802)).  Vera strings are UTF-8 byte sequences and `string_length` returns the **byte** count, but Z3's string theory (SMT-LIB 2.6) models strings as sequences of Unicode **code points** — its `Length` counts code points, which disagrees with the runtime on every multibyte character (`string_length("é")` is `2`, not `1`).  `string_length` is therefore modeled at **Tier 1** only for a string **literal**, whose exact byte length is known; on any non-literal argument it defers to a runtime-guarded **Tier 3** obligation (Z3's string theory has no byte-length operator).  The boolean predicates `string_contains` / `string_starts_with` / `string_ends_with` stay **Tier 1**: UTF-8 is self-synchronizing, so a valid substring / prefix / suffix matches at the byte level exactly when it matches at the code-point level.  The other byte/offset-sensitive string builtins (`string_slice`, `string_index_of`, `string_char_code`, `string_chars`) are not translated to Z3 and already fall to **Tier 3**.  Two further deferrals keep the predicates honest.  Z3's string-sort alphabet only reaches U+2FFFF, and its Python binding silently stores any higher code point as the literal's *escape text* rather than the character — so a literal containing a code point **above U+2FFFF** is unusable in the `z3.StringVal`-based predicate translation (`string_contains` / `string_starts_with` / `string_ends_with`) and defers to **Tier 3** there, instead of letting a predicate match phantom escape bytes the runtime never sees.  `string_length` is unaffected by this one — it byte-counts the *decoded* literal, so an astral literal's length stays **Tier 1**.  A **lone surrogate** (U+D800–U+DFFF) defers on **both** paths: `z3.StringVal` stores it as phantom escape text just like the astral case, and — since it has no UTF-8 encoding at all — `string_length`'s byte count cannot be taken either.

**Numeric type conversions** ([#807](https://github.com/aallan/vera/issues/807)).  Three Float64 builtins are modeled at **Tier 1**.  `float_clamp(v, lo, hi)` is pure Float64 and modeled **unconditionally** as the faithful WASM `f64.min(f64.max(v, lo), hi)` — NaN-propagating and ±0-correct.  Z3's own `fp.min` / `fp.max` *diverge* from WASM here (SMT-LIB returns the non-NaN operand and leaves ±0 implementation-defined, whereas WASM propagates NaN and pins the ±0 sign), so a naive `fpMin` / `fpMax` model would be **unsound** — it would prove `!float_is_nan(float_clamp(NaN, …))`, which the runtime refutes.  `float_clamp` is total, so it carries no obligation.  `int_to_float(n)` and `float_to_int(x)` cross the Int↔Float boundary, and Z3's *symbolic* Int↔Real↔FP reasoning is **unreliable** — it returns spurious counterexamples that do not satisfy their own constraints, non-deterministically across timeouts.  These are therefore modeled at Tier 1 **only for a concrete (constant-foldable) argument**, where Z3 is merely constant-folding; a symbolic argument defers to a sound **Tier 3** (the guiding principle: defer to Tier 3 what Z3 cannot soundly model).  `int_to_float` is total (`f64.convert_i64_s` never traps).  `float_to_int` is **partial** — `i64.trunc_f64_s` traps on NaN / ±Inf / out-of-i64-range — so a concrete argument additionally carries the domain obligation above (a provable violation is a loud **E529**), and a symbolic argument's Tier-3 obligation is guarded by the codegen trunc trap.  `floor`, `ceil` and `round` end in the same instruction after `f64.floor`, `f64.ceil` or `f64.nearest`, and carry the same obligation over the rounded value.  `float_to_string` extracts the integer part it prints with it too, after rendering the non-finite classes and taking the magnitude, so a finite value of magnitude 2^63 or more traps; each call carries the obligation, as does every `show` or interpolation of a `@Float64`, which lower to it (a composite value holding one is recorded Tier 3 at the `show`).  (The four format/parse Float64 builtins — `float_to_string`, `parse_float64`, `decimal_from_float`, `decimal_to_float` — remain **Tier 3** by necessity: Z3's string theory cannot format or parse a float, and `Decimal` is an opaque host handle.)

**Refinement predicates at a call argument** (§2.6.4).  A refinement the caller must establish is obligated wherever the value enters a refined slot, and that includes the refinements a parameter's type writes on a **component** — an ADT payload, a tuple component.  Those are *assumed* by the callee, which is verified once for every caller, so the value's own positions must establish them — the argument (a closure's included), a `let` binder, a constructor field, a tuple component, an effect-operation argument, and the function's return slot, the last of which is what makes the rule transitive.  A construction is excluded only where its own site carries the obligation.  The discharge is a solver query with the source's component invariants as premises, withheld when that source's producer was disclosed.  The tiering follows the guard rather than the site — the boundary guard reaches a parameter's own refinement and its tuple components only (§2.6.5), so an undischarged payload or array-element obligation is `tier3_unguarded`/`E506` while an undischarged tuple-component one is a guarded Tier 3.

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

<!-- vera:skip-parse category="FRAGMENT" reason="type SafeDiv = fn(...) + fn apply_div" -->
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

The refinement on `SafeDiv`'s **second** parameter serves as the contract. The call passes `@Int.1` into that refined position, so the compiler verifies `@Int.1 != 0` at the call site — `apply_div`'s first `@Int` parameter, which follows from the precondition.

## 6.8 Summary of Verification Tiers

![Three-tier verification: each contract obligation goes to Z3 with a ten-second budget — unsat is verified (Tier 1), sat is a compile error with a counterexample, unknown or timeout defers to a Tier 3 runtime guard whose violation traps with a kind, a Fix paragraph, and a backtrace. Tier 2 (hints) is not yet implemented and also falls to Tier 3.](../assets/diagrams/tiers.svg)

| Tier | Scope | Solver | Timeout | Failure mode |
|------|-------|--------|---------|--------------|
| 1 | Z3 quantifier-free decidable fragment: linear integer + real arithmetic, bool, strings (Z3 `String` sort), uninterpreted sorts/functions (length, **array literals and indexing via `index_<T>` functions** — #667).  No single SMT-LIB logic name covers all of these — QF_UFLIRA is the closest standard logic (integer + real + uninterpreted functions, without strings); strings are a Z3-specific extension. | Z3 | 10 seconds | Compile error with counterexample; falls to Tier 3 on unknown or timeout |
| 2 | Extended: quantifiers, lemma/assert hints — [not yet implemented](https://github.com/aallan/vera/issues/427) | Z3 with hints | 10 seconds | Falls to Tier 3 |
| 3 | Runtime | None (checks emitted as code) | N/A | Runtime trap |

The ten-second figure is the DEFAULT per-query budget, not a fixed property of the
language: `vera verify --timeout-ms N` sets it for one run and `VERA_Z3_TIMEOUT_MS`
for an environment, in that precedence. This matters for reading a Tier 3: an
obligation whose proof lands near the budget is Tier 1 on a fast host and Tier 3 on
a slow one, so raising the budget is what distinguishes a claim that needed more
time from one the solver can never see through.

A fully Tier 1-verified program has the strongest guarantee: if it compiles, the contracts hold for all inputs. A program with Tier 3 contracts may fail at runtime if the contracts are violated.

`vera verify` reports a one-line summary:

```text
$ vera verify tests/conformance/ch06_assert_assume.vera
OK: tests/conformance/ch06_assert_assume.vera
Verification: 8 verified (Tier 1), 3 runtime checks (Tier 3)
```

That program contains an `assume` statement, and the summary does not mention it: assumptions reach no tier and are counted nowhere (see the table below). The warning this chapter requires for every `assume` is not emitted either — tracked in [#1345](https://github.com/aallan/vera/issues/1345).

### 6.8.1 Obligation Vocabulary

Every obligation this chapter describes ends in exactly one of the first four states below; the remaining rows name adjacent concepts that are easily mistaken for them. The middle column is the `status` field `vera verify --json` reports for that obligation, so the words used in prose and the machine output are the same set.

| Word | `--json` status | Meaning |
|------|-----------------|---------|
| **proved** | `verified` | Tier 1. Z3 discharged the obligation; it holds for every input. Counted in `tier1_verified`. |
| **runtime-guarded** | `tier3`, `timeout` | Tier 3. Not proved, but the compiler emitted a guard that traps on violation. Counted in `tier3_runtime`. A call precondition over a binder of a closure, a quantifier's predicate or a handler clause lands here (`E532`, Section 6.4.2), as does one refuted only over a placeholder for a value the verifier cannot state, outside the function body's own translation. |
| **unguarded** | `tier3_unguarded` | Neither proved nor guarded. Counted in no tier, and reported as a warning (`E504`, `E506`, `E531`, `E539`, `E540`) — or, for `E538`, as an error that refuses the program (§6.8.2). |
| **refuted or unprovable** | `violated` | The obligation did not discharge and the compiler refuses the program. Two ways in: Z3 returned a concrete counterexample, or — for a user function's precondition over an opaque value, at a call the function body's translation checks (Section 6.4.2) — it could not establish the goal at all. Both report `violated`, which is why the diagnostic says a call *may* violate the precondition rather than that it does. A compile error (`E500`, `E501`, `E502`, `E505`, …), counted in no tier. |
| **assumed** | — | An `assume` statement (Section 6.2.6), not an obligation: the fact is taken on trust rather than discharged, so it reaches no tier and is counted nowhere. It is an unsound escape hatch. |
| **tested** | — | `vera test` generates inputs from the contracts and runs them through WASM. A distinct activity rather than a tier: it samples inputs, it does not quantify over them. |
| **specified, not implemented** | — | Carried by the `Status:` callouts in this specification and collected in the [implementation-status appendix](../docs/implementation-status.md). |

The counts partition accordingly: `total == tier1_verified + tier3_runtime`. A `violated` or `tier3_unguarded` obligation is discharged to no tier, so it appears in the `obligations` array and in the diagnostics, but in neither count.

### 6.8.2 Premise Consistency

A proof is worth no more than the premises it rests on, and a contradictory premise set entails every goal.  Before any obligation of a function is trusted, its premise set MUST be checked for satisfiability; where it has no model, every obligation in that function that would otherwise have been PROVED is reported `tier3_unguarded` rather than `verified`, because none of them was discharged against a reachable state.  An obligation that reached any other verdict keeps its own status and its own code: a contradiction can manufacture a proof and nothing else, so `violated`, `tier3`, `timeout` and `tier3_unguarded` were each reached for a reason the contradiction did not supply ([#1451](https://github.com/aallan/vera/issues/1451)).

The check is stated in two layers, because the two causes ask the reader for different things.

**The author's layer** is everything the program asserts without proof: the parameters' declared types, their refinement predicates, the `requires` clauses, and every top-level `assume`.  An `assume` (§6.2.6) is taken on trust rather than discharged, which makes it a premise in exactly the sense that matters here — `assume(@Int.0 < 3); assume(@Int.0 > 5);` is the same garbage-in as `requires(@Int.0 > 5 && @Int.0 < 3)`, and both MUST be read by this check.  REFUTED here means no call can reach the body under the program's own premises, so nothing in it was verified against anything — **E538**, an error, and the demotion above.  The program is refused.  A refutation is what the refusal rests on, not an unsatisfiability the check merely failed to rule out: where this layer is undecided the program stands, however contradictory its premises may in fact be.  The diagnostic is placed at a BEST-EFFORT site — the first top-level `assume` when the function has one, and otherwise the first non-trivial `requires` — and that placement is not an attribution: the screen establishes only that the premise set as a WHOLE has no model, so the clause named may be one that is perfectly satisfiable on its own.  The refuted object is the whole author layer, and the reader checks all of it: the `requires` clauses, every top-level `assume`, and the parameters' declared types and refinement predicates.  Naming the clause that contributes the contradiction requires an unsat core over that layer, which [#1471](https://github.com/aallan/vera/issues/1471) tracks.

**The full premise set** adds every fact the verifier itself derives — an assumed callee postcondition, a refined return's predicate, a declared-type fact read off a constructor sub-pattern.  Satisfiable at the author's layer and unsatisfiable here means the contradiction needs at least one derived fact: **E539**, with the same demotion.  E539 also covers the case where the author's layer could not be decided, since neither can be blamed on the author's clauses.  That is usually the program disagreeing with itself — an `assume` or a `requires` that no callee's contract permits — and the remedy is to weaken one of them; only where no such premise is at fault is the derived fact the compiler's.  The diagnostic therefore names the contradiction rather than declaring an internal error.  A `violated` obligation already on record is left alone, since a contradiction cannot manufacture a refutation.

Where the full set is refuted and the author's layer is neither proved satisfiable nor refuted inside the budget, the contradiction cannot be attributed to either.  The function is demoted just the same, and reported under **E539** with the diagnostic saying that the premise at fault could not be determined and how to obtain the attribution.  **E538** requires a REFUTATION of the author's layer, never an undecided one: a refusal names the clause to weaken, and `unknown` names nothing.  That is also what keeps acceptance checkable — refusing on an undecided attribution would leave the same program refused under one budget and accepted under a larger one, where the layer answers *satisfiable*.  A larger budget may turn an acceptance into the attributed refusal, which is the direction every Z3-backed diagnostic in this chapter already moves in, and never the other way.

A generic function is screened through its INSTANTIATIONS.  A still-generic signature has no SMT sort for its type parameters, so there is nothing to screen until a call monomorphizes it; the check runs on each clone, and a `forall` generic that nothing instantiates is reported uninstantiated (`E520`, counted in no tier) rather than refused.  Nothing is certified either way — what such a program does not get is the refusal.

A branch's own path condition is NOT part of either layer.  An `if` or `match` arm whose guard cannot hold under the precondition is *unreachable*, not contradictory: its obligations are discharged under that guard by construction, and demoting the function for it would report the program's shape as a defect.  So the check is per *function*, not per *path*, and a `tier1_verified` count may still contain an obligation proved inside an arm no call can enter.

A Tier-1 proof under premises OUTSIDE the decidable fragment requires those premises to be SHOWN satisfiable.  "Not refuted" is not the same claim as "has a model", and on a nonlinear premise the solver may answer *unknown* to both questions — in which case an obligation recorded `verified` was discharged against a premise set nobody has exhibited a model of, and a contradictory one entails it.  The screen ends in one of three states.  Where it REFUTES the premise set, the demotion and the codes above apply.  Where it establishes a model the tier stands: the first stage answers *satisfiable*, or the second does and its model extends to the whole premise set.  That extension has TWO routes, one per regime below, and the summary is not one condition: a **rank** axiom is dropped by the second stage, so its `sat` extends only when the quantified and quantifier-free halves share no uninterpreted symbol; a **totality** axiom is not dropped but carried as ground instances, so its `sat` extends whether or not the halves share symbols — and they routinely do, since the axiom constrains a symbol the quantifier-free premises are about.  Where it does neither, AND the premises are not ENTIRELY inside the fragment §2.6.1 defines, every obligation the function would have proved is reported `tier3_unguarded` under **E540**, a warning: nothing is refuted, so nothing is refused, but nothing is certified either.  The test is an allowlist — linear `Int` and `Real` arithmetic, comparisons, boolean connectives and the conditional, the datatype operations, the array and string operations this chapter lists, the uninterpreted constants and functions the translation mints, and the quantified axioms the screen installed under a regime — and anything else is outside: a floating-point or bit-vector term, nonlinear arithmetic in any theory, a quantified premise the screen installed under no regime, an operation the list does not name.  A classifier whose unlisted case would be a false Tier 1 MUST fail closed.

Premises INSIDE the fragment keep their tier on an undecided screen.  The quantified premises a `decreases` measure installs are the verifier's own rank axioms — consistent by construction, and neither written nor simplifiable by the author — so reading their *unknown* as "not established" would withdraw Tier 1 from ordinary recursive programs to close a hole none of them has.

One consequence is disclosed rather than hidden: for a function whose premises leave the fragment, `tier1_verified` MAY differ between runs of the same compiler on the same program, because the solver need not answer an undecidable query the same way twice.  `ok` does not vary with it — nothing here refuses a program — and the warning says which function and why.

Only a REFUTATION refuses, and only of the author's layer.  An undecided satisfiability check has established nothing, so it names no clause to weaken and the program stands — the distinction §6.8 draws everywhere else between "could not decide" and "decided against".  Demotion is the weaker act and has the wider trigger: a refutation demotes, and so does an undecided screen over premises outside the decidable fragment, under the rule above.  Inside the fragment an undecided screen changes nothing at all.

The refutation is sought in two stages, because one budget cannot serve both.  The first asks the WHOLE premise set under a short budget: a contradiction that propagates is refuted there whatever else is in the context.  The second asks the premise set's **quantifier-free subset** under the full query budget; a refutation on a subset is a refutation on the whole, so this is sound, and it is affordable precisely because the quantified facts — the rank axioms a `decreases` measure installs — are what make a satisfiability question undecidable at any budget.  Between them they reach both a contradiction that propagates and one that needs real search, such as `@Int.0 * @Int.0 == 2 * (@Int.1 * @Int.1)` over `0 < @Int.0, @Int.1 < 60`.  Reaching is not deciding: that second query is nonlinear integer arithmetic, where *unknown* is a legitimate answer at any budget, and the solver need not give the same answer twice for the same query.  So a contradiction of that kind MAY be refuted and MUST NOT be relied on to be — what is guaranteed is that the question is asked, at the full query budget, of a premise set the quantified facts cannot make undecidable on their own.

The second stage is asked only where the first decided nothing.  A model of the whole premise set is a model of every subset of it, so a first stage that answers *satisfiable* has already answered for the subset; asking again would spend the full query budget to be told what is known.  Nothing is lost by the restriction, since an unsatisfiable quantifier-free subset is still reached wherever the first stage fails to decide.

Stage 2 is not merely sound but **refutation-complete**, and what makes it so depends on the SHAPE of each quantified premise.  A quantified axiom the verifier installs is recorded, where it is installed, under one of two regimes.

A **rank** axiom relates one symbol's value at two points — `rank(accessor(x)) < rank(x)` — so no finite set of ground instances captures it.  Stage 2 drops these, and a `sat` it returns establishes a model of the whole premise set only when the quantified and quantifier-free halves share no uninterpreted symbol, which is checked FOR THAT RUN rather than assumed: the rank symbol is fresh, so a model of the quantifier-free part extends by interpreting it as structural depth.

A **totality** axiom constrains one application's value, pointwise — `length(x) >= 0`.  Stage 2 does not drop it: it carries the axiom's ground instances on the `f(t)` terms the quantifier-free premises mention.  A model of those premises together with those instances extends to the axiom itself by choosing the symbol's value freely everywhere else, so the completeness holds without any disjointness condition.

A quantified premise under NEITHER regime is foreign to the screen, and its presence puts the premises outside the fragment: the screen has no answer for it, so nothing in the function is certified on a stage-2 `sat`.  The regime MUST be read from what the installation recorded and never inferred from a symbol's name; an unrecognised axiom MUST be treated as foreign.

Any future quantified premise reopens the design of this screen, and so does any future SORT or theory.  A Tier 2 hint ([#427](https://github.com/aallan/vera/issues/427)) is the live candidate for the first: a quantified fact that is not a rank axiom, or a rank symbol occurring in an ordinary premise, makes the residual real — a contradiction refutable only through a quantified fact, that does not propagate inside the first stage's budget, would go undetected.  The second is the same question one theory over, and the allowlist above is where it lands: `str.substr` and `str.to_int` are inside it while the solver is INCOMPLETE on both, so an *unknown* under them would be undecidability rather than slowness.  Neither is reachable as a premise today — every string builtin that would introduce one leaves the fragment earlier and is disclosed (`E521`) with no premise behind it — but a sort or operation admitted here without that check would repeat the case that made this an allowlist.

An UNSAT precondition is an **error**, at the definition.  A premise set with no model admits no argument, so it constrains no behaviour: there is nothing for a tier to describe, and a language whose contracts are its source of truth does not accept a declaration whose contract says nothing.  The signal belongs where the clause that is wrong is, rather than at a call site that may be in another module or may not exist yet.  Its sibling `E539` stays a warning, because the premise at fault there can be a derived one the author does not directly control.

The call sites answer separately where they can, and MUST continue to: a call to a MONOMORPHIC function whose precondition has no model reports the ordinary `E501`.  Through a `forall` generic callee the same call is only disclosed — `call_pre` at Tier 3, `E532` — which matters for a callee whose definition this run never sees; that gap is [#1468](https://github.com/aallan/vera/issues/1468) and is not repaired here.

## 6.9 Limitations

| Limitation | Issue |
|-----------|-------|
| Tier 2 verification (Z3-guided with `assert`/lemma hints) is specified in §6.3.2 and §6.6 but not implemented; contracts requiring hints fall to Tier 3 | [#427](https://github.com/aallan/vera/issues/427) |
| The `invariant(...)` clause on `data` declarations is specified in §6.2.3 but not implemented; every documented form fails with `[E130] no <DataName> bindings in scope`.  Use refinement types (Chapter 2, §2.6) for the same effect on constraint-bearing data values. | [#686](https://github.com/aallan/vera/issues/686) |
