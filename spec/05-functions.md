# Chapter 5: Functions

## 5.1 Overview

Functions are the primary unit of abstraction in Vera. Every function declaration includes:

1. A name (for top-level functions)
2. Parameter types and return type
3. A contract (preconditions, postconditions, and optionally a decreases clause)
4. An effect declaration
5. A body expression

All components are mandatory. There are no defaults, no shortcuts, and no omissions.

## 5.2 Function Declaration Syntax

The canonical form of a function declaration:

<!-- vera:skip-parse category="FRAGMENT" reason="fn function_name(@ParamType1 ...)" -->
```
private fn function_name(@ParamType1, @ParamType2 -> @ReturnType)
  requires(precondition)
  ensures(postcondition)
  effects(effect_row)
{
  body_expression
}
```

An identifier the grammar claims is unavailable as a function name. Three groups are affected, and a fourth name is reserved for a different reason.

The first is the contract state forms `old` and `new` — in expression position `old(...)` and `new(...)` name an effect's state before and after a call, and take an effect reference rather than an arbitrary expression (Chapter 7, Section 7.9.2). A bare call written `old(x)` is therefore always read as a state reference, never as a function call.

The second is the keywords the lexer admits as a name after `fn` but reads as the keyword everywhere else: `assert`, `assume`, `forall`, `exists`, `match`, `if`, `let`, `fn`, `true`, and `false`. A body containing `match(x)` does not parse as a call at all.

The third is the remaining keywords, which the *contextual* lexer admits wherever a name is expected: `then`, `else`, `data`, `type`, `module`, `import`, `public`, `private`, `requires`, `ensures`, `invariant`, `decreases`, `effect`, `with`, `in`, `where`, `pure`, `ability`, `effects`, `op`, and `result`. These differ from the first two groups in that nothing stops a call reaching them — `private fn with(@Int -> @Int)` declares, and `with(1)` resolves to it. They are reserved because Chapter 1, Section 1.4 reserves the identifier: a keyword names one construct, and a second meaning for the same spelling — the language's construct in one position, a user function in another — is what the one-canonical-form rule excludes. Because reachability is not the argument here, the compiler derives this group from the grammar rather than from a list, which is why it covers `ability`, `effects`, `op` and `result`, and why a keyword added to the grammar joins it automatically.

`resume` is reserved on separate grounds. It is not a keyword — a declaration parses, and outside a handler clause a bare `resume(...)` reaches it — but inside every handler clause body `resume` names the operator that resumes the suspended operation (Chapter 7, Section 7.5.2), bound there rather than declared. A function of that name would give one spelling two meanings by position, which the one-canonical-form rule does not admit. Chapter 1, Section 1.4 lists the identifier as reserved; **E153** enforces it, at the declaration and alone — a clause body in the same file still resolves `resume` to the operator, so the rejected declaration draws no second error. Resuming inside a handler clause is unaffected.

In both of the first two groups the declaration parses and no bare call can reach it: a function under such a name cannot be called from its own file, and a module cannot call its own export. The only route that reaches one is a module-qualified call (`mod::old(...)`, Chapter 8), which parses through the module-call rule — leaving the name a trap in every unqualified position and half-usable cross-module. Vera reserves the whole identifier instead. In the third group the declaration is reachable and the program works; what the reservation removes there is the second meaning, not a trap.

Declaring a function under any name in any of the three groups, or under `resume`, is a compile error (**E153**); rename the function. Because the groups are reserved for different reasons, the diagnostic explains the one that applies — a reader told that `with` can never be called, when their own program just called it, would be misled. The restriction is on the whole identifier, so names that merely begin with a reserved word — `older`, `renew`, `matched` — are ordinary function names.

`handle` is the one exception. It is a keyword, and equally uncallable from Vera source, but `public fn handle(@Request -> @Response)` is the entry point a *host* invokes under `vera serve` and `wasi:http` (Chapter 9, Section 9.5.6), so it is not dead code and stays legal. A future host-invoked entry point is exempted on the same grounds; nothing else is.

The same one-canonical-form reasoning rejects redefining a built-in function (**E151**, Chapter 9, Section 9.6) and redeclaring a built-in effect (**E152**, Chapter 9, Section 9.5.1).

### 5.2.1 Complete Example

```
public fn absolute_value(@Int -> @Nat)
  requires(true)
  ensures(@Nat.result == if @Int.0 >= 0 then { @Int.0 } else { -@Int.0 })
  effects(pure)
{
  if @Int.0 >= 0 then {
    @Int.0
  } else {
    -@Int.0
  }
}
```

### 5.2.2 Multiple Preconditions and Postconditions

Multiple `requires` and `ensures` clauses may be specified. They are conjunctive (all must hold):

<!-- vera:skip-verify category="ILLUSTRATIVE" reason="safe_divide with imprecise ensures" -->
```
public fn safe_divide(@Int, @Int -> @Int)
  requires(@Int.1 != 0)
  requires(@Int.0 >= 0)
  ensures(@Int.result >= 0)
  ensures(@Int.result <= @Int.0)
  effects(pure)
{
  @Int.0 / @Int.1
}
```

Multiple `requires` clauses are equivalent to a single `requires` with `&&`. They are provided as separate clauses for readability and for more precise error reporting (the compiler can indicate which specific precondition was violated).

## 5.3 Parameter Binding Order

Parameters are bound left-to-right, with the leftmost parameter having the highest De Bruijn index and the rightmost parameter having index 0:

```
fn(@Int, @String, @Int -> @Bool)
```

Bindings (innermost first):
- `@Int.0` = third parameter (rightmost `Int`)
- `@String.0` = second parameter
- `@Int.1` = first parameter (leftmost `Int`)

This follows the De Bruijn convention where the most recently introduced binding has index 0. Since parameters are processed left-to-right, the rightmost parameter is "most recently introduced."

## 5.4 Contract Clauses

Every function MUST have at least one `requires` clause and one `ensures` clause. The trivial contract is:

```
requires(true)
ensures(true)
```

This states no preconditions and no postconditions. While permitted, the compiler SHOULD emit a note suggesting that the contracts could be strengthened.

Contract syntax and semantics are detailed in Chapter 6.

## 5.5 Effect Declaration

Every function MUST declare its effects:

```
effects(pure)                           -- no effects
effects(<IO>)                           -- performs IO
effects(<IO, State<Int>>)               -- performs IO and uses Int state
effects(<E>)                            -- polymorphic over effect E
effects(<IO, E>)                        -- performs IO plus additional effects E
```

A function that declares `effects(pure)` MUST NOT perform any effects in its body. A function that declares `effects(<IO>)` may perform IO operations but no other effects.

Effect syntax and semantics are detailed in Chapter 7.

## 5.6 Recursive Functions

Recursive functions are functions that call themselves (directly or mutually). A recursive function MUST declare a `decreases` clause:

```
public fn factorial(@Nat -> @Nat)
  requires(true)
  ensures(@Nat.result >= 1)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 == 0 then {
    1
  } else {
    let @Nat = @Nat.0 - 1;
    @Nat.1 * factorial(@Nat.0)
  }
}
```

### 5.6.1 Decreases Clauses

The `decreases` clause specifies an expression that must strictly decrease (in a well-founded ordering) on each recursive call. The compiler verifies this:

1. The `decreases` expression is evaluated at function entry.
2. At each recursive call site, the compiler verifies that the `decreases` expression (with the recursive call's arguments substituted) is strictly less than the value at function entry.
3. The expression MUST have a type with a well-founded ordering: `Nat`, `Int` (floored at zero — the runtime check rejects a step whose new value is negative), an algebraic data type (ordered by the structural size of its concrete constructors), or a lexicographic tuple of these. A measure of any other type — `Float64` (no well-founded ordering the runtime can check: values are dense below any floor, and `NaN` and the infinities do not participate in the order at all — a float measure never reaches the runtime check, because `E127` rejects it statically), `String`, `Bool`, a function type — is rejected at check time with `E127`.

Lexicographic decrease:

```
private fn ackermann(@Nat, @Nat -> @Nat)
  requires(true)
  ensures(true)
  decreases(@Nat.1, @Nat.0)
  effects(pure)
{
  if @Nat.1 == 0 then {
    @Nat.0 + 1
  } else {
    if @Nat.0 == 0 then {
      ackermann(@Nat.1 - 1, 1)
    } else {
      ackermann(@Nat.1 - 1, ackermann(@Nat.1, @Nat.0 - 1))
    }
  }
}
```

The tuple `(@Nat.1, @Nat.0)` decreases lexicographically on each recursive call.

**Runtime checking.** Whenever the backend can generate a supported guard — the exclusions are listed below (a parameterized or indirectly parameterized ADT measure, a function declaring `Exn`, a measure the backend cannot translate) — a `decreases` clause is also enforced at run time, for every function regardless of its static tier: for a Tier 3 obligation (`E525`) the guard is the promised fallback, and for a proved obligation it is belt-and-braces against any divergence between the proof and the machine. The measure is evaluated with machine 64-bit arithmetic, so a measure expression whose value exceeds the i64 range traps through the overflow channel even when the static proof (over unbounded integers) succeeded. For a guarded function, on each re-entry, the measure — an ADT component through its structural size — is compared with the previous activation's. A scalar measure MUST be strictly less than the previous value and non-negative. For a lexicographic tuple, the first component that differs MUST be strictly less than its previous value and non-negative, with every earlier component equal; later components are unconstrained on that hop — each is checked on the hop where it becomes the deciding component. A violating re-entry traps through the contract-violation channel with a message naming the function, so a non-terminating recursion in a guarded function fails loudly instead of hanging; an excluded function's obligation remains disclosed by the static tier only. Two consequences of the mechanism:

- Tail-call optimization is preserved for self-recursion: a self-recursive tail call keeps its `return_call`, with the hop checked at the call site (the arguments are captured, the measure evaluated over them and compared against the live chain state, and this activation's guard state closed out before the transfer), so guarded iteration runs at constant stack depth — when the call-site check can be generated; a self-tail site whose measure the backend cannot express at the site lowers to a plain call instead, still guarded at entry, at native stack depth. A *mutually*-recursive tail call between two guarded functions lowers to a plain call instead — with the frame elided there is no placement of the state restore that both preserves the chain and unwinds it — so that corner is bounded by the native stack, which the measure itself bounds.
- An ADT measure is runtime-checked only when its type's reachable field structure is fully concrete. A measure whose type is parameterized (`List<Int>`), or whose fields reach a parameterized type, is not yet runtime-ranked. Static verification still classifies the obligation as usual — a provable measure stays Tier 1; what is absent is the runtime fallback for an obligation the prover cannot discharge (Tier 3).
- A function whose effect row declares `Exn` receives no runtime guard: a thrown exception unwinds past the exit restores, and the stale chain state would make a later, unrelated call trap a terminating program. Static verification still classifies the obligation as usual; only the runtime fallback is absent.

### 5.6.2 Mutual Recursion

Mutually recursive functions are declared together in a `where` block. Each must have its own `decreases` clause:

```
public fn is_even(@Nat -> @Bool)
  requires(true)
  ensures(true)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 == 0 then {
    true
  } else {
    is_odd(@Nat.0 - 1)
  }
}
where {
  fn is_odd(@Nat -> @Bool)
    requires(true)
    ensures(true)
    decreases(@Nat.0)
    effects(pure)
  {
    if @Nat.0 == 0 then {
      false
    } else {
      is_even(@Nat.0 - 1)
    }
  }
}
```

A helper's **name** is scoped to its parent as well: it is callable from that function's body and contracts, from any closure or handler clause inside them, and from the parent's other helpers — and from nowhere else. A bare call naming a helper anywhere else is rejected (**E178**) — in the declaring file, and in a file that imports the parent's module, where the helper is no more callable than it is next door. A helper cannot be imported either (**E150**), being no part of that module's namespace. Where the name is also an effect operation's, a call outside the parent resolves the operation, by the ordinary bare-call rule (§7.4).

A `where`-helper is a closed, param-rooted scope: its body resolves slot references only against its **own** parameters, never the outer function's. The outer function's parameter slots are not in scope inside a helper — everything a helper needs must be passed as an explicit argument (a helper's mandatory contract covers only its own parameters, so an implicit outer-frame capture would move a value across a contract boundary). Reading an outer parameter slot from a helper body is an unresolved-slot error (E130). The parent's `forall` **type** parameters remain in scope, so a helper of a generic parent may still be written over `@T`; only value slots are isolated.

## 5.7 Anonymous Functions (Closures)

Anonymous functions (lambdas/closures) use the same `fn` keyword without a name:

```
fn(@Int -> @Int) effects(pure) {
  @Int.0 + 1
}
```

Anonymous functions:
- Do not have a name
- Do not have explicit contracts (they inherit the safety guarantees of their type)
- MUST declare their effects
- Can capture bindings from enclosing scopes (closures)

### 5.7.1 Closure Capture

Anonymous functions capture bindings from enclosing scopes by reference. The captured bindings are immutable (since all bindings in Vera are immutable):

<!-- vera:skip-parse category="FRAGMENT" reason="fn make_adder returns fn(...) inline" -->
```
private fn make_adder(@Int -> fn(Int -> Int) effects(pure))
  requires(true)
  ensures(true)
  effects(pure)
{
  fn(@Int -> @Int) effects(pure) {
    @Int.0 + @Int.1    -- @Int.1 captures the outer parameter
  }
}
```

### 5.7.2 Typed Closures in Arguments

When passing closures to higher-order functions:

```
type IntPred = fn(Int -> Bool) effects(pure);

private fn filter_positive(@Array<Int> -> @Array<Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  array_filter(@Array<Int>.0, fn(@Int -> @Bool) effects(pure) { @Int.0 > 0 })
}
```

## 5.8 Function Visibility

Every top-level `fn` and `data` declaration MUST have an explicit visibility modifier: either `public` or `private`. There is no default visibility. Omitting the modifier is a compile error. This enforces design principle 3 ("one canonical form"): every declaration has exactly one valid shape, eliminating ambiguity about whether an unadorned `fn` is public or private.

```
public fn add(@Int, @Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0 + @Int.1)
  effects(pure)
{
  @Int.0 + @Int.1
}

private fn helper(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0 + 1
}
```

`public` functions are visible to importing modules. `private` functions are visible only within their own module.

The same rule applies to `data` declarations:

```
public data Color {
  Red,
  Green,
  Blue
}

private data InternalState {
  Active(Int),
  Idle
}
```

For generic functions, the visibility modifier precedes `forall`:

```
private forall<T> fn identity(@T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{
  @T.0
}
```

Type aliases (`type Foo = ...`), effect declarations (`effect E { ... }`), module declarations, and import statements do not take visibility modifiers. Functions declared inside `where` blocks do not take visibility modifiers (they are always local to the parent function).

For the full module system — imports, resolution, cross-module type checking, verification, and compilation — see Chapter 8.

## 5.9 Generic Functions

Functions may be parameterised by type variables using `forall`:

```
private forall<T> fn identity(@T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{
  @T.0
}
```

```
private forall<A, B> fn pair(@A, @B -> @Tuple<A, B>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Tuple(@A.0, @B.0)
}
```

Type variables are introduced by `forall<...>` and are scoped to the entire function declaration (including contracts and body).

### 5.9.1 Effect-Polymorphic Functions

Functions can be polymorphic over effects:

<!-- vera:skip-parse category="FRAGMENT" reason="fn(A -> B) in param position" -->
```
private forall<A, B> fn option_map(@Option<A>, fn(A -> B) effects(<E>) -> @Option<B>)
  requires(true)
  ensures(true)
  effects(<E>)
{
  match @Option<A>.0 {
    Some(@A) -> Some(apply_fn(@Fn.0, @A.0)),
    None -> None,
  }
}
```

The stored function value is applied with `apply_fn` (Section 11.10.5). The effect variable `E` means: "whatever effects the function argument has, this function also has."

## 5.10 Function Type Summary

The type of a function with parameters `P1, P2, ..., Pn`, return type `R`, and effects `E` is:

```
Fn(@P1, @P2, ..., @Pn -> @R) effects(<E>)
```

Functions are first-class values. They can be:
- Passed as arguments
- Returned from other functions
- Stored in data structures
- Applied to arguments

## 5.11 Entry Point

A Vera program's entry point is a function named `main`:

```
public fn main(@Unit -> @Unit)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  IO.print("Hello, Vera!");
  ()
}
```

The `main` function:
- MUST have the signature `fn main(@Unit -> @Unit)`
- MUST declare `effects(<IO>)` (or any superset)
- Is the only function that may declare IO effects without being called by another IO function
- Every program MUST have exactly one `main` function (in the root module)
