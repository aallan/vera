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

```
private fn function_name(@ParamType1, @ParamType2 -> @ReturnType)
  requires(precondition)
  ensures(postcondition)
  effects(effect_row)
{
  body_expression
}
```

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
3. The expression must have a type with a well-founded ordering: `Nat`, `Int` (with a precondition that it is non-negative), or a lexicographic tuple.

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
      ackermann(1, @Nat.1 - 1)
    } else {
      ackermann(ackermann(@Nat.0 - 1, @Nat.1), @Nat.1 - 1)
    }
  }
}
```

The tuple `(@Nat.1, @Nat.0)` decreases lexicographically on each recursive call.

### 5.6.2 Mutual Recursion

Mutually recursive functions are declared together in a `where` block. Each must have its own `decreases` clause:

```
public fn is_even(@Nat -> @Bool)
  requires(true)
  ensures(true)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 == 0 then { true } else { is_odd(@Nat.0 - 1) }
}
where {
  fn is_odd(@Nat -> @Bool)
    requires(true)
    ensures(true)
    decreases(@Nat.0)
    effects(pure)
  {
    if @Nat.0 == 0 then { false } else { is_even(@Nat.0 - 1) }
  }
}
```

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

```
private forall<A, B> fn map_option(@Option<A>, fn(A -> B) effects(<E>) -> @Option<B>)
  requires(true)
  ensures(true)
  effects(<E>)
{
  match @Option<A>.0 {
    Some(@A) -> Some(@Fn.0(@A.0)),
    None -> None,
  }
}
```

The effect variable `E` means: "whatever effects the function argument has, this function also has."

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
