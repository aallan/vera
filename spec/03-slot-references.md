# Chapter 3: Slot References

## 3.1 Overview

Vera does not have variable names. Instead, every binding is referenced by its **type** and a **positional index** that counts bindings of the same type, from the innermost (most recent) binding outward. This system is called **typed slot references**.

The syntax for a slot reference is:

```
@T.n
```

Where:
- `@` is the slot reference prefix
- `T` is the exact type of the binding (including type parameters)
- `.n` is the zero-based De Bruijn index, counting only bindings of type `T`

`@Int.0` refers to the nearest (most recently bound) `Int` value. `@Int.1` refers to the next nearest, and so on.

## 3.2 Rationale

Traditional variable names serve two purposes:
1. **Binding**: associating a value with a location in the environment
2. **Reference**: retrieving a value from the environment

For human programmers, meaningful names ("width", "height") aid comprehension. For LLMs, arbitrary names introduce a coherence burden: the model must consistently use the same name across an entire scope, and must choose names that don't collide. Naming errors are among the most common LLM code generation failures.

Typed slot references eliminate this burden. The model needs only to know:
- What type of value it wants
- How many bindings of that type exist between here and the target

Both pieces of information are locally determinable — the model does not need to maintain global naming consistency.

## 3.3 Binding Sites

A binding is introduced at each of the following positions:

1. **Function parameters**: each parameter introduces a binding of its declared type.
2. **Let expressions**: `let @T = expr;` introduces a binding of type `T`.
3. **Match arms**: pattern variables in match arms introduce bindings.
4. **Effect handler parameters**: each operation in a handler introduces bindings for its parameters.
5. **Tuple destructuring**: `let Tuple<@T1, @T2> = expr;` introduces one binding per component.

Binding sites are ordered by textual position. Within a single scope, earlier bindings have higher indices (they are farther away):

```
let @Int = 10;    -- within subsequent code: @Int.1
let @Int = 20;    -- within subsequent code: @Int.0
@Int.0 + @Int.1   -- evaluates to 20 + 10 = 30
```

## 3.4 Reference Resolution

To resolve `@T.n`, the compiler:

1. Starting from the reference site, walks outward through enclosing scopes.
2. Counts each binding whose type is exactly `T` (after alias resolution for subtyping, but exact match for reference resolution — see Section 3.8).
3. The `n`th such binding (zero-indexed) is the referent.
4. If fewer than `n + 1` bindings of type `T` are in scope, the reference is a compile error.

### 3.4.1 Scope Ordering

Scopes are nested. Inner scopes are searched before outer scopes:

```
fn(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(@Int.result > 0)
  effects(pure)
{
  let @Int = @Int.0 + 1;   -- @Int.0 on the RHS refers to the parameter
  @Int.0                    -- this @Int.0 refers to the let binding (value: param + 1)
}
```

In this example:
- The function parameter is an `Int` binding.
- On the RHS of the `let`, `@Int.0` refers to the parameter (the only `Int` in scope).
- After the `let`, there are two `Int` bindings: the `let` binding (`@Int.0`) and the parameter (`@Int.1`).
- The final `@Int.0` evaluates to the `let` binding.

## 3.5 Worked Examples

### Example 1: Simple Function

```
private fn add(@Int, @Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0 + @Int.1)
  effects(pure)
{
  @Int.0 + @Int.1
}
```

Bindings in scope within the body:
- `@Int.0` = second parameter (nearer, introduced second in parameter list)
- `@Int.1` = first parameter (farther, introduced first)

**Note**: Function parameters are ordered such that the **last** parameter is `@T.0` and the **first** parameter is `@T.{n-1}`. This matches De Bruijn convention: the most recently bound variable has index 0.

**Wait — this is confusing.** Let's establish a clear convention:

**Convention**: Parameters are bound left-to-right. The leftmost parameter is bound first (outermost). The rightmost parameter is bound last (innermost). Therefore, in a function `fn(@Int, @Int, @String -> ...)`:
- The rightmost `@Int` (second parameter) is `@Int.0`
- The leftmost `@Int` (first parameter) is `@Int.1`
- The `@String` (third parameter) is `@String.0`

This follows standard De Bruijn indexing where the most recently introduced binding has index 0.

### Example 2: Mixed Types

```
fn(@Int, @String, @Int -> @String)
  requires(@Int.0 > @Int.1)
  ensures(length(@String.result) > 0)
  effects(pure)
{
  concat(to_string(@Int.1), @String.0, to_string(@Int.0))
}
```

Bindings (innermost first):
- `@Int.0` = third parameter (the rightmost `Int`)
- `@String.0` = second parameter
- `@Int.1` = first parameter

In `requires(@Int.0 > @Int.1)`: the third parameter must be greater than the first parameter.

### Example 3: Nested Let Bindings

```
fn(@Int -> @Int)
  requires(@Int.0 >= 0)
  ensures(@Int.result >= 0)
  effects(pure)
{
  let @Int = @Int.0 * 2;
  let @Int = @Int.0 + 1;
  let @String = to_string(@Int.0);
  @Int.0
}
```

Trace:
1. Function body entered. `@Int.0` = parameter.
2. `let @Int = @Int.0 * 2;` — RHS: `@Int.0` = parameter. Now in scope: `@Int.0` = this let (param * 2), `@Int.1` = parameter.
3. `let @Int = @Int.0 + 1;` — RHS: `@Int.0` = previous let (param * 2). Now in scope: `@Int.0` = this let (param * 2 + 1), `@Int.1` = previous let (param * 2), `@Int.2` = parameter.
4. `let @String = to_string(@Int.0);` — `@Int.0` = most recent Int let (param * 2 + 1). `@String` binding added.
5. `@Int.0` = most recent Int let = param * 2 + 1. This is the return value.

### Example 4: Pattern Matching

```
fn(@Option<Int> -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{
  match @Option<Int>.0 {
    Some(@Int) -> @Int.0,
    None -> 0,
  }
}
```

In the `Some` arm:
- `@Int.0` = the unwrapped integer from the `Some` variant.
- The function parameter `@Option<Int>` is still accessible as `@Option<Int>.0`.

In the `None` arm:
- No new bindings are introduced.

### Example 5: Nested Functions (Closures)

```
fn(@Int -> Fn(@Int -> @Int) effects(pure))
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{
  fn(@Int -> @Int) effects(pure) {
    @Int.0 + @Int.1
  }
}
```

In the inner function body:
- `@Int.0` = inner function's parameter
- `@Int.1` = outer function's parameter (captured from enclosing scope)

### Example 6: Tuple Destructuring

```
fn(@Tuple<Int, String, Bool> -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{
  let Tuple<@Int, @String, @Bool> = @Tuple<Int, String, Bool>.0;
  if @Bool.0 then {
    @Int.0 + length(@String.0)
  } else {
    0
  }
}
```

After destructuring:
- `@Int.0` = first component of the tuple
- `@String.0` = second component
- `@Bool.0` = third component

### Example 7: Recursive Function with Decreases

```
private fn factorial(@Nat -> @Nat)
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

In the else branch after the let:
- `@Nat.0` = the let binding (parameter - 1)
- `@Nat.1` = the function parameter

### Example 8: Higher-Order Functions

```
private fn map_array<A, B>(@Array<A>, fn(A -> B) effects(pure) -> @Array<B>)
  requires(true)
  ensures(length(@Array<B>.result) == length(@Array<A>.0))
  effects(pure)
{
  -- implementation uses built-in array mapping primitive
  array_map(@Array<A>.0, @Fn<A, B>.0)
}
```

Here `@Array<A>.0` refers to the first argument and `@Fn<A, B>.0` is a shorthand for the function argument (see Section 3.7).

### Example 9: ADT Construction and Matching

```
private data List<T> {
  Cons(T, List<T>),
  Nil
}

private fn list_head<T>(@List<T> -> @Option<T>)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @List<T>.0 {
    Cons(@T, @List<T>) -> Some(@T.0),
    Nil -> None,
  }
}
```

In the `Cons` arm:
- `@T.0` = the head element
- `@List<T>.0` = the tail (innermost `List<T>`, from the pattern) — note this shadows the function parameter

### Example 10: Multiple Return-Type References in Contracts

```
private fn clamp(@Int, @Int, @Int -> @Int)
  requires(@Int.2 <= @Int.1)
  ensures(@Int.result >= @Int.2 && @Int.result <= @Int.1)
  effects(pure)
{
  if @Int.0 < @Int.2 then {
    @Int.2
  } else {
    if @Int.0 > @Int.1 then {
      @Int.1
    } else {
      @Int.0
    }
  }
}
```

Parameters (rightmost = index 0):
- `@Int.0` = third parameter (the value to clamp)
- `@Int.1` = second parameter (maximum)
- `@Int.2` = first parameter (minimum)

The contract says: minimum <= maximum (precondition), and the result is between minimum and maximum (postcondition).

## 3.6 The `@result` Reference

In postcondition (`ensures`) clauses, the special reference `@T.result` refers to the function's return value, where `T` is the return type.

```
fn(@Int -> @Int)
  ensures(@Int.result > @Int.0)
  effects(pure)
```

`@Int.result` is only valid in `ensures` clauses. It is a compile error to use it elsewhere.

If the return type is a compound type:

```
fn(@Int -> @Tuple<Int, String>)
  ensures(@Int.result.0 > @Int.0)
```

Here `@Tuple<Int, String>.result` refers to the entire return tuple, and `.0` accesses its first component. The shorthand `@Int.result.0` is NOT valid — use the full tuple type.

## 3.7 Function Type References

Function-type parameters use the same `@T.n` system, where `T` is the full function type. Since function types can be long, a type alias is recommended:

```
type IntTransform = fn(Int -> Int) effects(pure);

private fn apply_to_array(@Array<Int>, @IntTransform -> @Array<Int>)
  requires(length(@Array<Int>.0) > 0)
  ensures(length(@Array<Int>.result) == length(@Array<Int>.0))
  effects(pure)
{
  array_map(@Array<Int>.0, @IntTransform.0)
}
```

## 3.8 Type Alias and Reference Resolution

Type aliases are **not transparent** for reference resolution. This is a critical rule:

```
type PosInt = { @Int | @Int.0 > 0 };

fn(@PosInt, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @PosInt.0 + @Int.0
}
```

Here `@PosInt.0` refers to the first parameter and `@Int.0` refers to the second parameter. They are in separate reference namespaces despite `PosInt` being a refinement of `Int`.

Rationale: If aliases were transparent, adding a type alias to a library could silently change the meaning of `@Int.0` in user code by splitting the `Int` namespace. Opaque alias resolution prevents this class of errors.

## 3.9 Index Elision

When there is exactly one binding of a given type in scope, the `.0` index MAY be elided:

```
fn(@Int, @String -> @String)
  requires(length(@String) > 0)    -- @String is unambiguous: only one String in scope
  ensures(length(@String.result) > @Int)  -- @Int is also unambiguous
  effects(pure)
```

**No.** In keeping with the "one canonical form" principle, the index MUST always be present. `@String.0` is the only valid form, never `@String`. This eliminates any ambiguity and maintains the invariant that all slot references have the same syntactic structure.

## 3.10 Scope Summary

| Construct | Bindings introduced | Scope of bindings |
|-----------|--------------------|--------------------|
| Function parameter | One per parameter | Function body and contract clauses |
| `let @T = expr;` | One of type `T` | Subsequent statements in the same block |
| `match` arm pattern | One per pattern variable | The arm's body expression |
| Tuple destructuring | One per component | Subsequent statements in the same block |
| Effect handler op | One per operation parameter | The operation's handler body |
| `forall<A>` | Type variable `A` | The entire declaration |

## 3.11 Error Cases

The compiler MUST reject the following:

1. **Unresolvable reference**: `@Int.2` when fewer than 3 `Int` bindings are in scope.
2. **Type mismatch**: `@String.0` used where an `Int` is expected.
3. **`@result` outside `ensures`**: using `@T.result` anywhere other than a postcondition clause.
4. **Ambiguous compound reference**: a slot reference to a type that doesn't exist in scope.

Each error MUST include:
- The source location of the reference
- The type and index referenced
- The bindings actually in scope (listed with their types and indices)
