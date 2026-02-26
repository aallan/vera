---
name: vera-language
description: Write programs in the Vera programming language. Use when asked to write, edit, debug, or review Vera code (.vera files). Vera is a statically typed, purely functional language with algebraic effects, mandatory contracts, and typed slot references (@T.n) instead of variable names.
---

# Vera Language Reference

Vera is a programming language designed for LLMs to write. It uses typed slot references instead of variable names, requires contracts on every function, and makes all effects explicit.

## Toolchain

```bash
vera check file.vera              # Parse and type-check (or "OK")
vera check --json file.vera       # Type-check with JSON diagnostics
vera typecheck file.vera          # Same as check (explicit alias)
vera verify file.vera             # Type-check and verify contracts via Z3
vera verify --json file.vera      # Verify with JSON diagnostics
vera compile file.vera            # Compile to .wasm binary
vera compile --wat file.vera      # Print WAT text (human-readable WASM)
vera compile --json file.vera     # Compile with JSON diagnostics
vera run file.vera                # Compile and execute (calls main)
vera run file.vera --fn f -- 42   # Call function f with argument 42
vera run --json file.vera         # Run with JSON output
vera parse file.vera              # Print the parse tree
vera ast file.vera                # Print the typed AST
vera ast --json file.vera         # Print the AST as JSON
pytest tests/ -v                  # Run the test suite
```

Errors are natural language instructions explaining what went wrong and how to fix it. Feed them back into your context to correct the code.

### JSON diagnostics

Use `--json` on `check` or `verify` for machine-readable output:

```json
{"ok": true, "file": "...", "diagnostics": [], "warnings": []}
```

On error, each diagnostic includes `severity`, `description`, `location` (`file`, `line`, `column`), `source_line`, `rationale`, `fix`, and `spec_ref`. The `verify --json` output also includes a `verification` summary with `tier1_verified`, `tier3_runtime`, and `total` counts.

## Function Structure

Every function has this exact structure. No part is optional except `decreases` and `where`.

```vera
fn function_name(@ParamType1, @ParamType2 -> @ReturnType)
  requires(precondition_expression)
  ensures(postcondition_expression)
  effects(effect_row)
{
  body_expression
}
```

Complete example:

```vera
fn safe_divide(@Int, @Int -> @Int)
  requires(@Int.1 != 0)
  ensures(@Int.result == @Int.0 / @Int.1)
  effects(pure)
{
  @Int.0 / @Int.1
}
```

Multiple `requires` and `ensures` clauses are allowed. They are conjunctive (AND'd together):

```vera
fn clamp(@Int, @Int, @Int -> @Int)
  requires(@Int.1 <= @Int.2)
  ensures(@Int.result >= @Int.1)
  ensures(@Int.result <= @Int.2)
  effects(pure)
{
  if @Int.0 < @Int.1 then {
    @Int.1
  } else {
    if @Int.0 > @Int.2 then {
      @Int.2
    } else {
      @Int.0
    }
  }
}
```

## Slot References (@T.n)

Vera has no variable names. Every binding is referenced by type and index:

```
@Type.index
```

- `@` is the slot reference prefix (mandatory)
- `Type` is the exact type of the binding, starting with uppercase
- `.index` is the zero-based De Bruijn index (0 = most recent binding of that type)

### Parameter ordering

Parameters bind left-to-right. The **rightmost** parameter of a given type is `@T.0`:

```vera
fn add(@Int, @Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0 + @Int.1)
  effects(pure)
{
  @Int.0 + @Int.1
}
-- @Int.0 = second parameter (rightmost Int)
-- @Int.1 = first parameter (leftmost Int)
```

### Mixed types

Each type has its own index counter:

```vera
fn repeat(@String, @Int -> @String)
  requires(@Int.0 >= 0)
  ensures(true)
  effects(pure)
{
  string_repeat(@String.0, @Int.0)
}
-- @String.0 = first parameter (only String)
-- @Int.0 = second parameter (only Int)
```

### Let bindings push new slots

```vera
fn example(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Int = @Int.0 * 2;     -- @Int.0 here refers to the parameter
  let @Int = @Int.0 + 1;     -- @Int.0 here refers to the first let (param * 2)
  @Int.0                      -- refers to the second let (param * 2 + 1)
}
```

### @T.result

Only valid inside `ensures` clauses. Refers to the function's return value:

```vera
fn abs(@Int -> @Nat)
  requires(true)
  ensures(@Nat.result >= 0)
  effects(pure)
{
  if @Int.0 >= 0 then { @Int.0 } else { -@Int.0 }
}
```

### Index is mandatory

`@Int` alone is not a valid reference. Always write `@Int.0`, `@Int.1`, etc.

## Types

### Primitive types

- `Bool` — `true`, `false`
- `Int` — signed integers (arbitrary precision)
- `Nat` — natural numbers (non-negative)
- `Float64` / `Float` — 64-bit floating-point
- `String` — text
- `Unit` — singleton type, value is `()`

### Composite types

```vera
@Array<Int>                              -- array of ints
@Tuple<Int, String>                      -- tuple
@Option<Int>                             -- Option type (Some/None)
Fn(Int -> Int) effects(pure)              -- function type
{ @Int | @Int.0 > 0 }                   -- refinement type
```

### Type aliases

```vera
type PosInt = { @Int | @Int.0 > 0 };
type Name = String;
```

## Data Types (ADTs)

```vera
data Color { Red, Green, Blue }

data List<T> {
  Nil,
  Cons(T, List<T>)
}

data Option<T> { None, Some(T) }
```

With an invariant:

```vera
data Positive invariant(@Int.0 > 0) {
  MkPositive(Int)
}
```

## Pattern Matching

```vera
fn to_int(@Color -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Color.0 {
    Red -> 0,
    Green -> 1,
    Blue -> 2
  }
}
```

Patterns can bind values:

```vera
fn unwrap_or(@Option<Int>, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Option<Int>.0 {
    None -> @Int.0,
    Some(@Int) -> @Int.0
  }
}
```

Available patterns: constructors (`Some(@Int)`), nullary constructors (`None`, `Red`), literals (`0`, `"x"`, `true`), wildcard (`_`).

Match must be exhaustive.

## Conditional Expressions

```vera
if @Bool.0 then { expr1 } else { expr2 }
```

Both branches are mandatory. Braces are mandatory.

## Block Expressions

Blocks contain statements followed by a final expression:

```vera
{
  let @Int = @Int.0 + 1;
  let @String = to_string(@Int.0);
  IO.print(@String.0);
  @Int.0
}
```

Statements end with `;`. The final expression (no `;`) is the block's value.

## Contracts

### requires (preconditions)

Conditions that must hold when the function is called:

```vera
fn safe_divide(@Int, @Int -> @Int)
  requires(@Int.1 != 0)
```

### ensures (postconditions)

Conditions guaranteed when the function returns. Use `@T.result` to refer to the return value:

```vera
  ensures(@Int.result == @Int.0 / @Int.1)
```

### decreases (termination)

Required on recursive functions. The expression must decrease on each recursive call:

```vera
fn factorial(@Nat -> @Nat)
  requires(true)
  ensures(@Nat.result >= 1)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 == 0 then { 1 } else { @Nat.0 * factorial(@Nat.0 - 1) }
}
```

For nested recursion, use lexicographic ordering: `decreases(@Nat.0, @Nat.1)`.

### Quantified expressions

```vera
-- For all indices in [0, bound):
forall(@Nat, length(@Array<Int>.0), fn(@Nat -> @Bool) effects(pure) {
  @Array<Int>.0[@Nat.0] > 0
})

-- There exists an index in [0, bound):
exists(@Nat, length(@Array<Int>.0), fn(@Nat -> @Bool) effects(pure) {
  @Array<Int>.0[@Nat.0] == 0
})
```

## Effects

Vera is pure by default. All side effects must be declared.

### Declaring effects on functions

```vera
effects(pure)                    -- no effects
effects(<IO>)                    -- performs IO
effects(<State<Int>>)            -- uses integer state
effects(<State<Int>, IO>)        -- multiple effects
```

### Effect declarations

```vera
effect Console {
  op print(String -> Unit);
  op read_line(Unit -> String);
}
```

### Performing effects

Call the effect operations directly:

```vera
fn greet(@String -> @Unit)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  IO.print(@String.0);
  ()
}
```

### State effects

```vera
fn increment(@Unit -> @Unit)
  requires(true)
  ensures(new(State<Int>) == old(State<Int>) + 1)
  effects(<State<Int>>)
{
  let @Int = get(());
  put(@Int.0 + 1);
  ()
}
```

In `ensures` clauses, `old(State<T>)` is the state before the call and `new(State<T>)` is the state after.

### Effect handlers

Handlers eliminate an effect, converting effectful code to pure code:

```vera
fn run_counter(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Int>](@Int = 0) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    put(42);
    get(())
  }
}
```

Handler syntax:
```vera
handle[EffectName<TypeArgs>](@StateType = initial_value) {
  operation(@ParamType) -> { handler_body },
  ...
} in {
  handled_body
}
```

Use `resume(value)` in a handler clause to continue the handled computation with the given return value.

### Qualified operation calls

When two effects have operations with the same name, qualify the call:

```vera
State.put(42);
Logger.put("message");
```

## Where Blocks (Mutual Recursion)

```vera
fn is_even(@Nat -> @Bool)
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

## Generic Functions

```vera
forall<T> fn identity(@T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{
  @T.0
}
```

## Modules

```vera
module vera.math;

import vera.collections;
import vera.collections(List, Option);

public fn exported(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0
}
```

Functions are private by default. Add `public` for external visibility.

## Comments

```vera
-- line comment

{- block comment -}

{- block comments {- can nest -} -}
```

## Operators (by precedence, loosest to tightest)

| Precedence | Operators | Associativity |
|------------|-----------|---------------|
| 1 | `\|>` (pipe) | left |
| 2 | `==>` (implies, contracts only) | right |
| 3 | `\|\|` | left |
| 4 | `&&` | left |
| 5 | `==` `!=` | none |
| 6 | `<` `>` `<=` `>=` | none |
| 7 | `+` `-` | left |
| 8 | `*` `/` `%` | left |
| 9 | `!` `-` (unary) | prefix |
| 10 | `[]` (index) `()` (call) | postfix |

## Common Mistakes

### Missing contract block

WRONG:
```vera
fn add(@Int, @Int -> @Int) {
  @Int.0 + @Int.1
}
```

CORRECT:
```vera
fn add(@Int, @Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0 + @Int.1)
  effects(pure)
{
  @Int.0 + @Int.1
}
```

### Missing effects clause

WRONG:
```vera
fn add(@Int, @Int -> @Int)
  requires(true)
  ensures(true)
{
  @Int.0 + @Int.1
}
```

CORRECT — add `effects(pure)` (or the appropriate effect row):
```vera
fn add(@Int, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0 + @Int.1
}
```

### Wrong slot index

WRONG — both `@Int.0` refer to the same binding (the second parameter):
```vera
fn add(@Int, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0 + @Int.0
}
```

CORRECT — `@Int.1` is the first parameter, `@Int.0` is the second:
```vera
fn add(@Int, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0 + @Int.1
}
```

### Missing index on slot reference

WRONG:
```vera
@Int + @Int
```

CORRECT:
```vera
@Int.0 + @Int.1
```

### Missing decreases on recursive function

WRONG:
```vera
fn factorial(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  if @Nat.0 == 0 then { 1 } else { @Nat.0 * factorial(@Nat.0 - 1) }
}
```

CORRECT:
```vera
fn factorial(@Nat -> @Nat)
  requires(true)
  ensures(true)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 == 0 then { 1 } else { @Nat.0 * factorial(@Nat.0 - 1) }
}
```

### Undeclared effects

WRONG — `IO.print` performs IO but function declares `pure`:
```vera
fn greet(@String -> @Unit)
  requires(true)
  ensures(true)
  effects(pure)
{
  IO.print(@String.0);
  ()
}
```

CORRECT:
```vera
fn greet(@String -> @Unit)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  IO.print(@String.0);
  ()
}
```

### Using @T.result outside ensures

WRONG:
```vera
fn f(@Int -> @Int)
  requires(@Int.result > 0)
  ensures(true)
  effects(pure)
{ @Int.0 }
```

CORRECT — `@T.result` is only valid in `ensures`:
```vera
fn f(@Int -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{ @Int.0 }
```

### Non-exhaustive match

WRONG:
```vera
match @Option<Int>.0 {
  Some(@Int) -> @Int.0
}
```

CORRECT:
```vera
match @Option<Int>.0 {
  Some(@Int) -> @Int.0,
  None -> 0
}
```

### Missing braces on if/else branches

WRONG:
```vera
if @Bool.0 then 1 else 0
```

CORRECT:
```vera
if @Bool.0 then { 1 } else { 0 }
```

## Complete Program Examples

### Pure function with postconditions

```vera
fn absolute_value(@Int -> @Nat)
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

### Recursive function with termination proof

```vera
fn factorial(@Nat -> @Nat)
  requires(true)
  ensures(@Nat.result >= 1)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 == 0 then {
    1
  } else {
    @Nat.0 * factorial(@Nat.0 - 1)
  }
}
```

### Stateful effects with old/new

```vera
fn increment(@Unit -> @Unit)
  requires(true)
  ensures(new(State<Int>) == old(State<Int>) + 1)
  effects(<State<Int>>)
{
  let @Int = get(());
  put(@Int.0 + 1);
  ()
}
```

### ADT with pattern matching

```vera
data List<T> {
  Nil,
  Cons(T, List<T>)
}

fn length(@List<Int> -> @Nat)
  requires(true)
  ensures(@Nat.result >= 0)
  decreases(@List<Int>.0)
  effects(pure)
{
  match @List<Int>.0 {
    Nil -> 0,
    Cons(@Int, @List<Int>) -> 1 + length(@List<Int>.0)
  }
}
```

## Specification Reference

The full language specification is in `spec/`:

| Chapter | File | Topic |
|---------|------|-------|
| 0 | `spec/00-introduction.md` | Design goals, diagnostics philosophy |
| 1 | `spec/01-lexical-structure.md` | Tokens, operators, formatting |
| 2 | `spec/02-types.md` | Type system, refinement types |
| 3 | `spec/03-slot-references.md` | The @T.n reference system |
| 4 | `spec/04-expressions.md` | Expressions and statements |
| 5 | `spec/05-functions.md` | Functions and contracts |
| 6 | `spec/06-contracts.md` | Verification system |
| 7 | `spec/07-effects.md` | Algebraic effect system |
| 9 | `spec/09-standard-library.md` | Built-in types, effects, functions |
| 10 | `spec/10-grammar.md` | Formal EBNF grammar |
| 11 | `spec/11-compilation.md` | Compilation model and WASM target |
| 12 | `spec/12-runtime.md` | Runtime execution, host bindings, memory model |
