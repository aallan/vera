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
vera fmt file.vera                # Format to canonical form (stdout)
vera fmt --write file.vera        # Format in place
vera fmt --check file.vera        # Check if already canonical
pytest tests/ -v                  # Run the test suite
```

Errors are natural language instructions explaining what went wrong and how to fix it. Feed them back into your context to correct the code.

### JSON diagnostics

Use `--json` on `check` or `verify` for machine-readable output:

```json
{"ok": true, "file": "...", "diagnostics": [], "warnings": []}
```

On error, each diagnostic includes `severity`, `description`, `location` (`file`, `line`, `column`), `source_line`, `rationale`, `fix`, `spec_ref`, and `error_code`. The `verify --json` output also includes a `verification` summary with `tier1_verified`, `tier3_runtime`, and `total` counts.

### Error codes

Every diagnostic has a stable error code (`E001`–`E607`) grouped by compiler phase:

- **E001–E007** — Parse errors (missing contracts, unexpected tokens)
- **E010** — Transform errors (internal)
- **E120–E176** — Type check: core + expressions (type mismatches, slot resolution, operators)
- **E200–E233** — Type check: calls (unresolved functions, argument mismatches, module calls)
- **E300–E335** — Type check: control flow (if/match, patterns, effect handlers)
- **E500–E525** — Verification (contract violations, undecidable fallbacks)
- **E600–E607** — Codegen (unsupported features)

Common codes you'll encounter:
- **E130** — Unresolved slot reference (`@T.n` has no matching binding)
- **E121** — Function body type doesn't match return type
- **E200** — Unresolved function call
- **E300** — If condition is not Bool
- **E001** — Missing contract block (requires/ensures/effects)

## Function Structure

Every function has this exact structure. No part is optional except `decreases` and `where`. Visibility (`public` or `private`) is mandatory on every top-level `fn` and `data` declaration.

```vera
private fn function_name(@ParamType1, @ParamType2 -> @ReturnType)
  requires(precondition_expression)
  ensures(postcondition_expression)
  effects(effect_row)
{
  body_expression
}
```

Complete example:

```vera
public fn safe_divide(@Int, @Int -> @Int)
  requires(@Int.1 != 0)
  ensures(@Int.result == @Int.0 / @Int.1)
  effects(pure)
{
  @Int.0 / @Int.1
}
```

## Function Visibility

Every top-level `fn` and `data` declaration **must** have an explicit visibility modifier. There is no default visibility -- omitting it is an error.

- `public` -- the declaration is visible to other modules that import this one. Only `public` functions are exported as WASM entry points (callable via `vera run`). Use for library APIs, exported functions, and program entry points.
- `private` -- the declaration is only visible within the current file/module. Private functions compile but are not WASM exports. Use for internal helpers.

```vera
public fn exported_api(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0
}

private fn internal_helper(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0 + 1
}

public data Color { Red, Green, Blue }

private data InternalState {
  Ready,
  Done(Int)
}
```

For generic functions, visibility comes before `forall`:

```vera
private forall<T> fn identity(@T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{
  @T.0
}
```

Visibility does **not** apply to: type aliases (`type Foo = ...`), effect declarations (`effect E { ... }`), module declarations, or import statements. Functions inside `where` blocks also do not take visibility.

Multiple `requires` and `ensures` clauses are allowed. They are conjunctive (AND'd together):

```vera
private fn clamp(@Int, @Int, @Int -> @Int)
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
private fn add(@Int, @Int -> @Int)
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
private fn repeat(@String, @Int -> @String)
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
private fn example(@Int -> @Int)
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
private fn abs(@Int -> @Nat)
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
- `Float64` — 64-bit IEEE 754 floating-point
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
private data Color { Red, Green, Blue }

private data List<T> {
  Nil,
  Cons(T, List<T>)
}

private data Option<T> { None, Some(T) }
```

With an invariant:

```vera
private data Positive invariant(@Int.0 > 0) {
  MkPositive(Int)
}
```

## Pattern Matching

```vera
private fn to_int(@Color -> @Int)
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
private fn unwrap_or(@Option<Int>, @Int -> @Int)
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
private fn safe_divide(@Int, @Int -> @Int)
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
private fn factorial(@Nat -> @Nat)
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
private fn greet(@String -> @Unit)
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
private fn increment(@Unit -> @Unit)
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
private fn run_counter(@Unit -> @Int)
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
  operation(@ParamType) -> { handler_body } with @StateType = new_value,
  ...
} in {
  handled_body
}
```

Use `resume(value)` in a handler clause to continue the handled computation with the given return value. Optionally update handler state with a `with` clause:

```vera
put(@Int) -> { resume(()) } with @Int = @Int.0
```

The `with @T = expr` clause updates the handler's state when resuming. The type must match the handler's state type declaration.

### Qualified operation calls

When two effects have operations with the same name, qualify the call:

```vera
State.put(42);
Logger.put("message");
```

## Where Blocks (Mutual Recursion)

```vera
private fn is_even(@Nat -> @Bool)
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
private forall<T> fn identity(@T -> @T)
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

Every top-level `fn` and `data` must have explicit `public` or `private` visibility. Use `public` for functions that other modules should be able to import.

Import paths resolve to files on disk: `import vera.math;` looks for `vera/math.vera` relative to the importing file's directory (or the project root). Imported files are parsed and cached automatically. Circular imports are detected and reported as errors.

Imported functions can be called by name (bare calls): `import vera.math(abs); abs(-5)` resolves `abs` from the imported module. Selective imports restrict available names; wildcard imports (`import m;`) make all declarations available. Local definitions shadow imported names. Imported ADT constructors are also available: `import col(List); Cons(1, Nil)`.

Imported function contracts are verified at call sites by the SMT solver. Preconditions of imported functions are checked at each call site; postconditions are assumed. This means `abs(x)` with `ensures(@Int.result >= 0)` lets the caller rely on the result being non-negative.

Cross-module compilation uses a flattening strategy: imported function bodies are compiled into the same WASM module as the importing program. The result is a single self-contained `.wasm` binary. Imported functions are internal (not exported); only the importing program's `public` functions are WASM exports.

Type aliases and effect declarations are module-local and cannot be imported. If another module needs the same alias or effect, it must declare its own copy.

Module-qualified calls use `::` between the module path and the function name: `vera.math::abs(42)`. The dot-separated path identifies the module and `::` separates it from the function name. This syntax can be used anywhere a function call is valid, and always resolves against the specific module's public declarations — it is not affected by local shadowing.

There is no import aliasing (`import m(abs as math_abs)`) and no wildcard exclusion (`import m hiding(x)`). These are intentional design decisions, not limitations. When names clash, use selective imports to pick the names you need, and use `::` syntax to disambiguate: `vera.math::abs(x)`. This preserves the one-canonical-form principle — every function has exactly one name.

There are no raw strings (`r"..."`) or multi-line string literals. Use escape sequences (`\\`, `\n`, `\t`, `\"`) for special characters. This is by design — alternative string syntaxes would create two representations for the same value.

See: spec Chapter 8 for the full module system specification.

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
private fn add(@Int, @Int -> @Int) {
  @Int.0 + @Int.1
}
```

CORRECT:
```vera
private fn add(@Int, @Int -> @Int)
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
private fn add(@Int, @Int -> @Int)
  requires(true)
  ensures(true)
{
  @Int.0 + @Int.1
}
```

CORRECT — add `effects(pure)` (or the appropriate effect row):
```vera
private fn add(@Int, @Int -> @Int)
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
private fn add(@Int, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0 + @Int.0
}
```

CORRECT — `@Int.1` is the first parameter, `@Int.0` is the second:
```vera
private fn add(@Int, @Int -> @Int)
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
private fn factorial(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  if @Nat.0 == 0 then { 1 } else { @Nat.0 * factorial(@Nat.0 - 1) }
}
```

CORRECT:
```vera
private fn factorial(@Nat -> @Nat)
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
private fn greet(@String -> @Unit)
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
private fn greet(@String -> @Unit)
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
private fn f(@Int -> @Int)
  requires(@Int.result > 0)
  ensures(true)
  effects(pure)
{ @Int.0 }
```

CORRECT — `@T.result` is only valid in `ensures`:
```vera
private fn f(@Int -> @Int)
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

### Trying to use import aliasing

WRONG — Vera does not support renaming imports:
```vera
import vera.math(abs as math_abs);
```

CORRECT — use selective import and `::` syntax to disambiguate:
```vera
import vera.math(abs);
vera.math::abs(-5)
```

### Trying to use wildcard exclusion

WRONG — Vera does not support `hiding` syntax:
```vera
import vera.math hiding(max);
```

CORRECT — use selective import to list the names you need:
```vera
import vera.math(abs, min);
```

### Trying to use raw or multi-line strings

WRONG — Vera does not support raw strings or multi-line literals:
```
r"path\to\file"
"""multi-line
string"""
```

CORRECT — use escape sequences:
```vera
"path\\to\\file"
"line one\nline two"
```

## Complete Program Examples

### Pure function with postconditions

```vera
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

### Recursive function with termination proof

```vera
public fn factorial(@Nat -> @Nat)
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
public fn increment(@Unit -> @Unit)
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
private data List<T> {
  Nil,
  Cons(T, List<T>)
}

public fn length(@List<Int> -> @Nat)
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
