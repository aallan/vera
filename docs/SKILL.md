---
name: vera-language
description: Write programs in the Vera programming language. Use when asked to write, edit, debug, or review Vera code (.vera files). Vera is a statically typed, purely functional language with algebraic effects, mandatory contracts, and typed slot references (@T.n) instead of variable names.
---

# Vera Language Reference

Vera is a programming language designed for LLMs to write. It uses typed slot references instead of variable names, requires contracts on every function, and makes all effects explicit.

## Installation

Vera requires Python 3.11 or later. Node.js 22+ is optional (only needed for `vera compile --target browser` and browser parity tests). Install from the repository:

```bash
git clone https://github.com/aallan/vera.git && cd vera
python -m venv .venv && source .venv/bin/activate
pip install -e .
```

This installs the `vera` command and all runtime dependencies (Lark parser, Z3 solver, wasmtime). After installation, verify it works:

```bash
vera check examples/hello_world.vera    # should print "OK: examples/hello_world.vera"
vera run examples/hello_world.vera      # should print "Hello, World!"
```

If you are working on the compiler itself, install development dependencies too:

```bash
pip install -e ".[dev]"
```

## Toolchain

```bash
vera check file.vera              # Parse and type-check (or "OK")
vera check --json file.vera       # Type-check with JSON diagnostics
vera check --quiet file.vera      # Type-check, suppress success output (errors still shown)
vera typecheck file.vera          # Same as check (explicit alias)
vera verify file.vera             # Type-check and verify contracts via Z3
vera verify --json file.vera      # Verify with JSON diagnostics
vera verify --quiet file.vera     # Verify, suppress success output (errors still shown)
vera compile file.vera                    # Compile to .wasm binary
vera compile --wat file.vera              # Print WAT text (human-readable WASM)
vera compile --json file.vera             # Compile with JSON diagnostics
vera compile --target browser file.vera   # Compile + emit browser bundle (wasm + JS + html)
vera run file.vera                # Compile and execute (calls main)
vera run file.vera --fn f -- 42         # Call function f with Int argument
vera run file.vera --fn f -- 3.14       # Call function f with Float64 argument
vera run file.vera --fn f -- true       # Call function f with Bool argument
vera run file.vera --fn f -- "hello"    # Call function f with String argument
vera run --json file.vera         # Run with JSON output
vera test file.vera               # Contract-driven testing via Z3 + WASM
vera test --json file.vera        # Test with JSON output
vera test --trials 50 file.vera   # Limit trials per function (default 100)
vera test file.vera --fn f        # Test a single function
vera parse file.vera              # Print the parse tree
vera ast file.vera                # Print the typed AST
vera ast --json file.vera         # Print the AST as JSON
vera fmt file.vera                # Format to canonical form (stdout)
vera fmt --write file.vera        # Format in place
vera fmt --check file.vera        # Check if already canonical
vera version                      # Print the installed version (also --version, -V)
pytest tests/ -v                  # Run the test suite
```

Errors are natural language instructions explaining what went wrong and how to fix it. Feed them back into your context to correct the code.

`vera test` generates Z3 inputs for `Int`, `Nat`, `Bool`, `Byte`, `String`, and `Float64` parameters. Functions with ADT or function-type parameters are skipped with a message naming the specific type. Float64 uses Z3's mathematical reals (NaN, ±∞, and subnormals are not generated). Strings are capped at 50 characters.

### Browser compilation

`vera compile --target browser` produces a ready-to-serve browser bundle:

```bash
vera compile --target browser file.vera            # Output to file_browser/
vera compile --target browser file.vera -o dist/   # Output to dist/
```

This generates three files: `module.wasm` (the compiled binary), `vera-runtime.mjs` (self-contained JavaScript runtime with all host bindings), and `index.html` (loads and runs the program). Serve the output directory with any HTTP server (`python -m http.server`) and open `index.html` — ES module imports require HTTP, not `file://`.

The JavaScript runtime provides browser-appropriate implementations: `IO.print` writes to the page, `IO.read_line` uses `prompt()`, `IO.stderr` captures into a separate buffer, `IO.time` uses `Date.now()`, `IO.sleep` busy-waits (main-thread blocking — best kept short in the browser), and file IO returns `Result.Err`. All other operations (State, contracts, Markdown) work identically to the Python runtime.

To run the WASM directly in Node.js:

```bash
node --experimental-wasm-exnref vera/browser/harness.mjs module.wasm
```

### JSON diagnostics

Use `--json` on `check` or `verify` for machine-readable output:

```json
{"ok": true, "file": "...", "diagnostics": [], "warnings": []}
```

On error, each diagnostic includes `severity`, `description`, `location` (`file`, `line`, `column`), `source_line`, `rationale`, `fix`, `spec_ref`, and `error_code`. The `verify --json` output also includes a `verification` summary with `tier1_verified`, `tier3_runtime`, and `total` counts.

### Error codes

Every diagnostic has a stable error code grouped by compiler phase:

- **W001** — Typed hole (`?`) — expected type and available bindings reported (warning, not error)
- **E001–E007** — Parse errors (missing contracts, unexpected tokens)
- **E010** — Transform errors (internal)
- **E120–E176** — Type check: core + expressions (type mismatches, slot resolution, operators)
- **E200–E233** — Type check: calls (unresolved functions, argument mismatches, module calls)
- **E300–E335** — Type check: control flow (if/match, patterns, effect handlers)
- **E500–E525** — Verification (contract violations, undecidable fallbacks)
- **E600–E614** — Codegen (unsupported features, typed holes block compilation)
- **E700–E702** — Testing (contract violations, input generation, execution errors)

Common codes you'll encounter:
- **W001** — Typed hole: fill `?` with an expression of the stated type
- **E130** — Unresolved slot reference (`@T.n` has no matching binding)
- **E121** — Function body type doesn't match return type
- **E200** — Unresolved function call
- **E300** — If condition is not Bool
- **E001** — Missing contract block (requires/ensures/effects)
- **E614** — Program contains typed holes; compile rejected until holes are filled

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

### Nullary and Unit-taking functions

Vera accepts two equivalent shapes for functions that take no meaningful argument:

```vera
public fn a(-> @Int)        requires(true) ensures(true) effects(pure) { 42 }
public fn b(@Unit -> @Int)  requires(true) ensures(true) effects(pure) { 42 }
```

At every call site the arity must match the declaration: `a()` calls the nullary form, `b(())` passes a `Unit` value to the Unit-taking form. They cannot be mixed — `a(())` and `b()` are both type errors. Use the nullary form for constants and computations that have no conceptual input; use the Unit-taking form when you want to match the shape of a combinator that expects a `Fn(T -> U)` (the callee side of `apply_fn`, see below) or when the program's entry point traditionally takes `Unit`. `main` works either way; all examples in this file use `main(@Unit -> @Unit)` for consistency with the broader spec.

### Stored function values and `apply_fn`

Functions passed as arguments or stored in `let` bindings use the type form `Fn(T -> U) effects(...)`. To invoke such a stored value, use `apply_fn`:

```vera
type IntToInt = Fn(Int -> Int) effects(pure)

private fn use_fn(@IntToInt, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  apply_fn(@IntToInt.0, @Int.0)
}
```

`apply_fn(f, x)` is the only way to call a function that's stored as a value — direct application syntax (`f(x)`) is reserved for declared names. The prelude uses this pattern for `option_map`, `option_and_then`, `result_map` etc., where the mapping function is a parameter. See `examples/closures.vera` and `tests/conformance/ch05_closures.vera` for worked examples.

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

public data Color {
  Red,
  Green,
  Blue
}

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

**De Bruijn slot ordering is the most common source of bugs in Vera programs.** Before writing contracts, `ensures` clauses, or body expressions that involve multiple parameters of the same type, run `vera check --explain-slots` to confirm which index maps to which parameter. Do not rely on intuition.

Vera has no variable names. Every binding is referenced by type and index. See [`DE_BRUIJN.md`](https://github.com/aallan/vera/blob/main/DE_BRUIJN.md) for the academic background, deeper examples, and the commutative-operations trap.

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
  if @Int.0 >= 0 then {
    @Int.0
  } else {
    -@Int.0
  }
}
```

### Index is mandatory

`@Int` alone is not a valid reference. Always write `@Int.0`, `@Int.1`, etc.

### Debugging slot indices with --explain-slots

**Always run `vera check --explain-slots` before writing contracts or function calls that
involve multiple parameters of the same type.** This is the single most reliable way to avoid
De Bruijn ordering mistakes.

```bash
vera check --explain-slots your_file.vera
```

Output:

```text
Slot environments (index 0 = last occurrence in signature):

  fn divide(@Int, @Int -> @Int)
    @Int.0  parameter 2 (last @Int)
    @Int.1  parameter 1 (first @Int)
```

**Read this table before writing any contract or recursive call.** The ordering only matters
when a function has multiple parameters of the same type — but that is exactly when bugs occur.

Example: for `fn divide(@Int, @Int -> @Int)`, the contract `requires(@Int.1 != 0)` guards the
*first* parameter (the divisor). Confirm this by checking the table: `@Int.1 = parameter 1
(first @Int)`.

**Workflow:**
1. Write the function signature.
2. Run `vera check --explain-slots` to get the slot table.
3. Use the table to write contracts and body expressions with correct `@T.n` indices.
4. If `vera check` reports E130 (unresolved slot), re-read the table — you have the wrong index.

The `--json` flag also works: `vera check --explain-slots --json` emits a `slot_environments`
array, useful when processing diagnostics programmatically.

## Types

### Primitive types

- `Bool` — `true`, `false`
- `Int` — signed integers (arbitrary precision)
- `Nat` — natural numbers (non-negative)
- `Float64` — 64-bit IEEE 754 floating-point
- `Byte` — unsigned 8-bit integer (0–255)
- `String` — text
- `Unit` — singleton type, value is `()`
- `Never` — bottom type (used for non-terminating expressions like `throw`)

### Composite types

```vera
@Array<Int>                              -- array of ints
@Array<Option<Int>>                      -- array of ADT (compound element type)
@Array<String>                           -- array of strings
@Tuple<Int, String>                      -- tuple
@Option<Int>                             -- Option type (Some/None)
@Map<String, Int>                        -- key-value map (keys: Eq + Hash)
@Set<Int>                                -- unordered unique elements (Eq + Hash)
@Decimal                                 -- exact decimal arithmetic
@Json                                    -- JSON data (parse/query/serialize)
@HtmlNode                                -- HTML document node (parse/query/serialize)
Fn(Int -> Int) effects(pure)              -- function type
{ @Int | @Int.0 > 0 }                   -- refinement type
```

### Array literals

Write `[1, 2, 3]` for a populated array and `[]` for an empty one. The element type is inferred from the elements when present, and from the surrounding type annotation when the literal is empty:

```vera
let @Array<Int> = [1, 2, 3];              -- populated: elements determine type
let @Array<Bool> = [true, false];          -- populated, any element type
let @Array<Int> = [];                      -- empty: annotation determines type
let @Array<Array<Int>> = [[1, 2], [3, 4]]; -- nested arrays
let @Array<Json> = [JNumber(1.0), JNull];   -- ADT elements
```

Empty arrays **must** appear in a position with a known type — a `let` binding with a type annotation, a function argument whose parameter type is known, or the branch of a match arm whose type is fixed by another arm. An empty literal with no surrounding type context is a type error. When the element type is polymorphic in the context (e.g. returning `Array<T>` from a `forall<T>` function body), annotate the `let` or thread through a concrete instantiation.

`[` and `]` are context-disambiguated: in expression position (`let @Array<Int> = []`) they delimit an array literal; in postfix position (`@Array<Int>.0[@Int.0]`) they are the index operator — see the operator precedence table at the bottom of this file. The parser resolves the two by lookahead; there is no ambiguity you need to work around.

### Type aliases

```vera
type PosInt = { @Int | @Int.0 > 0 };
type Name = String;
```

## Data Types (ADTs)

```vera
private data Color {
  Red,
  Green,
  Blue
}

private data List<T> {
  Nil,
  Cons(T, List<T>)
}

private data Option<T> {
  None,
  Some(T)
}
```

> **Note:** `Option<T>`, `Result<T, E>`, `Ordering`, and `UrlParts` are provided by the standard prelude and available in every program without explicit `data` declarations. You only need to define them locally if you want to shadow the prelude definition.

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
if @Bool.0 then {
  expr1
} else {
  expr2
}
```

Both branches are mandatory. Braces are mandatory. Each branch is always multi-line (closing brace on its own line).

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

## Typed Holes

**When you do not know the right expression to write, use `?` rather than guessing.** A typed hole tells you immediately what type is needed and what bindings are available — it is always faster than writing the wrong thing and debugging the type error.

```vera
public fn double(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  ?
}
```

`vera check` reports a `W001` warning (not an error):

```text
Warning [W001]: Typed hole: expected Int.
Fix: Replace ? with an expression of type Int. Available bindings: @Int.0: Int.
```

The program type-checks successfully (`ok: true`) — holes are warnings, not errors. This means you can check the *rest* of a function for type errors while one expression is still incomplete.

`vera check --json` includes hole warnings in the `warnings` array with the full expected type and binding context, making them machine-readable for agent workflows.

**Programs with holes cannot be compiled.** `vera compile` and `vera run` reject any program containing `?` with an `E614` error.

### Workflow

Use holes to build programs incrementally:

```vera
public fn safe_div(@Int, @Int -> @Option<Int>)
  requires(true) ensures(true) effects(pure)
{
  if ? then {       -- W001: expected Bool. Bindings: @Int.0: Int; @Int.1: Int
    Some(?)         -- W001: expected Int.  Bindings: @Int.0: Int; @Int.1: Int
  } else {
    None
  }
}
```

Check this, read the `W001` fix hints, then fill in the holes:

```vera
  if @Int.0 != 0 then {
    Some(@Int.1 / @Int.0)
  } else {
    None
  }
```

### Multiple holes

Multiple holes in one program each produce their own `W001` warning with independent context. You can fill them one at a time and re-check between iterations.

### Conformance

See `tests/conformance/ch03_typed_holes.vera` for a minimal working example.

## Iteration

Vera has no `for` or `while` loops. Iteration is always expressed as tail-recursive functions. The standard pattern for counted iteration:

```vera
private fn loop(@Nat, @Nat -> @Unit)
  requires(@Nat.0 <= @Nat.1)
  ensures(true)
  effects(<IO>)
{
  IO.print(string_concat(fizzbuzz(@Nat.0), "\n"));
  if @Nat.0 < @Nat.1 then {
    loop(@Nat.1, @Nat.0 + 1)
  } else {
    ()
  }
}
```

Here `@Nat.0` is the counter (De Bruijn index 0 = most recent, i.e. the second parameter) and `@Nat.1` is the limit (the first parameter). The contract `requires(@Nat.0 <= @Nat.1)` ensures the counter never exceeds the limit — and since the recursive call passes `@Nat.0 + 1` where `@Nat.0 < @Nat.1`, the precondition is maintained at every step. The function prints, then either recurses with an incremented counter or returns `()`.

Call with the limit first and counter second: `loop(100, 1)`.

For pure recursive functions that need termination proofs, add a `decreases` clause (see [Recursion](#recursion)). Effectful recursive functions like the loop above do not require `decreases`.

## Closures and captured bindings

Anonymous functions are written `fn(@ParamType1, @ParamType2 -> @ReturnType) effects(effect_row) { body_expression }`. They are first-class values and can be passed to higher-order built-ins (`array_map`, `array_filter`, `array_fold`, `array_any`, `array_find`, `array_sort_by`, …) or stored in `let` bindings.

```vera
let @Array<Int> = [1, 2, 3, 4, 5];
let @Array<Int> = array_map(
  @Array<Int>.0,
  fn(@Int -> @Int) effects(pure) { @Int.0 * 2 }
);
-- Result: [2, 4, 6, 8, 10]
```

Inside the closure body, `@Int.0` is the closure's own parameter (index 0 = most recent binding). This matches how slot indices work in top-level `fn` declarations.

### Capturing outer bindings

**Closures can capture primitive outer bindings (`Int`, `Nat`, `Bool`, `Byte`, `Float64`) and single-pointer ADTs (`Option<T>`, `Result<T, E>`, user-defined `data` types, opaque handles like `Map`/`Set`/`Decimal`/`Regex`).** **Pair-type captures (`String`, `Array<T>`) are still broken** — they compile and run but the captured value's length is silently lost ([#535](https://github.com/aallan/vera/issues/535)). The historical [#514](https://github.com/aallan/vera/issues/514) "all heap captures broken" framing was inaccurate; v0.0.121 fixed nested closures and clarified that the residual is specifically pair types.

Outer bindings are available at higher De Bruijn indices — the closure's own parameters are pushed on top of the slot stack, so outer `@T` bindings shift up by the number of inner `@T` parameters.

```vera
-- WORKS: capturing a primitive @Int.
public fn sum_plus_offset(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Int = 100;                      -- outer binding: @Int.0 = 100
  let @Array<Int> = [1, 2, 3];
  array_fold(
    @Array<Int>.0,
    0,
    fn(@Int, @Int -> @Int) effects(pure) {
      -- Inside this closure body, two @Int params are in scope:
      --   @Int.0 = element (most recent, the iterator's current value)
      --   @Int.1 = accumulator
      --   @Int.2 = outer `let @Int = 100`  (captured — primitive, OK)
      @Int.1 + @Int.0 + @Int.2
    }
  )
}
-- 0+1+100 + 2+100 + 3+100 = 306
```

The rule when capture IS safe: count the closure's own `@T` parameters, and the outermost captured `@T` binding sits at that index. A closure with no `@Int` parameters of its own would see the outer `let @Int` as `@Int.0`; a closure with two `@Int` parameters sees it as `@Int.2`. Types are independent — a closure's `@Int` parameter does not shift outer `@String` bindings.

Use `vera check --explain-slots file.vera` if you need the resolved index table printed for a specific function (including closures).

### What you cannot capture

```vera
-- BROKEN: capturing a pair-typed value silently corrupts it.
let @Array<Int> = [10, 20, 30];        -- captured (outer) @Array<Int>.0 = this
let @Array<Int> = [1, 2, 3];           -- iterated (inner) @Array<Int>.0 = this
                                       --             outer shifts to .1
array_fold(
  @Array<Int>.0,
  0,
  fn(@Int, @Int -> @Int) effects(pure) {
    -- Inside the closure: @Int.0 = element, @Int.1 = acc.
    -- @Array<Int>.1 refers to the OUTER (captured) array.
    @Int.1 + @Int.0 + nat_to_int(array_length(@Array<Int>.1))
  }
)
-- Compiles and runs without error, but the captured array reads as
-- empty (length 0) inside the closure body — the len field of the
-- (ptr, len) pair is dropped during closure-struct serialisation.
-- See #535 for the open issue and the in-progress fix.
```

The two pair-type capture failures:

- Any `Array<T>` (including `Array<Bool>`, `Array<Array<Int>>`, etc.)
- `String`

ADT captures (`Option<T>`, `Result<T, E>`, user `data` types, `Json`, `HtmlNode`, `MdBlock`, opaque handles like `Map<K, V>` / `Set<T>` / `Decimal` / `Regex`) all work — they are single-i32-pointer values, not pairs, so the closure-struct layout handles them correctly.

### Workaround for pair-type captures: lift to a helper

When a combinator needs to capture a `String` or `Array<T>` value, lift the closure body to a top-level `private fn` that takes the pair-typed value as an explicit parameter. The parameter path through `_compile_lifted_closure` already handles pair types correctly; only the capture path is broken (#535).

```vera
private fn use_array(@Int, @Array<Int> -> @Int)
  requires(true) ensures(true) effects(pure)
{
  @Int.0 + nat_to_int(array_length(@Array<Int>.0))
}

public fn build(@Unit -> @Array<Int>)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = array_range(0, 7);   -- the array we'd want to capture
  array_map(
    array_range(0, 3),
    -- Helper takes the array as a parameter; @Array<Int>.1 is the
    -- outer let, @Array<Int>.0 would be a capture (still broken).
    fn(@Int -> @Int) effects(pure) { use_array(@Int.0, @Array<Int>.1) }
  )
}
```

Awkward — defeats the locality of the closure form — but works until #535 lands.

### When to use recursion instead

Closures cover pure, self-contained transformations and simple captured constants. Prefer a top-level recursive function when any of these hold:

- The body needs an effect row other than `pure` that doesn't match the combinator's expected effect signature.
- The body needs to early-return or short-circuit in a way the combinator doesn't provide (`array_find` / `array_any` / `array_all` short-circuit; `array_map` / `array_fold` do not).
- The iteration shape isn't one-pass left-to-right (e.g. you need to look ahead, or process in reverse while mutating a different data structure).
- Termination requires a `decreases` clause that proves non-trivial progress — closures cannot carry `decreases`.

For counted iteration with IO, use the recursive `loop` pattern from the Iteration section above; for array transformations, use the array combinators with closures.

### Nested closures

Closures inside closure bodies work end-to-end as of v0.0.121 — the natural 2D `array_map(rows, fn(row) { array_map(cols, fn(col) { ... }) })` shape compiles, validates, and runs at any return type. Captures from the outer scope flow through nested closures correctly for primitives and ADTs (the pair-type capture caveat from [#535](https://github.com/aallan/vera/issues/535) applies to nested cases too — a nested closure capturing an outer `String` or `Array<T>` will hit the same len-loss). Three or more levels of nesting work the same way; the lifting pass uses a worklist that handles arbitrary depth.

```vera
public fn build_grid(@Unit -> @Array<Array<Int>>)
  requires(true) ensures(true) effects(pure)
{
  -- 2D array of products. No helper, no lifting workaround needed.
  array_map(
    array_range(0, 3),
    fn(@Int -> @Array<Int>) effects(pure) {
      array_map(
        array_range(0, 3),
        fn(@Int -> @Int) effects(pure) { @Int.0 + @Int.1 }
      )
    }
  )
}
```

## Built-in Functions

### Naming convention

All built-in functions follow predictable naming patterns. When guessing a function name you haven't seen, apply these rules:

| Pattern | When | Examples |
|---------|------|----------|
| `domain_verb` | Most functions | `string_length`, `array_append`, `regex_match`, `md_parse` |
| `source_to_target` | Type conversions | `int_to_float`, `float_to_int`, `nat_to_int` |
| `domain_is_predicate` | Boolean predicates | `float_is_nan`, `float_is_infinite` |
| Prefix-less | Math universals and float constants only | `abs`, `min`, `max`, `floor`, `ceil`, `round`, `sqrt`, `pow`, `nan`, `infinity` |

**String operations always use `string_` prefix** — `string_contains`, `string_starts_with`, `string_split`, `string_join`, `string_strip`, `string_upper`, `string_lower`, `string_replace`, `string_index_of`, `string_char_code`, `string_from_char_code`, `string_chars`, `string_lines`, `string_words`, `string_reverse`, `string_trim_start`, `string_trim_end`, `string_pad_start`, `string_pad_end`. **Character classifiers use `is_` prefix** — `is_digit`, `is_alpha`, `is_alphanumeric`, `is_whitespace`, `is_upper`, `is_lower`. **First-character conversion uses `char_` prefix** — `char_to_upper`, `char_to_lower`. **JSON typed accessors use `json_as_` and `json_get_` prefixes** — `json_as_string`/`number`/`bool`/`int`/`array`/`object` for Layer-1 coercions; `json_get_string`/`number`/`bool`/`int`/`array` for Layer-2 compound field accessors. **Float64 predicates use `float_` prefix** — `float_is_nan`, `float_is_infinite`. **Type conversions use `source_to_target`** — `int_to_float` (not `to_float`), `float_to_int`, `int_to_nat`. Math functions (`abs`, `min`, `max`, etc.) and float constants (`nan`, `infinity`) are the **only** exceptions — they need no prefix because they are universally understood mathematical names.

**If `vera check` reports an unresolved function name, apply these patterns to derive the correct name before giving up.** The convention is strict and consistent — the right name is always derivable. Do not invent names that don't follow the pattern; they will not exist.

### Option and Result Combinators

The standard prelude provides `Option<T>` and `Result<T, E>` along with combinator functions that are always available:

```vera
-- Option: unwrap with default
option_unwrap_or(Some(42), 0)           -- returns 42
option_unwrap_or(None, 0)               -- returns 0

-- Option: transform the value inside Some
option_map(Some(10), fn(@Int -> @Int) effects(pure) { @Int.0 + 1 })
-- returns Some(11)

-- Option: chain fallible operations (flatmap)
option_and_then(Some(5), fn(@Int -> @Option<Int>) effects(pure) {
  if @Int.0 > 0 then { Some(@Int.0 * 2) } else { None }
})
-- returns Some(10)

-- Result: unwrap with default
result_unwrap_or(Ok(42), 0)             -- returns 42
result_unwrap_or(Err("oops"), 0)        -- returns 0

-- Result: transform the Ok value
result_map(Ok(10), fn(@Int -> @Int) effects(pure) { @Int.0 + 1 })
-- returns Ok(11)
```

These are generic functions that follow the `domain_verb` naming convention. They are automatically injected and undergo normal monomorphization. If you define a function with the same name, your definition takes precedence.

### Array operations

```vera
array_length(@Array<Int>.0)             -- returns Int (always >= 0)
array_append(@Array<Int>.0, @Int.0)     -- returns Array<Int> (new array with element appended)
array_range(@Int.0, @Int.1)             -- returns Array<Int> (integers [start, end))
array_concat(@Array<Int>.0, @Array<Int>.1)  -- returns Array<Int> (merge two arrays)
array_slice(@Array<Int>.0, @Int.0, @Int.1)  -- returns Array<Int> (elements [start, end))
array_map(@Array<Int>.0, fn(@Int -> @Int) effects(pure) { ... })     -- returns Array<Int>
array_filter(@Array<Int>.0, fn(@Int -> @Bool) effects(pure) { ... }) -- returns Array<Int>
array_fold(@Array<Int>.0, 0, fn(@Int, @Int -> @Int) effects(pure) { @Int.1 + @Int.0 }) -- returns Int
array_mapi(@Array<Int>.0, fn(@Int, @Nat -> @Int) effects(pure) { ... }) -- returns Array<Int> (map with index)
array_reverse(@Array<Int>.0)                                         -- returns Array<Int> (element order reversed)
array_find(@Array<Int>.0, fn(@Int -> @Bool) effects(pure) { ... })   -- returns Option<Int> (first match)
array_any(@Array<Int>.0, fn(@Int -> @Bool) effects(pure) { ... })    -- returns Bool (at least one match)
array_all(@Array<Int>.0, fn(@Int -> @Bool) effects(pure) { ... })    -- returns Bool (every element matches)
array_flatten(@Array<Array<Int>>.0)                                  -- returns Array<Int> (one level)
array_sort_by(@Array<Int>.0, fn(@Int, @Int -> @Ordering) effects(pure) { ... }) -- returns Array<Int>
```

`array_map` / `array_mapi` are generic: the element type can change (e.g. `array_map(@Array<Int>.0, fn(@Int -> @String) ...)`).
`array_fold` is generic: the accumulator type can differ from the element type.
`array_mapi` passes the zero-based index as a `@Nat` second argument — use this rather than hand-rolling a recursive accumulator with an index counter.
`array_find` short-circuits on the first match; `array_any` and `array_all` do the same and observe the standard vacuous-truth convention on empty input (`any([], _) == false`, `all([], _) == true`).
`array_sort_by`'s comparator returns `@Ordering` (`Less` / `Equal` / `Greater`); insertion sort, stable.

`array_sort<T> where Ord<T>`, `array_contains<T> where Eq<T>`, and `array_index_of<T> where Eq<T>` (operations that would dispatch on the element type's built-in ability) are not yet implemented — use `array_sort_by` with an explicit comparator, or `array_any` / `array_find` with an equality predicate, until that infrastructure lands.

### Map operations

`Map<K, V>` is a key-value collection. Keys must satisfy `Eq` and `Hash` abilities (primitive types: `Int`, `Nat`, `Bool`, `Float64`, `String`, `Byte`, `Unit`). Values can be any type. All operations are pure — insert and remove return new maps.

```vera
map_insert(map_new(), "hello", 42)                  -- returns Map<String, Nat>
map_insert(@Map<String, Nat>.0, "world", 7)         -- returns Map<String, Nat> (new map with entry added)
map_get(@Map<String, Nat>.0, "hello")               -- returns Option<Nat> (Some(42) or None)
map_contains(@Map<String, Nat>.0, "hello")          -- returns Bool
map_remove(@Map<String, Nat>.0, "hello")            -- returns Map<String, Nat> (new map without key)
map_size(@Map<String, Nat>.0)                       -- returns Int (number of entries)
map_keys(@Map<String, Nat>.0)                       -- returns Array<String>
map_values(@Map<String, Nat>.0)                     -- returns Array<Nat>
```

> `map_new()` is a zero-argument generic function. Nest it inside `map_insert(map_new(), k, v)` so that type inference can resolve the key and value types from the arguments. Using `option_unwrap_or(map_get(...), default)` is the idiomatic way to extract values with a fallback.

### Set operations

`Set<T>` is an unordered collection of unique elements. Elements must satisfy `Eq` and `Hash` abilities (primitive types: `Int`, `Nat`, `Bool`, `Float64`, `String`, `Byte`, `Unit`). All operations are pure — add and remove return new sets.

```vera
set_add(set_add(set_new(), "hello"), "world")       -- returns Set<String>
set_contains(@Set<String>.0, "hello")               -- returns Bool (true)
set_remove(@Set<String>.0, "hello")                 -- returns Set<String> (new set without element)
set_size(@Set<String>.0)                            -- returns Int
set_to_array(@Set<String>.0)                        -- returns Array<String>
```

> `set_new()` is a zero-argument generic function. Nest it inside `set_add(set_new(), elem)` so that type inference can resolve the element type. Adding a duplicate element is a no-op (sets enforce uniqueness).

### Decimal operations

`Decimal` provides exact decimal arithmetic for financial and precision-sensitive applications. It is an opaque type (i32 handle) backed by the runtime's decimal implementation. All operations are pure.

```vera
decimal_from_int(42)                                -- returns Decimal (exact conversion)
decimal_from_float(3.14)                            -- returns Decimal (via str conversion)
decimal_add(@Decimal.0, @Decimal.1)                 -- returns Decimal (addition)
decimal_sub(@Decimal.0, @Decimal.1)                 -- returns Decimal (subtraction)
decimal_mul(@Decimal.0, @Decimal.1)                 -- returns Decimal (multiplication)
decimal_neg(@Decimal.0)                             -- returns Decimal (negation)
decimal_abs(@Decimal.0)                             -- returns Decimal (absolute value)
decimal_round(@Decimal.0, 2)                        -- returns Decimal (round to N places)
decimal_eq(@Decimal.0, @Decimal.1)                  -- returns Bool (equality)
decimal_compare(@Decimal.0, @Decimal.1)             -- returns Ordering (Less/Equal/Greater)
decimal_to_string(@Decimal.0)                       -- returns String
decimal_to_float(@Decimal.0)                        -- returns Float64 (potentially lossy)
```

`decimal_from_string` and `decimal_div` return `Option<Decimal>` — use `option_unwrap_or` or `match` to extract the value. `decimal_compare` returns `Ordering` — use `match` to dispatch on `Less`, `Equal`, `Greater`.

### JSON operations

`Json` is a built-in ADT for structured data interchange. Parse JSON strings, query fields and array elements, and serialize back to strings. All operations are pure.

The `Json` type has six constructors: `JNull`, `JBool(Bool)`, `JNumber(Float64)`, `JString(String)`, `JArray(Array<Json>)`, `JObject(Map<String, Json>)`. It is provided by the standard prelude — no `data` declaration needed.

```vera
json_parse("{\"name\":\"Vera\"}")               -- returns Result<Json, String>
json_stringify(@Json.0)                          -- returns String (JSON text)
json_get(@Json.0, "name")                        -- returns Option<Json> (field lookup)
json_has_field(@Json.0, "name")                  -- returns Bool
json_keys(@Json.0)                               -- returns Array<String> (object keys)
json_array_get(@Json.0, 0)                       -- returns Option<Json> (element at index)
json_array_length(@Json.0)                       -- returns Int (array length, 0 if not array)
json_type(@Json.0)                               -- returns String ("null"/"bool"/"number"/"string"/"array"/"object")
```

Pattern match on `Json` constructors to extract values:

```vera
match json_parse("{\"x\":42}") {
  Err(@String) -> Err(@String.0),
  Ok(@Json) -> match json_get(@Json.0, "x") {
    None -> Err("missing x"),
    Some(@Json) -> match @Json.0 {
      JNumber(@Float64) -> Ok(float_to_int(@Float64.0)),
      _ -> Err("x is not a number")
    }
  }
}
```

#### Typed accessors (Layer 1 and Layer 2)

For the common case of "unwrap `Option<Json>` and match on a specific constructor", use the typed accessors instead of the two-level match above:

```vera
-- Layer 1: Json -> Option<T>.  Some when the constructor matches.
json_as_string(@Json.0)   -- Option<String>
json_as_number(@Json.0)   -- Option<Float64>
json_as_bool(@Json.0)     -- Option<Bool>
json_as_int(@Json.0)      -- Option<Int>     (truncates; None for NaN/inf/|f| >= 2^63)
json_as_array(@Json.0)    -- Option<Array<Json>>
json_as_object(@Json.0)   -- Option<Map<String, Json>>

-- Layer 2: json_get + json_as_* composed (the common pattern).
json_get_string(@Json.0, "name")   -- Option<String>
json_get_number(@Json.0, "score")  -- Option<Float64>
json_get_bool(@Json.0, "active")   -- Option<Bool>
json_get_int(@Json.0, "age")       -- Option<Int>
json_get_array(@Json.0, "tags")    -- Option<Array<Json>>
```

The Layer-2 accessors return `None` both when the field is missing AND when the field is present but of the wrong type — exactly what 90% of real API-consuming code wants. The example above collapses to:

```vera
match json_parse("{\"x\":42}") {
  Err(@String) -> Err(@String.0),
  Ok(@Json) -> match json_get_int(@Json.0, "x") {
    Some(@Int) -> Ok(@Int.0),
    None -> Err("x missing or not a number")
  }
}
```

### String operations

```vera
string_length(@String.0)                -- returns Nat
string_concat(@String.0, @String.1)     -- returns String
string_slice(@String.0, @Nat.0, @Nat.1) -- returns String (start, end)
string_char_code(@String.0, @Int.0)     -- returns Nat (ASCII code at index)
string_from_char_code(@Nat.0)           -- returns String (single char from code point)
string_repeat(@String.0, @Nat.0)        -- returns String (repeated N times)
parse_nat(@String.0)                    -- returns Result<Nat, String>
parse_int(@String.0)                    -- returns Result<Int, String>
parse_float64(@String.0)                -- returns Result<Float64, String>
parse_bool(@String.0)                   -- returns Result<Bool, String>
base64_encode(@String.0)                -- returns String (RFC 4648)
base64_decode(@String.0)                -- returns Result<String, String>
url_encode(@String.0)                   -- returns String (RFC 3986 percent-encoding)
url_decode(@String.0)                   -- returns Result<String, String>
url_parse(@String.0)                    -- returns Result<UrlParts, String> (RFC 3986 decomposition)
url_join(@UrlParts.0)                   -- returns String (reassemble URL from UrlParts)
md_parse(@String.0)                     -- returns Result<MdBlock, String> (parse Markdown)
md_render(@MdBlock.0)                   -- returns String (render to canonical Markdown)
md_has_heading(@MdBlock.0, @Nat.0)      -- returns Bool (check if heading of level exists)
md_has_code_block(@MdBlock.0, @String.0) -- returns Bool (check if code block of language exists)
md_extract_code_blocks(@MdBlock.0, @String.0) -- returns Array<String> (extract code by language)
html_parse(@String.0)                  -- returns Result<HtmlNode, String> (parse HTML)
html_to_string(@HtmlNode.0)            -- returns String (serialize to HTML)
html_query(@HtmlNode.0, @String.0)     -- returns Array<HtmlNode> (CSS selector query)
html_text(@HtmlNode.0)                 -- returns String (extract text content)
html_attr(@HtmlNode.0, @String.0)      -- returns Option<String> (get attribute value)
regex_match(@String.0, @String.1)      -- returns Result<Bool, String> (test if pattern matches)
regex_find(@String.0, @String.1)       -- returns Result<Option<String>, String> (first match)
regex_find_all(@String.0, @String.1)   -- returns Result<Array<String>, String> (all matches)
regex_replace(@String.0, @String.1, @String.2) -- returns Result<String, String> (replace first match)
async(@T.0)                            -- returns Future<T> (requires effects(<Async>))
await(@Future<T>.0)                    -- returns T (requires effects(<Async>))
to_string(@Int.0)                       -- returns String (integer to decimal)
int_to_string(@Int.0)                   -- returns String (alias for to_string)
bool_to_string(@Bool.0)                 -- returns String ("true" or "false")
nat_to_string(@Nat.0)                   -- returns String (natural to decimal)
byte_to_string(@Byte.0)                 -- returns String (single character)
float_to_string(@Float64.0)             -- returns String (decimal representation)
string_strip(@String.0)                 -- returns String (trim whitespace)
```

#### String interpolation

```vera
"hello \(@String.0)"               -- embeds a String value
"x = \(@Int.0)"                    -- auto-converts Int to String
"a=\(@Int.1), b=\(@Int.0)"        -- multiple interpolations
"\(@String.0)"                     -- interpolation-only (no literal text)
"len=\(string_length(@String.0))"  -- function call inside interpolation
```

Expressions inside `\(...)` are auto-converted to String for types: Int, Nat, Bool, Byte, Float64. Other types produce error E148. Expressions cannot contain string literals (use `let` bindings instead).

#### String search

```vera
string_contains(@String.0, @String.1)  -- returns Bool (substring test)
string_starts_with(@String.0, @String.1) -- returns Bool (prefix test)
string_ends_with(@String.0, @String.1)   -- returns Bool (suffix test)
string_index_of(@String.0, @String.1)    -- returns Option<Nat> (first occurrence)
```

`string_contains` checks whether the needle appears anywhere in the haystack. `string_starts_with` and `string_ends_with` test prefix and suffix matches. `string_index_of` returns `Some(i)` with the byte offset of the first match, or `None` if not found. An empty needle always matches (returns `true` or `Some(0)`).

#### String transformation

```vera
string_upper(@String.0)                         -- returns String (ASCII uppercase)
string_lower(@String.0)                         -- returns String (ASCII lowercase)
string_replace(@String.0, @String.1, @String.2) -- returns String (replace all)
string_split(@String.0, @String.1)              -- returns Array<String> (split by delimiter)
string_join(@Array<String>.0, @String.0)        -- returns String (join with separator)
```

`string_upper` and `string_lower` convert ASCII letters only (a-z ↔ A-Z). `string_replace` substitutes all non-overlapping occurrences; an empty needle returns the original string unchanged. `string_split` returns an array of segments; an empty delimiter returns a single-element array. `string_join` concatenates array elements with the separator between each pair.

#### String utilities and character classification

```vera
-- Splits (bridge to the array combinators)
string_chars(@String.0)                            -- returns Array<String> (one byte each)
string_lines(@String.0)                            -- returns Array<String> (\n, \r\n, \r)
string_words(@String.0)                            -- returns Array<String> (whitespace runs)

-- Transformations
string_reverse(@String.0)                          -- returns String (byte reverse)
string_trim_start(@String.0)                       -- returns String (lstrip whitespace)
string_trim_end(@String.0)                         -- returns String (rstrip whitespace)
string_pad_start(@String.0, @Nat.0, @String.1)     -- returns String (left-pad to length, JS padStart)
string_pad_end(@String.0, @Nat.0, @String.1)       -- returns String (right-pad to length)

-- Case conversion (first byte only)
char_to_upper(@String.0)                           -- returns String
char_to_lower(@String.0)                           -- returns String

-- Character classifiers (first byte; false for empty)
is_digit(@String.0)                                -- returns Bool ('0'..'9')
is_alpha(@String.0)                                -- returns Bool ('A'..'Z', 'a'..'z')
is_alphanumeric(@String.0)                         -- returns Bool
is_whitespace(@String.0)                           -- returns Bool (tab, LF, VT, FF, CR, space — Python isspace() ASCII)
is_upper(@String.0)                                -- returns Bool
is_lower(@String.0)                                -- returns Bool
```

`string_chars` is the canonical bridge from `String` to `Array<String>` — combine with `array_map`, `array_filter`, `array_fold` to thread per-byte logic through the array combinators. `string_lines` follows Python's `splitlines()` (trailing `\n` does not add an empty segment). `string_words` follows Python's `split()` with no args (runs collapse, empty segments discarded).

`string_pad_start` and `string_pad_end` cycle the fill left-to-right and truncate to exactly the padding length, matching JavaScript's `padStart` / `padEnd`. If the input is already at least `n` bytes, the input is returned unchanged. An empty `fill` is a no-op.

`char_to_upper` / `char_to_lower` convert only the **first byte** of the string; remaining bytes pass through unchanged. Useful for title-casing a token. The six classifiers all inspect only the first byte and return `false` for the empty string. All sixteen are ASCII-only — no Unicode awareness.

String functions use the heap allocator (`$alloc`). Memory is managed automatically by a conservative mark-sweep garbage collector — there is no manual allocation or deallocation. All four parse functions return `Result<T, String>`: `parse_nat`, `parse_int`, `parse_float64`, and `parse_bool`. They return `Ok(value)` on valid input and `Err(msg)` on empty or invalid input; leading and trailing spaces are tolerated. `parse_int` accepts an optional `+` or `-` sign. `parse_bool` is strict: only `"true"` and `"false"` (lowercase) are valid. `base64_encode` encodes a string to standard Base64 (RFC 4648); `base64_decode` returns `Result<String, String>`, failing on invalid length or characters. `url_encode` percent-encodes a string for use in URLs (RFC 3986), leaving unreserved characters (`A-Z`, `a-z`, `0-9`, `-`, `_`, `.`, `~`) unchanged; `url_decode` returns `Result<String, String>`, failing on invalid `%XX` sequences. `url_parse` decomposes a URL into its RFC 3986 components, returning `Result<UrlParts, String>` where `UrlParts(scheme, authority, path, query, fragment)` is a built-in ADT with five String fields; it returns `Err("missing scheme")` if no `:` is found. `url_join` reassembles a `UrlParts` value into a URL string. Programs must redefine `UrlParts` locally (like `Result`) to use it in match expressions.

### Markdown operations

```vera
md_parse(@String.0)                     -- returns Result<MdBlock, String>
md_render(@MdBlock.0)                   -- returns String
md_has_heading(@MdBlock.0, @Nat.0)      -- returns Bool
md_has_code_block(@MdBlock.0, @String.0) -- returns Bool
md_extract_code_blocks(@MdBlock.0, @String.0) -- returns Array<String>
```

`md_parse` parses a Markdown string into a typed `MdBlock` document tree. Returns `Ok(MdDocument(...))` on success. `md_render` converts an `MdBlock` back to canonical Markdown text. `md_has_heading` checks whether the document contains a heading at the given level (1–6). `md_has_code_block` checks for a fenced code block with the given language tag (use `""` for untagged blocks). `md_extract_code_blocks` returns an array of code content strings for all blocks matching the language.

Two built-in ADTs represent the Markdown document structure:

**MdInline** — inline content within blocks:
- `MdText(String)` — plain text
- `MdCode(String)` — inline code
- `MdEmph(Array<MdInline>)` — emphasis (*italic*)
- `MdStrong(Array<MdInline>)` — strong (**bold**)
- `MdLink(Array<MdInline>, String)` — link with text and URL
- `MdImage(String, String)` — image with alt text and source

**MdBlock** — block-level content:
- `MdParagraph(Array<MdInline>)` — paragraph
- `MdHeading(Nat, Array<MdInline>)` — heading with level (1–6)
- `MdCodeBlock(String, String)` — fenced code block (language, code)
- `MdBlockQuote(Array<MdBlock>)` — block quote
- `MdList(Bool, Array<Array<MdBlock>>)` — list (ordered?, items)
- `MdThematicBreak` — horizontal rule
- `MdTable(Array<Array<Array<MdInline>>>)` — table (rows of cells)
- `MdDocument(Array<MdBlock>)` — top-level document

All Markdown functions are pure and available without imports. Pattern match on `MdBlock` and `MdInline` constructors to traverse the document tree.

### HTML operations

`HtmlNode` is a built-in ADT for parsing and querying HTML documents. Parse HTML strings, query elements with CSS selectors, and extract text content. All operations are pure.

```vera
html_parse(@String.0)                    -- returns Result<HtmlNode, String> (parse HTML)
html_to_string(@HtmlNode.0)             -- returns String (serialize to HTML)
html_query(@HtmlNode.0, @String.0)      -- returns Array<HtmlNode> (CSS selector query)
html_text(@HtmlNode.0)                  -- returns String (extract text content)
html_attr(@HtmlNode.0, @String.0)       -- returns Option<String> (get attribute value)
```

`html_parse` is lenient (like browsers) — malformed HTML produces a best-effort tree, not an error. `html_query` supports simple CSS selectors: tag name (`div`), class (`.classname`), ID (`#id`), attribute presence (`[href]`), and descendant combinator (`div p`). `html_text` recursively concatenates all text content, excluding comments. `html_attr` returns `None` for non-element nodes or missing attributes.

**HtmlNode constructors:**

- `HtmlElement(String, Map<String, String>, Array<HtmlNode>)` — element (tag name, attributes, children)
- `HtmlText(String)` — text content
- `HtmlComment(String)` — HTML comment

```vera
let @Result<HtmlNode, String> = html_parse("<div><a href=\"url\">link</a></div>");
match @Result<HtmlNode, String>.0 {
  Ok(@HtmlNode) -> {
    let @Array<HtmlNode> = html_query(@HtmlNode.0, "a");
    IO.print(int_to_string(array_length(@Array<HtmlNode>.0)))
  },
  Err(@String) -> IO.print(@String.0)
}
```

All HTML functions are pure and available without imports. Pattern match on `HtmlNode` constructors to traverse the document tree.

### Regular expressions

```vera
regex_match(@String.0, @String.1)                -- returns Result<Bool, String>
regex_find(@String.0, @String.1)                 -- returns Result<Option<String>, String>
regex_find_all(@String.0, @String.1)             -- returns Result<Array<String>, String>
regex_replace(@String.0, @String.1, @String.2)   -- returns Result<String, String>
```

All four regex functions take the input string as the first argument and the regex pattern as the second. `regex_replace` takes a third argument for the replacement string. All return `Result` types — `Err(msg)` for invalid patterns, `Ok(value)` on success.

`regex_match` tests whether the pattern matches anywhere in the input (substring match, not full-string). `regex_find` returns the first matching substring wrapped in `Option`. `regex_find_all` returns all non-overlapping matches as an `Array<String>` — always returns full match strings (group 0), even when the pattern contains capture groups. `regex_replace` replaces only the **first** match.

```vera
let @Result<Bool, String> = regex_match("hello123", "\\d+");
match @Result<Bool, String>.0 {
  Ok(@Bool) -> if @Bool.0 then { IO.print("found digits") } else { IO.print("no digits") },
  Err(@String) -> IO.print(string_concat("Error: ", @String.0))
}
```

All regex functions are pure and implemented as host imports (Python `re` / JavaScript `RegExp`).

### Numeric operations

```vera
abs(@Int.0)                         -- returns Nat (absolute value)
min(@Int.0, @Int.1)                 -- returns Int (smaller of two)
max(@Int.0, @Int.1)                 -- returns Int (larger of two)
floor(@Float64.0)                   -- returns Int (round down)
ceil(@Float64.0)                    -- returns Int (round up)
round(@Float64.0)                   -- returns Int (banker's rounding)
sqrt(@Float64.0)                    -- returns Float64 (square root)
pow(@Float64.0, @Int.0)             -- returns Float64 (exponentiation)
```

`abs` returns `Nat` because absolute values are non-negative. `floor`, `ceil`, and `round` convert `Float64` to `Int`; they trap on NaN or out-of-range values (WASM semantics). `round` uses IEEE 754 roundTiesToEven (banker's rounding): `round(2.5)` is `2`, not `3`. `pow` takes an `Int` exponent — negative exponents produce reciprocals (`pow(2.0, -1)` is `0.5`). The integer builtins (`abs`, `min`, `max`) are fully verifiable by the SMT solver (Tier 1). The float builtins fall to Tier 3 (runtime).

### Logarithmic, trigonometric, and numeric utility functions

```vera
log(@Float64.0)                     -- natural logarithm (base e)
log2(@Float64.0)                    -- base-2 logarithm
log10(@Float64.0)                   -- base-10 logarithm
sin(@Float64.0)                     -- sine (radians)
cos(@Float64.0)                     -- cosine (radians)
tan(@Float64.0)                     -- tangent (radians)
asin(@Float64.0)                    -- inverse sine, returns [-π/2, π/2]
acos(@Float64.0)                    -- inverse cosine, returns [0, π]
atan(@Float64.0)                    -- inverse tangent, returns (-π/2, π/2)
atan2(@Float64.0, @Float64.1)       -- quadrant-correct angle from (y, x)
pi()                                -- 3.141592653589793
e()                                 -- 2.718281828459045
sign(@Int.0)                        -- returns Int: -1, 0, or 1
clamp(@Int.0, @Int.1, @Int.2)       -- clamp(v, lo, hi) -> Int
float_clamp(@Float64.0, @Float64.1, @Float64.2)  -- Float64 clamp
```

All log and trig functions follow IEEE 754 semantics: `NaN` for out-of-domain inputs (e.g. `log(-1.0)`, `asin(2.0)`), `±Infinity` for overflow. The argument order for `atan2` is `(y, x)`, matching POSIX / Python / JavaScript — `atan2(1.0, 1.0)` is `π/4`. `sign` and `clamp` are inlined as WAT (no host call). `pi()` and `e()` inline as `f64.const` constants. The log and trig functions fall to Tier 3 verification (they're uninterpreted in Z3's real-arithmetic fragment).

### Type conversions

```vera
int_to_float(@Int.0)                -- returns Float64 (int to float)
float_to_int(@Float64.0)           -- returns Int (truncation toward zero)
nat_to_int(@Nat.0)                 -- returns Int (identity, both i64)
int_to_nat(@Int.0)                 -- returns Option<Nat> (None if negative)
byte_to_int(@Byte.0)              -- returns Int (zero-extension)
int_to_byte(@Int.0)               -- returns Option<Byte> (None if out of 0..255)
```

Vera has no implicit numeric conversions — use these functions to convert between numeric types. `int_to_float`, `nat_to_int`, and `byte_to_int` are widening conversions that always succeed. `float_to_int` truncates toward zero and traps on NaN/Infinity. `int_to_nat` and `int_to_byte` are checked narrowing conversions that return `Option` — pattern match on the result to handle the failure case. `nat_to_int` and `byte_to_int` are SMT-verifiable (Tier 1); the rest are Tier 3 (runtime).

### Float64 predicates

```vera
float_is_nan(@Float64.0)           -- returns Bool (true if NaN)
float_is_infinite(@Float64.0)      -- returns Bool (true if ±infinity)
nan()                              -- returns Float64 (quiet NaN)
infinity()                         -- returns Float64 (positive infinity)
```

`float_is_nan` and `float_is_infinite` test for IEEE 754 special values. `nan()` and `infinity()` construct them — use `0.0 - infinity()` for negative infinity. All four are Tier 3 (runtime-tested, not SMT-verifiable).

**Shadowing**: If you define a function with the same name as a built-in (e.g. `array_length` for a custom list type), your definition takes priority. The built-in is only used when no user-defined function with that name exists.

Example:

```vera
private fn greet(@String -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  string_concat("Hello, ", @String.0)
}
```

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
  if @Nat.0 == 0 then {
    1
  } else {
    @Nat.0 * factorial(@Nat.0 - 1)
  }
}
```

For nested recursion, use lexicographic ordering: `decreases(@Nat.0, @Nat.1)`.

### Workflow: writing contracts incrementally

**Start with scaffolding, then strengthen.** A function with placeholder contracts type-checks
and compiles:

```vera
requires(true) ensures(true)
```

Fill in real contracts *after* the body type-checks cleanly. Strengthen in this order:

1. Write `requires(true) ensures(true)` and run `vera check` — confirm the body is correct first.
2. Add a `requires` condition for each invariant the caller must satisfy.
3. Add an `ensures` condition describing what the function guarantees. Use `@T.result` for the
   return value.
4. Run `vera verify` — **not just `vera check`** — to confirm contracts are statically provable.
   `vera check` only type-checks; `vera verify` runs Z3.
5. If `vera verify` reports a contract will be checked at runtime (Tier 3), the Z3 solver could
   not prove it. Add a `decreases` clause for recursive functions, or simplify the contract
   expression.
6. Run `vera test` to find counterexamples. If `vera test` reports a failure, the contract is
   reachable and the function body is wrong.

### Quantified expressions

```vera
-- For all indices in [0, bound):
forall(@Nat, array_length(@Array<Int>.0), fn(@Nat -> @Bool) effects(pure) {
  @Array<Int>.0[@Nat.0] > 0
})

-- There exists an index in [0, bound):
exists(@Nat, array_length(@Array<Int>.0), fn(@Nat -> @Bool) effects(pure) {
  @Array<Int>.0[@Nat.0] == 0
})
```

## Effects

Vera is pure by default. All side effects must be declared.

### Declaring effects on functions

```vera
effects(pure)                    -- no effects
effects(<IO>)                    -- performs IO
effects(<Http>)                  -- network access
effects(<State<Int>>)            -- uses integer state
effects(<State<Int>, IO>)        -- multiple effects
effects(<Http, IO>)              -- network + IO
effects(<Async>)                 -- async computation
effects(<Random>)                -- non-deterministic (random number generation)
effects(<Diverge>)               -- may not terminate
effects(<Diverge, IO>)           -- divergent with IO
```

`Diverge` is a built-in marker effect with no operations. Its presence in the
effect row signals that the function may not terminate. Functions without
`Diverge` must be proven total (via `decreases` clauses on recursion).

### Effect declarations

The IO effect is built-in — no declaration is needed. It provides ten operations:

| Operation | Signature | Description |
|-----------|-----------|-------------|
| `IO.print` | `String -> Unit` | Print a string to stdout (no implicit newline; flushes per call) |
| `IO.read_line` | `Unit -> String` | Read a line from stdin |
| `IO.read_file` | `String -> Result<String, String>` | Read file contents |
| `IO.write_file` | `String, String -> Result<Unit, String>` | Write string to file |
| `IO.args` | `Unit -> Array<String>` | Get command-line arguments |
| `IO.exit` | `Int -> Never` | Exit with status code |
| `IO.get_env` | `String -> Option<String>` | Read environment variable |
| `IO.sleep` | `Nat -> Unit` | Pause execution for N milliseconds |
| `IO.time` | `Unit -> Nat` | Current Unix time in milliseconds |
| `IO.stderr` | `String -> Unit` | Print a string to stderr |

If you declare `effect IO { op print(String -> Unit); }` explicitly, that overrides the built-in and only the declared operations are available. Most examples do this — declaring only `print` — because it follows the principle of least privilege: a program that only declares `op print` cannot accidentally perform file I/O or call `exit`.

**Why IO works differently from State and Async:** IO has 10 operations and programs choose which ones they need. State and Async have fixed, minimal operation sets (State: `get`/`put`; Async: no operations, it is a marker effect), so there is nothing to restrict.

**Output buffering and live writes.** Under `vera run` text mode, every `IO.print` call writes to `sys.stdout` and flushes immediately — animations, progress bars, REPLs, and any output using ANSI escape sequences (cursor home, clear screen) render in real time. The captured transcript is *also* preserved in memory so that if the program traps, every byte printed before the trap reaches `WasmTrapError.stdout` and the JSON envelope's `stdout` field. Under `vera run --json`, live mirroring is suppressed — the transcript lives only in the JSON envelope, because writing live to stdout would corrupt the envelope for downstream consumers parsing it. Programs do not need to call any "flush" operation; per-call flushing is the contract. Pre-v0.0.123 the whole transcript was buffered until program exit; that behaviour was correct for trap preservation and JSON consumers but made interactive output invisible.

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

public fn main(-> @Unit)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  match IO.read_file("data.txt") {
    Ok(@String) -> IO.print(@String.0),
    Err(@String) -> IO.print(@String.0)
  };
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

### Exception effects

The `Exn<E>` effect models exceptions with error type `E`:

```vera
effect Exn<E> {
  op throw(E -> Never);
}
```

Throw exceptions using the qualified call syntax:

```vera
private fn safe_div(@Int, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(<Exn<String>>)
{
  if @Int.1 == 0 then {
    Exn.throw("division by zero")
  } else {
    @Int.0 / @Int.1
  }
}
```

Handle exceptions with `handle[Exn<E>]`:

```vera
private fn try_div(@Int, @Int -> @Option<Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[Exn<String>] {
    throw(@String) -> None
  } in {
    Some(safe_div(@Int.0, @Int.1))
  }
}
```

The handler catches the exception and returns a fallback value. The `throw` handler clause receives the error value and must return the same type as the overall `handle` expression. Exception handlers do not use `resume` — throwing is non-resumable.

### Async effect

The `Async` effect enables asynchronous computation with `Future<T>`:

```vera
effects(<Async>)                 -- async computation
effects(<IO, Async>)             -- async with IO
```

`async` and `await` are built-in generic functions:

```vera
private fn compute(@Int, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(<Async>)
{
  let @Future<Int> = async(@Int.1 * 2);
  let @Future<Int> = async(@Int.0 * 3);
  await(@Future<Int>.0) + await(@Future<Int>.1)
}
```

`async(expr)` evaluates `expr` and wraps the result in `Future<T>`. `await(@Future<T>.n)` unwraps it. In the reference implementation, evaluation is eager/sequential — `Future<T>` has the same WASM representation as `T` with no runtime overhead.

### Http effect

The `Http` effect enables network I/O. It is built-in — no `effect Http { ... }` declaration is needed.

| Operation | Signature | Description |
|-----------|-----------|-------------|
| `Http.get` | `String -> Result<String, String>` | HTTP GET request |
| `Http.post` | `String, String -> Result<String, String>` | HTTP POST request (body as JSON; sends `Content-Type: application/json`) |

```vera
effects(<Http>)                  -- network access
effects(<Http, IO>)              -- network + IO
```

Both operations return `Result<String, String>` — `Ok` with the response body on success, `Err` with the error message on failure. Compose with `json_parse` for typed API responses:

```vera
public fn fetch_json(@String -> @Result<Json, String>)
  requires(string_length(@String.0) > 0)
  ensures(true)
  effects(<Http>)
{
  let @Result<String, String> = Http.get(@String.0);
  match @Result<String, String>.0 {
    Ok(@String) -> json_parse(@String.0),
    Err(@String) -> Err(@String.0)
  }
}
```

Like IO, `Http` is a built-in effect. Unlike IO, it has a fixed set of two operations — there is no need to restrict operations via an explicit declaration.

### Inference effect

The `Inference` effect makes LLM calls explicit in the type system. It is built-in — no `effect Inference { ... }` declaration is needed.

| Operation | Signature | Description |
|-----------|-----------|-------------|
| `Inference.complete` | `String -> Result<String, String>` | Send a prompt, return `Ok(completion)` or `Err(message)` |

```vera
effects(<Inference>)             -- LLM access
effects(<Inference, IO>)         -- LLM + console output
effects(<Http, Inference>)       -- fetch + LLM
```

Returns `Result<String, String>` — `Ok` with the completion text on success, `Err` with the error message on failure. Provider is selected from environment variables: `VERA_ANTHROPIC_API_KEY`, `VERA_OPENAI_API_KEY`, `VERA_MOONSHOT_API_KEY` (Kimi), or `VERA_MISTRAL_API_KEY` (auto-detected from whichever key is set). Override with `VERA_INFERENCE_PROVIDER` (valid values: `anthropic`, `openai`, `moonshot`, `mistral`) and `VERA_INFERENCE_MODEL`.

```vera
private fn classify(@String -> @Result<String, String>)
  requires(string_length(@String.0) > 0)
  ensures(true)
  effects(<Inference>)
{
  let @String = string_concat("Classify the sentiment as Positive, Negative, or Neutral: ", @String.0);
  Inference.complete(@String.0)
}
```

Compose with `match` to handle the `Result`:

```vera
public fn safe_classify(@String -> @String)
  requires(string_length(@String.0) > 0)
  ensures(true)
  effects(<Inference>)
{
  let @Result<String, String> = classify(@String.0);
  match @Result<String, String>.0 {
    Ok(@String) -> @String.0,
    Err(@String) -> "unknown"
  }
}
```

Like `Http`, `Inference` is host-backed. The browser runtime returns a detailed `Err` explaining that API keys cannot be safely embedded in client-side JavaScript; use a server-side proxy with `Http` instead.

### Random effect

The `Random` effect provides non-deterministic number generation. Like `IO` and `Http`, it is built-in — no `effect Random { ... }` declaration is needed. Functions that draw random values must declare `effects(<Random>)`, making the non-determinism visible in the type signature.

| Operation | Signature | Description |
|-----------|-----------|-------------|
| `Random.random_int` | `Int, Int -> Int` | Random integer in inclusive range `[low, high]` (caller ensures `low <= high`) |
| `Random.random_float` | `Unit -> Float64` | Uniform random in `[0.0, 1.0)` |
| `Random.random_bool` | `Unit -> Bool` | Coin flip |

```vera
private fn pick_card(@Unit -> @Int)
  requires(true)
  ensures(@Int.result >= 1 && @Int.result <= 52)
  effects(<Random>)
{
  Random.random_int(1, 52)
}
```

The Python runtime backs Random onto the `random` module (`random.randint`, `random.random()`). The browser runtime backs all three onto `Math.random()` — fast, non-cryptographic, adequate for games and simulations. There is no seeding API yet (deterministic testing via `handle[Random]` is future work).

Functions that mix randomness with other effects compose normally:

```vera
public fn print_random_card(-> @Unit)
  requires(true)
  ensures(true)
  effects(<IO, Random>)
{
  IO.print(int_to_string(pick_card(())))
}
```

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

### State handler with a loop helper

The most common State pattern uses a `where` block to define a loop helper with `effects(<State<Int>>)`. The handler wraps the entire computation; the helper calls `get` and `put` directly.

```vera
-- Sum 1..n using State<Int>
private fn add_value(@Int, @Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.1 + @Int.0)
  effects(pure)
{
  @Int.1 + @Int.0
}

public fn sum_with_state(@Nat -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Int>](@Int = 0) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) } with @Int = @Int.0
  } in {
    sum_loop(@Nat.0, 1)
  }
}
where {
  fn sum_loop(@Nat, @Nat -> @Int)
    requires(true)
    ensures(true)
    decreases(@Nat.1 - @Nat.0 + 1)
    effects(<State<Int>>)
  {
    if @Nat.0 > @Nat.1 then {
      get(())
    } else {
      put(add_value(get(()), @Nat.0));
      sum_loop(@Nat.1, @Nat.0 + 1)
    }
  }
}
```

Key points:
- The outer function `sum_with_state` is **pure** — the handler discharges the State effect
- The `where` block helper `sum_loop` has `effects(<State<Int>>)` — it uses `get`/`put` directly
- Functions inside `where` blocks do NOT take `public`/`private` visibility
- The `with @Int = @Int.0` clause updates the handler state when `put` resumes
- Pure helper functions (like `add_value`) can be called from the `where` block helper (`sum_loop`)
- The `decreases` clause on the loop helper ensures termination

## Where Blocks (Mutual Recursion)

```vera
private fn is_even(@Nat -> @Bool)
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

## Abilities (Type Constraints)

Abilities constrain type variables in generic functions. An ability declares operations that a type must support:

```vera
ability Eq<T> {
  op eq(T, T -> Bool);
}
```

Use `where` in the `forall` clause to constrain type parameters:

```vera
private forall<T where Eq<T>> fn are_equal(@T, @T -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  eq(@T.1, @T.0)
}
```

Four built-in abilities are available — no declarations needed:

- **`Eq<T>`** — `eq(x, y)` returns `@Bool`. Satisfied by: Int, Nat, Bool, Float64, String, Byte, Unit, and simple enum ADTs.
- **`Ord<T>`** — `compare(x, y)` returns `@Ordering` (`Less`, `Equal`, `Greater`). Satisfied by: Int, Nat, Bool, Float64, String, Byte.
- **`Hash<T>`** — `hash(x)` returns `@Int`. Satisfied by: Int, Nat, Bool, Float64, String, Byte, Unit.
- **`Show<T>`** — `show(x)` returns `@String`. Satisfied by: Int, Nat, Bool, Float64, String, Byte, Unit.

The `Ordering` type is a built-in ADT with three constructors: `Less`, `Equal`, `Greater`. Use it with pattern matching:

```vera
public fn sign(@Int, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match compare(@Int.1, @Int.0) {
    Less -> 0 - 1,
    Equal -> 0,
    Greater -> 1
  }
}
```

Key rules:
- Abilities are first-order only: `Eq<T>`, not `Mappable<F>` where `F` is a type constructor
- Constraint syntax: `forall<T where Eq<T>>` — constraints go inside the angle brackets
- Multiple constraints: `forall<T where Eq<T>, Ord<T>>`
- Ability declarations mirror effect declarations (both use `op`)
- User-defined abilities are supported with the same syntax
- ADT auto-derivation: Simple enums automatically satisfy `Eq` — the compiler generates structural equality (tag comparison)
- Unsatisfied constraints produce error E613

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

If two imported modules define a function, data type, or constructor with the same name, the compiler reports an error (E608/E609/E610) listing both conflicting modules. Rename one of the conflicting declarations in the source module to resolve the collision. Local definitions shadow imported names without error.

Type aliases and effect declarations are module-local and cannot be imported. If another module needs the same alias or effect, it must declare its own copy.

Module-qualified calls use `::` between the module path and the function name: `vera.math::abs(42)`. The dot-separated path identifies the module and `::` separates it from the function name. This syntax can be used anywhere a function call is valid, and always resolves against the specific module's public declarations — it is not affected by local shadowing. Note: module-qualified calls (`math::abs(42)`) are available for readability but do not yet resolve name collisions in flat compilation — the compiler will still report a collision error. A future version will support qualified-call disambiguation via name mangling.

There is no import aliasing (`import m(abs as math_abs)`) and no wildcard exclusion (`import m hiding(x)`). These are intentional design decisions, not limitations. When names clash across modules, rename the conflicting declaration in one of the source modules. This preserves the one-canonical-form principle — every function has exactly one name.

There are no raw strings (`r"..."`) or multi-line string literals. Use escape sequences for special characters; this is by design — alternative string syntaxes would create two representations for the same value.

The full set of escape sequences Vera's lexer accepts:

| Escape | Produces | Notes |
|---|---|---|
| `\n` | LF (0x0A) | |
| `\t` | TAB (0x09) | |
| `\r` | CR (0x0D) | |
| `\0` | NUL (0x00) | |
| `\\` | backslash | |
| `\"` | double-quote | |
| `\u{XXXX}` | Unicode code point | 1–6 hex digits, up to U+10FFFF |

`\v` / `\f` / `\x..` / `\a` / `\b` are **not** recognised — Vera's rule is "one canonical form per value". For ASCII control bytes outside the simple-escape set (e.g. ESC 0x1B, VT 0x0B, FF 0x0C), either use the unicode escape (`"\u{1B}"`, `"\u{0B}"`, `"\u{0C}"`) or call `string_from_char_code(N)` at runtime:

```vera
-- ANSI cursor-home sequence (ESC [ H):
let @String = string_concat(string_from_char_code(27), "[H");
-- or equivalently using the unicode escape:
let @String = "\u{1B}[H";
```

Raw UTF-8 bytes in string literals are supported — the lexer reads the source as UTF-8 and stores the bytes unchanged. `"██ hello ██"` compiles and prints the six UTF-8 bytes of each block character. `string_length`, indexing, and the classifiers operate on bytes, not grapheme clusters; see the #509 roadmap entry for tracked Unicode-aware variants.

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

## Best Practices

### Keep functions small

Vera's De Bruijn slot references (`@T.n`) are clear when functions have 2–3 parameters of different types. They become harder to track with 4+ parameters of the same type or long let-chains where indices shift with each binding.

**Guidelines:**
- Keep functions under ~5 parameters total
- When multiple parameters share a type, prefer breaking into smaller helper functions or where-functions
- Break long let-chains (4+ bindings of the same type) into where-functions — they create fresh scopes with reset slot indices
- Commutative operations (`+`, `*`) mask index errors; be especially careful with non-commutative operations (`-`, `/`, `<`, `>`) and recursive calls

### Use typed holes to build incrementally

When writing a new function, start with `?` placeholders and check the skeleton first. The `W001` warning tells you the expected type and lists every available binding — it is the cheapest way to confirm the return type is correct before writing the body:

```vera
public fn gcd(@Int, @Int -> @Int)
  requires(@Int.1 > 0 && @Int.0 > 0)
  ensures(@Int.result > 0)
  effects(pure)
{
  ?   -- W001: expected Int. Available bindings: @Int.0: Int; @Int.1: Int
}
```

Read the hint, then fill in the expression. This is especially useful when De Bruijn indices are non-obvious — the hint always shows the correct `@T.n` form for every binding in scope.

### Use where-functions for complex logic

Where-functions are private helpers scoped to their parent function. They reset the slot index namespace, making code easier to reason about:

```vera
public fn process(@Int, @Int, @String -> @Int)
  requires(@Int.1 > 0)
  ensures(true)
  effects(pure)
{
  compute(@Int.1, @Int.0, string_length(@String.0))
}
where {
  fn compute(@Int, @Int, @Int -> @Int)
    requires(true)
    ensures(true)
    effects(pure)
  {
    (@Int.2 + @Int.1) * @Int.0
  }
}
```

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
  if @Nat.0 == 0 then {
    1
  } else {
    @Nat.0 * factorial(@Nat.0 - 1)
  }
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
  if @Nat.0 == 0 then {
    1
  } else {
    @Nat.0 * factorial(@Nat.0 - 1)
  }
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
{
  @Int.0
}
```

CORRECT — `@T.result` is only valid in `ensures`:
```vera
private fn f(@Int -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  @Int.0
}
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
if @Bool.0 then {
  1
} else {
  0
}
```

### Trying to use import aliasing

WRONG — Vera does not support renaming imports:
```vera
import vera.math(abs as math_abs);
```

CORRECT — use selective import and qualified calls for readability:
```vera
import vera.math(abs);
vera.math::abs(-5)
```

Note: if two imported modules define the same name, the compiler reports a collision error (E608/E609/E610). Rename the conflicting declaration in one of the source modules.

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

### Standalone `map_new()` / `set_new()` without type context

WRONG — type inference cannot resolve the key/value or element types:
```vera
let @Map = map_new();
let @Set = set_new();
```

CORRECT — nest inside an operation so types can be inferred, or provide explicit type annotation:
```vera
let @Map<String, Int> = map_new();
map_insert(map_new(), "key", 42)
let @Set<Int> = set_new();
set_add(set_new(), 1)
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

### Iteration with IO

FizzBuzz with a recursive loop and IO effects. `fizzbuzz` is pure; `loop` and `main` have `effects(<IO>)`. Run with `vera run examples/fizzbuzz.vera`.

```vera
effect IO {
  op print(String -> Unit);
}

public fn fizzbuzz(@Nat -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  if @Nat.0 % 15 == 0 then {
    "FizzBuzz"
  } else {
    if @Nat.0 % 3 == 0 then {
      "Fizz"
    } else {
      if @Nat.0 % 5 == 0 then {
        "Buzz"
      } else {
        "\(@Nat.0)"
      }
    }
  }
}

private fn loop(@Nat, @Nat -> @Unit)
  requires(@Nat.0 <= @Nat.1)
  ensures(true)
  effects(<IO>)
{
  IO.print(string_concat(fizzbuzz(@Nat.0), "\n"));
  if @Nat.0 < @Nat.1 then {
    loop(@Nat.1, @Nat.0 + 1)
  } else {
    ()
  }
}

public fn main(@Unit -> @Unit)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  loop(100, 1)
}
```

## Conformance Suite

The `tests/conformance/` directory contains 82 small, self-contained programs that validate every language feature against the spec — one program per feature. These are the best minimal working examples of Vera syntax and semantics.

Each program is organized by spec chapter (`ch01_int_literals.vera`, `ch04_match_basic.vera`, `ch07_state_handler.vera`, etc.) and the `manifest.json` file maps features to programs. When you need to see how a specific construct works, check the conformance program before reading the spec.

Key conformance programs by feature:

| Feature | Program |
|---------|---------|
| Slot references (`@T.n`) | `ch03_slot_basic.vera`, `ch03_slot_indexing.vera` |
| Typed holes (`?`) | `ch03_typed_holes.vera` |
| Match expressions | `ch04_match_basic.vera`, `ch04_match_nested.vera` |
| Contracts (requires/ensures) | `ch06_requires.vera`, `ch06_ensures.vera` |
| Effect handlers | `ch07_state_handler.vera`, `ch07_exn_handler.vera` |
| Closures | `ch05_closures.vera` |
| Generics | `ch02_generics.vera` |
| Recursive ADTs | `ch02_adt_recursive.vera` |

## Known Limitations

These are known limitations in the current reference implementation. Most are tracked as open issues; those without an issue link are noted as such.

| Limitation | Details | Issue |
|-----------|---------|-------|
| Effect row variable unification | Effect rows containing type variables (e.g. `<E>` in a generic function) are not unified with concrete effect rows at call sites. Functions that abstract over effects require explicit row declarations. | [#294](https://github.com/aallan/vera/issues/294) |
| `map_new()` / `set_new()` require type context | The empty-collection constructors `map_new()` and `set_new()` cannot infer their key/value types without a surrounding type annotation. Assign the result to a typed `let` binding: `let @Map<String, Int> = map_new();` | — |
| `Inference.complete` has no `max_tokens` or temperature controls | The host implementation uses provider defaults. Custom parameters (max tokens, temperature, top-p, system prompt) are not yet supported at the Vera level. | [#370](https://github.com/aallan/vera/issues/370) |
| `Inference` effect has no user-defined handlers | In the current implementation, `Inference` is always host-backed (dispatches to a real API). User-defined handlers for mocking, local models, or replay are not yet supported. | [#372](https://github.com/aallan/vera/issues/372) |

## Known Bugs and Workarounds

Current reference-implementation bugs that an agent writing Vera code is likely to hit. Every entry has a confirmed reproducer and a known workaround. The full curated list is in [KNOWN_ISSUES.md](https://github.com/aallan/vera/blob/main/KNOWN_ISSUES.md); the issue tracker is the source of truth.

| Shape | Bug summary | Workaround | Issue |
|---|---|---|---|
| Pair-type closure capture | A closure that captures an outer `String` or `Array<T>` binding compiles and runs without error, but the captured value's len field is silently dropped — the closure reads it as empty. Single-pointer ADTs (`Option`, `Result`, user `data`, `Map`/`Set`/`Decimal`/`Regex`) work; only pair types are affected. The historical [#514](https://github.com/aallan/vera/issues/514) "all heap captures broken" framing was inaccurate; v0.0.121 fixed nested closures and ADT captures, leaving this residual. | Lift the closure body to a top-level `private fn` and pass the pair-typed value as an explicit parameter — the parameter path through `_compile_lifted_closure` handles pair types correctly; only the capture path is broken. See [What you cannot capture](#what-you-cannot-capture) above. | [#535](https://github.com/aallan/vera/issues/535) |
| Tail-call optimization disabled for allocating functions | v0.0.126 ([#517](https://github.com/aallan/vera/issues/517)) ships WASM `return_call` for tail-position calls so non-allocating tail recursion runs in constant stack space. Allocating functions revert `return_call` → `call` because `return_call` discards the GC epilogue and would leak shadow-stack slots — so an allocating tail-recursive function still pays a WASM frame per iteration and traps with `call stack exhausted` at ~tens of thousands of frames. | Restructure to allocate outside the recursion (build the heap value at the top level, recurse over an `@Int` accumulator), or iterate via `array_fold` / `array_map` which compile to WASM loops with no per-iteration frame cost. | [#549](https://github.com/aallan/vera/issues/549) |
| WASM call translators | 10 pre-existing bugs in the decomposed `vera/wasm/calls_*.py` modules. The ones most likely to trip code up: `to_string(INT64_MIN)` produces `-` (negation overflow); `string_slice` / `array_slice` with indices `\|i\| > i32.MAX` wrap to negative then clamp to 0 silently; `string_char_code` with an out-of-range index reads arbitrary memory; `parse_nat` / `parse_int` accept embedded spaces (`"12 34"` parses as 1234). | For now: avoid those edge cases, or convert via alternate paths (e.g. `@Int.0 + 1` works for serialising INT64_MIN+1 when INT64_MIN itself would hit the bug). | [#475](https://github.com/aallan/vera/issues/475) |
| Large single allocations | `$alloc` grows the WASM memory by one page (64 KB) when the free list is exhausted. A single request larger than that traps with an out-of-bounds memory access even though the WASM max-memory limit is much higher. | Avoid single `$alloc` calls > 64 KB. For big arrays, pre-size or build via append loops that grow gradually. | [#487](https://github.com/aallan/vera/issues/487) |

When a Vera program type-checks cleanly, compiles without errors, and then produces a runtime trap you can't explain, check for one of these shapes: a closure capturing a `String` or `Array<T>` reading as empty is [#535](https://github.com/aallan/vera/issues/535); `call stack exhausted` from a tail-recursive *allocating* function is [#549](https://github.com/aallan/vera/issues/549) (non-allocating tail recursion runs in constant stack space as of v0.0.126). Runtime trap diagnostics are now Vera-native end-to-end: each trap carries a `kind` label (`divide_by_zero` / `out_of_bounds` / `stack_exhausted` / `unreachable` / `overflow` / `contract_violation` / `unknown`), a per-kind `Fix:` paragraph naming the canonical remediation, and a source backtrace pointing at the offending Vera function and line — not just `wasm trap: <reason>`.

## Specification Reference

The full language specification is in the [`spec/`](https://github.com/aallan/vera/tree/main/spec) directory of the repository:

| Chapter | Spec | Topic |
|---------|------|-------|
| 0 | [Introduction](https://github.com/aallan/vera/blob/main/spec/00-introduction.md) | Design goals, diagnostics philosophy |
| 1 | [Lexical Structure](https://github.com/aallan/vera/blob/main/spec/01-lexical-structure.md) | Tokens, operators, formatting |
| 2 | [Types](https://github.com/aallan/vera/blob/main/spec/02-types.md) | Type system, refinement types |
| 3 | [Slot References](https://github.com/aallan/vera/blob/main/spec/03-slot-references.md) | The @T.n reference system |
| 4 | [Expressions](https://github.com/aallan/vera/blob/main/spec/04-expressions.md) | Expressions and statements |
| 5 | [Functions](https://github.com/aallan/vera/blob/main/spec/05-functions.md) | Functions and contracts |
| 6 | [Contracts](https://github.com/aallan/vera/blob/main/spec/06-contracts.md) | Verification system |
| 7 | [Effects](https://github.com/aallan/vera/blob/main/spec/07-effects.md) | Algebraic effect system |
| 9 | [Standard Library](https://github.com/aallan/vera/blob/main/spec/09-standard-library.md) | Built-in types, effects, functions |
| 10 | [Grammar](https://github.com/aallan/vera/blob/main/spec/10-grammar.md) | Formal EBNF grammar |
| 11 | [Compilation](https://github.com/aallan/vera/blob/main/spec/11-compilation.md) | Compilation model and WASM target |
| 12 | [Runtime](https://github.com/aallan/vera/blob/main/spec/12-runtime.md) | Runtime execution, host bindings, memory model |
