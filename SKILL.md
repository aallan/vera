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
vera typecheck file.vera          # Same as check (explicit alias)
vera verify file.vera             # Type-check and verify contracts via Z3
vera verify --json file.vera      # Verify with JSON diagnostics
vera compile file.vera                    # Compile to .wasm binary
vera compile --wat file.vera              # Print WAT text (human-readable WASM)
vera compile --json file.vera             # Compile with JSON diagnostics
vera compile --target browser file.vera   # Compile + emit browser bundle (wasm + JS + html)
vera run file.vera                # Compile and execute (calls main)
vera run file.vera --fn f -- 42   # Call function f with argument 42
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
pytest tests/ -v                  # Run the test suite
```

Errors are natural language instructions explaining what went wrong and how to fix it. Feed them back into your context to correct the code.

### Browser compilation

`vera compile --target browser` produces a ready-to-serve browser bundle:

```bash
vera compile --target browser file.vera            # Output to file_browser/
vera compile --target browser file.vera -o dist/   # Output to dist/
```

This generates three files: `module.wasm` (the compiled binary), `vera-runtime.mjs` (self-contained JavaScript runtime with all host bindings), and `index.html` (loads and runs the program). Serve the output directory with any HTTP server (`python -m http.server`) and open `index.html` — ES module imports require HTTP, not `file://`.

The JavaScript runtime provides browser-appropriate implementations: `IO.print` writes to the page, `IO.read_line` uses `prompt()`, file IO returns `Result.Err`, and all other operations (State, contracts, Markdown) work identically to the Python runtime.

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

Every diagnostic has a stable error code (`E001`–`E702`) grouped by compiler phase:

- **E001–E007** — Parse errors (missing contracts, unexpected tokens)
- **E010** — Transform errors (internal)
- **E120–E176** — Type check: core + expressions (type mismatches, slot resolution, operators)
- **E200–E233** — Type check: calls (unresolved functions, argument mismatches, module calls)
- **E300–E335** — Type check: control flow (if/match, patterns, effect handlers)
- **E500–E525** — Verification (contract violations, undecidable fallbacks)
- **E600–E607** — Codegen (unsupported features)
- **E700–E702** — Testing (contract violations, input generation, execution errors)

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
  if @Int.0 >= 0 then {
    @Int.0
  } else {
    -@Int.0
  }
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

## Built-in Functions

### Option and Result Combinators

When a program defines `Option<T>` or `Result<T, E>`, combinator functions are automatically available:

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

> **Limitation ([#293](https://github.com/aallan/vera/issues/293)):** When a combinator's type variable appears only in a return position (not in any argument), the type checker cannot infer it from a bare constructor like `None` or `Err("msg")`. Use a typed binding instead:
>
> ```vera
> -- Won't type-check: option_map(None, fn(@Int -> @Int) effects(pure) { @Int.0 + 1 })
> -- Use a typed binding:
> let @Option<Int> = None;
> option_map(@Option<Int>.0, fn(@Int -> @Int) effects(pure) { @Int.0 + 1 })
> ```

### Array operations

```vera
array_length(@Array<Int>.0)             -- returns Int (always >= 0)
array_append(@Array<Int>.0, @Int.0)     -- returns Array<Int> (new array with element appended)
array_range(@Int.0, @Int.1)             -- returns Array<Int> (integers [start, end))
array_concat(@Array<Int>.0, @Array<Int>.1)  -- returns Array<Int> (merge two arrays)
```

### String operations

```vera
string_length(@String.0)                -- returns Nat
string_concat(@String.0, @String.1)     -- returns String
string_slice(@String.0, @Nat.0, @Nat.1) -- returns String (start, end)
char_code(@String.0, @Int.0)            -- returns Nat (ASCII code at index)
from_char_code(@Nat.0)                  -- returns String (single char from code point)
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
strip(@String.0)                        -- returns String (trim whitespace)
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
starts_with(@String.0, @String.1)      -- returns Bool (prefix test)
ends_with(@String.0, @String.1)        -- returns Bool (suffix test)
index_of(@String.0, @String.1)         -- returns Option<Nat> (first occurrence)
```

`string_contains` checks whether the needle appears anywhere in the haystack. `starts_with` and `ends_with` test prefix and suffix matches. `index_of` returns `Some(i)` with the byte offset of the first match, or `None` if not found. An empty needle always matches (returns `true` or `Some(0)`).

#### String transformation

```vera
to_upper(@String.0)                             -- returns String (ASCII uppercase)
to_lower(@String.0)                             -- returns String (ASCII lowercase)
replace(@String.0, @String.1, @String.2)        -- returns String (replace all)
split(@String.0, @String.1)                     -- returns Array<String> (split by delimiter)
join(@Array<String>.0, @String.0)               -- returns String (join with separator)
```

`to_upper` and `to_lower` convert ASCII letters only (a-z ↔ A-Z). `replace` substitutes all non-overlapping occurrences; an empty needle returns the original string unchanged. `split` returns an array of segments; an empty delimiter returns a single-element array. `join` concatenates array elements with the separator between each pair.

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

### Type conversions

```vera
to_float(@Int.0)                    -- returns Float64 (int to float)
float_to_int(@Float64.0)           -- returns Int (truncation toward zero)
nat_to_int(@Nat.0)                 -- returns Int (identity, both i64)
int_to_nat(@Int.0)                 -- returns Option<Nat> (None if negative)
byte_to_int(@Byte.0)              -- returns Int (zero-extension)
int_to_byte(@Int.0)               -- returns Option<Byte> (None if out of 0..255)
```

Vera has no implicit numeric conversions — use these functions to convert between numeric types. `to_float`, `nat_to_int`, and `byte_to_int` are widening conversions that always succeed. `float_to_int` truncates toward zero and traps on NaN/Infinity. `int_to_nat` and `int_to_byte` are checked narrowing conversions that return `Option` — pattern match on the result to handle the failure case. `nat_to_int` and `byte_to_int` are SMT-verifiable (Tier 1); the rest are Tier 3 (runtime).

### Float64 predicates

```vera
is_nan(@Float64.0)                 -- returns Bool (true if NaN)
is_infinite(@Float64.0)            -- returns Bool (true if ±infinity)
nan()                              -- returns Float64 (quiet NaN)
infinity()                         -- returns Float64 (positive infinity)
```

`is_nan` and `is_infinite` test for IEEE 754 special values. `nan()` and `infinity()` construct them — use `0.0 - infinity()` for negative infinity. All four are Tier 3 (runtime-tested, not SMT-verifiable).

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
effects(<State<Int>>)            -- uses integer state
effects(<State<Int>, IO>)        -- multiple effects
effects(<Async>)                 -- async computation
effects(<Diverge>)               -- may not terminate
effects(<Diverge, IO>)           -- divergent with IO
```

`Diverge` is a built-in marker effect with no operations. Its presence in the
effect row signals that the function may not terminate. Functions without
`Diverge` must be proven total (via `decreases` clauses on recursion).

### Effect declarations

The IO effect is built-in — no declaration is needed. It provides seven operations:

| Operation | Signature | Description |
|-----------|-----------|-------------|
| `IO.print` | `String -> Unit` | Print a string to stdout |
| `IO.read_line` | `Unit -> String` | Read a line from stdin |
| `IO.read_file` | `String -> Result<String, String>` | Read file contents |
| `IO.write_file` | `String, String -> Result<Unit, String>` | Write string to file |
| `IO.args` | `Unit -> Array<String>` | Get command-line arguments |
| `IO.exit` | `Int -> Never` | Exit with status code |
| `IO.get_env` | `String -> Option<String>` | Read environment variable |

If you declare `effect IO { op print(String -> Unit); }` explicitly, that overrides the built-in and only the declared operations are available. Most examples do this — declaring only `print` — because it follows the principle of least privilege: a program that only declares `op print` cannot accidentally perform file I/O or call `exit`.

**Why IO works differently from State and Async:** IO has 7 operations and programs choose which ones they need. State and Async have fixed, minimal operation sets (State: `get`/`put`; Async: no operations, it is a marker effect), so there is nothing to restrict.

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

The built-in `Eq` ability is automatically available — no declaration needed. Call `eq(x, y)` to compare values of a constrained type.

Key rules:
- Abilities are first-order only: `Eq<T>`, not `Mappable<F>` where `F` is a type constructor
- Constraint syntax: `forall<T where Eq<T>>` — constraints go inside the angle brackets
- Multiple constraints: `forall<T where Eq<T>, Ord<T>>`
- Ability declarations mirror effect declarations (both use `op`)
- User-defined abilities are supported with the same syntax

> **Note:** The built-in `Eq` ability is fully compilable for primitive types (Int, Nat, Bool, Float64, String, Byte, Unit). The monomorphizer checks constraint satisfaction (E613), and ability operation calls (`eq`) are rewritten to native equality at compile time. ADT auto-derivation and other abilities (Ord, Hash, Show) are planned for a future release.

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

## Best Practices

### Keep functions small

Vera's De Bruijn slot references (`@T.n`) are clear when functions have 2–3 parameters of different types. They become harder to track with 4+ parameters of the same type or long let-chains where indices shift with each binding.

**Guidelines:**
- Keep functions under ~5 parameters total
- When multiple parameters share a type, prefer breaking into smaller helper functions or where-functions
- Break long let-chains (4+ bindings of the same type) into where-functions — they create fresh scopes with reset slot indices
- Commutative operations (`+`, `*`) mask index errors; be especially careful with non-commutative operations (`-`, `/`, `<`, `>`) and recursive calls

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

The `tests/conformance/` directory contains 39 small, self-contained programs that validate every language feature against the spec — one program per feature. These are the best minimal working examples of Vera syntax and semantics.

Each program is organized by spec chapter (`ch01_int_literals.vera`, `ch04_match_basic.vera`, `ch07_state_handler.vera`, etc.) and the `manifest.json` file maps features to programs. When you need to see how a specific construct works, check the conformance program before reading the spec.

Key conformance programs by feature:

| Feature | Program |
|---------|---------|
| Slot references (`@T.n`) | `ch03_slot_basic.vera`, `ch03_slot_indexing.vera` |
| Match expressions | `ch04_match_basic.vera`, `ch04_match_nested.vera` |
| Contracts (requires/ensures) | `ch06_requires.vera`, `ch06_ensures.vera` |
| Effect handlers | `ch07_state_handler.vera`, `ch07_exn_handler.vera` |
| Closures | `ch05_closures.vera` |
| Generics | `ch02_generics.vera` |
| Recursive ADTs | `ch02_adt_recursive.vera` |

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
