# Chapter 9: Standard Library

## 9.1 Overview

Vera's standard library provides built-in types, effects, and functions that are available in every Vera program without explicit import. The library is deliberately small — it includes only the types and operations that are universally needed and cannot be expressed purely in user code.

The standard library comprises:

- **Built-in ADTs**: `Option<T>` and `Result<T, E>` for representing partiality and fallibility.
- **Built-in collections**: `Array<T>` for fixed-size homogeneous sequences, plus future collections (`Set<T>`, `Map<K, V>`).
- **Built-in effects**: `IO` for output, `State<T>` for mutable state, plus future effects for networking, concurrency, and LLM inference.
- **Built-in functions**: `array_length`, `array_append`, `array_range`, and `array_concat` for arrays, numeric operations (`abs`, `min`, `max`, `floor`, `ceil`, `round`, `sqrt`, `pow`), type conversions (`int_to_float`, `float_to_int`, `nat_to_int`, `int_to_nat`, `byte_to_int`, `int_to_byte`), Float64 predicates (`float_is_nan`, `float_is_infinite`, `nan`, `infinity`), string search (`string_contains`, `string_starts_with`, `string_ends_with`, `string_index_of`), string transformation (`string_upper`, `string_lower`, `string_replace`, `string_split`, `string_join`, `string_from_char_code`), regular expressions (`regex_match`, `regex_find`, `regex_find_all`, `regex_replace`), plus future functions for vector similarity.
- **Future types**: `Json` for structured data interchange, `Markdown` for agent-oriented document structure, `Decimal` for exact arithmetic.
- **Built-in abilities**: `Eq`, `Ord`, `Hash`, `Show` — type constraints for generic programming. The `Ordering` ADT (`Less`, `Equal`, `Greater`) supports `Ord`'s `compare` operation.

All built-in types participate fully in the type system: they can appear in contracts, be verified by the SMT solver, and be used with refinement types and pattern matching. Built-in effects follow the same algebraic effect semantics as user-defined effects (see Chapter 7).

### 9.1.1 Naming Convention

Built-in function names follow a consistent `domain_verb` convention to make names predictable and reduce LLM hallucination errors:

| Pattern | When to use | Examples |
|---------|-------------|----------|
| `domain_verb` | Most functions — domain prefix identifies the type or module | `string_length`, `array_append`, `regex_match`, `md_parse` |
| `source_to_target` | Type conversions — source and target types in the name | `int_to_float`, `float_to_int`, `nat_to_int`, `int_to_byte` |
| `domain_is_predicate` | Boolean predicates — domain prefix + `is_` + property | `float_is_nan`, `float_is_infinite` |
| Prefix-less | Math universals only — names understood across all languages | `abs`, `min`, `max`, `floor`, `ceil`, `round`, `sqrt`, `pow` |

**Key rules:**

1. **String operations always use `string_` prefix**: `string_contains`, `string_starts_with`, `string_split`, `string_join`, `string_strip`, `string_upper`, `string_lower`, `string_replace`, `string_index_of`, `string_char_code`, `string_from_char_code`.
2. **Float64 predicates use `float_` prefix**: `float_is_nan`, `float_is_infinite`.
3. **Type conversions use `source_to_target`**: `int_to_float` (not `to_float`), `float_to_int`, `int_to_nat`.
4. **Math functions are the only exception** to domain prefixing — `abs`, `min`, `max`, `floor`, `ceil`, `round`, `sqrt`, `pow` need no prefix because they are universally understood.
5. **New functions must follow these patterns.** When adding a function, choose the pattern that matches its category. If uncertain, use `domain_verb`.

## 9.2 Primitive Types

The primitive types (`Int`, `Nat`, `Bool`, `Byte`, `Float64`, `String`, `Unit`, `Never`) are documented in Chapter 2, Section 2.2. They are not part of the standard library per se — they are built into the language core.

## 9.3 Built-in ADTs

### 9.3.1 Option\<T\>

```
public data Option<T> {
  Some(T),
  None
}
```

`Option<T>` represents a value that may or may not be present. It is the standard way to express partiality in Vera — functions that might not produce a result return `Option<T>` rather than using null pointers or sentinel values.

Constructors:
- `Some(@T)` — wraps a present value.
- `None` — represents absence.

Pattern matching on `Option<T>` is exhaustive: both `Some` and `None` must be handled.

```
private fn safe_head(@Array<Int> -> @Option<Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  if array_length(@Array<Int>.0) > 0 then {
    Some(@Array<Int>.0[0])
  } else {
    None
  }
}
```

### 9.3.2 Result\<T, E\>

```
public data Result<T, E> {
  Ok(T),
  Err(E)
}
```

`Result<T, E>` represents a computation that may succeed with a value of type `T` or fail with an error of type `E`. It is the standard way to express fallible operations without using exceptions.

Constructors:
- `Ok(@T)` — wraps a successful result.
- `Err(@E)` — wraps an error value.

Pattern matching on `Result<T, E>` is exhaustive: both `Ok` and `Err` must be handled.

```
private fn parse_nat(@Int -> @Result<Nat, String>)
  requires(true)
  ensures(true)
  effects(pure)
{
  if @Int.0 >= 0 then {
    Ok(@Int.0)
  } else {
    Err("negative")
  }
}
```

### 9.3.3 UrlParts

```
data UrlParts {
  UrlParts(String, String, String, String, String)
}
```

`UrlParts` is a built-in ADT representing the five components of a URL per RFC 3986: scheme, authority, path, query, and fragment. Programs must redefine `UrlParts` locally (like `Result` and `Option`) to use it in match expressions.

Constructors:
- `UrlParts(@String, @String, @String, @String, @String)` — scheme, authority, path, query, fragment.

See §9.6.13 for the `url_parse` and `url_join` function specifications.

### 9.3.4 Future\<T\>

```
data Future<T> { Future(T) }
```

`Future<T>` represents the result of an asynchronous computation. It is WASM-transparent: it has the same runtime representation as `T`, with no overhead.

Constructors:
- `Future(@T)` — wraps a value.

See §9.5.4 for the `async` and `await` function specifications.

### 9.3.5 MdInline

```
public data MdInline {
  MdText(String),
  MdCode(String),
  MdEmph(Array<MdInline>),
  MdStrong(Array<MdInline>),
  MdLink(Array<MdInline>, String),
  MdImage(String, String)
}
```

`MdInline` represents inline-level Markdown content. It is one of two mutually defined ADTs (with `MdBlock`) that make illegal states unrepresentable — a heading cannot contain another heading at the type level.

Constructors:
- `MdText(@String)` — plain text run.
- `MdCode(@String)` — inline code span.
- `MdEmph(@Array<MdInline>)` — emphasis (italic).
- `MdStrong(@Array<MdInline>)` — strong emphasis (bold).
- `MdLink(@Array<MdInline>, @String)` — hyperlink: display text and URL.
- `MdImage(@String, @String)` — image: alt text and source URL.

See §9.7.3 for the Markdown function specifications.

### 9.3.6 MdBlock

```
public data MdBlock {
  MdParagraph(Array<MdInline>),
  MdHeading(Nat, Array<MdInline>),
  MdCodeBlock(String, String),
  MdBlockQuote(Array<MdBlock>),
  MdList(Bool, Array<Array<MdBlock>>),
  MdThematicBreak,
  MdTable(Array<Array<Array<MdInline>>>),
  MdDocument(Array<MdBlock>)
}
```

`MdBlock` represents block-level Markdown elements.

Constructors:
- `MdParagraph(@Array<MdInline>)` — paragraph.
- `MdHeading(@Nat, @Array<MdInline>)` — heading: level (1--6) and content.
- `MdCodeBlock(@String, @String)` — fenced code block: language and code body.
- `MdBlockQuote(@Array<MdBlock>)` — block quote.
- `MdList(@Bool, @Array<Array<MdBlock>>)` — list: ordered/unordered, with items.
- `MdThematicBreak` — horizontal rule (nullary).
- `MdTable(@Array<Array<Array<MdInline>>>)` — table: rows of cells of inlines.
- `MdDocument(@Array<MdBlock>)` — top-level document.

See §9.7.3 for the Markdown function specifications.

### 9.3.7 Option and Result Combinators

The standard prelude provides combinator functions that eliminate common match boilerplate for `Option<T>` and `Result<T, E>`. These are automatically available when the corresponding ADT is defined.

**Option combinators:**

| Function | Signature | Description |
|----------|-----------|-------------|
| `option_unwrap_or` | `forall<T> (Option<T>, T) -> T` | Extract `Some` value or return default |
| `option_map` | `forall<A, B> (Option<A>, fn(A -> B)) -> Option<B>` | Transform the value inside `Some` |
| `option_and_then` | `forall<A, B> (Option<A>, fn(A -> Option<B>)) -> Option<B>` | Chain fallible operations |

**Result combinators:**

| Function | Signature | Description |
|----------|-----------|-------------|
| `result_unwrap_or` | `forall<T, E> (Result<T, E>, T) -> T` | Extract `Ok` value or return default |
| `result_map` | `forall<A, B, E> (Result<A, E>, fn(A -> B)) -> Result<B, E>` | Transform the `Ok` value |

Combinators follow the `domain_verb` naming convention (see §5). They are injected as private generic functions before compilation and undergo normal monomorphization. A combinator is not injected if the user defines a function with the same name.

## 9.4 Built-in Collections

### 9.4.1 Array\<T\>

`Array<T>` is a fixed-size, homogeneous, immutable ordered collection. Arrays are created with array literal syntax and accessed by integer index.

**Syntax:**

```
let @Array<Int> = [1, 2, 3];
@Array<Int>.0[0]
```

**Properties:**
- Fixed size: the length is determined at creation and cannot change.
- Immutable: elements cannot be modified after creation.
- Zero-indexed: the first element is at index 0.
- Bounds-checked: indexing with an out-of-range index causes a runtime trap (see Chapter 12).

**Element types:** Arrays can contain any type for which a WASM representation exists, including primitives (`Int`, `Nat`, `Bool`, `Byte`, `Float64`), ADT types (`Option<Int>`, `Result<Nat, String>`), `String`, and nested arrays (`Array<Array<Int>>`).

**Length:** The `array_length` built-in function returns the number of elements (see Section 9.6.1).

For the compilation model of arrays, see Chapter 11, Section 11.12.

### 9.4.2 Set\<T\> (Future)

> **Status: Not yet implemented.** Tracked in [#62](https://github.com/aallan/vera/issues/62). Depends on Abilities ([#60](https://github.com/aallan/vera/issues/60)).

`Set<T>` will be an unordered collection of unique elements. It will require the `Eq` and `Hash` abilities on `T` (see Section 9.8).

Operations will include union, intersection, difference, membership testing, and size.

### 9.4.3 Map\<K, V\> (Future)

> **Status: Not yet implemented.** Tracked in [#62](https://github.com/aallan/vera/issues/62). Depends on Abilities ([#60](https://github.com/aallan/vera/issues/60)).

`Map<K, V>` will be a key-value mapping. It will require the `Eq` and `Hash` abilities on `K`.

`Map` is already implicitly needed by the proposed `Json` ADT (Section 9.7.1), where `JObject` wraps a `Map<String, Json>`.

## 9.5 Built-in Effects

### 9.5.1 IO

The `IO` effect provides input/output operations. Functions that perform IO must declare `effects(<IO>)`.

The `IO` effect has no type parameters. All IO operations are invoked as qualified calls (`IO.print(...)`, `IO.read_line(())`, etc.).

**Operations:**

| Operation | Signature | Description |
|-----------|-----------|-------------|
| `print` | `String -> Unit` | Write a UTF-8 string to stdout |
| `read_line` | `Unit -> String` | Read one line from stdin (trailing newline stripped) |
| `read_file` | `String -> Result<String, String>` | Read file contents; returns `Ok(contents)` or `Err(message)` |
| `write_file` | `String, String -> Result<Unit, String>` | Write string to file; returns `Ok(())` or `Err(message)` |
| `args` | `Unit -> Array<String>` | Command-line arguments |
| `exit` | `Int -> Never` | Terminate with exit code (never returns) |
| `get_env` | `String -> Option<String>` | Look up environment variable; returns `Some(value)` or `None` |

The IO effect is registered as a built-in — programs do not need to declare `effect IO { ... }` to use these operations. If a program does declare its own `effect IO` block, the user declaration overrides the built-in (for backward compatibility, but only the explicitly declared operations are available).

```
private fn hello(-> @Unit)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  IO.print("hello, world")
}
```

File operations return `Result` types for error handling:

```
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

For the runtime implementation of IO operations, see Chapter 12, Section 12.4.1.

### 9.5.2 State\<T\>

```
effect State<T> {
  op get(Unit -> T);
  op put(T -> Unit);
}
```

The `State<T>` effect provides mutable state operations. Functions that read or write state must declare the specific state type in their effect row: `effects(<State<Int>>)`.

Operations:
- `State<T>.get()` — reads the current state value. The `Unit` parameter is implicit.
- `State<T>.put(@T)` — writes a new state value.

Multiple independent state types can be used in the same function by declaring them in the effect row. State operations (`get`, `put`) are called without qualification — the type checker resolves which state cell is targeted from the types:

```
private fn increment(-> @Unit)
  requires(true)
  ensures(new(State<Int>) == old(State<Int>) + 1)
  effects(<State<Int>>)
{
  let @Int = get(());
  put(@Int.0 + 1);
  ()
}
```

State is handled by providing an initial value and a handler that manages the mutable cell:

```
private fn run_increment(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Int>](@Int = 0) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    let @Int = get(());
    put(@Int.0 + 1);
    get(())
  }
}
```

For the runtime implementation of `State<T>`, see Chapter 12, Section 12.4.2.

### 9.5.3 Http (Future)

> **Status: Not yet implemented.** Tracked in [#57](https://github.com/aallan/vera/issues/57).

Network I/O will be modelled as an algebraic effect with operations like `get` and `post`. Functions performing network access will declare `effects(<Http>)`. Handlers will provide the implementation: real HTTP in production, mocks in tests.

```
effect Http {
  op get(String -> String);
  op post(String, String -> String);
}
```

This fits naturally with Vera's algebraic effect system and makes network I/O explicit and testable.

When the `<Async>` effect is available, Http naturally composes with it for concurrent requests:

```
private fn fetch_both(@String, @String -> @Tuple<Json, Json>)
  requires(true)
  ensures(true)
  effects(<Http, Async>)
{
  let @Future<Json> = async(Http.get(@String.0));
  let @Future<Json> = async(Http.get(@String.1));
  let @Json = await(@Future<Json>.1);
  let @Json = await(@Future<Json>.0);
  Tuple(@Json.1, @Json.0)
}
```

### 9.5.4 Async

The `<Async>` effect enables asynchronous computation via `async(expr)` and `await(future)` operations with a `Future<T>` type (see §9.3.4 for the ADT definition).

**Built-in functions:**

```
fn async<T>(@T.0 -> @Future<T>) effects(<Async>)
fn await<T>(@Future<T>.0 -> @T) effects(<Async>)
```

**Example:**

```
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

Key design points:
- `async(expr)` evaluates `expr` and wraps the result in `Future<T>`.
- `await(@Future<T>.n)` unwraps the future, yielding the result of type `T`.
- The `<Async>` effect must be declared, making concurrency explicit and trackable.
- `Async` is a marker effect with no operations — `async` and `await` are built-in generic functions that require `effects(<Async>)`.
- `Future<T>` is WASM-transparent: it has the same runtime representation as `T`, with no overhead.
- The reference implementation evaluates `async(expr)` eagerly (sequential execution). True concurrent scheduling will be available when WASI 0.3 support is added ([#237](https://github.com/aallan/vera/issues/237)).
- Custom scheduling strategies (thread pool, event loop) can be provided via `handle[Async]` handlers (see [#270](https://github.com/aallan/vera/issues/270)).
- This avoids coloured-function problems because algebraic effects already separate the description of an operation from its execution.

### 9.5.5 Inference (Future)

> **Status: Not yet implemented.** Tracked in [#61](https://github.com/aallan/vera/issues/61).

LLM inference will be modelled as an algebraic effect, making model calls explicit in the type system:

```
effect Inference {
  op complete(String -> String);
  op embed(String -> Array<Float64>);
}
```

Operations:
- `complete(@String)` — sends a prompt to a language model and returns the completion.
- `embed(@String)` — computes a vector embedding of the input string.

Any function that calls an LLM declares `effects(<Inference>)`. Pure functions cannot secretly call models. Contracts still apply: preconditions on inference inputs are verified normally. Postconditions on outputs can use refinement types to constrain response format.

Handlers provide the implementation: one handler uses an HTTP API, another uses a local model, another uses cached replay for deterministic testing.

```
private fn classify(@String -> @String)
  requires(length(@String.0) > 0)
  ensures(true)
  effects(<Inference>)
{
  Inference.complete("Classify as Spam or Ham: " ++ @String.0)
}
```

## 9.6 Built-in Functions

### 9.6.1 array\_length

```
public forall<T> fn array_length(@Array<T> -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
```

Returns the number of elements in an array. The result is always non-negative. `array_length` is generic over the element type.

```
let @Array<Int> = [10, 20, 30];
array_length(@Array<Int>.0)
```

This expression evaluates to `3`.

For the compilation of `array_length`, see Chapter 11, Section 11.12.

### 9.6.2 array\_append

```
public forall<T> fn array_append(@Array<T>, @T -> @Array<T>)
  requires(true)
  ensures(true)
  effects(pure)
```

Returns a new array with the element appended at the end. The returned array has length `array_length(input) + 1`, with the new element at the last index. The original array is unchanged (arrays are immutable values). `array_append` is generic over the element type.

```
let @Array<Int> = array_append([10, 20, 30], 40);
array_length(@Array<Int>.0)
```

This expression evaluates to `4`.

### 9.6.3 array\_range

```vera
public fn array_range(@Int, @Int -> @Array<Int>)
  requires(true)
  ensures(true)
  effects(pure)
```

Produces an array of integers over the half-open interval `[start, end)`. The first argument is the start (inclusive) and the second is the end (exclusive). If `start >= end`, the result is an empty array. The elements are consecutive integers from `start` to `end - 1`.

```vera
array_range(0, 5)       -- [0, 1, 2, 3, 4]
array_range(3, 7)       -- [3, 4, 5, 6]
array_range(5, 5)       -- [] (empty, start == end)
array_range(10, 3)      -- [] (empty, start > end)
```

### 9.6.4 array\_concat

```vera
public forall<T> fn array_concat(@Array<T>, @Array<T> -> @Array<T>)
  requires(true)
  ensures(true)
  effects(pure)
```

Merges two arrays into a single array. The elements of the first array appear before the elements of the second. The result has length `array_length(first) + array_length(second)`. Both input arrays are unchanged (arrays are immutable values). `array_concat` is generic over the element type.

```vera
array_concat([1, 2, 3], [4, 5])       -- [1, 2, 3, 4, 5]
array_concat([], [1, 2])               -- [1, 2]
array_concat([1, 2], [])               -- [1, 2]
array_concat([], [])                   -- [] (empty)
```

### 9.6.5 array\_slice

```vera
public forall<T> fn array_slice(@Array<T>, @Int, @Int -> @Array<T>)
  requires(true)
  ensures(true)
  effects(pure)
```

Returns a new array containing elements from index `start` (inclusive) to `end` (exclusive). Indices are clamped to `[0, array_length(input)]`, so out-of-range values produce shorter slices rather than traps. If `start >= end` after clamping, returns an empty array. The original array is unchanged.

```vera
array_slice([10, 20, 30, 40, 50], 1, 4)  -- [20, 30, 40]
array_slice([10, 20, 30], 0, 2)          -- [10, 20]
array_slice([10, 20, 30], 5, 10)         -- [] (clamped, empty)
array_slice([10, 20, 30], 2, 1)          -- [] (start >= end)
```

### 9.6.6 array\_map

```vera
public forall<A, B> fn array_map(@Array<A>, fn(A -> B) effects(pure) -> @Array<B>)
  requires(true)
  ensures(true)
  effects(pure)
```

Applies a function to each element of the array and returns a new array of the results. The result has the same length as the input. The element type may change (e.g. mapping `Int` to `String`).

```vera
array_map([1, 2, 3], fn(@Int -> @Int) effects(pure) { @Int.0 * 10 })
-- [10, 20, 30]
```

### 9.6.7 array\_filter

```vera
public forall<T> fn array_filter(@Array<T>, fn(T -> Bool) effects(pure) -> @Array<T>)
  requires(true)
  ensures(true)
  effects(pure)
```

Returns a new array containing only the elements for which the predicate returns `true`. The result length is between 0 and the input length. Element order is preserved.

```vera
array_filter([1, 2, 3, 4, 5, 6], fn(@Int -> @Bool) effects(pure) { @Int.0 > 3 })
-- [4, 5, 6]
```

### 9.6.8 array\_fold

```vera
public forall<T, U> fn array_fold(@Array<T>, @U, fn(U, T -> U) effects(pure) -> @U)
  requires(true)
  ensures(true)
  effects(pure)
```

Reduces an array to a single value by applying a function to an accumulator and each element, left to right. The second argument is the initial accumulator value. The accumulator type may differ from the element type.

```vera
array_fold([1, 2, 3, 4], 0, fn(@Int, @Int -> @Int) effects(pure) { @Int.1 + @Int.0 })
-- 10 (0 + 1 + 2 + 3 + 4)
```

### 9.6.9 Numeric Operations

Vera provides eight built-in numeric functions for common mathematical operations. The integer functions (`abs`, `min`, `max`) operate on `Int` values and are pure — they perform no effects and are fully verifiable by the SMT solver (Tier 1). The floating-point functions (`floor`, `ceil`, `round`, `sqrt`, `pow`) use IEEE 754 semantics via WebAssembly's native instructions.

#### abs

```
public fn abs(@Int -> @Nat)
  requires(true)
  ensures(@Nat.result >= 0)
  effects(pure)
```

Returns the absolute value of an integer. The result type is `Nat` because absolute values are always non-negative. Both `Nat` and `Int` are `i64` at the WASM level, so this involves no runtime conversion.

```
abs(-42)
```

This expression evaluates to `42`.

#### min

```
public fn min(@Int, @Int -> @Int)
  requires(true)
  ensures(@Int.result <= @Int.0 && @Int.result <= @Int.1)
  effects(pure)
```

Returns the smaller of two integers.

```
min(3, 7)
```

This expression evaluates to `3`.

#### max

```
public fn max(@Int, @Int -> @Int)
  requires(true)
  ensures(@Int.result >= @Int.0 && @Int.result >= @Int.1)
  effects(pure)
```

Returns the larger of two integers.

```
max(3, 7)
```

This expression evaluates to `7`.

#### floor

```
public fn floor(@Float64 -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
```

Returns the largest integer less than or equal to the input. Compiles to `f64.floor` followed by `i64.trunc_f64_s`. Traps on NaN or out-of-range values (WASM semantics).

```
floor(3.7)
```

This expression evaluates to `3`.

#### ceil

```
public fn ceil(@Float64 -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
```

Returns the smallest integer greater than or equal to the input. Compiles to `f64.ceil` followed by `i64.trunc_f64_s`. Traps on NaN or out-of-range values (WASM semantics).

```
ceil(3.2)
```

This expression evaluates to `4`.

#### round

```
public fn round(@Float64 -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
```

Rounds to the nearest integer using banker's rounding (IEEE 754 roundTiesToEven). This means `round(2.5)` evaluates to `2`, not `3` — ties round to the nearest even integer. Compiles to `f64.nearest` followed by `i64.trunc_f64_s`. Traps on NaN or out-of-range values (WASM semantics).

```
round(3.7)
```

This expression evaluates to `4`.

#### sqrt

```
public fn sqrt(@Float64 -> @Float64)
  requires(true)
  ensures(true)
  effects(pure)
```

Returns the square root of a floating-point number. Compiles directly to the WASM `f64.sqrt` instruction.

```
sqrt(4.0)
```

This expression evaluates to `2.0`.

#### pow

```
public fn pow(@Float64, @Int -> @Float64)
  requires(true)
  ensures(true)
  effects(pure)
```

Raises a floating-point base to an integer exponent. The exponent is `Int`, not `Float64` — this avoids silent truncation of fractional exponents. Negative exponents produce reciprocals (`pow(2.0, -1)` evaluates to `0.5`). Implemented via exponentiation by squaring for efficiency.

```
pow(2.0, 10)
```

This expression evaluates to `1024.0`.

### 9.6.10 Type Conversions

Vera has no implicit numeric conversions. The following built-in functions provide explicit conversions between numeric types.

#### Widening conversions (always succeed)

```
public fn int_to_float(@Int -> @Float64)
  requires(true)
  ensures(true)
  effects(pure)
```

Converts an integer to a floating-point number. Compiled to `f64.convert_i64_s`.

```
int_to_float(42)
```

This expression evaluates to `42.0`.

```
public fn nat_to_int(@Nat -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
```

Converts a natural number to a signed integer. This is a no-op at runtime — both types share the same representation (i64). The postcondition captures the invariant that the result is non-negative.

```
nat_to_int(abs(42))
```

This expression evaluates to `42`.

```
public fn byte_to_int(@Byte -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
```

Converts a byte (0–255) to a signed integer. Compiled to `i64.extend_i32_u` (unsigned zero-extension from i32 to i64).

```
byte_to_int(@Byte.0)
```

#### Narrowing conversions (may fail)

```
public fn float_to_int(@Float64 -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
```

Truncates a floating-point number toward zero. Traps on NaN or Infinity (consistent with `floor`, `ceil`, and `round`). Compiled to `i64.trunc_f64_s`.

```
float_to_int(3.9)
```

This expression evaluates to `3` (truncation toward zero, not rounding).

```
public fn int_to_nat(@Int -> @Option<Nat>)
  requires(true)
  ensures(true)
  effects(pure)
```

Checked narrowing from signed integer to natural number. Returns `Some(n)` if the input is non-negative, `None` otherwise.

```
match int_to_nat(42) {
  Some(@Nat) -> nat_to_int(@Nat.0),
  None -> 0 - 1
}
```

This expression evaluates to `42`.

```
public fn int_to_byte(@Int -> @Option<Byte>)
  requires(true)
  ensures(true)
  effects(pure)
```

Checked narrowing from signed integer to byte. Returns `Some(b)` if the input is in the range 0–255, `None` otherwise.

```
match int_to_byte(65) {
  Some(@Byte) -> byte_to_int(@Byte.0),
  None -> 0 - 1
}
```

This expression evaluates to `65`.

### 9.6.11 Float64 Predicates

Vera provides built-in functions for testing and constructing IEEE 754 special float values (NaN and infinity).

#### Predicates

```
public fn float_is_nan(@Float64 -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
```

Tests whether a Float64 value is NaN (not a number). NaN is the only value that is not equal to itself. Compiled to `f64.ne(x, x)`.

```vera
public fn test_is_nan(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ if float_is_nan(nan()) then { 1 } else { 0 } }
```

This expression evaluates to `1`.

```
public fn float_is_infinite(@Float64 -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
```

Tests whether a Float64 value is positive or negative infinity. Compiled to `f64.eq(f64.abs(x), inf)`. Returns `false` for NaN.

```vera
public fn test_is_infinite(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ if float_is_infinite(infinity()) then { 1 } else { 0 } }
```

This expression evaluates to `1`.

#### Constants

```
public fn nan(-> @Float64)
  requires(true)
  ensures(true)
  effects(pure)
```

Returns a quiet NaN value. Compiled to `f64.const nan`.

```vera
public fn test_nan(@Unit -> @Float64)
  requires(true) ensures(true) effects(pure)
{ nan() }
```

```vera
public fn infinity(-> @Float64)
  requires(true)
  ensures(true)
  effects(pure)
```

Returns positive infinity. Negative infinity can be obtained via `0.0 - infinity()`. Compiled to `f64.const inf`.

```vera
public fn test_infinity(@Unit -> @Float64)
  requires(true) ensures(true) effects(pure)
{ infinity() }
```

### 9.6.12 String Search

String search functions test for the presence or position of substrings. All are pure, take `String` arguments, and operate on raw bytes (ASCII). All are Tier 3 for verification (String is not modeled in Z3).

#### string_contains

```vera
public fn string_contains(@String, @String -> @Bool)
  requires(true) ensures(true) effects(pure)
```

Returns `true` if the second argument (needle) appears as a contiguous substring of the first (haystack). An empty needle always matches. Uses a naive O(n×m) byte comparison.

```vera
string_contains("hello world", "world")  -- true
string_contains("hello", "xyz")          -- false
string_contains("hello", "")             -- true
```

#### string_starts_with

```vera
public fn string_starts_with(@String, @String -> @Bool)
  requires(true) ensures(true) effects(pure)
```

Returns `true` if the haystack begins with the given prefix. An empty prefix always matches. If the prefix is longer than the haystack, returns `false`.

```vera
string_starts_with("hello world", "hello")  -- true
string_starts_with("hello", "world")        -- false
string_starts_with("hello", "")             -- true
```

#### string_ends_with

```vera
public fn string_ends_with(@String, @String -> @Bool)
  requires(true) ensures(true) effects(pure)
```

Returns `true` if the haystack ends with the given suffix. An empty suffix always matches. If the suffix is longer than the haystack, returns `false`.

```vera
string_ends_with("hello world", "world")  -- true
string_ends_with("hello", "world")        -- false
string_ends_with("hello", "")             -- true
```

#### string_index_of

```vera
public fn string_index_of(@String, @String -> @Option<Nat>)
  requires(true) ensures(true) effects(pure)
```

Returns `Some(i)` where `i` is the byte offset of the first occurrence of the needle in the haystack, or `None` if not found. An empty needle matches at position 0. The returned index is a `Nat` (natural number).

```vera
match string_index_of("hello world", "world") {
  Some(@Nat) -> nat_to_int(@Nat.0),
  None -> 0 - 1
}
-- evaluates to 6
```

### 9.6.13 String Transformation

String transformation functions produce new strings by modifying characters or structure. All allocate heap memory for the result and register it with the GC shadow stack. All are pure and Tier 3.

#### string_upper

```vera
public fn string_upper(@String -> @String)
  requires(true) ensures(true) effects(pure)
```

Returns a new string with all ASCII lowercase letters (a–z, bytes 97–122) converted to uppercase (A–Z, bytes 65–90). Non-ASCII bytes and non-letter bytes are unchanged.

```vera
string_upper("hello")   -- "HELLO"
string_upper("Hello!")   -- "HELLO!"
string_upper("123")      -- "123"
```

#### string_lower

```vera
public fn string_lower(@String -> @String)
  requires(true) ensures(true) effects(pure)
```

Returns a new string with all ASCII uppercase letters (A–Z, bytes 65–90) converted to lowercase (a–z, bytes 97–122). Non-ASCII bytes and non-letter bytes are unchanged.

```vera
string_lower("HELLO")   -- "hello"
string_lower("Hello!")   -- "hello!"
string_lower("123")      -- "123"
```

#### string_replace

```vera
public fn string_replace(@String, @String, @String -> @String)
  requires(true) ensures(true) effects(pure)
```

Replaces all non-overlapping occurrences of the needle (second argument) in the haystack (first argument) with the replacement (third argument). If the needle is empty, returns a copy of the haystack. Uses a two-pass algorithm: pass 1 counts occurrences, then allocates the output buffer; pass 2 copies bytes with substitutions.

```vera
string_replace("hello world", "world", "vera")  -- "hello vera"
string_replace("aaa", "a", "bb")                -- "bbbbbb"
string_replace("hello", "xyz", "abc")           -- "hello"
string_replace("hello", "", "x")                -- "hello"
```

#### string_split

```vera
public fn string_split(@String, @String -> @Array<String>)
  requires(true) ensures(true) effects(pure)
```

Splits the string at each non-overlapping occurrence of the delimiter, returning an `Array<String>`. If the delimiter is empty, returns a single-element array containing the original string. Consecutive delimiters produce empty string segments. Uses a two-pass algorithm: pass 1 counts delimiters, then allocates the array and segment buffers in pass 2.

```vera
string_split("a,b,c", ",")     -- Array with 3 elements: "a", "b", "c"
string_split("hello", ",")     -- Array with 1 element: "hello"
string_split("a,,b", ",")      -- Array with 3 elements: "a", "", "b"
```

#### string_join

```vera
public fn string_join(@Array<String>, @String -> @String)
  requires(true) ensures(true) effects(pure)
```

Joins an array of strings with the given separator between each pair of elements. An empty array produces an empty string. Uses a two-pass algorithm: pass 1 sums the total length, pass 2 copies bytes.

```vera
string_join(string_split("a,b,c", ","), "-")  -- "a-b-c"
string_join(string_split("hello", ","), "-")  -- "hello"
```

#### string_from_char_code

```vera
public fn string_from_char_code(@Nat -> @String)
  requires(true) ensures(true) effects(pure)
```

Creates a single-character (1-byte) string from an ASCII code point. Inverse of `string_char_code`. Allocates 1 byte of heap memory for the result.

```vera
string_from_char_code(65)                        -- "A"
string_char_code(string_from_char_code(65), 0)          -- 65 (roundtrip)
string_concat(string_from_char_code(72), string_from_char_code(105))  -- "Hi"
```

#### string_repeat

```vera
public fn string_repeat(@String, @Nat -> @String)
  requires(true) ensures(true) effects(pure)
```

Repeats a string a given number of times. Allocates `length(s) × n` bytes of heap memory and fills the result by cycling through the source bytes.

```vera
string_repeat("ab", 3)                   -- "ababab"
string_repeat("x", 5)                    -- "xxxxx"
string_repeat("hello", 0)                -- "" (empty)
string_repeat("", 100)                   -- "" (empty)
```

### 9.6.14 Parsing Functions

Parsing functions convert strings to typed values, returning `Result<T, String>` to represent success or failure. All strip leading and trailing ASCII whitespace (spaces, tabs, `\r`, `\n`) before parsing. All are pure and Tier 3 for verification.

The `Result` type used by parsing functions is the standard ADT:

```vera
private data Result<T, E> { Ok(T), Err(E) }
```

On success, the `Ok` variant contains the parsed value. On failure, the `Err` variant contains a descriptive error message string.

#### parse_nat

```vera
public fn parse_nat(@String -> @Result<Nat, String>)
  requires(true) ensures(true) effects(pure)
```

Parses a non-negative integer from a string. After stripping whitespace, the remaining characters must all be ASCII digits (`0`–`9`). Leading zeros are permitted (e.g., `"007"` parses as `7`).

Error messages:
- `"empty string"` — the input is empty or contains only whitespace
- `"invalid digit"` — a non-digit character was encountered

```vera
parse_nat("42")        -- Ok(42)
parse_nat("  7  ")     -- Ok(7)   (whitespace stripped)
parse_nat("007")       -- Ok(7)   (leading zeros allowed)
parse_nat("abc")       -- Err("invalid digit")
parse_nat("")          -- Err("empty string")
parse_nat("  ")        -- Err("empty string")
```

#### parse_int

```vera
public fn parse_int(@String -> @Result<Int, String>)
  requires(true) ensures(true) effects(pure)
```

Parses a signed integer from a string. After stripping whitespace, an optional leading `+` or `-` sign is consumed. The remaining characters must all be ASCII digits (`0`–`9`). A bare sign with no digits (e.g., `"-"`) is an error.

Error messages:
- `"empty string"` — the input is empty or contains only whitespace
- `"invalid character"` — a non-digit character was encountered (after any sign)

```vera
parse_int("42")        -- Ok(42)
parse_int("-7")        -- Ok(-7)
parse_int("+3")        -- Ok(3)
parse_int("  -42  ")   -- Ok(-42) (whitespace stripped)
parse_int("abc")       -- Err("invalid character")
parse_int("-")         -- Err("invalid character")
parse_int("")          -- Err("empty string")
```

#### parse_float64

```vera
public fn parse_float64(@String -> @Result<Float64, String>)
  requires(true) ensures(true) effects(pure)
```

Parses a 64-bit floating-point number from a string. After stripping whitespace, an optional leading `-` sign is consumed, followed by one or more digits, an optional decimal point with additional digits, and an optional exponent (`e` or `E` followed by an optional sign and digits). At least one digit must appear in the integer part.

Error messages:
- `"empty string"` — the input is empty or contains only whitespace
- `"invalid character"` — a non-digit, non-`.`, non-`e`/`E` character was encountered

```vera
parse_float64("3.14")      -- Ok(3.14)
parse_float64("-2.5")      -- Ok(-2.5)
parse_float64("42")        -- Ok(42.0)
parse_float64("  1.0  ")   -- Ok(1.0) (whitespace stripped)
parse_float64("abc")       -- Err("invalid character")
parse_float64("")          -- Err("empty string")
```

#### parse_bool

```vera
public fn parse_bool(@String -> @Result<Bool, String>)
  requires(true) ensures(true) effects(pure)
```

Parses a boolean from a string. After stripping whitespace, the remaining content must be exactly `"true"` or `"false"` (strict lowercase). No other forms are accepted — `"True"`, `"TRUE"`, `"yes"`, `"1"`, etc. all produce errors. This strictness prevents ambiguity when models generate boolean values.

Error messages:
- `"expected true or false"` — the input does not match `"true"` or `"false"` after whitespace stripping

```vera
parse_bool("true")         -- Ok(true)
parse_bool("false")        -- Ok(false)
parse_bool("  true  ")     -- Ok(true) (whitespace stripped)
parse_bool("True")         -- Err("expected true or false")
parse_bool("yes")          -- Err("expected true or false")
parse_bool("")             -- Err("expected true or false")
```

### 9.6.15 Base64

#### base64\_encode

```
public fn base64_encode(@String -> @String)
  requires(true)
  ensures(string_length(@String.result) == ((string_length(@String.0) + 2) / 3) * 4
          || string_length(@String.0) == 0 && string_length(@String.result) == 0)
  effects(pure)
```

Encodes a UTF-8 string to standard Base64 (RFC 4648). Every 3 input bytes produce 4 output characters from the alphabet `A`–`Z`, `a`–`z`, `0`–`9`, `+`, `/`. Remaining 1–2 bytes are padded with `=`. An empty input produces an empty string.

```vera
base64_encode("Hello, World!")   -- "SGVsbG8sIFdvcmxkIQ=="
base64_encode("ABC")             -- "QUJD"
base64_encode("A")               -- "QQ=="
base64_encode("")                 -- ""
```

#### base64\_decode

```
public fn base64_decode(@String -> @Result<String, String>)
  requires(true)
  ensures(true)
  effects(pure)
```

Decodes a standard Base64 string (RFC 4648) to its original UTF-8 bytes. Returns `Ok(String)` on success or `Err(String)` with an error message on failure.

**Error conditions:**

- `"invalid base64 length"` — the input length is not a multiple of 4
- `"invalid base64"` — the input contains characters outside the Base64 alphabet

```vera
base64_decode("QUJD")                  -- Ok("ABC")
base64_decode("SGVsbG8sIFdvcmxkIQ==")  -- Ok("Hello, World!")
base64_decode("QQ==")                  -- Ok("A")
base64_decode("")                      -- Ok("")
base64_decode("ABC")                   -- Err("invalid base64 length")
base64_decode("QQ!!")                  -- Err("invalid base64")
```

### 9.6.16 URL Encoding

#### url\_encode

```
public fn url_encode(@String -> @String)
  requires(true)
  ensures(true)
  effects(pure)
```

Percent-encodes a string for use in URLs (RFC 3986). Unreserved characters (`A`–`Z`, `a`–`z`, `0`–`9`, `-`, `_`, `.`, `~`) pass through unchanged. All other bytes are encoded as `%XX` where `XX` is the uppercase hexadecimal representation of the byte value.

```vera
url_encode("Hello, World!")     -- "Hello%2C%20World%21"
url_encode("foo@bar.com")       -- "foo%40bar.com"
url_encode("a b c")             -- "a%20b%20c"
url_encode("safe-text_123.~")   -- "safe-text_123.~"
url_encode("")                  -- ""
```

#### url\_decode

```
public fn url_decode(@String -> @Result<String, String>)
  requires(true)
  ensures(true)
  effects(pure)
```

Decodes a percent-encoded string (RFC 3986). Each `%XX` sequence is converted to the byte with that hexadecimal value. Both uppercase and lowercase hex digits are accepted. Returns `Ok(String)` on success or `Err(String)` with an error message on failure.

**Error conditions:**

- `"invalid percent-encoding"` — truncated `%` sequence (fewer than 2 hex digits following `%`) or invalid hex digits

```vera
url_decode("Hello%2C%20World%21")  -- Ok("Hello, World!")
url_decode("%41%42%43")            -- Ok("ABC")
url_decode("hello")               -- Ok("hello")
url_decode("")                     -- Ok("")
url_decode("%ZZ")                  -- Err("invalid percent-encoding")
url_decode("%4")                   -- Err("invalid percent-encoding")
```

### 9.6.17 URL Parsing

The `UrlParts` ADT is defined in §9.3.3. Programs must redefine `UrlParts` locally (like `Result` and `Option`) to use it in match expressions.

```
public fn url_parse(@String -> @Result<UrlParts, String>)
  requires(true)
  ensures(true)
  effects(pure)
```

Decomposes a URL string into its RFC 3986 components. Returns `Ok(UrlParts(scheme, authority, path, query, fragment))` on success, or `Err("missing scheme")` if no `:` delimiter is found. Missing optional components (authority, query, fragment) are represented as empty strings.

```
url_parse("https://example.com/path?q=1#frag")
  -- Ok(UrlParts("https", "example.com", "/path", "q=1", "frag"))
url_parse("http:")
  -- Ok(UrlParts("http", "", "", "", ""))
url_parse("file:///path")
  -- Ok(UrlParts("file", "", "/path", "", ""))
url_parse("no-scheme")
  -- Err("missing scheme")
```

```
public fn url_join(@UrlParts -> @String)
  requires(true)
  ensures(true)
  effects(pure)
```

Reassembles a `UrlParts` value into a URL string. If the scheme is non-empty, the `://` separator is inserted. The `?` and `#` delimiters are only included when their respective components are non-empty.

```
url_join(UrlParts("https", "example.com", "/path", "q=1", "frag"))
  -- "https://example.com/path?q=1#frag"
url_join(UrlParts("", "", "", "", ""))
  -- ""
```

### 9.6.18 similarity (Future)

> **Status: Not yet implemented.** Will be introduced alongside the `Inference` effect ([#61](https://github.com/aallan/vera/issues/61)).

```
public fn similarity(@Array<Float64>, @Array<Float64> -> @Float64)
  requires(array_length(@Array<Float64>.0) == array_length(@Array<Float64>.1))
  ensures(@Float64.result >= -1.0 && @Float64.result <= 1.0)
  effects(pure)
```

Computes the cosine similarity between two vectors (embeddings). The arrays must have equal length (enforced by precondition). The result is in the range \[-1, 1\], where 1 indicates identical direction, 0 indicates orthogonality, and -1 indicates opposite direction.

This function is pure — it performs no effects. It is intended for use with the `Inference.embed` operation to compare semantic similarity of text.

### 9.6.19 Regular Expressions

Four pure functions for pattern matching on strings using regular expressions. All accept patterns in standard regex syntax and return `Result` types to safely handle invalid patterns.

#### regex\_match

```
public fn regex_match(@String, @String -> @Result<Bool, String>)
  requires(true)
  ensures(true)
  effects(pure)
```

Tests whether the input string (first argument) contains a substring matching the regex pattern (second argument). Returns `Ok(true)` if a match is found, `Ok(false)` otherwise, or `Err(msg)` if the pattern is invalid.

```vera
let @Result<Bool, String> = regex_match("hello123", "\\d+");
-- Ok(true) — digits found
```

#### regex\_find

```
public fn regex_find(@String, @String -> @Result<Option<String>, String>)
  requires(true)
  ensures(true)
  effects(pure)
```

Returns the first substring of the input that matches the pattern. Returns `Ok(Some(match))` if found, `Ok(None)` if not found, or `Err(msg)` for invalid patterns.

```vera
let @Result<Option<String>, String> = regex_find("abc123def", "\\d+");
-- Ok(Some("123"))
```

#### regex\_find\_all

```
public fn regex_find_all(@String, @String -> @Result<Array<String>, String>)
  requires(true)
  ensures(true)
  effects(pure)
```

Returns all non-overlapping substrings of the input that match the pattern. Always returns full match strings (group 0), even when the pattern contains capture groups. Returns `Ok([])` (empty array) if no matches are found, or `Err(msg)` for invalid patterns.

```vera
let @Result<Array<String>, String> = regex_find_all("a1b2c3", "\\d");
-- Ok(["1", "2", "3"])
```

#### regex\_replace

```
public fn regex_replace(@String, @String, @String -> @Result<String, String>)
  requires(true)
  ensures(true)
  effects(pure)
```

Replaces the **first** occurrence of the pattern in the input string with the replacement string (third argument). Returns the modified string, or the original string unchanged if no match is found. Returns `Err(msg)` for invalid patterns.

```vera
let @Result<String, String> = regex_replace("hello world", "world", "vera");
-- Ok("hello vera")
```

**Implementation note:** These functions are implemented as host imports — they delegate to the runtime's native regex engine (Python's `re` module for wasmtime, JavaScript's `RegExp` for the browser runtime). This avoids embedding a regex engine in WASM while providing access to mature, well-tested implementations.

## 9.7 Built-in Types (Future)

### 9.7.1 Json (Future)

> **Status: Not yet implemented.** Tracked in [#58](https://github.com/aallan/vera/issues/58). Depends on `Map<K, V>` ([#62](https://github.com/aallan/vera/issues/62)).

JSON will be a standard library ADT, not a primitive type:

```
public data Json {
  JNull,
  JBool(Bool),
  JNumber(Float64),
  JString(String),
  JArray(Array<Json>),
  JObject(Map<String, Json>)
}
```

Parse and serialize operations will belong in the standard library. Refinement types can express JSON schemas:

```
type ApiResponse = { @Json | has_field(@Json.0, "status") };
```

This approach keeps the core language small while providing ergonomic JSON support.

### 9.7.2 Decimal (Future)

> **Status: Not yet implemented.** Tracked in [#62](https://github.com/aallan/vera/issues/62).

`Decimal` will provide exact decimal arithmetic for financial and precision-sensitive applications. It will be implemented as a library type (not a primitive) since WebAssembly does not have native decimal floating-point. The runtime will provide a software implementation.

### 9.7.3 Markdown

Markdown is the lingua franca of large language models — they understand it natively and generate it naturally. A typed Markdown ADT makes document structure visible to the type system, enabling contracts that verify the structural properties of agent output.

Markdown is represented as two mutually defined ADTs: `MdBlock` for block-level elements (§9.3.6) and `MdInline` for inline-level content (§9.3.5). The two-level design makes illegal states unrepresentable — a heading cannot contain another heading at the type level.

```
public data MdInline {
  MdText(String),
  MdCode(String),
  MdEmph(Array<MdInline>),
  MdStrong(Array<MdInline>),
  MdLink(Array<MdInline>, String),
  MdImage(String, String)
}
```

`MdInline` constructors:
- `MdText(@String)` — plain text run. The leaf node of all inline content.
- `MdCode(@String)` — inline code span. Essential for agent communication about code.
- `MdEmph(@Array<MdInline>)` — emphasis (italic). Contains recursive inline content.
- `MdStrong(@Array<MdInline>)` — strong emphasis (bold). Contains recursive inline content.
- `MdLink(@Array<MdInline>, @String)` — hyperlink: display text (inline content) and target URL.
- `MdImage(@String, @String)` — image: alt text and source URL.

```
public data MdBlock {
  MdParagraph(Array<MdInline>),
  MdHeading(Nat, Array<MdInline>),
  MdCodeBlock(String, String),
  MdBlockQuote(Array<MdBlock>),
  MdList(Bool, Array<Array<MdBlock>>),
  MdThematicBreak,
  MdTable(Array<Array<Array<MdInline>>>),
  MdDocument(Array<MdBlock>)
}
```

`MdBlock` constructors:
- `MdParagraph(@Array<MdInline>)` — paragraph: a sequence of inline content.
- `MdHeading(@Nat, @Array<MdInline>)` — heading: level (1--6) as `Nat`, plus inline content. The level is a number rather than six separate constructors, allowing contracts like `@Nat.0 >= 1 && @Nat.0 <= 6`.
- `MdCodeBlock(@String, @String)` — fenced code block: language tag and code body. Critical for agents working with source code.
- `MdBlockQuote(@Array<MdBlock>)` — block quote: contains recursive block content.
- `MdList(@Bool, @Array<Array<MdBlock>>)` — list: ordered (`true`) or unordered (`false`), with each item containing block content.
- `MdThematicBreak` — horizontal rule. Nullary constructor.
- `MdTable(@Array<Array<Array<MdInline>>>)` — table: rows of cells, each cell containing inline content. Tables are a GitHub Flavored Markdown extension, not strict CommonMark, but they are ubiquitous in agent communication and document conversion output.
- `MdDocument(@Array<MdBlock>)` — top-level document: a sequence of blocks.

**Design note.** The following Markdown constructs are intentionally excluded per the one-canonical-form principle (§0.2.3). Each has a canonical equivalent in the ADT:

- **Raw HTML** (block and inline) — not safe for verification, not appropriate for agent-to-agent communication.
- **Link reference definitions** — resolved to inline `MdLink` during parsing. The parsed ADT has no reference indirection.
- **Setext headings** — merged with ATX headings into `MdHeading`. Both surface syntaxes parse to the same constructor.
- **Indented code blocks** — merged with fenced code blocks into `MdCodeBlock` (with an empty language string).
- **Hard and soft line breaks** — collapsed into paragraph text. Not structurally significant for agent communication.

**Parse and render operations:**

```
public fn md_parse(@String -> @Result<MdBlock, String>)
  requires(true)
  ensures(true)
  effects(pure)
```

Parses a Markdown string into an `MdDocument`. Returns `Err` if parsing fails. This is pure — it transforms one value to another with no side effects.

```
public fn md_render(@MdBlock -> @String)
  requires(true)
  ensures(true)
  effects(pure)
```

Renders an `MdBlock` to a canonical Markdown string. Always succeeds. The round-trip property `md_parse(md_render(b)) == Ok(b)` should hold: rendering then re-parsing preserves structure.

**Accessor functions for contracts:**

```
public fn md_has_heading(@MdBlock, @Nat -> @Bool)
  requires(@Nat.0 >= 1 && @Nat.0 <= 6)
  ensures(true)
  effects(pure)
```

Returns `true` if the document contains a heading of the given level.

```
public fn md_has_code_block(@MdBlock, @String -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
```

Returns `true` if the document contains a code block with the given language tag.

```
public fn md_extract_code_blocks(@MdBlock, @String -> @Array<String>)
  requires(true)
  ensures(true)
  effects(pure)
```

Extracts the code content from all code blocks with the given language tag. This is the key agent operation: extract code from documentation.

**Refinement type examples:**

Refinement types can express structural requirements on Markdown documents:

```
type HasTitle = { @MdBlock | md_has_heading(@MdBlock.0, 1) };
type HasVeraCode = { @MdBlock | md_has_code_block(@MdBlock.0, "vera") };
```

These predicates call pure functions, placing them in Tier 2 (extended, function calls in contracts). For small documents they may be verifiable by Z3 with function unrolling; for larger documents they fall to Tier 3 (runtime checks).

**Document conversion:**

Document conversion (PDF, Word, HTML, etc. to Markdown) is not part of the language specification. Vera provides the types; conversion uses the `IO` effect with host bindings that delegate to external tools:

```
public fn convert_to_markdown(@String -> @Result<MdBlock, String>)
  requires(true)
  ensures(true)
  effects(<IO>)
```

The host runtime can import tools like MarkItDown or pandoc. The WASM module receives a clean `MdBlock` value through the host binding.

**Connection to the Inference effect:**

`Inference.complete()` (Section 9.5.5) returns `String`. Callers compose explicitly to get Markdown:

```
let @String = Inference.complete("Write a report about: " ++ @String.0);
match md_parse(@String.0) {
  Ok(@MdBlock) -> @MdBlock.0,
  Err(@String) -> MdDocument([MdParagraph([MdText(@String.0)])])
}
```

This follows the same pattern as JSON: `json_parse(Http.get(url))`, not a dedicated `get_json` operation. One way to do things (§0.2.3).

## 9.8 Abilities

> **Status: Implemented.** Tracked in [#60](https://github.com/aallan/vera/issues/60). Four built-in abilities (`Eq`, `Ord`, `Hash`, `Show`) are fully compilable. Supported types: Int, Nat, Bool, Float64, String, Byte, Unit. `Eq` supports ADT auto-derivation for simple enums and ADTs whose fields are all Eq-satisfying primitive types. The built-in `Ordering` ADT (`Less`, `Equal`, `Greater`) is available for `Ord`'s `compare` operation.

Vera supports restricted abilities for constraining type variables in generic functions. To support practical generic programming — sorting, hashing, serialisation — type variables need constraints. Vera adopts restricted abilities rather than full typeclasses:

```
ability Eq<T> {
  op eq(T, T -> Bool);
}

ability Ord<T> {
  op compare(T, T -> Ordering);
}

public forall<T where Eq<T>> fn contains(@Array<T>, @T -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  exists(@Nat, array_length(@Array<T>.0), fn(@Nat -> @Bool) effects(pure) {
    eq(@Array<T>.0[@Nat.0], @T.0)
  })
}
```

Key design points:

1. **No higher-kinded types.** No `Functor`, `Monad`, or `Applicative`. Abilities are first-order only: `Eq<T>`, not `Mappable<F>` where `F` is a type constructor. This preserves decidable type checking and prevents the abstraction hierarchy that makes code harder for LLMs to generate correctly.

2. **Built-in abilities** are auto-derivable for ADTs composed of types that already support them: `Eq`, `Ord`, `Hash`, `Encode`, `Decode`, `Show`. If all fields of an ADT support `Eq`, the ADT supports `Eq` automatically. Four abilities are currently built-in: `Eq`, `Ord`, `Hash`, and `Show`.

3. **User-defined abilities** are permitted but restricted to first-order type parameters. This allows library authors to define domain-specific abilities without the complexity of higher-kinded polymorphism.

4. **`ability` declarations** look like `effect` declarations (using `op` for operations), keeping the language syntactically consistent.

5. **Constraint syntax** uses `forall<T where Ability<T>>`, consistent with the placeholder noted in Chapter 2, Section 2.7.1.

This design draws on Roc's abilities (deliberately no HKTs, auto-derivable) and Gleam's validation that useful languages need not have typeclasses.

### 9.8.1 Built-in Abilities

Four abilities are built into the language. Each is auto-satisfied for primitive types and (where noted) for ADTs composed of satisfying types.

**Eq\<T\>** — Equality comparison.

```
ability Eq<T> {
  op eq(T, T -> Bool);
}
```

Operation: `eq(@T, @T -> @Bool)`. Returns `true` if the two values are structurally equal.

Satisfied by: Int, Nat, Bool, Float64, String, Byte, Unit, and ADTs whose constructors contain only Eq-satisfying field types (auto-derivation). Simple enums (all-nullary constructors) always satisfy Eq.

**Ord\<T\>** — Ordering comparison.

```
ability Ord<T> {
  op compare(T, T -> Ordering);
}
```

Operation: `compare(@T, @T -> @Ordering)`. Returns `Less`, `Equal`, or `Greater`.

The `Ordering` ADT is a built-in type:

```
public data Ordering {
  Less,
  Equal,
  Greater
}
```

Satisfied by: Int, Nat, Bool, Float64, String, Byte.

**Hash\<T\>** — Hashing.

```
ability Hash<T> {
  op hash(T -> Int);
}
```

Operation: `hash(@T -> @Int)`. Returns a deterministic integer hash of the value.

Satisfied by: Int, Nat, Bool, Float64, String, Byte, Unit.

**Show\<T\>** — String representation.

```
ability Show<T> {
  op show(T -> String);
}
```

Operation: `show(@T -> @String)`. Returns a human-readable string representation.

Satisfied by: Int, Nat, Bool, Float64, String, Byte, Unit.

### 9.8.2 ADT Auto-Derivation

For `Eq`, ADTs are automatically derivable when all constructor fields are Eq-satisfying types. The compiler generates structural equality: compare tags first, then compare fields pairwise.

Simple enums (ADTs with only nullary constructors) always satisfy `Eq` — equality reduces to tag comparison.

ADTs with `String` or `Array` fields do not currently auto-derive `Eq` (these use pair representation in WASM and require special comparison logic beyond field-level comparison).

### 9.8.3 Compilation Strategy

Ability operations are compiled via two mechanisms:

1. **AST-level rewriting** (Pass 1.6): `eq(a, b)` is rewritten to `a == b`, and `compare(a, b)` is rewritten to `if a < b then Less else if a == b then Equal else Greater`. This reuses existing comparison codegen.

2. **WASM-level dispatch**: `show(x)` and `hash(x)` are dispatched at WASM generation time based on the inferred type of the argument, routing to type-specific implementations (e.g., `to_string` for Int, FNV-1a for String hashing).

## 9.9 Limitations

The current standard library has the following limitations, each tracked as a GitHub issue:

| Limitation | Issue | Notes |
|-----------|-------|-------|
| Combinator type inference with bare constructors | [#293](https://github.com/aallan/vera/issues/293) | `option_map(None, f)` cannot infer `None`'s type variable; use a typed binding instead |
