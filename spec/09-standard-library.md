# Chapter 9: Standard Library

## 9.1 Overview

Vera's standard library provides built-in types, effects, and functions that are available in every Vera program without explicit import. The library is deliberately small — it includes only the types and operations that are universally needed and cannot be expressed purely in user code.

The standard library comprises:

- **Built-in ADTs**: `Option<T>` and `Result<T, E>` for representing partiality and fallibility.
- **Built-in collections**: `Array<T>` for fixed-size homogeneous sequences, plus future collections (`Set<T>`, `Map<K, V>`).
- **Built-in effects**: `IO` for output, `State<T>` for mutable state, plus future effects for networking, concurrency, and LLM inference.
- **Built-in functions**: `length` for arrays, numeric operations (`abs`, `min`, `max`, `floor`, `ceil`, `round`, `sqrt`, `pow`), type conversions (`to_float`, `float_to_int`, `nat_to_int`, `int_to_nat`, `byte_to_int`, `int_to_byte`), Float64 predicates (`is_nan`, `is_infinite`, `nan`, `infinity`), string search (`string_contains`, `starts_with`, `ends_with`, `index_of`), string transformation (`to_upper`, `to_lower`, `replace`, `split`, `join`), plus future functions for vector similarity.
- **Future types**: `Json` for structured data interchange, `Markdown` for agent-oriented document structure, `Decimal` for exact arithmetic.
- **Future abilities**: Type constraints for generic programming (post-v0.1).

All built-in types participate fully in the type system: they can appear in contracts, be verified by the SMT solver, and be used with refinement types and pattern matching. Built-in effects follow the same algebraic effect semantics as user-defined effects (see Chapter 7).

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
  if length(@Array<Int>.0) > 0 then {
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

**Length:** The `length` built-in function returns the number of elements (see Section 9.6.1).

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

### 9.5.4 Async (Future)

> **Status: Not yet implemented.** Tracked in [#59](https://github.com/aallan/vera/issues/59).

Asynchronous operations will be modelled as an algebraic effect. An `<Async>` effect with `async` and `await` operations will allow concurrent computation:

```
private fn fetch_both(@String, @String -> @Tuple<Json, Json>)
  requires(true)
  ensures(true)
  effects(<Http, Async>)
{
  let @Future<Json> = async(http_get(@String.0));
  let @Future<Json> = async(http_get(@String.1));
  let @Json = await(@Future<Json>.1);
  let @Json = await(@Future<Json>.0);
  Tuple(@Json.1, @Json.0)
}
```

Key design points:
- `async(expr)` wraps an effectful computation in a `Future<T>`, starting it concurrently.
- `await(@Future<T>.n)` suspends until the future resolves, yielding the result.
- The `<Async>` effect must be declared, making concurrency explicit and trackable.
- Handlers can provide different scheduling strategies (thread pool, event loop, sequential).
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

### 9.6.1 length

```
public forall<T> fn length(@Array<T> -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
```

Returns the number of elements in an array. The result is always non-negative. `length` is generic over the element type.

```
let @Array<Int> = [10, 20, 30];
length(@Array<Int>.0)
```

This expression evaluates to `3`.

For the compilation of `length`, see Chapter 11, Section 11.12.

### 9.6.2 array_push

```
public forall<T> fn array_push(@Array<T>, @T -> @Array<T>)
  requires(true)
  ensures(true)
  effects(pure)
```

Returns a new array with the element appended at the end. The returned array has length `length(input) + 1`, with the new element at the last index. The original array is unchanged (arrays are immutable values). `array_push` is generic over the element type.

```
let @Array<Int> = array_push([10, 20, 30], 40);
length(@Array<Int>.0)
```

This expression evaluates to `4`.

### 9.6.3 Numeric Operations

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

### 9.6.4 Type Conversions

Vera has no implicit numeric conversions. The following built-in functions provide explicit conversions between numeric types.

#### Widening conversions (always succeed)

```
public fn to_float(@Int -> @Float64)
  requires(true)
  ensures(true)
  effects(pure)
```

Converts an integer to a floating-point number. Compiled to `f64.convert_i64_s`.

```
to_float(42)
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

### 9.6.5 Float64 Predicates

Vera provides built-in functions for testing and constructing IEEE 754 special float values (NaN and infinity).

#### Predicates

```
public fn is_nan(@Float64 -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
```

Tests whether a Float64 value is NaN (not a number). NaN is the only value that is not equal to itself. Compiled to `f64.ne(x, x)`.

```vera
public fn test_is_nan(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ if is_nan(nan()) then { 1 } else { 0 } }
```

This expression evaluates to `1`.

```
public fn is_infinite(@Float64 -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
```

Tests whether a Float64 value is positive or negative infinity. Compiled to `f64.eq(f64.abs(x), inf)`. Returns `false` for NaN.

```vera
public fn test_is_infinite(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ if is_infinite(infinity()) then { 1 } else { 0 } }
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

```
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

### 9.6.6 String Search

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

#### starts_with

```vera
public fn starts_with(@String, @String -> @Bool)
  requires(true) ensures(true) effects(pure)
```

Returns `true` if the haystack begins with the given prefix. An empty prefix always matches. If the prefix is longer than the haystack, returns `false`.

```vera
starts_with("hello world", "hello")  -- true
starts_with("hello", "world")        -- false
starts_with("hello", "")             -- true
```

#### ends_with

```vera
public fn ends_with(@String, @String -> @Bool)
  requires(true) ensures(true) effects(pure)
```

Returns `true` if the haystack ends with the given suffix. An empty suffix always matches. If the suffix is longer than the haystack, returns `false`.

```vera
ends_with("hello world", "world")  -- true
ends_with("hello", "world")        -- false
ends_with("hello", "")             -- true
```

#### index_of

```vera
public fn index_of(@String, @String -> @Option<Nat>)
  requires(true) ensures(true) effects(pure)
```

Returns `Some(i)` where `i` is the byte offset of the first occurrence of the needle in the haystack, or `None` if not found. An empty needle matches at position 0. The returned index is a `Nat` (natural number).

```vera
match index_of("hello world", "world") {
  Some(@Nat) -> nat_to_int(@Nat.0),
  None -> 0 - 1
}
-- evaluates to 6
```

### 9.6.7 String Transformation

String transformation functions produce new strings by modifying characters or structure. All allocate heap memory for the result and register it with the GC shadow stack. All are pure and Tier 3.

#### to_upper

```vera
public fn to_upper(@String -> @String)
  requires(true) ensures(true) effects(pure)
```

Returns a new string with all ASCII lowercase letters (a–z, bytes 97–122) converted to uppercase (A–Z, bytes 65–90). Non-ASCII bytes and non-letter bytes are unchanged.

```vera
to_upper("hello")   -- "HELLO"
to_upper("Hello!")   -- "HELLO!"
to_upper("123")      -- "123"
```

#### to_lower

```vera
public fn to_lower(@String -> @String)
  requires(true) ensures(true) effects(pure)
```

Returns a new string with all ASCII uppercase letters (A–Z, bytes 65–90) converted to lowercase (a–z, bytes 97–122). Non-ASCII bytes and non-letter bytes are unchanged.

```vera
to_lower("HELLO")   -- "hello"
to_lower("Hello!")   -- "hello!"
to_lower("123")      -- "123"
```

#### replace

```vera
public fn replace(@String, @String, @String -> @String)
  requires(true) ensures(true) effects(pure)
```

Replaces all non-overlapping occurrences of the needle (second argument) in the haystack (first argument) with the replacement (third argument). If the needle is empty, returns a copy of the haystack. Uses a two-pass algorithm: pass 1 counts occurrences, then allocates the output buffer; pass 2 copies bytes with substitutions.

```vera
replace("hello world", "world", "vera")  -- "hello vera"
replace("aaa", "a", "bb")                -- "bbbbbb"
replace("hello", "xyz", "abc")           -- "hello"
replace("hello", "", "x")                -- "hello"
```

#### split

```vera
public fn split(@String, @String -> @Array<String>)
  requires(true) ensures(true) effects(pure)
```

Splits the string at each non-overlapping occurrence of the delimiter, returning an `Array<String>`. If the delimiter is empty, returns a single-element array containing the original string. Consecutive delimiters produce empty string segments. Uses a two-pass algorithm: pass 1 counts delimiters, then allocates the array and segment buffers in pass 2.

```vera
split("a,b,c", ",")     -- Array with 3 elements: "a", "b", "c"
split("hello", ",")     -- Array with 1 element: "hello"
split("a,,b", ",")      -- Array with 3 elements: "a", "", "b"
```

#### join

```vera
public fn join(@Array<String>, @String -> @String)
  requires(true) ensures(true) effects(pure)
```

Joins an array of strings with the given separator between each pair of elements. An empty array produces an empty string. Uses a two-pass algorithm: pass 1 sums the total length, pass 2 copies bytes.

```vera
join(split("a,b,c", ","), "-")  -- "a-b-c"
join(split("hello", ","), "-")  -- "hello"
```

### 9.6.8 similarity (Future)

> **Status: Not yet implemented.** Will be introduced alongside the `Inference` effect ([#61](https://github.com/aallan/vera/issues/61)).

```
public fn similarity(@Array<Float64>, @Array<Float64> -> @Float64)
  requires(length(@Array<Float64>.0) == length(@Array<Float64>.1))
  ensures(@Float64.result >= -1.0 && @Float64.result <= 1.0)
  effects(pure)
```

Computes the cosine similarity between two vectors (embeddings). The arrays must have equal length (enforced by precondition). The result is in the range \[-1, 1\], where 1 indicates identical direction, 0 indicates orthogonality, and -1 indicates opposite direction.

This function is pure — it performs no effects. It is intended for use with the `Inference.embed` operation to compare semantic similarity of text.

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

### 9.7.3 Markdown (Future)

> **Status: Not yet implemented.** Tracked in [#147](https://github.com/aallan/vera/issues/147). Dependencies resolved: dynamic string construction ([#52](https://github.com/aallan/vera/issues/52), done) and string built-in operations ([#134](https://github.com/aallan/vera/issues/134), done). Does **not** depend on `Map<K, V>`.

Markdown is the lingua franca of large language models — they understand it natively and generate it naturally. A typed Markdown ADT makes document structure visible to the type system, enabling contracts that verify the structural properties of agent output.

Markdown will be represented as two mutually defined ADTs: `MdBlock` for block-level elements and `MdInline` for inline-level content. The two-level design makes illegal states unrepresentable — a heading cannot contain another heading at the type level.

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

## 9.8 Abilities (Future)

> **Status: Not yet implemented.** Tracked in [#60](https://github.com/aallan/vera/issues/60). Post-v0.1 feature.

Vera's type variables are currently unconstrained (`forall<T>`). To support practical generic programming — sorting, hashing, serialisation — type variables will need constraints. Vera will adopt restricted abilities rather than full typeclasses:

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
  exists(@Nat, length(@Array<T>.0), fn(@Nat -> @Bool) effects(pure) {
    eq(@Array<T>.0[@Nat.0], @T.0)
  })
}
```

Key design points:

1. **No higher-kinded types.** No `Functor`, `Monad`, or `Applicative`. Abilities are first-order only: `Eq<T>`, not `Mappable<F>` where `F` is a type constructor. This preserves decidable type checking and prevents the abstraction hierarchy that makes code harder for LLMs to generate correctly.

2. **Built-in abilities** will be auto-derivable for ADTs composed of types that already support them: `Eq`, `Ord`, `Hash`, `Encode`, `Decode`, `Show`. If all fields of an ADT support `Eq`, the ADT supports `Eq` automatically.

3. **User-defined abilities** are permitted but restricted to first-order type parameters. This allows library authors to define domain-specific abilities without the complexity of higher-kinded polymorphism.

4. **`ability` declarations** look like `effect` declarations (using `op` for operations), keeping the language syntactically consistent.

5. **Constraint syntax** uses `forall<T where Ability<T>>`, consistent with the placeholder noted in Chapter 2, Section 2.7.1.

This design draws on Roc's abilities (deliberately no HKTs, auto-derivable) and Gleam's validation that useful languages need not have typeclasses.
