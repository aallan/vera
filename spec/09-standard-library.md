# Chapter 9: Standard Library

## 9.1 Overview

Vera's standard library provides built-in types, effects, and functions that are available in every Vera program without explicit import. The library is deliberately small — it includes only the types and operations that are universally needed and cannot be expressed purely in user code.

The standard library comprises:

- **Built-in ADTs**: `Option<T>` and `Result<T, E>` for representing partiality and fallibility.
- **Built-in collections**: `Array<T>` for fixed-size homogeneous sequences, plus future collections (`Set<T>`, `Map<K, V>`).
- **Built-in effects**: `IO` for output, `State<T>` for mutable state, plus future effects for networking, concurrency, and LLM inference.
- **Built-in functions**: `length` for arrays, plus future functions for vector similarity.
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

### 9.6.3 similarity (Future)

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
