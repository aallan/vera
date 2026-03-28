# Examples

This document walks through Vera's key features with working code examples. Every example links to a runnable file in the `examples/` directory. For the complete language reference, see [SKILL.md](SKILL.md).

## Contracts the compiler proves

`requires(@Int.1 != 0)` means this function cannot be called with a zero divisor. The compiler checks every call site to prove the precondition holds. If it cannot prove it, the code does not compile. Division by zero is not a runtime error — it is a type error.

```vera
public fn safe_divide(@Int, @Int -> @Int)
  requires(@Int.1 != 0)
  ensures(@Int.result == @Int.0 / @Int.1)
  effects(pure)
{
  @Int.0 / @Int.1
}
```

> [`examples/safe_divide.vera`](examples/safe_divide.vera) — run with `vera run examples/safe_divide.vera --fn safe_divide -- 3 10`

## Refinement types — constraints at the type level

Types can carry predicates. `PosInt` is not just `Int` — it's an integer the compiler has proved is positive. `NonEmptyArray` is an array the compiler has proved is non-empty. Indexing into it is safe by construction.

```vera
type PosInt = { @Int | @Int.0 > 0 };
type Percentage = { @Int | @Int.0 >= 0 && @Int.0 <= 100 };
type NonEmptyArray = { @Array<Int> | array_length(@Array<Int>.0) > 0 };

public fn safe_divide(@Int, @PosInt -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0 / @PosInt.0
}

private fn head(@NonEmptyArray -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @NonEmptyArray.0[0]
}
```

> [`examples/refinement_types.vera`](examples/refinement_types.vera) — run with `vera run examples/refinement_types.vera --fn test_refine`

## Algebraic data types and pattern matching

User-defined types with recursive structure. `decreases(@List<Int>.0)` is a termination proof — the compiler verifies that the argument shrinks on every recursive call.

```vera
private data List<T> {
  Nil,
  Cons(T, List<T>)
}

public fn sum(@List<Int> -> @Int)
  requires(true)
  ensures(true)
  decreases(@List<Int>.0)
  effects(pure)
{
  match @List<Int>.0 {
    Nil -> 0,
    Cons(@Int, @List<Int>) -> @Int.0 + sum(@List<Int>.0)
  }
}
```

> [`examples/list_ops.vera`](examples/list_ops.vera) — run with `vera run examples/list_ops.vera --fn test_list`

## Effects — explicit state, no hidden mutation

Vera is pure by default. State changes must be declared as effects. `effects(<State<Int>>)` says this function reads and writes an integer. The `ensures` clause specifies exactly how the state changes. Handlers provide the actual state implementation — the function `run_counter` eliminates the effect entirely and is pure.

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

public fn run_counter(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Int>](@Int = 0) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) } with @Int = @Int.0
  } in {
    put(0);
    put(get(()) + 1);
    put(get(()) + 1);
    put(get(()) + 1);
    get(())
  }
}
```

> [`examples/effect_handler.vera`](examples/effect_handler.vera) — run with `vera run examples/effect_handler.vera --fn run_counter`

## Exceptions as effects

The `Exn<E>` effect models exceptions with a typed error value. Unlike most languages, exceptions are explicit in the type signature and must be handled by the caller. The handler catches the thrown value and returns a fallback — `safe_div` is pure because the effect has been discharged.

```vera
effect Exn<E> {
  op throw(E -> Never);
}

private fn checked_div(@Int, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(<Exn<Int>>)
{
  if @Int.1 == 0 then { throw(0 - 1) } else { @Int.0 / @Int.1 }
}

public fn safe_div(@Int, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[Exn<Int>] {
    throw(@Int) -> { @Int.0 }
  } in {
    checked_div(@Int.0, @Int.1)
  }
}
```

> [`examples/effect_handler.vera`](examples/effect_handler.vera) — run with `vera run examples/effect_handler.vera --fn safe_div -- 10 0`

## String interpolation and async

`IO.print` is an effect operation. The `\(@Int.0)` syntax interpolates values into strings, auto-converting primitive types. `effects(<IO, Async>)` declares both IO and async effects — the compiler rejects any call to this function from a context that doesn't permit both.

```vera
effect IO {
  op print(String -> Unit);
}

private fn roundtrip(@Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0)
  effects(<Async>)
{
  let @Future<Int> = async(@Int.0);
  await(@Future<Int>.0)
}

public fn main(@Unit -> @Unit)
  requires(true)
  ensures(true)
  effects(<IO, Async>)
{
  let @Int = roundtrip(42);
  IO.print("roundtrip(42) = \(@Int.0)");
  ()
}
```

> [`examples/async_futures.vera`](examples/async_futures.vera) — run with `vera run examples/async_futures.vera`

## Recursion as iteration

Vera has no `for` or `while` loops — iteration is always recursion. The `loop` function calls itself with `@Nat.0 + 1` until it reaches the bound. This is the standard Vera pattern for counted iteration.

Notice the separation of concerns: `fizzbuzz` is `effects(pure)` — the verifier can reason about it with SMT. `loop` has `effects(<IO>)` because it prints. `main` calls `loop` and also has `effects(<IO>)`. The effect annotations propagate up the call chain but never contaminate the pure classifier.

The contract `requires(@Nat.0 <= @Nat.1)` on `loop` ensures the function is only called with valid bounds — and since the recursive call passes `@Nat.0 + 1` where `@Nat.0 < @Nat.1`, the precondition is maintained at every step.

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

> [`examples/fizzbuzz.vera`](examples/fizzbuzz.vera) — run with `vera run examples/fizzbuzz.vera`

## Typed Markdown

Vera has a built-in Markdown document type. `md_parse` produces a typed `MdBlock` tree; `md_has_heading` and `md_extract_code_blocks` query its structure. This is designed for agent workflows where an LLM produces structured output and the contract system validates its shape.

```vera
public fn main(@Unit -> @Unit)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  let @Result<MdBlock, String> = md_parse("# Hello\n\n```vera\n42\n```");
  match @Result<MdBlock, String>.0 {
    Ok(@MdBlock) -> {
      if md_has_heading(@MdBlock.0, 1) then {
        IO.print("Has title")
      } else {
        IO.print("No title")
      };
      let @Array<String> = md_extract_code_blocks(@MdBlock.0, "vera");
      IO.print("Code blocks: \(array_length(@Array<String>.0))");
      ()
    },
    Err(@String) -> { IO.print(@String.0); () }
  };
  ()
}
```

> [`examples/markdown.vera`](examples/markdown.vera) — run with `vera run examples/markdown.vera`

## JSON — structured data interchange

Vera has a built-in `Json` ADT. `json_parse` parses a JSON string into a typed `Json` value; `json_get`, `json_array_get`, and `json_has_field` query its structure. Pattern matching on `JString`, `JNumber`, `JBool`, etc. extracts typed values with compiler-enforced exhaustiveness.

```vera
private fn get_name(@String -> @Result<String, String>)
  requires(true)
  ensures(true)
  effects(pure)
{
  match json_parse(@String.0) {
    Err(@String) -> Err(@String.0),
    Ok(@Json) -> match json_get(@Json.0, "name") {
      None -> Err("missing name"),
      Some(@Json) -> match @Json.0 {
        JString(@String) -> Ok(@String.0),
        _ -> Err("name is not a string")
      }
    }
  }
}
```

> [`examples/json.vera`](examples/json.vera) — run with `vera run examples/json.vera`

## HTTP — network I/O as an algebraic effect

`Http.get` and `Http.post` are effect operations returning `Result<String, String>`. The `<Http>` effect is declared in the signature, making network access explicit and testable. Compose with `json_parse` for typed API responses.

```vera
private fn fetch_title(@String -> @Result<String, String>)
  requires(string_length(@String.0) > 0)
  ensures(true)
  effects(<Http>)
{
  let @Result<String, String> = Http.get(@String.0);
  match @Result<String, String>.0 {
    Ok(@String) ->
      match json_parse(@String.0) {
        Ok(@Json) ->
          match json_get(@Json.0, "title") {
            Some(@Json) -> Ok(json_stringify(@Json.0)),
            None -> Err("missing title field")
          },
        Err(@String) -> Err(@String.0)
      },
    Err(@String) -> Err(@String.0)
  }
}
```

> [`examples/http.vera`](examples/http.vera) — run with `vera run examples/http.vera` (requires network)

## HTML — lenient parsing and CSS selector queries

`html_parse` produces a typed `HtmlNode` tree from any HTML string. The parser is lenient (like browsers) — malformed HTML produces a best-effort tree. Query elements with CSS selectors, extract text, and read attributes.

```vera
private fn count_links(@HtmlNode -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{
  array_length(html_query(@HtmlNode.0, "a"))
}
```

> [`examples/html.vera`](examples/html.vera) — run with `vera run examples/html.vera`

## LLM inference as an algebraic effect

`Inference.complete` sends a prompt to an LLM and returns the completion. The `<Inference>` effect is declared in the signature — a function typed `effects(pure)` provably cannot call an LLM. Provider auto-detected from environment variables.

```vera
private fn classify_sentiment(@String -> @Result<String, String>)
  requires(string_length(@String.0) > 0)
  ensures(true)
  effects(<Inference>)
{
  let @String = string_concat(
    "Classify the sentiment as Positive, Negative, or Neutral: ",
    @String.0);
  Inference.complete(@String.0)
}
```

> [`examples/inference.vera`](examples/inference.vera) — run with `VERA_ANTHROPIC_API_KEY=sk-ant-... vera run examples/inference.vera`
