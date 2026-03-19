# Chapter 4: Expressions and Statements

## 4.1 Overview

Vera is expression-oriented: nearly every construct produces a value. Blocks are expressions whose value is the last expression in the block. There are no void statements — even effectful operations return `Unit`.

The one exception is `let` bindings, which are statements (they introduce a binding but do not themselves have a value). Statements appear only within blocks.

## 4.2 Literals

Literal expressions produce values of the corresponding primitive type:

| Literal | Type | Examples |
|---------|------|----------|
| Integer | `Int` | `0`, `42`, `-17` |
| Floating-point | `Float64` | `3.14`, `-0.5`, `100.0` |
| String | `String` | `"hello"`, `""`, `"line\nbreak"` |
| Boolean | `Bool` | `true`, `false` |
| Unit | `Unit` | `()` |

Integer literals in a context expecting `Nat` are checked for non-negativity at compile time.

## 4.3 Slot References

Slot references (Chapter 3) are expressions:

```
@Int.0          -- type Int
@String.0       -- type String
@Array<Int>.0   -- type Array<Int>
@Option<String>.0  -- type Option<String>
```

The type of a slot reference `@T.n` is `T`.

## 4.4 Arithmetic Expressions

Arithmetic operators work on numeric types (`Int`, `Nat`, `Float64`):

```
@Int.0 + @Int.1        -- addition
@Int.0 - @Int.1        -- subtraction
@Int.0 * @Int.1        -- multiplication
@Int.0 / @Int.1        -- integer division (truncates toward zero)
@Int.0 % @Int.1        -- modulo (result has the sign of the dividend)
```

Division by zero is undefined behaviour in Vera. The compiler SHOULD verify that the divisor is non-zero via contracts or refinement types. If it cannot, it MUST insert a runtime check.

Unary negation:

```
-@Int.0                -- negation
```

**No implicit conversions.** `Int` and `Float64` cannot be mixed in arithmetic. Use explicit conversion functions:

```
to_float(@Int.0) + @Float64.0
```

**No operator overloading.** Arithmetic operators work only on built-in numeric types.

## 4.5 Comparison Expressions

Comparison operators produce `Bool`:

```
@Int.0 == @Int.1       -- equality
@Int.0 != @Int.1       -- inequality
@Int.0 < @Int.1        -- less than
@Int.0 > @Int.1        -- greater than
@Int.0 <= @Int.1       -- less or equal
@Int.0 >= @Int.1       -- greater or equal
```

Equality (`==`, `!=`) is defined on all types. It is structural equality:
- Primitives: value equality
- Tuples: element-wise equality
- Arrays: element-wise equality (same length and all elements equal)
- ADTs: same constructor and recursively equal fields
- Strings: character-by-character equality
- Functions: not comparable (compile error)

Ordering (`<`, `>`, `<=`, `>=`) is defined only on `Int`, `Nat`, `Float64`, `Byte`, and `String` (lexicographic).

## 4.6 Logical Expressions

Logical operators work on `Bool`:

```
!@Bool.0               -- NOT
@Bool.0 && @Bool.1     -- AND (short-circuiting)
@Bool.0 || @Bool.1     -- OR (short-circuiting)
```

`&&` and `||` are short-circuiting: the right operand is not evaluated if the left operand determines the result.

## 4.7 Let Bindings

A let binding introduces a new slot reference:

```
let @Int = 42;
let @String = "hello";
let @Bool = @Int.0 > 0;
```

The type on the left is mandatory — there is no type inference for let bindings. This ensures that the slot reference type is always explicit and locally determinable.

Let bindings are immutable. There is no reassignment. To "update" a value, bind a new slot:

```
let @Int = 10;
let @Int = @Int.0 + 1;   -- @Int.0 is now 11, @Int.1 is 10
```

### 4.7.1 Tuple Destructuring

Let bindings can destructure tuples:

```
let Tuple<@Int, @String> = some_function();
```

This introduces two bindings: one `Int` and one `String`.

### 4.7.2 Let with Type Alias

```
type PosInt = { @Int | @Int.0 > 0 };
let @PosInt = 42;
```

The compiler verifies that `42` satisfies the refinement `@Int.0 > 0`.

## 4.8 Conditional Expressions

Conditional expressions use `if`/`then`/`else` and MUST always include both branches:

```
if @Bool.0 then {
  @Int.0
} else {
  @Int.1
}
```

Both branches MUST have the same type. The type of the `if` expression is that common type.

The condition MUST have type `Bool`. There are no truthy/falsy conversions.

The braces around branch bodies are mandatory, even for single expressions. This is the one canonical form:

```
-- VALID:
if @Bool.0 then {
  1
} else {
  0
}

-- INVALID (no braces):
if @Bool.0 then 1 else 0
```

## 4.9 Match Expressions

Match expressions perform exhaustive pattern matching on algebraic data types:

```
match @Option<Int>.0 {
  Some(@Int) -> @Int.0 + 1,
  None -> 0,
}
```

### 4.9.1 Patterns

| Pattern | Matches | Bindings introduced |
|---------|---------|---------------------|
| `ConstructorName(@T1, @T2, ...)` | ADT variant with fields | One per field |
| `ConstructorName` | ADT variant with no fields | None |
| `_` | Anything (wildcard) | None |
| Literal (`42`, `"hi"`, `true`) | Exact value | None |

Patterns are matched top-to-bottom. The first matching arm is taken.

### 4.9.2 Exhaustiveness

The compiler MUST verify that the match is exhaustive: every possible value of the scrutinee type is covered by at least one arm. If the match is not exhaustive, the program is rejected.

Wildcard `_` matches everything and makes any match exhaustive if it is the last arm.

### 4.9.3 Redundancy

The compiler SHOULD warn (but not reject) if a match arm is unreachable because previous arms already cover all its cases.

### 4.9.4 Nested Patterns

Patterns can be nested:

```
match @List<Option<Int>>.0 {
  Cons(Some(@Int), @List<Option<Int>>) -> @Int.0,
  Cons(None, @List<Option<Int>>) -> 0,
  Nil -> -1,
}
```

Each level of nesting introduces bindings from the inner patterns.

## 4.10 Block Expressions

A block is a sequence of statements followed by a final expression, enclosed in braces:

```
{
  let @Int = compute_x();
  let @Int = compute_y();
  @Int.0 + @Int.1
}
```

The value of a block is the value of its final expression. The type of a block is the type of its final expression.

All let bindings in a block are scoped to the block — they are not visible outside.

An empty block is not valid. A block must contain at least one expression.

## 4.11 Function Application

Functions are applied by name with parenthesised arguments:

```
add(@Int.0, @Int.1)
string_length(@String.0)
factorial(@Nat.0)
```

Arguments are evaluated left-to-right before the function is called (strict evaluation).

### 4.11.1 Constructor Application

ADT constructors are applied like functions:

```
Some(42)
Cons(1, Nil)
Tuple(1, "hello", true)
```

### 4.11.2 Pipe Operator

The pipe operator `|>` passes the left operand as the first argument to the function on the right:

```
@Int.0 |> abs |> add(@Int.1)
```

is equivalent to:

```
add(abs(@Int.0), @Int.1)
```

Pipes are left-associative: `a |> f |> g` means `g(f(a))`.

## 4.12 Array Expressions

### 4.12.1 Array Literals

```
[1, 2, 3, 4, 5]
["hello", "world"]
[]
```

All elements must have the same type. The type of the literal is `Array<T>` where `T` is the element type. Empty array literals require a type annotation in context (the expected type must be known).

### 4.12.2 Array Indexing

```
@Array<Int>.0[3]
```

Indexing uses square brackets with an `Int` or `Nat` index. Array indexing is bounds-checked:
- Statically: if the index is a literal or can be proven in-bounds by the contract system
- At runtime: otherwise (generates a trap on out-of-bounds)

### 4.12.3 Array Operations

The built-in `array_length` function returns the number of elements in an array (see Chapter 9, Section 9.6.1):

```
array_length(@Array<Int>.0)                -- returns Int (>= 0)
```

The built-in `array_append` function returns a new array with an element appended (see Chapter 9, Section 9.6.2):

```
array_append(@Array<Int>.0, @Int.0)    -- returns Array<Int>
```

The built-in `array_range` function produces an array of integers over a half-open interval (see Chapter 9, Section 9.6.3):

```
array_range(@Int.0, @Int.1)            -- returns Array<Int> ([start, end))
```

The built-in `array_concat` function merges two arrays (see Chapter 9, Section 9.6.4):

```
array_concat(@Array<Int>.0, @Array<Int>.1)  -- returns Array<Int>
```

Higher-order array operations (`array_map`, `array_filter`, `array_fold`, `array_slice`) are built-in functions documented in Chapter 9, Sections 9.6.5–9.6.8.

## 4.13 String Operations

String operations are provided as built-in functions:

```
string_length(@String.0)                -- returns Nat
string_concat(@String.0, @String.1)     -- returns String
string_slice(@String.0, @Nat.0, @Nat.1) -- returns String
char_code(@String.0, @Int.0)            -- returns Nat (ASCII code at index)
parse_nat(@String.0)                    -- returns Result<Nat, String>
parse_int(@String.0)                    -- returns Result<Int, String>
parse_float64(@String.0)                -- returns Result<Float64, String>
parse_bool(@String.0)                   -- returns Result<Bool, String>
                                        -- strict: only "true" and "false" are valid
base64_encode(@String.0)                -- returns String (RFC 4648)
base64_decode(@String.0)                -- returns Result<String, String>
url_encode(@String.0)                   -- returns String (RFC 3986 percent-encoding)
url_decode(@String.0)                   -- returns Result<String, String>
url_parse(@String.0)                    -- returns Result<UrlParts, String>
url_join(@UrlParts.0)                   -- returns String
async(@T.0)                            -- returns Future<T> (effects(<Async>))
await(@Future<T>.0)                    -- returns T (effects(<Async>))
to_string(@Int.0)                       -- returns String
int_to_string(@Int.0)                   -- returns String (alias for to_string)
bool_to_string(@Bool.0)                 -- returns String ("true" or "false")
nat_to_string(@Nat.0)                   -- returns String
byte_to_string(@Byte.0)                 -- returns String (single character)
float_to_string(@Float64.0)             -- returns String
strip(@String.0)                        -- returns String (trim whitespace)
```

String concatenation uses a function, not an operator. There is no `+` on strings.

String memory is allocated via the bump allocator and is not freed. Garbage collection for WASM linear memory is tracked in [#51](https://github.com/aallan/vera/issues/51). See Chapter 11, Section 11.5 for the string pool implementation.

### 4.13.1 String Interpolation

String interpolation provides ergonomic syntax for building strings from mixed types. The syntax uses `\(expr)` inside double-quoted strings:

```
"hello \(@String.0)"               -- embeds a String value
"x = \(@Int.0)"                    -- auto-converts Int to String
"a=\(@Int.1), b=\(@Int.0)"        -- multiple interpolations
"\(@String.0)"                     -- interpolation-only (no literal text)
"len=\(string_length(@String.0))"  -- function call inside interpolation
```

**Type rules.** An interpolated string is an expression of type String. Each interpolated expression is type-checked independently:

- If the expression has type String, it is used directly.
- If the expression has type Int, Nat, Bool, Byte, or Float64, it is automatically converted using the appropriate built-in (`to_string`, `nat_to_string`, `bool_to_string`, `byte_to_string`, `float_to_string`).
- All other types produce error E148.

**Canonical form.** `InterpolatedString` is a first-class AST node and the canonical representation for strings with embedded expressions. The formatter preserves interpolation syntax — it does not desugar to `string_concat`/`to_string` chains.

**Compilation.** At the WASM level, interpolation desugars to a chain of `string_concat` and `*_to_string` calls. For example, `"a=\(@Int.0), b=\(@Bool.0)"` becomes `string_concat(string_concat(string_concat("a=", to_string(@Int.0)), ", b="), bool_to_string(@Bool.0))`.

**Limitation.** Expressions inside `\(...)` cannot contain string literals (nested `"` terminates the outer string in the regex lexer). Use `let` bindings for expressions that require string arguments:

```
let @String = string_concat("a", "b");
"result: \(@String.0)"
```

## 4.14 Expression Precedence (Complete)

From highest to lowest precedence:

| Level | Operators | Associativity |
|-------|-----------|---------------|
| 10 | Function application `f(...)`, array index `a[i]` | Left |
| 9 | Unary `-`, `!` | Prefix |
| 7 | `*`, `/`, `%` | Left |
| 6 | `+`, `-` | Left |
| 5 | `<`, `>`, `<=`, `>=` | None |
| 4 | `==`, `!=` | None |
| 3 | `&&` | Left |
| 2 | `||` | Left |
| 1 | `|>` | Left |

Parentheses can override precedence: `(@Int.0 + @Int.1) * @Int.2`.

## 4.15 No Loops

Vera has no loop constructs (`for`, `while`, `loop`). All iteration is expressed as recursion. Recursive functions must declare a `decreases` clause for termination checking (see Chapter 6).

This is deliberate: loops require reasoning about mutable state across iterations, which is a known weakness of LLMs. Recursion with explicit base cases and structural decomposition is a more pattern-matchable structure.

## 4.16 No Mutation

There are no assignment statements. All `let` bindings are immutable. State changes are handled through the effect system (Chapter 7).

The only way to "modify" data is to construct a new value. This is the standard functional programming approach, and Vera's garbage collector handles the allocation overhead.
