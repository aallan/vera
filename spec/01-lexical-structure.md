# Chapter 1: Lexical Structure

## 1.1 Source Encoding

Vera source files MUST be encoded in UTF-8. The file extension is `.vera`.

Source text is a sequence of Unicode code points. The lexer processes these into a sequence of tokens.

## 1.2 Whitespace and Line Structure

Whitespace (spaces, tabs, newlines) separates tokens but is not significant to the grammar, with one exception: at least one whitespace character is required between adjacent identifier-like tokens.

Vera does not use significant indentation. All block structure is delimited by braces `{}`.

There is one canonical formatting for each construct (see Section 1.8). A conforming formatter MUST produce this exact formatting.

## 1.3 Comments

Vera supports three comment forms:

```
-- This is a line comment (extends to end of line)

{- This is a block comment.
   Block comments {- can be nested -}.
-}

/* This is an annotation comment */
```

**Line comments** begin with `--` and extend to the end of the line.

**Block comments** begin with `{-` and end with `-}`. They nest: a `{-` inside a block comment begins a nested block comment that must be closed by its own `-}`.

**Annotation comments** begin with `/*` and end with `*/`. They do not nest. Annotation comments are semantically ignored by the compiler but are preserved in the CST. They serve as optional human-readable labels for bindings:

```
fn(@Int /* width */, @Int /* height */ -> @Int)
```

## 1.4 Keywords

The following identifiers are reserved keywords and MUST NOT be used as type names or function names:

```
fn          let         if          then        else
match       data        type        module      import
public      private     requires    ensures     invariant
decreases   assert      assume      effect      handle
resume      with        in          forall      where
true        false       pure
```

## 1.5 Operators and Punctuation

### Arithmetic Operators

| Symbol | Meaning | Precedence | Associativity |
|--------|---------|------------|---------------|
| `*`    | Multiplication | 7 | Left |
| `/`    | Integer division | 7 | Left |
| `%`    | Modulo | 7 | Left |
| `+`    | Addition | 6 | Left |
| `-`    | Subtraction | 6 | Left |

### Comparison Operators

| Symbol | Meaning | Precedence | Associativity |
|--------|---------|------------|---------------|
| `==`   | Equal | 4 | None |
| `!=`   | Not equal | 4 | None |
| `<`    | Less than | 5 | None |
| `>`    | Greater than | 5 | None |
| `<=`   | Less or equal | 5 | None |
| `>=`   | Greater or equal | 5 | None |

Comparison operators are non-associative: `a == b == c` is a syntax error. Chain comparisons explicitly with `&&`.

### Logical Operators

| Symbol | Meaning | Precedence | Associativity |
|--------|---------|------------|---------------|
| `!`    | Logical NOT (prefix) | 9 | — |
| `&&`   | Logical AND | 3 | Left |
| `\|\|`   | Logical OR | 2 | Left |

### Other Operators

| Symbol | Meaning | Precedence | Associativity |
|--------|---------|------------|---------------|
| `-`    | Unary negation (prefix) | 9 | — |
| `\|>`   | Pipe (function application) | 1 | Left |

The pipe operator `|>` passes the left operand as the first argument to the right operand:

```
@Int.0 |> abs |> add(@Int.1)
```

is equivalent to:

```
add(abs(@Int.0), @Int.1)
```

### Punctuation

| Symbol | Usage |
|--------|-------|
| `(` `)` | Grouping, function parameters, function application |
| `{` `}` | Blocks, record literals, refinement types |
| `[` `]` | Array literals, array indexing |
| `<` `>` | Type parameters (in type position only) |
| `@`     | Slot reference prefix |
| `.`     | Slot index separator, field access |
| `,`     | Separator in lists |
| `;`     | Statement terminator |
| `:`     | Type annotation separator |
| `->`    | Function return type, match arm body |
| `=`     | Binding, assignment in handlers |
| `\|`     | Refinement type predicate separator, match alternatives |
| `_`     | Wildcard pattern |

## 1.6 Literals

### Integer Literals

Integer literals are sequences of decimal digits, optionally preceded by a `-` sign:

```
0
42
-17
1000000
```

No underscores, no hex/octal/binary prefixes. One canonical form: no leading zeros (except for the literal `0`).

### Float Literals

Float literals contain a decimal point with digits on both sides:

```
3.14
-0.5
100.0
```

One canonical form: no trailing zeros after the last significant digit, except that at least one digit must follow the decimal point. `1.0` is valid; `1.` is not.

Scientific notation is not supported.

### String Literals

String literals are enclosed in double quotes:

```
"hello world"
"line one\nline two"
""
```

Escape sequences:

| Sequence | Meaning |
|----------|---------|
| `\\`     | Backslash |
| `\"`     | Double quote |
| `\n`     | Newline |
| `\t`     | Tab |
| `\r`     | Carriage return |
| `\0`     | Null |
| `\u{XXXX}` | Unicode code point (1-6 hex digits) |

No other escape sequences are valid.

**Design note.** Vera does not support raw string syntax or multi-line string literals. A raw string (`r"..."`) would be an alternative representation for any string containing backslash characters, and a multi-line literal would be an alternative representation for any string containing newline characters. Both would violate the one-canonical-form principle (§0.2.3): the same string value would be expressible in two syntactically distinct ways. Since Vera targets LLM emission rather than human authoring (§0.3.1), the readability benefit of alternative string syntaxes does not justify the representational ambiguity. The escape sequence table above is the canonical and only mechanism for embedding special characters in strings.

### Boolean Literals

```
true
false
```

### Unit Literal

```
()
```

## 1.7 Identifiers

Identifiers are used for:
- Type names (including built-in types)
- Function names
- Effect names
- Module names

Identifiers begin with a letter (uppercase or lowercase ASCII) and may contain letters, digits, and underscores:

```
identifier = [A-Za-z][A-Za-z0-9_]*
```

Convention (enforced by the compiler):
- **Type names** MUST begin with an uppercase letter: `Int`, `MyList`, `Option`
- **Function names** MUST begin with a lowercase letter: `add`, `map_array`, `to_string`
- **Effect names** MUST begin with an uppercase letter: `IO`, `State`, `Exn`
- **Module names** MUST begin with a lowercase letter: `vera.core`, `my_module`

This distinction is load-bearing: it allows the parser to unambiguously distinguish types from functions in all contexts.

## 1.8 Canonical Formatting

Every Vera construct has exactly one canonical textual representation. A conforming formatter MUST produce output identical to the canonical form. Two semantically equivalent programs that differ textually are not valid Vera — one of them is incorrectly formatted.

Rules:

1. **Indentation**: 2 spaces per level. No tabs.
2. **Braces**: opening brace on the same line, closing brace on its own line aligned with the construct:
   ```
   fn(@Int -> @Int)
     requires(@Int.0 > 0)
     ensures(@Int.result > 0)
     effects(pure)
   {
     @Int.0
   }
   ```
3. **Commas**: followed by a single space: `@Int.0, @Int.1`
4. **Operators**: surrounded by single spaces: `@Int.0 + @Int.1`
5. **Semicolons**: no space before, newline after (in block context)
6. **Parentheses**: no space inside: `add(@Int.0, @Int.1)` not `add( @Int.0, @Int.1 )`
7. **Contract clauses**: each on its own line, indented 2 spaces from the function declaration
8. **One statement per line** in block context
9. **No trailing whitespace** on any line
10. **File ends with a single newline**

## 1.9 Token Precedence

When the lexer encounters ambiguity, it applies these rules in order:

1. **Longest match**: the lexer consumes the longest possible token.
2. **Keyword priority**: if a longest match is both a keyword and a valid identifier, it is lexed as a keyword.
3. **Operator priority**: multi-character operators (`->`, `==`, `>=`, `|>`, `&&`, `||`) are preferred over sequences of single-character operators.
