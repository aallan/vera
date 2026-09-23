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

**Annotation comments** begin with `/*` and end with `*/`. They do not nest. They are semantically ignored by the compiler: no annotation comment changes how a program type-checks, verifies, or runs.

They serve as optional human-readable labels for bindings, recovering the readability that structural slot references leave implicit — `@Int.0` records where a value comes from, never what it means:

<!-- vera:run fn="area" args="3 3" stdout="9" -->
```
public fn area(@Int /* width */, @Int /* height */ -> @Int /* area */)
  requires(@Int.1 > 0)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{
  @Int.1 * @Int.0
}
```

A label written on a **function parameter** or on the **return slot** is preserved in the AST, attached to that slot's position rather than to a source line, and re-emitted by `vera fmt`. An annotation comment in any other position is an ordinary comment: still accepted and still ignored, but not carried in the AST.

## 1.4 Keywords

The following identifiers are reserved keywords and MUST NOT be used as function names:

```
fn          let         if          then        else
match       data        type        module      import
public      private     requires    ensures     invariant
decreases   assert      assume      effect      handle
resume      with        in          forall      exists
where       true        false       pure        ability
effects     op          old         new         result
```

The reservation is enforced by **E153** at the declaration, and the compiler derives the list above from the grammar itself rather than from a second hand-maintained copy, so a keyword cannot be reserved in this chapter and admitted by the checker. `resume` is the one entry that is not a grammar keyword; it is reserved on separate grounds, given in Chapter 5, Section 5.2.

The restriction is on function names alone. Type names cannot collide with a keyword in the first place: every type-namespace binder in the grammar — data types, type aliases, constructors, effects, abilities, and `forall` type parameters — is an `UPPER_IDENT`, and every keyword is lowercase, so `data with` is refused as a malformed type name rather than as a reserved one.

The restriction is also on the whole identifier, not on a prefix: `older`, `renew`, `matched`, `with_it` and `then_value` are ordinary function names.

`handle` is the one exception. `public fn handle(@Request -> @Response)` is the entry point a *host* invokes under `vera serve` and `wasi:http` (Chapter 9, Section 9.5.6), so a function of that name is not dead code and stays legal. A future host-invoked entry point is exempted on the same grounds; nothing else is. Chapter 5, Section 5.2 gives the full reasoning and the **E153** rule.

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
| `\(`...`)` | String interpolation (see §4.6) |

No other escape sequences are valid (except `\(` which begins interpolation).

#### String Interpolation

String interpolation embeds expressions inside string literals using `\(expr)` syntax:

```
"hello \(@String.0)"
"x = \(@Int.0)"
"a=\(@Int.1), b=\(@Int.0)"
```

The `\(` sequence opens an interpolation hole. The expression inside is parsed and type-checked normally. The matching `)` closes the hole (parentheses nest correctly). Non-String expressions of type Int, Nat, Bool, Byte, or Float64 are automatically converted to String using the appropriate `*_to_string` built-in. Other types produce a type error (E148).

An `InterpolatedString` is a first-class expression that returns String. It is the canonical form for strings with embedded expressions — there is no equivalent `string_concat`/`to_string` desugaring at the source level.

**Limitation.** Expressions inside `\(...)` cannot contain string literals, because the lexer's regex-based string matching would terminate at the inner `"`. Use `let` bindings for expressions requiring string arguments.

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
   This holds in **value position** as well as statement position. A `match`, `if` or `handle` bound by a `let`, or used as a block's result, is written exactly as one used as a statement — the text introducing it (`let @Int = `) shares the opening line, and the trailing `;` rides the closing brace:
   ```
   let @Int = if @Bool.0 then {
     1
   } else {
     2
   };
   ```
   The rule holds wherever a construct occupies a statement, a block's result, a `match` arm body, or a binding's value. A construct appearing *within* a one-line expression — an operand, a call or constructor argument, an array element — is rendered on a single line for now; unifying that remaining position is tracked as [#1139](https://github.com/aallan/vera/issues/1139). Within its stated scope the rule admits no position-dependence: a form that depended on position would give one construct two textual representations — the "equivalent alternatives" §0.2.3 excludes and the single canonical formatting §1.2 requires — and would oblige a generator to decide which one to emit at every site instead of applying one rule everywhere (§0.3.1). The expanded form is more verbose than a flattened one; that is not an argument against it, since §0.2.2 ranks explicitness above convenience and §0.3.1 makes human readability a non-goal.
3. **Commas**: followed by a single space: `@Int.0, @Int.1`
4. **Operators**: surrounded by single spaces: `@Int.0 + @Int.1`
5. **Semicolons**: no space before, newline after (in block context)
6. **Parentheses**: no space inside: `add(@Int.0, @Int.1)` not `add( @Int.0, @Int.1 )`
7. **Contract clauses**: each on its own line, indented 2 spaces from the function declaration
8. **One statement per line** in block context
9. **No trailing whitespace** on any line
10. **File ends with a single newline**, and every line ends with a bare `\n` — a canonical Vera source file contains no carriage returns
11. **Comments are preserved.** A formatter MUST NOT discard a comment. One occupying a line of its own stays on its own line, above the construct it precedes — a statement, a declaration, a contract or `effects` clause, a `where` block, a function inside it, a `match` arm, a handler clause, a constructor or operation inside a `data`, `effect` or `ability` declaration, or a multi-line `if`, `match` or `handle` used as a binding's value or an arm's body.  Attachment is to the construct that *follows* the comment, not merely to the innermost one whose span contains it; a comment between a signature and its first `requires` belongs to that clause, not to the function body.  One with code before it on the same line is claimed by the first construct emitted whose source-line range covers it, cut off at the next construct's start, and emitted after that construct separated by two spaces — so a comment trailing a statement stays with that statement. Where reformatting leaves no such position, the comment moves to the end of the enclosing declaration rather than being dropped. At most one line comment may share a physical line, and it must come last, since `--` runs to end of line and would otherwise absorb whatever followed. Annotation-comment labels on a parameter or return slot are emitted from their binding instead (Section 1.3).
12. **String escapes are normalised.** A character that cannot be read reliably in source is emitted as a `\u{...}` escape: the Unicode general categories `Cc`, `Cf`, `Cs`, `Co`, `Cn`, `Zl` and `Zp`, and any `Zs` other than the plain ASCII space; the named escapes `\\`, `\"`, `\n`, `\t`, `\r` and `\0` take precedence over `\u{...}` for their own code points.  Every other character — including printable non-ASCII such as `café` or an emoji — is emitted literally, so `\u{1F600}` and the glyph it denotes have one canonical form.  This keeps a zero-width space, a bidirectional override or a lone surrogate from sitting invisibly in a program: source that reads the same must be the same.
13. **Blank lines are preserved, at most one.** A blank line separating two statements, separating a block's trailing result expression from the statement above it, separating two contract clauses or the `effects` row from the clause above it, separating two handler clauses, separating two `match` arms, or separating an own-line comment from what it documents, is reproduced as exactly one blank line, however many the source had.  A gap the source did not have is never introduced, and a gap held against an opening or closing brace separates nothing and is dropped — rule 2 already gives the brace its own line.  Consecutive top-level declarations are separated by exactly one blank line unconditionally, as a separator rather than a preserved gap.  The AST records no separation, so the paragraph breaks an author writes inside a block are recoverable only from the source text: discarding them and inventing them are equally wrong, and only the source distinguishes the two.

## 1.9 Token Precedence

`{-` always opens a block comment, so a `{` immediately followed by `-` is never a block containing a negated value. Write `{ -1 }` with a separating space for that.

When the lexer encounters ambiguity, it applies these rules in order:

1. **Longest match**: the lexer consumes the longest possible token.
2. **Keyword priority**: if a longest match is both a keyword and a valid identifier, it is lexed as a keyword.
3. **Operator priority**: multi-character operators (`->`, `==`, `>=`, `|>`, `&&`, `||`) are preferred over sequences of single-character operators.
