# Chapter 10: Formal Grammar

## 10.1 Notation

This chapter defines the complete grammar of Vera using Extended Backus-Naur Form (EBNF). The grammar is designed to be directly usable with the Lark parser generator in LALR(1) mode.

Conventions:
- `UPPER_CASE`: terminal tokens (lexer rules)
- `lower_case`: non-terminal rules (parser rules)
- `"keyword"`: literal keyword or punctuation
- `rule?`: optional (zero or one)
- `rule*`: zero or more
- `rule+`: one or more
- `rule ("," rule)*`: comma-separated list
- `|`: alternatives
- `(...)`: grouping

## 10.2 Lexical Grammar (Tokens)

```ebnf
// Whitespace and comments (skipped)
WS: /\s+/
LINE_COMMENT: /--[^\n]*/
// Block comments nest (Section 1.3), so they are not a regular language and
// have no regex form.  The reference implementation removes them in
// vera/lexical.py, by counting depth, before the parser sees the text.
// The character alternative excludes both delimiters, so a `{-` inside the
// body opens a nested comment and must be closed: `{- {- -}` is not a
// block comment, and the implementation reports it unterminated (E020).
BLOCK_COMMENT: "{-" (BLOCK_COMMENT | /(?!\{-|-\})[\s\S]/)* "-}"
ANNOTATION_COMMENT: /\/\*[^*]*\*+([^/*][^*]*\*+)*\//

// Keywords
FN: "fn"
LET: "let"
IF: "if"
THEN: "then"
ELSE: "else"
MATCH: "match"
DATA: "data"
TYPE: "type"
MODULE: "module"
IMPORT: "import"
PUBLIC: "public"
PRIVATE: "private"
REQUIRES: "requires"
ENSURES: "ensures"
INVARIANT: "invariant"
DECREASES: "decreases"
ASSERT: "assert"
ASSUME: "assume"
ABILITY: "ability"
EFFECT: "effect"
HANDLE: "handle"
WITH: "with"
IN: "in"
FORALL: "forall"
WHERE: "where"
TRUE: "true"
FALSE: "false"
PURE: "pure"
OP: "op"
OLD: "old"
NEW: "new"
EFFECTS: "effects"
EXISTS: "exists"
RESULT: "result"

// Operators
PLUS: "+"
MINUS: "-"
STAR: "*"
SLASH: "/"
PERCENT: "%"
EQ: "=="
NEQ: "!="
LT: "<"
GT: ">"
LE: "<="
GE: ">="
AND: "&&"
OR: "||"
NOT: "!"
IMPLIES: "==>"
ARROW: "->"
PIPE: "|>"
ASSIGN: "="
AT: "@"
DOT: "."

// Punctuation
LPAREN: "("
RPAREN: ")"
LBRACE: "{"
RBRACE: "}"
LBRACKET: "["
RBRACKET: "]"
COMMA: ","
SEMICOLON: ";"
DOUBLE_COLON: "::"
BAR: "|"
UNDERSCORE: "_"
HOLE: "?"

// Literals
INT_LIT: /0|[1-9][0-9]*/
FLOAT_LIT: /[0-9]+\.[0-9]+/
STRING_LIT: /"([^"\\]|\\.)*"/

// Identifiers
UPPER_IDENT: /[A-Z][A-Za-z0-9_]*/
LOWER_IDENT: /[a-z][A-Za-z0-9_]*/
```

## 10.3 Parser Grammar

### 10.3.1 Program Structure

```ebnf
program: module_decl? import_decl* top_level_decl*

module_decl: MODULE module_path SEMICOLON

module_path: LOWER_IDENT (DOT LOWER_IDENT)*

import_decl: IMPORT module_path import_list? SEMICOLON

import_list: LPAREN import_name (COMMA import_name)* RPAREN

import_name: LOWER_IDENT | UPPER_IDENT

top_level_decl: visibility? fn_decl
              | visibility? data_decl
              | type_alias_decl
              | effect_decl
              | ability_decl

visibility: PUBLIC | PRIVATE
```

> **Note:** The grammar marks `visibility` as optional (`?`) for parser flexibility, but the type checker enforces it as mandatory for `fn` and `data` declarations (see Section 5.8). Omitting the modifier is a compile error.

For the semantics of module declarations, imports, visibility modifiers, and name resolution, see Chapter 8.

### 10.3.2 Function Declarations

```ebnf
fn_decl: forall_clause? FN LOWER_IDENT fn_signature contract_block effect_clause fn_body where_block?

forall_clause: FORALL LT type_var_list GT
             | FORALL LT type_var_list WHERE ability_constraint_list GT

ability_constraint_list: ability_constraint (COMMA ability_constraint)*

ability_constraint: UPPER_IDENT LT UPPER_IDENT GT

type_var_list: UPPER_IDENT (COMMA UPPER_IDENT)*

fn_signature: LPAREN fn_params? ARROW AT type_expr RPAREN
// The AT prefix marks each type as a binding site, creating slot references (@T.0, @T.1, etc.)

fn_params: AT type_expr (COMMA AT type_expr)*
// fn_params (with @) is used in function declarations and anonymous functions where types create bindings.
// param_types (without @) is used in type-level signatures (fn_type, op_decl) where no bindings are created.

param_types: type_expr (COMMA type_expr)*
           |  // empty

contract_block: contract_clause+

contract_clause: requires_clause
               | ensures_clause
               | decreases_clause

requires_clause: REQUIRES LPAREN expr RPAREN

ensures_clause: ENSURES LPAREN expr RPAREN

decreases_clause: DECREASES LPAREN expr (COMMA expr)* RPAREN

effect_clause: EFFECTS LPAREN effect_row RPAREN

effect_row: pure_effect
          | effect_set

pure_effect: PURE

effect_set: LT effect_list GT

effect_list: effect_ref (COMMA effect_ref)*

effect_ref: UPPER_IDENT type_args?
          | UPPER_IDENT DOT UPPER_IDENT type_args?  // qualified effect

fn_body: LBRACE block_contents RBRACE

where_block: WHERE LBRACE fn_decl+ RBRACE
```

### 10.3.3 Data Type Declarations

```ebnf
data_decl: DATA UPPER_IDENT type_params? invariant_clause? LBRACE constructor_list RBRACE

type_params: LT type_var_list GT

invariant_clause: INVARIANT LPAREN expr RPAREN

constructor_list: constructor (COMMA constructor)*

constructor: UPPER_IDENT LPAREN type_expr (COMMA type_expr)* RPAREN
           | UPPER_IDENT  // no fields
```

### 10.3.4 Type Aliases

```ebnf
type_alias_decl: TYPE UPPER_IDENT type_params? ASSIGN type_expr SEMICOLON
```

### 10.3.5 Effect Declarations

```ebnf
effect_decl: EFFECT UPPER_IDENT type_params? LBRACE op_decl+ RBRACE

op_decl: OP LOWER_IDENT LPAREN param_types ARROW type_expr RPAREN SEMICOLON
```

### 10.3.6 Ability Declarations

```ebnf
ability_decl: ABILITY UPPER_IDENT type_params? LBRACE op_decl+ RBRACE
```

Abilities share the `op_decl` production with effects. Both use the same `op` keyword for declaring operations. See Section 9.8 for semantics.

### 10.3.7 Type Expressions

```ebnf
type_expr: UPPER_IDENT type_args?          // named type or type variable: Int, T, Array<Int>, Tuple<Int, String>
         | fn_type                          // function type
         | refinement_type                  // { @Int | @Int.0 > 0 }

type_args: LT type_expr (COMMA type_expr)* GT

fn_type: FN LPAREN param_types ARROW type_expr RPAREN effect_clause

tuple_type: UPPER_IDENT LT type_expr (COMMA type_expr)* GT
          // not a separate alternative: "Tuple" is parsed by type_expr's
          // UPPER_IDENT type_args? form and distinguished semantically

refinement_type: LBRACE AT type_expr BAR expr RBRACE
```

### 10.3.8 Expressions

```ebnf
expr: pipe_expr

pipe_expr: implies_expr (PIPE implies_expr)*

implies_expr: or_expr (IMPLIES implies_expr)?

or_expr: and_expr (OR and_expr)*

and_expr: eq_expr (AND eq_expr)*

eq_expr: cmp_expr ((EQ | NEQ) cmp_expr)?

cmp_expr: add_expr ((LT | GT | LE | GE) add_expr)?

add_expr: mul_expr ((PLUS | MINUS) mul_expr)*

mul_expr: unary_expr ((STAR | SLASH | PERCENT) unary_expr)*

unary_expr: NOT unary_expr
          | MINUS unary_expr
          | postfix_expr

postfix_expr: primary_expr (LBRACKET expr RBRACKET)*  // array indexing

primary_expr: INT_LIT
            | FLOAT_LIT
            | STRING_LIT
            | TRUE
            | FALSE
            | LPAREN RPAREN                 // unit literal
            | HOLE                          // typed hole ? (Section 4.17)
            | slot_ref                      // @T.n
            | result_ref                    // @T.result
            | fn_call                       // function/constructor application
            | anonymous_fn                  // anonymous function
            | if_expr                       // conditional
            | match_expr                    // pattern matching
            | block_expr                    // block
            | handle_expr                   // effect handler
            | array_literal                 // [1, 2, 3]
            | old_expr                      // old(State<Int>)
            | new_expr                      // new(State<Int>)
            | assert_expr                   // assert(pred)
            | assume_expr                   // assume(pred)
            | forall_expr                   // forall(@Nat, bound, pred_fn)
            | exists_expr                   // exists(@Nat, bound, pred_fn)
            | LPAREN expr RPAREN            // parenthesized expression
```

### 10.3.9 Slot References

```ebnf
slot_ref: AT UPPER_IDENT type_args? DOT INT_LIT

result_ref: AT UPPER_IDENT type_args? DOT RESULT
```

### 10.3.10 Function Calls and Constructors

```ebnf
fn_call: LOWER_IDENT LPAREN arg_list? RPAREN          // function call
       | UPPER_IDENT LPAREN arg_list? RPAREN           // constructor call
       | UPPER_IDENT                                    // nullary constructor
       | qualified_call                                 // Effect.op(args)
       | module_call                                    // module::fn(args)

qualified_call: UPPER_IDENT DOT LOWER_IDENT LPAREN arg_list? RPAREN  // Effect.operation(args)

module_call: module_path DOUBLE_COLON LOWER_IDENT LPAREN arg_list? RPAREN  // module::function(args)

arg_list: expr (COMMA expr)*
```

### 10.3.11 Anonymous Functions

```ebnf
anonymous_fn: FN LPAREN fn_params? ARROW AT type_expr RPAREN effect_clause fn_body
```

### 10.3.12 Conditional Expressions

```ebnf
if_expr: IF expr THEN block_expr ELSE block_expr
```

### 10.3.13 Match Expressions

```ebnf
match_expr: MATCH expr LBRACE match_arm (COMMA match_arm)* RBRACE

match_arm: pattern ARROW expr

pattern: UPPER_IDENT LPAREN pattern (COMMA pattern)* RPAREN  // constructor pattern
       | UPPER_IDENT                                           // nullary constructor
       | UNDERSCORE                                            // wildcard
       | INT_LIT                                               // integer literal pattern
       | STRING_LIT                                            // string literal pattern
       | TRUE                                                  // boolean literal pattern
       | FALSE
       | AT type_expr                                          // typed binding pattern
```

### 10.3.14 Block Expressions

```ebnf
block_expr: LBRACE block_contents RBRACE

block_contents: statement* expr

statement: let_stmt
         | expr SEMICOLON                 // expression statement (for effects)

let_stmt: LET AT type_expr ASSIGN expr SEMICOLON
        | LET tuple_destruct ASSIGN expr SEMICOLON

tuple_destruct: UPPER_IDENT LT AT type_expr (COMMA AT type_expr)* GT
```

### 10.3.15 Effect Handlers

```ebnf
handle_expr: HANDLE LBRACKET effect_ref RBRACKET handler_state? LBRACE handler_clause (COMMA handler_clause)* RBRACE IN block_expr

handler_state: LPAREN AT type_expr ASSIGN expr RPAREN

handler_clause: LOWER_IDENT LPAREN handler_params? RPAREN ARROW handler_body with_clause?

handler_params: AT type_expr (COMMA AT type_expr)*

handler_body: expr
// Block expressions ({ ... }) are reachable via expr, so no separate alternative is needed.

with_clause: WITH AT type_expr ASSIGN expr
// The state update of a stateful handler clause: resume(expr) with @T = expr.
// It attaches to the clause, not to resume — resume is a LOWER_IDENT, not a
// keyword terminal, so resume(expr) is parsed as a regular fn_call.
```

`resume` stays an ordinary `LOWER_IDENT` at every point above: no production and no terminal mentions it, and the parser gives it no special treatment. Its reservation as a function name (Chapter 1, Section 1.4) is therefore enforced after parsing, by the checker — `fn resume(...)` parses and is then rejected **E153** (Chapter 5, Section 5.2). The two statements are about different phases and do not conflict.

### 10.3.16 Array Literals

```ebnf
array_literal: LBRACKET arg_list? RBRACKET
```

### 10.3.17 Contract-Only Expressions

```ebnf
old_expr: OLD LPAREN effect_ref RPAREN

new_expr: NEW LPAREN effect_ref RPAREN

assert_expr: ASSERT LPAREN expr RPAREN

assume_expr: ASSUME LPAREN expr RPAREN

forall_expr: FORALL LPAREN AT type_expr COMMA expr COMMA anonymous_fn RPAREN

exists_expr: EXISTS LPAREN AT type_expr COMMA expr COMMA anonymous_fn RPAREN
```

`assert_expr` and `assume_expr` are expressions, reachable through `primary_expr` like any other. `assert(p);` is a statement only by way of `expr SEMICOLON`, which is also where it is almost always written; nothing stops either from appearing in any other expression position.

### 10.3.18 Tuple Literals

```ebnf
tuple_literal: UPPER_IDENT LPAREN arg_list RPAREN
             // not a separate alternative: "Tuple" is parsed by fn_call's
             // constructor form and distinguished semantically
```

## 10.4 Operator Precedence Table

| Precedence | Operators | Associativity | Grammar rule |
|------------|-----------|---------------|--------------|
| 10 | function call, `[]` | Left | `postfix_expr` |
| 9 | unary `-`, `!` | Prefix | `unary_expr` |
| 7 | `*`, `/`, `%` | Left | `mul_expr` |
| 6 | `+`, `-` | Left | `add_expr` |
| 5 | `<`, `>`, `<=`, `>=` | None | `cmp_expr` |
| 4 | `==`, `!=` | None | `eq_expr` |
| 3 | `&&` | Left | `and_expr` |
| 2 | `\|\|` | Left | `or_expr` |
| 1.5 | `==>` | Right | `implies_expr` |
| 1 | `\|>` | Left | `pipe_expr` |

## 10.5 Grammar Ambiguities and Resolution

### 10.5.1 Angle Bracket Ambiguity

The `<` and `>` tokens serve double duty as comparison operators and type parameter delimiters. Resolution:

- In **type position** (after a type name, in function signatures, in slot references), `<` begins type arguments.
- In **expression position**, `<` is the less-than operator.

The parser distinguishes these by context: after `UPPER_IDENT` in a type context, `<` is a type argument delimiter. In all other contexts, it is a comparison operator.

### 10.5.2 Minus Ambiguity

`-` is both binary subtraction and unary negation. Resolution:

- If `-` appears at the start of an expression or after an operator, it is unary negation.
- Otherwise, it is binary subtraction.

### 10.5.3 Identifier Classification

`UPPER_IDENT` can be a type name, constructor name, effect name, or ability name. `LOWER_IDENT` can be a function name or module name. The parser uses syntactic context to distinguish:

- After `data`, `type`, `effect`, `ability`, `handle[`, in type annotations: type/effect/ability name
- After `match` patterns, in constructor position: constructor name
- After `fn`, in call position with `LOWER_IDENT(`: function name
- In `module`/`import`: module name

## 10.6 LALR(1) Compatibility Notes

The grammar as specified is designed to be LALR(1)-compatible with the Lark parser generator. Key design choices that ensure this:

1. **No optional semicolons**: all statements end with `;`, removing the need for ASI.
2. **Mandatory braces on all blocks**: no dangling-else ambiguity.
3. **`then` keyword in conditionals**: `if expr then { ... } else { ... }` avoids if/else parsing ambiguity.
4. **Prefix markers**: `@` for slot references, `fn` for functions, `data` for ADTs — each construct has a unique leading token.
5. **No operator overloading**: operator tokens have fixed meaning.
6. **Explicit effect syntax**: `effects(...)` is unambiguous.

If LALR(1) conflicts are discovered during implementation, the grammar should be refactored (not the parser upgraded to GLR). LALR(1) parsability is a design goal because it guarantees the grammar is unambiguous.
