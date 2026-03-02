# Vera Reference Compiler

Architecture documentation for the Vera compiler (`vera/` package). This is for humans who want to understand, modify, or extend the reference implementation.

For other documentation:
- [Root README](../README.md) — project overview, getting started, language examples
- [SKILLS.md](../SKILLS.md) — language reference for LLM agents writing Vera code
- [spec/](../spec/) — formal language specification (13 chapters, 0-12)
- [CONTRIBUTING.md](../CONTRIBUTING.md) — contributor workflow and conventions

## Pipeline Overview

The compiler is a seven-stage pipeline. Each stage consumes the output of the previous one. Each stage has a single public entry point and is independently testable.

```
Source (.vera)
  │
  ▼
┌──────────────────────────────────────────────────────────┐
│  1. Parse                    grammar.lark + parser.py    │
│     Source text → Lark parse tree                        │
└────────────────────────┬─────────────────────────────────┘
                         ▼
┌──────────────────────────────────────────────────────────┐
│  2. Transform                          transform.py      │
│     Lark parse tree → typed AST (ast.py)                 │
└────────────────────────┬─────────────────────────────────┘
                         ▼
┌──────────────────────────────────────────────────────────┐
│  2b. Resolve                           resolver.py       │
│      Map import paths → source files, parse + cache      │
│      Circular import detection                           │
└────────────────────────┬─────────────────────────────────┘
                         ▼
┌──────────────────────────────────────────────────────────┐
│  3. Type Check            checker/ + environment.py      │
│     AST → list[Diagnostic]        types.py               │
│     Two-pass: register declarations, then check bodies   │
└────────────────────────┬─────────────────────────────────┘
                         ▼
┌──────────────────────────────────────────────────────────┐
│  4. Verify                      verifier.py + smt.py     │
│     AST → VerifyResult               (Z3 SMT solver)    │
│     Tier 1: Z3 proves   Tier 3: runtime fallback        │
└────────────────────────┬─────────────────────────────────┘
                         ▼
┌──────────────────────────────────────────────────────────┐
│  5. Compile                    codegen/ + wasm/           │
│     AST → CompileResult          (WAT text + WASM binary)│
│     Runtime contract insertion for Tier 3                │
└────────────────────────┬─────────────────────────────────┘
                         ▼
┌──────────────────────────────────────────────────────────┐
│  6. Execute                            (wasmtime)        │
│     WASM binary → host runtime with IO bindings          │
└──────────────────────────────────────────────────────────┘
```

Errors never cause early exit. Parse errors raise exceptions (the tree is incomplete), but the type checker and verifier **accumulate** all diagnostics and return them as a list. This is critical for LLM consumption — the model gets all feedback in one pass.

Public entry points (from `parser.py` and `codegen/`):

```python
parse(source, file=None)        # → Lark Tree
parse_file(path)                # → Lark Tree (from disk)
parse_to_ast(source, file=None) # → Program AST
typecheck_file(path)            # → list[Diagnostic]
verify_file(path)               # → VerifyResult
compile(program, verify_result) # → CompileResult (WAT + WASM bytes)
execute(compile_result, ...)    # → run WASM via wasmtime
```

## Module Map

| Module | Lines | Stage | Purpose | Key API |
|--------|------:|-------|---------|---------|
| `grammar.lark` | 330 | Parse | LALR(1) grammar definition | *(consumed by Lark)* |
| `parser.py` | 147 | Parse | Lark frontend, error diagnosis | `parse()`, `parse_file()` |
| `transform.py` | 1,000 | Transform | Lark tree → AST transformer | `transform()` |
| `ast.py` | 785 | Transform | Frozen dataclass AST nodes, source formatting | `Program`, `Node`, `Expr`, `format_expr` |
| `types.py` | 307 | Type check | Semantic type representation | `Type`, `is_subtype()` |
| `environment.py` | 302 | Type check | Type environment, scope stacks | `TypeEnv` |
| `checker/` | 2,248 | Type check | Two-pass type checker (mixin package) | `typecheck()` |
| `  core.py` | 356 | | TypeChecker class, orchestration, contracts | |
| `  resolution.py` | 190 | | AST TypeExpr → semantic Type, inference | |
| `  modules.py` | 153 | | Cross-module registration (C7b/C7c) | |
| `  registration.py` | 138 | | Pass 1 forward declarations | |
| `  expressions.py` | 548 | | Expression synthesis, operators, statements | |
| `  calls.py` | 405 | | Function/constructor/module calls | |
| `  control.py` | 453 | | If/match, patterns, effect handlers | |
| `resolver.py` | 213 | Resolve | Module path resolution, parse cache | `ModuleResolver` |
| `smt.py` | 547 | Verify | Z3 translation layer | `SmtContext`, `SlotEnv` |
| `verifier.py` | 703 | Verify | Contract verification | `verify()` |
| `wasm/` | 2,474 | Compile | WASM translation layer (package) | `WasmContext`, `WasmSlotEnv`, `StringPool` |
| ` ├ context.py` | 369 | | Composed WasmContext, expression dispatcher, block translation | |
| ` ├ helpers.py` | 211 | | WasmSlotEnv, StringPool, type mapping, array element helpers | |
| ` ├ inference.py` | 527 | | Type inference, slot/type utilities, operator tables | |
| ` ├ operators.py` | 430 | | Binary/unary operators, if, quantifiers, assert/assume, old/new | |
| ` ├ calls.py` | 223 | | Function calls, generic resolution, effect handlers | |
| ` ├ closures.py` | 248 | | Closures, anonymous functions, free variable analysis | |
| ` └ data.py` | 460 | | Constructors, match expressions, arrays, indexing | |
| `codegen/` | 2,140 | Compile | Codegen orchestrator (mixin package) | `compile()`, `execute()` |
| `  api.py` | 265 | | Public API, dataclasses, host bindings, `execute()` | |
| `  core.py` | 285 | | CodeGenerator class, orchestration, type helpers | |
| `  modules.py` | 200 | | Cross-module registration + call detection (C7e) | |
| `  registration.py` | 105 | | Pass 1 forward declarations, ADT layout | |
| `  monomorphize.py` | 410 | | Generic instantiation, type inference (Pass 1.5) | |
| `  functions.py` | 185 | | Function body compilation (Pass 2) | |
| `  closures.py` | 175 | | Closure lifting | |
| `  contracts.py` | 250 | | Runtime pre/postconditions, old state snapshots | |
| `  assembly.py` | 100 | | WAT module assembly | |
| `  compilability.py` | 155 | | Compilability checks, state handler scanning | |
| `tester.py` | ~530 | Test | Z3-guided input generation, WASM execution, tier classification | `test()` |
| `formatter.py` | 1,018 | Format | Canonical code formatter | `format_source()` |
| `errors.py` | 459 | All | Diagnostic class, error hierarchy, error code registry | `Diagnostic`, `VeraError`, `ERROR_CODES` |
| `cli.py` | 725 | All | CLI commands | `main()` |
| `registration.py` | 58 | Type check | Shared function registration | `register_fn()` |

Total: ~12,069 lines of Python + 330 lines of grammar.

## Parsing

**Files:** `grammar.lark` (330 lines), `parser.py` (147 lines)

The grammar is a Lark LALR(1) grammar derived from the formal EBNF in spec Chapter 10. It uses:

- **String literals** for keywords (`"fn"`, `"let"`, `"match"`, etc.)
- **`?rule` prefix** to inline single-child nodes (cleaner parse trees)
- **`UPPER_CASE`** for terminal rules (`INT_LIT`, `UPPER_IDENT`, etc.)
- **Precedence climbing** for operators: pipe > implies > or > and > eq > cmp > add > mul > unary > postfix

The parser is **lazily constructed and cached** — `_get_parser()` builds the Lark parser on first call and reuses it. Lark's `propagate_positions=True` attaches source locations to every tree node, which the transformer carries through to AST `Span` objects.

**Error diagnosis:** When Lark raises an `UnexpectedToken` or `UnexpectedCharacters`, `diagnose_lark_error()` pattern-matches on the expected token set to produce LLM-oriented diagnostics. For example, if the expected set includes `"requires"` but the parser got `"{"`, the diagnostic is "missing contract block" with a concrete fix showing the `requires()`/`ensures()`/`effects()` structure.

## AST

**Files:** `ast.py` (690 lines), `transform.py` (1,000 lines)

### Node hierarchy

The AST is a shallow class hierarchy. Every node is a frozen dataclass carrying an optional source `Span`.

```
Node
├── Expr                                    Expressions
│   ├── IntLit, FloatLit, StringLit         Literals
│   ├── BoolLit, UnitLit, ArrayLit
│   ├── SlotRef(@Type.n)                    Typed De Bruijn reference
│   ├── ResultRef(@Type.result)             Return value reference
│   ├── BinaryExpr, UnaryExpr              Operators
│   ├── FnCall, ConstructorCall            Calls
│   ├── QualifiedCall, ModuleCall          Qualified calls
│   ├── NullaryConstructor                 Enum-like constructors
│   ├── IfExpr, MatchExpr                  Control flow
│   ├── Block                              Block expression (stmts + expr)
│   ├── HandleExpr                         Effect handlers
│   ├── AnonFn                             Anonymous functions
│   ├── ForallExpr, ExistsExpr             Quantifiers (contracts only)
│   ├── OldExpr, NewExpr                   State snapshots (contracts only)
│   ├── AssertExpr, AssumeExpr             Assertions
│   └── IndexExpr, PipeExpr                Postfix operations
│
├── TypeExpr                                Type expressions (syntactic)
│   ├── NamedType                          Simple and parameterised types
│   ├── FnType                             Function types
│   └── RefinementType                     { @T | predicate }
│
├── Pattern                                 Match patterns
│   ├── ConstructorPattern                 Some(@Int)
│   ├── NullaryPattern                     None, Red
│   ├── BindingPattern                     @Type (binds a value)
│   ├── LiteralPattern                     0, "x", true
│   └── WildcardPattern                    _
│
├── Stmt                                    Statements
│   ├── LetStmt                            let @T = expr;
│   ├── LetDestruct                        let Ctor<@T> = expr;
│   └── ExprStmt                           expr; (side-effect)
│
├── Decl                                    Declarations
│   ├── FnDecl                             Function
│   ├── DataDecl                           ADT
│   ├── TypeAliasDecl                      Type alias
│   └── EffectDecl                         Effect
│
├── Contract                                Contract clauses
│   ├── Requires, Ensures                  Pre/postconditions
│   ├── Decreases                          Termination metric
│   └── Invariant                          Data type invariant
│
└── EffectRow                               Effect specifications
    ├── PureEffect                         effects(pure)
    └── EffectSet                          effects(<IO, State<Int>>)
```

### Transformation

`transform.py` is a Lark `Transformer` — its methods are named after grammar rules and called bottom-up. Each method receives already-transformed children and returns an AST node. Sentinel types (`_ForallVars`, `_Signature`, `_TypeParams`, `_WhereFns`, `_TupleDestruct`) aggregate intermediate results during transformation but are never exported in the final AST.

**Immutability:** All fields use tuples, not lists. All dataclasses are frozen. This means compiler phases never mutate the AST — they produce new data or collect diagnostics.

## Type Checking

**Files:** `checker/` (2,248 lines across 8 modules), `types.py` (307 lines), `environment.py` (302 lines)

This is the most architecturally complex stage.

### Three-pass architecture

```
 Pass 0: Module Registration       Pass 1: Local Registration         Pass 2: Checking
  ┌──────────────────────┐          ┌────────────────────────┐          ┌──────────────────────────┐
  │  For each resolved   │          │  Walk all declarations │          │  Walk all declarations   │
  │  module:             │          │                        │          │                          │
  │   • create temp      │          │  Register into TypeEnv:│          │  For each function:      │
  │     TypeChecker      │  TypeEnv │   • functions           │  TypeEnv │   • bind forall vars    │
  │   • register decls   │ ───────▶ │   • ADTs + constructors│ ───────▶ │   • resolve param types  │
  │   • harvest into     │ imports  │   • type aliases       │ populated│   • push scope, bind     │
  │     module-qual dicts│ injected │   • effects + ops      │          │   • check contracts      │
         │                        │          │   • synthesise body type │
         │  (signatures only,     │          │   • check effects        │
         │   no bodies checked)   │          │   • pop scope            │
         └────────────────────────┘          └──────────────────────────┘
```

**Why two passes:** Forward references and mutual recursion. A function declared on line 50 can call a function declared on line 10, or vice versa. Pass 1 makes all signatures visible before any bodies are checked.

### Syntactic vs semantic types

The compiler maintains two distinct type representations:

- **`ast.TypeExpr`** — what the programmer wrote. `NamedType("PosInt")`, `FnType(...)`, `RefinementType(...)`. These are AST nodes with source spans.
- **`types.Type`** — resolved canonical form. `PrimitiveType("Int")`, `AdtType("Option", (INT,))`, `FunctionType(...)`. These are semantic objects used for type compatibility.

`_resolve_type()` in the checker bridges them: it looks up type aliases, expands parameterised types, and resolves type variables from `forall` bindings.

**Why this matters:** Type aliases are **opaque** for slot reference matching. If `type PosInt = { @Int | @Int.0 > 0 }`, then `@PosInt.0` counts `PosInt` bindings and `@Int.0` counts `Int` bindings — they are separate namespaces. But for type compatibility, `PosInt` resolves to a refined `Int` and subtypes accordingly.

### De Bruijn slot resolution

Vera uses typed De Bruijn indices instead of variable names. `@Int.0` means "the most recent `Int` binding", `@Int.1` means "the one before that".

```
private fn add(@Int, @Int -> @Int) {        Parameters bind left-to-right.
  let @Int = @Int.0 + @Int.1;       @Int.0 = param₂ (rightmost), @Int.1 = param₁
  @Int.0                             @Int.0 = let binding (shadows param₂)
}

Scope stack after the let binding:
┌──────────────────────────────┐
│ scope 0 (fn params)          │
│   Int: [param₁, param₂]     │  ← bound left-to-right
├──────────────────────────────┤
│ scope 1 (fn body)            │
│   Int: [let_binding]         │  ← most recent
└──────────────────────────────┘

resolve("Int", 0) → let_binding    (index 0 = most recent)
resolve("Int", 1) → param₂         (index 1 = one before)
resolve("Int", 2) → param₁         (index 2 = two before)
```

The resolver walks scopes **innermost to outermost**, counting backwards within each scope. This is implemented in `TypeEnv.resolve_slot()`.

Each binding tracks its **source** (`"param"`, `"let"`, `"match"`, `"handler"`, `"destruct"`) and its **canonical type name** — the syntactic name used for slot reference matching, which respects alias opacity.

### Subtyping

The subtyping rules (in `types.py`) are:

- `Nat <: Int` — naturals are integers
- `Never <: T` — bottom type subtypes everything
- `{ T | P } <: T` — refinement types subtype their base
- `TypeVar("T") <: TypeVar("T")` — reflexive equality only; TypeVars are not compatible with concrete types
- `AdtType` — structural: same name + covariant subtyping on type arguments

### Error accumulation

The type checker **never raises exceptions** for type errors. All errors are collected as `Diagnostic` objects in a list. When a subexpression has an error, `UnknownType` is returned instead — this prevents cascading errors (e.g., one wrong type causing ten downstream mismatches).

Context flags (`in_ensures`, `in_contract`, `current_return_type`, `current_effect_row`) control context-sensitive checks: `@T.result` is only valid inside `ensures`, `old()`/`new()` only in postconditions, etc.

### Built-ins

`TypeEnv._register_builtins()` registers the built-in types and operations:

| Built-in | Kind | Details |
|----------|------|---------|
| `Option<T>` | ADT | `None`, `Some(T)` constructors |
| `Result<T, E>` | ADT | `Ok(T)`, `Err(E)` constructors |
| `State<T>` | Effect | `get(Unit) → T`, `put(T) → Unit` operations |
| `IO` | Effect | No operations exposed at type level |
| `Diverge` | Effect | No operations — marker for non-termination |
| `length` | Function | `forall<T> Array<T> → Int`, pure |
| `string_length` | Function | `String → Nat`, pure |
| `string_concat` | Function | `String, String → String`, pure |
| `string_slice` | Function | `String, Nat, Nat → String`, pure |
| `char_code` | Function | `String, Int → Nat`, pure |
| `parse_nat` | Function | `String → Nat`, pure (see [#174](https://github.com/aallan/vera/issues/174)) |
| `parse_float64` | Function | `String → Float64`, pure |
| `to_string` | Function | `Int → String`, pure |
| `strip` | Function | `String → String`, pure (zero-copy) |

Additionally, `resume` is bound as a temporary function inside handler clause bodies (in `_check_handle()`). Its type is derived from the operation: for `op(params) → ReturnType`, `resume` has type `fn(ReturnType) → Unit effects(pure)`. The binding is added to `env.functions` before checking the clause body and removed afterward.

## Contract Verification

**Files:** `verifier.py` (703 lines), `smt.py` (547 lines)

### Tiered model

The spec defines three verification tiers. The compiler implements Tiers 1 and 3:

| Tier | What | How | Status |
|------|------|-----|--------|
| **1** | Decidable fragment: QF_LIA + Booleans + comparisons + if/else + let + match + constructors + `length` + decreases | Z3 proves automatically | Implemented |
| **2** | Extended: quantifiers, function call reasoning, array access | Z3 with hints/timeouts | Future |
| **3** | Everything else | Runtime assertion fallback | Warning emitted |

When a contract or function body contains constructs that can't be translated to Z3, the verifier **does not error** — it classifies the contract as Tier 3 and emits a warning. This means every valid program can be verified (at least partially).

### Verification condition generation

```
 requires(P₁), requires(P₂)           ensures(Q)
         │                                 │
         ▼                                 ▼
  assumptions = [P₁, P₂]          goal = Q[result ↦ body_expr]
         │                                 │
         └────────────┬────────────────────┘
                      ▼
               ┌─────────────┐
               │  Z3 Solver  │
               │             │
               │  assert P₁  │   Refutation: if ¬Q is satisfiable
               │  assert P₂  │   under the assumptions, there's a
               │  assert ¬Q  │   counterexample. If unsatisfiable,
               │             │   the postcondition always holds.
               │  check()    │
               └──────┬──────┘
                      │
            ┌─────────┼──────────┐
            ▼         ▼          ▼
         unsat       sat      unknown
        Verified   Violated    Tier 3
                  + counter-
                   example
```

**Forward symbolic execution:** The function body is translated to a Z3 expression, and `@T.result` in postconditions is substituted with this expression. This is simpler than weakest-precondition calculus and equivalent for the non-recursive straight-line code that Tier 1 handles.

**Trivial contract fast path:** `requires(true)` and `ensures(true)` are detected syntactically (`BoolLit(true)`) and counted as Tier 1 verified without invoking Z3. Most example programs use `requires(true)`, so this avoids unnecessary solver overhead.

### SMT translation

`SmtContext` in `smt.py` translates AST expressions to Z3 formulas. It returns `None` for any construct it can't handle — this triggers Tier 3 gracefully.

`SlotEnv` mirrors the De Bruijn scope stack with Z3 variables. It's immutable: `push()` returns a new environment. `resolve(T, n)` computes `stack[len - 1 - n]`.

| AST construct | Z3 translation |
|---------------|----------------|
| `IntLit(v)` | `z3.IntVal(v)` |
| `BoolLit(v)` | `z3.BoolVal(v)` |
| `SlotRef(T, n)` | `env.resolve(T, n)` |
| `ResultRef(T)` | `result_var` |
| `+`, `-`, `*`, `/`, `%` | Z3 integer arithmetic |
| `==`, `!=`, `<`, `>`, `<=`, `>=` | Z3 comparison |
| `&&`, `\|\|`, `==>` | `z3.And`, `z3.Or`, `z3.Implies` |
| `!`, `-` (unary) | `z3.Not`, negation |
| `if c then t else e` | `z3.If(c, t, e)` |
| `length(arr)` | Uninterpreted function, constrained `>= 0` |
| `let @T = v; body` | Push `v` onto `SlotEnv`, translate body |
| `match ... { arms }` | Nested `z3.If` chain with recognizer conditions |
| `Nil`, `Cons(a, b)` | Z3 ADT sort constructor applications |
| `decreases(e)` | Verified via `e_callee < e_caller` (Nat) or rank function (ADT) |
| Handle, lambda, quantifier, old/new | `None` (Tier 3) |

### Counterexample extraction

When Z3 finds a satisfying assignment to the negated postcondition (= a counterexample), the verifier extracts concrete values from the Z3 model and includes them in the diagnostic:

```
Error at line 3, column 3:
  Postcondition may not hold: @Int.result > @Int.0

  Counterexample: @Int.0 = 0, @Int.1 = -5
  The Z3 solver found concrete inputs where the postcondition fails.

  Fix: strengthen the requires() clause or weaken the ensures() clause.
  See: Chapter 6, Section 6.4 "Verification Conditions"
```

## Code Generation

**Files:** `codegen/` (2,140 lines across 11 modules), `wasm/` (2,474 lines across 7 modules)

### Compilation pipeline

`compile()` in `codegen/api.py` takes a `Program` AST and optional `VerifyResult`, and produces a `CompileResult` containing WAT text, WASM bytes, export names, and diagnostics.

```
Program AST → CodeGenerator._register_functions()  (pass 1)
            → CodeGenerator._compile_functions()   (pass 2)
            → WAT module text
            → wasmtime.wat2wasm() → WASM bytes
```

The two-pass architecture mirrors the type checker: pass 1 registers all function signatures so forward references and mutual recursion work, pass 2 compiles bodies.

### WASM translation

`WasmContext` in `wasm/` mirrors `SmtContext` in `smt.py`. It translates AST expressions to WAT instructions via `translate_expr()`, which dispatches on AST node type. Returns `None` for unsupported constructs (graceful degradation, same pattern as SMT translation).

`WasmSlotEnv` mirrors `SlotEnv` — it maps typed De Bruijn indices (`@T.n`) to WASM local indices. Immutable: `push()` returns a new environment.

### String pool

`StringPool` manages string constants in the WASM data section. Identical strings are deduplicated. Each string gets an `(offset, length)` pair. `StringLit` compiles to two `i32.const` instructions pushing the pointer and length.

### IO host bindings

`IO.print` compiles to a call to an imported host function. The `execute()` function in `codegen/api.py` provides the host implementation via wasmtime's `Linker`: it reads UTF-8 bytes from WASM linear memory and writes to stdout (or a capture buffer for testing).

### Runtime contracts

The code generator classifies contracts using the verifier's tier results:
- **Tier 1 (proven):** omitted — statically guaranteed
- **Trivial (`requires(true)`, `ensures(true)`):** omitted — no meaningful check
- **Tier 3 (unverified):** compiled as runtime assertions using `unreachable` traps

Preconditions are checked at function entry. Postconditions store the return value in a temporary local, check the condition, and trap or return.

**Informative violation messages:** Before each `unreachable`, the codegen emits a call to the `vera.contract_fail` host import with a pre-interned message string describing which contract failed (function name, contract kind, expression text). The host callback stores the message; when the trap is caught, `execute()` raises a `RuntimeError` with the stored message instead of a raw WASM trap. `format_expr()` and `format_fn_signature()` in `ast.py` reconstruct source text from AST nodes for the message.

## Error System

**File:** `errors.py` (459 lines)

```
VeraError (exception hierarchy)
├── ParseError       ← raised, stops pipeline
├── TransformError   ← raised, stops pipeline
├── TypeError        ← accumulated as Diagnostic, never raised
└── VerifyError      ← accumulated as Diagnostic, never raised
```

Every diagnostic includes eight fields designed for LLM consumption:

```
┌──────────────────────────────────────────────────────┐
│  Diagnostic                                          │
│                                                      │
│  description   "what went wrong" (plain English)     │
│  location      file, line, column                    │
│  source_line   the offending line of code            │
│  rationale     which language rule was violated       │
│  fix           concrete corrected code               │
│  spec_ref      "Chapter X, Section Y.Z"              │
│  severity      "error" or "warning"                  │
│  error_code    stable identifier ("E130", "E200")    │
└──────────────────────────────────────────────────────┘
```

`Diagnostic.format()` produces the multi-section natural language output shown in the root README's "What Errors Look Like" section. The format is designed so the compiler's output can be fed directly back to the model that wrote the code.

**Parse error patterns:** `diagnose_lark_error()` in `parser.py` maps common Lark exception patterns to specific diagnostics. It checks expected token sets to distinguish "missing contract block" from "missing effects clause" from "malformed slot reference", producing targeted fix suggestions for each.

## Design Patterns

These patterns pervade the codebase. Understanding them makes the code easier to navigate.

### 1. Frozen dataclasses

All AST nodes, type objects, and environment data structures are frozen dataclasses. Fields use tuples, not lists. Compiler phases never mutate their input — they produce new data or collect diagnostics. This prevents accidental state sharing between phases and makes reasoning about data flow straightforward.

### 2. Syntactic vs semantic type separation

`ast.TypeExpr` nodes represent what the programmer wrote. `types.Type` objects represent the resolved canonical form. The `_resolve_type()` method in the checker bridges them. This distinction enables **alias opacity**: `@PosInt.0` matches `PosInt` bindings syntactically, while `PosInt` resolves to `Int` semantically for type compatibility.

### 3. Error accumulation

The type checker and verifier never stop at the first error. All diagnostics are collected and returned at once. `UnknownType` propagates silently through expressions to prevent cascading — one wrong type won't generate ten downstream errors. This is critical for LLM workflows where the model needs all feedback in a single pass.

### 4. Tiered verification with graceful degradation

`SmtContext.translate_expr()` returns `None` for any construct it can't handle. The verifier interprets `None` as "Tier 3: warn and assume runtime check". This means **no valid program ever fails verification** — contracts that Z3 can't prove get warnings, not errors. As the SMT translation grows (Tier 2, quantifiers, etc.), constructs graduate from Tier 3 to Tier 1.

The same pattern applies to code generation: `WasmContext.translate_expr()` returns `None` for unsupported expressions, and the code generator skips those functions with a warning. As codegen support grows, more functions become compilable.

### 5. Lark Transformer bottom-up

Methods in `transform.py` are named after grammar rules and receive already-transformed children. Sentinel types (`_ForallVars`, `_Signature`, `_TypeParams`, `_WhereFns`) carry intermediate results between grammar rules during transformation but are never part of the exported AST. The `__default__()` method catches any unhandled grammar rule and raises `TransformError`.

### 6. Effect row infrastructure

The type system includes open effect rows (`row_var` field in `ConcreteEffectRow`) for future row polymorphism (`forall<E> fn(...) effects(<E>)`). Currently, effect checking is basic — pure functions can't call effectful operations, and handlers discharge their declared effect. The infrastructure is in place for richer effect tracking in later phases.

### 7. LLM-oriented diagnostics

Every diagnostic includes a description (what went wrong), rationale (which language rule), fix (corrected code), spec reference, and a stable error code (`E001`–`E607`). The compiler's output is designed to be fed directly back to the model as corrective context. See spec Chapter 0, Section 0.5 "Diagnostics as Instructions" for the philosophy.

### 8. Stable error code taxonomy

Every diagnostic has a unique code grouped by compiler phase:

| Range | Phase | Source |
|-------|-------|--------|
| E001–E007 | Parse | `errors.py` factory functions |
| E010 | Transform | `transform.py` |
| E1xx | Type check: core + expressions | `checker/core.py`, `checker/expressions.py` |
| E2xx | Type check: calls | `checker/calls.py` |
| E3xx | Type check: control flow | `checker/control.py` |
| E5xx | Verification | `verifier.py` |
| E6xx | Codegen | `codegen/` |

The `ERROR_CODES` dict in `errors.py` maps every code to a short description (80 entries). Codes are stable across versions — they can be used for programmatic filtering, suppression, and documentation lookups. Formatted output shows the code in brackets: `[E130] Error at line 5, column 3:`.

## Test Suite

See **[TESTING.md](../TESTING.md)** for the comprehensive testing reference -- test file table, compiler code coverage, language feature coverage, helper conventions, validation scripts, CI pipeline, and guidelines for adding tests.

## Current Limitations

Honest inventory of what the compiler cannot do, and where each limitation is addressed in the roadmap.

| Limitation | Why | Planned |
|-----------|-----|---------|
| **Module system limitations** | Module system complete (C7a-C7f); remaining issue: flat-compilation name collisions | [#110](https://github.com/aallan/vera/issues/110) |
| **Limited effect checking** | Pure vs effectful only; no subeffecting or row unification | [#21](https://github.com/aallan/vera/issues/21) |
| **No quantifier termination** | `decreases` verified for self-recursive and mutual recursion (where-blocks); no support for lexicographic ordering or non-structural measures | [#45](https://github.com/aallan/vera/issues/45) |
| **No quantifier verification** | `forall`/`exists` in contracts always Tier 3 | [#13](https://github.com/aallan/vera/issues/13) |
| **Minimal type inference** | Call-site generic instantiation only, no Hindley-Milner | [#55](https://github.com/aallan/vera/issues/55) |
| **No incremental compilation** | Full file processed from scratch each time | [#56](https://github.com/aallan/vera/issues/56) |
| **No garbage collection** | Bump allocator only; linear memory is not reclaimed | [#51](https://github.com/aallan/vera/issues/51) |
| **String constants only** | No dynamic string construction | [#52](https://github.com/aallan/vera/issues/52) |

## Extending the Compiler

Practical recipes for common extensions.

### New AST node

1. Add a frozen dataclass to `ast.py` under the appropriate category base (`Expr`, `Stmt`, etc.)
2. Add a grammar rule to `grammar.lark`
3. Add a transformer method to `transform.py` with the same name as the grammar rule
4. The transformer method receives already-transformed children and returns the new node

### New semantic type

1. Add a `Type` subclass to `types.py`
2. Update `is_subtype()`, `types_equal()`, `substitute()`, and `pretty_type()` in `types.py`
3. Update `_resolve_type()` in `checker/resolution.py` to handle the new `TypeExpr` → `Type` mapping

### New built-in function or effect

Add entries to `TypeEnv._register_builtins()` in `environment.py`:

```python
# Built-in function:
self.functions["name"] = FunctionInfo(
    name="name", forall_vars=..., param_types=...,
    return_type=..., effect=PureEffectRow(),
)

# Built-in effect:
self.effects["Name"] = EffectInfo(
    name="Name", type_params=...,
    operations={"op": OpInfo("op", param_types, return_type, "Name")},
)
```

### Extending SMT translation

Add a case to `SmtContext.translate_expr()` in `smt.py`. Return a Z3 expression for supported constructs. **Return `None`** for anything that can't be translated — this triggers Tier 3 gracefully rather than causing an error.

### Extending WASM compilation

Add a case to `WasmContext.translate_expr()` in `wasm/context.py` (or the appropriate submodule). Return a list of WAT instruction strings for supported constructs. **Return `None`** for anything that can't be compiled — this triggers a "function skipped" warning rather than a compilation error.

To add a new WASM type mapping, update `wasm_type()` in `wasm/helpers.py` and the type mapping table in `codegen/core.py`.

### New CLI command

1. Add a `cmd_*` function to `cli.py` following the existing pattern (try/except VeraError)
2. Wire it into `main()` dispatch
3. Update the `USAGE` string

## Dependencies

### Runtime

| Package | Version | Purpose |
|---------|---------|---------|
| `lark` | ≥1.1 | LALR(1) parser generator. Chosen for its Python-native implementation, deterministic parsing, and built-in Transformer pattern. |
| `z3-solver` | ≥4.12 | SMT solver for contract verification. Industry-standard solver supporting QF_LIA and Boolean logic. Note: does not ship `py.typed` — mypy override configured in `pyproject.toml`. |
| `wasmtime` | ≥15.0 | WebAssembly runtime. Used for WAT→WASM compilation and execution via `vera compile` / `vera run`. Note: does not ship complete type stubs — mypy override configured in `pyproject.toml`. |

### Development

`pytest`, `pytest-cov` (testing), `mypy` (strict type checking), `hypothesis` (property testing, declared but not yet used), `pre-commit` (commit hooks).

---

**See also:** [Project README](../README.md) · [Language spec](../spec/) · [SKILLS.md](../SKILLS.md) · [CONTRIBUTING.md](../CONTRIBUTING.md)
