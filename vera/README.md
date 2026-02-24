# Vera Reference Compiler

Architecture documentation for the Vera compiler (`vera/` package). This is for humans who want to understand, modify, or extend the reference implementation.

For other documentation:
- [Root README](../README.md) — project overview, getting started, language examples
- [SKILLS.md](../SKILLS.md) — language reference for LLM agents writing Vera code
- [spec/](../spec/) — formal language specification (10 chapters)
- [CONTRIBUTING.md](../CONTRIBUTING.md) — contributor workflow and conventions

## Pipeline Overview

The compiler is a six-stage pipeline. Each stage consumes the output of the previous one. Each stage has a single public entry point and is independently testable.

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
│  3. Type Check             checker.py + environment.py   │
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
│  5. Compile                    codegen.py + wasm.py      │
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

Public entry points (from `parser.py` and `codegen.py`):

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
| `grammar.lark` | 328 | Parse | LALR(1) grammar definition | *(consumed by Lark)* |
| `parser.py` | 147 | Parse | Lark frontend, error diagnosis | `parse()`, `parse_file()` |
| `transform.py` | 990 | Transform | Lark tree → AST transformer | `transform()` |
| `ast.py` | 682 | Transform | Frozen dataclass AST nodes | `Program`, `Node`, `Expr` |
| `types.py` | 302 | Type check | Semantic type representation | `Type`, `is_subtype()` |
| `environment.py` | 299 | Type check | Type environment, scope stacks | `TypeEnv` |
| `checker.py` | 1,569 | Type check | Two-pass type checker | `typecheck()` |
| `smt.py` | 363 | Verify | Z3 translation layer | `SmtContext`, `SlotEnv` |
| `verifier.py` | 539 | Verify | Contract verification | `verify()` |
| `wasm.py` | 585 | Compile | WASM translation layer | `WasmContext`, `WasmSlotEnv` |
| `codegen.py` | 653 | Compile | Codegen orchestrator | `compile()`, `execute()` |
| `errors.py` | 354 | All | Diagnostic class, error hierarchy | `Diagnostic`, `VeraError` |
| `cli.py` | 541 | All | CLI commands | `main()` |

Total: ~7,082 lines of Python + 328 lines of grammar.

## Parsing

**Files:** `grammar.lark` (328 lines), `parser.py` (147 lines)

The grammar is a Lark LALR(1) grammar derived from the formal EBNF in spec Chapter 10. It uses:

- **String literals** for keywords (`"fn"`, `"let"`, `"match"`, etc.)
- **`?rule` prefix** to inline single-child nodes (cleaner parse trees)
- **`UPPER_CASE`** for terminal rules (`INT_LIT`, `UPPER_IDENT`, etc.)
- **Precedence climbing** for operators: pipe > implies > or > and > eq > cmp > add > mul > unary > postfix

The parser is **lazily constructed and cached** — `_get_parser()` builds the Lark parser on first call and reuses it. Lark's `propagate_positions=True` attaches source locations to every tree node, which the transformer carries through to AST `Span` objects.

**Error diagnosis:** When Lark raises an `UnexpectedToken` or `UnexpectedCharacters`, `diagnose_lark_error()` pattern-matches on the expected token set to produce LLM-oriented diagnostics. For example, if the expected set includes `"requires"` but the parser got `"{"`, the diagnostic is "missing contract block" with a concrete fix showing the `requires()`/`ensures()`/`effects()` structure.

## AST

**Files:** `ast.py` (682 lines), `transform.py` (990 lines)

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

**Files:** `checker.py` (1,569 lines), `types.py` (302 lines), `environment.py` (299 lines)

This is the most architecturally complex stage.

### Two-pass architecture

```
              Pass 1: Registration                  Pass 2: Checking
         ┌────────────────────────┐          ┌──────────────────────────┐
         │  Walk all declarations │          │  Walk all declarations   │
         │                        │          │                          │
         │  Register into TypeEnv:│          │  For each function:      │
         │   • functions           │  TypeEnv │   • bind forall vars    │
         │   • ADTs + constructors│ ───────▶ │   • resolve param types  │
         │   • type aliases       │ populated│   • push scope, bind     │
         │   • effects + ops      │          │   • check contracts      │
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
fn add(@Int, @Int -> @Int) {        Parameters bind left-to-right.
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
- `TypeVar` — compatible with anything (deferred to instantiation)
- `AdtType` — structural equality on name and type arguments

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
| `length` | Function | `forall<T> Array<T> → Int`, pure |

## Contract Verification

**Files:** `verifier.py` (539 lines), `smt.py` (363 lines)

### Tiered model

The spec defines three verification tiers. The compiler implements Tiers 1 and 3:

| Tier | What | How | Status |
|------|------|-----|--------|
| **1** | Decidable fragment: QF_LIA + Booleans + comparisons + if/else + let + `length` | Z3 proves automatically | Implemented |
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
| Match, handle, lambda, constructor, quantifier, old/new | `None` (Tier 3) |

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

**Files:** `codegen.py` (653 lines), `wasm.py` (585 lines)

### Compilation pipeline

`compile()` in `codegen.py` takes a `Program` AST and optional `VerifyResult`, and produces a `CompileResult` containing WAT text, WASM bytes, export names, and diagnostics.

```
Program AST → CodeGenerator._register_functions()  (pass 1)
            → CodeGenerator._compile_functions()   (pass 2)
            → WAT module text
            → wasmtime.wat2wasm() → WASM bytes
```

The two-pass architecture mirrors the type checker: pass 1 registers all function signatures so forward references and mutual recursion work, pass 2 compiles bodies.

### WASM translation

`WasmContext` in `wasm.py` mirrors `SmtContext` in `smt.py`. It translates AST expressions to WAT instructions via `translate_expr()`, which dispatches on AST node type. Returns `None` for unsupported constructs (graceful degradation, same pattern as SMT translation).

`WasmSlotEnv` mirrors `SlotEnv` — it maps typed De Bruijn indices (`@T.n`) to WASM local indices. Immutable: `push()` returns a new environment.

### String pool

`StringPool` manages string constants in the WASM data section. Identical strings are deduplicated. Each string gets an `(offset, length)` pair. `StringLit` compiles to two `i32.const` instructions pushing the pointer and length.

### IO host bindings

`IO.print` compiles to a call to an imported host function. The `execute()` function in `codegen.py` provides the host implementation via wasmtime's `Linker`: it reads UTF-8 bytes from WASM linear memory and writes to stdout (or a capture buffer for testing).

### Runtime contracts

The code generator classifies contracts using the verifier's tier results:
- **Tier 1 (proven):** omitted — statically guaranteed
- **Trivial (`requires(true)`, `ensures(true)`):** omitted — no meaningful check
- **Tier 3 (unverified):** compiled as runtime assertions using `unreachable` traps

Preconditions are checked at function entry. Postconditions store the return value in a temporary local, check the condition, and trap or return.

## Error System

**File:** `errors.py` (354 lines)

```
VeraError (exception hierarchy)
├── ParseError       ← raised, stops pipeline
├── TransformError   ← raised, stops pipeline
├── TypeError        ← accumulated as Diagnostic, never raised
└── VerifyError      ← accumulated as Diagnostic, never raised
```

Every diagnostic includes six fields designed for LLM consumption:

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

Every diagnostic includes a description (what went wrong), rationale (which language rule), fix (corrected code), and spec reference. The compiler's output is designed to be fed directly back to the model as corrective context. See spec Chapter 0, Section 0.5 "Diagnostics as Instructions" for the philosophy.

## Test Suite

**540 tests** across 8 files, plus 4 validation scripts and CI infrastructure.

### Test files

| File | Tests | Lines | What it covers |
|------|------:|------:|----------------|
| `test_parser.py` | 95 | 791 | Grammar rules, operator precedence, parse errors |
| `test_ast.py` | 84 | 896 | AST transformation, node structure, serialisation |
| `test_checker.py` | 91 | 950 | Type synthesis, slot resolution, effects, contracts |
| `test_verifier.py` | 55 | 654 | Z3 verification, counterexamples, tier classification, Int→Nat enforcement |
| `test_codegen.py` | 130 | 1,397 | WASM compilation, arithmetic, Float64, control flow, strings, IO, contracts, example round-trips |
| `test_cli.py` | 67 | 832 | CLI commands (check, verify, compile, run), subprocess integration, runtime traps, arg validation |
| `test_readme.py` | 2 | 68 | README code sample parsing |
| `test_errors.py` | 16 | 129 | Diagnostic formatting, error patterns |

Total: 5,717 lines of test code (77% of source code size).

### Round-trip testing

Every one of the 14 example programs in `examples/` is tested through **every pipeline stage** via parametrised tests. If you add a new `.vera` example, it's automatically included in the round-trip suite.

### Helper conventions

Each test module defines module-level helper functions (no `conftest.py`):

```python
# test_checker.py pattern:
_check_ok(source)              # assert no type errors
_check_err(source, "match")    # assert at least one error matching substring

# test_verifier.py pattern:
_verify_ok(source)             # assert no verification errors
_verify_err(source, "match")   # assert at least one verification error
_verify_warn(source, "match")  # assert at least one warning

# test_codegen.py pattern:
_compile_ok(source)            # assert compilation succeeds
_run(source, fn, args)         # compile + execute, return result
_run_io(source, fn, args)      # compile + execute, return captured stdout
_run_trap(source, fn, args)    # compile + execute, assert WASM trap
```

### Validation scripts

| Script | What it validates |
|--------|-------------------|
| `scripts/check_examples.py` | All 14 `.vera` examples pass `vera check` + `vera verify` |
| `scripts/check_spec_examples.py` | 154 code blocks from spec chapters parse correctly |
| `scripts/check_readme_examples.py` | Vera code blocks in README.md parse correctly |
| `scripts/check_version_sync.py` | `pyproject.toml` and `vera/__init__.py` versions match |

### CI and pre-commit

**CI** runs on every push and PR to `main`:
- **Test matrix:** 6 jobs (ubuntu + macOS × Python 3.11, 3.12, 3.13)
- **Coverage:** ≥80% threshold (Python 3.12 on ubuntu)
- **Mypy:** strict mode, 11 source files
- **Lint:** example validation + version sync + spec code blocks

**Pre-commit hooks** run on every local commit:
- Trailing whitespace, end-of-file, YAML/TOML, merge conflicts, large files, debug statements
- `mypy vera/` — type checking
- `pytest tests/ -q` — full test suite
- `python scripts/check_examples.py` — example validation (triggers on `.vera` or `vera/**/*.py` or `grammar.lark` changes)

### Adding tests

When extending the compiler, add tests following the existing patterns:

1. **New grammar construct:** Add parser tests to `test_parser.py` (positive and negative)
2. **New AST node:** Add transformation tests to `test_ast.py` (check node fields, spans, serialisation)
3. **New type rule:** Add checker tests to `test_checker.py` using `_check_ok()`/`_check_err()`
4. **New SMT support:** Add verifier tests to `test_verifier.py` using `_verify_ok()`/`_verify_err()`
5. **New codegen support:** Add compilation tests to `test_codegen.py` using `_compile_ok()`/`_run()`/`_run_trap()`
6. **New example program:** Add to `examples/` — it's automatically included in round-trip tests
7. **New error pattern:** Add formatting tests to `test_errors.py`

## Current Limitations

Honest inventory of what the compiler cannot do, and where each limitation is addressed in the roadmap.

| Limitation | Why | Planned |
|-----------|-----|---------|
| **No ADT/match codegen** | Needs tagged union representation in linear memory | [#26](https://github.com/aallan/vera/issues/26) |
| **No closure codegen** | Needs closure conversion pass | [#27](https://github.com/aallan/vera/issues/27) |
| **No effect handler codegen** | Needs continuation-passing transform | [#28](https://github.com/aallan/vera/issues/28) |
| **No generic function codegen** | Needs monomorphization or type erasure | [#29](https://github.com/aallan/vera/issues/29) |
| **No Float64/Byte codegen** | Straightforward extensions | [#25](https://github.com/aallan/vera/issues/25), [#30](https://github.com/aallan/vera/issues/30) |
| **No module resolution** | `import` declarations parsed but not resolved | C7 (module system) |
| **Limited effect checking** | Pure vs effectful only; no subeffecting or row unification | Incremental |
| **No termination verification** | `decreases` clauses parsed but always Tier 3 | Future |
| **No quantifier verification** | `forall`/`exists` in contracts always Tier 3 | Tier 2 |
| **No match/constructor body verification** | Untranslatable to Z3, always Tier 3 | Tier 2 |
| **Minimal type inference** | Call-site generic instantiation only, no Hindley-Milner | Incremental |
| **No incremental compilation** | Full file processed from scratch each time | Low priority |
| **No exhaustiveness checking** | Match expressions not checked for missing cases | Incremental |
| **Spec/parser `@T` notation mismatch** | Spec uses `@T` in data/effect declarations; parser expects bare `T` — see below | Reconciliation |

### Spec/parser notation mismatch

The language specification uses `@T` notation in data type constructor fields and effect operation signatures (e.g., `data Option<T> { Some(@T), None }`, `op get(@Unit -> @T)`). The parser expects bare types in these positions (e.g., `Some(T)`, `op get(Unit -> T)`).

This is an intentional design distinction: the grammar reserves `@` for value-level bindings (function parameters, where `@T.0` creates a slot reference) and uses bare types in type-level signatures (constructor fields, effect ops) where no runtime bindings are created. The spec aspirationally shows `@T` for visual consistency with function parameters.

There are 30 spec code blocks affected, tracked as MISMATCH entries in `scripts/check_spec_examples.py`. Reconciliation will update either the spec or the parser to match; the question is whether binding-site notation should be syntactically uniform across all declaration forms.

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
3. Update `_resolve_type()` in `checker.py` to handle the new `TypeExpr` → `Type` mapping

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

Add a case to `WasmContext.translate_expr()` in `wasm.py`. Return a list of WAT instruction strings for supported constructs. **Return `None`** for anything that can't be compiled — this triggers a "function skipped" warning rather than a compilation error.

To add a new WASM type mapping, update `wasm_type()` in `wasm.py` and the type mapping table in `codegen.py`.

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
