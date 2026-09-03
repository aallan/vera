# Vera Reference Compiler

Architecture documentation for the Vera compiler (`vera/` package). This is for humans who want to understand, modify, or extend the reference implementation.

For other documentation:
- [Root README](../README.md) — project overview, getting started, language examples
- [SKILL.md](../SKILL.md) — language reference for LLM agents writing Vera code
- [spec/](../spec/) — formal language specification (13 chapters, 0-12)
- [CONTRIBUTING.md](../CONTRIBUTING.md) — contributor workflow and conventions

## Pipeline Overview

The compiler is a seven-stage pipeline. Each stage consumes the output of the previous one. Each stage has a single public entry point and is independently testable.

![The compiler pipeline and module map: parse, transform and resolve feed the two-pass type checker, where naming.py answers what any type expression is called for every later stage; after checking, vera verify proves each contract obligation (Tier 1) or defers it to a runtime guard (Tier 3) with a warm-verification sidecar for the LSP, while vera compile emits WAT and WASM for the wasmtime host, the browser bundle, or a WASI 0.2 component.](../assets/diagrams/architecture.svg)

<details>
<summary>Text version</summary>

```text
Source (.vera)
  |
  v
1   Parse        grammar.lark + parser.py     -> Lark parse tree (LALR(1))
2   Transform    transform.py + ast.py        -> typed AST
3   Resolve      resolver.py                  -> transitive module closure
4   Type Check   checker/ + naming.py + environment.py -> list[Diagnostic]
  |              (two passes: register every signature, then check bodies)
  |
  +--- vera verify ------------->  5  Verify   verifier.py + smt.py (Z3)
  |                                   each obligation proved (Tier 1) or
  |                                   deferred to a runtime guard (Tier 3)
  |                                   -> ok / diagnostics / tier counts
  |                                   sidecar: obligations/ + lsp/ -- warm
  |                                   incremental re-verification (LSP)
  v    vera compile / vera run
6   Compile      codegen/ + wasm/             -> WAT + .wasm
  |              monomorphize generics / insert contract guards
  +------------------------------>  Browser bundle   (--target browser)
  +------------------------------>  WASI 0.2 component (--target wasi-p2)
  v
7   Execute      runtime/ + wasmtime          vera run / test / serve

Cross-cutting: cli.py (orchestrates every stage) / errors.py (Diagnostic,
E- and W-series diagnostic codes) / formatter.py (vera fmt) /
tester.py (vera test).
naming.py answers "what is this type expression called?" once -- stages 5
and 6, tester.py and lsp/ all render slot names and State/Exn cell families
through it, never their own.
Nothing exits early -- every stage accumulates diagnostics, so an agent
gets all feedback in one pass.
```

</details>

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
| `grammar.lark` | 344 | Parse | LALR(1) grammar definition | *(consumed by Lark)* |
| `parser.py` | 191 | Parse | Lark frontend, error diagnosis | `parse()`, `parse_file()` |
| `lexical.py` | 329 | Parse | Shared lexical scanning (comment spans, blanking) | `scan_comments()`, `blank_block_comments()` |
| `transform.py` | 1,572 | Transform | Lark tree → AST transformer | `transform()` |
| `ast.py` | 917 | Transform | Frozen dataclass AST nodes, source formatting | `Program`, `Node`, `Expr`, `format_expr` |
| `types.py` | 859 | Type check | Semantic type representation | `Type`, `is_subtype()` |
| `prelude.py` | 1,115 | Type check | Standard prelude — built-in ADT and combinator injection | `inject_prelude()`, `prelude_adt_names()`, `overridable_builtin_names()` |
| `naming.py` | 857 | Type check | The ONE slot / slot-reference-key / State-Exn-family renderer (#1208, #1209) — the checker's rendering, as a total pure function over an `AliasEnv`, consumed by the checker, the monomorphizer, the verifier, the SMT layer, codegen, the tester, the LSP, and `vera check --explain-slots`.  Also the ONE refinement-binder derivation, from the type expression for codegen's runtime guard (`refinement_binder_parts`) and from the predicate's own reference for the verifier and SMT layers (`predicate_binder_key`, #1226), both rendering through `slot_name`; and each consumer is handed the env of the module that DECLARED what it is rendering | `slot_name()`, `slot_ref_key()`, `family_name()`, `resolve_type_expr()`, `AliasEnv` |
| `slots.py` | 427 | Type check | Presentation over `naming.py`: slot resolution tables and their text/JSON rendering, plus the two scope walks the tables need (`forall` narrowing, `where`-helper nesting).  The walks here that are NOT naming say so in their docstrings — the alias-opaque syntactic spelling for WASM representation questions, the last-resort name for a State/Exn cell family that resolves to none, and the bare-call ownership predicate the checker, codegen, and mono discovery all resolve a `get`/`put` call site through | `slot_table()`, `format_slot_table()`, `fn_slot_scope()`, `fn_scopes()`, `type_expr_slot_name()`, `family_fallback_name()`, `bare_call_denotes_user_fn()` |
| `environment.py` | 2,327 | Type check | Type environment, scope stacks, ability registry, all built-in registrations | `TypeEnv`, `AbilityInfo` |
| `checker/` | 7,264 | Type check | Two-pass type checker (mixin package) | `typecheck()` |
| `  core.py` | 1,165 | | TypeChecker class, orchestration, contracts, constraint validation | |
| `  resolution.py` | 535 | | AST TypeExpr → semantic Type, inference | |
| `  modules.py` | 476 | | Cross-module registration (C7b/C7c), plus the per-module body check that makes a module's diagnostics independent of which file `vera check` was given (#1244) and the #1304 refusal of a bare function, data-type or constructor name two imports both supply (E155/E156/E157) | |
| `  registration.py` | 1,032 | | Pass 1 forward declarations, ability registration | |
| `  expressions.py` | 1,485 | | Expression synthesis (bidirectional), operators, statements | |
| `  eq_ability.py` | 199 | | Eq ability derivation checks | |
| `  sql.py` | 309 | | SQL literal-provenance resolution + placeholder counting (#309) | `resolve_literal_string()`, `count_placeholders()` |
| `  calls.py` | 1,631 | | Function/constructor/module/ability calls | |
| `  control.py` | 929 | | If/match, patterns, effect handlers | |
| `resolver.py` | 332 | Resolve | Module path resolution, parse cache | `ModuleResolver` |
| `monomorphize.py` | 3,891 | Resolve | Shared generic instantiation discovery + AST substitution (verifier and codegen); each clone's De Bruijn recount renders its binder names under the **origin module's** `AliasEnv`, the one its consumers rebuild the clone's scope with (#1208) | `substitute_type_vars()`, `resolve_type_alias()`, `canonicalize_type_aliases()` |
| `smt.py` | 3,289 | Verify | Z3 translation layer; reads each callee's contract in the module that declared it (`_callee_contract_scope`), swapping the naming env its slots render against and the registry its bare-name calls resolve in as one `CalleeScope` (#1208, #1225) | `SmtContext`, `SlotEnv`, `CalleeScope` |
| `verifier.py` | 9,446 | Verify | Contract verification; owns the per-module registries every rendering goes through — an imported callee's contract and an imported generic's clone are named, resolved, and quoted in the module that **declared** them (#1208, #1220, #1225) | `verify()` |
| `wasm/` | 27,524 | Compile | WASM translation layer (package) | `WasmContext`, `WasmSlotEnv`, `StringPool` |
| ` ├ context.py` | 1,292 | | Composed WasmContext, expression dispatcher, block translation | |
| ` ├ helpers.py` | 643 | | WasmSlotEnv, StateClauseEntry, StringPool, type mapping, array element helpers | |
| ` ├ inference.py` | 2,631 | | Type inference, slot/type utilities, operator tables | |
| ` ├ operators.py` | 2,798 | | Binary/unary operators, if, quantifiers, assert/assume, old/new | |
| ` ├ calls.py` | 1,313 | | Core dispatcher for `_translate_call` / `_translate_qualified_call`, generic resolution, shared element-type inference (domain mixins below) | |
| ` ├ calls_arrays.py` | 2,694 | | `array_length` / `append` / `range` / `concat` / `slice` / `map` / `filter` / `fold` / `mapi` / `reverse` / `find` / `any` / `all` / `flatten` / `sort_by` | |
| ` ├ calls_containers.py` | 1,304 | | Map, Set, Decimal (opaque-handle types) | |
| ` ├ calls_encoding.py` | 2,210 | | Base64 and URL encoding/decoding/parsing | |
| ` ├ calls_handlers.py` | 2,513 | | Show/Hash ability dispatch, `handle[State<T>]` and `handle[Exn<E>]` | |
| ` ├ calls_markup.py` | 400 | | JSON, HTML, Markdown, Regex, async/await (#841: fused concurrent lowering for `async(Http.get/post)`, identity otherwise) | |
| ` ├ async_fusion.py` | 436 | | #841 fusion predicates — the single source of truth shared by the `_scan_io_ops` import pre-scan and the `WasmContext` async/await lowering | `fused_async_target()`, `await_needs_check()`, `compute_future_ret_fns()` |
| ` ├ calls_math.py` | 635 | | `abs`, `min`, `max`, `floor`, `ceil`, `round`, `sqrt`, `pow`, Float64 predicates, numeric conversions | |
| ` ├ calls_parsing.py` | 1,035 | | `parse_nat` / `parse_int` / `parse_bool` / `parse_float64` state machines | |
| ` ├ calls_strings.py` | 4,185 | | All string ops (length, concat, slice, search, transform, split, join, chars/lines/words, reverse, trim_start/end, pad_start/end, char_to_upper/lower, classifiers) + to-string conversions; `_translate_strip` delegates to the trim helper to keep the whitespace predicate consistent | |
| ` ├ closures.py` | 582 | | Closures, anonymous functions, free variable analysis | |
| ` ├ data.py` | 1,823 | | Constructors, match expressions (incl. nested patterns), arrays, indexing | |
| ` ├ markdown.py` | 651 | | WASM memory marshalling for MdInline/MdBlock ADTs | |
| ` ├ json_serde.py` | 631 | | WASM memory marshalling for Json ADT | |
| ` └ html_serde.py` | 261 | | WASM memory marshalling for HtmlNode ADT | |
| `markdown.py` | 728 | Compile | Python Markdown parser/renderer (§9.7.3 subset) | `parse_markdown()`, `render_markdown()`, `has_heading()`, `has_code_block()`, `extract_code_blocks()` |
| `obligations/` | 785 | Verify | Reified proof obligations + warm incremental session (#222 A/B) | `ProofObligation`, `VerificationSession` |
| `  core.py` | 198 | | ProofObligation record: identity (content_key) + discharge outcome | |
| `  cache.py` | 219 | | Invalidation keys (structural/callee/context hashes), DischargeCache | |
| `  session.py` | 311 | | Warm-Z3 daemon: per-function replay vs re-verify in declaration order | |
| `lsp/` | 1,718 | Serve | Language Server Protocol over stdio (#222 C/D/E/F) | `create_server()`, `vera lsp` |
| `  convert.py` | 218 | | Span/SourceLocation/LSP coordinate conversions, UTF-16 transcoding | |
| `  documents.py` | 69 | | URI-keyed document store, full-text sync | |
| `  features.py` | 374 | | Diagnostics + tier hints, hover, slot goto (keyed through `naming.slot_ref_key`, so parameterised and alias-spelled references resolve, and a `where` helper resolves in its own accumulated scope), hole completion | |
| `  extensions.py` | 153 | | vera/speculativeEdit proof-delta | |
| `  server.py` | 287 | | pygls wiring, single-session serialisation | |
| `  workflows.py` | 608 | | Skill-layer workflows: enforced edit sequences (#222 F) | |
| `codegen/` | 19,686 | Compile | Codegen orchestrator (mixin package) | `compile()`, `execute()` |
| `  api.py` | 1,402 | | Public API, dataclasses, `compile()`/`execute()` orchestration, core IO host bindings (#421) | |
| `  memory.py` | 105 | | Compile-time ADT layout helpers (`ConstructorLayout`, alignment) (#421) | |
| `  core.py` | 3,361 | | CodeGenerator class, orchestration, ability op rewriting (Pass 1.6), skip propagation to callers (#1100) | |
| `  modules.py` | 1,425 | | Cross-module registration + call detection (C7e), per-module alias + source scopes (#1111/#1186) — `_module_alias_scope` swaps the alias maps *and* the `AliasEnv` every codegen rendering goes through as one pair (#1208) | |
| `  registration.py` | 499 | | Pass 1 forward declarations, ADT layout | |
| `  monomorphize.py` | 1,581 | | Generic instantiation, type inference, ability constraint checking (Pass 1.5) | |
| `  functions.py` | 1,455 | | Function body compilation, GC prologue/epilogue (Pass 2) | |
| `  tail_position.py` | 106 | | Tail-position analysis for the function body compiler | |
| `  closures.py` | 1,052 | | Closure lifting, GC instrumentation | |
| `  contracts.py` | 1,337 | | Runtime pre/postconditions, old state snapshots, decreases termination guard (entry check-and-set, per-function chain state, ADT rank helpers, self-tail site checks); the refinement boundary guard derives its binder from `naming.refinement_binder_parts` and layers the erased-base skip and the nested-base E618 on top.  Also the ONE derivation of what that guard layer lowers — `_tuple_component_guard_sites` decomposes a boundary tuple for the emitter, the return-epilogue gate and the host-import pre-scan alike, and `_signature_refinement_predicates` enumerates every predicate a signature will be guarded by (#1210) | |
| `  assembly.py` | 1,502 | | WAT module assembly, `$alloc`, `$gc_collect` | |
| `  compilability.py` | 1,004 | | Compilability checks; the two host-import pre-scans (State/Exn families and IO/Markdown/Regex builtins), walking each function's body, its contract predicates and every signature the guard layer will check — including closures', cycle-guarded | |
| `  wasi.py` | 4,828 | | WASI Preview 2 component/adapter emitter — `--target wasi-p2` / `--world server` (#237, #853) | |
| `runtime/` | 5,563 | Execute | wasmtime host layer (#421): traps + per-effect host-binding families | `register_*()`, `WasmTrapError` |
| `  traps.py` | 493 | | `WasmTrapError`, `_classify_trap` / `_classify_host_error`, source-backtrace resolution | |
| `  heap.py` | 1,376 | | WASM memory marshalling primitives, ADT/Option/Array/bucket codecs, `_ShadowGuard`, shared collection helpers | |
| `  collections.py` | 16 | | `_VAL_WASM_TYPES` value-type dispatch table (shared by Map/Set) | |
| `  text.py` | 34 | | `safe_utf8_decode` — the single lossy-decode site (#592) | |
| `  <effect>.py` ×14 | 3,214 | | one `register_<effect>(linker, …)` per family: random, math, md, json, regex, html, map, set, decimal, http, async_http (#841 fused-async: worker-thread submit + blocking await + kind-4 cancel/evict decref), inference, state, db | |
| `  wasi_host.py` | 213 | | Built-in `wasi-p2` runner via `add_wasip2` — `vera run --target wasi-p2` (#237, #853) | |
| `  server.py` | 150 | | `vera serve` HTTP driver for `handle(Request -> Response)` (#305) | |
| `tester.py` | 1,285 | Test | Z3-guided input generation (parameter types resolved through `naming.py`; a TIER-3 target whose input constraints do not all translate is skipped naming the blocker rather than trialled, while a Tier-1-proved function is reported verified and never trialled at all), WASM execution, tier classification | `test()` |
| `formatter.py` | 2,036 | Format | Canonical code formatter | `format_source()` |
| `errors.py` | 813 | All | Diagnostic class, error hierarchy, error code registry | `Diagnostic`, `VeraError`, `ERROR_CODES` |
| `skip.py` | 242 | All | Codegen-internal control-flow exceptions behind structured skip diagnostics (#626) | `CodegenSkip`, `CodegenInvariantError` |
| `introspect.py` | 127 | All | Payloads for `vera builtins` / `effects` / `errors --json` | `builtins_payload()`, `effects_payload()`, `errors_payload()` |
| `envflags.py` | 35 | All | One truthiness rule for the `VERA_*` diagnostic flags catalogued in ENVIRONMENT.md; a leaf module (imports `os` only) so any layer can read a flag without a cycle | `flag_enabled()` |
| `_since.py` | 376 | All | Best-effort `since` version attribution for built-ins, effects, abilities | |
| `browser/` | 138 | Execute | Browser runtime for compiled WASM (package) | `emit_browser_bundle()` |
| ` ├ emit.py` | 137 | | Browser bundle emission (wasm + runtime + html) | `emit_browser_bundle()` |
| ` ├ runtime.mjs` | 3,877 | | Self-contained JS runtime: IO, State, Http, Inference, contracts, Markdown, Json, Html | |
| ` └ harness.mjs` | 106 | | Node.js test harness for parity testing | |
| `cli.py` | 2,224 | All | CLI commands | `main()` |
| `registration.py` | 158 | Type check | Shared function registration | `register_fn()` |

Total: ~88,000 lines of Python + 344 lines of grammar + 3,983 lines of JavaScript.

## Parsing

**Files:** `grammar.lark`, `parser.py` (sizes in the module map above)

The grammar is a Lark LALR(1) grammar derived from the formal EBNF in spec Chapter 10. It uses:

- **String literals** for keywords (`"fn"`, `"let"`, `"match"`, etc.)
- **`?rule` prefix** to inline single-child nodes (cleaner parse trees)
- **`UPPER_CASE`** for terminal rules (`INT_LIT`, `UPPER_IDENT`, etc.)
- **Precedence climbing** for operators: pipe > implies > or > and > eq > cmp > add > mul > unary > postfix

The parser is **lazily constructed and cached** — `_get_parser()` builds the Lark parser on first call and reuses it. Lark's `propagate_positions=True` attaches source locations to every tree node, which the transformer carries through to AST `Span` objects.

**Error diagnosis:** When Lark raises an `UnexpectedToken` or `UnexpectedCharacters`, `diagnose_lark_error()` pattern-matches on the expected token set to produce LLM-oriented diagnostics. For example, if the expected set includes `"requires"` but the parser got `"{"`, the diagnostic is "missing contract block" with a concrete fix showing the `requires()`/`ensures()`/`effects()` structure.

## AST

**Files:** `ast.py`, `transform.py` (sizes in the module map above)

### Node hierarchy

The AST is a shallow class hierarchy. Every node is a frozen dataclass carrying an optional source `Span`.

```
Node
├── Expr                                    Expressions
│   ├── IntLit, FloatLit, StringLit         Literals
│   ├── BoolLit, UnitLit, ArrayLit, InterpolatedString
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

**Files:** `checker/`, `naming.py`, `types.py`, `environment.py` (sizes in the module map above)

This is the most architecturally complex stage.

### Three-pass architecture

![The three checker passes: module registration harvests imported signatures, local registration populates the TypeEnv, and the checking pass verifies every function body against it.](../assets/diagrams/checker-passes.svg)

<details>
<summary>Text version</summary>

```text
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

</details>

**Why two passes:** Forward references and mutual recursion. A function declared on line 50 can call a function declared on line 10, or vice versa. Pass 1 makes all signatures visible before any bodies are checked.

### Syntactic vs semantic types

The compiler maintains two distinct type representations:

- **`ast.TypeExpr`** — what the programmer wrote. `NamedType("PosInt")`, `FnType(...)`, `RefinementType(...)`. These are AST nodes with source spans.
- **`types.Type`** — resolved canonical form. `PrimitiveType("Int")`, `AdtType("Option", (INT,))`, `FunctionType(...)`. These are semantic objects used for type compatibility.

`_resolve_type()` in the checker bridges them: it looks up type aliases, expands parameterised types, and resolves type variables from `forall` bindings.

**Why this matters:** Type aliases are **opaque at the head** of a slot name. If `type PosInt = { @Int | @Int.0 > 0 }`, then `@PosInt.0` counts `PosInt` bindings and `@Int.0` counts `Int` bindings — they are separate namespaces. But for type compatibility, `PosInt` resolves to a refined `Int` and subtypes accordingly.

A slot name's type **arguments** are the other half of the rule: they resolve in full, so under `type Cnt = Int` a parameter written `@Option<Cnt>` binds `Option<Int>` — one namespace with `@Option<Int>` — where `@Cnt` and `@Int` remain two ([spec §3.8.1](../spec/03-slot-references.md)). The head is the name the programmer chose for a binding, so leaving it opaque keeps a library's new alias from splitting a caller's namespace; an argument is a *component* of a structural type, so resolving it keeps one type from becoming two namespaces. A *refinement* alias resolves in argument position too, but to the predicate-elided `{@Int | ...}` form, which stays distinct from plain `Int`. `naming.py` implements all of it (Design Pattern 8).

### De Bruijn slot resolution

See [`DE_BRUIJN.md`](../DE_BRUIJN.md) for the conceptual background and worked examples. In brief: Vera uses typed De Bruijn indices instead of variable names. `@Int.0` means "the most recent `Int` binding", `@Int.1` means "the one before that".

![Slot resolution: parameters bind left-to-right into scope 0, a let pushes scope 1, and each Int slot reference counts backwards from the most recent Int binding.](../assets/diagrams/slot-scopes.svg)

<details>
<summary>Text version</summary>

```text
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

</details>

The resolver walks scopes **innermost to outermost**, counting backwards within each scope. This is implemented in `TypeEnv.resolve_slot()`.

Each binding tracks its **source** (`"param"`, `"let"`, `"match"`, `"handler"`, `"destruct"`) and its **canonical type name** — the name slot references match against, rendered by `naming.py`. Alias opacity applies to that name's **head** only: `@PosInt.0` never counts `Int` bindings, while a parameter written `@Option<Cnt>` under `type Cnt = Int` binds `Option<Int>` and is reached by `@Option<Int>.0` (spec §3.8.1).

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

`TypeEnv._register_builtins()` registers the built-in types and operations. Function names follow the `domain_verb` convention (see spec §9.1.1): `string_` prefix for string ops, `float_` prefix for float predicates, `source_to_target` for conversions, prefix-less for math universals only (`abs`, `min`, `max`, etc.). New built-in functions must follow these patterns.

The **standard prelude** automatically provides `Option<T>`, `Result<T, E>`, `Ordering`, and `UrlParts` in every program without explicit `data` declarations, along with Option/Result combinators and the array built-ins (including `array_length`, `array_append`, `array_range`, `array_concat`, `array_slice`, `array_map`, `array_filter`, `array_fold`, `array_mapi`, `array_reverse`, `array_find`, `array_any`, `array_all`, `array_flatten`, `array_sort_by`). User-defined `data` declarations with the same name shadow the prelude.

| Built-in | Kind | Details |
|----------|------|---------|
| `Option<T>` | ADT | `None`, `Some(T)` constructors |
| `Result<T, E>` | ADT | `Ok(T)`, `Err(E)` constructors |
| `Future<T>` | ADT | `Future(T)` constructor — WASM-transparent wrapper |
| `MdInline` | ADT | `MdText(String)`, `MdCode(String)`, `MdEmph(Array<MdInline>)`, `MdStrong(Array<MdInline>)`, `MdLink(Array<MdInline>, String)`, `MdImage(String, String)` |
| `MdBlock` | ADT | `MdParagraph(Array<MdInline>)`, `MdHeading(Nat, Array<MdInline>)`, `MdCodeBlock(String, String)`, `MdBlockQuote(Array<MdBlock>)`, `MdList(Bool, Array<Array<MdBlock>>)`, `MdThematicBreak`, `MdTable(Array<Array<Array<MdInline>>>)`, `MdDocument(Array<MdBlock>)` |
| `State<T>` | Effect | `get(Unit) → T`, `put(T) → Unit` operations |
| `IO` | Effect | `print`, `read_line`, `read_file`, `write_file`, `args`, `exit`, `get_env` |
| `Async` | Effect | No operations — marker for async computation |
| `Diverge` | Effect | No operations — marker for non-termination |
| `array_length` | Function | `forall<T> Array<T> → Int`, pure |
| `array_append` | Function | `forall<T> Array<T>, T → Array<T>`, pure |
| `array_range` | Function | `Int, Int → Array<Int>`, pure |
| `array_concat` | Function | `forall<T> Array<T>, Array<T> → Array<T>`, pure |
| `array_slice` | Function | `forall<T> Array<T>, Int, Int → Array<T>`, pure |
| `array_map` | Function | `forall<A, B> Array<A>, fn(A → B) pure → Array<B>`, pure |
| `array_filter` | Function | `forall<T> Array<T>, fn(T → Bool) pure → Array<T>`, pure |
| `array_fold` | Function | `forall<T, U> Array<T>, U, fn(U, T → U) pure → U`, pure |
| `array_mapi` | Function | `forall<A, B> Array<A>, fn(A, Nat → B) pure → Array<B>`, pure |
| `array_reverse` | Function | `forall<T> Array<T> → Array<T>`, pure |
| `array_find` | Function | `forall<T> Array<T>, fn(T → Bool) pure → Option<T>`, pure |
| `array_any` | Function | `forall<T> Array<T>, fn(T → Bool) pure → Bool`, pure |
| `array_all` | Function | `forall<T> Array<T>, fn(T → Bool) pure → Bool`, pure |
| `array_flatten` | Function | `forall<T> Array<Array<T>> → Array<T>`, pure |
| `array_sort_by` | Function | `forall<T> Array<T>, fn(T, T → Ordering) pure → Array<T>`, pure |
| `string_length` | Function | `String → Nat`, pure |
| `string_concat` | Function | `String, String → String`, pure |
| `string_slice` | Function | `String, Nat, Nat → String`, pure |
| `string_char_code` | Function | `String, Int → Nat`, pure |
| `string_from_char_code` | Function | `Nat → String`, pure |
| `string_repeat` | Function | `String, Nat → String`, pure |
| `parse_nat` | Function | `String → Result<Nat, String>`, pure |
| `parse_int` | Function | `String → Result<Int, String>`, pure |
| `parse_float64` | Function | `String → Result<Float64, String>`, pure |
| `parse_bool` | Function | `String → Result<Bool, String>`, pure |
| `base64_encode` | Function | `String → String`, pure (RFC 4648) |
| `base64_decode` | Function | `String → Result<String, String>`, pure |
| `url_encode` | Function | `String → String`, pure (RFC 3986 percent-encoding) |
| `url_decode` | Function | `String → Result<String, String>`, pure |
| `url_parse` | Function | `String → Result<UrlParts, String>`, pure (RFC 3986 decomposition) |
| `url_join` | Function | `UrlParts → String`, pure (reassemble URL) |
| `md_parse` | Function | `String → Result<MdBlock, String>`, pure (Markdown → typed AST) |
| `md_render` | Function | `MdBlock → String`, pure (typed AST → canonical Markdown) |
| `md_has_heading` | Function | `MdBlock, Nat → Bool`, pure (query heading level) |
| `md_has_code_block` | Function | `MdBlock, String → Bool`, pure (query code block language) |
| `md_extract_code_blocks` | Function | `MdBlock, String → Array<String>`, pure (extract code by language) |
| `async` | Function | `T → Future<T>`, `effects(<Async>)` (generic, eager evaluation) |
| `await` | Function | `Future<T> → T`, `effects(<Async>)` (generic, identity unwrap) |
| `to_string` | Function | `Int → String`, pure |
| `int_to_string` | Function | `Int → String`, pure (alias for `to_string`) |
| `bool_to_string` | Function | `Bool → String`, pure |
| `nat_to_string` | Function | `Nat → String`, pure |
| `byte_to_string` | Function | `Byte → String`, pure |
| `float_to_string` | Function | `Float64 → String`, pure |
| `string_strip` | Function | `String → String`, pure (zero-copy) |
| `abs` | Function | `Int → Nat`, pure |
| `min` | Function | `Int, Int → Int`, pure |
| `max` | Function | `Int, Int → Int`, pure |
| `floor` | Function | `Float64 → Int`, pure |
| `ceil` | Function | `Float64 → Int`, pure |
| `round` | Function | `Float64 → Int`, pure |
| `sqrt` | Function | `Float64 → Float64`, pure |
| `pow` | Function | `Float64, Int → Float64`, pure |
| `int_to_float` | Function | `Int → Float64`, pure |
| `float_to_int` | Function | `Float64 → Int`, pure |
| `nat_to_int` | Function | `Nat → Int`, pure |
| `int_to_nat` | Function | `Int → Option<Nat>`, pure |
| `byte_to_int` | Function | `Byte → Int`, pure |
| `int_to_byte` | Function | `Int → Option<Byte>`, pure |
| `float_is_nan` | Function | `Float64 → Bool`, pure |
| `float_is_infinite` | Function | `Float64 → Bool`, pure |
| `nan` | Function | `→ Float64`, pure |
| `infinity` | Function | `→ Float64`, pure |
| `string_contains` | Function | `String, String → Bool`, pure |
| `string_starts_with` | Function | `String, String → Bool`, pure |
| `string_ends_with` | Function | `String, String → Bool`, pure |
| `string_index_of` | Function | `String, String → Option<Nat>`, pure |
| `string_upper` | Function | `String → String`, pure |
| `string_lower` | Function | `String → String`, pure |
| `string_replace` | Function | `String, String, String → String`, pure |
| `string_split` | Function | `String, String → Array<String>`, pure |
| `string_join` | Function | `Array<String>, String → String`, pure |

Additionally, `resume` is bound as a temporary function inside handler clause bodies (in `_check_handle()`). Its type is derived from the operation: for `op(params) → ReturnType`, `resume` has type `fn(ReturnType) → Unit effects(pure)`. The binding is added to `env.functions` before checking the clause body and removed afterward.

## Contract Verification

**Files:** `verifier.py`, `smt.py` (sizes in the module map above)

### Tiered model

The spec defines three verification tiers. The compiler implements Tiers 1 and 3:

| Tier | What | How | Status |
|------|------|-----|--------|
| **1** | Decidable fragment: QF_LIA + Booleans + comparisons + if/else + let + match + constructors + `array_length` + decreases | Z3 proves automatically | Implemented |
| **2** | Extended: quantifiers, function call reasoning, array access | Z3 with hints/timeouts | Future |
| **3** | Everything else | Runtime assertion fallback | Warning emitted |

When a contract or function body contains constructs that can't be translated to Z3, the verifier **does not error** — it classifies the contract as Tier 3 and emits a warning. This means every valid program can be verified (at least partially).

### Verification condition generation

![Proof by refutation: the requires clauses become assumptions, the negated ensures becomes the goal, and Z3's unsat/sat/unknown answers map to Verified, Violated-with-counterexample, and Tier 3.](../assets/diagrams/z3-refutation.svg)

<details>
<summary>Text version</summary>

```text
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

</details>

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
| `array_length(arr)` | Uninterpreted function, constrained `>= 0` |
| `abs(x)` | `z3.If(x >= 0, x, -x)` |
| `min(a, b)` | `z3.If(a <= b, a, b)` |
| `max(a, b)` | `z3.If(a >= b, a, b)` |
| `nat_to_int(x)` | Identity (both IntSort) |
| `byte_to_int(x)` | Identity (both IntSort) |
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

**Files:** `codegen/`, `wasm/` (split into domain mixins; sizes and the mixin split in the module map above)

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

`IO.print` compiles to a call to an imported host function. The `execute()` function in `codegen/api.py` provides the host implementation via wasmtime's `Linker`: it reads UTF-8 bytes from WASM linear memory and writes to stdout (or a capture buffer for testing). The IO host functions stay inline in `execute()` — unlike the other effects, which are factored into `vera/runtime/`. See **Host-binding families** below for the rationale.

### Host-binding families (`vera/runtime/`)

Before #421, `execute()` and every effect's host bindings lived in one ~4,358-line `codegen/api.py`. The wasmtime host layer is now factored into `vera/runtime/`: trap classification (`traps.py`), WASM memory marshalling (`heap.py`, `collections.py`), and **one module per optional effect family**, each exposing a single `register_<family>(linker, …)` that defines and registers its host callbacks. `execute()` calls these in sequence instead of inlining ~3,000 lines of branches. The compiled `.wasm` import interface is unchanged — this is an internal refactor, not a contract change.

![The wasmtime host layer: execute() registers one pluggable adapter per optional effect family into the Linker — Decimal, State, and the fused Async adapter carry an explicit store — while IO stays inline as execute()'s observation channel; the module's import interface is the portability contract the browser runtime also implements.](../assets/diagrams/host-families.svg)

**What counts as a "family" module.** Each of the fourteen (`random`, `math`, `md`, `json`, `regex`, `html`, `map`, `set`, `decimal`, `http`, `async_http`, `inference`, `state`, `db`) is a *pluggable adapter* with minimal coupling to `execute()`. Map/Set/Decimal marshal opaque handles; Json/Html/Markdown/Regex bridge Python parsers; Http/Inference wrap network calls; Db opens one connection per run, captured by its op closures; Random/Math/State are thin shims. Most are stateless and registered conditionally (`if result.<effect>_ops_used`). The three stateful ones — Decimal, State, and the fused Async adapter — keep a single Python-side store that `execute()` creates and reads back (Decimal's handle store feeds the GC decref hook and `host_store_sizes`; State's cell stacks feed `ExecuteResult.state`; `async_http.py`'s `register_async` takes the `future_store` `execute()` builds up-front, publishes it as `host_store_refs["future"]` so it too reaches `host_store_sizes`, and has its entries evicted by the same `host_decref_handle` — kind 4, which also cancels a future that never started, #841), passed as one explicit parameter (e.g. `register_decimal(linker, ops, decimal_store, host_store_refs)`), keeping each family a clean unit. `heap.py` holds the marshalling primitives they all call.

**Why IO is *not* a family module.** IO stays inline in `execute()` by design. Unlike the fourteen adapters, IO is execute()'s **observation channel**: its host callbacks write into state that *becomes the return value* — `output_buf`/`stderr_buf` → `ExecuteResult.stdout`/`stderr`, `last_violation` → the trap diagnostic via `_classify_trap`, `tee_stdout` → the live-streaming decision — and it shares the `_VeraExit` Ctrl-C exception with execute()'s exit handling. Extracting the fourteen adapters *reduced* coupling (each became self-contained); extracting IO would not — it would relocate a naturally cohesive unit across a file boundary behind a 7-field context object that both the host callbacks and the result-building code would thread through. Cohesion of a genuinely-coupled unit outweighs uniform "every effect lives in `runtime/`" placement. (By Vera's *surface* model IO is an effect like any other; by the *compiler's* internal structure it is execute()'s I/O substrate. The decomposition follows the compiler's structure — the principle that each module be a cohesive, independently-testable unit.)

### Markdown host bindings

`markdown.py` implements a hand-written Python Markdown parser and renderer (§9.7.3 subset). This is the **first set of pure functions implemented as host bindings** rather than inline WASM. The architectural rationale:

- Markdown parsing is too complex for inline WASM (recursive tree construction, regex-based tokenization)
- Functions are genuinely pure (deterministic, referentially transparent) — the host implementation is part of the trusted computing base
- No external dependency — the parser handles ATX headings, fenced code blocks, paragraphs, lists, block quotes, GFM tables, thematic breaks, and inline formatting (emphasis, strong, code, links, images)

`wasm/markdown.py` provides bidirectional WASM memory marshalling for the `MdInline` and `MdBlock` ADT trees. Write direction (`write_md_inline`, `write_md_block`) allocates ADT nodes in WASM linear memory using the same `$alloc` + tag-dispatch layout as user-defined ADTs. Read direction (`read_md_inline`, `read_md_block`) reconstructs Python objects from WASM memory. Helper functions `_read_i32`, `_read_i64`, and `_write_i64` handle raw memory access for struct fields.

The WASM import interface is the portability contract: the compiled `.wasm` binary declares `(import "vera" "md_parse" ...)` etc., and any host runtime provides matching implementations. The Python implementation in `api.py` is the reference; the browser runtime in `browser/runtime.mjs` provides JavaScript host bindings with the same WASM memory allocation protocol.

### Browser runtime

`browser/runtime.mjs` is a self-contained JavaScript runtime (~3,877 lines) that provides JavaScript implementations of all Vera host bindings. It works with any core Vera `.wasm` module — the default and browser targets share one import ABI, so no code generation is needed; the `--target wasi-p2` component is a different artifact format with its own host.

**Dynamic import introspection:** Instead of generating per-program glue code, the runtime uses `WebAssembly.Module.imports(module)` at initialization to discover which host functions the module actually needs, then builds the import object dynamically. State\<T\> types are pattern-matched from `state_get_*`/`state_put_*` import names.

**Browser adaptations:** IO operations have browser-appropriate implementations. `IO.print` captures output in a buffer (flushed via `getStdout()`). `IO.read_line` reads from a pre-queued input array or falls back to `prompt()`. File IO returns `Result.Err("File I/O not available in browser")`. `IO.exit` throws a `VeraExit` error. `Inference.complete` returns `Result.Err(...)` with an explanation — embedding API keys in client-side JavaScript exposes them in page source and network requests; the recommended pattern is a server-side proxy called via the `Http` effect.

**Bundled Markdown parser:** The runtime includes a JavaScript Markdown parser (~400 lines, bundled inline) matching the Python §9.7.3 subset. Zero external dependencies.

**GC reachability discipline (JS host side):** JS host functions that allocate multiple WASM heap blocks and hold intermediates in JS locals must root those intermediates on the shadow stack — otherwise EAGER_GC (and, under pressure, normal GC) reclaims them mid-walk. The runtime exports two helpers: `gcShadowPush(ptr)` writes a pointer to `$gc_sp` and advances it (throws if `$gc_sp` / `$gc_stack_limit` aren't exported, since that means the module was built without GC support but is calling allocators that can trigger GC), and `gcGuard(fn)` saves `$gc_sp` at entry and restores it on exit (success or exception). This is the browser parallel of the CLI-side `_ShadowGuard` context manager added in v0.0.158 (#692). The walkers `writeJson` / `writeHtml` and the parsers `json_parse` / `html_parse` wrap their bodies in `gcGuard` and push intermediates (`arrPtr`, `wrapperPtr`, `jsonPtr`) as soon as each is allocated — see `runtime.mjs` for the canonical pattern. Without this, `Map<K, Json>` / `Set<Json>` and similar heap-pointer-keyed collections drop values under GC pressure (#708).

**Parity enforcement:** `tests/test_browser.py` runs the examples the browser target can execute — two explicit lists in that file, not the whole `examples/` directory, since an example that reads stdin interactively, uses a refused host family (file IO, `DB`), or does not compile standalone cannot be compared — plus per-binding batteries over the Map/Set/Decimal/Json/Regex/Markdown host imports, through both Python/wasmtime and Node.js/JS-runtime. The two example lists carry different oracles: the examples exporting `main` are run and compared on stdout, while the ones reached as exported functions are called with fixed arguments and compared on the returned value. The per-binding batteries compare stdout. `json_stringify` and `md_render` are compared the same way and additionally against the canonical form the specification states for each (§9.7.1, §9.7.3), because cross-host equality alone would be satisfied by two hosts agreeing on a wrong answer; `md_render` is also asserted stable under re-render and exercised on `MdBlock` values the test *builds*, since several renderer rules are unreachable through `md_parse`, and `json_stringify`'s number rendering is checked differentially against a real `JSON.stringify`. `json_parse` is compared by accepted domain, the parse-side counterpart: §9.7.1 states the domain — RFC 8259-valid text that decodes to finite numbers and strings of Unicode scalar values — and the battery compares the whole `Err` message across hosts for the JavaScript constants, for a number that overflows to an infinity in either spelling — with an exponent (`1e999`) or as plain digits (`1` followed by 309 zeros, the route `json.loads` decodes to an `int`) — and for a lone-surrogate escape, parameterised over every position a string can occupy (value, key, array element, nested), beside controls the refusals must not disturb: matched surrogate pairs, `"NaN"` as an ordinary string value, the finite boundary values, underflow to `0`, and the band between the largest finite double and the rounding boundary, whose integers are larger than `sys.float_info.max` and still accepted by both hosts. `md_parse` is the one parser still diverging — plain-text run grouping inside a paragraph, and a handful of block markers §9.7.3 does not pin — tracked as [#1301](https://github.com/aallan/vera/issues/1301); for it the suite pins the inputs the two do agree on. The browser stubs are covered on two different shapes: `IO.read_file` and `IO.write_file` get the same per-host pinning, run through both runtimes against a path that really is readable or writable so the native `Ok` and the browser `Err` are each asserted (a missing file or an unwritable directory would `Err` on both sides and prove nothing), while `IO.read_char` is exercised in Node alone — the module links and the stub's `Err` arm returns `0` — with no native run to compare against. `Inference` and `DB` return `Err` from every browser operation, which is a deliberate platform boundary — the credentials they need would be readable from page source — rather than a divergence awaiting a fix. Pre-commit hooks and CI trigger these tests on any change to the host binding surface.

`browser/emit.py` provides `emit_browser_bundle()` for the `vera compile --target browser` CLI command, which produces a ready-to-serve directory (module.wasm + vera-runtime.mjs + index.html).

### Runtime contracts

The code generator does **not** consult the verifier: `vera compile` emits the module — with its contract guards — whether or not `vera verify` ever ran. Tier classification is `vera verify`'s *reporting*, not a codegen input:
- **Trivial (`requires(true)`, `ensures(true)`):** omitted — recognised syntactically, no meaningful check
- **Everything else:** compiled as runtime assertions using `unreachable` traps, whether Z3 proved it (Tier 1) or deferred it (Tier 3)

Omitting statically-proven guards is the spec §11.8 aspiration tracked in [#958](https://github.com/aallan/vera/issues/958) — it must wait on the soundness guarantees noted there.

Preconditions are checked at function entry. Postconditions store the return value in a temporary local, check the condition, and trap or return.

**Informative violation messages:** Before each `unreachable`, the codegen emits a call to the `vera.contract_fail` host import with a pre-interned message string describing which contract failed (function name, contract kind, expression text). The host callback stores the message; when the trap is caught, `execute()` raises a `RuntimeError` with the stored message instead of a raw WASM trap. `format_expr()` and `format_fn_signature()` in `ast.py` reconstruct source text from AST nodes for the message.

### Memory management

Memory is managed automatically. The allocator and garbage collector are implemented entirely in WASM — no host-side GC logic.

**Memory layout** (when the program allocates):

```
[0, data_end)            String constants (data section)
[data_end, +16K)         GC shadow stack (4096 root slots)
[data_end+16K, +32K)     GC mark worklist (4096 entries)
[data_end+32K, ...)      Heap (objects with 4-byte headers)
```

**Allocator** (`$alloc` in `assembly.py`): Bump allocator with free-list overlay. Each allocation prepends a 4-byte header (`mark_bit | size << 1`). Allocation tries free-list first-fit, then bump, triggers GC on OOM, falls back to `memory.grow`.

**Garbage collector** (`$gc_collect` in `assembly.py`): Conservative mark-sweep in three phases:
1. **Clear** — walk heap linearly, clear all mark bits
2. **Mark** — seed worklist from shadow stack roots, drain iteratively; any i32 word that looks like a valid heap pointer (in heap range, properly aligned, below `$heap_ptr`) is treated as one (no type descriptors needed). Because those guards don't prove the word at `val - 4` is actually an object header, the marker also bounds the conservative scan against `$heap_ptr` at two layers — early-skip if `obj_ptr + obj_size > heap_ptr` before marking, plus a per-iteration check inside the scan loop — so a non-pointer payload value that happens to satisfy the seeding guards (e.g. a bit-packed `Nat` row) cannot cause the collector to walk past the heap and trap (#515)
3. **Sweep** — walk heap, link unmarked objects into free list

**Shadow stack** (`gc_shadow_push` in `helpers.py`): WASM has no stack scanning, so the compiler pushes live heap pointers explicitly. `_compile_fn` in `functions.py` emits a prologue (save `$gc_sp`, push pointer params) and epilogue (save return, restore `$gc_sp`, push return back). Allocation sites in `data.py`, `closures.py`, and `calls.py` push newly allocated pointers after each `call $alloc`. A `match` applies that same save/restore/re-root discipline to its own extent (`_scope_match_shadow_roots` in `data.py`), so an arm's roots are reclaimed when the arm produces its value rather than at frame exit; the shadow stack roots ADDRESSES, so a copy of a pointer the producer already rooted is not pushed again (#1322). An overflow guard (`$gc_sp + 4 > $gc_stack_limit` — slot-complete, since the store writes four bytes) traps if the shadow stack would overflow into the worklist region — this prevents silent GC corruption during deep recursion (#464, #791, #860).

**Zero overhead:** The GC infrastructure (globals, shadow stack, worklist, `$gc_collect`) is only emitted when `needs_alloc` is True. Programs that perform no heap allocation have no GC overhead.

## Error System

**File:** `errors.py` (803 lines)

```
VeraError (exception hierarchy)
├── ParseError       ← raised, stops pipeline
├── TransformError   ← raised, stops pipeline
├── TypeError        ← accumulated as Diagnostic, never raised
└── VerifyError      ← accumulated as Diagnostic, never raised
```

Every diagnostic includes eight fields designed for LLM consumption:

![The Diagnostic record: description, location, source line, rationale, fix, spec_ref, severity, and a stable error code.](../assets/diagrams/diagnostic-card.svg)

<details>
<summary>Text version</summary>

```text
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

</details>

`Diagnostic.format()` produces the multi-section natural language output shown in the root README's "What Errors Look Like" section. The format is designed so the compiler's output can be fed directly back to the model that wrote the code.

**Parse error patterns:** `diagnose_lark_error()` in `parser.py` maps common Lark exception patterns to specific diagnostics. It checks expected token sets to distinguish "missing contract block" from "missing effects clause" from "malformed slot reference", producing targeted fix suggestions for each.

## Design Patterns

These patterns pervade the codebase. Understanding them makes the code easier to navigate.

### 1. Frozen dataclasses

All AST nodes, type objects, and environment data structures are frozen dataclasses. Fields use tuples, not lists. Compiler phases never mutate their input — they produce new data or collect diagnostics. This prevents accidental state sharing between phases and makes reasoning about data flow straightforward.

### 2. Syntactic vs semantic type separation

`ast.TypeExpr` nodes represent what the programmer wrote. `types.Type` objects represent the resolved canonical form. The `_resolve_type()` method in the checker bridges them. This distinction is what makes **head opacity** expressible: `@PosInt.0` matches `PosInt` bindings syntactically, while `PosInt` resolves to `Int` semantically for type compatibility. The bridge is crossed *within* a single slot name too — a name's head stays syntactic while its type arguments are resolved and rendered from the semantic side ([spec §3.8.1](../spec/03-slot-references.md)), which is why one renderer owns both halves (Design Pattern 8).

### 3. Error accumulation

The type checker and verifier never stop at the first error. All diagnostics are collected and returned at once. `UnknownType` propagates silently through expressions to prevent cascading — one wrong type won't generate ten downstream errors. This is critical for LLM workflows where the model needs all feedback in a single pass.

### 4. Tiered verification with graceful degradation

`SmtContext.translate_expr()` returns `None` for any construct it can't handle. The verifier interprets `None` as "Tier 3: warn and assume runtime check". This means an untranslatable CONTRACT never fails verification — a predicate Z3 cannot prove gets a warning and a runtime guard, not an error. It is a statement about the SMT translation, not a blanket guarantee that verification accepts every type-checking program: a program can still be refused for something verification must know before it can tier anything, and `E622` is that shape — a generic call whose type argument no walker could name has no determined specialisation to verify, so it is refused rather than tiered against a guess. As the SMT translation grows (Tier 2, quantifiers, etc.), constructs graduate from Tier 3 to Tier 1.

The same pattern applies to code generation: `WasmContext.translate_expr()` returns `None` for unsupported expressions, and the code generator skips those functions with a warning. As codegen support grows, more functions become compilable.

### 5. Lark Transformer bottom-up

Methods in `transform.py` are named after grammar rules and receive already-transformed children. Sentinel types (`_ForallVars`, `_Signature`, `_TypeParams`, `_WhereFns`) carry intermediate results between grammar rules during transformation but are never part of the exported AST. The `__default__()` method catches any unhandled grammar rule and raises `TransformError`.

### 6. Effect row infrastructure

The type system includes open effect rows (`row_var` field in `ConcreteEffectRow`) for row polymorphism (`forall<E> fn(...) effects(<E>)`). Effect checking enforces subeffecting (Spec Section 7.8): `effects(pure) <: effects(<IO>) <: effects(<IO, State<Int>>)`. A function can only be called from a context whose effect row contains all of the callee's effects (`is_effect_subtype` in `types.py`, call-site check in `checker/calls.py`, error code E125). Handlers discharge their declared effect by temporarily adding it to the context. Row variable unification for `forall<E>` polymorphism is permissive; full bidirectional type checking is not yet implemented.

### 7. De Bruijn indices and monomorphization

De Bruijn slot references and generic monomorphization interact non-trivially. When type-variable substitution merges formerly separate slot namespaces — distinct vars collapsing to one concrete type (`A→Int, B→Int`), or a var's namespace merging with an already-concrete one (a body `let @Int` next to `@A.0` at `A=Int`) — De Bruijn indices must be recomputed. The `_compute_scoped_reindex` walker in `monomorphize.py` (#769) resolves every `SlotRef` against the full binding scope at its reference site (parameters, `let`/destructuring bindings, match-arm binders, closure parameters, handler clauses — with contracts as a params-only scope, and every binder name rendered by `naming.slot_name` against the clone's **origin module** `AliasEnv`, narrowed by the `forall` variables in scope on each side of the recount) and computes its index in the collapsed namespace, so `@Array<Option<A>>.0` correctly becomes `@Array<Option<Int>>.1` even when the shift depends on bindings the parameter list alone cannot see. Without this, the monomorphized clone silently reads the wrong slot — a correctness bug that compiles, verifies, and runs but produces wrong results (both consumers share the substitution, so verify and codegen agree on the wrong answer).

The WASM type inference system (`inference.py`) must also handle all expression types that can appear as arguments to builtins. Missing cases (e.g. `IndexExpr`, `IfExpr`, `apply_fn` calls) return `None`, which cascades to E602 (unsupported expressions) or incorrect type inference. When adding new builtins or inference paths, check `_infer_vera_type`, `_infer_fncall_vera_type`, and `_infer_expr_wasm_type` for completeness.

### 8. One renderer for slot names

"What is the name of this type expression?" was answered independently by six subsystems, and they disagreed about aliases. A name minted one way and looked up another misses silently, and the miss reads as "not statically known" — a dangling `E699`, a false Tier 1, a split `State` cell (#1208, #1209). `naming.py` is the single answer, as a total pure function of an `AliasEnv`.

**The rule is the checker's rendering**, because the binding table is keyed by it: a slot name's head is syntactic (`@PosInt` renders `PosInt`, never `Int`), its type arguments are fully resolved (`@Option<MyAlias>` renders `Option<Int>`), a refinement renders its base at top level and the elided `{@Int | ...}` form in argument position, a function type renders `Fn` at top level and its full `fn(...) effects(...)` spelling (effect row sorted) in argument position, and nothing is unnameable — an unresolvable expression renders `?`, matching the checker's `UnknownType`. `family_name` is the one deliberate divergence: a `State`/`Exn` family names a *cell*, not a spelling, so its head resolves too, and the resolution renders through `types.structural_type_key` rather than `pretty_type` — the same discriminating key the checker orders effect rows by, because `pretty_type`'s two elisions (a refinement's predicate, a type variable's built-in marker) would merge cells the checker keeps apart (#1218, #1219). What is left over is `family_fallback_name`, for a type expression with no cell to name at all — one resolving to a bare function type, one that does not resolve — and both are refused downstream before a cell exists, so naming them by spelling can only split what is already rejected.

**The environment is the other half of the contract, and getting it wrong fails just as silently.** An `AliasEnv` is module-scoped (spec §8.4.1), so every consumer renders against the env of the module that **declared** the enclosing function, narrowed by that function's `forall` variables (`slots.fn_slot_scope` — they shadow same-named module aliases): codegen through `_module_alias_scope`, the monomorphizer against each clone's origin module, the verifier from its own per-module registration, so an imported callee's contract is rendered in *its* namespace rather than the importer's. Rendering against a neighbouring module's namespace is the same failure as rendering with a different renderer.

Two derivations stay behind in `slots.py`, and both are about a type's **representation** rather than its name: `type_expr_slot_name` (the alias-opaque spelling the WASM width/erasure walks and the structural-`Eq` derivability oracle want) and `family_fallback_name` (the last-resort name for a family whose type expression resolves to none). `slots.py` is otherwise presentation — the tables `--explain-slots`, the LSP, and the verifier read — plus two shared predicates the subsystems consult rather than restate: `fn_slot_scope`, the `forall`-narrowing scope helper the tester and the monomorphizer import so their slot scopes narrow exactly the way the checker's do, and `bare_call_denotes_user_fn` (#1284), which answers whether a bare effect-operation call site denotes a user declaration or the operation — for every such name, the built-in `get`, `put` and `throw` among them. The second exists for the same reason the first does: the checker resolves user-fn-first, and codegen's two op-registry sites and mono discovery each used to decide it themselves — the declared-effect row withheld the op when a function owned the name, the handler expression did not, and a `fn get` called under a `handle[State<T>]` compiled to the host cell intrinsic the checker had never typed.

The proof that the two sides agree is a differential, not a unit test: `tests/test_slot_naming_differential.py` instruments the checker's naming entry points, sweeps the whole `.vera` corpus plus a targeted battery, and requires zero divergence between the module's answer and a test-local statement of the rule.

### 9. LLM-oriented diagnostics

Every diagnostic includes a description (what went wrong), rationale (which language rule), fix (corrected code), spec reference, and a stable code — errors `E001`–`E702`, warnings `W001` (typed holes) and `W002` (an eagerly evaluated `async` argument). The compiler's output is designed to be fed directly back to the model as corrective context. See spec Chapter 0, Section 0.5 "Diagnostics as Instructions" for the philosophy.

### 10. Stable error code taxonomy

Every diagnostic has a unique code grouped by compiler phase:

| Range | Phase | Source |
|-------|-------|--------|
| E001–E008 | Parse | `errors.py` factory functions |
| E009 | Transform: string escapes | `transform.py` |
| E010 | Transform: unhandled rule | `transform.py` |
| E020, E021, E023 | Parse: malformed comments (lexical) | `lexical.py` scan + `errors.py` factory |
| E030, E031 | Parse: `old()`/`new()` applied to an expression | `errors.py` factory |
| E1xx | Type check: core + expressions | `checker/core.py`, `checker/expressions.py` |
| E2xx | Type check: calls | `checker/calls.py` |
| E3xx | Type check: control flow | `checker/control.py` |
| E5xx | Verification | `verifier.py` |
| E6xx | Codegen | `codegen/` |

The `ERROR_CODES` dict in `errors.py` maps every code to a short description (163 entries — 161 `E` codes and the two `W` warning codes). Codes are stable across versions — they can be used for programmatic filtering, suppression, and documentation lookups. Formatted output shows the code in brackets: `[E130] Error at line 5, column 3:`.

## Test Suite

Testing spans a **pytest suite** of 12,454 tests across 186 files: compiler-internals unit tests plus a **conformance suite** (247 programs in `tests/conformance/` validating every language feature against the spec) and **example programs** (43 end-to-end demos). The conformance suite is the definitive specification artifact; most programs target a single feature, though some (slot references, match, contracts) span several, and each serves as a minimal working example.

See **[TESTING.md](../TESTING.md)** for the comprehensive testing reference -- test file table, conformance suite details, compiler code coverage, language feature coverage, helper conventions, validation scripts, CI pipeline, and guidelines for adding tests.

## Current Limitations

Honest inventory of what the compiler cannot do, and where each limitation is addressed in the roadmap.

| Limitation | Why | Planned |
|-----------|-----|---------|
| **Verification gaps that downgrade silently** | the effect-operation argument, the generic-instantiated constructor field, the `nat_to_int`/`nat_to_string` conversion-builtin arguments, and the *refined* nested constructor sub-pattern (#765; the `@Nat` nested bind is guarded) have no codegen runtime guard, so an unverified compile can store a negative `@Nat` at one of those sites — or, at the refined nested bind, a value violating its refinement predicate (the E506 disclosure) — every other narrowing **binding site** and the top-level/where-helper and closure **return** positions — nested closures included — are statically obligated (#552, #747, #758, #984, #985) and codegen-guarded | [#754](https://github.com/aallan/vera/issues/754), [#757](https://github.com/aallan/vera/issues/757) |
| **No effect row variable unification** | Subeffecting implemented; `forall<E>` row variables permissive (full row-variable unification deferred) | [#294](https://github.com/aallan/vera/issues/294) |
| **No incremental compilation** | Full file processed from scratch each time | [#56](https://github.com/aallan/vera/issues/56) |
| **No REPL** | No interactive evaluation; all code must be written to files | [#224](https://github.com/aallan/vera/issues/224) |
| **No date/time, crypto, CSV** | Standard library limited to core types, strings, and arrays | [#233](https://github.com/aallan/vera/issues/233), [#235](https://github.com/aallan/vera/issues/235), [#236](https://github.com/aallan/vera/issues/236) |
| **Http: GET/POST only** | No custom headers, no PUT/DELETE/PATCH, no status codes, no timeouts, no streaming, no cookies | [#351](https://github.com/aallan/vera/issues/351)–[#356](https://github.com/aallan/vera/issues/356) |
| **Inference: complete only** | No `embed` (vector embeddings), no streaming, no system prompt; `embed` blocked on [#373](https://github.com/aallan/vera/issues/373) (float array host-alloc infrastructure) | [#371](https://github.com/aallan/vera/issues/371) |
| **No float array host-alloc** | Host functions cannot return `Array<Float64>`; `_alloc_result_ok_float_array` helper not yet implemented | [#373](https://github.com/aallan/vera/issues/373) |
| **Inference: no token/temperature controls** | `max_tokens` hardcoded to 1024 for Anthropic; no temperature override | [#370](https://github.com/aallan/vera/issues/370) |
| **Inference: no user handlers** | `handle[Inference]` blocks not supported; host-backed only in this release | [#372](https://github.com/aallan/vera/issues/372) |
| **Partial WASI support** | The experimental `--target wasi-p2` routes IO/clocks/random through standard component interfaces and `--world server` serves `wasi:http`, but the surface is IO + Random only — Http and every other host family are rejected under wasi-p2, and the default `wasm` target still uses ad-hoc `vera.*` host imports | [#853](https://github.com/aallan/vera/issues/853) |
| **No resource limits** | No built-in fuel, memory, or timeout controls for untrusted code | [#239](https://github.com/aallan/vera/issues/239) |
| **Browser target: `IO.sleep` freezes the tab** | Busy-waits the main thread instead of yielding to the event loop; the JSPI-based suspend/resume fix needs no language change | [#609](https://github.com/aallan/vera/issues/609) |
| **Browser target: ANSI escapes render as literal text** | No escape-sequence interpretation in `runtime.mjs`; a minimal ANSI-subset interpreter closes it without a language change | [#610](https://github.com/aallan/vera/issues/610) |

## Extending the Compiler

Practical recipes for common extensions.

### New AST node

1. Add a frozen dataclass to `ast.py` under the appropriate category base (`Expr`, `Stmt`, etc.)
2. Add a grammar rule to `grammar.lark`
3. Add a transformer method to `transform.py` with the same name as the grammar rule
4. The transformer method receives already-transformed children and returns the new node
5. **If you added a new `Expr` subclass**: every walker function carrying a `# WALKER_COVERAGE:` checklist comment must be updated to either add an `isinstance` branch or document a disposition (Handled / Intentionally ignored / Cannot occur) for the new subclass.  The pre-commit hook `walker-coverage` (which runs `scripts/check_walker_coverage.py`) enforces this and will reject the commit if any walker is incomplete.  See the section "Walker-completeness convention" below.

### Walker-completeness convention

Several functions in the compiler dispatch on `Expr` subclasses via `isinstance(expr, ast.X)` chains.  Historical bugs in this codebase (`#588`, `#604`, `#559`, `#648`) all had the same shape: a walker handled N of the N+1 subclasses, the missing case fell through to the default (`None` / `False` / no-op), and the enclosing function silently produced wrong output.  The walker-coverage convention (introduced by `#597`) prevents the bug class by making "did you handle every subclass?" a mechanically checkable contract.

Every walker function carries a `# WALKER_COVERAGE:` checklist comment listing every `Expr` subclass with one of four dispositions:

- **Handled** — explicit `isinstance` branch in the walker body.
- **Intentionally ignored** — default fall-through is correct (e.g. literals in a sub-expression-recursing walker: literals have no sub-exprs).
- **Cannot occur** — structurally impossible (e.g. `OldExpr` in a body-only walker; `HoleExpr` post-typecheck).
- **MISSING** — open bug, branch should exist but does not yet.  Filed as a separate issue.

`scripts/check_walker_coverage.py` parses each walker's `isinstance(expr, ast.X)` calls AND its `# WALKER_COVERAGE:` checklist text, then verifies the union covers every `Expr` subclass declared in `vera/ast.py`.  Wired into pre-commit, so a new `Expr` subclass added to `ast.py` forces every walker to either handle it or explicitly document its disposition.

The script is intentionally permissive about disposition text — it only enforces *coverage*, not correctness of the chosen disposition.  Disposition correctness is human-reviewer territory.

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

`pytest`, `pytest-cov` (testing), `mypy` (strict type checking), `pre-commit` (commit hooks).

---

**See also:** [Project README](../README.md) · [Language spec](../spec/) · [SKILL.md](../SKILL.md) · [CONTRIBUTING.md](../CONTRIBUTING.md) · [VeraBench](https://github.com/aallan/vera-bench)
