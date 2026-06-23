# Testing

This is the single source of truth for Vera's testing infrastructure, coverage data, and test conventions.

## Overview

| Metric | Value |
|--------|-------|
| **Tests** | 4,738 across 38 files (~61,300 lines of test code; 4,706 passed + 16 stress, 16 skipped) |
| **Compiler code coverage** | 95% Python, 61% JavaScript — 91% combined (CI minimum: 80%) |
| **Conformance programs** | 92 programs across 9 spec chapters, validating every language feature |
| **Example programs** | 35, all validated through `vera check` + `vera verify` |
| **Spec code blocks** | 164 parseable blocks from 13 spec chapters: 86 parse, 72 type-check, 71 verify |
| **README code blocks** | 13 Vera blocks (12 validated, 1 allowlisted future syntax) |
| **FAQ code blocks** | 1 Vera block in FAQ.md (0 validated, 1 allowlisted snippet) |
| **HTML code blocks** | 4 Vera blocks in docs/index.html (4 validated: parse + check + verify) |
| **Contract verification** | 256 of 280 contracts (91.4%) verified statically (Tier 1) |
| **CI matrix** | 12 combinations (Python 3.11/3.12/3.13 × ubuntu-latest/macos-15/macos-26/windows-latest) + browser parity (Node.js 22) + wheel-availability preflight |

## Running Tests

All commands assume the virtual environment is active (`source .venv/bin/activate`).

```bash
# Test suite
pytest tests/ -v                                     # full suite, verbose
pytest tests/test_codegen.py                         # single file
pytest tests/test_codegen.py::TestArithmetic          # single class
pytest tests/test_conformance.py -v                  # conformance suite only
pytest tests/ --cov=vera --cov-report=term-missing   # with coverage

# JavaScript coverage (browser runtime)
VERA_JS_COVERAGE=1 pytest tests/test_browser.py -v  # V8 coverage via c8

# GC-rooting diagnostic (forces $gc_collect on every alloc, see ENVIRONMENT.md)
VERA_EAGER_GC=1 pytest tests/test_codegen_closures.py::TestClosureReturnShadowPushBalance -v

# Type checking
mypy vera/                                           # strict mode

# Validation scripts
python scripts/check_conformance.py                  # conformance suite (92 programs, see manifest.json)
python scripts/check_examples.py                     # 35 example programs
python scripts/check_spec_examples.py                # spec code blocks
python scripts/check_readme_examples.py              # README code blocks
python scripts/check_skill_examples.py               # SKILL.md code blocks
python scripts/check_faq_examples.py                 # FAQ.md code blocks
python scripts/check_html_examples.py               # docs/index.html code blocks
python scripts/check_version_sync.py                 # version consistency
python scripts/check_wheel_availability.py           # pre-flight: every runtime dep has wheels for all supported platforms (#691 backstop)
python scripts/fix_allowlists.py --fix               # auto-fix stale allowlists
```

## Test Files

| File | Tests | Lines | What it covers |
|------|------:|------:|----------------|
| `test_parser.py` | 129 | 968 | Grammar rules, operator precedence, parse errors |
| `test_ast.py` | 128 | 1,122 | AST transformation, node structure, serialisation, string escape sequences, ability declarations |
| `test_checker.py` | 527 | 6,057 | Type synthesis, slot resolution, effects, effect subtyping, contracts, exhaustiveness, cross-module typing, visibility, error codes, string built-ins, generic rejection, IO operation types, Markdown types, Regex types, abilities, Map collection, Set collection, Decimal type, Json type, Html type, Http effect, Inference effect, removed legacy name regression |
| `test_obligations.py` | 282 | 1080 | Reified proof obligations + warm `VerificationSession` (#222 Phase A): full-corpus differential oracle (warm session == cold `verify()` on diagnostics, summary, and obligation stream, plus warm-twice determinism, across all 35 examples and every verify/run-level conformance program), summary↔obligation tier-bookkeeping consistency, per-kind unit tests (requires / ensures / decreases / nat_sub / call_pre statuses, counterexamples, error codes), content-key stability + same-text-two-sites span disambiguation, session solver reuse, type-error short-circuit, ADT-registry resync between programs; plus the Phase B incremental suite — identical-source full replay, callee-body-edit replays callers while callee-contract-edit invalidates them, span-shift and ADT-edit conservative invalidation, cross-program isolation, timeout-status never cached (monkeypatched solver), FIFO eviction bound; plus the #727 dedup pin — a violating call in a let RHS records exactly one E501 diagnostic and one call_pre obligation |
| `test_verifier.py` | 383 | 7,035 | Z3 verification, counterexamples, tier classification, call-site preconditions, branch-aware preconditions, pipe operator, cross-module contracts, match/ADT verification, decreases verification, mutual recursion, refined Bool/String/Float64 param sorts, **@Nat subtraction underflow obligation** (#520 — Path-A obligation discharge via requires/path-conditions/path-aware Z3 refutation, pure-literal exclusion, Int-Int and Nat-Int → Int exemptions), **@Nat binding-site narrowing obligation** (#552 — Tier-1 `value >= 0` at let/call-arg/effect-op-arg/ctor-field/match-bind/literal-destructure narrowing, #520 double-emit disjointness, E503 counterexample-witness pin; #747 — generic-instantiation, ADT sub-pattern, non-literal tuple-destructure, and cross-module imported-ctor narrowing, with concrete-site Tier-3 narrowings (incl. the if-expr-source SMT gap, recorded per-component) classified as codegen-guarded `tier3_runtime`, generic function-formal call-args guarded on the monomorphised callee (keyed on `call_target`, not the erased generic decl), and the two genuinely-unguarded residuals — effect-op-arg narrowings (no codegen guard yet, #754) and generic-instantiated constructor-field narrowings (constructors carry no per-field `@Nat` mono metadata) — surfacing the `E504` unguarded warning; #749 — IndexExpr/InterpolatedString walker-recursion pins, `_fresh_slot_var` nat-alias unit test, `_narrows_into_nat` verifier/codegen soundness parity), **refinement-predicate verification** (#746 — Tier-1 discharge at let/call-arg/ctor-field/effect-op-arg/match-bind/tuple-destructure narrowings and refined return positions, E505 violation with counterexample, E506 Tier-3 for untranslatable/non-primitive-base predicates, the R3 already-refined-source exemption via predicate-AST equality, the R5 violating-return pin, the refinement-over-`@Nat` `>= 0 && P` conjoin, and the **refined-ADT-sub-pattern arm-fact carry** — a `Some(@PosInt)` bind on `Option<PosInt>` carries the field's source-type predicate into the arm body so a downstream `@Nat` narrowing discharges instead of a false E503, and reaches call **preconditions** in the arm body via the SMT match-translation fact hook so `Some(@PosInt) -> needs_positive(@PosInt.0)` discharges instead of a false E501, while a genuine `Option<Int>` narrowing stays obligated (E505/E501), never silently assumed; an **alias-base refined return** (`{ @Age \| @Age.0 >= 18 }`) is assumed by the caller via the predicate binder name; and a **refined return from a match arm** (`Some(@PosInt) -> @PosInt.0`) discharges via a global `arm-matched => source-fact` SMT implication on both the normal and generic-fast paths, a violating `Option<Int>` payload still E505), **per-monomorphization generic verification** (#732 — an instantiated `forall<T>` body is verified per concrete instantiation: a generic-body `@Nat` underflow is caught (naming the instantiation, with a counterexample) or discharged when guarded, the never-instantiated residual stays Tier-3 `E520`, collapsed-type-var (`A=B=Int`) De Bruijn reindex soundness, one-diagnostic dedup across multiple instantiations, and discovery of a generic reached only through a `decreases(...)` measure, plus a mixed-`tier3`/`timeout` aggregate-label completeness pin and a recursive-generic-clone source-name pin so `decreases` resolves on the monomorphised instance), **primitive-operation safety obligations** (#680 — division/modulo by-zero `E526` and array-index-bounds `E527`, the in-bounds/out-of-bounds two-check with float-exemption, honest Tier-3 for opaque lengths, the off-by-one and `i >= 0` lower-bound pins, walker recursion through array-literal / assert / interpolated-string / let-destructure positions, the opaque-shadow Tier-3 routing that stops an untranslatable `let`/destructure from silently discharging a stale same-type-outer divisor, De Bruijn-correct `E526`/`E527` fix hints rendered from the actual operands, Tier-1 projection of literal-constructor destructure components (`let Tuple<@Int, @Int> = Tuple(10, 6); _ / @Int.1` discharges `10 != 0` rather than shadowing to Tier-3, while a non-literal source stays a tracked Tier-3 shadow), a tracked placeholder pushed for *every* destructured component so same-type De Bruijn positions don't collapse (`Tuple(10, <opaque>)` keeps `@Int.0` on the opaque second component, never silently discharging against the literal `10`), `_contains_opaque_shadow` recursion so a *compound* divisor / subtraction operand embedding a shadow (`shadow + 1`) falls to Tier-3 instead of a spurious `E526`/`E502` counterexample, and tracked shadowing of match-arm pattern slots bound over an untranslatable (effect-op) scrutinee so a primitive op in the arm falls to Tier-3 rather than silently discharging against a stale same-name outer (`match Source.next(()) { Some(@Int) -> 1 / @Int.0 }`); plus a **multi-agent shadow/projection audit battery** (`TestShadowAuditDivision680` / `TestShadowAuditSubtraction680` / `TestShadowAuditIndex680` / `TestDestructureDeBruijnAlignment680` / `TestShadowAuditInteractions680`) — 57 differential tests pinning the invariant trichotomy (safe → verified, opaque/shadow → Tier-3, provably-unsafe → loud) across compound shadows, modulo parity, multi-component De Bruijn alignment with value-distinct siblings, intervening-type namespaces, stacked / nested destructures, opaque match scrutinees, nested blocks, and intra-block scoping; **mutation-validated** — every shadow/projection test was confirmed to flip RED when its target machinery (`_is_opaque_shadow` / `_contains_opaque_shadow` / the De Bruijn placeholder push / the `let`-shadow / the match-arm `_fresh_pattern_env` / literal projection) is deliberately broken, so none is green-for-the-wrong-reason) |
| `test_monomorphize_differential.py` | 13 | 682 | #732 differential soundness: the verifier's per-monomorphization instantiation discovery covers every instantiation codegen emits (name coverage + per-generic count), over real generic programs (conformance ch02/ch09, `examples/generics.vera`) plus inline cases for the soundness-critical scenarios — collapsed type vars, **prelude combinator emission** (`option_map`), transitive generics, a generic whose type arg is fixed only by a **where-helper's return** (a `Float64`-returning helper, so the unresolved-var `"Bool"` phantom default cannot mask a miss), a generic whose type arg is fixed only by an **imported constructor** (`id2(MkBox(7))` — the verifier's mono-context must include `_module_constructors`, else it phantom-defaults and misses codegen's `id2<Box>`), a generic whose type arg is fixed only by an **imported function's return** (`id_g(make_int(...))` — the verifier's mono-context must seed `fn_ret_types` from imported functions, else it phantom-defaults and misses codegen's `id_g<Int>`, plus a **private-shadow** case pinning the imported-fn seeding stays unfiltered like codegen since filtering would diverge into a false Tier-1), and a generic reached only through a **contract clause or `where` helper** (codegen must seed Pass 1.5 from the shared node-level walk, not just `decl.body`, or it skips the clone → `CodegenSkip` at run time) — so a missed instantiation (a false Tier-1) is caught. Guards against a vacuous pass when codegen emits nothing, plus a **determinism guard** (`vera compile --wat` is byte-stable across `PYTHONHASHSEED` — the mono worklist sorts its instantiation sets) |
| `test_codegen.py` | 1,211 | 21,050 | WASM compilation, arithmetic, Float64, Byte, arrays (incl. compound element types), ADTs, match (incl. nested patterns), generics, State\<T\>, Exn\<E\> handlers, control flow, strings, string escape sequences, IO (read\_line, read\_file, write\_file, args, exit, get\_env, sleep, time, stderr), bounds checking, quantifiers, assert/assume, refinement type aliases, pipe operator, string built-ins, built-in shadowing, parse\_nat Result, GC, Markdown host bindings, Regex host bindings, Map collection, Set collection, Decimal type, Json type, Html type, Http effect, Inference effect, Random effect, example round-trips, GC shadow stack overflow, **WASM tail-call optimization** (#517 — `return_call` emission for tail-position calls, 50K- and 1M-iteration stress, structural assertions on `return_call`/plain `call` boundary, **GC-aware TCO for allocating fns (#549 — `$gc_sp` restore before each `return_call`)**, postcondition-fallback regression (still reverts to plain `call`), analyzer unit tests covering Block-trailing / IfExpr-both-branches / MatchExpr-arm-bodies / let-value-NOT-marked / call-args-NOT-marked / ExprStmt-statement-NOT-marked / IfExpr-condition-NOT-marked / MatchExpr-scrutinee-NOT-marked), **@Nat narrowing runtime guards** (#552 let site; #747 extends to tuple-destructure / top-level match-bind / ADT sub-pattern / concrete ctor-field / call-arg sites — `i64.lt_s; unreachable` net, @Int targets exempt), **refinement-predicate runtime guards** (#746 — primitive-base (incl. `@Bool` / `@Float64`) refined params/returns traverse a `$vera.contract_fail` predicate guard at the function boundary: violating value traps, valid passes, call-args guarded transitively, generic refined returns guarded on the monomorphised instance; non-primitive `@Array` refinements (`array_length(...) > 0`) guarded too, the alias-aware `@Nat` base conjoins its implicit `>= 0`, and erased `@Unit` refinements emit no guard; **tuple-component boundary guards** decompose a `Tuple<PosInt, Int>` param/return at the FFI boundary — loading each refined / `@Nat` component from the heap value and guarding it recursively for nested tuples, so a violating component traps instead of laundering past the verifier's component assumption; a **generic tuple alias** (`type Box<T> = Tuple<T, Int>`) substitutes its argument so `Box<PosInt>` still guards its component, and a mutually-recursive (infinite) tuple alias **fails closed with E617** rather than silently emitting partial guards; a **refinement OVER a tuple** (`type Pair = { @Tuple<PosInt, Int> \| true }`) is unwrapped so its components are guarded too, recursively through nested `Tuple<Pair, Int>`) |
| `test_codegen_contracts.py` | 32 | 570 | Runtime pre/postconditions, contract fail messages, old/new state postconditions |
| `test_codegen_monomorphize.py` | 71 | 1,320 | Generic instantiation, type inference, monomorphization edge cases, ability constraint satisfaction (Eq/Ord/Hash/Show), operation rewriting (eq/compare), show/hash dispatch, ADT auto-derivation, array operations (slice/map/filter/fold) |
| `test_codegen_closures.py` | 50 | 1,618 | Closure lifting, captured variables, higher-order functions, iterative-builder shadow-stack regressions (#570), closure return-value shadow-push balance for both i32-pair and i32-ADT branches across array_map and array_mapi, plus VERA_EAGER_GC injection self-test (#593), IndexExpr-of-FnCall element-type inference (#614), non-contiguous capture and walker-order miscompiles (#615) |
| `test_codegen_modules.py` | 23 | 828 | Cross-module guard rail, cross-module codegen, name collision detection (E608/E609/E610) |
| `test_codegen_coverage.py` | 5 | 244 | Defensive error paths: E600, E601, E605, E606, unknown module calls  |
| `test_execute_characterization.py` | 22 | 467 | Characterization harness pinning `execute()`'s observable contract ahead of the #421 runtime decomposition (#734): every `ExecuteResult` field (`value` int/float/str/heap-pointer/None, `stdout`, `state`, `exit_code`, `stderr`) crossed with the three completion modes — normal return, WASM trap (raises `WasmTrapError` with a classified `kind`, output-before-trap preserved), and interrupt/exit (`IO.exit(n)` → `exit_code` n with `value` None, Ctrl-C → 130) — plus the positional-constructor compatibility shape and `capture_stderr` True-vs-default. **Mutation-validated**: every cell confirmed to flip RED when its target return path in `api.py` is deliberately broken (9 mutations, 0 green-for-the-wrong-reason tests) |
| `test_walker_defensive_branches_597.py` | 21 | 296 | Synthetic-AST tests for the 11 defensive `isinstance` branches added by #597 (`_scan_io_ops` / `_scan_expr_for_handlers` / `_infer_expr_wasm_type` / `_infer_vera_type`) plus the 5 pr-review fixes (#2/#3/#8 — ModuleCall/AnonFn/QualifiedCall return None; dead `is not None` guards on Block/HandleExpr removed) |
| `test_check_walker_coverage_597.py` | 15 | 311 | Unit tests for `scripts/check_walker_coverage.py` parsing logic — Expr subclass extraction, isinstance flattening (incl. tuple form), checklist-block anchoring (incl. CR-3 regression test: `# Foo → bar` outside WALKER_COVERAGE block not counted), section-header tolerance, auto-discovery invariants, end-to-end main exit code |
| `test_stress.py` | 16 | 553 | Scale-dependent regression tests (#596) — `@pytest.mark.stress`, skipped by default.  9 logical tests × eager-GC lane parametrisation = 16 test instances.  10K `array_map`, 5K nested-array `array_map`, 1K-deep tail recursion with allocating arg, 1M-deep tail recursion with allocating arg (#549 GC-aware TCO), 20×20 nested array-fold-of-array-fold, 100K `array_fold`, 10K String allocations, 1K `State<Int>` get/put cycles, 10K `IO.print` calls.  Pins #570 / #515 / #593 / #549 / #487 / #348 / #573 regression coverage |
| `test_errors.py` | 52 | 525 | Error code registry, diagnostic formatting, serialisation, SourceLocation, error display sync (README/HTML/spec) |
| `test_formatter.py` | 124 | 1,074 | Comment extraction, interior comment positioning, expression/declaration formatting, match arm block bodies, idempotency, parenthesization, spec rules, ability declarations |
| `test_cli.py` | 229 | 3,382 | CLI commands (check, verify, compile, run, test, fmt, version, quiet), subprocess integration, JSON error paths, runtime traps, arg validation, multi-file resolution, IO exit codes, --explain-slots |
| `test_resolver.py` | 15 | 411 | Module resolution, path lookup, parse caching, circular import detection |
| `test_types.py` | 73 | 388 | Type operations: subtyping, effect subtyping, equality, substitution, pretty-printing, canonical names |
| `test_wasm.py` | 24 | 344 | WASM internals: StringPool, WasmSlotEnv, translation edge cases via full pipeline |
| `test_verifier_coverage.py` | 91 | 1,589 | Verifier/SMT coverage gaps: SMT encoding paths, verifier edge cases, defensive branches, **#667 SMT translator coverage for `FloatLit` / `IndexExpr` / `ArrayLit`** (Tier 1 verification of float/array literal/index contract predicates) |
| `test_wasm_coverage.py` | 226 | 3,976 | WASM coverage gaps: helpers unit tests, inference branches, closure free-var walking, operator/data/context edge cases |
| `test_tester.py` | 17 | 445 | Contract-driven testing: tier classification, input generation, test execution, skip message content |
| `test_tester_coverage.py` | 34 | 913 | Tester coverage gaps: String/Float64/ADT parameter input generation, Bool/Byte parameters, unsatisfiable preconditions, type expression edge cases |
| `test_markdown.py` | 59 | 393 | Markdown parser: block/inline parsing, rendering, round-trips, edge cases |
| `test_lsp.py` | 94 | 1211 | LSP transport + coordinate layer (#222 Phase C) and language features (#222 Phase D): parametrized code-point↔UTF-16 goldens incl. astral-plane fixtures and surrogate-pair snapping, Span (1-based, exclusive-end) and SourceLocation (0-based col) → LSP Range conversions, point→token-range widening, DocumentStore open/change/close + index invalidation, an in-process handler-drive test, and one stdio end-to-end round-trip against the real `vera lsp` subprocess (initialize → didOpen → shutdown → exit) pinning serverInfo + textDocumentSync capabilities; plus the Phase D feature suite — parse-error single-diagnostic path, type-error verification short-circuit, tier=3 in E520 diagnostic data, per-function tier Hint synthesis (and its suppression for functions with violated obligations), smallest-enclosing-span hover, De Bruijn slot goto (most-recent-parameter jump, out-of-range None, off-slot None), and typed-hole completion (inside/after hole, away-from-hole None); plus the Phase E speculativeEdit suite — identical-text all-unchanged, breaking edit surfaces newly_undischarged (violated nat_sub) with canonical state untouched, strengthening edit surfaces newly_discharged, parse/type errors report ok:false, deleted functions report removed, proof_delta purity; plus the Phase F1 proposeEdit suite — the apply gate (clean and strengthening edits apply, breaking and non-compiling edits refuse), force overriding both gates with the delta still reported, wiring against a structural fake server (apply round-trip with exact full-document replacement range, refuse touches no canonical state, unopened-URI clamp sentinel), and full-document-range goldens (trailing-newline virtual line, UTF-16 end column); plus the Phase F2 strengthenContract suite — splice goldens (first-clause-only replacement with byte-identical remainder, ensures variant, unknown-fn None), the call-site audit pin (tightened precondition refused with newly_undischarged call_pre items, canonical state untouched), provable-ensures strengthening applies, and the three splice-target refusal paths (no analysis, unparseable document, unknown function); plus the Phase F3 addEffect suite — transitive-caller closure goldens (diamond in declaration order, leaf, unknown-fn None, recursion appears once), effect-row rewrite goldens (pure to singleton set, source-preserving append, already-present None, base-name identity blocking State<Int> next to State<Bool>), diamond propagation applying one multi-site candidate with the bystander untouched, mixed append/replace rows with already-satisfied callers skipped, the fully-satisfied no-op shape, and the two refusal paths; plus the #728 instruction-contract suite — the LSP message carries description, rationale, and the Fix: paragraph (also pinning single E501 emission at the LSP surface), and a bare diagnostic maps to the description alone |
| `test_browser.py` | 106 | 2,117 | Browser parity: Python/wasmtime vs Node.js/JS-runtime output equivalence across IO, State, contracts, Markdown, Regex, and all compilable examples |
| `test_conformance.py` | 460 | 102 | Parametrized conformance suite: parse, check, verify, run, format idempotency across 92 programs |
| `test_prelude.py` | 24 | 422 | Prelude injection: Option/Result/array operation detection, combinator shadowing, type aliases, end-to-end compilation |
| `test_readme.py` | 2 | 79 | README code sample parsing |
| `test_html.py` | 4 | 189 | HTML landing page code samples: parse, check, verify |
| `test_build_site.py` | 23 | 316 | Site-asset tooling — `_abs_links` rewriting (relative links, fenced-block immunity incl. inline backticks and tilde fences, http/https/fragment pass-through, Vera effect syntax not mis-parsed), `build_site` `<lastmod>` stability (preserve/refresh keyed on URL-structure change), and `check_site_assets` sitemap staleness (missing / date-only-clean / structural-stale) |
| `test_check_changelog_updated.py` | 67 | 663 | `check_changelog_updated.py` unit + end-to-end tests: file classification (incl. file-style exact-match vs directory-style prefix-match), CHANGELOG diff parsing with `[Unreleased]` section tracking, bare-heading rejection, and full-file context (regression test for bullets far below the heading), `Skip-changelog:` trailer detection, temp-repo integration covering substantive/exempt/label/trailer paths |
| `test_check_doc_counts.py` | 15 | 150 | `check_doc_counts.py` planning-document checks: KNOWN_ISSUES refactoring line counts (±10% tolerance band incl. the exact-boundary case, drift detection, empty-file citation, hyphenated paths, missing file/section/rows) and HISTORY version-row format (issue-link limit, ` — ` separator rejection, dateless-row and prose exemption, line-number reporting) |
| `test_check_limitations_sync.py` | 5 | 77 | `check_limitations_sync.py` section extraction: table-rows-only issue harvesting, prose-link exemption, bounding at the next second-level heading, `None` for absent or sub-level headings so renamed sections fail loudly |
| `test_runtime_traps.py` | 66 | 2,405 | Runtime trap categorisation (#516 Stage 1), stdout/stderr-on-trap preservation (#522), `IO.print` live tee (#543), and trap source backtrace (#516 Stage 2): `_classify_trap` per-`kind` mapping (`divide_by_zero`/`out_of_bounds`/`stack_exhausted`/`unreachable`/`overflow`/`contract_violation`/`unknown`), `WasmTrapError` shape + `RuntimeError` substitutability, end-to-end `cmd_run` text + JSON envelopes including `trap_kind`, captured `stdout`, captured `stderr`, JSON-mode "no stderr leak" invariant, cross-stream code-order regression using merged `redirect_stdout`/`redirect_stderr`, the v0.0.123 tee suite (live streaming, write-count + order preservation, JSON-mode tee suppression, trap preservation invariant under tee, per-write flush count, default-execute silence), and the v0.0.124 source-mapping suite — `_resolve_trap_frames` unit tests covering user-fn / built-in / built-in-prefix / monomorphized base-name fallback / unknown-name / no-frames-attribute / leaf-first ordering preservation; end-to-end `cmd_run` text-mode + JSON-mode backtrace including the **leaf-first** ordering invariant; contract-violation backtrace in both text and JSON modes; direct `execute()` `WasmTrapError.frames` attachment; **suppression marker** for collapsed leading runtime-helper frames (mocked `vera.codegen.execute` with synthetic `is_builtin=True` leaf frames so the collapse logic is testable deterministically); source-map population for top-level fns + lifted closures (with span-value assertion against the closure literal's exact line range); and the no-builtin-leakage regression that pins built-in helpers (`alloc` / `gc_collect` / `contract_fail`) NOT being registered in `fn_source_map`; plus the v0.0.125 Stage 3 suite (`#547`) — text-mode `Fix:` block surfacing with position-ordering invariant (Fix appears after the source backtrace), text-mode block suppression for `contract_violation` (no empty header noise), JSON-mode `fix` field always-present (schema stability) including the empty-string case, `_TRAP_FIX_PARAGRAPHS` table-completeness assertion (every kind in the taxonomy has a Fix paragraph entry), and the column-wrap invariant (~76 chars max per line, two-space indent under the `Fix:` heading); plus the UTF-8 hardening suite **`TestHostPrintInvalidUtf8589`** (`#589`) — six structural decode-site assertions pinning `errors="replace"` at every UTF-8 decode path in the host runtime (`host_print` / `host_stderr` / `host_contract_fail` / `_read_wasm_string` / `vera/wasm/markdown.py::_read_string` / the String-return decoder in `execute()`), plus one synthetic-WAT end-to-end test that imports `vera.print` and calls it with raw invalid UTF-8 bytes to pin the wasmtime-trampoline contract (a Python `UnicodeDecodeError` inside a host import escapes as a "python exception" cause iff the host decode is strict); plus the Ctrl-C-during-host-import suite **`TestHostSleepKeyboardInterrupt`** ([#595](https://github.com/aallan/vera/issues/595) / [#599](https://github.com/aallan/vera/issues/599)) — after the v0.0.160 relocation to a single `except KeyboardInterrupt` handler in `execute()` (enabled by `wasmtime>=45.0.0`'s `except BaseException` trampoline fix): one structural assertion that the four per-host-import `raise _VeraExit(130)` guards are gone and the centralized handler maps to `exit_code=130`, plus two end-to-end tests that compile real Vera programs calling `IO.sleep(...)` and `IO.read_char(())`, raise `KeyboardInterrupt` from inside the blocking call, and assert the program exits with `ExecuteResult.exit_code == 130` (pre-interrupt stdout preserved) instead of a raw Python traceback escaping wasmtime's trampoline |

## Conformance Suite

The conformance suite is a collection of 92 small, focused programs in `tests/conformance/` that systematically validate every language feature against the spec. Each program is self-contained and imports nothing, with the single exception of `ch07_cross_module_contracts.vera` which depends on `ch07_cross_module_contracts_lib.vera`. Each program tests one feature or a small group of related features.

Simon Willison [argues](https://simonwillison.net/tags/conformance-suites/) that conformance suites are a "huge unlock" for language projects — they transform development from trust-based to verification-based. The conformance suite serves as the definitive specification artifact that any implementation (or agent) can validate against.

### Three-layer testing model

Vera has three distinct test layers, each serving a different purpose:

| Layer | Location | Purpose | What it tests |
|-------|----------|---------|---------------|
| **Unit tests** | `tests/test_*.py` | Test compiler internals | Error paths, edge cases, internal APIs |
| **Conformance suite** | `tests/conformance/` | Spec-anchored feature validation | Every language feature, one program per feature |
| **Example programs** | `examples/` | Showcase programs and demos | End-to-end usage, documentation |

Unit tests verify that the compiler works correctly. Conformance programs verify that the *language* works correctly. Examples demonstrate how to use the language. All three run in CI and pre-commit hooks.

### Test levels

Each conformance program declares the deepest pipeline stage it must pass:

| Level | What it validates | Count |
|-------|-------------------|------:|
| `parse` | Source text is syntactically valid | 0 |
| `check` | Parses and type-checks cleanly | 4 |
| `verify` | Type-checks and all contracts verified by Z3 | 8 |
| `run` | Compiles to WASM and executes correctly | 80 |

Almost all programs are at the `run` level — they compile and execute, producing correct results. Four programs (`ch07_cross_module_contracts_lib`, `ch09_http`, `ch09_inference`, `ch03_typed_holes`) are at the `check` level. Eight programs (`ch03_slot_let_chains`, `ch03_slot_noncommutative`, `ch04_primitive_obligations`, `ch07_cross_module_contracts`, `ch07_io_read_char`, `ch07_io_sleep`, `ch07_random_effect`, `ch09_math_builtins`) are at the `verify` level, using Z3-provable contracts.

### Skipped tests

`pytest tests/ -v` reports 16 skipped tests across two categories:

**Level-limited skips** — the conformance framework only runs tests up to the declared level; stages beyond that level are automatically skipped. These are expected and correct.

| Test | Program | Declared level | Skipped stage | Reason |
|------|---------|---------------|--------------|--------|
| `test_run[ch03_slot_let_chains]` | `ch03_slot_let_chains.vera` | `verify` | `run` | `verify`-level programs don't get a `run` test |
| `test_run[ch03_slot_noncommutative]` | `ch03_slot_noncommutative.vera` | `verify` | `run` | `verify`-level programs don't get a `run` test |
| `test_verify[ch03_typed_holes]` | `ch03_typed_holes.vera` | `check` | `verify` | `check`-level program: verify stage not run |
| `test_run[ch03_typed_holes]` | `ch03_typed_holes.vera` | `check` | `run` | `check`-level program: no standalone `main` |
| `test_run[ch04_primitive_obligations]` | `ch04_primitive_obligations.vera` | `verify` | `run` | `verify`-level programs don't get a `run` test |
| `test_run[ch07_cross_module_contracts]` | `ch07_cross_module_contracts.vera` | `verify` | `run` | `verify`-level programs don't get a `run` test |
| `test_verify[ch07_cross_module_contracts_lib]` | `ch07_cross_module_contracts_lib.vera` | `check` | `verify` | `check`-level program: verify stage not run |
| `test_run[ch07_cross_module_contracts_lib]` | `ch07_cross_module_contracts_lib.vera` | `check` | `run` | `check`-level library module: no standalone `main` |
| `test_run[ch07_io_read_char]` | `ch07_io_read_char.vera` | `verify` | `run` | `verify`-level programs don't get a `run` test |
| `test_run[ch07_io_sleep]` | `ch07_io_sleep.vera` | `verify` | `run` | `verify`-level programs don't get a `run` test |
| `test_run[ch07_random_effect]` | `ch07_random_effect.vera` | `verify` | `run` | `verify`-level programs don't get a `run` test |
| `test_run[ch09_math_builtins]` | `ch09_math_builtins.vera` | `verify` | `run` | `verify`-level programs don't get a `run` test |

**Environment-gated skips** — these programs require network access or a live API key that is not available in CI. They pass `vera check` (type-checking) but cannot be executed.

| Test | Program | Declared level | Skipped stage | Reason |
|------|---------|---------------|--------------|--------|
| `test_verify[ch09_http]` | `ch09_http.vera` | `check` | `verify` | Requires outbound HTTP; unavailable in CI sandbox |
| `test_run[ch09_http]` | `ch09_http.vera` | `check` | `run` | Requires outbound HTTP; unavailable in CI sandbox |
| `test_verify[ch09_inference]` | `ch09_inference.vera` | `check` | `verify` | Requires `VERA_*_API_KEY`; not set in CI |
| `test_run[ch09_inference]` | `ch09_inference.vera` | `check` | `run` | Requires `VERA_*_API_KEY`; not set in CI |

To run the environment-gated tests locally: set `VERA_ANTHROPIC_API_KEY` (or another provider key) and ensure outbound HTTP is available, then `vera run tests/conformance/ch09_http.vera` / `vera run tests/conformance/ch09_inference.vera`.

### Directory structure

```
tests/conformance/
├── manifest.json              # Machine-readable test metadata
├── ch01_int_literals.vera     # Chapter 1: Integer literals
├── ch01_float_literals.vera   # Chapter 1: Float64 literals
├── ch01_string_escapes.vera   # Chapter 1: String escape sequences
├── ...                        # 92 programs total, organized by spec chapter
├── ch07_state_handler.vera    # Chapter 7: State<T> effect handler
├── ch07_exn_handler.vera      # Chapter 7: Exn<E> effect handler
├── ch09_numeric_builtins.vera # Chapter 9: Numeric built-in functions
├── ch09_type_conversions.vera # Chapter 9: Numeric type conversions
├── ch09_markdown.vera         # Chapter 9: Markdown standard library
├── ch09_regex.vera            # Chapter 9: Regular expression matching
├── ch09_decimal.vera          # Chapter 9: Decimal type operations
├── ch09_json.vera             # Chapter 9: JSON standard library
├── ch09_http.vera             # Chapter 9: Http effect (check level)
└── ch10_float_predicates.vera # Chapter 9: Float64 predicates and constants
```

### Manifest

`manifest.json` maps each program to its spec chapter, test level, and feature tags:

```json
{
  "id": "ch04_arithmetic",
  "file": "ch04_arithmetic.vera",
  "chapter": 4,
  "title": "Arithmetic operators",
  "level": "run",
  "spec_ref": "Section 4.1",
  "features": ["add", "sub", "mul", "div", "mod", "unary_neg"]
}
```

The manifest is the machine-readable feature inventory — agents can query it to find which features exist and where they are tested.

### Running the conformance suite

```bash
# Via pytest (parametrized — 450 tests)
pytest tests/test_conformance.py -v

# Via standalone script (used in CI and pre-commit)
python scripts/check_conformance.py
```

The pytest runner (`test_conformance.py`) parametrizes over every manifest entry and runs five checks per program: parse, check, verify, run, and format idempotency.

### Adding a conformance test

1. Write a `.vera` program in `tests/conformance/` following the naming convention `chNN_feature_name.vera`
2. Include a header comment indicating the spec chapter and what the program tests
3. Ensure the program has a `main` function (for `run`-level tests)
4. Format it: `vera fmt --write tests/conformance/your_file.vera`
5. Add an entry to `manifest.json` with the appropriate level and feature tags
6. Run `python scripts/check_conformance.py` to validate

When implementing a new language feature, the conformance program should be written *first* — this is test-driven development against the spec.

## Compiler Code Coverage

Coverage by module, measured by `pytest --cov=vera`:

| Module | Stmts | Miss | Coverage |
|--------|------:|-----:|---------:|
| `wasm/` | 11,130 | 566 | 95% |
| `codegen/` | 3,605 | 239 | 93% |
| `checker/` | 1,223 | 68 | 94% |
| `lsp/` | 492 | 52 | 89% |
| `obligations/` | 188 | 1 | 99% |
| `browser/` | 21 | 0 | 100% |
| `verifier.py` | 702 | 31 | 96% |
| `transform.py` | 617 | 24 | 96% |
| `formatter.py` | 675 | 49 | 93% |
| `ast.py` | 462 | 17 | 96% |
| `smt.py` | 651 | 32 | 95% |
| `markdown.py` | 413 | 54 | 87% |
| `types.py` | 182 | 7 | 96% |
| `errors.py` | 129 | 1 | 99% |
| `environment.py` | 339 | 8 | 98% |
| `cli.py` | 583 | 29 | 95% |
| `parser.py` | 45 | 0 | 100% |
| `resolver.py` | 68 | 2 | 97% |
| `slots.py` | 41 | 5 | 88% |
| `skip.py` | 12 | 3 | 75% |
| `tester.py` | 389 | 3 | 99% |
| `prelude.py` | 187 | 9 | 95% |
| `registration.py` | 18 | 0 | 100% |
| `__init__.py` | 2 | 0 | 100% |
| **Total** | **22,174** | **1,200** | **95%** |

The lowest-coverage files of any size are `vera/lsp/server.py` at 64% (pygls feature-registration glue, exercised end-to-end by editors rather than by unit tests) and `wasm/inference.py` at 80% (deep type-dispatch branches for specific builtin return types).

## Contract Verification Coverage

Vera's verifier classifies each contract into one of three tiers. **Tier 1** contracts are proved correct statically by Z3 — no runtime overhead. **Tier 3** contracts cannot be fully decided by the SMT solver and fall back to runtime assertion checks. The verifier never rejects a valid program; it simply warns when a contract drops to Tier 3.

Across all 35 example programs:

| Metric | Value |
|--------|-------|
| **Tier 1 (static)** | 256 contracts — proved automatically by Z3 |
| **Tier 3 (runtime)** | 24 contracts — verified at runtime via assertion checks |
| **Total** | 280 contracts (91.4% static) |

The 24 remaining Tier 3 contracts and why they cannot be promoted:

| Example | Contract | Reason |
|---------|----------|--------|
| array\_utilities.vera | 4 contracts | Postconditions over array built-in pipelines (filter/sort/fold) outside the decidable fragment |
| async\_futures.vera | 2 contracts | Async/future combinators not in decidable fragment |
| collections.vera | 8 contracts | Collection operations (Map/Set) not modeled in Z3 |
| gc\_pressure.vera | `decreases` in `repeat` | Termination metric not in decidable fragment |
| generics.vera | `ensures(@T.result == @T.0)` | Generic type parameters have no Z3 sort |
| generics.vera | `ensures(@A.result == @A.0)` | Generic type parameters have no Z3 sort |
| html.vera | 2 contracts | Postconditions over Html ADT traversal built-ins not modeled in Z3 |
| increment.vera | `ensures(new(State<Int>) == old(State<Int>) + 1)` | `old`/`new` state modeling not yet implemented |
| json.vera | `decreases` in `sum_hourly` | Termination metric not in decidable fragment |
| string\_utilities.vera | 3 contracts | Postconditions over string-splitting built-ins outside the decidable fragment |

The Tier 1 fragment covers: integer/boolean arithmetic, comparisons, if/else, let bindings, match expressions, ADT constructors, function calls (modular postcondition), `length`, and `decreases` clauses (self-recursive, mutual recursion via where-blocks, Nat and structural ADT measures).

## Language Feature Coverage

How Vera language features (by spec chapter) map to test files and example programs:

| Spec chapter | Feature | Test files | Conformance | Examples |
|-------------|---------|-----------|-------------|----------|
| Ch 1: Lexical | Literals (Int, Float64, Bool, Byte, String) | test_ast, test_codegen | ch01_int_literals, ch01_float_literals, ch01_bool_literals, ch01_byte_literals | most examples |
| Ch 1: Lexical | String escape sequences (`\n`, `\t`, `\\`, `\"`, `\r`, `\0`, `\u{XXXX}`) | test_ast, test_codegen | ch01_string_escapes | io_operations, file_io |
| Ch 1: Lexical | Comments | test_parser | ch01_comments | — |
| Ch 2: Types | Int, Nat, Bool, String, Float64, Byte, Unit | test_codegen, test_checker | ch02_builtin_types | most examples |
| Ch 2: Types | ADTs (algebraic data types), Option, Result | test_codegen, test_checker | ch02_adt_basic, ch02_adt_recursive, ch02_option_result | pattern_matching, list_ops |
| Ch 2: Types | Refinement types | test_codegen, test_verifier | ch02_refinement_types | refinement_types, safe_divide |
| Ch 2: Types | Generics (`forall<T>`) | test_codegen_monomorphize, test_checker | ch02_generics | generics |
| Ch 3: Slots | `@T.n` references, De Bruijn indexing | test_checker, test_codegen | ch03_slot_basic, ch03_slot_indexing, ch03_slot_result | all 35 examples |
| Ch 4: Expressions | Arithmetic, comparison, boolean, unary ops | test_codegen, test_checker | ch04_arithmetic, ch04_comparison, ch04_boolean_ops | factorial, absolute_value |
| Ch 4: Expressions | If/else, let, match, pipe operator | test_codegen, test_checker | ch04_if_else, ch04_let_binding, ch04_match_basic, ch04_match_nested, ch04_pipe_operator | pattern_matching |
| Ch 4: Expressions | String and array builtins | test_codegen | ch04_string_builtins, ch04_array_ops | string_ops |
| Ch 5: Functions | Declarations, recursion, mutual recursion | test_codegen, test_checker | ch05_basic_function, ch05_recursion, ch05_mutual_recursion | factorial, mutual_recursion |
| Ch 5: Functions | Closures, higher-order functions | test_codegen_closures | ch05_closures | closures |
| Ch 5: Functions | Visibility (`public`/`private`) | test_checker | ch05_visibility | modules |
| Ch 6: Contracts | Preconditions (`requires`) | test_codegen_contracts, test_verifier | ch06_requires | safe_divide |
| Ch 6: Contracts | Postconditions (`ensures`) | test_codegen_contracts, test_verifier | ch06_ensures | absolute_value |
| Ch 6: Contracts | Decreases clauses, assert/assume | test_verifier, test_codegen | ch06_decreases, ch06_assert_assume | factorial |
| Ch 6: Contracts | Quantifiers (forall, exists) | test_codegen, test_verifier | ch06_quantifiers | quantifiers |
| Ch 7: Effects | Pure, IO, State\<T\> | test_codegen, test_checker | ch07_pure, ch07_io, ch07_state_handler | hello_world, increment, io_operations, file_io |
| Ch 7: Effects | Effect handlers (State\<T\>, Exn\<E\>) | test_codegen, test_checker | ch07_state_handler, ch07_exn_handler | effect_handler |
| Ch 9: Stdlib | Numeric builtins (abs, min, max, floor, ceil, round, sqrt, pow) | test_codegen, test_checker | ch09_numeric_builtins | — |
| Ch 9: Stdlib | Type conversions (int_to_float, float_to_int, nat_to_int, int_to_nat, byte_to_int, int_to_byte) | test_codegen, test_checker | ch09_type_conversions | — |
| Ch 9: Stdlib | Float64 predicates (float_is_nan, float_is_infinite, nan, infinity) | test_codegen, test_checker | ch10_float_predicates | — |
| Ch 7: Effects | Effect subtyping (§7.8), call-site checking | test_types, test_checker | — | — |
| Ch 2: Types | Bidirectional type checking (local inference) | test_checker | — | — |
| Ch 4: Expressions | Nested constructor patterns in match | test_codegen | ch04_match_nested | pattern_matching |
| Ch 8: Modules | Imports, cross-module typing and codegen | test_codegen_modules, test_resolver | — | modules |
| Ch 11: Compilation | Cross-module name collision detection (E608/E609/E610) | test_codegen_modules | — | — |
| Ch 9: Stdlib | Markdown (md_parse, md_render, md_has_heading, md_has_code_block, md_extract_code_blocks) | test_codegen, test_markdown | ch09_markdown | markdown |
| Ch 9: Stdlib | Regex (regex_match, regex_find, regex_find_all, regex_replace) | test_codegen, test_checker | ch09_regex | regex |
| Ch 9: Stdlib | Map, Set, Decimal collections | test_codegen, test_checker | ch09_map, ch09_set, ch09_decimal, ch09_decimal_generics | collections |
| Ch 9: Stdlib | Json (json_parse, json_stringify, json_get, json_array_get, json_array_length, json_keys, json_has_field, json_type) | test_codegen, test_checker | ch09_json | json |
| Ch 9: Stdlib | Html (html_parse, html_to_string, html_query, html_text, html_attr) | test_codegen, test_checker | ch09_html | html |
| Ch 9: Stdlib | Http effect (Http.get, Http.post) | test_codegen, test_checker | ch09_http | http |
| Ch 11: Compilation | Contract-driven testing (Z3 input gen + WASM execution) | test_tester, test_cli | — | safe_divide, factorial |
| Ch 12: Runtime | Browser runtime parity (JS host bindings match Python) | test_browser | — | — |

## Test Helpers

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

## Round-Trip Testing

Every one of the 35 example programs in `examples/` is tested through **every pipeline stage** via parametrised tests: parsing, AST transformation, type checking, contract verification, WASM compilation, and execution. If you add a new `.vera` example, it is automatically included in the round-trip suite.

The formatter has **idempotency tests**: `format(format(x)) == format(x)` for all tested programs.

## Stress Tests

Scale-dependent regression tests live in `tests/test_stress.py` (#596).  These exercise Vera programs at sizes where historical bugs (#570 iterative-builder shadow-stack overflow at ~4000 elements, #515 GC self-fault under sustained allocation, #593 Conway's Life corruption at 12×30+) first manifested, plus 2-3x safety margin.

### The 9 initial test programs

Each test compiles a self-contained Vera program, executes it via the in-process API, and asserts on a SPECIFIC observable.  Iteration counts are tuned to the smallest scale where each bug class historically manifested.

Tests marked **[eager-GC]** also run under the `VERA_EAGER_GC=1` lane (see below).

**1. `test_array_map_over_10k_int_array`** **[eager-GC]** — `array_map` over a 10,000-element `Array<Int>`, each element incremented by 1.  Asserts `array_length` of the result == 10000.  Pre-#570 this class of program shadow-stack-overflowed at ~4,000 elements; 10K is a 2.5x safety margin.  Pins the iterative-builder fix and acts as an early-warning for any future regression in shadow-stack hygiene under `array_map`.

**2. `test_array_map_over_5k_nested_bool_array`** **[eager-GC]** — `array_map` over a 5,000-element `Array<Int>` producing a fresh `Array<Bool>` (`[true, false, true]`) per iteration.  Asserts the outer length == 5000.  Tests per-iteration allocation pressure where each closure call allocates and the result must remain rooted across the loop.  Pre-#570 + pre-#515 this class corrupted intermediate roots; the test pins the per-iteration alloc/root hygiene fix.

**3. `test_deep_tail_recursion_with_allocating_arg`** **[eager-GC]** — 1,000-deep tail recursion over `loop(@Int, @Int -> @Int)` where each iteration allocates a fresh `let @Array<Int> = [@Int.0, @Int.1]` before recursing.  Asserts the final accumulator == 2,000 (1,000 × `array_length([_, _])` = 1,000 × 2).  Tests the TCO / GC interaction (#549) — tail-call optimisation must not discard the shadow-stack roots that keep the allocating arg live.  Pre-#549 this body used a string-pool literal (`"stress"`) which doesn't actually trigger `needs_alloc`, so the test passed trivially without exercising the path it documented; switched to a genuine heap allocation in v0.0.154 so the eager-GC lane actually fires on every iteration.

**4. `test_conways_life_grid_alloc_and_count_alive_20x20`** **[eager-GC]** — synthetic regression covering #593 (Life corruption from gen 1+ at 12×30).  Bug is closed; this test pins the fix.  The program builds a 20×20 all-false `Array<Array<Bool>>` via nested `array_map`-of-`array_range`, then runs a single `count_alive` pass — an array-fold over array-fold that walks every cell.  Asserts the count == 0.  This is a **structural-shape** test, not a Life simulation: it does NOT run 100 generations (the original test name implied that; the rename in #669 corrects it).  The structural shape — 400-cell allocation, nested `array_fold` of `array_fold`, captured outer-binding references inside the inner closure — is what matters; the trivially-deterministic outcome (all-false → 0) makes the test fast and unambiguous while still exercising the code paths #593 hit.  (An earlier version of this entry also cited #595 — that was misattributed; #595 is a cleanup-path bug exercised by `TestHostSleepKeyboardInterrupt` in `test_runtime_traps.py`, not by this stress test.)

**5. `test_array_fold_100k_iterations`** — `array_fold` over an `array_range(0, 100000)` summing all values.  Asserts the result == 4,999,950,000 (the closed-form sum of 0..99999).  Tests the fold accumulator across many GC cycles.  Pre-#487 / #348 (worklist + multi-page grow) this class of program ran the heap into multi-page territory and tripped allocation-pressure bugs; the test pins the fixes.  The closed-form assertion catches any regression that silently short-circuits or skips iterations.  *Not in the eager-GC lane* — allocation-pressure target, not GC-rooting; 100K × forced-GC would inflate suite time without strengthening detection.

**6. `test_10k_string_allocations`** **[eager-GC]** — `array_fold` over `array_range(0, 10000)` where each iteration produces a fresh String via `let @String = "\(@Int.0)"` and accumulates `string_length`.  Asserts the total == 38,890 (10 × 1-digit + 90 × 2-digit + 900 × 3-digit + 9000 × 4-digit).  Pre-#573 (wrap-table compaction) and #575 / #576 (host-store reclamation) this class of program would leak handles or self-fault under sustained String allocation; the test pins the fixes.  The digit-count assertion is uniquely sensitive to any short-circuit because it varies non-linearly with iteration count.

**7. `test_state_handler_1k_ops`** **[eager-GC]** — 1,000 `State<Int>` get/put cycles within a single `handle[State<Int>](@Int = 0) { ... } in { ... }` scope, driven by a `count_up(@Int -> @Int)` helper that does `get(()); put(state + 1); count_up(n - 1)`.  Asserts the final state == 1000.  Pins the handler installation + resume continuation plumbing under sustained host-import call rate.  Pre-stage-11 / pre-#535 work, large State-handler programs accumulated captured-frame roots without bound.

**8. `test_10k_io_print_calls`** — 10,000 `IO.print("x\n")` calls in sequence via a `loop(@Int -> @Unit)` helper, with `tee_stdout=True` so the captured output buffer grows in lock-step.  Asserts the captured stdout contains exactly 10,000 `x` characters.  Exercises the `host_print` bridge at sustained rate; tests the in-process stdout-capture buffer's growth and the host-import call path under load.  The character-count assertion (rather than line-count) is robust to subtle buffering variations.  *Not in the eager-GC lane* — host-import target, not GC-rooting; the `host_print` bridge doesn't allocate Vera-heap data.

**9. `test_tco_with_allocation_1m_iterations`** **[eager-GC]** — 1,000,000-deep tail recursion over `loop(@Int, @Int -> @Int)` with a fresh `let @Array<Int> = [_, _]` per iteration.  Asserts the final accumulator == 2,000,000 (1M × 2).  The high-volume companion to #3.  Pre-#549 this depth would have been impossible: 1M plain `call`s blow the WASM call stack at ~30K frames.  Post-#549 the `return_call` + `$gc_sp` restore keeps shadow-stack usage flat, so 1M iterations complete in constant memory in ~190ms in both default and eager-GC modes.  A shadow-stack leak per iteration would trap the overflow guard around 1,300 iterations (16K shadow stack / ~12 bytes per leaked frame); completing all 1M proves the invariant.

### Eager-GC lane

Seven of the nine tests target GC-rooting bug classes (#570 / #515 / #549 / #573 / #593 / captured-frame State handlers).  Each of those runs under **two parameter modes**: default GC and `VERA_EAGER_GC=1`.  The `VERA_EAGER_GC` env var (read at compile time by `vera/codegen/assembly.py`) emits a `call $gc_collect` as the first instruction of the runtime's `$alloc` function, forcing a full GC pass on every allocation.

This converts latent missing-shadow-root bugs from "fires occasionally at scale" to "fires on the very next allocation," so a regression that would normally require thousands of iterations to surface will fail on the first or second iteration under eager GC.  The pattern was used to diagnose #593 originally; the eager lane embeds that diagnostic capability as ongoing regression coverage.

The eager-GC lane is implemented via a `pytest.mark.parametrize("eager_gc", [False, True], ids=["default_gc", "eager_gc"])` decorator + a `monkeypatch` fixture that scopes the env var to the parametrised test instance.  The two non-parametrised tests — `test_array_fold_100k_iterations` (allocation-pressure target, not GC-rooting) and `test_10k_io_print_calls` (host-import target) — would inflate the suite under eager GC without strengthening detection of the relevant bug class.

### Configuration and behaviour

**Default behaviour**: stress tests are skipped from the per-PR pytest run via `addopts = "-m 'not stress'"` in `pyproject.toml`.  Local invocation:

```bash
pytest -m stress                    # all 16 parametrised test instances (9 logical tests × eager-GC lane)
pytest tests/test_stress.py -m stress -v   # full stress suite, verbose
pytest tests/test_stress.py::test_array_map_over_10k_int_array -m stress -v   # both modes of one test
pytest "tests/test_stress.py::test_array_map_over_10k_int_array[eager_gc]" -m stress -v   # one mode only
```

**CI integration**: `.github/workflows/nightly-stress.yml` runs them in three triggers:

1. **Nightly cron** (`0 6 * * *` UTC) — primary safety net, catches drift in a daily window so bisection cost stays small.  **Failures auto-file (or comment on) a tracking issue** with the `stress-regression` label so the regression is visible to anyone watching the issue feed.  See the failure-reporting subsection below.
2. **Path-filtered PRs** touching `vera/codegen/**`, `vera/wasm/**`, `vera/checker/**`, `tests/test_stress.py`, or the workflow file itself — fail-fast for PRs that change code most likely to break stress invariants.  `vera/checker/**` is included because the AST shape it produces flows into codegen — a checker change that subtly alters the AST can break runtime invariants without touching `vera/codegen/` or `vera/wasm/`.  PR failures show on the PR's checks tab; no tracking issue is filed (the PR author already sees the failure).
3. **`workflow_dispatch`** — manual trigger from the Actions tab for local-suspicious commits.  Failures are visible to whoever triggered the run; no tracking issue is filed.

**Failure reporting (cron only)**: when the nightly cron fails, the workflow opens an issue titled "Nightly stress regression on main (tracking)" with the `stress-regression` label, including the commit SHA and the run URL.  If an open issue with that label already exists, the new failure posts a comment on it instead of filing a duplicate — so the issue persists across days of failures until a maintainer manually closes it.  The `stress-regression` label is auto-created on first failure.  This converts cron failures from "visible only to whoever opens the Actions tab" to "visible in the issue feed where Vera work is already triaged."  Implementation uses `actions/github-script@v7` with `issues: write` job-scoped permission.

**Budget**: the full suite completes in well under the 5-minute target — measured at **0.66s in-process** on a developer laptop on 2026-05-13 for all 16 test instances (9 logical × eager-GC lane on 7 of them).  CI cold-start adds workflow setup time on top.  Iteration counts are tuned to the smallest scale where each bug class has historically manifested with ~2-3x safety margin, NOT maximised — the goal is reliable detection of the bug class, not benchmarking.  If this measured figure drifts more than ~2x in either direction, treat it as a signal: either iteration counts have grown without rationale (revisit per the "Adding a stress test" rule 2) or a runtime perf regression has landed.

**Assertion shape**: each test asserts on a SPECIFIC observable (e.g. `array_fold` returning the closed-form sum `4999950000`, `IO.print` producing exactly 10000 `x` characters), not just "completed without crashing".  This catches a future regression where the loop silently short-circuits or skips iterations.

### Adding a stress test

A new stress test should:

1. **Target a specific scale axis** (iteration count, allocation pressure, recursion depth, handler-op rate, etc.) and **name the bug class it guards against** in its docstring.  Reference the issue number(s).
2. **Pick the smallest scale that reliably manifested the bug class historically**, plus ~2-3x safety margin.  Don't maximise — bigger isn't better and inflates the suite.
3. **Assert on a SPECIFIC observable** with a closed-form or otherwise unambiguous expected value.  Avoid "no exception raised" — that passes silently when the loop short-circuits.
4. **Use the `_run` helper** (or a parallel helper for non-pure tests) — it handles tempfile lifecycle, parsing, compilation, error checking, and execution.
5. **Carry `pytestmark = pytest.mark.stress` at module level** (the file already does) so the test is collected only under `pytest -m stress`.
6. **Opt into the eager-GC lane** if the target bug class is GC-rooting-related (shadow-stack, captured-frame, alloc-pressure-root-loss).  Add `@EAGER_GC_PARAMS` above the function, change the signature to `(eager_gc: bool, monkeypatch: pytest.MonkeyPatch)`, and pass both through to `_run(src, eager_gc=eager_gc, monkeypatch=monkeypatch)`.  Skip the lane if the bug class is unrelated to GC rooting (host-import call rate, parser perf) — doubling the test cost without strengthening detection is the wrong trade.

## Mutation Testing

A passing suite is necessary, not sufficient — a green test can pass *for the wrong reason* (the #680 audit found 8 such tests in one 57-test battery; #734 had to mutation-validate its own harness).  Mutation testing checks the checker: it deliberately breaks each line of `vera/` and confirms a test flips RED.  A surviving mutant is a test gap — a **weak test** to strengthen or an **equivalent mutant** to annotate (`# pragma: no mutate`).

The full mechanics — the tool decision (`mutmut`, the `[mutation]` extra, the `[tool.mutmut]` config), the **in-process-oracle caveat** (subprocess suites import the un-mutated package, so they can't kill mutants), resume-after-hard-kill, the Z3-flakiness guardrail, and the survivor-triage workflow — live in the runbook: **[`MUTATION.md`](MUTATION.md)**.

**Baseline — soundness core.**  The first sweep covers `verifier.py`, `smt.py`, `checker/`, and `obligations/`: 10,620 mutants, **80.8% caught**, 2,038 survivors.  The committed score is `mutation-summary.csv` (per-module, diff-able) plus a README badge (`mutation.json`, regenerated by `scripts/mutation_report.py`); the full survivor inventory and per-module chart are attached to [#387](https://github.com/aallan/vera/issues/387).  Soundness-core triage and the whole-`vera/` sweep — deferred behind the [#421](https://github.com/aallan/vera/issues/421) `execute()` decomposition, which otherwise inflates a mutant file mutmut can't index — are tracked there.

Mutation testing runs **locally** for now (the measure-all sweep is multi-day; CI's 6 h job cap can't hold it).  A non-gating on-demand workflow and a diff-scoped PR gate are deferred to a focused follow-up PR — see `MUTATION.md` § CI.

## Test Fixture Conventions

Cross-platform footguns hit by the post-#637 Windows CI rollout (PRs #639/#643/#644/#646).  Each has a workaround that makes the fixture portable across Linux / macOS / Windows.

### Tempfiles handed off to subprocesses must use `delete=False`

Windows can't reopen a file while another handle is still held; if a test fixture writes to a tempfile via `with tempfile.NamedTemporaryFile(delete=True) as f:` and then runs `subprocess.run([..., f.name])` inside the `with` block, the subprocess fails with a `PermissionError` because the parent still holds the handle.  Unix allows concurrent handles so the same fixture works there.

```python
# Wrong — fails on Windows:
with tempfile.NamedTemporaryFile(mode="w", suffix=".vera", delete=True) as f:
    f.write(content)
    f.flush()
    subprocess.run([sys.executable, "-m", "vera.cli", "check", f.name])

# Right — portable:
f = tempfile.NamedTemporaryFile(mode="w", suffix=".vera", delete=False)
try:
    f.write(content)
    f.close()
    subprocess.run([sys.executable, "-m", "vera.cli", "check", f.name])
finally:
    Path(f.name).unlink(missing_ok=True)
```

Surfaced via `tests/test_html.py::TestHtmlCodeSamples` — see PR #646 for the fix.

### Paths embedded into Vera string literals must use POSIX form

Windows tempfile paths look like `C:\Users\runner\AppData\Local\Temp\...`.  Vera's grammar (correctly) rejects `\U` as an invalid string-literal escape, so embedding such a path via f-string interpolation trips `[E009] Invalid escape sequence: \U` at parse time.  Convert to POSIX form before embedding:

```python
# Wrong — fails on Windows:
source = f'IO.read_file("{tmp_path}")'

# Right — portable (Windows file APIs accept forward slashes).
# `Path(tmp_path).as_posix()` works whether `tmp_path` is a str
# (from `tempfile.NamedTemporaryFile().name`) or a `pathlib.Path`
# (from pytest's `tmp_path` fixture).  Don't use `tmp_path.replace`
# — that's `str.replace` on a string but `Path.replace` (the
# rename method!) on a Path, which would silently move the file.
vera_path = Path(tmp_path).as_posix()
source = f'IO.read_file("{vera_path}")'
```

Surfaced via `tests/test_codegen.py::TestIOOperations::test_io_read_file_*` — see PR #643 for the fix.

### File I/O without explicit encoding falls back to the locale default

Python's text-mode `open()` / `read_text()` / `write_text()` without an explicit `encoding=` kwarg defaults to `locale.getpreferredencoding()`, which is **cp1252 on en-US Windows**.  Tests that read or write files containing `→` (right arrow), `—` (em-dash), or other non-ASCII characters fail on Windows with `UnicodeEncodeError: 'charmap' codec can't encode '→'` or `UnicodeDecodeError: ... 0x97`.

CI sets `PYTHONUTF8=1` (PEP 540) globally so all text-mode I/O defaults to UTF-8 regardless of locale.  For local-developer ergonomics on Windows without `PYTHONUTF8=1` in the shell, the durable fix is explicit `encoding='utf-8'` at every `open()` site — tracked as a follow-up audit in #645.  When adding new test fixtures or scripts that touch text files, prefer the explicit form:

```python
# Implicit — works only when PYTHONUTF8=1 is set:
text = path.read_text()

# Explicit — works everywhere:
text = path.read_text(encoding="utf-8")
```

Surfaced via ~9 tests across `test_codegen.py`, `test_codegen_monomorphize.py`, `test_codegen_closures.py`, `test_html.py` — see PR #646 for the CI-side fix.

## Adding Tests

When extending the compiler, add tests following the existing patterns:

1. **New grammar construct:** Add parser tests to `test_parser.py` (positive and negative)
2. **New AST node:** Add transformation tests to `test_ast.py` (check node fields, spans, serialisation)
3. **New type rule:** Add checker tests to `test_checker.py` using `_check_ok()`/`_check_err()`
4. **New SMT support:** Add verifier tests to `test_verifier.py` using `_verify_ok()`/`_verify_err()`
5. **New codegen support:** Add compilation tests to `test_codegen.py` using `_compile_ok()`/`_run()`/`_run_trap()`
6. **New example program:** Add to `examples/` -- it is automatically included in round-trip tests
7. **New error pattern:** Add formatting tests to `test_errors.py`
8. **New tester feature:** Add tests to `test_tester.py` using `_test(source)` helper
9. **New host binding:** Add parity tests to `test_browser.py` to ensure the JavaScript runtime stays in sync with the Python runtime

## Validation Scripts

Twenty scripts in `scripts/` validate cross-cutting concerns beyond unit tests (two of them — `build_site.py` and `fix_allowlists.py` — generate or repair rather than check):

| Script | What it validates |
|--------|-------------------|
| `check_conformance.py` | All 92 conformance programs pass their declared level (parse/check/verify/run) |
| `check_examples.py` | All 35 `.vera` examples pass `vera check` + `vera verify` |
| `check_examples_readme.py` | Every `vera run` command in examples/README.md references an existing file and exported function |
| `check_spec_examples.py` | 164 parseable code blocks from spec chapters: parse, type-check, and verify |
| `check_readme_examples.py` | All Vera code blocks in README.md parse correctly |
| `check_skill_examples.py` | All Vera code blocks in SKILL.md parse correctly |
| `check_faq_examples.py` | All Vera code blocks in FAQ.md parse correctly |
| `check_examples_doc.py` | All Vera code blocks in EXAMPLES.md parse correctly |
| `check_html_examples.py` | All Vera code blocks in docs/index.html pass parse + check + verify |
| `check_site_assets.py` | Generated site assets under `docs/` are up-to-date |
| `check_version_sync.py` | `pyproject.toml`, `vera/__init__.py`, and the docs badge carry the same version |
| `check_doc_counts.py` | Counts cited in the docs match the live codebase, KNOWN_ISSUES refactoring counts within ±10%, HISTORY version-row format |
| `check_limitations_sync.py` | Limitation tables consistent across KNOWN_ISSUES.md, vera/README.md, spec chapters, SKILL.md, and LSP_SERVER.md |
| `check_changelog_updated.py` | CHANGELOG.md gains an entry when substantive files change (`Skip-changelog:` trailer to bypass) |
| `check_walker_coverage.py` | Every walker function in `vera/` covers every `Expr` subclass via `isinstance` dispatch or `# WALKER_COVERAGE:` checklist comment (#597) |
| `check_e602_clean.py` | No unexpected E602/E604 silent-skip sites outside the explicit allowlist |
| `check_wheel_availability.py` | Every runtime dependency ships wheels for all supported platforms |
| `check_licenses.py` | All installed packages have MIT-compatible licenses |
| `build_site.py` | Regenerates the AI-readable site assets that `check_site_assets.py` verifies |
| `fix_allowlists.py` | Auto-fix stale allowlist line numbers after Markdown edits |

These run in both pre-commit hooks and CI, so issues are caught locally before they reach the remote.

### Spec validation pipeline

`check_spec_examples.py` pushes spec code blocks through three compiler stages, with allowlists at each level:

| Stage | Pass | Allowlisted | Categories |
|-------|-----:|------------:|------------|
| **Parse** | 81 | 67 | FUTURE (9), FRAGMENT (58) |
| **Type-check** | 67 | 14 | INCOMPLETE (13), FUTURE (1) |
| **Verify** | 66 | 1 | ILLUSTRATIVE (1) |

Allowlisted entries have stale-detection: when a feature lands or a spec edit shifts line numbers, CI flags the entry for removal or the `fix_allowlists.py` script auto-fixes the line numbers. The INCOMPLETE check entries reference functions, types, or imports not defined in the block (e.g. `abs`, `Tuple`, `array_map`, `parse_int`). The 1 FUTURE check entry uses `async/await`. The 1 ILLUSTRATIVE verify entry is a spec example demonstrating multiple postconditions syntax where the contract is intentionally imprecise.

## JSON Output Stability

`vera check --json`, `vera verify --json`, and `vera test --json` emit structured JSON for downstream tooling (CI pipelines, IDE plugins, agent feedback loops).  The field set is a public API — see [`spec/00-introduction.md` §0.5.8](../spec/00-introduction.md#058-machine-readable-output---json) for the stability rules.  Tests in `tests/test_cli.py` assert on the documented field set, so a regression that drops a documented field will fail at least one test.

### `vera check --json` / `vera verify --json`

Top-level:

| Field | Type | Description |
|---|---|---|
| `ok` | bool | `true` iff the file passed all checks at the requested stage; the canonical exit-code signal |
| `file` | string | The source file checked (echoes the path argument) |
| `diagnostics` | array | List of error-severity `Diagnostic` objects (see below) |
| `warnings` | array | List of warning-severity `Diagnostic` objects |
| `verification` | object | Only on `vera verify --json` — counts of `tier1_verified`, `tier3_runtime`, `total` |
| `slot_environments` | array | Only when `--explain-slots` is passed — per-function slot tables |

`Diagnostic` shape: `severity`, `description`, `location`, `source_line`, `rationale`, `fix`, `spec_ref`, `error_code` (the `error_code` set is documented in `vera/errors.py::ERROR_CODES`).

### `vera test --json`

Top-level:

| Field | Type | Description |
|---|---|---|
| `ok` | bool | `true` iff `summary.failed == 0` and no verifier errors; the canonical exit-code signal |
| `file` | string | The source file tested |
| `functions` | array | Per-function `FunctionTestResult`: `name`, `category` (one of `"verified"`, `"tested"`, `"failed"`, `"skipped"`), `reason`, `trials_run`, `trials_passed`, `trials_failed`, `failures` |
| `summary` | object | Aggregate counts (see below) |
| `diagnostics` | array | Verifier-error diagnostics that fed into `"failed"` classifications |

`summary` field set:

| Field | Description |
|---|---|
| `verified` | Functions classified Tier 1 (proved by Z3) |
| `tested` | Functions exercised with Z3-generated inputs |
| `passed` | Subset of `tested` where all trials passed |
| `failed` | Verifier-refuted OR Tier-3-tested-with-trial-failures |
| `skipped` | Functions whose inputs can't be Z3-generated (e.g. ADT params) |
| `total_trials` | Sum of trials run across all tested functions |
| `total_passes` | Sum of passing trials |
| `total_failures` | Sum of failing trials |
| `unlisted_errors` | Verifier-error diagnostics whose attributable function isn't in the displayed `functions` list (`--fn` filtering, private helpers).  Added in v0.0.156. |

### Stability contract

Per `spec/00-introduction.md` §0.5.8: fields MAY be added (consumers MUST tolerate unknowns), fields MUST NOT be removed or renamed without a major version bump, and field semantics MUST NOT change.  `ok` is the canonical gate; downstream CI SHOULD read it rather than parse field-by-field.

## Pre-commit Hooks

Every push is checked by 28 configured hooks across two stages: 26 are configured at the commit stage (after `pre-commit install`), and 2 (`check-changelog-updated`, `uv-lock-check`) are configured at the push stage (after `pre-commit install --hook-type pre-push`). Many commit-stage hooks use per-hook `files:` / `types:` filters and only fire when matching files are staged — a docs-only commit triggers a small subset, a compiler-level commit triggers most. Full list:

| Hook | What it does |
|------|-------------|
| `trailing-whitespace` | Strip trailing whitespace |
| `end-of-file-fixer` | Ensure files end with a newline |
| `check-yaml` / `check-toml` | Validate config file syntax |
| `check-merge-conflict` | Detect conflict markers |
| `check-added-large-files` | Reject files >500 KB |
| `debug-statements` | Detect `pdb`/`ipdb` imports |
| `ruff check .` | Lint Python with ruff (default `F` + `E` rules) |
| `mypy vera/` | Type-check compiler in strict mode |
| `pytest tests/ -q` | Run full test suite |
| `fix_allowlists.py --fix` | Auto-fix stale allowlist line numbers |
| `check_conformance.py` | All 92 conformance programs pass their declared level |
| `check_examples.py` | All 35 examples pass `vera check` + `vera verify` |
| `check_examples_readme.py` | `vera run` commands in `examples/README.md` reference existing files and exported functions |
| `check_readme_examples.py` | README code blocks parse correctly |
| `check_examples_doc.py` | EXAMPLES.md code blocks parse correctly |
| `check_skill_examples.py` | SKILL.md code blocks parse correctly |
| `check_faq_examples.py` | FAQ.md code blocks parse correctly |
| `check_html_examples.py` | HTML landing page code blocks pass parse + check + verify |
| `check_e602_clean.py` | No unexpected `[E602]` (body unsupported) / `[E604]` (param unsupported) silent skips outside the explicit allowlist (Layer 1 of [#626](https://github.com/aallan/vera/issues/626)) |
| `check_doc_counts.py` | Counts in docs match live codebase |
| `check_walker_coverage.py` | Every walker function covers every `Expr` subclass via dispatch or checklist comment (#597) |
| `check_limitations_sync.py` | Limitation tables consistent across KNOWN_ISSUES.md, vera/README.md, spec chapters, SKILL.md, and LSP_SERVER.md |
| `check_licenses.py` | All package licenses are MIT-compatible |
| `build_site.py` | Regenerate AI-readable site assets (llms.txt, llms-full.txt, robots.txt, sitemap.xml, index.md) |
| `browser parity` | Browser runtime produces identical output to Python runtime |
| `check-changelog-updated` (pre-push) | CHANGELOG has a new entry when substantive files changed |
| `uv-lock-check` (pre-push) | `uv.lock` is in sync with `pyproject.toml` |

The validation hooks are smart about triggers -- they only run when relevant files change (`.vera`, `vera/**/*.py`, `grammar.lark`, the corresponding Markdown file, or `vera/browser/*` for browser parity). The two pre-push hooks only fire at push time.

## CI Pipeline

GitHub Actions ([`.github/workflows/ci.yml`](.github/workflows/ci.yml)) runs the following nine parallel jobs on every push and pull request to `main` (the test row is split into a baseline variant and a coverage-instrumented variant on the gating cell, sharing the same underlying job definition):

| Job | Matrix / Runner | What it checks |
|-----|----------------|---------------|
| **test** | Python 3.11, 3.12, 3.13 × ubuntu-latest, macos-15, macos-26, windows-latest (12 combos) | `pytest -v` passes on all combinations |
| **test** (coverage) | Python 3.12 x Ubuntu only | `pytest --cov=vera --cov-fail-under=80` |
| **typecheck** | Python 3.12 x Ubuntu | `mypy vera/` clean in strict mode |
| **lint** | Python 3.12 x Ubuntu | `check_changelog_updated.py`, `check_conformance.py`, `check_examples.py`, `check_examples_readme.py`, `check_version_sync.py`, `check_spec_examples.py`, `check_readme_examples.py`, `check_skill_examples.py`, `check_faq_examples.py`, `check_html_examples.py`, `check_e602_clean.py`, `check_site_assets.py`, `check_licenses.py`, `check_doc_counts.py`, `check_limitations_sync.py`, `ruff check --select S vera/` (security rules) |
| **security** | Ubuntu | [Gitleaks](https://github.com/gitleaks/gitleaks-action) secret scanning on full history |
| **dependency-audit** | Python 3.12 x Ubuntu | `pip-audit --skip-editable --ignore-vuln CVE-2026-4539` — checks all installed packages against the OSV vulnerability database (skips the local editable `vera` package; `CVE-2026-4539` suppressed pending a pygments fix release) |
| **wheel-preflight** | Python 3.12 x Ubuntu | `python scripts/check_wheel_availability.py` — verifies every runtime dep has prebuilt wheels for every (platform, python-version) tuple documented in README §Supported platforms; structural backstop for #691-class install regressions |
| **sbom** | Python 3.12 x Ubuntu | `cyclonedx-py environment` — generates a [CycloneDX](https://cyclonedx.org) JSON SBOM of the full installed dependency tree and uploads it as a 90-day CI artifact |
| **browser-parity** | Python 3.12 + Node.js 22 x Ubuntu | `pytest tests/test_browser.py -v` — verifies JS runtime matches Python runtime; collects V8 coverage via `NODE_V8_COVERAGE` and uploads to Codecov |

The coverage threshold of **80%** is enforced in CI. Current coverage is 96%. JavaScript coverage for `vera/browser/runtime.mjs` is collected separately using V8's built-in coverage and uploaded to Codecov with the `javascript` flag.

Each job uses scoped permissions (`contents: read`; the security job additionally has `security-events: write`) and all checkout steps set `persist-credentials: false` to prevent the `GITHUB_TOKEN` from being baked into `.git/config`. Actions without SHA-pinned version refs are tracked in [#390](https://github.com/aallan/vera/issues/390).

## Open CI/Tooling Issues

Tracked improvements to the testing and CI infrastructure:

| Issue | Description |
|-------|-------------|
| [#349](https://github.com/aallan/vera/issues/349) | Improve browser runtime (`runtime.mjs`) test coverage to >80% — JS code is invisible to pytest-cov, blocking codecov/patch on PRs that touch the runtime |

## Opportunities

Testing infrastructure that could be added in the future:

- **Property-based testing** -- `hypothesis` is installed as a dev dependency but not yet used. Could generate random programs to test parser robustness and formatter idempotency at scale.
- **Formatter round-trip invariant** -- verify `parse(format(parse(src))) == parse(src)` for all valid programs, not just the examples.
- **WASM inference.py coverage** -- `wasm/inference.py` at 80% has the most remaining gaps, mostly in deep type-dispatch branches for specific builtin function return types. These branches require very specific expression nesting patterns to reach.
- **Performance benchmarks** -- no benchmark infrastructure exists. Could track compilation time and Z3 verification time across releases.
