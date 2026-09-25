# Roadmap

Where the project is going.  See [HISTORY.md](HISTORY.md) for what's been built and [CHANGELOG.md](CHANGELOG.md) for per-release detail.

The goal is unchanged: **a stable, working, usable language that doesn't silently fail under the agents using it** — and, on that foundation, the flagship demonstration that an agent can write verified tools in it.

## How this file works

The roadmap is a sequence of **stages** — concentrated sprints over a coherent class of issues — continuing the numbering from [HISTORY.md](HISTORY.md).  A stage is a campaign: pick a themed set, drive it to zero, release, move on.  When a stage's table empties, the stage moves to HISTORY.md with its releases and the next one starts.

Ordering derives from the design principles ([DESIGN.md](DESIGN.md)): verification truth first, then structural drift-proofing, then the capabilities the flagship needs, then the experience around them.  Priority lives in this file and nowhere else — issues carry kind and area labels, not priority labels.  Completed items are deleted from these tables and noted in HISTORY.md.  Stages beyond the next one or two are a forecast, not a commitment — they reorder freely as reality intervenes, and a new bug class outranks everything and becomes its own burndown.

## Where we are

16,978 tests, 256 conformance programs, 43 examples, 14 spec chapters.  [KNOWN_ISSUES.md](KNOWN_ISSUES.md) tracks the open bugs (burndown material rather than stage work), plus the *limitations* the stages below retire.

The next release is a feature release, v0.3.0: the `Decision` effect ([#1467](https://github.com/aallan/vera/issues/1467)), which waits on [#351](https://github.com/aallan/vera/issues/351), [#352](https://github.com/aallan/vera/issues/352), [#372](https://github.com/aallan/vera/issues/372) and [#373](https://github.com/aallan/vera/issues/373).

## The next burndown

*Seventy-three open bugs, driven to zero.*

A bug class outranks stage work, so the open `bug`-labelled set is the queue the fix releases work from, soundness defects first.  [KNOWN_ISSUES.md](KNOWN_ISSUES.md) carries each row's full account and stays the one place the detail lives; this table is the order of attack.

| Issue | What |
|---|---|
| [#1470](https://github.com/aallan/vera/issues/1470) | A refutation can rest on a value whose refinement the solver cannot state: the sort is built, the predicate is not, and the counterexample names a value the type forbids. |
| [#1468](https://github.com/aallan/vera/issues/1468) | A false precondition on a `forall` generic callee is disclosed as **E532** at the call site instead of refuted as **E501**, so a program calling it is accepted. |
| [#1542](https://github.com/aallan/vera/issues/1542) | A composite value coerced into a composite type with a `@Nat` component is obligated nowhere unless it is built at the site. |
| [#1543](https://github.com/aallan/vera/issues/1543) | `let @Int = @Nat.0 + 1` at i64.MAX returns -2^63 unobligated: arithmetic with a literal operand is never a genuine `@Nat`. |
| [#1545](https://github.com/aallan/vera/issues/1545) | A destructuring `let` is not checked against its source: `let Tuple<@Int, @String> = Tuple(1, 2)` passes check and verify. |
| [#1546](https://github.com/aallan/vera/issues/1546) | A heterogeneous `@Nat`/`@Int` join read into an `@Int` is unguarded as a tuple component or a `handle`. |
| [#1557](https://github.com/aallan/vera/issues/1557) | A `@Nat` subtraction over a call to a non-generic `@Nat` function is claimed `nat_sub` `tier3` and compiled with no underflow check. |
| [#1501](https://github.com/aallan/vera/issues/1501) | `&&`, `\|\|` and `==>` evaluate both operands, although spec §4.6 says `&&` and `\|\|` short-circuit, so a guard written beside the operation it protects does not protect it. |
| [#1504](https://github.com/aallan/vera/issues/1504) | `@Nat` values above i64.MAX are compared, divided and printed as negative numbers, and a Tier-1 `ensures` fails. |
| [#1530](https://github.com/aallan/vera/issues/1530) | A `decreases` the backend does not guard (an `Exn` row, a parameterized ADT measure) is recorded as checked at run time. |
| [#1551](https://github.com/aallan/vera/issues/1551) | The verifier discovers a module `where` helper's call as the entry file's same-named generic, and verifies a clone that is never emitted. |
| [#1555](https://github.com/aallan/vera/issues/1555) | `==` between two call results of a generic data type compares heap addresses, and a Tier-1 `ensures` fails at run time. |
| [#1560](https://github.com/aallan/vera/issues/1560) | A module's own `data Json` accepts a prelude `Json` value and reads it through the wrong layout. |
| [#1562](https://github.com/aallan/vera/issues/1562) | A nested constructor pattern is modelled by its outer constructor, so an `ensures` is proved that fails at run time. |
| [#1571](https://github.com/aallan/vera/issues/1571) | A callee's `ensures` is assumed on runs where the call never happens, giving a false Tier 1. |
| [#1572](https://github.com/aallan/vera/issues/1572) | A qualified call to another module's generic leaves that instantiation unverified, so a false `ensures` passes verify. |
| [#1581](https://github.com/aallan/vera/issues/1581) | A module generic's call to its `where` helper compiles, in an importer, as a call to the same-named top-level generic. |
| [#1582](https://github.com/aallan/vera/issues/1582) | A widening inside an `assume` is counted as a Tier 3 runtime check, but an `assume` never runs. |
| [#1587](https://github.com/aallan/vera/issues/1587) | `0 - 18446744073709551615` proves `ensures(@Int.result < 0)` at Tier 1 and returns 1. |
| [#1590](https://github.com/aallan/vera/issues/1590) | `nat_to_int` of a `@Nat` above i64.MAX is read as negative outside an `@Int` binding, and a Tier-1 `ensures` fails. |
| [#1592](https://github.com/aallan/vera/issues/1592) | A unary negation of a `@Nat` above i64.MAX is unguarded, and a Tier-1 `ensures` fails at run time. |
| [#1598](https://github.com/aallan/vera/issues/1598) | `INT_MIN / -1` has no verifier obligation, so a Tier-1-clean division traps. |
| [#1482](https://github.com/aallan/vera/issues/1482) | `float_to_string` traps on a finite value of magnitude 2^63 or more. |
| [#1483](https://github.com/aallan/vera/issues/1483) | `string_repeat` and `string_pad_*` reduce a size argument modulo 2^32 and return a wrong value. |
| [#1490](https://github.com/aallan/vera/issues/1490) | Four diagnostics, missing visibility among them, carry no error code, and nothing enforces one. |
| [#1494](https://github.com/aallan/vera/issues/1494) | A user function named after a generated runtime symbol (`alloc`, `gc_collect`, `anon_0`) passes check and fails at compile. |
| [#1495](https://github.com/aallan/vera/issues/1495) | A user function named after a prelude function replaces it inside the prelude's own bodies. |
| [#1496](https://github.com/aallan/vera/issues/1496) | An entry-file `data` declaration named after a prelude ADT with a different shape passes check and verify, then fails at compile. |
| [#1498](https://github.com/aallan/vera/issues/1498) | **E608** refuses, at compile, same-named functions that no namespace can name together. |
| [#1499](https://github.com/aallan/vera/issues/1499) | A call to a user ability operation, or a qualified ability call, passes check and verify and fails at compile. |
| [#1500](https://github.com/aallan/vera/issues/1500) | Spec §5.11's `main` signature and `<IO>` requirement is enforced by neither check nor run. |
| [#1502](https://github.com/aallan/vera/issues/1502) | Host-implemented built-ins trap with `host_error` on inputs their signatures accept, and the `Result` ones trap instead of returning `Err`. |
| [#1505](https://github.com/aallan/vera/issues/1505) | Diagnostics render type arguments with `@` (`@Array<@Int>.0`), a spelling that does not parse. |
| [#1506](https://github.com/aallan/vera/issues/1506) | A quantifier predicate whose signature code generation cannot lower passes check and verify, then stops compile with **E699**. |
| [#1510](https://github.com/aallan/vera/issues/1510) | The collector traps when one live structure holds more than 16,384 heap values. |
| [#1512](https://github.com/aallan/vera/issues/1512) | A `State<String>` or `State<Array<T>>` cell passes check and verify, and code generation refuses it (**E607**). |
| [#1514](https://github.com/aallan/vera/issues/1514) | A binder typed through a parameterised alias has no WASM representation, and one case drops `main` silently. |
| [#1515](https://github.com/aallan/vera/issues/1515) | The call site and monomorphization discovery name a nested generic call differently, so the caller is dropped (**E602**). |
| [#1516](https://github.com/aallan/vera/issues/1516) | `apply_fn` on a closure that a call returns passes check and verify, and code generation refuses it (**E616**). |
| [#1517](https://github.com/aallan/vera/issues/1517) | A `@T.result` whose type is not the return type, or is undeclared, verifies. |
| [#1519](https://github.com/aallan/vera/issues/1519) | A generic from a module with an alias named like the caller's type argument compiles to a module that fails to load. |
| [#1522](https://github.com/aallan/vera/issues/1522) | A generic `State<T>` handler nested in a `State<Int>` handler passes check and is dropped at compile when `T` is `Int`. |
| [#1526](https://github.com/aallan/vera/issues/1526) | An escaped exception's quoted `String` can end in U+FFFD at the 64-byte cut. |
| [#1527](https://github.com/aallan/vera/issues/1527) | `check_doc_counts`' CI job-count check never matches `TESTING.md`, so the job count is ungated. |
| [#1540](https://github.com/aallan/vera/issues/1540) | A case missing inside a nested constructor pattern passes the exhaustiveness check, and the match runs a wrong arm. |
| [#1548](https://github.com/aallan/vera/issues/1548) | `show()` and `hash()` of a value typed by an imported signature read the type name through the importer's aliases. |
| [#1549](https://github.com/aallan/vera/issues/1549) | A user function's **E602** is suppressed when its line falls inside a prelude generic's line span. |
| [#1550](https://github.com/aallan/vera/issues/1550) | `show()` and `hash()` of a generic data type's value returned by a generic function are refused (**E602**). |
| [#1552](https://github.com/aallan/vera/issues/1552) | A type alias naming a later alias is registered unresolved, and its uses are refused with errors far from the cause. |
| [#1553](https://github.com/aallan/vera/issues/1553) | A `type` alias named `Decimal` or `Array`, used beside a built-in value of that type, builds a module that fails to load. |
| [#1556](https://github.com/aallan/vera/issues/1556) | A type parameter named `Array` passes check and drops its caller at compile (**E602**). |
| [#1563](https://github.com/aallan/vera/issues/1563) | A refused refined binder also draws a redundant **E501** at a call its refinement satisfies. |
| [#1564](https://github.com/aallan/vera/issues/1564) | Indexing an array literal directly passes check and is dropped at compile (**E602**). |
| [#1567](https://github.com/aallan/vera/issues/1567) | A call inside a callee's `ensures` is checked at each caller, which refuses it with **E501**. |
| [#1570](https://github.com/aallan/vera/issues/1570) | A call precondition in a match arm, a closure, a handler clause or an interpolation raises no obligation. |
| [#1573](https://github.com/aallan/vera/issues/1573) | The `@Nat`-subtraction trap message drops a compound operand's parentheses. |
| [#1575](https://github.com/aallan/vera/issues/1575) | A module generic reached only through another generic's instantiation drops `main` when it calls a private generic sibling. |
| [#1578](https://github.com/aallan/vera/issues/1578) | A match on an `array_fold` call or a pipe passes check and verify, and code generation drops the function (**E602**). |
| [#1580](https://github.com/aallan/vera/issues/1580) | A pipe whose callee returns `@Nat` is never a widening into `@Int`: u64.MAX comes back as -1. |
| [#1584](https://github.com/aallan/vera/issues/1584) | An array literal's elements after the first are never checked against its element type. |
| [#1586](https://github.com/aallan/vera/issues/1586) | A later arm's `@Int` binder guards a `@Nat` that an earlier arm of the same constructor takes, so a valid program traps. |
| [#1589](https://github.com/aallan/vera/issues/1589) | A `@Nat` above i64.MAX bound out of a tuple or constructor pattern into a `@Nat` binder traps as negative. |
| [#1591](https://github.com/aallan/vera/issues/1591) | A `@Nat` sum holding a negative literal part is read as an `@Int` operand with no widening check. |
| [#1593](https://github.com/aallan/vera/issues/1593) | `@Nat.0 + (if b then { 0 - 1 } else { 0 })` traps with a false overflow. |
| [#1594](https://github.com/aallan/vera/issues/1594) | A `Some(Tuple(...))` built from `@Nat` values crashes the verifier with a Z3 sort mismatch (**E699**). |
| [#1595](https://github.com/aallan/vera/issues/1595) | An untranslatable call in a recursive call's argument leaves `decreases` and the precondition at Tier 3, even outside the measure. |
| [#1596](https://github.com/aallan/vera/issues/1596) | `let @Nat = id(0 - 3) + 1` passes verify and is caught only by the runtime guard. |
| [#1597](https://github.com/aallan/vera/issues/1597) | A handler for an effect other than `State` or `Exn` passes check and verify, and code generation drops its function (**E602**). |
| [#1599](https://github.com/aallan/vera/issues/1599) | A pipe as a tuple or constructor component passes check and verify, and code generation drops the function (**E602**). |
| [#1600](https://github.com/aallan/vera/issues/1600) | An entry file importing a module's `data Json` resolves `@Json` to the prelude's type, and a match on the module's constructors is refused (**E311**). |
| [#1601](https://github.com/aallan/vera/issues/1601) | An `assume` over a `let` bound to a user function's result does not reach `ensures`, which is refused (**E500**). |
| [#1602](https://github.com/aallan/vera/issues/1602) | The E506 explanation lists construction positions as unguarded, which they are not since #1426. |
| [#1603](https://github.com/aallan/vera/issues/1603) | Codes E603, E604, E605 and E607 have registry titles that do not match their use, and E604/E605 duplicate E600/E601. |

## Stage 19 — The verification completeness sprint

*`vera verify` tells the whole truth.*

Verification-completeness gaps — an obligation not emitted, a guard not planted — individually small:

| Issue | What |
|---|---|
| [#909](https://github.com/aallan/vera/issues/909) | A value's postcondition / refinement is forgotten through an ADT field (box then unbox loses the fact), degrading provable programs to Tier 3. |
| [#1561](https://github.com/aallan/vera/issues/1561) | A generic function's `decreases` stays Tier 3 when it calls a non-recursive helper, where the monomorphic form is proved. |
| [#1585](https://github.com/aallan/vera/issues/1585) | A generic `where` helper on a recursion cycle with its generic parent leaves its own `decreases` at Tier 3, though the parent's is proved. |
| [#1577](https://github.com/aallan/vera/issues/1577) | An imported generic whose `decreases` measure is one of its module's data types is proved in the module's own run and falls to Tier 3 through an importer. |
| [#1177](https://github.com/aallan/vera/issues/1177) | A parameterized ADT `decreases` measure (`List<Int>`) is ranked at run time through per-instantiation size helpers, so it gets a runtime guard. |
| [#1450](https://github.com/aallan/vera/issues/1450) | The boundary guard composes a refinement over a refined base, so such a type compiles instead of being refused with **E618**. |

## Stage 20 — The single-source sprint

*One fact, one home, drift caught by a gate.*

This stage makes drift-prone consistency classes structural — each gets a generator or a gate, so a doc fact lives in one place and the next consistency pass finds nothing. A gate that doesn't check its own premise is itself drift waiting to happen. Release-process automation rides here too: automation is single-sourcing for process.

Exit criterion: each listed drift class has a generator or a gate, and a release requires no manual tag/publish steps.

| Issue | What |
|---|---|
| [#1344](https://github.com/aallan/vera/issues/1344) | **Single-source registries umbrella** — one typed source of truth for built-ins, diagnostics, and doc mirrors.  The next three rows are its parts, and it is what makes them one campaign rather than three coincidences. |
| [#735](https://github.com/aallan/vera/issues/735) | **Builtin dispatch table** — replace the 475-line `_translate_call` if-chain with a `{name: BuiltinSpec}` table, then have checker registration and the spec §9 tables consume it.  One table, three consumers. |
| [#1342](https://github.com/aallan/vera/issues/1342) | Conformance matrix — generate a construct × phase × target support table, so which constructs `check`, `verify`, and each compile target accept is read off the suite rather than asserted in prose. |
| [#653](https://github.com/aallan/vera/issues/653) | Spec audit for §0.2 / §0.3 design-principle violations — the spec held to its own principles. |
| [#540](https://github.com/aallan/vera/issues/540) | lychee + markdownlint MD051 cross-doc anchor validation. |
| [#1525](https://github.com/aallan/vera/issues/1525) | **Derive each fact once** — a resolved program representation shared by the checker, the verifier and code generation, so no two of them re-derive a fact and disagree. |
| [#1396](https://github.com/aallan/vera/issues/1396) | Spec question: whether a repeated contract clause (two identical `requires`) is refused, warned about or accepted — decide it and state it in the spec. |
| [#1529](https://github.com/aallan/vera/issues/1529) | Each fix PR carries its own CHANGELOG fragment, assembled at release, so fix PRs share no lines. |
| [#1531](https://github.com/aallan/vera/issues/1531) | Close two more ways a CI gate line can exit 0 unseen by the gate-placement test. |
| [#1532](https://github.com/aallan/vera/issues/1532) | Pin the nested refused-constructor search in the #1433 duplicate-name tests. |

## Stage 21 — The effect hardening sprint

*Production controls for the headline effects.*

Before the flagship builds on them, `Http` and `Inference` get the controls real agent workloads need: auth headers, status codes, timeouts and verbs on one side; cost gates, deterministic replays, mocking, and provider breadth on the other.  A second model tier joins the same surface: typed decisions carrying a confidence value ([#1467](https://github.com/aallan/vera/issues/1467)), which begin as a user-declared effect and are promoted to a built-in only once their calibration is measured.  The Http and Inference control rows are current KNOWN_ISSUES limitations; the provider and example rows are supporting work on the same effect surface.

Exit criterion: the Http and Inference limitation rows are retired; an agent can call an authenticated API and mock the model call in tests.

| Issue | What |
|---|---|
| [#351](https://github.com/aallan/vera/issues/351) | Http: custom request headers (`Authorization` is the blocking case). |
| [#352](https://github.com/aallan/vera/issues/352) | Http: status-code access — distinguish a 404 from a 500. |
| [#353](https://github.com/aallan/vera/issues/353) | Http: per-request timeout control. |
| [#356](https://github.com/aallan/vera/issues/356) | Http: PUT / PATCH / DELETE. |
| [#370](https://github.com/aallan/vera/issues/370) | Inference: configurable `max_tokens` / `temperature` — cost gates and deterministic replays. |
| [#372](https://github.com/aallan/vera/issues/372) | Inference: user-defined `handle[Inference]` handlers — mocking, caching, routing. |
| [#1467](https://github.com/aallan/vera/issues/1467) | `Decision` effect — typed probabilistic decisions from System One models: `noul` / `choice` / `score` return a value already in the type system with a `Confidence` refinement, a fast tier beside `Inference` so a function's effect row states what it may spend.  Userland first (a declared effect with a handler over `Http.post`), then a calibration measurement as a hard gate, then promotion to a built-in host effect mirroring `Http` and `DB` with the `async` whitelist entry; a batch `Decision.ask` and handler support follow, the latter decided with #372. |
| [#373](https://github.com/aallan/vera/issues/373) | Host-import `Array<Float64>` returns (`alloc_result_ok_float_array`) — the infrastructure #371 needs. |
| [#371](https://github.com/aallan/vera/issues/371) | `Inference.embed` — vector embeddings, unblocked by #373. |
| [#451](https://github.com/aallan/vera/issues/451) | Provider: Google Gemini. |
| [#1289](https://github.com/aallan/vera/issues/1289) | Provider registry — a model name reaches the toolchain as data rather than a compiler-source edit to `_PROVIDERS`. |
| [#380](https://github.com/aallan/vera/issues/380) | Example: handler mocking for Inference (unblocked by #372). |

## Stage 22 — The verified tool server

*The flagship: an MCP tool server whose tool schemas are compile-time guarantees.*

The thesis demo.  The `<HttpServer>` effect, the WASI Preview 2 target, and its `wasi:http` serve backend shipped in the server-effects sprint (Stage 16); Stage 21 hardens the effects it consumes.  What remains is the `<McpServer>` effect itself, the safety rails a server on untrusted input needs, and the small stdlib surface real tools keep reaching for.

Exit criterion: a working MCP tool server written in Vera, serving contract-verified tools to a real agent, with the demo documented end to end.

| Issue | What |
|---|---|
| [#306](https://github.com/aallan/vera/issues/306) | **`<McpServer>` effect** — verified MCP tool server; contracts guarantee tool schemas at compile time.  The flagship use case. |
| [#239](https://github.com/aallan/vera/issues/239) | Resource limits (fuel, memory, timeout) — essential for untrusted inputs. |
| [#235](https://github.com/aallan/vera/issues/235) | SHA-256 / HMAC — webhook signatures and API authentication patterns. |
| [#233](https://github.com/aallan/vera/issues/233) | Date and time handling beyond `IO.time`. |
| [#236](https://github.com/aallan/vera/issues/236) | CSV parsing and generation. |
| [#440](https://github.com/aallan/vera/issues/440) | `vera test` ADT input generation — tool payloads are ADTs; testing verified tools needs constructor synthesis. |
| [#401](https://github.com/aallan/vera/issues/401) | Static MCP documentation endpoint for Vera itself. |
| [#529](https://github.com/aallan/vera/issues/529) | Use mcp-assert as the test harness for the Vera MCP server. |
| [#329](https://github.com/aallan/vera/issues/329) | Explore Plumbing integration — Vera WASM modules as verified agent tool calls (the exploration item; this sprint is its trigger). |

## Stage 23 — The agent experience sprint

*The loop the model lives in.*

With the flagship standing, invest in the write–verify–fix loop agents actually experience: the language server's remaining seams, the context tools that keep a project inside a token budget, the discoverability surface, and the evidence base — this is where VeraBench's pass@k re-run lands, measuring whether all of the above moved the number.

Exit criterion: the LSP limitation rows are retired, and a fresh VeraBench run (pass@k, current models) is published.

| Issue | What |
|---|---|
| [#724](https://github.com/aallan/vera/issues/724) | LSP: buffer-aware module resolution (imports currently resolve from disk, not open buffers). |
| [#181](https://github.com/aallan/vera/issues/181) | Slot go-to-definition and mechanical slot-index rewriting beyond parameters (`let`/`match` bindings). |
| [#558](https://github.com/aallan/vera/issues/558) | `--explain-slots-at <line>:<col>` — query the slot table at any position, not only where a diagnostic already fires. |
| [#1292](https://github.com/aallan/vera/issues/1292) | LSP: `vera/addEffect` bounds handlers by resolved effect instance, so an alias-spelled `handle[State<MyAlias>]` prunes what `State<Int>` prunes. |
| [#1471](https://github.com/aallan/vera/issues/1471) | **E538** names the premise that contributes the contradiction (an unsat core over the author's premises), not the first `assume`. |
| [#523](https://github.com/aallan/vera/issues/523) | `vera context` — token-budgeted project export for agents. |
| [#698](https://github.com/aallan/vera/issues/698) | `vera shape` — function-archetype histograms per module. |
| [#224](https://github.com/aallan/vera/issues/224) | REPL — the shortest feedback path is currently `vera run` on a file. |
| [#562](https://github.com/aallan/vera/issues/562) | `vera test` advanced features — input shrinking, cross-function scenarios, coverage-guided generation. |
| [#143](https://github.com/aallan/vera/issues/143) | Expand to 50+ examples. |
| [#519](https://github.com/aallan/vera/issues/519) | SKILL.md documentation gap inventory. |
| [#424](https://github.com/aallan/vera/issues/424) | Register veralang.dev with llms.txt directories. |
| [#525](https://github.com/aallan/vera/issues/525) | Close the remaining Agent Score gaps on veralang.dev. |
| [#225](https://github.com/aallan/vera/issues/225) | VeraBench: pass@k evaluation, more models, more tiers — the sprint's measurement. |
| [#1139](https://github.com/aallan/vera/issues/1139) | Formatter internals: parse-time comment ownership and a single recursive renderer, making comment preservation and one-canonical-form structural properties rather than invariants spread across the emitters; retires the remaining relocation cases and the inline/multi-line dual paths. |

## Stage 24 — The browser sprint

*Demos that move.*

The browser seam was deliberately demoted below correctness work (June 2026); it comes due after the flagship.  One suspend/resume mechanism (JSPI) unblocks the three biggest items — sleep-driven animation, async `fetch`, and (with the ANSI interpreter) terminal-style programs rendering unchanged.

Exit criterion: the browser limitation rows are retired and an animated demo runs on veralang.dev.

| Issue | What |
|---|---|
| [#609](https://github.com/aallan/vera/issues/609) | `IO.sleep` via JSPI (or Asyncify fallback) so animations don't freeze the tab; unblocks the browser half of `IO.read_char`. |
| [#355](https://github.com/aallan/vera/issues/355) | Replace sync XHR with `fetch` — every fix option is an async-to-sync bridge, so it shares the JSPI machinery. |
| [#610](https://github.com/aallan/vera/issues/610) | Minimal ANSI-subset interpreter so terminal-style programs render unchanged. |
| [#603](https://github.com/aallan/vera/issues/603) | Export string-marshalling helpers so JS can pass `String` arguments into Vera functions. |

## The horizon

Beyond the staged sprints — grouped by arc, each pulled forward by its trigger, not before.

**Verification depth** — [#427](https://github.com/aallan/vera/issues/427) Tier 2 verification (Z3 with `assert`/lemma hints; its differential oracle — per-monomorphization results from #732 — has shipped, so this is unblocked but outranked), [#439](https://github.com/aallan/vera/issues/439) lifting effect-handler bodies out of Tier 3 (research-grade; approach 3 depends on #427), [#686](https://github.com/aallan/vera/issues/686) `data invariant(...)` clauses (blocked; refinement types are the working alternative).

**Nominal types** — [#1358](https://github.com/aallan/vera/issues/1358) `newtype`: nominal scalar types, checked at use (the issue carries the design, a validation plan and an estimate).

**Testing depth** — [#795](https://github.com/aallan/vera/issues/795) mutation testing beyond the soundness core (needs the full-sweep deadlock on mutmut 3.6 / Python 3.14 resolved first), [#792](https://github.com/aallan/vera/issues/792) feedback-driven hardening for the deep verifier/smt layers, [#170](https://github.com/aallan/vera/issues/170) Hypothesis as `vera test` generation backend (bookmark; trigger is sustained "cannot generate inputs" warnings).

**Concurrency and WASI** — [#406](https://github.com/aallan/vera/issues/406) WASI 0.3 native async (gated on wasmtime-py exposing component async), [#853](https://github.com/aallan/vera/issues/853) extend wasi-p2 beyond IO+Random (Http via `wasi:http` outgoing-handler, streaming filesystem, sockets), [#270](https://github.com/aallan/vera/issues/270) `handle[Async]` scheduling strategies, [#227](https://github.com/aallan/vera/issues/227) timeout/cancellation effects, [#228](https://github.com/aallan/vera/issues/228) WebSocket/SSE, [#770](https://github.com/aallan/vera/issues/770) non-blocking / timed stdin, [#844](https://github.com/aallan/vera/issues/844) advisory diagnostic for shape-unfusable `async` arguments.

**Modules and ecosystem** — [#127](https://github.com/aallan/vera/issues/127) module re-exports, [#130](https://github.com/aallan/vera/issues/130) package system and registry, [#163](https://github.com/aallan/vera/issues/163) standalone WASM runtime package, [#238](https://github.com/aallan/vera/issues/238) Component Model interop, [#56](https://github.com/aallan/vera/issues/56) incremental compilation, [#294](https://github.com/aallan/vera/issues/294) effect row variable unification, [#1469](https://github.com/aallan/vera/issues/1469) reserve the prelude ADT names uniformly, so a redefinition is refused at its declaration rather than where a use of it becomes ambiguous, [#785](https://github.com/aallan/vera/issues/785) GitHits MCP (bookmark; trial at the next dependency-facing milestone).

**Standard library long tail** — [#367](https://github.com/aallan/vera/issues/367) Markdown extractors, [#368](https://github.com/aallan/vera/issues/368) HTML accessors, [#507](https://github.com/aallan/vera/issues/507) ability-dispatched array operations, [#509](https://github.com/aallan/vera/issues/509) Unicode-aware string built-ins phase 2, [#1143](https://github.com/aallan/vera/issues/1143) `<DB>` effect phases 2–3 — named columns (via Map), typed rows (via JSON), and further backends.

**Compiler internals** — [#672](https://github.com/aallan/vera/issues/672) canonical WAT formatter, [#745](https://github.com/aallan/vera/issues/745) narrow the wrap-table / Phase 2c emission to `decimal_ops_used` only, [#739](https://github.com/aallan/vera/issues/739) typed `Protocol` interfaces for the mixin mypy carve-outs, [#1343](https://github.com/aallan/vera/issues/1343) decompose `vera/verifier.py` and `smt.py` around explicit obligation generators and translators — sequenced after the [#1344](https://github.com/aallan/vera/issues/1344) umbrella, whose typed registries the generators are meant to consume.

## Ongoing threads

Not stage-gated; advanced alongside whatever stage is active.

- **VeraBench** ([vera-bench](https://github.com/aallan/vera-bench)) — the suite is its own thread; the compiler-side pass@k re-run is staged as Stage 23's measurement ([#225](https://github.com/aallan/vera/issues/225)).
- **CI, process, and tooling** — [#386](https://github.com/aallan/vera/issues/386) Hypothesis round-trip properties (bookmark), [#712](https://github.com/aallan/vera/issues/712) Codecov → Harness migration watch, [#753](https://github.com/aallan/vera/issues/753) pygls / Python 3.16 watch, [#1126](https://github.com/aallan/vera/issues/1126) z3-solver 5.0 bake period, then re-run the obligation differential, [#1103](https://github.com/aallan/vera/issues/1103) migrate GitHub Pages off legacy branch-deploy to a self-owned Actions workflow, [#1295](https://github.com/aallan/vera/issues/1295) decide whether the four abilities (`Eq`/`Hash`/`Ord`/`Show`) highlight distinctly from ordinary types in the editor grammars, [#1263](https://github.com/aallan/vera/issues/1263) detect `_PROVIDERS` model IDs that a vendor has stopped documenting — every provider test pins the ID to a literal, which catches a registry edit but not rot at the vendor, so the signal needs a network-allowed probe.

## Not doing now

Deliberate trade-offs, recorded so they aren't re-litigated by accident.

- **No typed IR for WAT emission.**  The cost-benefit doesn't clear while string-based emission is held safe by the walker-completeness gate and the planned canonical WAT formatter ([#672](https://github.com/aallan/vera/issues/672)).
- **No parser fuzzing yet** ([#402](https://github.com/aallan/vera/issues/402), bookmark).  Trigger: a parser crash from the wild, or spare CI budget.
- **No full Tier 2 verification yet** ([#427](https://github.com/aallan/vera/issues/427)).  Its old blocker is gone — per-monomorphization verification shipped and provides the differential oracle — but the staged sprints above outrank it; it stays on the horizon by priority, not dependency.

## Speculative

Deferred decisions — features without a current driver, captured so the design analysis isn't re-derived if one shows up.  Promotes into a stage when a real trigger appears.

| Item | Issue | Trigger condition |
|------|-------|-------------------|
| Allow `@Byte` arithmetic with verified underflow + overflow guards | [#564](https://github.com/aallan/vera/issues/564) | A real Vera program (or proposed feature) requires byte arithmetic at the user-code level — e.g., a binary-format parser the stdlib doesn't cover; or VeraBench shows a measurable adoption tax from `byte_to_int` round-trips on byte-heavy benchmarks.  Today: the type checker excludes `Byte` from `NUMERIC_TYPES`, so `@Byte - @Byte` etc. produce E140; the round-trip via `byte_to_int` / `int_to_byte` is the canonical idiom. |
