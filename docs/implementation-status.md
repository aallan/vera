<!-- GENERATED FILE — do not edit.
     Source: scripts/build_site.py (build_impl_status).
     Regenerate: python scripts/build_site.py -->

# Implementation Status

Vera's specification describes the language; the reference compiler implements most of it. Where the two stand apart, the chapter says so in a `Status:` callout — usually naming a gap, sometimes recording that a feature has landed. This page collects every one of those callouts — 9 across 5 chapters — so the boundary between what is shipped and what is specified is readable in one place.

Each entry keeps its chapter's wording, including the issue it cites. The specification remains the normative source; this page is an index into it.

## [spec/02-types.md](https://raw.githubusercontent.com/aallan/vera/main/spec/02-types.md)

### 2.4.1 ADT Invariants

**Status: Not yet implemented.** The `invariant(...)` clause on `data` declarations is specified here but is not currently working in the reference compiler — every documented form fails with `[E130] no <DataName> bindings in scope`, because the slot environment for the invariant predicate is not yet wired up.  Tracked in [#686](https://github.com/aallan/vera/issues/686).  Until the implementation lands, refinement types (Section 2.6) are the working alternative for expressing constraints on data values.

## [spec/06-contracts.md](https://raw.githubusercontent.com/aallan/vera/main/spec/06-contracts.md)

### 6.2.3 Invariants (`invariant`)

**Status: Not yet implemented.** The `invariant(...)` clause on `data` declarations is specified here but is not currently working in the reference compiler — every documented form fails with `[E130] no <DataName> bindings in scope`, because the slot environment for the invariant predicate is not yet wired up.  Tracked in [#686](https://github.com/aallan/vera/issues/686).  Until the implementation lands, refinement types (Chapter 2, Section 2.6) are the working alternative for expressing constraints on data values.

### 6.3.2 Additionally Allowed in Contracts (Tier 2)

**Status: Not yet implemented.** Tier 2 (Z3-guided) is specified here but not implemented in the reference compiler. Tracked in [#427](https://github.com/aallan/vera/issues/427). Contracts using these constructs currently fall to Tier 3 (runtime check).

### 6.6 Lemma Functions

**Status: Not yet implemented.** Lemma functions are part of Tier 2 verification ([#427](https://github.com/aallan/vera/issues/427)) and are not yet supported by the reference compiler.

## [spec/07-effects.md](https://raw.githubusercontent.com/aallan/vera/main/spec/07-effects.md)

### 7.5 Effect Handlers

**Status: Not yet implemented.** Code generation compiles handlers only for `State<T>` and `Exn<E>`. A handler for any other effect, a user-declared one included, passes `vera check` and `vera verify`, but the function containing it is dropped at compile time (E602). Tracked in [#1597](https://github.com/aallan/vera/issues/1597).

## [spec/09-standard-library.md](https://raw.githubusercontent.com/aallan/vera/main/spec/09-standard-library.md)

### 9.5.3 Http

**Status: Implemented.** Tracked in [#57](https://github.com/aallan/vera/issues/57). `Http.get` and `Http.post` are fully compilable and execute via host imports (Python `urllib` / a synchronous `XMLHttpRequest` in the browser). Returns `Result<String, String>` — `Ok` with the response body, `Err` with the error message. The conformance test `ch09_http` and the example `http.vera` exercise it.

### 9.6.19 similarity (Future)

**Status: Not yet implemented.** Requires `Inference.embed` (returning `Array<Float64>`) which is deferred to a follow-up release. `Inference.complete` is implemented ([#61](https://github.com/aallan/vera/issues/61)); `embed` is tracked separately ([#371](https://github.com/aallan/vera/issues/371)).

### 9.8 Abilities

**Status: Implemented.** Tracked in [#60](https://github.com/aallan/vera/issues/60). Four built-in abilities (`Eq`, `Ord`, `Hash`, `Show`) are fully compilable. Supported types: Int, Nat, Bool, Float64, String, Byte, Unit. `Eq` derivation is **structural** ([#773](https://github.com/aallan/vera/issues/773)): a simple enum, or an ADT every field of which is itself `Eq` — an `Eq` primitive (`String` included, compared by content) or a nested `Eq` ADT (compared recursively, including recursive types) — supports `Eq` automatically. Fields with no `Eq` semantics (`Array`, `Map`, host handles) make the ADT non-derivable. `Show` and `Hash` derive **structurally** for composite types too ([#911](https://github.com/aallan/vera/issues/911)) — ADT, `Tuple`, `Option`, `Result`, and `Array`, recursing into each field/element by its own `show`/`hash` (see §9.8.2) — including directly-recursive ADTs (`List<T>`, `Tree<T>`), which lower to a generated self-calling helper ([#924](https://github.com/aallan/vera/issues/924)). The built-in `Ordering` ADT (`Less`, `Equal`, `Greater`) is available for `Ord`'s `compare` operation.

## [spec/13-wasi.md](https://raw.githubusercontent.com/aallan/vera/main/spec/13-wasi.md)

### 13.1 Overview

**Status: experimental.**  The target covers the **IO and Random host families** (Section 13.4).  It is not a blanket "WASI 0.2 compliant" mode: a program using any other host family (Http, Map, Set, Decimal, Json, Html, Md, Regex, Math, Inference, DB, State, Async) is rejected with a diagnostic naming the unsupported family — never silently compiled against the core target instead.
