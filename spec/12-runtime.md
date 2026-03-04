# Chapter 12: Runtime and Execution

## 12.1 Overview

Vera programs compile to WebAssembly (WASM) modules and execute in a host runtime. The reference implementation uses [wasmtime](https://wasmtime.dev/) as the WASM engine. The runtime is responsible for:

- Instantiating compiled WASM modules
- Providing host function implementations for effects (`IO`, `State<T>`)
- Managing linear memory (for string constants, heap-allocated ADTs, and arrays)
- Capturing output and state for the caller
- Handling traps and runtime errors

The runtime is deliberately minimal. It provides only what is needed to execute the compiled WASM — there is no garbage collector, no scheduler, and no standard I/O beyond `print`. Future runtime features (networking, async, inference) will extend this model without changing its fundamentals.

## 12.2 WASM Module Structure

A compiled Vera module is a standalone WASM module containing:

### 12.2.1 Exports

Every compilable top-level function is exported by name. The entry point for `vera run` is resolved as follows:

1. If `--fn <name>` is provided, call that function.
2. Otherwise, if a function named `main` exists, call `main`.
3. Otherwise, call the first exported function.

Functions with unsupported parameter or return types (e.g., `String`, `Array<T>` in signatures) are skipped during compilation with a warning — they do not appear in the module's exports.

### 12.2.2 Imports

The module imports host functions for effects that the program uses:

| Import | Signature | Condition |
|--------|-----------|-----------|
| `vera.print` | `(i32, i32) -> ()` | Program uses `IO.print` |
| `vera.state_get_{T}` | `() -> {wasm_t}` | Program uses `State<T>.get` |
| `vera.state_put_{T}` | `({wasm_t}) -> ()` | Program uses `State<T>.put` |

Imports are only emitted when the program actually uses the corresponding effect operations. A pure program produces a module with no imports.

### 12.2.3 Linear Memory

The module exports one page (64 KiB) of linear memory as `"memory"`. The host runtime uses this export to read string data for `IO.print` operations.

For the memory layout, see Section 12.5.

### 12.2.4 Data Section

String constants are stored in the WASM data section at the start of linear memory (offset 0). The string pool deduplicates identical strings. Each string is stored as raw UTF-8 bytes with no null terminator.

For the string pool implementation, see Chapter 11, Section 11.5.

## 12.3 Host Runtime

### 12.3.1 Wasmtime Integration

The reference runtime uses wasmtime's Python bindings. The execution pipeline is:

```
Engine → Module(engine, wat) → Linker(engine) → Store(engine)
  → linker.define_func(...)   [register host functions]
  → linker.instantiate(store, module)
  → instance.exports(store).get(fn_name)
  → func(store, *args)
```

Each execution creates a fresh engine, module, linker, and store. There is no persistent state between invocations.

### 12.3.2 Module Instantiation

The linker resolves all imports before instantiation. If the module imports a host function that the linker has not defined, instantiation fails with an error.

The linker registers host functions before instantiation:
1. `vera.print` — always registered (even if unused, for simplicity).
2. `vera.state_get_{T}` / `vera.state_put_{T}` — registered for each concrete `State<T>` type used by the program.

### 12.3.3 Entry Point Resolution

After instantiation, the runtime resolves the function to call:

1. If `--fn <name>` is specified, look up `name` in the module's exports.
2. Otherwise, look up `main`.
3. Otherwise, use the first export.
4. If no exports exist, raise an error.

Arguments are passed as WASM values. The CLI parses string arguments to integers or floats based on the function's WASM parameter types.

## 12.4 Host Function Bindings

### 12.4.1 IO.print

**Import:** `(import "vera" "print" (func $vera.print (param i32 i32)))`

**Parameters:**
- `ptr` (i32): byte offset into linear memory where the string data begins.
- `len` (i32): length of the string in bytes.

**Behaviour:**
1. Read `len` bytes from linear memory starting at offset `ptr`.
2. Decode the bytes as UTF-8.
3. Write the decoded string to standard output.

The output is captured in a buffer so the caller can inspect it programmatically (e.g., in tests). The `ExecuteResult` returned by `execute()` includes a `stdout` field containing all captured output.

### 12.4.2 State\<T\>

**Imports:** One pair per concrete state type:

```wat
(import "vera" "state_get_Int" (func $vera.state_get_Int (result i64)))
(import "vera" "state_put_Int" (func $vera.state_put_Int (param i64)))
```

**State cells:** The host runtime maintains one mutable cell per concrete `State<T>` type. Cells are initialized to zero (0 for integers, 0.0 for floats). The `execute()` function accepts an optional `initial_state` parameter to override initial values for testing.

**Type mapping:**
| Vera State Type | WASM Type | Default |
|----------------|-----------|---------|
| `State<Int>` | `i64` | `0` |
| `State<Nat>` | `i64` | `0` |
| `State<Bool>` | `i32` | `0` |
| `State<Byte>` | `i32` | `0` |
| `State<Float64>` | `f64` | `0.0` |

**get:** Returns the current value of the state cell.

**put:** Replaces the value of the state cell with the argument.

Multiple independent state types can coexist — each has its own cell and its own pair of host functions.

## 12.5 Memory Model

### 12.5.1 Linear Memory Layout

```
┌──────────────────────────────────┐  offset 0
│  String constants (data section) │
├──────────────────────────────────┤  $heap_ptr (initial)
│  Heap-allocated data             │
│  (ADTs, closures, arrays)        │
│          ↓ grows downward        │
├──────────────────────────────────┤
│  (unused)                        │
└──────────────────────────────────┘  65536 (64 KiB)
```

String constants occupy the lowest addresses. The heap grows upward from the first byte after the string data section.

### 12.5.2 Bump Allocator

The heap uses a bump allocator. A mutable WASM global `$heap_ptr` tracks the next free byte. The internal `$alloc` function:

1. Reads `$heap_ptr`.
2. Aligns the pointer up to the required alignment.
3. Advances `$heap_ptr` by the requested size.
4. Returns the original (aligned) pointer.

The allocator and `$heap_ptr` global are only emitted when the program actually allocates heap data (ADTs, closures, or arrays).

### 12.5.3 Alignment

All heap allocations are 8-byte aligned. This ensures correct access for all WASM value types:

| WASM Type | Size | Alignment |
|-----------|------|-----------|
| `i32` | 4 bytes | 4 bytes |
| `i64` | 8 bytes | 8 bytes |
| `f64` | 8 bytes | 8 bytes |

8-byte alignment satisfies all requirements.

### 12.5.4 No Garbage Collection

> **Limitation.** Tracked in [#51](https://github.com/aallan/vera/issues/51).

The bump allocator does not reclaim memory. Once allocated, heap memory is never freed. This is acceptable for short-lived computations but will not scale to long-running programs.

Future work: a tracing garbage collector or region-based memory management.

## 12.6 Execution Flow

### 12.6.1 Compilation, Instantiation, and Call

The full pipeline from source to result:

```
Source (.vera)
  → parse_file()           Lark parse tree
  → transform()            Typed AST
  → typecheck()            Type diagnostics
  → compile()              CompileResult (WAT + WASM bytes)
  → execute()              ExecuteResult (value + stdout + state)
```

The `compile()` step produces WAT text and assembles it to WASM bytes via `wasmtime.wat2wasm()`. The `execute()` step instantiates the WASM module and calls the specified function.

### 12.6.2 Argument Passing

Arguments are passed to the WASM function as typed values:

- `Int` / `Nat` arguments → `i64` values
- `Bool` / `Byte` arguments → `i32` values
- `Float64` arguments → `f64` values

The CLI (`vera run file.vera --fn f -- 42 3.14`) parses string arguments to the appropriate types. Integer arguments become `i64`; arguments containing a decimal point become `f64`.

### 12.6.3 Return Value Extraction

The raw WASM return value is extracted and returned as a Python `int` or `float`:

- `i64` results → Python `int`
- `i32` results → Python `int`
- `f64` results → Python `float`
- Void results (Unit) → `None`

### 12.6.4 Stdout Capture

All `IO.print` calls during execution write to an in-memory buffer. The buffer contents are returned in `ExecuteResult.stdout`. This allows programmatic inspection of output without interfering with the host process's stdout.

The CLI prints `ExecuteResult.stdout` to the terminal after execution completes. If the function also returns a value, the value is printed after the captured output.

## 12.7 Error Handling

### 12.7.1 WASM Traps

WASM traps are unrecoverable runtime errors. The following conditions cause traps:

| Condition | WASM Instruction | Source |
|-----------|-----------------|--------|
| Integer division by zero | `i64.div_s` | `/` operator on Int |
| Unreachable code | `unreachable` | `assert` failure, bounds check failure |
| Out-of-bounds memory access | `i64.load`, etc. | Invalid pointer dereference |
| Integer overflow (in `i64.div_s`) | — | `Int.min_value / -1` |

When a trap occurs, the wasmtime engine raises a `WasmtimeError` or `Trap` exception. The CLI reports this as a runtime error and exits with a non-zero status.

### 12.7.2 Runtime Contract Violations

Contracts that the verifier could not prove statically (Tier 3) are compiled as runtime assertions. A failed runtime precondition or postcondition executes `unreachable`, causing a WASM trap.

For the contract insertion strategy, see Chapter 11, Section 11.8.

The `assert` expression also compiles to a conditional trap: if the condition is false, the program traps (see Chapter 11, Section 11.14).

### 12.7.3 Array Bounds Checking

Array index expressions are bounds-checked at runtime. If the index is negative or greater than or equal to the array length, the program traps via `unreachable`.

For the bounds checking implementation, see Chapter 11, Section 11.12.

## 12.8 Limitations

The current runtime has the following limitations, each tracked as a GitHub issue:

| Limitation | Issue | Notes |
|-----------|-------|-------|
| No garbage collection | [#51](https://github.com/aallan/vera/issues/51) | Bump allocator only; linear memory is not reclaimed |
| Flat module compilation | [#110](https://github.com/aallan/vera/issues/110) | Imported functions are compiled into the importing module; name collisions are detected (E608/E609/E610); qualified-call disambiguation via name mangling is tracked separately |
