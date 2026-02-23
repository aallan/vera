# Chapter 11: Compilation Model

## 11.1 Overview

Vera programs compile to WebAssembly (WASM). The compilation pipeline extends the verification pipeline: after parsing, transformation, type checking, and contract verification, the code generator translates the verified AST into a WASM module.

```
Source (.vera)
  │
  ├── Parse        → Lark parse tree
  ├── Transform    → Typed AST
  ├── Type Check   → Diagnostics
  ├── Verify       → VerifyResult (Tier 1/3 classification)
  └── Compile      → CompileResult (WAT text + WASM binary)
```

The compilation target is a standalone WASM module containing:
- Exported functions (callable from the host or other modules)
- A linear memory segment (for string constants and future heap allocation)
- Imported host functions (for IO operations)
- An optional data section (for string literals)

## 11.2 Type Mapping

Vera types map to WASM value types as follows:

| Vera Type | WASM Type | Notes |
|-----------|-----------|-------|
| `Int` | `i64` | 64-bit signed integer |
| `Nat` | `i64` | Non-negativity enforced by contracts, not by WASM type |
| `Bool` | `i32` | `0` = `false`, `1` = `true` |
| `Unit` | *(none)* | Functions returning `Unit` have no WASM result type |
| `String` | `i32, i32` | Pointer and length pair (UTF-8 bytes in linear memory) |

Types not in this table (ADTs, arrays, closures, generic type variables) are not yet compilable. Functions using non-compilable types are skipped with a warning.

### 11.2.1 Nat as i64

`Nat` and `Int` share the same WASM representation (`i64`). The non-negativity invariant of `Nat` is enforced by the contract system (preconditions, postconditions), not by the WASM type. This avoids the overhead of runtime range checks on every arithmetic operation while maintaining the correctness guarantee through verification.

### 11.2.2 Unit as Void

Functions with return type `Unit` compile to WASM functions with no result type. The caller does not receive a return value. This matches WASM's native support for void functions and avoids allocating a dummy return value.

### 11.2.3 String Representation

String values are pairs `(ptr: i32, len: i32)` where `ptr` is a byte offset into linear memory and `len` is the length in bytes. String constants are stored in the WASM data section (see Section 11.5).

## 11.3 Expression Compilation

Each AST expression node compiles to a sequence of WASM instructions that leaves the result on the operand stack.

### 11.3.1 Literals

| Expression | WASM Output |
|------------|-------------|
| `IntLit(42)` | `i64.const 42` |
| `BoolLit(true)` | `i32.const 1` |
| `BoolLit(false)` | `i32.const 0` |
| `UnitLit` | *(nothing)* |
| `StringLit("hello")` | `i32.const <offset>  i32.const <length>` |

### 11.3.2 Slot References

`SlotRef(@T.n)` compiles to `local.get $N`, where `$N` is the WASM local index corresponding to the De Bruijn reference. The code generator maintains a `WasmSlotEnv` that maps typed De Bruijn indices to WASM local indices, mirroring the `SlotEnv` used by the SMT translation layer.

### 11.3.3 Arithmetic and Comparison

Binary operators compile to their WASM equivalents:

| Operator | Int/Nat (i64) | Bool (i32) |
|----------|---------------|------------|
| `+` | `i64.add` | — |
| `-` | `i64.sub` | — |
| `*` | `i64.mul` | — |
| `/` | `i64.div_s` | — |
| `%` | `i64.rem_s` | — |
| `==` | `i64.eq` | `i32.eq` |
| `!=` | `i64.ne` | `i32.ne` |
| `<` | `i64.lt_s` | `i32.lt_s` |
| `>` | `i64.gt_s` | `i32.gt_s` |
| `<=` | `i64.le_s` | `i32.le_s` |
| `>=` | `i64.ge_s` | `i32.ge_s` |
| `&&` | — | `i32.and` |
| `\|\|` | — | `i32.or` |

Unary operators:

| Operator | WASM Output |
|----------|-------------|
| `-` (negation) | `i64.const 0  [expr]  i64.sub` |
| `!` (Boolean not) | `[expr]  i32.eqz` |

The implies operator `==>` is lowered to `(!a) || b`:

```
[left]  i32.eqz  [right]  i32.or
```

### 11.3.4 Comparison Type Awareness

When both operands of a comparison are `Bool` (i32), the compiler uses `i32` comparison instructions instead of `i64`. The operand type is inferred from the AST node type (literals, slot reference type names, result references). This avoids type mismatches in WASM validation.

### 11.3.5 Control Flow

`IfExpr` compiles to a WASM structured `if/else`:

```
[condition]
if (result <type>)
  [then_branch]
else
  [else_branch]
end
```

If both branches have type `Unit`, the `(result ...)` annotation is omitted.

### 11.3.6 Let Bindings and Blocks

`LetStmt` allocates a new WASM local, evaluates the initialiser, and stores it:

```
[initialiser]
local.set $N
```

The new local is registered in the `WasmSlotEnv` so subsequent `SlotRef` nodes resolve to the correct local index.

`Block` compiles each statement sequentially, then compiles the final expression. `ExprStmt` (side-effect statements like `IO.print(...)`) compile the expression and add `drop` if it produces a value.

### 11.3.7 Function Calls

`FnCall(name, args)` compiles to:

```
[arg0] [arg1] ... [argN]
call $name
```

Arguments are evaluated left to right onto the stack, then the function is called. Recursive calls work naturally since WASM supports calling functions by name within the same module.

`QualifiedCall(IO, print, args)` compiles to a call to the corresponding host import:

```
[args]
call $vera.print
```

## 11.4 Function Compilation

### 11.4.1 Compilable Subset

A function is compilable if:

1. All parameter and return types map to WASM primitives (Section 11.2)
2. The function body uses only supported expression types
3. Effects are either `pure` or `<IO>`

Functions that fail any of these criteria are skipped with a diagnostic warning. This is analogous to the verifier's Tier 3 classification — the compiler degrades gracefully rather than failing.

### 11.4.2 Two-Pass Compilation

The code generator uses a two-pass approach:

**Pass 1 (Registration):** Walk all declarations and register compilable functions. This makes all function names available for forward references and mutual recursion.

**Pass 2 (Compilation):** For each registered function, compile the body to WASM instructions. Allocate locals, translate the body, and emit the function definition.

### 11.4.3 Where-Block Functions

Functions declared in `where` blocks are compiled as module-level WASM functions alongside the parent function. They are visible to the parent function and to each other (supporting mutual recursion within the where block).

### 11.4.4 Exported Functions

All compiled top-level functions are exported from the WASM module. Where-block functions are internal (not exported).

## 11.5 String Pool

String literals are stored in the WASM data section. A `StringPool` tracks all string constants encountered during compilation and assigns each a unique `(offset, length)` pair.

Identical strings are deduplicated — if the same string literal appears multiple times, it is stored once in the data section and both references share the same offset.

The data section is emitted as:

```wat
(data (i32.const 0) "Hello, World!Goodbye")
```

All strings are concatenated into a single data segment starting at offset 0. Each `StringLit` compiles to `i32.const <offset>  i32.const <length>`, pushing the pointer and length onto the stack.

## 11.6 Linear Memory

The WASM module exports one page (64 KiB) of linear memory as `"memory"`. This memory holds:

- **String constants** (data section, starting at offset 0)
- **Future:** heap-allocated data (ADTs, arrays, closures)

The memory is exported so the host runtime can read string data for IO operations.

## 11.7 IO Host Bindings

The `IO` effect is implemented via host imports. The WASM module imports:

```wat
(import "vera" "print" (func $vera.print (param i32 i32)))
```

The host runtime (wasmtime) provides the implementation:

1. Read `length` bytes from linear memory starting at `offset`
2. Decode as UTF-8
3. Print to stdout

This means `IO.print("Hello")` compiles to pushing the string's offset and length, then calling the imported host function. The effect system ensures only functions declaring `effects(<IO>)` can call `IO.print`.

## 11.8 Runtime Contract Insertion

Contracts that the verifier proved (Tier 1) are omitted from the compiled output — they are statically guaranteed and need no runtime check.

Contracts that the verifier could not prove (Tier 3) are compiled as runtime assertions.

### 11.8.1 Trivial Contract Elimination

Contracts of the form `requires(true)` and `ensures(true)` are detected syntactically and produce no runtime code. These are the most common contracts in practice (used when the programmer has no meaningful precondition or postcondition to state).

### 11.8.2 Precondition Checks

Non-trivial `requires` clauses compile to checks at function entry:

```wat
;; requires(@Int.0 > 0)
local.get $param0
i64.const 0
i64.gt_s
i32.eqz
if
  unreachable    ;; trap: precondition violated
end
```

The precondition expression is compiled to a Boolean value. If it is false (`i32.eqz`), the function traps via `unreachable`.

### 11.8.3 Postcondition Checks

Non-trivial `ensures` clauses compile to checks after the function body:

```wat
;; body computes result
[body]
local.set $result    ;; store result in temp local
;; ensures(@Int.result > 0)
local.get $result
i64.const 0
i64.gt_s
i32.eqz
if
  unreachable    ;; trap: postcondition violated
end
local.get $result    ;; push result back for return
```

The body's return value is stored in a temporary local. The `@T.result` reference in the ensures clause resolves to this local. After the check passes, the result is pushed back onto the stack for return.

### 11.8.4 Trap Handling

When a runtime contract check fails, the WASM `unreachable` instruction causes a trap. The host runtime catches the trap and reports it as a contract violation.

## 11.9 CLI Commands

### 11.9.1 `vera compile`

```
vera compile <file.vera>
```

Runs the full pipeline (parse → typecheck → verify → compile) and writes a `.wasm` binary file.

Flags:
- `--wat` — print WAT text to stdout instead of writing binary
- `--json` — JSON output with diagnostics and compilation summary
- `-o <path>` — specify output file path (default: same name with `.wasm` extension)

### 11.9.2 `vera run`

```
vera run <file.vera>
```

Runs the full pipeline through execution. Compiles the program, instantiates it with wasmtime, and calls the entry function.

Flags:
- `--fn <name>` — function to call (default: `main`)
- `--json` — JSON output with result, stdout capture, and diagnostics
- Arguments after `--` are passed to the function (parsed as integers)

## 11.10 Limitations

The current compilation model has the following limitations, each tracked as a GitHub issue:

| Limitation | Issue | Notes |
|-----------|-------|-------|
| No Float64 codegen | [#25](https://github.com/aallan/vera/issues/25) | Straightforward i64 → f64 extension |
| No ADT / match codegen | [#26](https://github.com/aallan/vera/issues/26) | Needs tagged union representation in linear memory |
| No closure / anonymous function codegen | [#27](https://github.com/aallan/vera/issues/27) | Needs closure conversion pass |
| No effect handler codegen | [#28](https://github.com/aallan/vera/issues/28) | Needs continuation-passing transform |
| No generic function codegen | [#29](https://github.com/aallan/vera/issues/29) | Needs monomorphization or type erasure |
| No Byte type codegen | [#30](https://github.com/aallan/vera/issues/30) | Needs linear memory byte operations |
| No module-level code generation | — | Each file compiles independently |
| No garbage collection | — | Linear memory is not reclaimed |
| String constants only | — | No dynamic string construction |
