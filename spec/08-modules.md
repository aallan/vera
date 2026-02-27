# Chapter 8: Modules

## 8.1 Overview

Vera supports a file-based module system. Each `.vera` file is a module. Modules declare their identity, import declarations from other modules, and control which of their own declarations are visible to importers.

The module system provides:

1. **Module identity**: a dotted path that names the module.
2. **Imports**: selective or wildcard import of declarations from other modules.
3. **Visibility**: `public` and `private` access control on functions and data types.
4. **Resolution**: a file-system-based algorithm that maps import paths to source files.
5. **Cross-module type checking**: imported declarations are registered in the type environment for bare-call lookup.
6. **Cross-module verification**: imported function contracts are available to the SMT solver at call sites.
7. **Cross-module compilation**: imported function bodies are flattened into the importing module's WASM binary.

## 8.2 Module Declaration

Every module may optionally declare its identity with a `module` statement at the top of the file:

```
module vera.math;
```

The module path is a dot-separated sequence of lowercase identifiers. The path conventionally mirrors the file's location on disk relative to the project root (e.g., `vera.math` corresponds to `vera/math.vera`), but this is not enforced.

The grammar for module declarations is:

```ebnf
module_decl: MODULE module_path SEMICOLON
module_path: LOWER_IDENT (DOT LOWER_IDENT)*
```

The module declaration must appear before any import declarations or top-level definitions. A file without a module declaration is still a valid module — it is treated as an anonymous module.

## 8.3 Import Declarations

A module imports declarations from other modules using `import` statements:

```
import vera.math;
import vera.collections(List, Option);
```

Import declarations appear after the module declaration (if any) and before any top-level definitions. There are two forms:

### 8.3.1 Wildcard Import

```
import vera.math;
```

A wildcard import makes all `public` declarations from the imported module available in the importing module. No parenthesised name list is given.

### 8.3.2 Selective Import

```
import vera.math(abs, max);
```

A selective import makes only the named declarations available. Each name in the parenthesised list must refer to a `public` declaration in the imported module. Attempting to import a `private` declaration is an error:

```
Error: Cannot import 'helper' from module 'vera.math': it is private.
```

### 8.3.3 Grammar

```ebnf
import_decl: IMPORT module_path import_list? SEMICOLON
import_list: LPAREN import_name (COMMA import_name)* RPAREN
import_name: LOWER_IDENT | UPPER_IDENT
```

Import names can be lowercase (functions) or uppercase (data type names). Importing a data type also makes its constructors available.

## 8.4 Visibility

Every top-level `fn` and `data` declaration must have an explicit visibility modifier: `public` or `private`. Omitting the modifier is a compile error.

```
public fn abs(@Int -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{
  if @Int.0 < 0 then { 0 - @Int.0 } else { @Int.0 }
}

private fn helper(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0 + 1
}
```

### 8.4.1 Visibility Rules

- `public` declarations are visible to any module that imports them.
- `private` declarations are visible only within the module that defines them.
- Type aliases (`type Foo = ...`), effect declarations (`effect E { ... }`), module declarations, and import statements do not take visibility modifiers. These declarations are **module-local** — they are not importable by other modules. If another module needs the same type alias or effect, it must declare its own copy.
- Functions declared inside `where` blocks are always local to the parent function and do not take visibility modifiers.

### 8.4.2 Data Type Visibility

The same rules apply to `data` declarations:

```
public data Color { Red, Green, Blue }
private data InternalState { Active(Int), Idle }
```

When a `public` data type is imported, all of its constructors are also available. A `private` data type's constructors cannot be accessed from outside the module.

### 8.4.3 Generic Declarations

For generic functions, the visibility modifier precedes `forall`:

```
public forall<T> fn identity(@T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{
  @T.0
}
```

## 8.5 Name Resolution

### 8.5.1 Bare Calls

Imported declarations are available as **bare calls** — the importer does not need to qualify the name with the module path:

```
module vera.examples.modules;

import vera.math(abs, max);

public fn abs_max(@Int, @Int -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{
  abs(max(@Int.0, @Int.1))
}
```

Here, `abs` and `max` resolve to the imported functions from `vera.math`.

### 8.5.2 Shadowing

Local definitions shadow imported declarations. If a module imports `abs` from `vera.math` but also defines its own `abs`, the local definition takes precedence for bare-call resolution. The import is not an error — it is simply unused for that name.

The shadowing rule is implemented via `setdefault`: imported names are injected into the type environment only if no local definition with the same name already exists.

### 8.5.3 Module-Qualified Calls

Vera's grammar defines a `ModuleCall` syntax for module-qualified function calls:

```
vera.math.abs(-5)
```

The path portion (`vera.math`) identifies the module and the final segment (`abs`) identifies the function. This syntax is defined in the grammar and the AST but is currently limited by an LALR parser ambiguity ([#95](https://github.com/aallan/vera/issues/95)). Use bare calls (Section 8.5.1) instead.

### 8.5.4 Constructor Resolution

When a `public` data type is imported, its constructors are available as bare names:

```
import vera.collections(List);

-- Nil and Cons are now available
```

Constructor names follow the same shadowing rules as function names.

## 8.6 Module Resolution Algorithm

The resolver maps an import path to a source file on disk using a simple file-system-based algorithm.

### 8.6.1 Path Mapping

Given an import path like `vera.math`:

1. Convert the dotted path to directory separators and append `.vera`:
   `vera.math` becomes `vera/math.vera`

2. Try to find the file relative to the importing file's parent directory.

3. If the importing file's parent differs from the project root, also try relative to the project root.

For example, if `examples/modules.vera` imports `vera.math`, the resolver looks for:
- `examples/vera/math.vera` (relative to importing file)
- `vera/math.vera` (relative to project root)

### 8.6.2 Caching

Each resolved module is parsed and transformed exactly once. Subsequent imports of the same module path return the cached result. The cache key is the module path tuple (e.g., `("vera", "math")`).

### 8.6.3 Circular Import Detection

The resolver tracks modules that are currently being resolved (in-progress set). If a module is encountered while it is already in progress, a circular import error is reported:

```
Error: Circular import detected: 'vera.math' is already being resolved.
```

Circular imports are not allowed. The dependency graph must be acyclic.

### 8.6.4 Transitive Resolution

When a module is resolved, its own imports are also resolved recursively. This means importing module A, which imports module B, will resolve both A and B. However, declarations from B are not transitively visible to the original importer — only A's public declarations are available.

### 8.6.5 Resolution Errors

If the resolver cannot find a file for an import path, a diagnostic is emitted:

```
Error: Cannot resolve import 'vera.missing': no file found.
  Looked for 'vera/missing.vera' relative to the importing file and project root.
  Fix: Create the file 'vera/missing.vera' or check the import path.
```

If parsing the resolved file fails, the parse error is reported as a resolution diagnostic with the import location.

## 8.7 Cross-Module Type Checking

When a program has imports, the type checker performs an additional registration pass before checking the main program.

### 8.7.1 Module Registration

For each resolved module:

1. Create a temporary type checker instance with the module's source.
2. Run the registration pass (Pass 1) to populate the temporary type environment with all of the module's declarations.
3. Harvest the registered declarations, excluding built-in names.
4. Filter to `public` declarations only.
5. Check that selective imports do not reference `private` names.
6. Inject the filtered declarations into the main program's type environment using `setdefault` (so local definitions shadow imports).

This is Pass 0 of the three-pass type-checking architecture (see Chapter 5).

### 8.7.2 Type Environment Injection

After module registration, the main type environment contains:

- All built-in types and functions.
- All imported `public` functions (with their full signatures and contracts).
- All imported `public` data types (with their constructors).
- All locally declared types and functions (from Pass 1).

Local declarations always take priority over imported declarations due to the `setdefault` injection order: imports are injected first, then local registration overwrites any collisions.

### 8.7.3 Per-Module Dictionaries

The checker maintains per-module dictionaries of all declarations (both public and private) for two purposes:

- **Module-qualified call lookup**: `ModuleCall` nodes look up the function in the specific module's public dictionary.
- **Better error messages**: when a selective import names a private declaration, the checker can report "it is private" rather than "not found".

## 8.8 Cross-Module Verification

The contract verifier extends the same module registration pattern to make imported function contracts available during SMT verification.

### 8.8.1 Contract Availability

When the verifier encounters a call to an imported function:

- The function's **preconditions** are checked at the call site: the verifier must prove that the arguments satisfy the imported function's `requires()` clauses.
- The function's **postconditions** are assumed: the verifier uses the imported function's `ensures()` clauses as axioms when reasoning about the call result.

This is the standard modular verification approach: each module verifies its own function bodies, and callers rely on the declared contracts.

### 8.8.2 Example

Given an imported function:

```
public fn abs(@Int -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{
  if @Int.0 < 0 then { 0 - @Int.0 } else { @Int.0 }
}
```

A caller in another module can rely on `abs(x) >= 0`:

```
import vera.math(abs);

public fn non_negative(@Int -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{
  abs(@Int.0)
}
```

The verifier proves `non_negative`'s postcondition by assuming `abs`'s postcondition (`@Int.result >= 0`).

## 8.9 Cross-Module Compilation

The code generator uses a **flattening** strategy: imported function bodies are compiled into the same WASM module as the importing program. This produces a single self-contained `.wasm` binary.

### 8.9.1 Compilation Process

1. **Pass 0 — Module registration**: For each resolved module, register all function signatures, ADT layouts, and type aliases into the code generator's state. Imported names are injected via `setdefault` so local definitions shadow imports.

2. **Pass 2.5 — Imported function compilation**: After compiling local functions (Pass 2), compile all imported function bodies — both public and private — as internal WASM functions. Private helpers must be compiled because imported public functions may call them.

3. **Call desugaring**: `ModuleCall` AST nodes (e.g., `vera.math.abs(x)`) are desugared to flat `FnCall` nodes (e.g., `abs(x)`) since the imported function exists in the same WASM module.

### 8.9.2 Export Rules

Imported functions are **not** exported from the WASM module. Only the importing program's `public` functions are WASM exports. An imported public function is internal to the compiled binary — it exists as a callable helper but is not externally visible.

### 8.9.3 Guard Rail

The code generator maintains a guard rail that detects calls to undefined functions. After module registration populates the known-function set, the guard rail only flags truly unknown calls — imported functions are recognised as known.

If a function call cannot be resolved against either local definitions or imported modules, the guard rail reports:

```
Error: Function 'foo' is not defined in this module and was not found in any imported module.
```

## 8.10 Complete Example

A complete multi-module example demonstrating all features:

**`vera/math.vera`** — a utility module:

```
module vera.math;

public fn abs(@Int -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{
  if @Int.0 < 0 then { 0 - @Int.0 } else { @Int.0 }
}

public fn max(@Int, @Int -> @Int)
  requires(true)
  ensures(@Int.result >= @Int.0)
  ensures(@Int.result >= @Int.1)
  effects(pure)
{
  if @Int.0 >= @Int.1 then { @Int.0 } else { @Int.1 }
}
```

**`vera/collections.vera`** — generic data types:

```
module vera.collections;

public data List<T> { Nil, Cons(T, List<T>) }

public data Option<T> { None, Some(T) }
```

**`modules.vera`** — the importing program:

```
module vera.examples.modules;

import vera.math(abs, max);
import vera.collections(List, Option);

public fn clamp(@Int, @Int, @Int -> @Int)
  requires(@Int.1 <= @Int.2)
  ensures(@Int.result >= @Int.1)
  ensures(@Int.result <= @Int.2)
  effects(pure)
{
  if @Int.0 < @Int.1 then {
    @Int.1
  } else {
    if @Int.0 > @Int.2 then {
      @Int.2
    } else {
      @Int.0
    }
  }
}

public fn abs_max(@Int, @Int -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{
  abs(max(@Int.0, @Int.1))
}

private fn helper(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0 + 1
}
```

Running this program:

```
$ vera check examples/modules.vera
OK: examples/modules.vera

$ vera verify examples/modules.vera
OK: examples/modules.vera

$ vera run examples/modules.vera --fn abs_max -- -3 -5
3

$ vera run examples/modules.vera --fn clamp -- 10 1 5
5
```

## 8.11 Limitations

The current module system has the following limitations, each tracked as a GitHub issue:

| Limitation | Issue | Notes |
|-----------|-------|-------|
| Module-qualified call syntax | [#95](https://github.com/aallan/vera/issues/95) | LALR grammar limitation prevents parsing `path.fn(args)` — use bare calls |
| Name collision in flat compilation | [#110](https://github.com/aallan/vera/issues/110) | If two imported modules define functions with the same name, the flat namespace may collide |
| No re-exports | — | A module cannot re-export declarations imported from other modules |
| No wildcard exclusion | — | Cannot import all names except specific ones |
| No import aliasing | — | Cannot rename imported declarations (e.g., `import m(abs as absolute)`) |
| No package system | — | Module resolution is file-system-only; no package manager or registry |
