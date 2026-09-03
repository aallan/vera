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
import vera.math(magnitude, larger);
```

A selective import makes only the named declarations available. Each name in the parenthesised list must refer to a `public` declaration in the imported module. Attempting to import a `private` declaration is an error:

```
Error: Cannot import 'helper' from module 'vera.math': it is private.
```

**Design note.** Vera does not support wildcard exclusion syntax (e.g., `import m hiding(x)`). When a module exports names that conflict with local definitions or other imports, the canonical mechanism is selective import: list exactly the names needed — advice for the local-definition case (§8.5.2), and a requirement for the two-import case (§8.5.2.2). Wildcard exclusion would be a semantic equivalent of selective import — the same import set expressible two ways — violating the one-canonical-form principle (§0.2.3). When wildcard import causes a name clash, the local definition shadows the import (§8.5.2), and the imported version remains accessible via module-qualified call syntax (§8.5.3). Both mechanisms address **function** names. A clashing data type or constructor name is not resolved by either: the flat compilation strategy refuses two modules' same-named data declarations however the importer filters or shadows them (§11.16), so the remedy there is to rename the declaration in one of the source modules (§8.5.2.2).

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
public fn magnitude(@Int -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{
  if @Int.0 < 0 then {
    0 - @Int.0
  } else {
    @Int.0
  }
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
- Type aliases (`type Foo = ...`), effect declarations (`effect E { ... }`), module declarations, and import statements do not take visibility modifiers. These declarations are **module-local** — they are not importable by other modules. If another module needs the same type alias or effect, it must declare its own copy. The prelude's own combinators resolve their closure-parameter types through aliases a program cannot name: those aliases carry reserved names, and a name beginning with `Vera` followed by an uppercase letter or digit is a compile error (**E154**) — whether the program *declares* that name as a type, an alias, an effect, an ability or a constructor, *binds* it as a type parameter, or merely *mentions* it in a type. The reservation is one rule across every namespace, so the prelude's internal namespace can be neither re-typed, shadowed by a binder, nor referenced, and a program that wants a short name for a function type declares its own alias for it. Outside a type position there is no alias escape, so the fix in the effect, ability and constructor namespaces is simply a name that does not start with the reserved prefix. The prelude's data types (`Option`, `Result`, `Ordering`, `UrlParts`, …) are not in that namespace: they are ordinary public declarations a program names, and shadows, like any other. One built-in type name is the exception, and is reserved in the **data** namespace: `Future`, whose semantics the compiler recognises by name throughout code generation — how a value is rendered, compared and laid out — so a declaration of either could not be told apart from the built-in. Declaring one is **E158**, on the same rule that reserves built-in function names (**E151**) and built-in effect names (**E152**). A `type` alias of those names is unaffected: an alias names a binding, not a layout. A declaration in the **entry file** shadows the prelude's for the whole program: the prelude injects nothing under that name, so the entry's declaration never contends with the prelude's. Where a *module* declares the same name as well, the entry's declaration and the module's are a distinct pair, arbitrated by the same shape test: they share the one layout when their shapes match, and the compiler reports **E623** at the entry declaration when they differ (§11.16). A declaration in a **module** shadows it for that module alone only while the prelude is not also compiling its own declaration of that name — the two would otherwise contend for one layout in the flat compiled namespace (§11.16), and the compiler reports **E621** at the module's declaration. Whether they contend is decided by the two declarations' *shapes*: a module that restates the prelude's type — the same constructors, in the same order, with the same field types, type parameters compared by position — shares the one layout and is not a contention. A differently-shaped one is, and the condition differs between the two halves of the prelude's data types: for `Json`, `HtmlNode`, `Request` and `Response`, which the prelude injects only when the entry program uses them, the module's declaration stands alone until it does; for `Option`, `Result`, `Ordering` and `UrlParts`, which every program compiles, a differently-shaped module declaration always contends.
- Functions declared inside `where` blocks are always local to the parent function and do not take visibility modifiers.

### 8.4.2 Data Type Visibility

The same rules apply to `data` declarations:

```
public data Color {
  Red,
  Green,
  Blue
}

private data InternalState {
  Active(Int),
  Idle
}
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

import vera.math(magnitude, larger);

public fn abs_max(@Int, @Int -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{
  magnitude(larger(@Int.0, @Int.1))
}
```

Here, `magnitude` and `larger` resolve to the imported functions from `vera.math`.

### 8.5.2 Shadowing

Local definitions shadow imported declarations. If a module imports `magnitude` from `vera.math` but also defines its own `magnitude`, the local definition takes precedence for bare-call resolution. The import is not an error — it is simply unused for that name.

The shadowing rule is implemented via `setdefault`: imported names are injected into the type environment only if no local definition with the same name already exists.

### 8.5.2.1 Resolution Inside an Imported Module's Body

A module's own bodies resolve in **that module's** namespace: its declarations
plus what it imports (§8.5.1, §8.5.2). This is independent of which program is
compiling it. A bare call inside `mid.vera` names what `mid` can see, never what
the importing program happens to declare.

The importing program's namespace is a different set, and the two need not agree
on a name. A declaration is reachable by its **bare name in the importing
program** only when all three hold:

- it is `public`;
- the importing program's import list admits it (a wildcard import admits every
  public declaration; a selective import admits only the names it lists);
- the importing program does not itself declare that name (§8.5.2 shadowing).

A declaration failing any of these is **qualified-only**: it does not own the
bare name in the importing program. It is still called by bare name from its own
module's bodies, which resolve in their own namespace as above.

Qualified-only is not the same as importer-callable. A module-qualified call
(§8.5.3) reaches a declaration only when it is `public` **and** its module is
imported directly **and** the import list admits the name; the other cases are
rejected rather than routed — a private declaration is `E232`, a name outside the
import list is `E231`, and a module the program does not import at all is not in
scope to qualify. So the only declarations that fail the bare-name predicate and
remain callable by an importer are the public, admitted ones of a directly
imported module that the importer also shadows. Everything else that is
qualified-only — private declarations, names outside the import list, and
everything in a transitively reached module — is reachable only from its own
module's bodies; it is compiled under a module-qualified internal name (§8.9.1)
so that the flattened namespace keeps it distinct, which is a naming rule, not a
call surface.

Two same-named qualified-only declarations in different modules are distinct, and
neither is the importer's.

A module reached only **transitively** (§8.6.4) contributes nothing to the
importing program's namespace, so all of its declarations are qualified-only
there, whatever their visibility.

These are properties of the importer, not of the declaration: the same module,
imported two ways, can have a declaration own the bare name in one program and be
qualified-only in another.

### 8.5.2.2 Two Imports Supplying One Name

§8.5.2 orders a local declaration against an import. Nothing orders two
**imports** against each other. When two of a namespace's imports both supply
the same bare name — each `public`, each admitted by that import's list — and
the namespace declares nothing of that name itself, the bare name names two
declarations and the language chooses neither.

A program **MUST NOT** leave a namespace in that position. The rule covers all
three declaration namespaces, each with its own code:

| Clashing name | Code | Compilation backstop |
|---------------|------|----------------------|
| function | **E155** | E608 |
| data type | **E156** | E609 (differing shapes only) |
| constructor | **E157** | E610 (differing shapes only) |

A constructor is admitted by its parent type's name (§8.5.4), so
`import m(Shape)` supplies `Sq` without naming it, and two modules exporting
differently-named types that share a constructor name clash on the constructor
alone. The three are therefore reported independently.

Each is rejected at check time, in whichever namespace holds the clash: the
entry program's, or any module's, since a module's bodies resolve in their own
namespace (§8.5.2.1) and the rule is a property of that namespace rather than of
the file being compiled. A name the built-in registry or the prelude already
owns is not a clash — the incumbent holds the bare name and the imports never
win it, exactly as a local declaration settles one (§8.5.2).

The refusal is a property of the **import list alone**. It does not require any
body to name the clashing name, and rewriting a call in module-qualified form
does not lift it — qualification disambiguates a call site, while the clash is
in the namespace.

For a clashing **function** name, two resolutions, differing in which
suppliers the namespace can still reach:

- **Selective import** (§8.3.2) — list exactly the names needed, so at most one
  import supplies the clashing name. The other module's declaration of it is
  then outside the import list and unreachable from this namespace (§8.5.2.1).
- **A local declaration** (§8.5.2) — declare the name here. Every bare call is
  then the local one, so the imports no longer compete, and each import's
  declaration remains reachable through the module-qualified form (§8.5.3).

For a clashing **data type** or **constructor** name, neither of those applies.
If the two declarations describe the same layout — the same constructors, in the
same order, with the same field types, type parameters compared by position —
they share one layout in the compiled program and only the check-time ambiguity
has to be resolved. If they describe different layouts, the resolution is to
rename the declaration in one of the two modules: the flat compilation strategy
refuses a differently-shaped pair whatever the importing namespace does with
them (§11.16), so narrowing an import or shadowing the name locally removes the
ambiguity without making the program compile.

Two modules may therefore declare this and share the one compiled layout —
the constructor names, their order and their field types all agree, and the
type parameter's *name* is free because parameters are matched by position:

```
-- in module `shapes`
public data Box<T> {
  Empty,
  Full(T)
}

-- in module `crates`, a compatible restatement
public data Box<U> {
  Empty,
  Full(U)
}
```

while these two describe different layouts — the constructors are reordered,
so the tags differ — and one of them has to be renamed:

```
-- in module `shapes`
public data Box<T> {
  Empty,
  Full(T)
}

-- in module `crates`, an incompatible layout
public data Box<T> {
  Full(T),
  Empty
}
```

**Design note.** The alternative — defining an order, first import wins or last
— was rejected. It would make the resolved declaration implicit in import
sequence, which §0.2.2 excludes, and it would enlarge the valid-program set with
programs whose meaning depends on that sequence, which §0.2.6 excludes. It would
also make a *dependency update* a silent semantic change: a library adding an
export would rebind a downstream namespace's bare call to a different body,
where refusal reports the change at the importer. Refusal is additionally the
reversible choice — an order could still be defined later, giving every refused
program a meaning, whereas retreating from an order to refusal would break
programs that had come to rely on it.

### 8.5.3 Module-Qualified Calls

Vera supports module-qualified function calls using `::` to separate the module path from the function name:

```
vera.math::magnitude(-5)
```

The path portion (`vera.math`) identifies the module using dot separators, and `::` separates the path from the function name (`magnitude`). Arguments follow in parentheses. This syntax can be used anywhere a function call is valid.

The grammar is:

```ebnf
module_call: module_path "::" LOWER_IDENT "(" arg_list? ")"
```

Module-qualified calls always resolve against the specific module's public declarations. They are not affected by local shadowing -- if the importer defines its own `magnitude`, a module-qualified call `vera.math::magnitude(x)` still calls the module's version.

**Design note.** Vera does not support import aliasing (renaming a declaration at the import site). Where two reachable declarations share a name, the module-qualified call syntax (`vera.math::magnitude(x)`) names the one wanted without introducing a second name for the same declaration — for a name a local declaration shadows (§8.5.2), and, together with a local declaration or a selective import, for two imports supplying one name (§8.5.2.2). Aliasing would violate the one-canonical-form principle (§0.2.3): the same function could be referenced by different names in different files, making semantically identical call sites textually distinct.

### 8.5.4 Constructor Resolution

When a `public` data type is imported, its constructors are available as bare names:

```
import vera.collections(List);

-- Nil and Cons are now available
```

Constructor names follow the same shadowing rules as function names: a local
declaration shadows an imported constructor (§8.5.2), and a constructor name two
imports both supply is refused (§8.5.2.2, **E157**) exactly as a function name
is. An imported type's constructors are admitted by the type's name, so a
selective import naming the type admits all of them.

Constructors differ from functions in one respect, and it is a property of
compilation rather than of resolution: what two modules of one program may
share under one `data` name is a LAYOUT, not merely a namespace. Two
declarations describing the same layout — the same constructors, in the same
order, with the same field types, type parameters compared by position — share
the single registered one and compile, and their shared constructor names
compile with them. Two describing different layouts **MUST NOT** both be
declared at all, whatever any namespace imports or shadows (§11.16).

Sharing a layout settles compilation, not scope: where two imports both
supply the bare name, §8.5.2.2's ambiguity refusal applies first and
independently of the layouts, so identical declarations are still E156 /
E157 at check time.

## 8.6 Module Resolution Algorithm

The resolver maps an import path to a source file on disk using a simple file-system-based algorithm.

![Module resolution: path mapping relative to the importer then the project root, a parse cache keyed by module path, an in-progress set that rejects circular imports, and recursive resolution — with transitively reached modules compiled but not visible to the original importer.](../assets/diagrams/module-resolution.svg)

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
- All imported `public` data types, with their constructors.
- All locally declared types and functions (from Pass 1).

A name two imports both supply is the exception, in every one of those namespaces: it is refused (§8.5.2.2) and enters none of them, so a use of it resolves to nothing rather than to whichever supplier was injected first. That holds for a clashing function name (`E155`), a clashing data type name (`E156`) and a clashing constructor name (`E157`) independently — a type excluded for a clash takes its constructors with it, and a constructor name two differently-named types supply is excluded on its own while both types remain.

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
public fn magnitude(@Int -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{
  if @Int.0 < 0 then {
    0 - @Int.0
  } else {
    @Int.0
  }
}
```

A caller in another module can rely on `magnitude(x) >= 0`:

```
import vera.math(magnitude);

public fn non_negative(@Int -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{
  magnitude(@Int.0)
}
```

The verifier proves `non_negative`'s postcondition by assuming `magnitude`'s postcondition (`@Int.result >= 0`).

## 8.9 Cross-Module Compilation

The code generator uses a **flattening** strategy: imported function bodies are compiled into the same WASM module as the importing program. This produces a single self-contained `.wasm` binary.

### 8.9.1 Compilation Process

1. **Pass 0 — Module registration**: For each resolved module, register all function signatures and ADT layouts into the code generator's state. Imported names are injected via `setdefault` so local definitions shadow imports. Type aliases are **not** merged into the shared state: an alias is module-local (§8.4.1), so each module's aliases are captured in a per-module namespace, and that module's declarations compile and register against `{prelude aliases, module's own aliases}` — never against the importing program's. Harvested return-type expressions are canonicalized (alias references substituted) against the defining module's namespace before entering the shared registries. That same per-module namespace is what slot names, slot-reference keys and `State`/`Exn` cell families are rendered against — in the checker, the verifier and the code generator alike — so a declaration is named in the module that declared it, whichever phase is asking.

2. **Pass 2.5 — Imported function compilation**: After compiling local functions (Pass 2), compile all imported function bodies — both public and private — as internal WASM functions. Private helpers must be compiled because imported public functions may call them.

3. **Call desugaring**: `ModuleCall` AST nodes (e.g., `vera.math.magnitude(x)`) are desugared to flat `FnCall` nodes (e.g., `magnitude(x)`) since the imported function exists in the same WASM module.

4. **Qualified-only naming**: flattening puts every module's declarations in one WASM namespace, where a bare name can belong to only one of them. A declaration that owns the importing program's bare name (§8.5.2.1) keeps it; every other module declaration — private, outside the importer's import filter, shadowed by a local, or reached only transitively — is emitted and called under a **module-qualified** name derived from its owning module's path, so two modules' same-named declarations stay distinct. This applies to generic declarations by way of their instantiations: a qualified-only generic's monomorphized clones are named under its owning module, never under the bare name, so an importer's same-named generic and a module's compile to different functions.

5. **Bare calls in imported bodies**: because an imported body resolves in its own module's namespace (§8.5.2.1), a bare call there is compiled against what THAT module sees. Where the callee is qualified-only, the call is compiled to the callee's module-qualified name — including when the callee belongs to a module the body's own module imported, rather than to the body's own module. Without this the flattened bare name would be resolved in the importing program's namespace, and a same-named declaration there would silently be called instead.

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

public fn magnitude(@Int -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{
  if @Int.0 < 0 then {
    0 - @Int.0
  } else {
    @Int.0
  }
}

public fn larger(@Int, @Int -> @Int)
  requires(true)
  ensures(@Int.result >= @Int.0)
  ensures(@Int.result >= @Int.1)
  effects(pure)
{
  if @Int.0 >= @Int.1 then {
    @Int.0
  } else {
    @Int.1
  }
}
```

**`vera/collections.vera`** — generic data types:

```
module vera.collections;

public data List<T> {
  Nil,
  Cons(T, List<T>)
}

public data Option<T> {
  None,
  Some(T)
}
```

**`modules.vera`** — the importing program:

```
module vera.examples.modules;

import vera.math(magnitude, larger);
import vera.collections(List, Option);

public fn clamp_to_range(@Int, @Int, @Int -> @Int)
  requires(@Int.1 <= @Int.0)
  ensures(@Int.result >= @Int.1)
  ensures(@Int.result <= @Int.0)
  effects(pure)
{
  if @Int.2 < @Int.1 then {
    @Int.1
  } else {
    if @Int.2 > @Int.0 then {
      @Int.0
    } else {
      @Int.2
    }
  }
}

public fn abs_max(@Int, @Int -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{
  magnitude(larger(@Int.0, @Int.1))
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

$ vera run examples/modules.vera --fn clamp_to_range -- 10 1 5
5
```

## 8.11 Limitations

The current module system has the following limitations, each tracked as a GitHub issue:

| Limitation | Issue | Notes |
|-----------|-------|-------|
| Two modules may not declare the same `data` name | [#1317](https://github.com/aallan/vera/issues/1317) | The flat namespace's collision rails (§11.16) key on the declarations rather than on what any namespace can name, so neither a selective import, a local declaration (§8.5.2), nor `private` resolves the clash — only renaming in a source module does |
| No re-exports | [#127](https://github.com/aallan/vera/issues/127) | A module cannot re-export declarations imported from other modules |
| No package system | [#130](https://github.com/aallan/vera/issues/130) | Module resolution is file-system-only; no package manager or registry |
