// vera-runtime.mjs — Browser/Node.js runtime for compiled Vera WASM modules.
//
// Provides JavaScript implementations of every WASM host import that the
// Python/wasmtime reference runtime provides (vera/codegen/api.py).
// A single file, zero dependencies, works with ANY compiled Vera program.
//
// Usage (browser):
//   import init, { call, getStdout } from './vera-runtime.mjs';
//   await init('./module.wasm');
//   call('main');
//   console.log(getStdout());
//
// Usage (Node.js):
//   import { initFromBytes, call, getStdout } from './vera-runtime.mjs';
//   import { readFileSync } from 'fs';
//   await initFromBytes(readFileSync('./module.wasm'));
//   call('main');
//
// Architecture:
//   init() introspects the WASM module's imports via WebAssembly.Module.imports()
//   and dynamically builds the import object.  Only bindings for imports the
//   module actually declares are registered.  State<T> types are pattern-matched
//   from state_get_*/state_put_* import names.
//
// CRITICAL: Never cache TypedArray views across WASM calls — memory.buffer
// can detach on memory.grow.  Always re-read memory.buffer before each access.

// ---------------------------------------------------------------------------
// Module state (singleton)
// ---------------------------------------------------------------------------

let wasm = null;       // WebAssembly instance exports
let stdoutBuf = '';    // Captured IO.print output
let stderrBuf = '';    // Captured IO.stderr output (#463)
let lastViolation = ''; // Last contract violation message
let lastOverflow = false; // #808: #798 integer-overflow guard fired this call
const stateCells = {}; // State<T> stacks: { TypeName: [value, ...] } — top is [-1]
// #920: the WASM value type (`i32`/`i64`/`f64`) of each State<T> cell, keyed
// by the mangled type suffix — the SAME key as `stateCells`.  Populated from
// the module's own `state_*` import declarations in `buildImportObject`, this
// is the authoritative scalar-vs-pointer distinction the default cell value
// must respect (see `stateDefaultFor`).
const stateWasmTypes = {};
let stdinQueue = [];   // Pre-queued input lines for IO.read_line
let cliArgs = [];      // Command-line arguments for IO.args
let envVars = {};      // Environment variables for IO.get_env
let exitCode = null;   // Set by IO.exit

// ``ignoreBOM: true`` means "do not treat a leading U+FEFF specially",
// which is the opposite of what the name suggests and the only setting
// that reads a Vera string back unchanged (#1303 review).  The default
// (false) REMOVES a BOM at the start of the buffer, so every string
// whose first character was U+FEFF lost it crossing into the host:
// `IO.print` dropped it, `json_parse` silently accepted a
// BOM-prefixed document the reference host refuses, and
// `decimal_from_string` accepted a BOM-padded decimal.  These bytes are
// a string payload, not a document with an encoding signature — the
// reference host's ``safe_utf8_decode`` never strips one.
const decoder = new TextDecoder('utf-8', { ignoreBOM: true });
const encoder = new TextEncoder();

// ---------------------------------------------------------------------------
// Memory access helpers
// ---------------------------------------------------------------------------

/** Get the WASM linear memory (never cache the buffer). */
function mem() {
  return wasm.memory;
}

/** Read a UTF-8 string from WASM memory. */
function readString(ptr, len) {
  if (len === 0) return '';
  return decoder.decode(new Uint8Array(mem().buffer, ptr, len));
}

/** Write raw bytes into WASM memory at the given offset. */
function writeBytes(offset, data) {
  new Uint8Array(mem().buffer, offset, data.length).set(data);
}

/** Write a little-endian i32 into WASM memory. */
function writeI32(offset, value) {
  new DataView(mem().buffer).setInt32(offset, value | 0, true);
}

/** Read a little-endian i32 from WASM memory. */
function readI32(offset) {
  return new DataView(mem().buffer).getInt32(offset, true);
}

/** Write a little-endian i64 into WASM memory. */
function writeI64(offset, value) {
  new DataView(mem().buffer).setBigInt64(offset, BigInt(value), true);
}

/** Read a little-endian i64 from WASM memory. */
function readI64(offset) {
  return new DataView(mem().buffer).getBigInt64(offset, true);
}

/** Write a little-endian f64 into WASM memory. */
function writeF64(offset, value) {
  new DataView(mem().buffer).setFloat64(offset, value, true);
}

/** Read a little-endian f64 from WASM memory. */
function readF64(offset) {
  return new DataView(mem().buffer).getFloat64(offset, true);
}

/** Call the exported $alloc to allocate WASM heap memory. */
function alloc(size) {
  return wasm.alloc(size);
}

/** Allocate a UTF-8 string in WASM memory; returns [ptr, len]. */
function allocString(str) {
  const encoded = encoder.encode(str);
  if (encoded.length === 0) return [0, 0];
  const ptr = alloc(encoded.length);
  writeBytes(ptr, encoded);
  return [ptr, encoded.length];
}

// ---------------------------------------------------------------------------
// ADT allocation helpers (mirror api.py _alloc_result_*, _alloc_option_*)
// ---------------------------------------------------------------------------

/**
 * Root a freshly-allocated WASM heap pointer on the GC shadow stack
 * across fn(), then pop it.  No-op when the module has no GC
 * infrastructure (then $alloc never collects, so nothing can sweep ptr)
 * or when ptr is 0 (the GC's "not a heap object" sentinel).  Mirrors the
 * CLI _ShadowGuard discipline for host-side ADT builders; folded into
 * #706 to close a pre-existing rooting gap in these helpers.
 */
function gcRooted(ptr, fn) {
  if (ptr === 0 || !wasm || !wasm.gc_sp || !wasm.gc_stack_limit) {
    return fn();
  }
  const sp = wasm.gc_sp.value;
  // #860, following #791: slot-complete bound.  The write below is FOUR
  // bytes at [sp..sp+3], so an sp with 1-3 bytes of headroom passed
  // `sp >= limit` and then spilled past the window.  Unreachable while
  // generated code advances $gc_sp in 4-byte steps from a 4-aligned base
  // — defence in depth, matching the CLI `_ShadowGuard.push` predicate.
  if (sp < 0 || sp + 4 > wasm.gc_stack_limit.value) {
    throw new Error('GC shadow stack overflow in browser runtime (gcRooted)');
  }
  writeI32(sp, ptr | 0);
  wasm.gc_sp.value = sp + 4;
  try {
    return fn();
  } finally {
    wasm.gc_sp.value = sp;
  }
}

// PR #707 review: JS-side shadow-stack push/pop using
// the exported ``$gc_sp`` / ``$gc_stack_limit`` mutable globals
// (added in v0.0.158 / #692 for host-side rooting).  Needed
// because the JS multi-alloc patterns (``allocMapWrapper``, the
// markdown tree builders, and any future caller) have the same
// root-discipline problem as the CLI ``_ShadowGuard``: a
// freshly-allocated wrapper held only in a JS local is invisible
// to the conservative GC scan, so a sub-alloc that fires
// ``$gc_collect`` can reclaim it.  The wrap-table region (below
// ``gc_heap_start``) is NOT walked by the mark phase, so
// ``register_wrapper`` alone isn't enough — explicit shadow-stack
// rooting is required.
//
// #744: hoisted from the ``buildImportObject`` closure to module
// scope so the top-level markdown builders (``writeMdInline`` /
// ``writeMdBlock`` and their array helpers) can use the same
// primitives as ``writeJson`` / ``writeHtml``.  They only touch
// the module-level ``wasm`` binding, so behavior is unchanged for
// the closure-scoped callers.
//
// ``gcShadowPush`` reads $gc_sp, writes the value, advances $gc_sp.
// ``gcShadowPop`` decrements $gc_sp.  Stack-discipline must be
// strict — callers MUST pair push with pop on every exit path
// (try/finally), or run under ``gcGuard`` which restores $gc_sp
// wholesale on exit.
// PR #707 review (silent-failure-hunter C1): symmetric with the
// CLI-side ``_ShadowGuard`` discipline — raise rather than silently
// degrade.  A caller reaching this point (allocMapWrapper, the
// markdown builders, et al.) requires the value to be rooted across
// an allocation window; if ``$gc_sp`` / ``$gc_stack_limit`` are
// missing the module was compiled without GC support but is still
// trying to build multi-alloc values — that's a build-config bug
// and should surface immediately, not as a downstream UAF.
function gcShadowPush(value) {
  if (!wasm || !wasm.gc_sp || !wasm.gc_stack_limit) {
    throw new Error(
      '#707 browser runtime: $gc_sp / $gc_stack_limit not exported; ' +
      'module was built without GC support — multi-alloc host builders ' +
      '(Map / Set / markdown) cannot root intermediates.  Recompile ' +
      'with GC enabled (any of map_ops_used / set_ops_used / ' +
      'decimal_ops_used / md_ops_used / wrap-table-needing types).'
    );
  }
  const sp = wasm.gc_sp.value;
  // #860, following #791: slot-complete bound — see `gcRooted` above.
  if (sp < 0 || sp + 4 > wasm.gc_stack_limit.value) {
    throw new Error('GC shadow stack overflow in browser runtime');
  }
  writeI32(sp, value | 0);
  wasm.gc_sp.value = sp + 4;
}
function gcShadowPop() {
  // Symmetric guard with gcShadowPush — see comment above.  Both
  // checked against the same export-pair invariant (gc_sp and
  // gc_stack_limit travel together) so the pop won't underflow if
  // a future module ever exports one but not the other.
  if (!wasm || !wasm.gc_sp || !wasm.gc_stack_limit) {
    throw new Error(
      '#707 browser runtime: gcShadowPop called without $gc_sp / ' +
      '$gc_stack_limit exports — push/pop must be balanced under ' +
      'the same export-pair invariant'
    );
  }
  wasm.gc_sp.value -= 4;
}

// #708 (PR #707): JS-side parallel of the CLI
// ``_ShadowGuard`` context manager added in v0.0.158 for #692.
// ``writeJson`` / ``writeHtml`` / ``writeMdBlock`` (#744) are
// multi-alloc walkers — they build a tree of heap blocks via
// repeated ``alloc()`` and JS-local pointer holding.  Without
// explicit shadow-stack rooting, intermediates (e.g. JArray's
// ``arrPtr`` between its allocation and the writes into it) are
// reclaimed by EAGER_GC and the resulting tree has dangling
// pointers — observed empirically as ``json_array_length``
// returning 0 instead of the JArray length.
//
// ``gcGuard`` saves ``$gc_sp`` at entry and restores it on exit
// (success OR exception), atomically popping every push made
// within the callback.  Equivalent to ``_ShadowGuard.__enter__/
// __exit__``.  Caller pushes intermediates via ``gcShadowPush``;
// the guard pops them all at the end without per-push bookkeeping.
function gcGuard(fn) {
  if (!wasm || !wasm.gc_sp) {
    // Module without GC infrastructure — just call.  This is fine
    // because such modules can't fire $gc_collect either.
    return fn();
  }
  const savedSp = wasm.gc_sp.value;
  try {
    return fn();
  } finally {
    wasm.gc_sp.value = savedSp;
  }
}

/**
 * SameValueZero equality (the semantics native JS Map/Set use): like
 * ===, but NaN equals NaN.  Used for Float64 Map-key / Set-element
 * comparisons in the bucket codec (decodeColumn lists), so a NaN
 * key/element round-trips the way the old native-Map runtime did for
 * free.  Folded into #706.
 */
function sameValueZero(a, b) {
  return a === b || (a !== a && b !== b);
}

/** Allocate Result.Ok(String) → heap pointer. Tag=0, str at +4/+8. */
function allocResultOkString(str) {
  const [strPtr, strLen] = allocString(str);
  // GC-rooting (folded into #706): strPtr lives only in this JS local
  // across the struct alloc; root it so a GC there can't sweep it.
  return gcRooted(strPtr, () => {
    const ptr = alloc(12);
    writeI32(ptr, 0);            // tag = Ok
    writeI32(ptr + 4, strPtr);
    writeI32(ptr + 8, strLen);
    return ptr;
  });
}

/** Allocate Result.Err(String) → heap pointer. Tag=1, str at +4/+8. */
function allocResultErrString(str) {
  const [strPtr, strLen] = allocString(str);
  // GC-rooting (folded into #706): see allocResultOkString.
  return gcRooted(strPtr, () => {
    const ptr = alloc(12);
    writeI32(ptr, 1);            // tag = Err
    writeI32(ptr + 4, strPtr);
    writeI32(ptr + 8, strLen);
    return ptr;
  });
}

/** Allocate Result.Ok(()) → heap pointer. Tag=0, no payload. */
function allocResultOkUnit() {
  const ptr = alloc(4);
  writeI32(ptr, 0);            // tag = Ok
  return ptr;
}

/** Allocate Result.Ok(i32) → heap pointer. Tag=0, value at +4. */
function allocResultOkI32(value) {
  // GC-rooting (#706): root the heap-pointer payload across the struct
  // alloc.  Harmless for the one Bool caller (0 no-ops, 1 is out of heap
  // range); redundant-safe for callers that already root (json/html parse).
  return gcRooted(value, () => {
    const ptr = alloc(8);
    writeI32(ptr, 0);            // tag = Ok
    writeI32(ptr + 4, value);
    return ptr;
  });
}

/** Allocate Option.Some(String) → heap pointer. Tag=1, str at +4/+8. */
function allocOptionSomeString(str) {
  const [strPtr, strLen] = allocString(str);
  // GC-rooting (#706): root strPtr across the option-struct alloc.
  return gcRooted(strPtr, () => {
    const ptr = alloc(12);
    writeI32(ptr, 1);            // tag = Some
    writeI32(ptr + 4, strPtr);
    writeI32(ptr + 8, strLen);
    return ptr;
  });
}

/** Allocate Option.None → heap pointer. Tag=0, no payload. */
function allocOptionNone() {
  const ptr = alloc(4);
  writeI32(ptr, 0);            // tag = None
  return ptr;
}

/** Allocate Option.Some(i32_value) on the WASM heap. */
function allocOptionSomeI32(val) {
  const ptr = alloc(8);
  writeI32(ptr, 1);              // tag = Some
  writeI32(ptr + 4, val);        // payload
  return ptr;
}

/** Allocate an Ordering value: 0=Less, 1=Equal, 2=Greater. */
function allocOrdering(tag) {
  const ptr = alloc(4);
  writeI32(ptr, tag);
  return ptr;
}

/** Allocate Array<String> → [backingPtr, count]. Each element is 8 bytes. */
function allocArrayOfStrings(strings) {
  const count = strings.length;
  if (count === 0) return [0, 0];
  const backingPtr = alloc(count * 8);
  // GC-rooting (#706): root the backing array across the per-element
  // string allocs.
  return gcRooted(backingPtr, () => {
    for (let i = 0; i < count; i++) {
      const [sPtr, sLen] = allocString(strings[i]);
      writeI32(backingPtr + i * 8, sPtr);
      writeI32(backingPtr + i * 8 + 4, sLen);
    }
    return [backingPtr, count];
  });
}

// ---------------------------------------------------------------------------
// IO host functions (mirror api.py lines 290-423)
// ---------------------------------------------------------------------------

/** vera.print(ptr, len) → capture to stdout buffer. */
function hostPrint(ptr, len) {
  stdoutBuf += readString(ptr, len);
}

/**
 * vera.read_char() → Result<String, String> heap ptr.  #618
 *
 * Browser stub returning Err — actual implementation requires JSPI
 * for the suspend/resume primitive (a keypress listener pushes
 * characters into a queue, then read_char suspends the WASM call
 * and resumes on the next keypress).  Same primitive #609 needs
 * for IO.sleep; until that lands, terminal-style real-time programs
 * compile cleanly for --target browser but error at runtime.
 */
function hostReadChar() {
  return allocResultErrString(
    'IO.read_char not yet supported in browser target ' +
    '(depends on JSPI suspend/resume; tracking: #609, #618)',
  );
}

/** vera.read_line() → [ptr, len] string pair. */
function hostReadLine() {
  let line;
  if (stdinQueue.length > 0) {
    line = stdinQueue.shift();
  } else if (typeof globalThis.prompt === 'function') {
    line = globalThis.prompt('Input:') || '';
  } else {
    line = '';
  }
  return allocString(line);
}

/** vera.read_file(pathPtr, pathLen) → Result<String, String> heap ptr. */
function hostReadFile(_pathPtr, _pathLen) {
  return allocResultErrString('File I/O not available in browser');
}

/** vera.write_file(pPtr, pLen, dPtr, dLen) → Result<Unit, String> heap ptr. */
function hostWriteFile(_pPtr, _pLen, _dPtr, _dLen) {
  return allocResultErrString('File I/O not available in browser');
}

/** vera.args() → [backingPtr, count] Array<String>. */
function hostArgs() {
  return allocArrayOfStrings(cliArgs);
}

/** Sentinel error for IO.exit — mirrors _VeraExit in api.py. */
class VeraExit extends Error {
  constructor(code) {
    super(`IO.exit(${code})`);
    this.name = 'VeraExit';
    this.code = Number(code);
  }
}

/** vera.exit(code) → throw VeraExit. */
function hostExit(code) {
  throw new VeraExit(code);
}

/** vera.get_env(namePtr, nameLen) → Option<String> heap ptr. */
function hostGetEnv(namePtr, nameLen) {
  const name = readString(namePtr, nameLen);
  const value = envVars[name];
  if (value !== undefined) {
    return allocOptionSomeString(value);
  }
  return allocOptionNone();
}

/** vera.sleep(ms) → busy-wait (browser has no synchronous sleep). #463
 *
 * Vera's IO effect is synchronous: `IO.sleep(ms)` must return after
 * roughly `ms` milliseconds without yielding the main thread.
 * Node/Python back it with `time.sleep`; in a browser we have
 * neither `Atomics.wait` on the main thread nor an async bridge
 * into the linear-memory ABI, so we busy-wait on `performance.now()`.
 * The trade is: accuracy within ~1ms, but blocks rendering for the
 * duration.  Programs with short sleeps (animation frames, rate-
 * limiting) work correctly; long sleeps should be avoided in the
 * browser runtime. */
function hostSleep(ms) {
  if (ms <= 0) return;
  const now = typeof performance !== 'undefined' && performance.now
    ? () => performance.now()
    : () => Date.now();
  const deadline = now() + Number(ms);
  while (now() < deadline) { /* busy-wait */ }
}

/** vera.time() → i64 Unix time in ms.  Uses Date.now(). */
function hostTime() {
  // BigInt conversion — WASM i64 is marshalled as BigInt in modern JS.
  return BigInt(Date.now());
}

/** vera.stderr(ptr, len) → capture to stderr buffer. */
function hostStderr(ptr, len) {
  stderrBuf += readString(ptr, len);
}

// ---------------------------------------------------------------------------
// Contract violation reporting (mirror api.py lines 425-450)
// ---------------------------------------------------------------------------

/** vera.contract_fail(ptr, len) → store message; WASM executes unreachable. */
function hostContractFail(ptr, len) {
  lastViolation = readString(ptr, len);
}

/**
 * vera.overflow_trap() → signal an integer overflow; WASM executes unreachable.
 * #808: the #798 `@Int` / `@Nat` arithmetic-overflow guard calls this right
 * before its `unreachable`, so `call()` reports "Integer overflow" instead of
 * the generic trap (mirrors `hostContractFail`; parameterless — the message is
 * fixed, not interned).
 */
function hostOverflowTrap() {
  lastOverflow = true;
}

// ---------------------------------------------------------------------------
// Markdown parser (§9.7.3 subset)
// ---------------------------------------------------------------------------
// JS port of vera/markdown.py — same two-pass strategy:
//   Block pass: headings, code blocks, block quotes, lists, tables, breaks
//   Inline pass: emphasis, strong, code spans, links, images

// -- AST node classes --

class MdText { constructor(text) { this.tag = 'MdText'; this.text = text; } }
class MdCode { constructor(text) { this.tag = 'MdCode'; this.text = text; } }
class MdEmph { constructor(children) { this.tag = 'MdEmph'; this.children = children; } }
class MdStrong { constructor(children) { this.tag = 'MdStrong'; this.children = children; } }
class MdLink { constructor(children, url) { this.tag = 'MdLink'; this.children = children; this.url = url; } }
class MdImage { constructor(alt, url) { this.tag = 'MdImage'; this.alt = alt; this.url = url; } }

class MdParagraph { constructor(children) { this.tag = 'MdParagraph'; this.children = children; } }
class MdHeading { constructor(level, children) { this.tag = 'MdHeading'; this.level = level; this.children = children; } }
class MdCodeBlock { constructor(lang, code) { this.tag = 'MdCodeBlock'; this.lang = lang; this.code = code; } }
class MdBlockQuote { constructor(children) { this.tag = 'MdBlockQuote'; this.children = children; } }
class MdList { constructor(ordered, items) { this.tag = 'MdList'; this.ordered = ordered; this.items = items; } }
class MdThematicBreak { constructor() { this.tag = 'MdThematicBreak'; } }
class MdTable { constructor(rows) { this.tag = 'MdTable'; this.rows = rows; } }
class MdDocument { constructor(children) { this.tag = 'MdDocument'; this.children = children; } }

// --- BEGIN GENERATED: §9.7.3 Markdown grammar ---
// Source of truth: vera/markdown_grammar.py.  Do not hand-edit — the
// #1301 gate in tests/test_browser.py asserts this block is byte-for-byte
// what the generator emits.  Regenerate with:
//   python -c "from vera.markdown_grammar import js_grammar_block as g; print(g())"

const MD_WS_CHARS = " \t\r\u000b\f";
const MD_WS = "[ \\t\\r\\x0b\\x0c]";
const MD_PATTERNS = {
  "atx_heading": "^(#{1,6})[ \\t\\r\\x0b\\x0c]+([^\\n]*?)(?:[ \\t\\r\\x0b\\x0c]+#+[ \\t\\r\\x0b\\x0c]*)?$",
  "fence_open": "^(`{3,}|~{3,})[ \\t\\r\\x0b\\x0c]*([^\\n]*?)$",
  "thematic_break": "^(?:---+|\\*\\*\\*+|___+)[ \\t\\r\\x0b\\x0c]*$",
  "blockquote_line": "^>[ \\t\\r\\x0b\\x0c]?([^\\n]*)",
  "unordered_item": "^[-*+][ \\t\\r\\x0b\\x0c]+([^\\n]*)",
  "ordered_item": "^([0-9]+)[.)][ \\t\\r\\x0b\\x0c]+([^\\n]*)",
  "table_row": "^\\|([^\\n]+)\\|?[ \\t\\r\\x0b\\x0c]*$",
  "table_sep": "^\\|[ \\t\\r\\x0b\\x0c:]*-[- \\t\\r\\x0b\\x0c:|]*\\|?[ \\t\\r\\x0b\\x0c]*$",
};
const MD_CONTINUATION_INDENT = {
  "unordered": 2,
  "ordered": 3,
};
const MD_RE = {};
for (const [key, pattern] of Object.entries(MD_PATTERNS)) {
  MD_RE[key] = new RegExp(pattern);
}
function mdFenceClose(fenceChar, fenceLen) {
  const escaped = fenceChar === '`' ? '\\`' : '~';
  return new RegExp('^' + escaped + '{' + fenceLen + ',}' + MD_WS + '*$');
}
// --- END GENERATED: §9.7.3 Markdown grammar ---

/**
 * `str.strip()` over the grammar's own whitespace class.
 *
 * NOT `String.prototype.trim`, which strips a different set from
 * Python's `str.strip` — Unicode space separators and U+FEFF on one
 * side, the C1-adjacent controls on the other.  Two hosts trimming
 * different characters is the same drift the shared patterns close, one
 * level down (#1301).
 */
function mdTrim(text) {
  let start = 0;
  let end = text.length;
  while (start < end && MD_WS_CHARS.includes(text[start])) start++;
  while (end > start && MD_WS_CHARS.includes(text[end - 1])) end--;
  return text.slice(start, end);
}

/** Is this line nothing but grammar whitespace? */
function mdIsBlank(line) {
  return mdTrim(line) === '';
}

// -- Inline parser --

/**
 * Parse inline content, mirroring `_parse_inlines` in vera/markdown.py
 * statement for statement (#1301).
 *
 * Two properties of that mirror are load-bearing and were both absent
 * before.  Plain text accumulates in ONE buffer that is flushed only
 * when a real node is emitted, so a paragraph's text runs are maximal —
 * the browser used to push one `MdText` per scan segment, which renders
 * to the same string and is a different ADT, and that alone was 82% of
 * the measured divergence.  And a delimiter run is scanned by its
 * LENGTH rather than two characters at a time, so `***both***` opens a
 * three-long run whose leftover delimiter is resolved after the strong
 * span closes, instead of being read as `**` plus a stray `*`.
 */
function parseInlines(text) {
  const result = [];
  let i = 0;
  let buf = '';  // accumulator for plain text

  function flushText() {
    if (buf) {
      result.push(new MdText(buf));
      buf = '';
    }
  }

  while (i < text.length) {
    const ch = text[i];

    // Inline code span: a run of N backticks closes on the next run of N.
    if (ch === '`') {
      const runStart = i;
      while (i < text.length && text[i] === '`') i++;
      const runLen = i - runStart;
      const closePat = '`'.repeat(runLen);
      const closeIdx = text.indexOf(closePat, i);
      if (closeIdx !== -1) {
        flushText();
        let codeContent = text.slice(i, closeIdx);
        // Strip one leading/trailing space if both present — the pad the
        // renderer adds so a span's own spaces survive.
        if (codeContent.length >= 2 && codeContent[0] === ' '
            && codeContent[codeContent.length - 1] === ' ') {
          codeContent = codeContent.slice(1, -1);
        }
        result.push(new MdCode(codeContent));
        i = closeIdx + runLen;
      } else {
        buf += closePat;
      }
      continue;
    }

    // Image: ![alt](src)
    if (ch === '!' && i + 1 < text.length && text[i + 1] === '[') {
      const closeBracket = findMatchingBracket(text, i + 1);
      if (closeBracket !== null && closeBracket + 1 < text.length
          && text[closeBracket + 1] === '(') {
        const closeParen = text.indexOf(')', closeBracket + 2);
        if (closeParen !== -1) {
          flushText();
          result.push(new MdImage(
            text.slice(i + 2, closeBracket),
            text.slice(closeBracket + 2, closeParen),
          ));
          i = closeParen + 1;
          continue;
        }
      }
      buf += ch;
      i++;
      continue;
    }

    // Link: [text](url).  The closing bracket is the MATCHING one, so a
    // nested `[b]` inside the label does not end it early.
    if (ch === '[') {
      const closeBracket = findMatchingBracket(text, i);
      if (closeBracket !== null && closeBracket + 1 < text.length
          && text[closeBracket + 1] === '(') {
        const closeParen = text.indexOf(')', closeBracket + 2);
        if (closeParen !== -1) {
          flushText();
          result.push(new MdLink(
            parseInlines(text.slice(i + 1, closeBracket)),
            text.slice(closeBracket + 2, closeParen),
          ));
          i = closeParen + 1;
          continue;
        }
      }
      buf += ch;
      i++;
      continue;
    }

    // Strong (**) or emphasis (*), by delimiter-run length.
    if (ch === '*' || ch === '_') {
      const delim = ch;
      const runStart = i;
      while (i < text.length && text[i] === delim) i++;
      let runLen = i - runStart;

      if (runLen >= 2) {
        // Try strong first.
        const closeIdx = text.indexOf(delim + delim, i);
        if (closeIdx !== -1) {
          flushText();
          result.push(new MdStrong(parseInlines(text.slice(i, closeIdx))));
          i = closeIdx + 2;
          // Handle remaining delimiters from the opening run.
          const remaining = runLen - 2;
          if (remaining > 0) {
            const closeSingle = text.indexOf(delim, i);
            if (remaining === 1 && closeSingle !== -1) {
              result.push(new MdEmph(parseInlines(text.slice(i, closeSingle))));
              i = closeSingle + 1;
            } else {
              buf += delim.repeat(remaining);
            }
          }
          continue;
        }
        // Fall through to try single emphasis.
        i = runStart + 1;
        runLen = 1;
      }

      if (runLen === 1) {
        const closeIdx = text.indexOf(delim, i);
        if (closeIdx !== -1) {
          flushText();
          result.push(new MdEmph(parseInlines(text.slice(i, closeIdx))));
          i = closeIdx + 1;
        } else {
          buf += delim;
        }
        continue;
      }
    }

    // Plain character
    buf += ch;
    i++;
  }

  flushText();
  return result;
}

/** Find the matching `]` for a `[` at `start`; null if there is none. */
function findMatchingBracket(text, start) {
  if (start >= text.length || text[start] !== '[') return null;
  let depth = 0;
  let i = start;
  while (i < text.length) {
    if (text[i] === '[') depth++;
    else if (text[i] === ']') {
      depth--;
      if (depth === 0) return i;
    }
    i++;
  }
  return null;
}

// -- Block parser --

/**
 * Does this line open a block-level construct?  The disjunction of the
 * six branch predicates in `parseBlocks`, and the SAME regexes those
 * branches use — mirroring `_is_block_start` in vera/markdown.py.
 *
 * That identity is what makes the paragraph fallback terminate.  The old
 * port hand-wrote a second, slightly different list here and a third
 * inside the paragraph loop, so a line could be excluded from the
 * paragraph while no branch claimed it: `md_parse("# heading\r")` — an
 * ordinary CRLF document — spun forever, because ECMAScript's `.` does
 * not match `\r` and the heading branch therefore declined a line the
 * paragraph loop still refused.
 */
function isBlockStart(line) {
  return MD_RE.atx_heading.test(line)
    || MD_RE.fence_open.test(line)
    || MD_RE.thematic_break.test(line)
    || MD_RE.blockquote_line.test(line)
    || MD_RE.unordered_item.test(line)
    || MD_RE.ordered_item.test(line);
}

/**
 * Parse `lines[start..end)` into blocks, mirroring `_parse_blocks` in
 * vera/markdown.py — including the ORDER the constructs are tried in,
 * which decides which branch claims a line two of them could open.
 */
function parseBlocks(lines, start, end) {
  const blocks = [];
  let i = start;

  while (i < end) {
    const line = lines[i];

    // Blank line — skip
    if (mdIsBlank(line)) {
      i++;
      continue;
    }

    // ATX heading
    const heading = MD_RE.atx_heading.exec(line);
    if (heading) {
      blocks.push(new MdHeading(
        heading[1].length, parseInlines(mdTrim(heading[2])),
      ));
      i++;
      continue;
    }

    // Fenced code block
    const fence = MD_RE.fence_open.exec(line);
    if (fence) {
      const closeRe = mdFenceClose(fence[1][0], fence[1].length);
      const lang = mdTrim(fence[2]);
      const codeLines = [];
      i++;
      while (i < end) {
        if (closeRe.test(lines[i])) {
          i++;
          break;
        }
        codeLines.push(lines[i]);
        i++;
      }
      blocks.push(new MdCodeBlock(lang, codeLines.join('\n')));
      continue;
    }

    // Thematic break
    if (MD_RE.thematic_break.test(line)) {
      blocks.push(new MdThematicBreak());
      i++;
      continue;
    }

    // Block quote
    if (MD_RE.blockquote_line.test(line)) {
      const bqLines = [];
      while (i < end) {
        const marked = MD_RE.blockquote_line.exec(lines[i]);
        if (marked) {
          bqLines.push(marked[1]);
        } else if (!mdIsBlank(lines[i]) && !isBlockStart(lines[i])) {
          // Lazy continuation
          bqLines.push(lines[i]);
        } else {
          break;
        }
        i++;
      }
      blocks.push(new MdBlockQuote(parseBlocks(bqLines, 0, bqLines.length)));
      continue;
    }

    // GFM table (must have header + separator row)
    if (MD_RE.table_row.test(line) && i + 1 < end
        && MD_RE.table_sep.test(lines[i + 1])) {
      const rows = [parseTableRow(line)];
      i += 2;  // skip separator
      while (i < end && MD_RE.table_row.test(lines[i])) {
        rows.push(parseTableRow(lines[i]));
        i++;
      }
      blocks.push(new MdTable(rows));
      continue;
    }

    // Unordered list
    if (MD_RE.unordered_item.test(line)) {
      const items = [];
      const width = MD_CONTINUATION_INDENT.unordered;
      const indent = ' '.repeat(width);
      while (i < end) {
        const item = MD_RE.unordered_item.exec(lines[i]);
        if (!item) break;
        const itemLines = [item[1]];
        i++;
        // Continuation lines lose a FIXED width — the marker plus its
        // space — not all their leading whitespace, which is what keeps
        // a third nesting level distinguishable from a second.
        while (i < end && lines[i].startsWith(indent) && !mdIsBlank(lines[i])) {
          itemLines.push(lines[i].slice(width));
          i++;
        }
        // Skip blank lines between items, but only while the list
        // continues — a loose list is ONE list, not two.
        while (i < end && mdIsBlank(lines[i])) {
          i++;
          if (i < end && !MD_RE.unordered_item.test(lines[i])) break;
        }
        items.push(parseBlocks(itemLines, 0, itemLines.length));
      }
      blocks.push(new MdList(false, items));
      continue;
    }

    // Ordered list
    if (MD_RE.ordered_item.test(line)) {
      const items = [];
      const width = MD_CONTINUATION_INDENT.ordered;
      const indent = ' '.repeat(width);
      while (i < end) {
        const item = MD_RE.ordered_item.exec(lines[i]);
        if (!item) break;
        const itemLines = [item[2]];
        i++;
        while (i < end && lines[i].startsWith(indent) && !mdIsBlank(lines[i])) {
          itemLines.push(lines[i].slice(width));
          i++;
        }
        while (i < end && mdIsBlank(lines[i])) {
          i++;
          if (i < end && !MD_RE.ordered_item.test(lines[i])) break;
        }
        items.push(parseBlocks(itemLines, 0, itemLines.length));
      }
      blocks.push(new MdList(true, items));
      continue;
    }

    // Paragraph (default fallback — collect until blank or block start).
    // Reached only when `isBlockStart(line)` is false, so it always
    // consumes at least this line: that is the termination argument.
    const paraLines = [];
    while (i < end && !mdIsBlank(lines[i]) && !isBlockStart(lines[i])) {
      paraLines.push(lines[i]);
      i++;
    }
    if (paraLines.length > 0) {
      // Joined with a space, not a newline.  Spec §9.7.3 excludes hard
      // and soft line breaks from the ADT — "collapsed into paragraph
      // text" — so a paragraph's internal breaks have to go somewhere at
      // parse time or they survive into MdText, where no renderer can
      // tell them from text the author wrote.
      blocks.push(new MdParagraph(parseInlines(paraLines.join(' '))));
    }
  }
  return blocks;
}

function parseTableRow(line) {
  // Strip leading/trailing pipes and split
  let content = mdTrim(line);
  if (content.startsWith('|')) content = content.slice(1);
  if (content.endsWith('|')) content = content.slice(0, -1);
  return content.split('|').map(cell => parseInlines(mdTrim(cell)));
}

function parseMarkdown(text) {
  const lines = text.split('\n');
  return new MdDocument(parseBlocks(lines, 0, lines.length));
}

// Exported for the cross-runtime `md_parse` parity gate (#1301), which
// compares THIS parser's ADT against the Python reference's directly.  A
// comparison routed through `md_render` cannot see how a paragraph's
// plain-text runs are grouped — the runs concatenate to the same string —
// and that class was 82% of the measured divergence.
export { parseMarkdown };

// -- Renderer --

function renderInline(node) {
  switch (node.tag) {
    case 'MdText': return node.text;
    case 'MdCode': {
      // One backtick longer than the content's longest run, padded only
      // when the content starts or ends with one — mirrors
      // _render_code_span.  A fixed two-backtick fence terminates on
      // the content's own `` and loses the rest.
      let longest = 0;
      let run = 0;
      for (const ch of node.text) {
        run = ch === '`' ? run + 1 : 0;
        if (run > longest) longest = run;
      }
      const fence = '`'.repeat(longest + 1);
      // #1303 review: also pad when the content itself starts AND ends
      // with a space.  parseInlines strips one such pair whenever the
      // fenced text is two characters or longer, so without a pad the
      // strip eats the content's own spaces and `MdCode(' x ')` comes
      // back as `MdCode('x')` — and `MdCode(' `x` ')` rendered to the
      // same bytes as `MdCode('`x`')`.  Mirrors _render_code_span.
      const stripsOwnSpaces = node.text.length >= 2
        && node.text.startsWith(' ') && node.text.endsWith(' ');
      const pad = (node.text.startsWith('`') || node.text.endsWith('`')
        || stripsOwnSpaces) ? ' ' : '';
      return fence + pad + node.text + pad + fence;
    }
    case 'MdEmph': return '*' + node.children.map(renderInline).join('') + '*';
    case 'MdStrong': return '**' + node.children.map(renderInline).join('') + '**';
    case 'MdLink': return '[' + node.children.map(renderInline).join('') + '](' + node.url + ')';
    case 'MdImage': return '![' + node.alt + '](' + node.url + ')';
    default: return '';
  }
}

/**
 * Render a block to an array of LINES, mirroring `_render_block` in
 * vera/markdown.py.
 *
 * #1294: the previous version returned one string and threaded a prefix
 * down as an `indent` argument, which a container could only apply to
 * the *first* line of each child — a fenced block inside a blockquote
 * lost the `> ` on its body, and re-rendering that output moved the
 * body out of the quote.  Lines are the unit a container prefixes, so
 * they are the unit this returns: every caller re-applies its own
 * prefix to every line it receives, which is what makes the render a
 * fixed point.
 */
function renderBlockLines(node) {
  switch (node.tag) {
    case 'MdParagraph':
      return [node.children.map(renderInline).join('')];
    case 'MdHeading':
      return ['#'.repeat(node.level) + ' ' + node.children.map(renderInline).join('')];
    case 'MdCodeBlock':
      return ['```' + node.lang, ...node.code.split('\n'), '```'];
    case 'MdBlockQuote': {
      // An empty quote still occupies a line; rendering it as nothing
      // makes the block vanish on re-parse (mirrors _render_block).
      if (node.children.length === 0) return ['>'];
      const out = [];
      node.children.forEach((child, i) => {
        const childLines = renderBlockLines(child);
        // A child that renders nothing must not leave a bare '>'
        // standing for it (#1303 review; mirrors _render_block).
        if (childLines.length === 0) return;
        // A bare '>' between children, mirroring _render_block: without
        // it a quote holding two paragraphs re-parses as one.
        if (i > 0 && out.length > 0) out.push('>');
        for (const line of childLines) {
          out.push(line ? '> ' + line : '>');
        }
      });
      return out;
    }
    case 'MdList': {
      const out = [];
      node.items.forEach((item, idx) => {
        const marker = node.ordered ? `${idx + 1}.` : '-';
        const indent = ' '.repeat(marker.length + 1);
        const itemLines = [];
        for (const child of item) itemLines.push(...renderBlockLines(child));
        if (itemLines.length === 0) {
          // #1303 review: an item with no blocks is a value the PARSER
          // produces — '- ' reads back as one empty item — so dropping
          // it deleted the item and renumbered every ordered item after
          // it.  The marker plus its space is what reads back; a bare
          // '-' is a paragraph, since both item patterns require the
          // whitespace.  Mirrors _render_block.
          out.push(marker + ' ');
          return;
        }
        itemLines.forEach((line, j) => {
          out.push(j === 0 ? marker + ' ' + line : indent + line);
        });
      });
      return out;
    }
    case 'MdThematicBreak':
      return ['---'];
    case 'MdTable': {
      if (node.rows.length === 0) return [];
      const cell = cells => cells.map(renderInline).join('');
      const out = ['| ' + node.rows[0].map(cell).join(' | ') + ' |'];
      out.push('| ' + node.rows[0].map(() => '---').join(' | ') + ' |');
      for (const row of node.rows.slice(1)) {
        out.push('| ' + row.map(cell).join(' | ') + ' |');
      }
      return out;
    }
    case 'MdDocument': {
      const out = [];
      for (const child of node.children) {
        const childLines = renderBlockLines(child);
        // #1303 review: a child that renders to NOTHING — an MdList
        // with no items, an MdTable with no rows — must not drag a
        // separator in with it, or the blank line survives as a stray
        // the next parse cannot attribute to anything and the render
        // stops being a fixed point.  Mirrors _render_block.
        if (childLines.length === 0) continue;
        if (out.length > 0) out.push('');
        out.push(...childLines);
      }
      return out;
    }
    default:
      return [];
  }
}

function renderMarkdown(doc) {
  // Match Python's "\n".join(lines) — no trailing newline.
  return renderBlockLines(doc).join('\n');
}

// -- Query helpers --

function hasHeading(block, level) {
  if (block.tag === 'MdHeading') return block.level === level;
  const children = block.children || block.items;
  if (Array.isArray(children)) {
    for (const child of children) {
      if (Array.isArray(child)) {
        for (const c of child) { if (hasHeading(c, level)) return true; }
      } else if (child && child.tag) {
        if (hasHeading(child, level)) return true;
      }
    }
  }
  return false;
}

function hasCodeBlock(block, lang) {
  if (block.tag === 'MdCodeBlock') return block.lang === lang;
  const children = block.children || block.items;
  if (Array.isArray(children)) {
    for (const child of children) {
      if (Array.isArray(child)) {
        for (const c of child) { if (hasCodeBlock(c, lang)) return true; }
      } else if (child && child.tag) {
        if (hasCodeBlock(child, lang)) return true;
      }
    }
  }
  return false;
}

function extractCodeBlocks(block, lang) {
  const result = [];
  function walk(node) {
    if (node.tag === 'MdCodeBlock' && node.lang === lang) {
      result.push(node.code);
    }
    const children = node.children || node.items;
    if (Array.isArray(children)) {
      for (const child of children) {
        if (Array.isArray(child)) {
          child.forEach(walk);
        } else if (child && child.tag) {
          walk(child);
        }
      }
    }
  }
  walk(block);
  return result;
}

// ---------------------------------------------------------------------------
// Markdown WASM marshalling (mirror vera/wasm/markdown.py)
// ---------------------------------------------------------------------------
// ADT byte layouts must match vera/codegen/registration.py exactly.

// MdInline tags: 0=MdText, 1=MdCode, 2=MdEmph, 3=MdStrong, 4=MdLink, 5=MdImage
// MdBlock tags:  0=MdParagraph, 1=MdHeading, 2=MdCodeBlock, 3=MdBlockQuote,
//                4=MdList, 5=MdThematicBreak, 6=MdTable, 7=MdDocument

// #744 GC-rooting discipline (the #692 / #708 sibling that was
// missed): these builders are multi-alloc walkers, so every
// intermediate heap pointer held only in a JS local must be pushed
// onto the WASM shadow stack (``gcShadowPush``) before any
// subsequent ``alloc()`` that could fire ``$gc_collect``.  The
// convention mirrors the CLI ``vera/wasm/markdown.py`` exactly:
// **allocate fields first, root them, allocate the body last** —
// that way the body's own pointer is never held in a JS local
// across another alloc, so the body never needs rooting.  Array
// helpers push their backing buffer before recursing into
// children; element pointers are stored into the (rooted) backing
// immediately on return, making them reachable via the
// conservative scan without a per-element push.  Pushes are NOT
// popped here — the entry point (``hostMdParse``) runs the whole
// walk under ``gcGuard``, which restores ``$gc_sp`` wholesale.
// The returned root pointer is NOT pushed — the caller roots it
// before its next alloc (see ``hostMdParse``).

function writeInlineArray(inlines) {
  const count = inlines.length;
  if (count === 0) return [0, 0];
  const backingPtr = alloc(count * 4);
  gcShadowPush(backingPtr);
  for (let i = 0; i < count; i++) {
    const ptr = writeMdInline(inlines[i]);
    writeI32(backingPtr + i * 4, ptr);
  }
  return [backingPtr, count];
}

function writeMdInline(node) {
  switch (node.tag) {
    case 'MdText': {  // tag=0, String at +4/+8, total=16
      const [sPtr, sLen] = allocString(node.text);
      if (sPtr !== 0) gcShadowPush(sPtr);
      const ptr = alloc(12);
      writeI32(ptr, 0);
      writeI32(ptr + 4, sPtr);
      writeI32(ptr + 8, sLen);
      return ptr;
    }
    case 'MdCode': {  // tag=1, String at +4/+8, total=16
      const [sPtr, sLen] = allocString(node.text);
      if (sPtr !== 0) gcShadowPush(sPtr);
      const ptr = alloc(12);
      writeI32(ptr, 1);
      writeI32(ptr + 4, sPtr);
      writeI32(ptr + 8, sLen);
      return ptr;
    }
    case 'MdEmph': {  // tag=2, Array at +4/+8, total=16
      // ``writeInlineArray`` already roots its backing buffer.
      const [aPtr, aLen] = writeInlineArray(node.children);
      const ptr = alloc(12);
      writeI32(ptr, 2);
      writeI32(ptr + 4, aPtr);
      writeI32(ptr + 8, aLen);
      return ptr;
    }
    case 'MdStrong': {  // tag=3, Array at +4/+8, total=16
      const [aPtr, aLen] = writeInlineArray(node.children);
      const ptr = alloc(12);
      writeI32(ptr, 3);
      writeI32(ptr + 4, aPtr);
      writeI32(ptr + 8, aLen);
      return ptr;
    }
    case 'MdLink': {  // tag=4, Array at +4/+8, String at +12/+16, total=24
      const [aPtr, aLen] = writeInlineArray(node.children);
      const [sPtr, sLen] = allocString(node.url);
      if (sPtr !== 0) gcShadowPush(sPtr);
      const ptr = alloc(20);
      writeI32(ptr, 4);
      writeI32(ptr + 4, aPtr);
      writeI32(ptr + 8, aLen);
      writeI32(ptr + 12, sPtr);
      writeI32(ptr + 16, sLen);
      return ptr;
    }
    case 'MdImage': {  // tag=5, String at +4/+8, String at +12/+16, total=24
      const [s1Ptr, s1Len] = allocString(node.alt);
      if (s1Ptr !== 0) gcShadowPush(s1Ptr);
      const [s2Ptr, s2Len] = allocString(node.url);
      if (s2Ptr !== 0) gcShadowPush(s2Ptr);
      const ptr = alloc(20);
      writeI32(ptr, 5);
      writeI32(ptr + 4, s1Ptr);
      writeI32(ptr + 8, s1Len);
      writeI32(ptr + 12, s2Ptr);
      writeI32(ptr + 16, s2Len);
      return ptr;
    }
    default:
      throw new Error(`Unknown MdInline tag: ${node.tag}`);
  }
}

function writeBlockArray(blocks) {
  const count = blocks.length;
  if (count === 0) return [0, 0];
  const backingPtr = alloc(count * 4);
  gcShadowPush(backingPtr);
  for (let i = 0; i < count; i++) {
    const ptr = writeMdBlock(blocks[i]);
    writeI32(backingPtr + i * 4, ptr);
  }
  return [backingPtr, count];
}

function writeMdBlock(node) {
  switch (node.tag) {
    case 'MdParagraph': {  // tag=0, Array<MdInline> at +4/+8, total=16
      // ``writeInlineArray`` already roots its backing buffer.
      const [aPtr, aLen] = writeInlineArray(node.children);
      const ptr = alloc(12);
      writeI32(ptr, 0);
      writeI32(ptr + 4, aPtr);
      writeI32(ptr + 8, aLen);
      return ptr;
    }
    case 'MdHeading': {  // tag=1, Nat(i64) at +8, Array at +16/+20, total=24
      const [aPtr, aLen] = writeInlineArray(node.children);
      const ptr = alloc(24);
      writeI32(ptr, 1);
      writeI64(ptr + 8, node.level);
      writeI32(ptr + 16, aPtr);
      writeI32(ptr + 20, aLen);
      return ptr;
    }
    case 'MdCodeBlock': {  // tag=2, String at +4/+8, String at +12/+16, total=24
      const [s1Ptr, s1Len] = allocString(node.lang);
      if (s1Ptr !== 0) gcShadowPush(s1Ptr);
      const [s2Ptr, s2Len] = allocString(node.code);
      if (s2Ptr !== 0) gcShadowPush(s2Ptr);
      const ptr = alloc(20);
      writeI32(ptr, 2);
      writeI32(ptr + 4, s1Ptr);
      writeI32(ptr + 8, s1Len);
      writeI32(ptr + 12, s2Ptr);
      writeI32(ptr + 16, s2Len);
      return ptr;
    }
    case 'MdBlockQuote': {  // tag=3, Array<MdBlock> at +4/+8, total=16
      // ``writeBlockArray`` already roots its backing buffer.
      const [aPtr, aLen] = writeBlockArray(node.children);
      const ptr = alloc(12);
      writeI32(ptr, 3);
      writeI32(ptr + 4, aPtr);
      writeI32(ptr + 8, aLen);
      return ptr;
    }
    case 'MdList': {  // tag=4, Bool(i32) at +4, Array<Array<MdBlock>> at +8/+12, total=16
      // Each item is Array<MdBlock> — we need Array<Array<MdBlock>>.
      // Root the outer backing before recursing; each inner array's
      // (ptr, len) pair is stored into the rooted backing immediately.
      const count = node.items.length;
      let backingPtr = 0;
      if (count > 0) {
        // Each element is an i32_pair (ptr, len) = 8 bytes
        backingPtr = alloc(count * 8);
        gcShadowPush(backingPtr);
        for (let i = 0; i < count; i++) {
          const [itemPtr, itemLen] = writeBlockArray(node.items[i]);
          writeI32(backingPtr + i * 8, itemPtr);
          writeI32(backingPtr + i * 8 + 4, itemLen);
        }
      }
      const ptr = alloc(16);
      writeI32(ptr, 4);
      writeI32(ptr + 4, node.ordered ? 1 : 0);
      writeI32(ptr + 8, backingPtr);
      writeI32(ptr + 12, count);
      return ptr;
    }
    case 'MdThematicBreak': {  // tag=5, no fields, total=8
      const ptr = alloc(4);
      writeI32(ptr, 5);
      return ptr;
    }
    case 'MdTable': {  // tag=6, Array<Array<Array<MdInline>>> at +4/+8, total=16
      // rows: Array<Array<Array<MdInline>>> — root the outer backing
      // AND each row's cell backing so all three levels of nesting
      // stay reachable during the inline-array recursion.
      const rowCount = node.rows.length;
      let rowsPtr = 0;
      if (rowCount > 0) {
        // Each row is Array<Array<MdInline>> — i32_pair (ptr, len) = 8 bytes
        rowsPtr = alloc(rowCount * 8);
        gcShadowPush(rowsPtr);
        for (let ri = 0; ri < rowCount; ri++) {
          const row = node.rows[ri];
          const cellCount = row.length;
          let cellsPtr = 0;
          if (cellCount > 0) {
            // Each cell is Array<MdInline> — i32_pair = 8 bytes
            cellsPtr = alloc(cellCount * 8);
            gcShadowPush(cellsPtr);
            for (let ci = 0; ci < cellCount; ci++) {
              const [cPtr, cLen] = writeInlineArray(row[ci]);
              writeI32(cellsPtr + ci * 8, cPtr);
              writeI32(cellsPtr + ci * 8 + 4, cLen);
            }
          }
          writeI32(rowsPtr + ri * 8, cellsPtr);
          writeI32(rowsPtr + ri * 8 + 4, cellCount);
        }
      }
      const ptr = alloc(12);
      writeI32(ptr, 6);
      writeI32(ptr + 4, rowsPtr);
      writeI32(ptr + 8, rowCount);
      return ptr;
    }
    case 'MdDocument': {  // tag=7, Array<MdBlock> at +4/+8, total=16
      const [aPtr, aLen] = writeBlockArray(node.children);
      const ptr = alloc(12);
      writeI32(ptr, 7);
      writeI32(ptr + 4, aPtr);
      writeI32(ptr + 8, aLen);
      return ptr;
    }
    default:
      throw new Error(`Unknown MdBlock tag: ${node.tag}`);
  }
}

// -- Read MdBlock/MdInline from WASM memory --

function readInlineArray(ptr, len) {
  const result = [];
  for (let i = 0; i < len; i++) {
    const nodePtr = readI32(ptr + i * 4);
    result.push(readMdInline(nodePtr));
  }
  return result;
}

function readMdInline(ptr) {
  const tag = readI32(ptr);
  switch (tag) {
    case 0: return new MdText(readString(readI32(ptr + 4), readI32(ptr + 8)));
    case 1: return new MdCode(readString(readI32(ptr + 4), readI32(ptr + 8)));
    case 2: return new MdEmph(readInlineArray(readI32(ptr + 4), readI32(ptr + 8)));
    case 3: return new MdStrong(readInlineArray(readI32(ptr + 4), readI32(ptr + 8)));
    case 4: return new MdLink(
      readInlineArray(readI32(ptr + 4), readI32(ptr + 8)),
      readString(readI32(ptr + 12), readI32(ptr + 16))
    );
    case 5: return new MdImage(
      readString(readI32(ptr + 4), readI32(ptr + 8)),
      readString(readI32(ptr + 12), readI32(ptr + 16))
    );
    default: throw new Error(`Unknown MdInline tag: ${tag}`);
  }
}

function readBlockArray(ptr, len) {
  const result = [];
  for (let i = 0; i < len; i++) {
    const nodePtr = readI32(ptr + i * 4);
    result.push(readMdBlock(nodePtr));
  }
  return result;
}

function readMdBlock(ptr) {
  const tag = readI32(ptr);
  switch (tag) {
    case 0: return new MdParagraph(readInlineArray(readI32(ptr + 4), readI32(ptr + 8)));
    case 1: return new MdHeading(
      Number(readI64(ptr + 8)),
      readInlineArray(readI32(ptr + 16), readI32(ptr + 20))
    );
    case 2: return new MdCodeBlock(
      readString(readI32(ptr + 4), readI32(ptr + 8)),
      readString(readI32(ptr + 12), readI32(ptr + 16))
    );
    case 3: return new MdBlockQuote(readBlockArray(readI32(ptr + 4), readI32(ptr + 8)));
    case 4: {
      const ordered = readI32(ptr + 4) !== 0;
      const arrPtr = readI32(ptr + 8);
      const arrLen = readI32(ptr + 12);
      const items = [];
      for (let i = 0; i < arrLen; i++) {
        const itemPtr = readI32(arrPtr + i * 8);
        const itemLen = readI32(arrPtr + i * 8 + 4);
        items.push(readBlockArray(itemPtr, itemLen));
      }
      return new MdList(ordered, items);
    }
    case 5: return new MdThematicBreak();
    case 6: {
      const rowsPtr = readI32(ptr + 4);
      const rowCount = readI32(ptr + 8);
      const rows = [];
      for (let ri = 0; ri < rowCount; ri++) {
        const cellsPtr = readI32(rowsPtr + ri * 8);
        const cellCount = readI32(rowsPtr + ri * 8 + 4);
        const row = [];
        for (let ci = 0; ci < cellCount; ci++) {
          const inlPtr = readI32(cellsPtr + ci * 8);
          const inlLen = readI32(cellsPtr + ci * 8 + 4);
          row.push(readInlineArray(inlPtr, inlLen));
        }
        rows.push(row);
      }
      return new MdTable(rows);
    }
    case 7: return new MdDocument(readBlockArray(readI32(ptr + 4), readI32(ptr + 8)));
    default: throw new Error(`Unknown MdBlock tag: ${tag}`);
  }
}

// -- Markdown host bindings --

/** vera.md_parse(ptr, len) → Result<MdBlock, String> heap ptr. */
function hostMdParse(ptr, len) {
  const text = readString(ptr, len);
  // Only parseMarkdown failures become Err(String); a failure in the
  // gcGuard walk below (rooting bug, shadow-stack overflow, builder
  // invariant) is runtime infrastructure breakage and must trap
  // loudly, never masquerade as a Markdown parse error.
  let doc;
  try {
    doc = parseMarkdown(text);
  } catch (e) {
    return allocResultErrString(e.message || String(e));
  }
  // #744: same gcGuard discipline as the json_parse / html_parse
  // bindings — the whole tree walk runs under one guard (every
  // ``gcShadowPush`` made by the builders is popped wholesale on
  // exit), and the returned root is pushed before
  // ``allocResultOkI32``'s alloc can fire GC.
  return gcGuard(() => {
    const blockPtr = writeMdBlock(doc);
    gcShadowPush(blockPtr);
    return allocResultOkI32(blockPtr);
  });
}

/** vera.md_render(blockPtr) → [ptr, len] string pair. */
function hostMdRender(blockPtr) {
  const block = readMdBlock(blockPtr);
  const text = renderMarkdown(block);
  return allocString(text);
}

/** vera.md_has_heading(blockPtr, level) → i32 bool. */
function hostMdHasHeading(blockPtr, level) {
  const block = readMdBlock(blockPtr);
  return hasHeading(block, Number(level)) ? 1 : 0;
}

/** vera.md_has_code_block(blockPtr, langPtr, langLen) → i32 bool. */
function hostMdHasCodeBlock(blockPtr, langPtr, langLen) {
  const block = readMdBlock(blockPtr);
  const lang = readString(langPtr, langLen);
  return hasCodeBlock(block, lang) ? 1 : 0;
}

/** vera.md_extract_code_blocks(blockPtr, langPtr, langLen) → [ptr, count]. */
function hostMdExtractCodeBlocks(blockPtr, langPtr, langLen) {
  const block = readMdBlock(blockPtr);
  const lang = readString(langPtr, langLen);
  const codes = extractCodeBlocks(block, lang);
  return allocArrayOfStrings(codes);
}

// ---------------------------------------------------------------------------
// Regex host functions (mirror api.py host_regex_* — §9.6.15)
// ---------------------------------------------------------------------------

/** vera.regex_match(inPtr, inLen, patPtr, patLen) → Result<Bool, String>. */
function hostRegexMatch(inPtr, inLen, patPtr, patLen) {
  const input = readString(inPtr, inLen);
  const pattern = readString(patPtr, patLen);
  try {
    const re = new RegExp(pattern);
    const matched = re.test(input);
    return allocResultOkI32(matched ? 1 : 0);
  } catch (e) {
    return allocResultErrString(`invalid regex: ${e.message}`);
  }
}

/** vera.regex_find(inPtr, inLen, patPtr, patLen) → Result<Option<String>, String>. */
function hostRegexFind(inPtr, inLen, patPtr, patLen) {
  const input = readString(inPtr, inLen);
  const pattern = readString(patPtr, patLen);
  try {
    const re = new RegExp(pattern);
    const m = input.match(re);
    let optionPtr;
    if (m) {
      optionPtr = allocOptionSomeString(m[0]);
    } else {
      optionPtr = allocOptionNone();
    }
    return allocResultOkI32(optionPtr);
  } catch (e) {
    return allocResultErrString(`invalid regex: ${e.message}`);
  }
}

/** vera.regex_find_all(inPtr, inLen, patPtr, patLen) → Result<Array<String>, String>. */
function hostRegexFindAll(inPtr, inLen, patPtr, patLen) {
  const input = readString(inPtr, inLen);
  const pattern = readString(patPtr, patLen);
  try {
    const re = new RegExp(pattern, 'g');
    const matches = [];
    let m;
    while ((m = re.exec(input)) !== null) {
      matches.push(m[0]);
      // Prevent infinite loop on zero-length matches
      if (m[0].length === 0) re.lastIndex++;
    }
    const [backingPtr, count] = allocArrayOfStrings(matches);
    // GC-rooting (#706): root backingPtr across the Result.Ok alloc.
    return gcRooted(backingPtr, () => {
      // Wrap in Result.Ok — layout: tag=0, backing_ptr, count (12 bytes)
      const ptr = alloc(12);
      writeI32(ptr, 0);              // tag = Ok
      writeI32(ptr + 4, backingPtr);
      writeI32(ptr + 8, count);
      return ptr;
    });
  } catch (e) {
    return allocResultErrString(`invalid regex: ${e.message}`);
  }
}

/** vera.regex_replace(inPtr, inLen, patPtr, patLen, repPtr, repLen) → Result<String, String>. */
function hostRegexReplace(inPtr, inLen, patPtr, patLen, repPtr, repLen) {
  const input = readString(inPtr, inLen);
  const pattern = readString(patPtr, patLen);
  const replacement = readString(repPtr, repLen);
  try {
    const re = new RegExp(pattern);  // no 'g' flag — first match only
    const result = input.replace(re, replacement);
    return allocResultOkString(result);
  } catch (e) {
    return allocResultErrString(`invalid regex: ${e.message}`);
  }
}

// ---------------------------------------------------------------------------
// Import object builder (dynamic introspection)
// ---------------------------------------------------------------------------

const IO_BINDINGS = {
  print: hostPrint,
  read_line: hostReadLine,
  read_char: hostReadChar,
  read_file: hostReadFile,
  write_file: hostWriteFile,
  args: hostArgs,
  exit: hostExit,
  get_env: hostGetEnv,
  sleep: hostSleep,
  time: hostTime,
  stderr: hostStderr,
};

const MD_BINDINGS = {
  md_parse: hostMdParse,
  md_render: hostMdRender,
  md_has_heading: hostMdHasHeading,
  md_has_code_block: hostMdHasCodeBlock,
  md_extract_code_blocks: hostMdExtractCodeBlocks,
};

const REGEX_BINDINGS = {
  regex_match: hostRegexMatch,
  regex_find: hostRegexFind,
  regex_find_all: hostRegexFindAll,
  regex_replace: hostRegexReplace,
};

// #920: WASM value types, as encoded in the type section.
const _WASM_I32 = 0x7f;
const _WASM_I64 = 0x7e;
const _WASM_F64 = 0x7c;

/**
 * The correct initial value for a fresh State<T> cell, keyed on the WASM value
 * type of the cell's `state_*` host imports (#920).
 *
 * Node/browser WASM boundary coercion is strict and type-specific: an `i64`
 * result MUST be a JS BigInt (a plain number throws), while `i32`/`f64` results
 * MUST be plain numbers (a BigInt throws).  So the default is NOT "float vs
 * everything else" — it is exactly what `vera/runtime/state.py`'s
 * `_DEFAULT_STATE[wasm_t]` picks natively:
 *   - f64  → 0.0   (bare `State<Float64>`)
 *   - i64  → 0n    (bare `State<Int>` / `State<Nat>`)
 *   - i32  → 0     (heap pointers: every composite/ADT `State<T>`, and
 *                   `State<Bool>` / `State<Byte>`) — a NULL pointer, as number.
 * The pre-#920 `key.includes('Float')` heuristic mis-seeded composite pointer
 * cells whose mangled suffix lacked `Float` (e.g. `State<Option<Int>>`) with a
 * BigInt, which threw on the `i32` import the moment the default was read.
 *
 * @param {string} key Mangled type suffix (the `stateCells` / `stateWasmTypes`
 *   key), e.g. `Int`, `Tuple_LFloat64_CInt_R`.
 * @returns {number|bigint}
 */
function stateDefaultFor(key) {
  const wt = stateWasmTypes[key];
  if (wt === _WASM_F64) return 0.0;
  if (wt === _WASM_I64) return BigInt(0);
  // i32 (heap pointer / Bool / Byte) — and the defensive fallback for a key
  // whose type was never recorded — take the plain-number null/zero default.
  return 0;
}

/**
 * Record the WASM value type of every `state_*` host import into
 * `stateWasmTypes`, keyed by mangled type suffix (#920).
 *
 * The compiled `WebAssembly.Module` does not expose function signatures via
 * `WebAssembly.Module.imports()` (only `{module, name, kind}`), so this reads
 * the type + import sections of the raw module bytes directly.  Each
 * `state_get_<suffix>` import is `() -> wt` and `state_put_<suffix>` is
 * `(wt) -> ()`; both carry the same `wt`, which is the authoritative
 * scalar-vs-pointer type the cell default must match.
 *
 * A parse failure (truncated / unexpected bytes) leaves `stateWasmTypes`
 * as-is; unrecorded keys then fall back to the `i32`/number default in
 * `stateDefaultFor`, which is correct for every pointer-typed composite.
 *
 * @param {Uint8Array} bytes Raw WASM module bytes.
 */
function recordStateWasmTypes(bytes) {
  try {
    let off = 8; // skip 4-byte magic + 4-byte version

    const readU32 = () => {
      let result = 0, shift = 0, byte;
      do {
        byte = bytes[off++];
        result |= (byte & 0x7f) << shift;
        shift += 7;
      } while (byte & 0x80);
      return result >>> 0;
    };

    // funcTypes[i] = the sole result/param value type of type i, or null if it
    // is not a single-value 0->1 / 1->0 signature (state imports only use those).
    const funcTypes = [];
    const readValType = () => bytes[off++]; // single-byte numeric value type

    while (off < bytes.byteLength) {
      const sectionId = bytes[off++];
      const sectionLen = readU32();
      const sectionEnd = off + sectionLen;
      if (sectionId === 1) {
        // Type section
        const count = readU32();
        for (let i = 0; i < count; i++) {
          const form = bytes[off++]; // 0x60 = func
          if (form !== 0x60) { off = sectionEnd; break; }
          const nParams = readU32();
          const params = [];
          for (let p = 0; p < nParams; p++) params.push(readValType());
          const nResults = readU32();
          const results = [];
          for (let r = 0; r < nResults; r++) results.push(readValType());
          // state_get: 0 params, 1 result; state_put: 1 param, 0 results.
          if (nParams === 0 && nResults === 1) funcTypes.push(results[0]);
          else if (nParams === 1 && nResults === 0) funcTypes.push(params[0]);
          else funcTypes.push(null);
        }
      } else if (sectionId === 2) {
        // Import section
        const count = readU32();
        for (let i = 0; i < count; i++) {
          const modLen = readU32();
          const modName = decoder.decode(bytes.subarray(off, off + modLen));
          off += modLen;
          const nmLen = readU32();
          const name = decoder.decode(bytes.subarray(off, off + nmLen));
          off += nmLen;
          const kind = bytes[off++];
          if (kind === 0x00) {
            // function import: typeidx follows
            const typeIdx = readU32();
            if (modName === 'vera') {
              const m = name.match(/^state_(?:get|put)_(.+)$/);
              if (m && funcTypes[typeIdx] != null) {
                stateWasmTypes[m[1]] = funcTypes[typeIdx];
              }
            }
          } else if (kind === 0x01) {
            // table: reftype + limits
            off++; // reftype
            const flags = bytes[off++];
            readU32(); // min
            if (flags & 0x01) readU32(); // max
          } else if (kind === 0x02) {
            // memory: limits
            const flags = bytes[off++];
            readU32(); // min
            if (flags & 0x01) readU32(); // max
          } else if (kind === 0x03) {
            // global: valtype + mutability
            off++; // valtype
            off++; // mutability
          } else if (kind === 0x04) {
            // tag: attribute + typeidx
            off++; // attribute
            readU32(); // typeidx
          }
        }
        // Imports parsed — no later section matters for state types.
        return;
      }
      off = sectionEnd;
    }
  } catch {
    // Leave stateWasmTypes as-is; stateDefaultFor's i32 fallback is safe.
  }
}

function buildImportObject(module, moduleBytes) {
  const imports = { vera: {} };
  const needed = new Set();

  for (const imp of WebAssembly.Module.imports(module)) {
    if (imp.module === 'vera') needed.add(imp.name);
  }

  // #920: learn each State<T> cell's WASM value type from the module's own
  // import declarations, so the default cell value matches the native host.
  if (moduleBytes) recordStateWasmTypes(moduleBytes);

  // IO bindings
  for (const [name, fn] of Object.entries(IO_BINDINGS)) {
    if (needed.has(name)) imports.vera[name] = fn;
  }

  // Contract fail
  if (needed.has('contract_fail')) {
    imports.vera.contract_fail = hostContractFail;
  }

  // #808: integer-overflow trap signal (declared by the #798 overflow guard)
  if (needed.has('overflow_trap')) {
    imports.vera.overflow_trap = hostOverflowTrap;
  }

  // State<T> bindings — dynamically created from import names.
  // stateCells[key] is a stack; top is the active cell for the current handler.
  for (const name of needed) {
    const getMatch = name.match(/^state_get_(.+)$/);
    if (getMatch) {
      const key = getMatch[1];
      if (!(key in stateCells)) {
        stateCells[key] = [stateDefaultFor(key)];
      }
      imports.vera[name] = () => stateCells[key][stateCells[key].length - 1];
    }
    const putMatch = name.match(/^state_put_(.+)$/);
    if (putMatch) {
      const key = putMatch[1];
      if (!(key in stateCells)) {
        stateCells[key] = [stateDefaultFor(key)];
      }
      imports.vera[name] = (val) => { stateCells[key][stateCells[key].length - 1] = val; };
    }
    const pushMatch = name.match(/^state_push_(.+)$/);
    if (pushMatch) {
      const key = pushMatch[1];
      const def = stateDefaultFor(key);
      if (!(key in stateCells)) {
        stateCells[key] = [def];
      }
      imports.vera[name] = () => { stateCells[key].push(def); };
    }
    const popMatch = name.match(/^state_pop_(.+)$/);
    if (popMatch) {
      const key = popMatch[1];
      if (!(key in stateCells)) {
        stateCells[key] = [stateDefaultFor(key)];
      }
      imports.vera[name] = () => { if (stateCells[key].length > 1) stateCells[key].pop(); };
    }
  }

  // Markdown bindings
  for (const [name, fn] of Object.entries(MD_BINDINGS)) {
    if (needed.has(name)) imports.vera[name] = fn;
  }

  // Regex bindings
  for (const [name, fn] of Object.entries(REGEX_BINDINGS)) {
    if (needed.has(name)) imports.vera[name] = fn;
  }

  // Map<K, V> bindings — #706: the WASM bucket array is the sole
  // source of truth.  Host imports take the wrapper pointer and
  // decode / encode the bucket directly (no JS-side mapStore).  Import
  // names stay type-specific: map_insert$ks_vi, map_get$ki_vb, etc.

  // #573: host_decref_handle is called from Phase 2c of $gc_collect for
  // every wrapper-ADT object that became unmarked.  #706: Map / Set
  // wrappers are no longer registered (they are plain heap objects
  // reclaimed by ordinary mark-sweep), so only Decimal (kind=3) — which
  // keeps the value-typed JS store — needs eviction here.
  imports.vera.host_decref_handle = (kind, handle) => {
    if (kind === 3) {
      decimalStore.delete(handle);
    } else if (kind === 4) {
      // #841: fused-async Future whose wrapper became unreachable
      // without being awaited — evict the buffered outcome.
      futureStore.delete(handle);
    }
    // Map (1) / Set (2) are bucket-as-truth — no store entry to evict.
    // Unknown kinds: silent no-op.
  };

  // #706: bucket-as-truth codec (JS parallel of the Python codec in
  // vera/codegen/api.py).  Layout must match: 8-byte header (capacity
  // @+0, count @+4) + capacity * 20-byte slots (occupancy @+0,
  // key_lo @+4, key_hi @+8, val_lo @+12, val_hi @+16).  The browser
  // runs small programs (no 10K perf chain — that's CLI-only), so
  // per-slot access is fine; each helper refetches mem().buffer so an
  // intervening memory.grow can't leave a detached DataView.
  const _BKT_HEADER = 8;
  const _BKT_SLOT = 20;

  // #706: slot capacity rounded UP to a power of two (min
  // _BUCKET_INITIAL_CAPACITY) — same-size-class inserts reuse freed
  // buckets from the GC free list, keeping an insert chain's heap
  // high-water ~O(N) rather than ~O(N^2).  Mirrors _bkt_capacity in
  // vera/codegen/api.py.
  function bktCapacity(count) {
    const want = Math.max(_BUCKET_INITIAL_CAPACITY, count * 2);
    let cap = _BUCKET_INITIAL_CAPACITY;
    while (cap < want) cap *= 2;
    return cap;
  }

  function allocBucket(capacity) {
    const total = _BKT_HEADER + capacity * _BKT_SLOT;
    const ptr = alloc(total);
    new Uint8Array(mem().buffer, ptr, total).fill(0);
    writeI32(ptr, capacity);
    return ptr;
  }

  function allocBktWrapper(kind, bucketPtr) {
    const ptr = alloc(12); // tag(4) + vestigial(4) + bucket_ptr(4)
    writeI32(ptr, _KIND_TO_TAG_JS[kind]);
    writeI32(ptr + 4, 0); // vestigial — no host handle
    writeI32(ptr + 8, bucketPtr | 0);
    return ptr;
  }

  function encodeField(tag, base, value) {
    if (tag === 'i') { writeI64(base, value); }
    else if (tag === 'f') { writeF64(base, Number(value)); }
    else if (tag === 's') {
      const [p, l] = allocString(String(value)); // may grow memory
      writeI32(base, p);
      writeI32(base + 4, l);
    } else { // "b": Bool / Byte / ADT / heap pointer
      writeI32(base, Number(value) | 0);
      writeI32(base + 4, 0);
    }
  }

  function decodeField(tag, base) {
    const dv = new DataView(mem().buffer);
    if (tag === 'i') return dv.getBigInt64(base, true);
    if (tag === 'f') return dv.getFloat64(base, true);
    if (tag === 's') {
      const p = dv.getInt32(base, true);
      const l = dv.getInt32(base + 4, true);
      return l ? readString(p, l) : '';
    }
    return dv.getInt32(base, true) >>> 0; // "b" — unsigned i32
  }

  // Decode a Map wrapper's bucket into a JS Map.
  function decodeMap(wrapperPtr, kt, vt) {
    const out = new Map();
    const bucketPtr = readI32(wrapperPtr + 8);
    if (bucketPtr === 0) return out;
    const count = readI32(bucketPtr + 4);
    if (count === 0) return out;
    const cap = readI32(bucketPtr);
    const slotsBase = bucketPtr + _BKT_HEADER;
    for (let i = 0; i < cap && out.size < count; i++) {
      const base = slotsBase + i * _BKT_SLOT;
      if (readI32(base) === 0) continue;
      out.set(decodeField(kt, base + 4), decodeField(vt, base + 12));
    }
    return out;
  }

  // Decode one field column (keys at off=4, vals at off=12) in order.
  function decodeColumn(wrapperPtr, tag, off) {
    const out = [];
    const bucketPtr = readI32(wrapperPtr + 8);
    if (bucketPtr === 0) return out;
    const count = readI32(bucketPtr + 4);
    if (count === 0) return out;
    const cap = readI32(bucketPtr);
    const slotsBase = bucketPtr + _BKT_HEADER;
    for (let i = 0; i < cap && out.length < count; i++) {
      const base = slotsBase + i * _BKT_SLOT;
      if (readI32(base) === 0) continue;
      out.push(decodeField(tag, base + off));
    }
    return out;
  }

  function bktCount(wrapperPtr) {
    const bp = readI32(wrapperPtr + 8);
    return bp === 0 ? 0 : readI32(bp + 4);
  }

  // Encode [key, val] entries into a fresh wrapper + bucket.  vt === null
  // for Sets (val field stays 0).  The new wrapper + bucket are
  // shadow-rooted across the encode so a string alloc's GC can't sweep
  // them; val is written before the key so a heap-pointer value is
  // rooted before the key-string alloc fires.
  function encodeEntries(kind, entries, kt, vt) {
    const count = entries.length;
    const capacity = bktCapacity(count);
    const wrapperPtr = allocBktWrapper(kind, 0);
    gcShadowPush(wrapperPtr);
    try {
      const bucketPtr = allocBucket(capacity);
      gcShadowPush(bucketPtr);
      try {
        writeI32(wrapperPtr + 8, bucketPtr);
        const slotsBase = bucketPtr + _BKT_HEADER;
        for (let i = 0; i < count; i++) {
          const slot = slotsBase + i * _BKT_SLOT;
          writeI32(slot, 1);
          if (vt !== null) encodeField(vt, slot + 12, entries[i][1]);
          encodeField(kt, slot + 4, entries[i][0]);
        }
        writeI32(bucketPtr + 4, count);
      } finally { gcShadowPop(); }
    } finally { gcShadowPop(); }
    return wrapperPtr;
  }

  // Structural rebuild dropping the matching key (no value tag needed —
  // 16-byte key+val field regions are copied verbatim, sharing the
  // immutable String / heap blocks with the source).
  function rebuildWithout(wrapperPtr, kt, key, kind) {
    const survivors = [];
    const bucketPtr = readI32(wrapperPtr + 8);
    if (bucketPtr !== 0) {
      const count = readI32(bucketPtr + 4);
      const cap = readI32(bucketPtr);
      const slotsBase = bucketPtr + _BKT_HEADER;
      let seen = 0;
      for (let i = 0; i < cap && seen < count; i++) {
        const base = slotsBase + i * _BKT_SLOT;
        if (readI32(base) === 0) continue;
        seen++;
        if (sameValueZero(decodeField(kt, base + 4), key)) continue;
        const fields = new Uint8Array(16);
        fields.set(new Uint8Array(mem().buffer, base + 4, 16));
        survivors.push(fields);
      }
    }
    const newWrapper = allocBktWrapper(kind, 0);
    gcShadowPush(newWrapper);
    try {
      const newBucket = allocBucket(
        bktCapacity(survivors.length),
      );
      gcShadowPush(newBucket);
      try {
        writeI32(newWrapper + 8, newBucket);
        const slotsBase = newBucket + _BKT_HEADER;
        for (let i = 0; i < survivors.length; i++) {
          const slot = slotsBase + i * _BKT_SLOT;
          writeI32(slot, 1);
          new Uint8Array(mem().buffer, slot + 4, 16).set(survivors[i]);
        }
        writeI32(newBucket + 4, survivors.length);
      } finally { gcShadowPop(); }
    } finally { gcShadowPop(); }
    return newWrapper;
  }

  const _BUCKET_INITIAL_CAPACITY = 8;
  // #706: Map and Set are bucket-as-truth (their wrappers carry the
  // bucket directly) and Decimal is value-typed, so nothing needs a
  // bucket attached.  The import stays defined because the Decimal wrap
  // path (_emit_wrap_handle) still emits a call to it; the body is a
  // tripwire asserting only Decimal (kind=3) reaches it (mirrors the
  // CLI host_attach_bucket), so a regression that routes a Map / Set
  // wrapper back through this path fails loudly instead of silently
  // leaving its bucket unpopulated.
  imports.vera.attach_bucket_to_wrapper = (_wrapperPtr, kind) => {
    if (kind !== 3) {
      throw new Error(
        '#706 browser runtime: attach_bucket_to_wrapper called with ' +
        'kind=' + kind + '; expected Decimal (3).  A Map/Set wrapper ' +
        'was routed back through _emit_wrap_handle — the bucket-as-truth ' +
        'invariant is violated.'
      );
    }
  };

  // #573 wrapper-ADT layout constants (must match
  // vera/wasm/calls_containers.py).
  const _MAP_HANDLE_TAG = 0xFEEDC001 | 0;
  const _SET_HANDLE_TAG = 0xFEEDC002 | 0;
  const _DECIMAL_HANDLE_TAG = 0xFEEDC003 | 0;
  const _KIND_TO_TAG_JS = {
    1: _MAP_HANDLE_TAG,
    2: _SET_HANDLE_TAG,
    3: _DECIMAL_HANDLE_TAG,
  };

  // wrapHandle(kind, rawHandle) — JS counterpart of `_wrap_handle`
  // in vera/codegen/api.py.  Allocates a 12-byte wrapper ADT,
  // writes tag + handle, calls the exported $register_wrapper.
  // Decimal-only post-#706: Map / Set are bucket-as-truth and no
  // longer wrap a handle.  Used by decimal host helpers that have a
  // raw handle and need to lift it to a wrapper pointer before
  // stuffing into an Option<Decimal> Some payload.
  // Wrapper body layout (must match _WRAPPER_BODY_SIZE in
  // vera/codegen/api.py and vera/wasm/calls_containers.py):
  //   +0  tag (i32)            [#573]
  //   +4  handle | 0x80000000  [#578 — bit-31 tag keeps it out
  //                             of the conservative GC scan]
  //   +8  bucket_ptr (i32)     [0 — Decimal is value-typed]
  function wrapHandle(kind, rawHandle) {
    const tag = _KIND_TO_TAG_JS[kind];
    const ptr = alloc(12);
    writeI32(ptr, tag);
    // #578: tag the handle with bit-31 so the conservative scan
    // never mistakes it for a heap pointer.  Matches the
    // WAT-emitted ``_emit_wrap_handle`` discipline.
    writeI32(ptr + 4, (rawHandle | 0x80000000) | 0);
    // bucket_ptr is 0 — Decimal is value-typed (and this helper is
    // Decimal-only post-#706, so nothing attaches a bucket here).
    writeI32(ptr + 8, 0);
    // PR #707 review (silent-failure-hunter C2): symmetric with the
    // CLI-side ``_call_register_wrapper`` discipline.  A caller
    // reaching wrapHandle is building a Decimal wrapper — so the
    // wrap-table is required for Phase 2c reclamation.  If
    // ``register_wrapper`` isn't exported, the wrapper is allocated
    // and the decimalStore entry created but the wrap-table
    // registration is skipped → ``host_decref_handle`` never fires →
    // permanent decimalStore leak per write.  That's a build-config
    // bug; raise rather than silently leak.
    if (!wasm || typeof wasm.register_wrapper !== "function") {
      throw new Error(
        '#707 browser runtime: $register_wrapper not exported; ' +
        'module was built without wrap-table support but is trying ' +
        'to wrap a host handle.  Recompile with wrap-table-needing ' +
        'types enabled (Map / Set / Decimal).'
      );
    }
    wasm.register_wrapper(ptr, kind, rawHandle);
    return ptr;
  }

  // allocMapWrapper(d) — used by writeJson / writeHtml to build the
  // Map<String, V> wrapper for a JObject / HtmlElement's attrs.
  // #706: it encodes ``d`` directly into a bucket-as-truth wrapper +
  // bucket via ``encodeEntries`` (matches the CLI
  // ``_alloc_map_wrapper``); there is no ``mapStore`` and no
  // ``wrapHandle``.  ``encodeEntries`` shadow-roots the new wrapper +
  // bucket across the per-entry string allocations, so a sub-alloc
  // that fires ``$gc_collect`` mid-encode can't reclaim them.  The
  // caller is responsible for storing the returned ptr promptly (it
  // is unrooted again on return — see writeJson's JObject branch,
  // the only consumer of this helper).
  function allocMapWrapper(d) {
    // #706: build a bucket-as-truth Map<String, V> wrapper directly.
    // write_json's JObject values are Json heap pointers ("b");
    // write_html's attrs values are strings ("s").  The two callers
    // never mix value types, so a single uniform tag is correct.
    const entries = [...d.entries()].map(([k, v]) => [String(k), v]);
    const vt = entries.some(([, v]) => typeof v === 'string') ? 's' : 'b';
    return encodeEntries(1, entries, 's', vt);
  }

  // Helper: allocate Option.None on heap (tag=0, 4 bytes)
  function mapAllocOptionNone() {
    const p = alloc(4);
    writeI32(p, 0);
    return p;
  }

  // Helper: allocate Option.Some with typed payload
  function mapAllocOption(val, vt) {
    if (val === undefined) return mapAllocOptionNone();
    if (vt === 'i') {
      const p = alloc(16); // tag(4) + padding(4) + i64(8)
      writeI32(p, 1);
      writeI64(p + 8, val);
      return p;
    }
    if (vt === 'f') {
      const p = alloc(16); // tag(4) + padding(4) + f64(8)
      writeI32(p, 1);
      new DataView(mem().buffer).setFloat64(p + 8, Number(val), true);
      return p;
    }
    if (vt === 's') {
      const [sp, sl] = allocString(String(val));
      // GC-rooting (#706): root sp across the option-struct alloc.
      return gcRooted(sp, () => {
        const p = alloc(12); // tag(4) + ptr(4) + len(4)
        writeI32(p, 1);
        writeI32(p + 4, sp);
        writeI32(p + 8, sl);
        return p;
      });
    }
    // i32 (Bool, Byte, ADT, Map handle)
    const p = alloc(8); // tag(4) + i32(4)
    writeI32(p, 1);
    writeI32(p + 4, Number(val));
    return p;
  }

  // Helper: allocate Array of strings
  function mapAllocArrayOfStrings(strings) {
    const count = strings.length;
    if (count === 0) return [0, 0];
    const ptr = alloc(count * 8); // each string is (i32 ptr, i32 len)
    // GC-rooting (#706): root the backing array across the per-element
    // string allocs; each str ptr is written into the rooted backing
    // immediately, so no element pointer is held unrooted across an alloc.
    return gcRooted(ptr, () => {
      for (let i = 0; i < count; i++) {
        const [sp, sl] = allocString(strings[i]);
        writeI32(ptr + i * 8, sp);
        writeI32(ptr + i * 8 + 4, sl);
      }
      return [ptr, count];
    });
  }

  // Serialize a JS array of decoded keys / values / elements into a WASM
  // Array<T> ([backingPtr, count]); used by map_keys / map_values /
  // set_to_array.
  function emitArray(values, tag) {
    if (tag === 's') return mapAllocArrayOfStrings(values.map(String));
    const count = values.length;
    if (count === 0) return [0, 0];
    const elemSize = tag === 'i' || tag === 'f' ? 8 : 4;
    const ptr = alloc(count * elemSize);
    const view = new DataView(mem().buffer);
    for (let i = 0; i < count; i++) {
      if (tag === 'i') view.setBigInt64(ptr + i * 8, BigInt(values[i]), true);
      else if (tag === 'f') view.setFloat64(ptr + i * 8, Number(values[i]), true);
      else view.setInt32(ptr + i * 4, Number(values[i]), true);
    }
    return [ptr, count];
  }

  if (needed.has('map_new')) {
    imports.vera.map_new = () => allocBktWrapper(1, 0);
  }
  if (needed.has('map_size')) {
    imports.vera.map_size = (wp) => BigInt(bktCount(wp));
  }

  for (const name of needed) {
    // map_insert$k<kt>_v<vt>
    let m = name.match(/^map_insert\$k(.)_v(.)$/);
    if (m) {
      const [, kt, vt] = m;
      imports.vera[name] = (wp, ...args) => {
        let idx = 0;
        const k = kt === 's' ? readString(args[idx++], args[idx++]) : args[idx++];
        const v = vt === 's' ? readString(args[idx++], args[idx++]) : args[idx++];
        const d = decodeMap(wp, kt, vt);
        d.set(k, v);
        return encodeEntries(1, [...d.entries()], kt, vt);
      };
      continue;
    }
    // map_get$k<kt>_v<vt>
    m = name.match(/^map_get\$k(.)_v(.)$/);
    if (m) {
      const [, kt, vt] = m;
      imports.vera[name] = (wp, ...args) => {
        let idx = 0;
        const k = kt === 's' ? readString(args[idx++], args[idx++]) : args[idx++];
        return mapAllocOption(decodeMap(wp, kt, vt).get(k), vt);
      };
      continue;
    }
    // map_contains$k<kt>
    m = name.match(/^map_contains\$k(.)$/);
    if (m) {
      const [, kt] = m;
      imports.vera[name] = (wp, ...args) => {
        let idx = 0;
        const k = kt === 's' ? readString(args[idx++], args[idx++]) : args[idx++];
        return decodeColumn(wp, kt, 4).some((x) => sameValueZero(x, k)) ? 1 : 0;
      };
      continue;
    }
    // map_remove$k<kt>
    m = name.match(/^map_remove\$k(.)$/);
    if (m) {
      const [, kt] = m;
      imports.vera[name] = (wp, ...args) => {
        let idx = 0;
        const k = kt === 's' ? readString(args[idx++], args[idx++]) : args[idx++];
        return rebuildWithout(wp, kt, k, 1);
      };
      continue;
    }
    // map_keys$k<kt>
    m = name.match(/^map_keys\$k(.)$/);
    if (m) {
      const [, kt] = m;
      imports.vera[name] = (wp) => emitArray(decodeColumn(wp, kt, 4), kt);
      continue;
    }
    // map_values$v<vt>
    m = name.match(/^map_values\$v(.)$/);
    if (m) {
      const [, vt] = m;
      imports.vera[name] = (wp) => emitArray(decodeColumn(wp, vt, 12), vt);
      continue;
    }
  }

  // Set<T> bindings — #706: bucket-as-truth, parallel to Map.  The
  // element lives in the slot's key field (decodeColumn off=4); the val
  // field is unused (encodeEntries with vt === null).  Int elements stay
  // BigInt end-to-end so the JS Set dedups consistently with the i64
  // round-trip (the old runtime coerced to Number).
  if (needed.has("set_new")) {
    imports.vera["set_new"] = () => allocBktWrapper(2, 0);
  }
  if (needed.has("set_size")) {
    imports.vera["set_size"] = (wp) => BigInt(bktCount(wp));
  }

  for (const name of needed) {
    let m;
    // set_add$e(.)
    m = name.match(/^set_add\$e(.)$/);
    if (m) {
      const et = m[1];
      const add = (wp, e) => {
        const s = new Set(decodeColumn(wp, et, 4));
        s.add(e);
        return encodeEntries(2, [...s].map((x) => [x, 0]), et, null);
      };
      imports.vera[name] = et === "s"
        ? (wp, ptr, len) => add(wp, readString(ptr, len))
        : (wp, e) => add(wp, e);
      continue;
    }

    // set_contains$e(.)
    m = name.match(/^set_contains\$e(.)$/);
    if (m) {
      const et = m[1];
      const has = (wp, e) => decodeColumn(wp, et, 4).some((x) => sameValueZero(x, e)) ? 1 : 0;
      imports.vera[name] = et === "s"
        ? (wp, ptr, len) => has(wp, readString(ptr, len))
        : (wp, e) => has(wp, e);
      continue;
    }

    // set_remove$e(.)
    m = name.match(/^set_remove\$e(.)$/);
    if (m) {
      const et = m[1];
      imports.vera[name] = et === "s"
        ? (wp, ptr, len) => rebuildWithout(wp, et, readString(ptr, len), 2)
        : (wp, e) => rebuildWithout(wp, et, e, 2);
      continue;
    }

    // set_to_array$e(.)
    m = name.match(/^set_to_array\$e(.)$/);
    if (m) {
      const et = m[1];
      imports.vera[name] = (wp) => emitArray(decodeColumn(wp, et, 4), et);
      continue;
    }
  }

  // ── Decimal host imports ──────────────────────────────────────
  // JS lacks a native Decimal, so this is an exact scaled-BigInt
  // engine mirroring the Python runtime's ``decimal.Decimal`` under
  // its default context (28 significant digits, ROUND_HALF_EVEN).
  // It matches the ``vera/runtime/decimal.py`` host semantics op-for-op
  // — arithmetic, division, rounding, comparison, and string form —
  // so `--target browser` honours spec §9.7.2's exactness promise and
  // ``decimal_compare`` / ``decimal_eq`` can never contradict each
  // other (the #856 self-contradiction: the old engine routed through
  // JS ``Number`` for compare/arithmetic while ``eq`` string-compared).
  //
  // Value model: ``{sign: 0|1, coeff: BigInt >= 0, exp: int}`` with
  // value = (-1)^sign * coeff * 10^exp — the same digits/sign/exponent
  // triple as Python's ``Decimal.as_tuple()``.  The store keeps the
  // *canonical* string form (``decToString`` output), so every op reads
  // back a losslessly-parseable operand and every producer stores a
  // Python-identical rendering.  Special values (Inf/NaN) are out of
  // scope: ``decimal_from_string`` rejects them (returns None), so the
  // engine only ever sees finite decimals.
  const DEC_PREC = 28n;
  const DEC_RE = /^([+-]?)(\d*)(?:\.(\d*))?(?:[eE]([+-]?\d+))?$/;

  // The whitespace §9.7.2 states, rather than whatever the host's own
  // trim happens to take (#1303 review).  ``String.prototype.trim``
  // strips U+FEFF and every Unicode space separator but NOT
  // U+001C..U+001F or U+0085, while the reference host's ``str.strip``
  // does the opposite on both counts — so the accepted domain diverged
  // in both directions.  This is the set ``is_whitespace`` already
  // states: tab, LF, VT, FF, CR, space.  Mirrors _ASCII_WS in
  // vera/runtime/decimal.py.
  const DEC_WS = /^[\t\n\v\f\r ]+|[\t\n\v\f\r ]+$/g;
  const decStripWs = (str) => str.replace(DEC_WS, "");

  function decNumDigits(n) {
    return n === 0n ? 1 : n.toString().length;
  }

  // Parse a (canonical or user) decimal string to the value model.
  // Returns null on malformed input.
  function decParse(str) {
    const m = decStripWs(str).match(DEC_RE);
    if (!m) return null;
    const intPart = m[2] || "";
    const fracPart = m[3] || "";
    if (intPart === "" && fracPart === "") return null;
    const sign = m[1] === "-" ? 1 : 0;
    let coeffStr = intPart + fracPart;
    let exp = -fracPart.length;
    if (m[4] !== undefined) exp += parseInt(m[4], 10);
    coeffStr = coeffStr.replace(/^0+(?=\d)/, "");
    return { sign, coeff: BigInt(coeffStr), exp };
  }

  // Spec §9.7.2 exponent bound for decimal_from_string acceptance: the
  // literal exponent token must satisfy |exp| <= 999999 (the context's
  // Emax/Emin floor already cited by the decimal_round Overflow
  // fallback — a literal outside it could never participate in any
  // operation without overflowing).  Checked on the token STRING before
  // any numeric conversion: parseInt silently ROUNDS above
  // Number.MAX_SAFE_INTEGER ("1e9007199254740993" parsed as ...992
  // while Python stored it exactly — CR finding 3518083324).  This
  // bound applies to decimal_from_string ONLY, not decParse: a stored
  // canonical string can legitimately carry an adjusted-exponent token
  // of -1000000 (a 999999 token plus a long fraction), and decimalGet
  // must keep round-tripping those.
  function decExpTokenInRange(str) {
    const m = decStripWs(str).match(DEC_RE);
    if (!m || m[4] === undefined) return true;
    const digits = m[4].replace(/^[+-]/, "").replace(/^0+(?=\d)/, "");
    return digits.length <= 6;  // 6 digits: at most 999999
  }

  // Render to Python's to-sci-string form (plain when exp <= 0 and the
  // adjusted exponent >= -6, else scientific ``d.ddddE±n``).
  function decToString(d) {
    const sgn = d.sign ? "-" : "";
    const digits = d.coeff.toString();
    const numDig = digits.length;
    const adj = d.exp + numDig - 1;
    if (d.exp <= 0 && adj >= -6) {
      if (d.exp === 0) return sgn + digits;
      const pointPos = numDig + d.exp;
      if (pointPos > 0) {
        return sgn + digits.slice(0, pointPos) + "." + digits.slice(pointPos);
      }
      return sgn + "0." + "0".repeat(-pointPos) + digits;
    }
    const mant = numDig === 1 ? digits : digits[0] + "." + digits.slice(1);
    return sgn + mant + "E" + (adj >= 0 ? "+" : "-") + Math.abs(adj).toString();
  }

  // Round a value's coefficient to at most ``prec`` significant digits
  // with ROUND_HALF_EVEN (the default-context rounding).
  function decRoundToPrec(d, prec) {
    const nd = decNumDigits(d.coeff);
    if (BigInt(nd) <= prec) return d;
    const drop = BigInt(nd) - prec;
    const pow = 10n ** drop;
    const q = d.coeff / pow;
    const r = d.coeff % pow;
    const half = pow / 2n;
    let up;
    if (r > half) up = true;
    else if (r < half) up = false;
    else up = (q % 2n) === 1n;
    let coeff = up ? q + 1n : q;
    let exp = d.exp + Number(drop);
    if (decNumDigits(coeff) > Number(prec)) { coeff /= 10n; exp += 1; }
    return { sign: d.sign, coeff, exp };
  }

  function decIsZero(d) { return d.coeff === 0n; }

  function decAdd(a, b) {
    const minExp = Math.min(a.exp, b.exp);
    const ca = a.coeff * 10n ** BigInt(a.exp - minExp);
    const cb = b.coeff * 10n ** BigInt(b.exp - minExp);
    let sum = (a.sign ? -ca : ca) + (b.sign ? -cb : cb);
    let sign;
    if (sum < 0n) { sign = 1; sum = -sum; }
    else if (sum > 0n) { sign = 0; }
    // Exact-zero sum: negative iff BOTH operands negative (ROUND_HALF_EVEN).
    else { sign = (a.sign === 1 && b.sign === 1) ? 1 : 0; }
    return decRoundToPrec({ sign, coeff: sum, exp: minExp }, DEC_PREC);
  }

  function decSub(a, b) {
    // subtract = add(a, copy_negate(b)); copy_negate flips the sign bit
    // even on zero (unlike decNeg, which canonicalises -0 to +0).
    return decAdd(a, { sign: b.sign ? 0 : 1, coeff: b.coeff, exp: b.exp });
  }

  function decMul(a, b) {
    const coeff = a.coeff * b.coeff;
    return decRoundToPrec(
      { sign: a.sign ^ b.sign, coeff, exp: a.exp + b.exp }, DEC_PREC);
  }

  // Exact division mirroring Python __truediv__ (prec 28, HALF_EVEN,
  // ideal-exponent trailing-zero trimming).  Returns null on x/0.
  function decDiv(a, b) {
    if (decIsZero(b)) return null;
    const sign = a.sign ^ b.sign;
    if (decIsZero(a)) return { sign, coeff: 0n, exp: a.exp - b.exp };
    const shiftAmt =
      decNumDigits(b.coeff) - decNumDigits(a.coeff) + Number(DEC_PREC) + 1;
    let exp = (a.exp - b.exp) - shiftAmt;
    let coeff, rem;
    if (shiftAmt >= 0) {
      const scaled = a.coeff * 10n ** BigInt(shiftAmt);
      coeff = scaled / b.coeff;
      rem = scaled % b.coeff;
    } else {
      const divisor = b.coeff * 10n ** BigInt(-shiftAmt);
      coeff = a.coeff / divisor;
      rem = a.coeff % divisor;
    }
    if (rem !== 0n) {
      // Guard digit so the final HALF_EVEN round is correct.
      if (coeff % 5n === 0n) coeff += 1n;
    } else {
      // Exact quotient: reduce toward the ideal exponent (expA - expB).
      const idealExp = a.exp - b.exp;
      while (exp < idealExp && coeff % 10n === 0n) { coeff /= 10n; exp += 1; }
    }
    return decRoundToPrec({ sign, coeff, exp }, DEC_PREC);
  }

  function decNegVal(d) {
    // User-facing negate: canonicalise signed zero to positive, and
    // APPLY THE CONTEXT — Python's unary minus rounds to 28 significant
    // digits (the constructor does not, so a 29+-digit value can sit in
    // the store; PR #877 panel finding A).
    if (decIsZero(d)) return { sign: 0, coeff: 0n, exp: d.exp };
    return decRoundToPrec(
      { sign: d.sign ? 0 : 1, coeff: d.coeff, exp: d.exp }, DEC_PREC);
  }

  function decAbsVal(d) {
    // abs() applies the context too (mirrors Python __abs__).
    return decRoundToPrec({ sign: 0, coeff: d.coeff, exp: d.exp }, DEC_PREC);
  }

  // Exact numeric comparison: -1 / 0 / 1 (never routes through Number).
  function decCompareVal(a, b) {
    const za = decIsZero(a), zb = decIsZero(b);
    if (za && zb) return 0;
    const sa = za ? 0 : (a.sign ? -1 : 1);
    const sb = zb ? 0 : (b.sign ? -1 : 1);
    if (sa !== sb) return sa < sb ? -1 : 1;
    if (sa === 0) return 0;
    const minExp = Math.min(a.exp, b.exp);
    const ca = a.coeff * 10n ** BigInt(a.exp - minExp);
    const cb = b.coeff * 10n ** BigInt(b.exp - minExp);
    const mag = ca < cb ? -1 : (ca > cb ? 1 : 0);
    return sa > 0 ? mag : -mag;
  }

  // Round to N decimal places, mirroring the Python host's
  // ``d.quantize(Decimal(10) ** -places)`` with the InvalidOperation
  // fallback (value returned unchanged).  The quantize target is the
  // QUANTUM'S exponent, and the quantum ``Decimal(10) ** k`` (k = -places
  // >= 0) is itself computed under the context: exact (exponent 0) only
  // while its k+1 digits fit in the 28-digit precision; for k >= 28 it
  // context-rounds to a 28-digit coefficient with exponent k - 27.  So
  // the target exponent for places <= 0 is ``max(0, -places - 27)``, NOT
  // always 0 (PR #877 panel finding B).
  function decRoundPlaces(d, places) {
    if (-places > 999999) {
      // places < -Emax (999999): the Python host's quantum computation
      // Decimal(10)**-places raises Overflow before quantize even sees
      // the operand, and the host falls back to the value unchanged —
      // mirror that here, ahead of every other path including the
      // zero special-case (PR #877 fold-in).
      return d;
    }
    const targetExp =
      places > 0 ? -places : Math.max(0, -places - (Number(DEC_PREC) - 1));
    if (decIsZero(d)) {
      // Zero quantizes to any exponent (coefficient stays one digit, so
      // quantize can never raise); sign is preserved (-0 -> -0E+n).
      return { sign: d.sign, coeff: 0n, exp: targetExp };
    }
    if (d.exp >= targetExp) {
      const diff = d.exp - targetExp;
      // Padded digit count check BEFORE constructing the power (a huge
      // stored exponent must fall back, not build an astronomic BigInt).
      if (decNumDigits(d.coeff) + diff > Number(DEC_PREC)) {
        return d;  // InvalidOperation -> unchanged
      }
      return { sign: d.sign, coeff: d.coeff * 10n ** BigInt(diff), exp: targetExp };
    }
    const drop = targetExp - d.exp;
    if (drop > decNumDigits(d.coeff)) {
      // Every digit is dropped and the remainder is strictly below the
      // rounding half (coeff < 10^digits <= 10^(drop-1) < 5*10^(drop-1)):
      // HALF_EVEN rounds to zero.  Short-circuit before the power.
      return { sign: d.sign, coeff: 0n, exp: targetExp };
    }
    const pow = 10n ** BigInt(drop);
    const q = d.coeff / pow;
    const r = d.coeff % pow;
    const half = pow / 2n;
    let up;
    if (r > half) up = true;
    else if (r < half) up = false;
    else up = (q % 2n) === 1n;
    const coeff = up ? q + 1n : q;
    if (decNumDigits(coeff) > Number(DEC_PREC)) return d;  // InvalidOperation
    return { sign: d.sign, coeff, exp: targetExp };
  }

  // Convert an integer (may exceed Number range) to the canonical form.
  function decFromInt(v) {
    const bi = BigInt(v);
    return { sign: bi < 0n ? 1 : 0, coeff: bi < 0n ? -bi : bi, exp: 0 };
  }

  // Python ``str(float)`` over JS's shortest round-trip digits, so
  // ``decimal_from_float`` mirrors the Python host's ``Decimal(str(v))``
  // INCLUDING the exponent the float repr implies (``str(100.0)`` is
  // "100.0", exponent -1 — which then propagates through arithmetic:
  // from_float(100.0)*2 renders "200.0", not "200").  Rules (CPython
  // float_repr): fixed notation when -4 <= x < 16 (x = decimal exponent
  // of the shortest digits), integral values keep a trailing ".0";
  // otherwise scientific with the exponent zero-padded to >= 2 digits.
  // ``toExponential()`` with no argument returns exactly the shortest
  // uniquely-identifying digits, same as Python's repr digits.
  // Non-finite floats map to the Python Decimal renderings (str(nan) ->
  // Decimal('nan') -> "NaN", etc.); they are stored verbatim and are
  // outside the finite-decimal parity domain (spec §9.7.2).
  function pyFloatRepr(v) {
    if (Number.isNaN(v)) return "NaN";
    if (v === Infinity) return "Infinity";
    if (v === -Infinity) return "-Infinity";
    if (v === 0) return Object.is(v, -0) ? "-0.0" : "0.0";
    const neg = v < 0;
    const [mant, expPart] = Math.abs(v).toExponential().split("e");
    const x = parseInt(expPart, 10);
    const digits = mant.replace(".", "");
    let s;
    if (x < -4 || x >= 16) {
      const m = digits.length === 1 ? digits : digits[0] + "." + digits.slice(1);
      const ea = Math.abs(x).toString();
      s = m + "e" + (x < 0 ? "-" : "+") + (ea.length < 2 ? "0" + ea : ea);
    } else if (x >= 0) {
      s = x + 1 >= digits.length
        ? digits + "0".repeat(x + 1 - digits.length) + ".0"
        : digits.slice(0, x + 1) + "." + digits.slice(x + 1);
    } else {
      s = "0." + "0".repeat(-x - 1) + digits;
    }
    return (neg ? "-" : "") + s;
  }

  const decimalStore = new Map();
  let decimalNextHandle = 1;
  // Store the CANONICAL string form so every op parses a lossless
  // operand and to_string matches Python exactly.
  function decimalAllocVal(d) {
    const h = decimalNextHandle++;
    decimalStore.set(h, decToString(d));
    return h;
  }
  function decimalAlloc(s) {
    const h = decimalNextHandle++;
    decimalStore.set(h, s);
    return h;
  }
  // Read a stored handle back into the value model.  Stored strings are
  // canonical except the non-finite renderings ("NaN" / "Infinity" /
  // "-Infinity"), reachable only via decimal_from_float of a non-finite
  // float — those construct and to_string/to_float fine, but
  // arithmetic/comparison on them is outside the finite-decimal parity
  // domain (spec §9.7.2) and must fail LOUDLY, not corrupt.
  function decimalGet(h) {
    const s = decimalStore.get(h);
    const d = decParse(s);
    if (d === null) {
      throw new Error(
        `Decimal arithmetic/comparison on non-finite value '${s}' is not ` +
        "supported in the browser runtime (spec §9.7.2: the parity " +
        "domain is finite decimals)");
    }
    return d;
  }

  if (needed.has("decimal_from_int")) {
    imports.vera.decimal_from_int = (v) => decimalAllocVal(decFromInt(v));
  }
  if (needed.has("decimal_from_float")) {
    // Mirrors the Python host's ``Decimal(str(v))`` byte-for-byte via
    // the pyFloatRepr port (Python float-repr formatting over the same
    // shortest digits).  Non-finite floats store the Python Decimal
    // renderings verbatim (to_string/to_float match; arithmetic on them
    // is outside the finite-decimal parity domain).
    imports.vera.decimal_from_float = (v) => {
      const s = pyFloatRepr(v);
      const d = decParse(s);
      return d === null ? decimalAlloc(s) : decimalAllocVal(d);
    };
  }
  if (needed.has("decimal_from_string")) {
    imports.vera.decimal_from_string = (ptr, len) => {
      const s = readString(ptr, len);
      // Exponent-token bound checked BEFORE the (parseInt-based) parse.
      const d = decExpTokenInRange(s) ? decParse(s) : null;
      if (d !== null) {
        // Store the canonical form so to_string matches Python exactly.
        const h = decimalAllocVal(d);
        // #573 phase 3: wrap before stuffing into Some.
        // GC-rooting (#706): root the wrapper across the Option alloc —
        // register_wrapper is not a mark root.
        const wrapperPtr = wrapHandle(3, h);
        return gcRooted(wrapperPtr, () => allocOptionSomeI32(wrapperPtr));
      }
      return allocOptionNone();
    };
  }
  if (needed.has("decimal_to_string")) {
    imports.vera.decimal_to_string = (h) => allocString(decimalStore.get(h));
  }
  if (needed.has("decimal_to_float")) {
    imports.vera.decimal_to_float = (h) => Number(decimalStore.get(h));
  }
  if (needed.has("decimal_add")) {
    imports.vera.decimal_add = (a, b) =>
      decimalAllocVal(decAdd(decimalGet(a), decimalGet(b)));
  }
  if (needed.has("decimal_sub")) {
    imports.vera.decimal_sub = (a, b) =>
      decimalAllocVal(decSub(decimalGet(a), decimalGet(b)));
  }
  if (needed.has("decimal_mul")) {
    imports.vera.decimal_mul = (a, b) =>
      decimalAllocVal(decMul(decimalGet(a), decimalGet(b)));
  }
  if (needed.has("decimal_div")) {
    imports.vera.decimal_div = (a, b) => {
      // #573 phase 3: a, b are raw handles (the WASM-side
      // translator unwraps wrapper pointers).  Result is wrapped
      // here before stuffing into Some, matching the Python side.
      const q = decDiv(decimalGet(a), decimalGet(b));
      if (q === null) return allocOptionNone();  // division by zero
      const h = decimalAllocVal(q);
      // GC-rooting (#706): root the wrapper across the Option alloc.
      const wrapperPtr = wrapHandle(3, h);
      return gcRooted(wrapperPtr, () => allocOptionSomeI32(wrapperPtr));
    };
  }
  if (needed.has("decimal_neg")) {
    imports.vera.decimal_neg = (h) =>
      decimalAllocVal(decNegVal(decimalGet(h)));
  }
  if (needed.has("decimal_compare")) {
    imports.vera.decimal_compare = (a, b) => {
      // Exact numeric comparison (never Number()): keeps compare and
      // eq consistent — both dispatch on the same value model.
      const c = decCompareVal(decimalGet(a), decimalGet(b));
      const tag = c < 0 ? 0 : c === 0 ? 1 : 2;
      return allocOrdering(tag);
    };
  }
  if (needed.has("decimal_eq")) {
    // Numeric equality (not string identity): "1.0" == "1".  Shares the
    // exact comparison with decimal_compare so they can never disagree.
    imports.vera.decimal_eq = (a, b) =>
      decCompareVal(decimalGet(a), decimalGet(b)) === 0 ? 1 : 0;
  }
  if (needed.has("decimal_round")) {
    imports.vera.decimal_round = (h, places) =>
      decimalAllocVal(decRoundPlaces(decimalGet(h), Number(places)));
  }
  if (needed.has("decimal_abs")) {
    imports.vera.decimal_abs = (h) =>
      decimalAllocVal(decAbsVal(decimalGet(h)));
  }

  // ── Json host imports ────────────────────────────────────────
  // Json ADT is heap-allocated in WASM memory. Parse/stringify
  // are host imports; utility functions are compiled Vera source.

  // Write a JS value into WASM memory as a Json ADT, returns heap pointer.
  function writeJson(value) {
    // #708 (PR #707): wrap in gcGuard so intermediates
    // (arrPtr, recursive results, string ptrs) can be shadow-pushed
    // and atomically popped at function exit.  Mirrors the CLI
    // ``write_json`` ``_ShadowGuard`` discipline from v0.0.158 (#692).
    return gcGuard(() => writeJsonImpl(value));
  }
  function writeJsonImpl(value) {
    if (value === null || value === undefined) {
      // JNull — tag=0, total=8
      const ptr = alloc(8);
      writeI32(ptr, 0);
      return ptr;
    }
    if (typeof value === "boolean") {
      // JBool(Bool) — tag=1, i32 at offset 4, total=8
      const ptr = alloc(8);
      writeI32(ptr, 1);
      writeI32(ptr + 4, value ? 1 : 0);
      return ptr;
    }
    if (typeof value === "number") {
      // JNumber(Float64) — tag=2, f64 at offset 8, total=16
      const ptr = alloc(16);
      writeI32(ptr, 2);
      writeF64(ptr + 8, value);
      return ptr;
    }
    if (typeof value === "string") {
      // JString(String) — tag=3, i32_pair at offset 4, total=16
      //
      // #708: allocate the JString body first, push it onto the
      // shadow stack, then allocate the string buffer.  The
      // ``allocString`` call below can fire ``$gc_collect``; without
      // rooting the body, it gets reclaimed and the writes scribble
      // freed memory.
      const ptr = alloc(16);
      writeI32(ptr, 3);
      gcShadowPush(ptr);
      const [sp, sl] = allocString(value);
      writeI32(ptr + 4, sp);
      writeI32(ptr + 8, sl);
      return ptr;
    }
    if (Array.isArray(value)) {
      // JArray(Array<Json>) — tag=4, i32_pair at offset 4, total=16
      //
      // #708: explicitly root ``arrPtr`` (the array backing) and
      // each element's heap ptr before storing into the backing.
      // Without these pushes, EAGER_GC reclaims ``arrPtr`` between
      // the recursive ``writeJson(value[i])`` calls and the writes
      // into it, leaving a JArray with a dangling backing pointer
      // — the failure mode observed on the browser-side
      // ``test_eager_gc_set_of_json_browser``.
      const count = value.length;
      let arrPtr = 0;
      if (count > 0) {
        arrPtr = alloc(count * 4);
        gcShadowPush(arrPtr);
        for (let i = 0; i < count; i++) {
          const ep = writeJson(value[i]);
          // PR #707 review: push ep to root it across writeI32, then
          // pop immediately after the store — once ep lives at
          // ``arrPtr + i * 4`` and arrPtr is rooted, the conservative
          // scan reaches ep via arrPtr's block, so the per-iteration
          // push is no longer needed.  Without the matching pop the
          // shadow stack grew O(count) and risked overflowing
          // ``gc_stack_limit`` on large arrays.
          gcShadowPush(ep);
          writeI32(arrPtr + i * 4, ep);
          gcShadowPop();
        }
      }
      const ptr = alloc(16);
      writeI32(ptr, 4);
      writeI32(ptr + 4, arrPtr);
      writeI32(ptr + 8, count);
      return ptr;
    }
    if (typeof value === "object") {
      // JObject(Map<String, Json>) — tag=5, i32 wrapper ptr at offset 4 (#573)
      //
      // #1293: the entry source is a ``Map`` for anything
      // ``parseJsonOrdered`` built, and iterating one yields insertion
      // order.  ``Object.entries`` is kept for a plain object reaching
      // here from somewhere else, but it is NOT order-preserving —
      // array-index keys come out first, ascending — so nothing on the
      // json_parse path may hand this branch one.
      //
      // #708: each recursive ``writeJson(v)`` call returns a heap
      // ptr stored in the JS-side Map ``m`` only.  Between
      // returning ep and ``m.set(k, ep)``, the result is in a JS
      // local — invisible to the conservative scan.  Push each ep
      // before storing in m, then push wrapperPtr before the
      // final 8-byte alloc.
      const entries = value instanceof Map ? value : Object.entries(value);
      const m = new Map();
      for (const [k, v] of entries) {
        const ep = writeJson(v);
        // PR #707 review: no matching pop here — unlike the JArray
        // branch above, ``m`` is a JS Map (not WASM memory), so
        // ``m.set(k, ep)`` does NOT make ep reachable from the
        // conservative scan.  ep stays on the shadow stack until
        // ``allocMapWrapper(m)`` below builds the WAT-resident bucket
        // array and writes ep into it.  Stack depth is therefore
        // O(n_keys) inside this loop; bounded by the same
        // ``gc_stack_limit`` guard as everything else.  Tracked as
        // a refactor opportunity under #706 (move-to-truth would let
        // allocMapWrapper take a pre-rooted bucket).
        gcShadowPush(ep);
        m.set(k, ep);
      }
      const wrapperPtr = allocMapWrapper(m);
      gcShadowPush(wrapperPtr);
      const ptr = alloc(8);
      writeI32(ptr, 5);
      writeI32(ptr + 4, wrapperPtr);
      return ptr;
    }
    // Fallback: stringify
    return writeJson(String(value));
  }

  // Read a Json ADT from WASM memory back to a JS value.  A JObject
  // decodes to a ``Map``, never to an ordinary object, because an
  // ordinary object cannot carry two things the Json ADT does (#1293):
  //
  //   * Key order.  ES OrdinaryOwnPropertyKeys lists array-index keys
  //     first, in ascending numeric order, so ``{"2":1,"1":2}`` comes
  //     back out as ``{"1":2,"2":1}`` — and insertion order is what the
  //     canonical form of spec §9.7.1 is, matching the reference host,
  //     whose ``dict`` preserves it for free.
  //   * A key literally named ``__proto__``.  ``obj["__proto__"] = v``
  //     runs Object.prototype's setter and creates no own property at
  //     all, so the field disappears from the output entirely.
  //
  // Both are silent, so the Map is not a stylistic preference: it is
  // the only JS shape that round-trips the ADT.
  function readJson(ptr) {
    const tag = readI32(ptr);
    if (tag === 0) return null;
    if (tag === 1) return readI32(ptr + 4) !== 0;
    if (tag === 2) return readF64(ptr + 8);
    if (tag === 3) return readString(readI32(ptr + 4), readI32(ptr + 8));
    if (tag === 4) {
      const arrPtr = readI32(ptr + 4);
      const arrLen = readI32(ptr + 8);
      const result = [];
      for (let i = 0; i < arrLen; i++) {
        result.push(readJson(readI32(arrPtr + i * 4)));
      }
      return result;
    }
    if (tag === 5) {
      // #706: the i32 at +4 is a Map wrapper whose bucket IS the map
      // (bucket-as-truth).  Decode the Map<String, Json> directly; the
      // values are i32 Json heap pointers.  ``decodeMap`` walks the
      // bucket in slot order and already returns a JS ``Map``, so
      // rebuilding the values in place is all that is needed — and
      // keeps the bucket's order, which is the ADT's order.
      const wrapperPtr = readI32(ptr + 4);
      const result = new Map();
      for (const [k, v] of decodeMap(wrapperPtr, 's', 'b')) {
        result.set(String(k), readJson(Number(v)));
      }
      return result;
    }
    console.warn(`readJson: unknown tag ${tag} at pointer ${ptr}; possible memory corruption`);
    return null;
  }

  // Re-read JSON text into a tree whose objects are ``Map``s (#1293).
  //
  // ``JSON.parse`` cannot produce one: its objects are ordinary, so by
  // the time any code sees the result the key order of spec §9.7.1 is
  // already gone (array-index keys hoisted to the front, ascending) and
  // a ``__proto__`` key has become a prototype write.  The caller runs
  // ``JSON.parse`` first and only reaches this scanner on text that
  // parse ACCEPTED, which is what keeps the two implementations from
  // disagreeing about what valid JSON is: the accept/reject decision
  // and its Err message stay ECMAScript's, and so does every *leaf*
  // value — each string and number is handed back to ``JSON.parse`` on
  // its own slice rather than decoded a second way.  This scanner only
  // finds token boundaries and builds containers, so a throw from it is
  // an internal bug, not bad input.
  function parseJsonOrdered(text) {
    let i = 0;
    const fail = (what) => {
      throw new Error(
        `json_parse: ${what} at offset ${i}, in text JSON.parse accepted ` +
        `— the order-preserving re-scan disagrees with JSON.parse`
      );
    };
    const skipWs = () => {
      while (i < text.length) {
        const c = text.charCodeAt(i);
        // RFC 8259 §2 whitespace: space, tab, LF, CR.
        if (c === 0x20 || c === 0x09 || c === 0x0a || c === 0x0d) i++;
        else break;
      }
    };
    const scanString = () => {
      const start = i;
      i++;                                   // opening quote
      for (;;) {
        if (i >= text.length) fail("unterminated string");
        const c = text[i];
        if (c === "\\") { i += 2; continue; }
        i++;
        if (c === '"') break;
      }
      return JSON.parse(text.slice(start, i));
    };
    const scanNumber = () => {
      const start = i;
      while (i < text.length && "+-0123456789.eE".includes(text[i])) i++;
      if (i === start) fail("expected a value");
      return JSON.parse(text.slice(start, i));
    };
    const scanValue = () => {
      skipWs();
      if (i >= text.length) fail("unexpected end of input");
      const c = text[i];
      if (c === "{") {
        i++;
        // A Map, so the order below is the document's.  A repeated key
        // keeps its FIRST position and its LAST value, which is what a
        // Python dict does on the reference host — and what JSON.parse
        // does here, so the two agree on the duplicate case too.
        const out = new Map();
        skipWs();
        if (text[i] === "}") { i++; return out; }
        for (;;) {
          skipWs();
          if (text[i] !== '"') fail("expected a key");
          const k = scanString();
          skipWs();
          if (text[i] !== ":") fail("expected ':'");
          i++;
          out.set(k, scanValue());
          skipWs();
          if (text[i] === ",") { i++; continue; }
          if (text[i] === "}") { i++; return out; }
          fail("expected ',' or '}'");
        }
      }
      if (c === "[") {
        i++;
        const out = [];
        skipWs();
        if (text[i] === "]") { i++; return out; }
        for (;;) {
          out.push(scanValue());
          skipWs();
          if (text[i] === ",") { i++; continue; }
          if (text[i] === "]") { i++; return out; }
          fail("expected ',' or ']'");
        }
      }
      if (c === '"') return scanString();
      if (text.startsWith("true", i)) { i += 4; return true; }
      if (text.startsWith("false", i)) { i += 5; return false; }
      if (text.startsWith("null", i)) { i += 4; return null; }
      return scanNumber();
    };
    const value = scanValue();
    skipWs();
    if (i !== text.length) fail("trailing text");
    return value;
  }

  // Serialize a value ``readJson`` produced into canonical JSON text
  // (spec §9.7.1) — the JS twin of ``dumps_canonical`` in
  // ``vera/wasm/json_serde.py``, kept structurally parallel to it.
  //
  // ``JSON.stringify`` cannot do this job any more: it does not know
  // about ``Map``, and its ordinary-object enumeration is where the key
  // order was being lost.  Leaf rendering is still ECMAScript's —
  // strings through ``JSON.stringify``, finite numbers through
  // ``String``, which IS the Number::toString that JSON.stringify would
  // have used — so the canonical form is unchanged for every value that
  // was already coming out right.
  //
  // Anything outside ``readJson``'s range raises rather than being
  // coerced, matching ``dumps_canonical``'s TypeError: a value that is
  // not a Json value means the ADT walk went wrong, and a
  // plausible-looking string would hide it.
  function stringifyCanonical(value) {
    const parts = [];
    const emit = (node) => {
      if (node === null) { parts.push("null"); return; }
      if (node === true) { parts.push("true"); return; }
      if (node === false) { parts.push("false"); return; }
      if (typeof node === "number") {
        // RFC 8259 has no NaN and no Infinity, so there is no right
        // value to return for one — only a right way to fail.  Bare
        // JSON.stringify writes "null", swapping a value the format
        // cannot carry for a different, perfectly valid one that no
        // later consumer can distinguish from a genuine null.  The
        // reference runtime has always refused; this refuses with the
        // same sentence (#1293).
        if (!Number.isFinite(node)) {
          throw new Error(
            `json_stringify: ${String(node)} is not representable in JSON ` +
            `— RFC 8259 has no NaN or Infinity.  Guard with float_is_nan ` +
            `/ float_is_infinite before serialising.`
          );
        }
        parts.push(String(node));
        return;
      }
      if (typeof node === "string") { parts.push(JSON.stringify(node)); return; }
      if (Array.isArray(node)) {
        parts.push("[");
        node.forEach((item, idx) => {
          if (idx) parts.push(",");
          emit(item);
        });
        parts.push("]");
        return;
      }
      if (node instanceof Map) {
        parts.push("{");
        let first = true;
        for (const [k, v] of node) {
          if (!first) parts.push(",");
          first = false;
          parts.push(JSON.stringify(String(k)));
          parts.push(":");
          emit(v);
        }
        parts.push("}");
        return;
      }
      throw new Error(
        `json_stringify: readJson produced ${typeof node}, which is not a ` +
        `Json value; the ADT walk is wrong`
      );
    };
    emit(value);
    return parts.join("");
  }

  // ── json_parse's accept domain (spec §9.7.1) ──────────────────
  //
  // ``json_parse`` accepts exactly RFC 8259-valid text that decodes to
  // finite numbers and strings of Unicode scalar values; everything
  // else is a handled Err, identically on both hosts, at the parse.  The domain is Vera's
  // own, not whatever the host parser happens to implement — so each
  // exclusion needs an explicit gate on the side whose parser does not
  // already enforce it.
  //
  //   * the bare JavaScript constants: ``JSON.parse`` refuses them for
  //     free here, where Python's ``json.loads`` does not — which is
  //     what the reference host's ``parse_constant`` hook is for.  The
  //     only work on this side is naming the refusal in the shared
  //     sentence rather than in ECMAScript's syntax message.
  //   * a lone-surrogate escape, and a number that overflows to an
  //     infinity: BOTH parsers accept these texts, so both gates are
  //     this host's to enforce as much as the reference host's, and
  //     both are decided on the decoded value by one walk.
  //
  // All three sentences are hand-copied from ``vera/wasm/json_serde.py``
  // (``non_finite_parse_message`` / ``lone_surrogate_message`` /
  // ``non_finite_number_message``) and held against those originals by
  // tests/test_browser.py.

  const NON_FINITE_TOKENS = ["-Infinity", "Infinity", "NaN"];

  function nonFiniteParseMessage(name) {
    return (
      `json_parse: ${name} is not valid JSON — RFC 8259 has no NaN or ` +
      `Infinity.  json_parse accepts RFC 8259 text only, not the ` +
      `JavaScript constants: quote the value as a string, or write null.`
    );
  }

  function nonFiniteNumberMessage(name) {
    return (
      `json_parse: a number in the text overflows to ${name}, which JSON ` +
      `cannot represent — RFC 8259 §6 lets an implementation set limits ` +
      `on the range of numbers it accepts, and Vera's accepted range is ` +
      `the finite Float64 values.  Keep the magnitude at or below ` +
      `1.7976931348623157e308, or carry the value as a string.`
    );
  }

  function loneSurrogateMessage(codePoint) {
    const hex = codePoint.toString(16).toUpperCase().padStart(4, "0");
    return (
      `json_parse: \\u${hex} decodes to a lone surrogate, which ` +
      `is not a Unicode scalar value — a Vera string is a sequence of ` +
      `scalar values, so this text has no representable decoding.  Write ` +
      `the character as a matched high-then-low surrogate escape pair, or ` +
      `remove the escape.`
    );
  }

  // Replace every bare NaN / Infinity / -Infinity with ``0``, reporting
  // the first one replaced.  String literals are copied through
  // untouched, so ``{"k":"NaN"}`` — ordinary JSON — is not a candidate.
  //
  // Used ONLY after JSON.parse has already rejected the text, so it
  // cannot widen the accept domain; it only decides which sentence
  // explains the refusal.  Naming the FIRST constant in document order
  // matches the reference host, whose ``parse_constant`` hook is
  // called left to right and records the first it is handed.
  // A token only counts where a VALUE may begin: at the start of the
  // text, or after '[', ',' or ':'.  Whitespace does not move that.
  // Without the constraint the scan found NaN at offset 1 of "-NaN",
  // substituted, re-parsed "-0" successfully and reported the shared
  // sentence — where the reference host, whose parser never reaches the
  // token at all, gives a plain syntax error.  Note '{' is NOT a
  // value-start: what may follow it is a key.
  function stripBareNonFinite(text) {
    let out = "";
    let first = null;
    let i = 0;
    let atValueStart = true;
    while (i < text.length) {
      const c = text[i];
      if (c === '"') {
        const start = i;
        i++;
        while (i < text.length) {
          if (text[i] === "\\") { i += 2; continue; }
          if (text[i] === '"') { i++; break; }
          i++;
        }
        out += text.slice(start, i);
        atValueStart = false;
        continue;
      }
      // RFC 8259 §2 whitespace: space, tab, LF, CR.
      if (c === " " || c === "\t" || c === "\n" || c === "\r") {
        out += c;
        i++;
        continue;
      }
      if (atValueStart) {
        const token = NON_FINITE_TOKENS.find((t) => text.startsWith(t, i));
        if (token !== undefined) {
          if (first === null) first = token;
          out += "0";
          i += token.length;
          atValueStart = false;
          continue;
        }
      }
      atValueStart = (c === "[" || c === "," || c === ":");
      out += c;
      i++;
    }
    return { first, text: out };
  }

  // The first lone surrogate code unit in a JS string, or null.
  //
  // A JS string is UTF-16, so a paired astral character is STORED as
  // two surrogate code units and is perfectly representable — the pair
  // has to be consumed whole before anything is judged lone, or every
  // emoji in every document would be refused.  The reference host's
  // twin needs no pairing step: ``json.loads`` has already combined a
  // well-formed escape pair into one astral code point, so a plain
  // range test is complete there.  Same rule, two representations of
  // the decoded value.
  function firstLoneSurrogateInString(s) {
    for (let i = 0; i < s.length; i++) {
      const unit = s.charCodeAt(i);
      if (unit >= 0xd800 && unit <= 0xdbff) {
        const next = i + 1 < s.length ? s.charCodeAt(i + 1) : 0;
        if (next >= 0xdc00 && next <= 0xdfff) { i++; continue; }
        return unit;
      }
      if (unit >= 0xdc00 && unit <= 0xdfff) return unit;
    }
    return null;
  }

  // One walk over a parseJsonOrdered tree for both value-level
  // exclusions — a string holding a lone surrogate, and a number that
  // is not finite — returning the Err sentence itself, exactly as
  // ``first_domain_violation`` does on the reference host.  Document
  // order means, for an object, each key before its own value; one
  // traversal for both kinds is what makes "whichever comes first names
  // the refusal" the rule rather than a precedence table the two hosts
  // could implement differently.  Keys are checked as well as values: a
  // key crosses the WASM boundary as a string exactly like a value does.
  //
  // ``1e999`` is where the number arm earns its place: syntactically
  // valid RFC 8259 that JSON.parse accepts, decoding to Infinity, which
  // the bare-constant gate above never sees because the text IS valid
  // JSON.  Same exclusion, a different entry route, its own sentence.
  function firstDomainViolation(node) {
    if (typeof node === "string") {
      const codePoint = firstLoneSurrogateInString(node);
      return codePoint === null ? null : loneSurrogateMessage(codePoint);
    }
    if (typeof node === "number") {
      if (Number.isFinite(node)) return null;
      // NaN is unreachable from here — JSON.parse rejects the bare
      // constant before this walk runs, and no numeric literal decodes
      // to one — but it is named rather than folded into the negative
      // branch, because ``node > 0`` is false for NaN and would report
      // "-Infinity".  The reference host's twin gets the name from
      // ``_NON_FINITE_NAMES``, which covers all three; a host that
      // answers differently on a case neither can reach today is a
      // divergence waiting for the day one of them can.
      const name = Number.isNaN(node)
        ? "NaN"
        : (node > 0 ? "Infinity" : "-Infinity");
      return nonFiniteNumberMessage(name);
    }
    if (Array.isArray(node)) {
      for (const item of node) {
        const found = firstDomainViolation(item);
        if (found !== null) return found;
      }
      return null;
    }
    if (node instanceof Map) {
      for (const [key, item] of node) {
        const codePoint = firstLoneSurrogateInString(String(key));
        if (codePoint !== null) return loneSurrogateMessage(codePoint);
        const found = firstDomainViolation(item);
        if (found !== null) return found;
      }
      return null;
    }
    return null;
  }

  if (needed.has("json_parse")) {
    imports.vera.json_parse = (ptr, len) => {
      const text = readString(ptr, len);
      // Same failure-domain split as hostMdParse: only JSON.parse
      // errors become Err(String); gcGuard-walk failures trap loudly.
      try {
        JSON.parse(text);
      } catch (e) {
        // #1306: if the ONLY thing wrong with the text is a bare
        // JavaScript constant, both hosts say so in one sentence.  The
        // stripped text is handed back to JSON.parse rather than
        // trusted: a token that merely looks like one (``Infinity_x``)
        // leaves the document malformed, so it falls through to the
        // host parser's own syntax message, which is what every other
        // malformed input has always reported.
        const probe = stripBareNonFinite(text);
        if (probe.first !== null) {
          let strippedParses = true;
          try { JSON.parse(probe.text); } catch { strippedParses = false; }
          if (strippedParses) {
            return allocResultErrString(nonFiniteParseMessage(probe.first));
          }
        }
        return allocResultErrString(e.message || String(e));
      }
      // #1293: JSON.parse decided whether the text is JSON; its result
      // is discarded because it cannot carry key order.  The tree the
      // ADT is built from comes from the order-preserving re-scan.
      const parsed = parseJsonOrdered(text);
      // The value-level half of the domain, checked on the decoded
      // VALUE and before anything crosses into WASM memory.  A lone
      // surrogate (#1308) has no UTF-8 encoding and no Vera string can
      // hold one: past this point writeJson reaches allocString, whose
      // TextEncoder silently substituted U+FFFD — a different value
      // than the text encoded, with nothing to tell the caller.  A
      // number that overflowed to an infinity (#1306) would reach
      // json_stringify's refusal instead, one call too late and on a
      // value the domain says never gets in.
      const violation = firstDomainViolation(parsed);
      if (violation !== null) {
        return allocResultErrString(violation);
      }
      // #708 (PR #707): wrap in gcGuard and push jsonPtr
      // before allocResultOkI32's alloc can fire GC.  writeJson
      // has its own internal guard that pops on return — by the
      // time control returns here, jsonPtr is unrooted again.
      return gcGuard(() => {
        const jsonPtr = writeJson(parsed);
        gcShadowPush(jsonPtr);
        return allocResultOkI32(jsonPtr);
      });
    };
  }

  if (needed.has("json_stringify")) {
    imports.vera.json_stringify = (ptr) => {
      // #1293: the canonical form of spec §9.7.1, emitted by a walk
      // that mirrors the reference host's ``dumps_canonical`` — compact
      // separators, insertion-ordered keys, ECMAScript number
      // rendering, and a refusal on a non-finite number rather than the
      // silent ``null`` bare JSON.stringify would substitute.
      return allocString(stringifyCanonical(readJson(ptr)));
    };
  }

  // ── Http host imports ─────────────────────────────────────────
  // Uses synchronous XMLHttpRequest (browser) with a guard for
  // non-browser runtimes (Node.js) that returns a clear Err.
  if (needed.has("http_get")) {
    imports.vera.http_get = (urlPtr, urlLen) => {
      const url = readString(urlPtr, urlLen);
      try {
        if (typeof XMLHttpRequest === "undefined") {
          return allocResultErrString(
            "Unsupported runtime: synchronous HTTP requires XMLHttpRequest (browser only)");
        }
        const xhr = new XMLHttpRequest();
        xhr.open('GET', url, false);
        xhr.send();
        if (xhr.status >= 200 && xhr.status < 300) {
          return allocResultOkString(xhr.responseText);
        }
        return allocResultErrString(`HTTP ${xhr.status}: ${xhr.statusText}`);
      } catch (e) {
        return allocResultErrString(e.message || 'HTTP request failed');
      }
    };
  }

  if (needed.has("http_post")) {
    imports.vera.http_post = (urlPtr, urlLen, bodyPtr, bodyLen) => {
      const url = readString(urlPtr, urlLen);
      const body = readString(bodyPtr, bodyLen);
      try {
        if (typeof XMLHttpRequest === "undefined") {
          return allocResultErrString(
            "Unsupported runtime: synchronous HTTP requires XMLHttpRequest (browser only)");
        }
        const xhr = new XMLHttpRequest();
        xhr.open('POST', url, false);
        xhr.setRequestHeader('Content-Type', 'application/json');
        xhr.send(body);
        if (xhr.status >= 200 && xhr.status < 300) {
          return allocResultOkString(xhr.responseText);
        }
        return allocResultErrString(`HTTP ${xhr.status}: ${xhr.statusText}`);
      } catch (e) {
        return allocResultErrString(e.message || 'HTTP request failed');
      }
    };
  }

  // ── Fused-async host imports (#841) ────────────────────────────
  // The browser runtime stays EAGER (spec-conformant: §9.5.4 says an
  // implementation MAY evaluate concurrently; value semantics are
  // identical either way).  The request fires synchronously at the
  // async(...) point — preserving program order for request issuance,
  // exactly like the eager identity lowering — but only the raw
  // (isOk, payload) strings are buffered JS-side; the Result ADT is
  // built at await time on demand.  Buffering the strings rather than
  // an eagerly-built ADT pointer matters for GC: a guest heap pointer
  // held only in a JS map is invisible to the conservative scan and
  // would be swept (#570/#692 class); JS strings live host-side.
  const futureStore = new Map();
  let nextFutureHandle = 1;

  const syncFetch = (method, url, body) => {
    try {
      if (typeof XMLHttpRequest === "undefined") {
        return [false,
          "Unsupported runtime: synchronous HTTP requires XMLHttpRequest (browser only)"];
      }
      const xhr = new XMLHttpRequest();
      xhr.open(method, url, false);
      if (method === 'POST') {
        xhr.setRequestHeader('Content-Type', 'application/json');
        xhr.send(body);
      } else {
        xhr.send();
      }
      if (xhr.status >= 200 && xhr.status < 300) {
        return [true, xhr.responseText];
      }
      return [false, `HTTP ${xhr.status}: ${xhr.statusText}`];
    } catch (e) {
      return [false, e.message || 'HTTP request failed'];
    }
  };

  if (needed.has("async_http_get")) {
    imports.vera.async_http_get = (urlPtr, urlLen) => {
      const url = readString(urlPtr, urlLen);
      const handle = nextFutureHandle++;
      futureStore.set(handle, syncFetch('GET', url));
      return handle;
    };
  }

  if (needed.has("async_http_post")) {
    imports.vera.async_http_post = (urlPtr, urlLen, bodyPtr, bodyLen) => {
      const url = readString(urlPtr, urlLen);
      const body = readString(bodyPtr, bodyLen);
      const handle = nextFutureHandle++;
      futureStore.set(handle, syncFetch('POST', url, body));
      return handle;
    };
  }

  if (needed.has("async_await")) {
    imports.vera.async_await = (handle) => {
      const outcome = futureStore.get(handle);
      if (outcome === undefined) {
        // Mirrors the native defensive branch: a live wrapper implies
        // a live store entry; surface a value-level Err, not a crash.
        return allocResultErrString(
          "await: future was already reclaimed (#841 invariant violation — please report)");
      }
      const [isOk, payload] = outcome;
      return isOk ? allocResultOkString(payload)
                  : allocResultErrString(payload);
    };
  }

  // ── Inference host imports ─────────────────────────────────────
  // LLM API keys cannot safely be embedded in client-side JavaScript —
  // they would be visible in page source and network requests.  Return
  // a rich Err explaining the constraint and the recommended pattern.

  if (needed.has("inference_complete")) {
    imports.vera.inference_complete = (promptPtr, promptLen) => {
      return allocResultErrString(
        "The Inference effect cannot run in the browser directly. " +
        "LLM API keys embedded in client-side JavaScript are visible in " +
        "page source and network requests, creating a serious security risk. " +
        "To use Inference in a browser application, implement a server-side " +
        "proxy endpoint that holds the API key and forwards completion " +
        "requests from your frontend. Call that endpoint with the Http effect instead."
      );
    };
  }

  // ── DB host imports (#229) ─────────────────────────────────────
  // SQL execution needs a database driver and credentials that cannot
  // live safely in client-side JavaScript.  Both ops return a
  // Result<_, String>, so a deliberate Err is a valid value on either op: a
  // Result is tag-dispatched (tag 1 = Err, str_ptr @+4, str_len @+8), so a
  // fully-formed Err never touches the Ok payload — whose size differs by op
  // (db_query's grid Ok is 12 bytes, db_execute's Int Ok is 16).  Mirrors the
  // Inference stub above.

  if (needed.has("db_query")) {
    imports.vera.db_query = (sqlPtr, sqlLen, paramsPtr, paramsCount) => {
      return allocResultErrString(
        "The DB effect cannot run in the browser directly. " +
        "Database access requires a driver and credentials that would be " +
        "exposed in client-side JavaScript. To use DB in a browser application, " +
        "run the query on a server-side endpoint and call it with the Http effect instead."
      );
    };
  }

  if (needed.has("db_execute")) {
    imports.vera.db_execute = (sqlPtr, sqlLen, paramsPtr, paramsCount) => {
      return allocResultErrString(
        "The DB effect cannot run in the browser directly. " +
        "Database access requires a driver and credentials that would be " +
        "exposed in client-side JavaScript. To use DB in a browser application, " +
        "run the statement on a server-side endpoint and call it with the Http effect instead."
      );
    };
  }

  // ── Random host imports (#465) ─────────────────────────────────
  // All three back onto Math.random() — fast, non-cryptographic,
  // adequate for games and simulations.  No determinism / seeding
  // is offered yet (would require a separate `Random.seed` op
  // tracked as future work in #465).

  if (needed.has("random_int")) {
    // random_int(low: i64, high: i64) -> i64.  Inclusive range.
    // Math.random() returns [0, 1); scale to (high - low + 1)
    // values then offset by low.  BigInt arithmetic keeps i64
    // semantics on the WASM boundary.
    imports.vera.random_int = (lowBig, highBig) => {
      // Guard: i64 can hold values outside JS's 53-bit safe integer
      // range.  Silently coercing a BigInt like 2^60 to Number loses
      // precision and the returned span/result can be off by
      // thousands.  Throw a clear error instead so callers see a
      // real failure instead of subtle wrong numbers.  The WASM
      // runtime turns this into a trap the host can surface.
      const MIN_SAFE = BigInt(Number.MIN_SAFE_INTEGER);
      const MAX_SAFE = BigInt(Number.MAX_SAFE_INTEGER);
      if (lowBig < MIN_SAFE || highBig > MAX_SAFE) {
        throw new Error(
          `random_int bounds exceed JavaScript safe integer range ` +
          `[${Number.MIN_SAFE_INTEGER}, ${Number.MAX_SAFE_INTEGER}]; ` +
          `got [${lowBig}, ${highBig}]. ` +
          `Use smaller bounds or adjust the runtime to use BigInt arithmetic.`
        );
      }
      if (highBig < lowBig) {
        throw new Error(
          `random_int requires low <= high; got low=${lowBig}, high=${highBig}.`
        );
      }
      const low = Number(lowBig);
      const high = Number(highBig);
      const span = high - low + 1;
      const r = Math.floor(Math.random() * span);
      return BigInt(low + r);
    };
  }
  if (needed.has("random_float")) {
    // random_float() -> f64 in [0.0, 1.0)
    imports.vera.random_float = () => Math.random();
  }
  if (needed.has("random_bool")) {
    // random_bool() -> i32 (0 or 1)
    imports.vera.random_bool = () => (Math.random() < 0.5 ? 1 : 0);
  }

  // ── Math host imports (#467) ───────────────────────────────────
  // Log/trig families — all Float64 → Float64 except atan2 which
  // is (y, x) → angle.  Constants pi/e and sign/clamp/float_clamp
  // are inlined in WAT by the compiler, so they don't appear here.
  // `Math.log`, `Math.log2`, `Math.log10` and the trig functions
  // follow IEEE 754: NaN for out-of-domain inputs, ±Infinity for
  // overflow.  Matches the Python runtime's `math.*` semantics.
  const _mathUnary = {
    log:   Math.log,
    log2:  Math.log2,
    log10: Math.log10,
    sin:   Math.sin,
    cos:   Math.cos,
    tan:   Math.tan,
    asin:  Math.asin,
    acos:  Math.acos,
    atan:  Math.atan,
  };
  for (const [name, fn] of Object.entries(_mathUnary)) {
    if (needed.has(name)) {
      imports.vera[name] = fn;
    }
  }
  if (needed.has("atan2")) {
    // Note argument order: (y, x), matching POSIX / Math.atan2.
    imports.vera.atan2 = Math.atan2;
  }

  // ── Html host imports ──────────────────────────────────────────
  // Lenient HTML parser using DOMParser (browser) or returning Err
  // in non-browser runtimes (Node.js).

  // Write a JS HTML node object to WASM memory as HtmlNode ADT.
  // HtmlElement: tag=0, String(name)+4, Map handle+12, Array(ptr,len)+16, total=24
  // HtmlText: tag=1, String(content)+4, total=16
  // HtmlComment: tag=2, String(content)+4, total=16
  function writeHtml(node) {
    // #708 (PR #707): same gcGuard discipline as writeJson.
    return gcGuard(() => writeHtmlImpl(node));
  }
  function writeHtmlImpl(node) {
    if (node.tag === 'comment') {
      // #708: root the comment body's ptr before allocString fires GC.
      const ptr = alloc(16);
      writeI32(ptr, 2);
      gcShadowPush(ptr);
      const [sp, sl] = allocString(node.content || '');
      writeI32(ptr + 4, sp);
      writeI32(ptr + 8, sl);
      return ptr;
    }
    if (node.tag === 'text') {
      // Same #708 discipline as the comment branch.
      const ptr = alloc(16);
      writeI32(ptr, 1);
      gcShadowPush(ptr);
      const [sp, sl] = allocString(node.content || '');
      writeI32(ptr + 4, sp);
      writeI32(ptr + 8, sl);
      return ptr;
    }
    // element
    //
    // #708: root each intermediate before any alloc that could
    // fire GC.  The CLI ``write_html`` uses ``_ShadowGuard``
    // pushing for the same set of intermediates (np, wrapperPtr,
    // arrPtr, and each recursive child result).
    const [np, nl] = allocString(node.name || '');
    gcShadowPush(np);
    // Attributes as Map<String, String>
    const m = new Map();
    if (node.attrs) {
      for (const [k, v] of Object.entries(node.attrs)) {
        m.set(k, v);
      }
    }
    // #573: store wrapper-ADT pointer, not raw handle, so user-
    // level map_get / map_contains on the attrs field unwraps
    // correctly and the entry is reclaimable by the GC.
    const wrapperPtr = allocMapWrapper(m);
    gcShadowPush(wrapperPtr);
    // Children array
    const children = node.children || [];
    const count = children.length;
    let arrPtr = 0;
    if (count > 0) {
      arrPtr = alloc(count * 4);
      gcShadowPush(arrPtr);
      for (let i = 0; i < count; i++) {
        const cp = writeHtml(children[i]);
        // PR #707 review: same push+pop pairing as the JArray loop in
        // writeJson.  Once cp is stored at ``arrPtr + i * 4`` and
        // arrPtr is rooted, the conservative scan reaches cp via
        // arrPtr's block, so the per-iteration push can be popped.
        // Keeps shadow stack depth O(1) instead of O(count).
        gcShadowPush(cp);
        writeI32(arrPtr + i * 4, cp);
        gcShadowPop();
      }
    }
    const ptr = alloc(24);
    writeI32(ptr, 0);
    writeI32(ptr + 4, np);
    writeI32(ptr + 8, nl);
    writeI32(ptr + 12, wrapperPtr);
    writeI32(ptr + 16, arrPtr);
    writeI32(ptr + 20, count);
    return ptr;
  }

  // Read an HtmlNode ADT from WASM memory to a JS object.
  function readHtml(ptr) {
    const tag = readI32(ptr);
    if (tag === 1) {
      const sp = readI32(ptr + 4);
      const sl = readI32(ptr + 8);
      return { tag: 'text', content: readString(sp, sl) };
    }
    if (tag === 2) {
      const sp = readI32(ptr + 4);
      const sl = readI32(ptr + 8);
      return { tag: 'comment', content: readString(sp, sl) };
    }
    // tag === 0: element
    const np = readI32(ptr + 4);
    const nl = readI32(ptr + 8);
    const name = readString(np, nl);
    // #706: the i32 at +12 is a Map wrapper whose bucket IS the
    // attributes Map<String, String> (bucket-as-truth).
    const wrapperPtr = readI32(ptr + 12);
    const arrPtr = readI32(ptr + 16);
    const arrLen = readI32(ptr + 20);
    const attrs = {};
    for (const [k, v] of decodeMap(wrapperPtr, 's', 's')) {
      attrs[String(k)] = String(v);
    }
    const children = [];
    for (let i = 0; i < arrLen; i++) {
      children.push(readHtml(readI32(arrPtr + i * 4)));
    }
    return { tag: 'element', name, attrs, children };
  }

  // Convert DOM node tree to HtmlNode JS object
  function domToHtml(domNode) {
    if (domNode.nodeType === 8) {
      return { tag: 'comment', content: domNode.textContent || '' };
    }
    if (domNode.nodeType === 3) {
      return { tag: 'text', content: domNode.textContent || '' };
    }
    if (domNode.nodeType === 1) {
      const attrs = {};
      for (const attr of domNode.attributes) {
        attrs[attr.name] = attr.value;
      }
      const children = [];
      for (const child of domNode.childNodes) {
        children.push(domToHtml(child));
      }
      return { tag: 'element', name: domNode.tagName.toLowerCase(), attrs, children };
    }
    // Other node types: treat as text
    return { tag: 'text', content: domNode.textContent || '' };
  }

  // Simple HTML to string serializer
  function escapeHtml(s) {
    return s.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
  }
  function escapeAttr(s) {
    return s.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/"/g, '&quot;');
  }

  function htmlToString(node) {
    if (node.tag === 'text') return escapeHtml(node.content || '');
    if (node.tag === 'comment') {
      const c = (node.content || '').replace(/-->/g, '-- >');
      return `<!--${c}-->`;
    }
    const name = node.name || 'div';
    let attrStr = '';
    if (node.attrs) {
      for (const [k, v] of Object.entries(node.attrs)) {
        attrStr += ` ${k}="${escapeAttr(v)}"`;
      }
    }
    const voidElems = new Set(['area','base','br','col','embed','hr','img','input','link','meta','param','source','track','wbr']);
    if (voidElems.has(name.toLowerCase())) return `<${name}${attrStr}>`;
    const inner = (node.children || []).map(htmlToString).join('');
    return `<${name}${attrStr}>${inner}</${name}>`;
  }

  // Extract text content recursively
  function htmlText(node) {
    if (node.tag === 'text') return node.content || '';
    if (node.tag === 'comment') return '';
    return (node.children || []).map(htmlText).join('');
  }

  // Simple CSS selector matcher
  function htmlMatchesSelector(node, sel) {
    if (node.tag !== 'element') return false;
    if (sel.startsWith('#')) return (node.attrs || {}).id === sel.slice(1);
    if (sel.startsWith('.')) return ((node.attrs || {}).class || '').split(/\s+/).includes(sel.slice(1));
    if (sel.startsWith('[') && sel.endsWith(']')) return sel.slice(1, -1) in (node.attrs || {});
    return node.name === sel;
  }

  // CSS selector query (descendant combinator)
  function htmlQuery(node, selector) {
    const parts = selector.trim().split(/\s+/);
    if (!parts.length) return [];
    const results = [];
    function walk(n, depth) {
      if (n.tag !== 'element') return;
      if (htmlMatchesSelector(n, parts[depth])) {
        if (depth === parts.length - 1) {
          results.push(n);
        } else {
          for (const c of (n.children || [])) walk(c, depth + 1);
        }
      }
      for (const c of (n.children || [])) walk(c, 0);
    }
    walk(node, 0);
    return results;
  }

  if (needed.has("html_parse")) {
    imports.vera.html_parse = (ptr, len) => {
      const text = readString(ptr, len);
      // Same failure-domain split as hostMdParse: only parsing
      // (DOMParser + domToHtml) failures become Err(String); a
      // failure in the gcGuard walk below traps loudly.
      let root;
      try {
        if (typeof DOMParser !== "undefined") {
          const parser = new DOMParser();
          const doc = parser.parseFromString(text, 'text/html');
          root = domToHtml(doc.body);
        } else {
          // Node.js fallback: simple regex-based parser for basic HTML
          // Just wrap content as a single text node
          return allocResultErrString(
            "Unsupported runtime: HTML parsing requires DOMParser (browser only)");
        }
      } catch (e) {
        return allocResultErrString(String(e.message || 'HTML parse error'));
      }
      // #708 (PR #707): same gcGuard discipline as
      // json_parse — root nodePtr before allocResultOkI32 fires
      // GC.
      return gcGuard(() => {
        const nodePtr = writeHtml(root);
        gcShadowPush(nodePtr);
        return allocResultOkI32(nodePtr);
      });
    };
  }

  if (needed.has("html_to_string")) {
    imports.vera.html_to_string = (ptr) => {
      const node = readHtml(ptr);
      const text = htmlToString(node);
      return allocString(text);
    };
  }

  if (needed.has("html_query")) {
    imports.vera.html_query = (nodePtr, selPtr, selLen) => {
      const node = readHtml(nodePtr);
      const selector = readString(selPtr, selLen);
      const matches = htmlQuery(node, selector);
      const count = matches.length;
      let arrPtr = 0;
      if (count > 0) {
        arrPtr = alloc(count * 4);
        // GC-rooting (#706): root arrPtr across writeHtml's allocations.
        gcRooted(arrPtr, () => {
          for (let i = 0; i < count; i++) {
            writeI32(arrPtr + i * 4, writeHtml(matches[i]));
          }
        });
      }
      return [arrPtr, count];
    };
  }

  if (needed.has("html_text")) {
    imports.vera.html_text = (ptr) => {
      const node = readHtml(ptr);
      return allocString(htmlText(node));
    };
  }

  return imports;
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/**
 * Initialize the Vera runtime from a URL (browser) or fetch Response.
 * Idempotent — calling init() twice is a no-op.
 *
 * @param {string|URL|Response} [wasmSource] URL to .wasm file, or a Response.
 *   Defaults to './module.wasm' relative to this module.
 * @param {object} [options]
 * @param {string[]} [options.stdin] Pre-queued input lines for IO.read_line.
 * @param {string[]} [options.args] Command-line arguments for IO.args.
 * @param {Object<string,string>} [options.env] Environment variables for IO.get_env.
 */
export async function init(wasmSource, options = {}) {
  if (wasm) return;

  // Apply options
  if (options.stdin) stdinQueue = [...options.stdin];
  if (options.args) cliArgs = [...options.args];
  if (options.env) envVars = { ...options.env };

  let module;
  let moduleBytes; // #920: raw bytes, for state-import type reflection
  if (wasmSource instanceof ArrayBuffer || ArrayBuffer.isView(wasmSource)) {
    // Node.js path: raw bytes
    moduleBytes = ArrayBuffer.isView(wasmSource)
      ? new Uint8Array(wasmSource.buffer, wasmSource.byteOffset, wasmSource.byteLength)
      : new Uint8Array(wasmSource);
    module = await WebAssembly.compile(wasmSource);
  } else {
    // Browser path: URL or Response
    const url = wasmSource ?? new URL('./module.wasm', import.meta.url);
    const response = url instanceof Response ? url : await fetch(url);
    const bytes = await response.arrayBuffer();
    moduleBytes = new Uint8Array(bytes);
    module = await WebAssembly.compile(bytes);
  }

  const importObject = buildImportObject(module, moduleBytes);
  const instance = await WebAssembly.instantiate(module, importObject);
  wasm = instance.exports;
}

/**
 * Initialize the Vera runtime from raw WASM bytes (Node.js convenience).
 * @param {ArrayBuffer|Uint8Array|Buffer} bytes
 * @param {object} [options] Same options as init().
 */
export async function initFromBytes(bytes, options = {}) {
  return init(bytes, options);
}

/**
 * Call an exported WASM function by name.
 * @param {string} fnName
 * @param {...(number|bigint)} args
 * @returns {number|bigint|undefined}
 */
export function call(fnName, ...args) {
  if (!wasm) throw new Error('Runtime not initialized — call init() first');
  const fn = wasm[fnName];
  if (typeof fn !== 'function') {
    throw new Error(`No exported function '${fnName}'`);
  }
  exitCode = null;
  lastViolation = '';
  lastOverflow = false;
  try {
    return fn(...args);
  } catch (e) {
    if (e instanceof VeraExit) {
      exitCode = e.code;
      return undefined;
    }
    // Check for contract violation message
    if (lastViolation && e instanceof WebAssembly.RuntimeError) {
      throw new Error(lastViolation);
    }
    // #808: integer-overflow guard fired before the trap
    if (lastOverflow && e instanceof WebAssembly.RuntimeError) {
      throw new Error('Integer overflow');
    }
    throw e;
  }
}

/** Return all captured IO.print output. */
export function getStdout() {
  return stdoutBuf;
}

/** Clear captured IO.print output. */
export function clearStdout() {
  stdoutBuf = '';
}

/** Return captured IO.stderr output (#463). */
export function getStderr() {
  return stderrBuf;
}

/** Clear captured IO.stderr output. */
export function clearStderr() {
  stderrBuf = '';
}

/** Return current State<T> top-of-stack values. */
export function getState() {
  const result = {};
  for (const [k, v] of Object.entries(stateCells)) {
    const top = v[v.length - 1];
    result[k] = typeof top === 'bigint' ? Number(top) : top;
  }
  return result;
}

/** Reset all State<T> stacks to a single default cell. */
export function resetState() {
  for (const key of Object.keys(stateCells)) {
    stateCells[key] = [stateDefaultFor(key)];
  }
}

/** Return the exit code from IO.exit, or null if not called. */
export function getExitCode() {
  return exitCode;
}

/** Reset all runtime state for a fresh execution. */
export function reset() {
  stdoutBuf = '';
  stderrBuf = '';
  lastViolation = '';
  lastOverflow = false;
  exitCode = null;
  resetState();
  stdinQueue = [];
}

/** Return list of exported function names. */
export function getExports() {
  if (!wasm) return [];
  return Object.entries(wasm)
    .filter(([_, v]) => typeof v === 'function')
    .map(([k]) => k)
    .filter(k => k !== 'alloc');
}

export { VeraExit };
export default init;
