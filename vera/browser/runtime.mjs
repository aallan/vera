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
const stateCells = {}; // State<T> stacks: { TypeName: [value, ...] } — top is [-1]
let stdinQueue = [];   // Pre-queued input lines for IO.read_line
let cliArgs = [];      // Command-line arguments for IO.args
let envVars = {};      // Environment variables for IO.get_env
let exitCode = null;   // Set by IO.exit

const decoder = new TextDecoder('utf-8');
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

/** Allocate Result.Ok(String) → heap pointer. Tag=0, str at +4/+8. */
function allocResultOkString(str) {
  const [strPtr, strLen] = allocString(str);
  const ptr = alloc(12);
  writeI32(ptr, 0);            // tag = Ok
  writeI32(ptr + 4, strPtr);
  writeI32(ptr + 8, strLen);
  return ptr;
}

/** Allocate Result.Err(String) → heap pointer. Tag=1, str at +4/+8. */
function allocResultErrString(str) {
  const [strPtr, strLen] = allocString(str);
  const ptr = alloc(12);
  writeI32(ptr, 1);            // tag = Err
  writeI32(ptr + 4, strPtr);
  writeI32(ptr + 8, strLen);
  return ptr;
}

/** Allocate Result.Ok(()) → heap pointer. Tag=0, no payload. */
function allocResultOkUnit() {
  const ptr = alloc(4);
  writeI32(ptr, 0);            // tag = Ok
  return ptr;
}

/** Allocate Result.Ok(i32) → heap pointer. Tag=0, value at +4. */
function allocResultOkI32(value) {
  const ptr = alloc(8);
  writeI32(ptr, 0);            // tag = Ok
  writeI32(ptr + 4, value);
  return ptr;
}

/** Allocate Option.Some(String) → heap pointer. Tag=1, str at +4/+8. */
function allocOptionSomeString(str) {
  const [strPtr, strLen] = allocString(str);
  const ptr = alloc(12);
  writeI32(ptr, 1);            // tag = Some
  writeI32(ptr + 4, strPtr);
  writeI32(ptr + 8, strLen);
  return ptr;
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
  for (let i = 0; i < count; i++) {
    const [sPtr, sLen] = allocString(strings[i]);
    writeI32(backingPtr + i * 8, sPtr);
    writeI32(backingPtr + i * 8 + 4, sLen);
  }
  return [backingPtr, count];
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

// -- Inline parser --

function parseInlines(text) {
  const result = [];
  let i = 0;
  const n = text.length;

  while (i < n) {
    // Code span
    if (text[i] === '`') {
      let end = text.indexOf('`', i + 1);
      if (end !== -1) {
        result.push(new MdCode(text.slice(i + 1, end)));
        i = end + 1;
        continue;
      }
    }

    // Image: ![alt](url)
    if (text[i] === '!' && i + 1 < n && text[i + 1] === '[') {
      const altEnd = text.indexOf(']', i + 2);
      if (altEnd !== -1 && altEnd + 1 < n && text[altEnd + 1] === '(') {
        const urlEnd = text.indexOf(')', altEnd + 2);
        if (urlEnd !== -1) {
          const alt = text.slice(i + 2, altEnd);
          const url = text.slice(altEnd + 2, urlEnd);
          result.push(new MdImage(alt, url));
          i = urlEnd + 1;
          continue;
        }
      }
    }

    // Link: [text](url)
    if (text[i] === '[') {
      const textEnd = text.indexOf(']', i + 1);
      if (textEnd !== -1 && textEnd + 1 < n && text[textEnd + 1] === '(') {
        const urlEnd = text.indexOf(')', textEnd + 2);
        if (urlEnd !== -1) {
          const linkText = text.slice(i + 1, textEnd);
          const url = text.slice(textEnd + 2, urlEnd);
          result.push(new MdLink(parseInlines(linkText), url));
          i = urlEnd + 1;
          continue;
        }
      }
    }

    // Strong: ** or __
    if ((text[i] === '*' && i + 1 < n && text[i + 1] === '*') ||
        (text[i] === '_' && i + 1 < n && text[i + 1] === '_')) {
      const marker = text.slice(i, i + 2);
      const end = text.indexOf(marker, i + 2);
      if (end !== -1) {
        result.push(new MdStrong(parseInlines(text.slice(i + 2, end))));
        i = end + 2;
        continue;
      }
    }

    // Emphasis: * or _
    if (text[i] === '*' || text[i] === '_') {
      const marker = text[i];
      // Avoid matching ** as emphasis
      if (i + 1 < n && text[i + 1] !== marker) {
        const end = text.indexOf(marker, i + 1);
        if (end !== -1) {
          result.push(new MdEmph(parseInlines(text.slice(i + 1, end))));
          i = end + 1;
          continue;
        }
      }
    }

    // Plain text — accumulate until next special character
    let textStart = i;
    i++;
    while (i < n && !'`*_!['.includes(text[i])) {
      i++;
    }
    result.push(new MdText(text.slice(textStart, i)));
  }
  return result;
}

// -- Block parser --

function parseBlocks(text) {
  const lines = text.split('\n');
  const blocks = [];
  let i = 0;

  while (i < lines.length) {
    const line = lines[i];

    // Empty line — skip
    if (line.trim() === '') {
      i++;
      continue;
    }

    // ATX heading: # ... ######
    const headingMatch = line.match(/^(#{1,6})\s+(.*?)(?:\s+#+)?$/);
    if (headingMatch) {
      const level = headingMatch[1].length;
      const content = headingMatch[2].trim();
      blocks.push(new MdHeading(level, parseInlines(content)));
      i++;
      continue;
    }

    // Thematic break: --- or *** or ___ (3+ characters)
    if (/^(\*{3,}|-{3,}|_{3,})\s*$/.test(line)) {
      blocks.push(new MdThematicBreak());
      i++;
      continue;
    }

    // Fenced code block: ``` or ~~~
    const fenceMatch = line.match(/^(`{3,}|~{3,})(.*?)$/);
    if (fenceMatch) {
      const fence = fenceMatch[1];
      const lang = fenceMatch[2].trim();
      const codeLines = [];
      i++;
      while (i < lines.length) {
        if (lines[i].startsWith(fence[0].repeat(fence.length)) &&
            lines[i].trim() === fence[0].repeat(fence.length)) {
          i++;
          break;
        }
        codeLines.push(lines[i]);
        i++;
      }
      blocks.push(new MdCodeBlock(lang, codeLines.join('\n')));
      continue;
    }

    // Block quote: > ...
    if (line.startsWith('> ') || line === '>') {
      const quoteLines = [];
      while (i < lines.length && (lines[i].startsWith('> ') || lines[i] === '>')) {
        quoteLines.push(lines[i].startsWith('> ') ? lines[i].slice(2) : '');
        i++;
      }
      const inner = parseBlocks(quoteLines.join('\n'));
      blocks.push(new MdBlockQuote(inner));
      continue;
    }

    // Unordered list: - or * (with space)
    if (/^[-*]\s/.test(line)) {
      const items = [];
      while (i < lines.length && /^[-*]\s/.test(lines[i])) {
        const itemLines = [lines[i].slice(2)];
        i++;
        // Continuation lines (indented)
        while (i < lines.length && /^\s{2,}/.test(lines[i]) && lines[i].trim() !== '') {
          itemLines.push(lines[i].trimStart());
          i++;
        }
        items.push(parseBlocks(itemLines.join('\n')));
      }
      blocks.push(new MdList(false, items));
      continue;
    }

    // Ordered list: 1. 2. etc.
    if (/^\d+\.\s/.test(line)) {
      const items = [];
      while (i < lines.length && /^\d+\.\s/.test(lines[i])) {
        const dotIdx = lines[i].indexOf('. ');
        const itemLines = [lines[i].slice(dotIdx + 2)];
        i++;
        while (i < lines.length && /^\s{2,}/.test(lines[i]) && lines[i].trim() !== '') {
          itemLines.push(lines[i].trimStart());
          i++;
        }
        items.push(parseBlocks(itemLines.join('\n')));
      }
      blocks.push(new MdList(true, items));
      continue;
    }

    // GFM table: | ... | ... |
    if (line.includes('|') && i + 1 < lines.length && /^\|?\s*[-:]+/.test(lines[i + 1])) {
      const rows = [];
      // Header row
      rows.push(parseTableRow(line));
      i++; // skip separator
      i++;
      // Body rows
      while (i < lines.length && lines[i].includes('|') && lines[i].trim() !== '') {
        rows.push(parseTableRow(lines[i]));
        i++;
      }
      blocks.push(new MdTable(rows));
      continue;
    }

    // Paragraph — collect consecutive non-blank, non-special lines
    const paraLines = [];
    while (i < lines.length && lines[i].trim() !== '' &&
           !lines[i].match(/^#{1,6}\s/) &&
           !lines[i].match(/^(`{3,}|~{3,})/) &&
           !lines[i].startsWith('> ') &&
           !/^[-*]\s/.test(lines[i]) &&
           !/^\d+\.\s/.test(lines[i]) &&
           !/^(\*{3,}|-{3,}|_{3,})\s*$/.test(lines[i])) {
      paraLines.push(lines[i]);
      i++;
    }
    if (paraLines.length > 0) {
      blocks.push(new MdParagraph(parseInlines(paraLines.join('\n'))));
    }
  }
  return blocks;
}

function parseTableRow(line) {
  // Strip leading/trailing pipes and split
  let trimmed = line.trim();
  if (trimmed.startsWith('|')) trimmed = trimmed.slice(1);
  if (trimmed.endsWith('|')) trimmed = trimmed.slice(0, -1);
  return trimmed.split('|').map(cell => parseInlines(cell.trim()));
}

function parseMarkdown(text) {
  return new MdDocument(parseBlocks(text));
}

// -- Renderer --

function renderInline(node) {
  switch (node.tag) {
    case 'MdText': return node.text;
    case 'MdCode': return '`' + node.text + '`';
    case 'MdEmph': return '*' + node.children.map(renderInline).join('') + '*';
    case 'MdStrong': return '**' + node.children.map(renderInline).join('') + '**';
    case 'MdLink': return '[' + node.children.map(renderInline).join('') + '](' + node.url + ')';
    case 'MdImage': return '![' + node.alt + '](' + node.url + ')';
    default: return '';
  }
}

function renderBlock(node, indent = '') {
  switch (node.tag) {
    case 'MdParagraph':
      return indent + node.children.map(renderInline).join('') + '\n';
    case 'MdHeading':
      return indent + '#'.repeat(node.level) + ' ' + node.children.map(renderInline).join('') + '\n';
    case 'MdCodeBlock':
      return indent + '```' + node.lang + '\n' + node.code + '\n' + indent + '```\n';
    case 'MdBlockQuote':
      return node.children.map(c => renderBlock(c, indent + '> ')).join('');
    case 'MdList': {
      return node.items.map((item, idx) => {
        const prefix = node.ordered ? `${idx + 1}. ` : '- ';
        return item.map((b, bi) => (bi === 0 ? indent + prefix : indent + '  ') + renderBlock(b).trimStart()).join('');
      }).join('');
    }
    case 'MdThematicBreak':
      return indent + '---\n';
    case 'MdTable': {
      if (node.rows.length === 0) return '';
      const header = '| ' + node.rows[0].map(cells => cells.map(renderInline).join('')).join(' | ') + ' |\n';
      const sep = '| ' + node.rows[0].map(() => '---').join(' | ') + ' |\n';
      const body = node.rows.slice(1).map(row =>
        '| ' + row.map(cells => cells.map(renderInline).join('')).join(' | ') + ' |\n'
      ).join('');
      return indent + header + indent + sep + body;
    }
    case 'MdDocument':
      return node.children.map(c => renderBlock(c, indent)).join('\n');
    default:
      return '';
  }
}

function renderMarkdown(doc) {
  // Match Python's "\n".join(lines) — no trailing newline.
  const raw = renderBlock(doc);
  return raw.endsWith('\n') ? raw.slice(0, -1) : raw;
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

function writeInlineArray(inlines) {
  const count = inlines.length;
  if (count === 0) return [0, 0];
  const backingPtr = alloc(count * 4);
  for (let i = 0; i < count; i++) {
    const ptr = writeMdInline(inlines[i]);
    writeI32(backingPtr + i * 4, ptr);
  }
  return [backingPtr, count];
}

function writeMdInline(node) {
  switch (node.tag) {
    case 'MdText': {  // tag=0, String at +4/+8, total=16
      const ptr = alloc(12);
      const [sPtr, sLen] = allocString(node.text);
      writeI32(ptr, 0);
      writeI32(ptr + 4, sPtr);
      writeI32(ptr + 8, sLen);
      return ptr;
    }
    case 'MdCode': {  // tag=1, String at +4/+8, total=16
      const ptr = alloc(12);
      const [sPtr, sLen] = allocString(node.text);
      writeI32(ptr, 1);
      writeI32(ptr + 4, sPtr);
      writeI32(ptr + 8, sLen);
      return ptr;
    }
    case 'MdEmph': {  // tag=2, Array at +4/+8, total=16
      const ptr = alloc(12);
      const [aPtr, aLen] = writeInlineArray(node.children);
      writeI32(ptr, 2);
      writeI32(ptr + 4, aPtr);
      writeI32(ptr + 8, aLen);
      return ptr;
    }
    case 'MdStrong': {  // tag=3, Array at +4/+8, total=16
      const ptr = alloc(12);
      const [aPtr, aLen] = writeInlineArray(node.children);
      writeI32(ptr, 3);
      writeI32(ptr + 4, aPtr);
      writeI32(ptr + 8, aLen);
      return ptr;
    }
    case 'MdLink': {  // tag=4, Array at +4/+8, String at +12/+16, total=24
      const ptr = alloc(20);
      const [aPtr, aLen] = writeInlineArray(node.children);
      const [sPtr, sLen] = allocString(node.url);
      writeI32(ptr, 4);
      writeI32(ptr + 4, aPtr);
      writeI32(ptr + 8, aLen);
      writeI32(ptr + 12, sPtr);
      writeI32(ptr + 16, sLen);
      return ptr;
    }
    case 'MdImage': {  // tag=5, String at +4/+8, String at +12/+16, total=24
      const ptr = alloc(20);
      const [s1Ptr, s1Len] = allocString(node.alt);
      const [s2Ptr, s2Len] = allocString(node.url);
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
  for (let i = 0; i < count; i++) {
    const ptr = writeMdBlock(blocks[i]);
    writeI32(backingPtr + i * 4, ptr);
  }
  return [backingPtr, count];
}

function writeMdBlock(node) {
  switch (node.tag) {
    case 'MdParagraph': {  // tag=0, Array<MdInline> at +4/+8, total=16
      const ptr = alloc(12);
      const [aPtr, aLen] = writeInlineArray(node.children);
      writeI32(ptr, 0);
      writeI32(ptr + 4, aPtr);
      writeI32(ptr + 8, aLen);
      return ptr;
    }
    case 'MdHeading': {  // tag=1, Nat(i64) at +8, Array at +16/+20, total=24
      const ptr = alloc(24);
      writeI32(ptr, 1);
      writeI64(ptr + 8, node.level);
      const [aPtr, aLen] = writeInlineArray(node.children);
      writeI32(ptr + 16, aPtr);
      writeI32(ptr + 20, aLen);
      return ptr;
    }
    case 'MdCodeBlock': {  // tag=2, String at +4/+8, String at +12/+16, total=24
      const ptr = alloc(20);
      const [s1Ptr, s1Len] = allocString(node.lang);
      const [s2Ptr, s2Len] = allocString(node.code);
      writeI32(ptr, 2);
      writeI32(ptr + 4, s1Ptr);
      writeI32(ptr + 8, s1Len);
      writeI32(ptr + 12, s2Ptr);
      writeI32(ptr + 16, s2Len);
      return ptr;
    }
    case 'MdBlockQuote': {  // tag=3, Array<MdBlock> at +4/+8, total=16
      const ptr = alloc(12);
      const [aPtr, aLen] = writeBlockArray(node.children);
      writeI32(ptr, 3);
      writeI32(ptr + 4, aPtr);
      writeI32(ptr + 8, aLen);
      return ptr;
    }
    case 'MdList': {  // tag=4, Bool(i32) at +4, Array<Array<MdBlock>> at +8/+12, total=16
      const ptr = alloc(16);
      writeI32(ptr, 4);
      writeI32(ptr + 4, node.ordered ? 1 : 0);
      // Each item is Array<MdBlock> — we need Array<Array<MdBlock>>
      const count = node.items.length;
      let backingPtr = 0;
      if (count > 0) {
        // Each element is an i32_pair (ptr, len) = 8 bytes
        backingPtr = alloc(count * 8);
        for (let i = 0; i < count; i++) {
          const [itemPtr, itemLen] = writeBlockArray(node.items[i]);
          writeI32(backingPtr + i * 8, itemPtr);
          writeI32(backingPtr + i * 8 + 4, itemLen);
        }
      }
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
      const ptr = alloc(12);
      writeI32(ptr, 6);
      // rows: Array<Array<Array<MdInline>>>
      const rowCount = node.rows.length;
      let rowsPtr = 0;
      if (rowCount > 0) {
        // Each row is Array<Array<MdInline>> — i32_pair (ptr, len) = 8 bytes
        rowsPtr = alloc(rowCount * 8);
        for (let ri = 0; ri < rowCount; ri++) {
          const row = node.rows[ri];
          const cellCount = row.length;
          let cellsPtr = 0;
          if (cellCount > 0) {
            // Each cell is Array<MdInline> — i32_pair = 8 bytes
            cellsPtr = alloc(cellCount * 8);
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
      writeI32(ptr + 4, rowsPtr);
      writeI32(ptr + 8, rowCount);
      return ptr;
    }
    case 'MdDocument': {  // tag=7, Array<MdBlock> at +4/+8, total=16
      const ptr = alloc(12);
      const [aPtr, aLen] = writeBlockArray(node.children);
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
  try {
    const doc = parseMarkdown(text);
    const blockPtr = writeMdBlock(doc);
    return allocResultOkI32(blockPtr);
  } catch (e) {
    return allocResultErrString(e.message || String(e));
  }
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
    // Wrap in Result.Ok — layout: tag=0, backing_ptr, count (12 bytes)
    const ptr = alloc(12);
    writeI32(ptr, 0);              // tag = Ok
    writeI32(ptr + 4, backingPtr);
    writeI32(ptr + 8, count);
    return ptr;
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

function buildImportObject(module) {
  const imports = { vera: {} };
  const needed = new Set();

  for (const imp of WebAssembly.Module.imports(module)) {
    if (imp.module === 'vera') needed.add(imp.name);
  }

  // IO bindings
  for (const [name, fn] of Object.entries(IO_BINDINGS)) {
    if (needed.has(name)) imports.vera[name] = fn;
  }

  // Contract fail
  if (needed.has('contract_fail')) {
    imports.vera.contract_fail = hostContractFail;
  }

  // State<T> bindings — dynamically created from import names.
  // stateCells[key] is a stack; top is the active cell for the current handler.
  for (const name of needed) {
    const getMatch = name.match(/^state_get_(.+)$/);
    if (getMatch) {
      const key = getMatch[1];
      if (!(key in stateCells)) {
        stateCells[key] = [key.includes('Float') ? 0.0 : BigInt(0)];
      }
      imports.vera[name] = () => stateCells[key][stateCells[key].length - 1];
    }
    const putMatch = name.match(/^state_put_(.+)$/);
    if (putMatch) {
      const key = putMatch[1];
      if (!(key in stateCells)) {
        stateCells[key] = [key.includes('Float') ? 0.0 : BigInt(0)];
      }
      imports.vera[name] = (val) => { stateCells[key][stateCells[key].length - 1] = val; };
    }
    const pushMatch = name.match(/^state_push_(.+)$/);
    if (pushMatch) {
      const key = pushMatch[1];
      const def = key.includes('Float') ? 0.0 : BigInt(0);
      if (!(key in stateCells)) {
        stateCells[key] = [def];
      }
      imports.vera[name] = () => { stateCells[key].push(def); };
    }
    const popMatch = name.match(/^state_pop_(.+)$/);
    if (popMatch) {
      const key = popMatch[1];
      if (!(key in stateCells)) {
        stateCells[key] = [key.includes('Float') ? 0.0 : BigInt(0)];
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
    const capacity = Math.max(_BUCKET_INITIAL_CAPACITY, count * 2);
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
        if (decodeField(kt, base + 4) === key) continue;
        const fields = new Uint8Array(16);
        fields.set(new Uint8Array(mem().buffer, base + 4, 16));
        survivors.push(fields);
      }
    }
    const newWrapper = allocBktWrapper(kind, 0);
    gcShadowPush(newWrapper);
    try {
      const newBucket = allocBucket(
        Math.max(_BUCKET_INITIAL_CAPACITY, survivors.length * 2),
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
  // path (_emit_wrap_handle) still emits a call to it.
  imports.vera.attach_bucket_to_wrapper = () => {};

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
  // in vera/codegen/api.py.  Allocates an 8-byte wrapper ADT,
  // writes tag + handle, calls the exported $register_wrapper.
  // Used by host helpers that have already obtained a raw handle
  // and need to lift it to a wrapper pointer before stuffing into
  // an Option<T> Some payload (e.g. decimal_from_string).
  // Wrapper body layout (must match _WRAPPER_BODY_SIZE in
  // vera/codegen/api.py and vera/wasm/calls_containers.py):
  //   +0  tag (i32)            [#573]
  //   +4  handle | 0x80000000  [#578 — bit-31 tag keeps it out
  //                             of the conservative GC scan]
  //   +8  bucket_ptr (i32)     [#695/#705 — attached below]
  function wrapHandle(kind, rawHandle) {
    const tag = _KIND_TO_TAG_JS[kind];
    const ptr = alloc(12);
    writeI32(ptr, tag);
    // #578: tag the handle with bit-31 so the conservative scan
    // never mistakes it for a heap pointer.  Matches the
    // WAT-emitted ``_emit_wrap_handle`` discipline.
    writeI32(ptr + 4, (rawHandle | 0x80000000) | 0);
    // #695/#705: default bucket_ptr is 0.  Map/Set callers fill it
    // via attach_bucket_to_wrapper below; Decimal leaves it 0.
    writeI32(ptr + 8, 0);
    // PR #707 review (silent-failure-hunter C2): symmetric with the
    // CLI-side ``_call_register_wrapper`` discipline.  A caller
    // reaching wrapHandle is building a Map / Set / Decimal wrapper
    // — so the wrap-table is required for Phase 2c reclamation.  If
    // ``register_wrapper`` isn't exported, the wrapper is allocated
    // and the mapStore entry created but the wrap-table registration
    // is skipped → ``host_decref_handle`` never fires → permanent
    // mapStore leak per write.  That's a build-config bug; raise
    // rather than silently leak.
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

  // PR #707 review: JS-side shadow-stack push/pop using
  // the exported ``$gc_sp`` / ``$gc_stack_limit`` mutable globals
  // (added in v0.0.158 / #692 for host-side rooting).  Needed
  // because the JS multi-alloc patterns (``allocMapWrapper`` and
  // any future caller) have the same root-discipline problem as
  // the CLI ``_ShadowGuard``: a freshly-allocated wrapper held
  // only in a JS local is invisible to the conservative GC scan,
  // so a sub-alloc that fires ``$gc_collect`` can reclaim it.
  // The wrap-table region (below ``gc_heap_start``) is NOT walked
  // by the mark phase, so ``register_wrapper`` alone isn't enough
  // — explicit shadow-stack rooting is required.
  //
  // ``gcShadowPush`` reads $gc_sp, writes the value, advances $gc_sp.
  // ``gcShadowPop`` decrements $gc_sp.  Stack-discipline must be
  // strict — callers MUST pair push with pop on every exit path
  // (use the try/finally pattern below).
  // PR #707 review (silent-failure-hunter C1): symmetric with the
  // CLI-side ``_ShadowGuard`` discipline — raise rather than silently
  // degrade.  A caller reaching this point (allocMapWrapper et al.)
  // requires the wrapper to be rooted across the bucket-attach
  // window; if ``$gc_sp`` / ``$gc_stack_limit`` are missing the
  // module was compiled without GC support but is still trying to
  // build Map / Set values — that's a build-config bug and should
  // surface immediately, not as a downstream UAF.
  function gcShadowPush(value) {
    if (!wasm || !wasm.gc_sp || !wasm.gc_stack_limit) {
      throw new Error(
        '#707 browser runtime: $gc_sp / $gc_stack_limit not exported; ' +
        'module was built without GC support — Map / Set wrappers ' +
        'cannot be rooted across the attach window.  Recompile with ' +
        'GC enabled (any of map_ops_used / set_ops_used / ' +
        'decimal_ops_used / wrap-table-needing types).'
      );
    }
    const sp = wasm.gc_sp.value;
    if (sp >= wasm.gc_stack_limit.value) {
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
  // ``writeJson`` / ``writeHtml`` are multi-alloc walkers — they
  // build a tree of heap blocks via repeated ``alloc()`` and JS-
  // local pointer holding.  Without explicit shadow-stack rooting,
  // intermediates (e.g. JArray's ``arrPtr`` between its allocation
  // and the writes into it) are reclaimed by EAGER_GC and the
  // resulting tree has dangling pointers — observed empirically as
  // ``json_array_length`` returning 0 instead of the JArray length.
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

  // allocMapWrapper(d) : drop-in replacement for mapAlloc(d) used by
  // writeJson / writeHtml.  Inserts d into mapStore, lifts the
  // resulting handle to a wrapper pointer via wrapHandle, and
  // populates the wrapper's bucket array for GC reachability
  // (#695 mirror parallel — matches CLI ``_alloc_map_wrapper``).
  //
  // PR #707 review: the wrapper returned from
  // ``wrapHandle`` is registered with the wrap-table but the
  // wrap-table region is NOT scanned by Phase 2a marking, so the
  // wrapper is only kept alive transitively (via another reachable
  // block pointing at it).  Between ``wrapHandle`` returning and
  // the caller (e.g. ``writeJson``'s JObject branch) storing the
  // wrapper into a body field, the wrapper is unrooted — and the
  // ``attach_bucket_to_wrapper`` call below internally allocates
  // the bucket, which can fire ``$gc_collect``.  Shadow-push the
  // wrapper across the attach so it stays alive.  Caller is still
  // responsible for storing the returned ptr promptly (the
  // wrapper becomes unrooted again on return — see writeJson
  // JObject branch which is the only consumer of this helper).
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
      const p = alloc(12); // tag(4) + ptr(4) + len(4)
      writeI32(p, 1);
      writeI32(p + 4, sp);
      writeI32(p + 8, sl);
      return p;
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
    for (let i = 0; i < count; i++) {
      const [sp, sl] = allocString(strings[i]);
      writeI32(ptr + i * 8, sp);
      writeI32(ptr + i * 8 + 4, sl);
    }
    return [ptr, count];
  }

  // #706: every Map host import takes the wrapper pointer and goes
  // through the bucket codec above.
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
        return decodeColumn(wp, kt, 4).some((x) => x === k) ? 1 : 0;
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
      const has = (wp, e) => decodeColumn(wp, et, 4).some((x) => x === e) ? 1 : 0;
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
  // JS lacks native Decimal — use string-based arithmetic via a
  // minimal implementation that wraps string representations.
  const decimalStore = new Map();
  let decimalNextHandle = 1;
  function decimalAlloc(s) {
    const h = decimalNextHandle++;
    decimalStore.set(h, s);
    return h;
  }

  // String-based decimal arithmetic helpers.
  // MVP limitation: these use JS Number() which loses precision for values
  // beyond Number.MAX_SAFE_INTEGER or with many decimal digits.  A future
  // version should use a proper arbitrary-precision decimal library.
  function decStrAdd(a, b) { return String(Number(a) + Number(b)); }
  function decStrSub(a, b) { return String(Number(a) - Number(b)); }
  function decStrMul(a, b) { return String(Number(a) * Number(b)); }
  function decStrDiv(a, b) { return String(Number(a) / Number(b)); }

  if (needed.has("decimal_from_int")) {
    imports.vera.decimal_from_int = (v) => decimalAlloc(String(v));
  }
  if (needed.has("decimal_from_float")) {
    imports.vera.decimal_from_float = (v) => decimalAlloc(String(v));
  }
  if (needed.has("decimal_from_string")) {
    imports.vera.decimal_from_string = (ptr, len) => {
      const s = readString(ptr, len);
      if (/^-?(\d+\.?\d*|\.\d+)([eE][+-]?\d+)?$/.test(s.trim())) {
        const h = decimalAlloc(s.trim());
        // #573 phase 3: wrap before stuffing into Some.
        return allocOptionSomeI32(wrapHandle(3, h));
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
      decimalAlloc(decStrAdd(decimalStore.get(a), decimalStore.get(b)));
  }
  if (needed.has("decimal_sub")) {
    imports.vera.decimal_sub = (a, b) =>
      decimalAlloc(decStrSub(decimalStore.get(a), decimalStore.get(b)));
  }
  if (needed.has("decimal_mul")) {
    imports.vera.decimal_mul = (a, b) =>
      decimalAlloc(decStrMul(decimalStore.get(a), decimalStore.get(b)));
  }
  if (needed.has("decimal_div")) {
    imports.vera.decimal_div = (a, b) => {
      // #573 phase 3: a, b are raw handles (the WASM-side
      // translator unwraps wrapper pointers).  Result is wrapped
      // here before stuffing into Some, matching the Python side.
      const bVal = Number(decimalStore.get(b));
      if (bVal === 0) return allocOptionNone();
      const h = decimalAlloc(decStrDiv(decimalStore.get(a), decimalStore.get(b)));
      return allocOptionSomeI32(wrapHandle(3, h));
    };
  }
  if (needed.has("decimal_neg")) {
    imports.vera.decimal_neg = (h) => {
      const s = decimalStore.get(h);
      if (s.startsWith("-")) return decimalAlloc(s.slice(1));
      // Canonical zero: neg("0") → "0", not "-0"
      if (s === "0" || s === "0.0") return decimalAlloc(s);
      return decimalAlloc("-" + s);
    };
  }
  if (needed.has("decimal_compare")) {
    imports.vera.decimal_compare = (a, b) => {
      const na = Number(decimalStore.get(a));
      const nb = Number(decimalStore.get(b));
      const tag = na < nb ? 0 : na === nb ? 1 : 2;
      return allocOrdering(tag);
    };
  }
  if (needed.has("decimal_eq")) {
    // Compare string representations rather than converting to Number,
    // which would lose precision for large or high-precision values.
    imports.vera.decimal_eq = (a, b) =>
      decimalStore.get(a) === decimalStore.get(b) ? 1 : 0;
  }
  if (needed.has("decimal_round")) {
    imports.vera.decimal_round = (h, places) => {
      const n = Number(decimalStore.get(h));
      const p = Number(places);
      const factor = 10 ** p;
      return decimalAlloc(String(Math.round(n * factor) / factor));
    };
  }
  if (needed.has("decimal_abs")) {
    imports.vera.decimal_abs = (h) => {
      const s = decimalStore.get(h);
      return decimalAlloc(s.startsWith("-") ? s.slice(1) : s);
    };
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
      // #708: each recursive ``writeJson(v)`` call returns a heap
      // ptr stored in the JS-side Map ``m`` only.  Between
      // returning ep and ``m.set(k, ep)``, the result is in a JS
      // local — invisible to the conservative scan.  Push each ep
      // before storing in m, then push wrapperPtr before the
      // final 8-byte alloc.
      const m = new Map();
      for (const [k, v] of Object.entries(value)) {
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

  // Read a Json ADT from WASM memory back to a JS value.
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
      // values are i32 Json heap pointers.
      const wrapperPtr = readI32(ptr + 4);
      const result = {};
      for (const [k, v] of decodeMap(wrapperPtr, 's', 'b')) {
        result[String(k)] = readJson(Number(v));
      }
      return result;
    }
    console.warn(`readJson: unknown tag ${tag} at pointer ${ptr}; possible memory corruption`);
    return null;
  }

  if (needed.has("json_parse")) {
    imports.vera.json_parse = (ptr, len) => {
      const text = readString(ptr, len);
      try {
        const parsed = JSON.parse(text);
        // #708 (PR #707): wrap in gcGuard and push jsonPtr
        // before allocResultOkI32's alloc can fire GC.  writeJson
        // has its own internal guard that pops on return — by the
        // time control returns here, jsonPtr is unrooted again.
        return gcGuard(() => {
          const jsonPtr = writeJson(parsed);
          gcShadowPush(jsonPtr);
          return allocResultOkI32(jsonPtr);
        });
      } catch (e) {
        return allocResultErrString(String(e.message || e));
      }
    };
  }

  if (needed.has("json_stringify")) {
    imports.vera.json_stringify = (ptr) => {
      const value = readJson(ptr);
      const text = JSON.stringify(value);
      // JSON.stringify can return undefined for unsupported values
      // (e.g. bare undefined, symbols, functions).  Fall back to "null"
      // to match the JSON spec and avoid allocString crashing.
      return allocString(text !== undefined ? text : "null");
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
      try {
        let root;
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
        // #708 (PR #707): same gcGuard discipline as
        // json_parse — root nodePtr before allocResultOkI32 fires
        // GC.
        return gcGuard(() => {
          const nodePtr = writeHtml(root);
          gcShadowPush(nodePtr);
          return allocResultOkI32(nodePtr);
        });
      } catch (e) {
        return allocResultErrString(String(e.message || 'HTML parse error'));
      }
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
        for (let i = 0; i < count; i++) {
          writeI32(arrPtr + i * 4, writeHtml(matches[i]));
        }
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
  if (wasmSource instanceof ArrayBuffer || ArrayBuffer.isView(wasmSource)) {
    // Node.js path: raw bytes
    module = await WebAssembly.compile(wasmSource);
  } else {
    // Browser path: URL or Response
    const url = wasmSource ?? new URL('./module.wasm', import.meta.url);
    const response = url instanceof Response ? url : await fetch(url);
    const bytes = await response.arrayBuffer();
    module = await WebAssembly.compile(bytes);
  }

  const importObject = buildImportObject(module);
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
    stateCells[key] = [key.includes('Float') ? 0.0 : BigInt(0)];
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
