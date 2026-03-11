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
let lastViolation = ''; // Last contract violation message
const stateCells = {}; // State<T> cells: { TypeName: value }
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
// Import object builder (dynamic introspection)
// ---------------------------------------------------------------------------

const IO_BINDINGS = {
  print: hostPrint,
  read_line: hostReadLine,
  read_file: hostReadFile,
  write_file: hostWriteFile,
  args: hostArgs,
  exit: hostExit,
  get_env: hostGetEnv,
};

const MD_BINDINGS = {
  md_parse: hostMdParse,
  md_render: hostMdRender,
  md_has_heading: hostMdHasHeading,
  md_has_code_block: hostMdHasCodeBlock,
  md_extract_code_blocks: hostMdExtractCodeBlocks,
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

  // State<T> bindings — dynamically created from import names
  for (const name of needed) {
    const getMatch = name.match(/^state_get_(.+)$/);
    if (getMatch) {
      const key = getMatch[1];
      if (!(key in stateCells)) {
        stateCells[key] = key.includes('Float') ? 0.0 : BigInt(0);
      }
      imports.vera[name] = () => stateCells[key];
    }
    const putMatch = name.match(/^state_put_(.+)$/);
    if (putMatch) {
      const key = putMatch[1];
      if (!(key in stateCells)) {
        stateCells[key] = key.includes('Float') ? 0.0 : BigInt(0);
      }
      imports.vera[name] = (val) => { stateCells[key] = val; };
    }
  }

  // Markdown bindings
  for (const [name, fn] of Object.entries(MD_BINDINGS)) {
    if (needed.has(name)) imports.vera[name] = fn;
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

/** Return current State<T> cell values. */
export function getState() {
  const result = {};
  for (const [k, v] of Object.entries(stateCells)) {
    result[k] = typeof v === 'bigint' ? Number(v) : v;
  }
  return result;
}

/** Reset all State<T> cells to defaults. */
export function resetState() {
  for (const key of Object.keys(stateCells)) {
    stateCells[key] = key.includes('Float') ? 0.0 : BigInt(0);
  }
}

/** Return the exit code from IO.exit, or null if not called. */
export function getExitCode() {
  return exitCode;
}

/** Reset all runtime state for a fresh execution. */
export function reset() {
  stdoutBuf = '';
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
