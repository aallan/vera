// Browser leg of the `md_parse` parity gate (#1301).
//
// Reads a JSON array of Markdown strings from the file named by argv[2],
// runs each through the browser runtime's own `parseMarkdown`, and writes
// one canonical encoding per line to stdout.  The encoding mirrors
// `encode_block` in tests/md_parse_corpus.py exactly, positional tag for
// positional tag, so the two sides can be compared as bytes: a
// comparison through `md_render` cannot see how a paragraph's plain-text
// runs are grouped, which is the largest divergence class the issue
// measured.
//
// One process for the whole corpus — a process per input would make the
// gate minutes long and it would stop being run.

import { readFileSync } from 'node:fs';
import { parseMarkdown } from '../vera/browser/runtime.mjs';

function encodeInline(node) {
  switch (node.tag) {
    case 'MdText': return ['text', node.text];
    case 'MdCode': return ['code', node.text];
    case 'MdEmph': return ['emph', node.children.map(encodeInline)];
    case 'MdStrong': return ['strong', node.children.map(encodeInline)];
    case 'MdLink': return ['link', node.children.map(encodeInline), node.url];
    case 'MdImage': return ['image', node.alt, node.url];
    default: throw new Error(`unknown MdInline node: ${node.tag}`);
  }
}

function encodeBlock(node) {
  switch (node.tag) {
    case 'MdParagraph': return ['para', node.children.map(encodeInline)];
    case 'MdHeading':
      return ['heading', node.level, node.children.map(encodeInline)];
    case 'MdCodeBlock': return ['code_block', node.lang, node.code];
    case 'MdBlockQuote': return ['quote', node.children.map(encodeBlock)];
    case 'MdList':
      return [
        'list',
        node.ordered,
        node.items.map(item => item.map(encodeBlock)),
      ];
    case 'MdThematicBreak': return ['break'];
    case 'MdTable':
      return [
        'table',
        node.rows.map(row => row.map(cell => cell.map(encodeInline))),
      ];
    case 'MdDocument': return ['doc', node.children.map(encodeBlock)];
    default: throw new Error(`unknown MdBlock node: ${node.tag}`);
  }
}

/** `JSON.stringify` with Python's `ensure_ascii=True` escaping. */
function encodeJson(value) {
  // Python escapes everything outside printable ASCII (0x20..0x7e);
  // JSON.stringify escapes only the control range, so the tail is
  // added here.  Both spell the escape the same way: lowercase, four
  // hex digits.
  return JSON.stringify(value).replace(
    /[\u007f-\uffff]/g,
    ch => '\\u' + ch.charCodeAt(0).toString(16).padStart(4, '0'),
  );
}

const inputs = JSON.parse(readFileSync(process.argv[2], 'utf8'));
const lines = [];
for (const text of inputs) {
  try {
    lines.push(encodeJson(encodeBlock(parseMarkdown(text))));
  } catch (err) {
    lines.push(encodeJson(['ERR', String(err && err.message ? err.message : err)]));
  }
}
process.stdout.write(lines.join('\n') + '\n');
