#!/usr/bin/env node
// harness.mjs — Node.js test harness for running compiled Vera WASM
// with the JavaScript runtime.  Used by tests/test_browser.py for
// parity testing against Python/wasmtime.
//
// Usage:
//   node vera/browser/harness.mjs module.wasm
//   node vera/browser/harness.mjs module.wasm --fn myFunc
//   node vera/browser/harness.mjs module.wasm --fn myFunc -- 42 3
//   node vera/browser/harness.mjs module.wasm --stdin "line1\nline2"
//   node vera/browser/harness.mjs module.wasm --args "a,b,c"
//   node vera/browser/harness.mjs module.wasm --env "KEY=val,FOO=bar"
//
// Output: JSON on stdout:
//   { "stdout": "...", "stderr": "...", "state": { "Int": 0 },
//     "exitCode": null, "error": null, "value": null, "exports": [...] }

import { readFileSync } from 'fs';
import { initFromBytes, call, getStdout, getStderr, getState, getExitCode, getExports } from './runtime.mjs';

function parseArgs() {
  const argv = process.argv.slice(2);
  const result = { wasmPath: null, fn: null, fnArgs: [], stdin: null, args: null, env: null };

  let i = 0;
  if (i < argv.length && !argv[i].startsWith('--')) {
    result.wasmPath = argv[i];
    i++;
  }

  while (i < argv.length) {
    if (argv[i] === '--fn' && i + 1 < argv.length) {
      result.fn = argv[i + 1];
      i += 2;
    } else if (argv[i] === '--stdin' && i + 1 < argv.length) {
      result.stdin = argv[i + 1].split('\\n');
      i += 2;
    } else if (argv[i] === '--args' && i + 1 < argv.length) {
      result.args = argv[i + 1].split(',');
      i += 2;
    } else if (argv[i] === '--env' && i + 1 < argv.length) {
      result.env = {};
      for (const pair of argv[i + 1].split(',')) {
        const eq = pair.indexOf('=');
        if (eq > 0) result.env[pair.slice(0, eq)] = pair.slice(eq + 1);
      }
      i += 2;
    } else if (argv[i] === '--') {
      // Function arguments after --
      result.fnArgs = argv.slice(i + 1).map(a => {
        if (a.includes('.')) return parseFloat(a);
        return BigInt(a);
      });
      break;
    } else {
      i++;
    }
  }
  return result;
}

async function main() {
  const config = parseArgs();
  if (!config.wasmPath) {
    process.stderr.write('Usage: node harness.mjs <module.wasm> [options]\n');
    process.exit(1);
  }

  const bytes = readFileSync(config.wasmPath);
  const options = {};
  if (config.stdin) options.stdin = config.stdin;
  if (config.args) options.args = config.args;
  if (config.env) options.env = config.env;

  await initFromBytes(bytes, options);

  const fnName = config.fn || 'main';
  let error = null;
  let value = undefined;

  try {
    value = call(fnName, ...config.fnArgs);
  } catch (e) {
    error = e.message || String(e);
  }

  // Serialize BigInt values for JSON
  const serializedValue = typeof value === 'bigint' ? Number(value) : value ?? null;

  const output = {
    stdout: getStdout(),
    stderr: getStderr(),
    state: getState(),
    exitCode: getExitCode(),
    error,
    value: serializedValue,
    exports: getExports(),
  };

  process.stdout.write(JSON.stringify(output));
}

main().catch(e => {
  process.stderr.write(`Harness error: ${e.message}\n`);
  process.exit(2);
});
