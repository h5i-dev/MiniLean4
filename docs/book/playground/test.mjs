// Runs every examples/*.leanmini through the wasm kernel. Usage:
//   node docs/book/playground/test.mjs
import { readFileSync, readdirSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

const here = dirname(fileURLToPath(import.meta.url));
const root = resolve(here, '..', '..', '..');
const wasmPath = join(here, '..', 'assets', 'minilean.wasm');
const { instance } = await WebAssembly.instantiate(readFileSync(wasmPath), {});
const ex = instance.exports;

function runScript(script) {
  const enc = new TextEncoder().encode(script);
  const ptr = ex.alloc(enc.length);
  new Uint8Array(ex.memory.buffer, ptr, enc.length).set(enc);
  ex.run_script(ptr, enc.length);
  ex.dealloc(ptr, enc.length);
  const len = ex.result_len();
  return new TextDecoder().decode(new Uint8Array(ex.memory.buffer, ex.result_ptr(), len));
}

const dir = join(root, 'examples');
let failed = false;
for (const f of readdirSync(dir).filter((f) => f.endsWith('.leanmini')).sort()) {
  const out = runScript(readFileSync(join(dir, f), 'utf8'));
  console.log(`===== ${f}\n${out}`);
  if (/(^|\n)error/.test(out) || !out.includes('QED')) failed = true;
}
process.exit(failed ? 1 : 0);
