// A tiny stack VM for make.fun's tiny stack ISA (v1), for
// tiny-stack-vm-01: one run answers the whole set, running each
// /input/<id>/program.bin on its /input/<id>/input.bin and writing
// its output bytes and end code to /output/<id>/. Machine: wrapping
// 32-bit values, stack 256, call stack 64, 256 memory words, at most
// 1,000,000 steps and 65,536 output bytes a program; traps (codes
// 2..11) become the exit code, keeping output written before them.

import { mkdirSync, readFileSync, readdirSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const STACK_CAP = 256, CALL_CAP = 64, MEM_WORDS = 256, STEP_CAP = 1_000_000, OUT_CAP = 65_536;

// Runs one program to its end: [output bytes, exit code]. Every
// finish (halt, EXIT, a trap) unwinds through `end`, throwing it.
function execute(prog, inp) {
  const size = prog.length;
  const stack = new Int32Array(STACK_CAP);
  const calls = new Int32Array(CALL_CAP);
  const mem = new Int32Array(MEM_WORDS);
  const out = new Uint8Array(OUT_CAP);
  let sp = 0, csp = 0, olen = 0, inPos = 0, pc = 0, steps = 0;

  const end = (code) => { throw code; };
  // The stack traps, checked before an instruction's own: underflow 2, overflow 3.
  const need = (k) => { if (sp < k) end(2); };
  const push = (v) => { if (sp >= STACK_CAP) end(3); stack[sp++] = v; };
  // The signed 16-bit immediate behind the opcode at p.
  const imm16s = (p) => ((prog[p + 1] | (prog[p + 2] << 8)) << 16) >> 16;

  try {
    for (;;) {
      // Each step's gauntlet, in ISA order: limit, pc, opcode, immediate.
      if (steps >= STEP_CAP) end(10);
      if (pc < 0 || pc >= size) end(9);
      const op = prog[pc];
      const immLen = op === 0x01 ? 1 : op === 0x02 ? 4 : op >= 0x30 && op <= 0x33 ? 2 : 0;
      if (pc + immLen >= size) end(9);
      steps++;
      const at = pc; // the opcode's address; its immediate sits behind it
      const next = pc + 1 + immLen;
      pc = next;

      switch (op) {
        case 0x00: end(0); break; // HALT
        case 0x01: push((prog[next - 1] << 24) >> 24); break; // PUSH8, sign-extended
        case 0x02: // PUSH32, little-endian
          push(prog[next - 4] | (prog[next - 3] << 8) | (prog[next - 2] << 16) | (prog[next - 1] << 24));
          break;
        case 0x03: need(1); sp--; break; // POP
        case 0x04: need(1); push(stack[sp - 1]); break; // DUP
        case 0x05: { // SWAP
          need(2);
          const t = stack[sp - 1];
          stack[sp - 1] = stack[sp - 2];
          stack[sp - 2] = t;
          break;
        }
        case 0x06: need(2); push(stack[sp - 2]); break; // OVER
        case 0x07: { // ROT: ( a b c -- b c a )
          need(3);
          const a = stack[sp - 3];
          stack[sp - 3] = stack[sp - 2];
          stack[sp - 2] = stack[sp - 1];
          stack[sp - 1] = a;
          break;
        }
        case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15:
        case 0x16: case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d:
        case 0x1e: case 0x20: case 0x21: case 0x22: { // the two-value operators
          need(2);
          const b = stack[sp - 1];
          const a = stack[sp - 2];
          let r;
          switch (op) {
            case 0x10: r = (a + b) | 0; break;
            case 0x11: r = (a - b) | 0; break;
            case 0x12: r = Math.imul(a, b); break; // the exact low 32 bits
            case 0x13: if (b === 0) end(4); r = a === -2147483648 && b === -1 ? a : (a / b) | 0; break;
            case 0x14: if (b === 0) end(4); r = b === -1 ? 0 : (a % b) | 0; break;
            case 0x15: if (b === 0) end(4); r = Math.floor((a >>> 0) / (b >>> 0)) | 0; break;
            case 0x16: if (b === 0) end(4); r = ((a >>> 0) % (b >>> 0)) | 0; break;
            case 0x18: r = a & b; break;
            case 0x19: r = a | b; break;
            case 0x1a: r = a ^ b; break;
            case 0x1c: r = a << (b & 31); break; // the count is its low five bits
            case 0x1d: r = a >> (b & 31); break; // arithmetic: the sign fills in
            case 0x1e: r = (a >>> (b & 31)) | 0; break; // logical: zeros fill in
            case 0x20: r = a === b ? 1 : 0; break;
            case 0x21: r = a < b ? 1 : 0; break;
            default: r = (a >>> 0) < (b >>> 0) ? 1 : 0; // LTU: unsigned compare
          }
          sp--;
          stack[sp - 1] = r;
          break;
        }
        case 0x17: need(1); stack[sp - 1] = (-stack[sp - 1]) | 0; break; // NEG
        case 0x1b: need(1); stack[sp - 1] = ~stack[sp - 1]; break; // NOT
        case 0x30: pc = next + imm16s(at); break; // JMP, from the next instruction
        case 0x31: need(1); if (stack[--sp] === 0) pc = next + imm16s(at); break; // JZ
        case 0x32: need(1); if (stack[--sp] !== 0) pc = next + imm16s(at); break; // JNZ
        case 0x33: // CALL: the immediate is an unsigned absolute address
          if (csp >= CALL_CAP) end(7);
          calls[csp++] = next;
          pc = prog[at + 1] | (prog[at + 2] << 8);
          break;
        case 0x34: if (csp === 0) end(8); pc = calls[--csp]; break; // RET
        case 0x40: { // LOAD
          need(1);
          const addr = stack[sp - 1];
          if (addr < 0 || addr >= MEM_WORDS) end(6);
          stack[sp - 1] = mem[addr];
          break;
        }
        case 0x41: { // STORE: ( v addr -- )
          need(2);
          const addr = stack[sp - 1];
          if (addr < 0 || addr >= MEM_WORDS) end(6);
          mem[addr] = stack[sp - 2];
          sp -= 2;
          break;
        }
        case 0x50: { // PRINT: the value in decimal ASCII, no newline
          need(1);
          const text = String(stack[sp - 1]);
          if (olen + text.length > OUT_CAP) end(11); // it writes none of it
          sp--;
          for (let i = 0; i < text.length; i++) out[olen++] = text.charCodeAt(i);
          break;
        }
        case 0x51: // PUTC: one byte, the value's low eight bits
          need(1);
          if (olen >= OUT_CAP) end(11);
          out[olen++] = stack[--sp] & 255;
          break;
        case 0x52: push(inPos < inp.length ? inp[inPos++] : -1); break; // IN; -1 once spent
        case 0x53: need(1); end(stack[--sp] & 255); break; // EXIT: the low byte is the code
        default: end(5); // a byte no opcode names
      }
    }
  } catch (e) {
    if (typeof e !== 'number') throw e;
    return [out.slice(0, olen), e];
  }
}

const INPUT_DIR = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUTPUT_DIR = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(INPUT_DIR).sort()) {
  const prog = readFileSync(join(INPUT_DIR, id, 'program.bin'));
  let inp = Buffer.alloc(0);
  try {
    inp = readFileSync(join(INPUT_DIR, id, 'input.bin'));
  } catch { /* no input file: empty input */ }
  const [bytes, code] = execute(prog, inp);
  mkdirSync(join(OUTPUT_DIR, id), { recursive: true });
  writeFileSync(join(OUTPUT_DIR, id, 'stdout.bin'), bytes);
  writeFileSync(join(OUTPUT_DIR, id, 'exit.txt'), code + '\n');
}
