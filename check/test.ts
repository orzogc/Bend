#!/usr/bin/env bun

declare const process: {
  env: Record<string, string | undefined>;
  execPath: string;
  exit(code?: number): never;
  kill(pid: number, signal?: string | number): void;
  on(event: string, listener: () => void): void;
  pid: number;
  stderr: { write(data: string): boolean };
  stdout: { write(data: string): boolean };
};

declare const Buffer: {
  from(data: string | Uint8Array): { toString(): string };
};

declare const require: (id: string) => {
  writeSync: (fd: number, b: Uint8Array, at?: number,
    len?: number) => number;
};

import * as perf from "./perf.ts";
import * as repo from "./repo.ts";
import * as core from "../bend2/bend.ts";
import * as tocl from "../bend2/comp.ts";

declare const setTimeout: (fn: () => void, ms: number) =>
  { unref(): void };

// Types
// =====

export type Kid = {
  on(event: "message", listener: (value: never) => void): void;
  on(event: "error", listener: (e: Error) => void): void;
  on(event: "exit", listener: (code: number) => void): void;
  postMessage(value: unknown): void;
  removeAllListeners(event: string): void;
  terminate(): Promise<number>;
};

export type Deal = { kind: string; tmp: string; deadline: number };

export type Exec = {
  out: string;
  err: string;
  code: number;
  sig: string | null;
  halt: "exit" | "signal" | "timeout" | "spawn";
};

export type Block = { cmd: string; exp: string };

export type Test = {
  name: string;
  file: string;
  blocks: Block[];
  fails: string[];
  yellow?: string;
  rss?: number;
  csrc?: string[];
  cnot?: string[];
};

export type Checked = { book?: core.Book; err?: string };

export type Built = { bin?: string; js?: string; err?: string };

export type Defer = {
  kind: "c" | "js";
  name: string;
  prog: string;
  prefix: string;
  body: string;
  key: string;
  blocks: Block[];
};

export type FileRet = { test: Test; defers: Defer[] };

export type Fail = { name: string; cmd: string; exp: string; got: string };

export type ShardRet = { fails: Fail[]; notes?: string[] };

export type Job = { kind: "file"; name: string; file: string; src: string }
  | { kind: "shard"; sub: "c" | "js"; tag: number; members: Defer[] }
  | { kind: "stack" }
  | { kind: "cli" }
  | { kind: "lint" }
  | { kind: "emit" }
  | { kind: "pins" }
  | { kind: "pure" }
  | { kind: "load" }
  | { kind: "guard" }
  | { kind: "knob" };

export type Ret = { file?: FileRet; fails?: Fail[]; notes?: string[] };

export type Pool = {
  push: (j: Job, front?: boolean) => void;
  close: () => void;
  done: Promise<void>;
};

// Constants
// =========

const child = import.meta.require("child_process") as {
  execFile(cmd: string, args: string[], opts: {
    cwd?: string;
    env?: Record<string, string | undefined>;
    encoding?: "utf8";
    timeout?: number;
    maxBuffer?: number;
  }, done: (e: (Error & { code?: number | string }) | null,
    out: string, err: string) => void): void;
  execFileSync(cmd: string, args?: string[], opts?: {
    cwd?: string;
    encoding?: "utf8";
    input?: string;
    maxBuffer?: number;
  }): string;
  spawnSync(cmd: string, args: string[], opts?: {
    cwd?: string;
    encoding?: "utf8";
    maxBuffer?: number;
  }): { status: number | null; stdout: string; stderr: string };
};

const fs = import.meta.require("fs") as {
  copyFileSync(from: string, to: string): void;
  existsSync(file: string): boolean;
  mkdirSync(file: string, opts?: { recursive?: boolean }): void;
  mkdtempSync(prefix: string): string;
  readFileSync(file: string, encoding: "utf8"): string;
  readdirSync(file: string): string[];
  realpathSync(file: string): string;
  rmSync(file: string, opts?: { recursive?: boolean;
    force?: boolean }): void;
  statSync(file: string): { size: number; mtimeMs: number;
    isDirectory(): boolean };
  writeFileSync(file: string, data: string): void;
};

const os = import.meta.require("os") as {
  availableParallelism(): number;
  setPriority(pid: number, priority: number): void;
  tmpdir(): string;
};

const path = import.meta.require("path") as {
  sep: string;
  basename(file: string, ext?: string): string;
  dirname(file: string): string;
  join(...parts: string[]): string;
  relative(from: string, to: string): string;
};

const workers = import.meta.require("worker_threads") as {
  isMainThread: boolean;
  workerData: unknown;
  parentPort: {
    on(event: "message", listener: (value: never) => void): void;
    postMessage(value: unknown): void;
  } | null;
  Worker: new (file: string, opts?: { eval?: boolean;
    workerData?: unknown }) => Kid;
};

export const ROOT = path.join(import.meta.dirname, "..");

export const TESTS = path.join("check", "tests");

export const GOLDS = path.join(TESTS, "demos");

export const MAIN = path.join(ROOT, "bend2", "comp.ts");

export const DEMOS = ["http_server", "nat_proofs", "runtime_stress"];

export const CC = ["-std=c11", "-O0", "-w"];

export const LANES: Record<string, string[]> = {
  "--seq": ["--parallel", "off"],
  "--par": ["--threads", "8", "--gpu", "off"],
};

export const JOIN: Record<string, [string, string]> = {
  "IO(Unit)": ["IO(Unit)", "bt_join"],
};

export const EXEC_TIMEOUT = 30_000;

export const SHARD_TIMEOUT = 120_000;

export const SHARD_STACK = "33554432";

export const BUDGET = 150_000;

export const WIDTH = 8;

export const SHARD_MAX = 48;

export const SENTINEL = "@@B4T";

export const PERF = path.join(os.tmpdir(), "bend-perf-here");

export const RESCUED: string[] = [];

const DEAL = workers.workerData as Deal | null;

const LOCK = path.join(os.tmpdir(), "bend-test-lock");

const DEADLINE = DEAL?.deadline ?? lock_boot();

let BASE_BOOK: core.Book | null = null;

let BASE_PATH: string | null = null;

let BASE_NAMES: Set<string> | null = null;

// Lock
// ====

function lock_take(): void {
  const pidf = path.join(LOCK, "pid");
  for (;;) {
    try {
      fs.mkdirSync(LOCK);
      fs.writeFileSync(pidf, String(process.pid));
      process.on("exit", () => {
        try {
          fs.rmSync(LOCK, { recursive: true, force: true });
        } catch {}
      });
      return;
    } catch {}
    let live = false;
    let age = 0;
    try {
      age = Date.now() - fs.statSync(LOCK).mtimeMs;
      process.kill(Number(fs.readFileSync(pidf, "utf8")), 0);
      live = true;
    } catch {}
    if (!live && age > 5_000) {
      try {
        fs.rmSync(LOCK, { recursive: true, force: true });
      } catch {}
    } else {
      child.execFileSync("/bin/sleep", ["1"]);
    }
  }
}

function lock_sweep(): void {
  try {
    child.execFileSync("/usr/bin/pkill", ["-9", "-f", "bend-test-"]);
  } catch {}
}

function lock_boot(): number {
  if (import.meta.main) {
    lock_take();
    lock_sweep();
  }
  return Date.now() + BUDGET;
}

// Exec
// ====

export function exec_tail(got: Exec): string {
  switch (got.halt) {
    case "exit": {
      return "exit " + String(got.code);
    }
    case "signal": {
      return "signal " + String(got.sig);
    }
    case "spawn": {
      return "spawn failure";
    }
    default: {
      return "timeout";
    }
  }
}

export function exec_run(cmd: string, args: string[], cwd?: string,
  cap: number = EXEC_TIMEOUT,
  env?: Record<string, string | undefined>): Promise<Exec> {
  const go = (bg: boolean): Promise<Exec> => {
    const left = DEADLINE - Date.now();
    const timeout = Math.max(1, Math.min(cap, left));
    const exe = bg ? "/usr/sbin/taskpolicy" : cmd;
    const argv = bg ? ["-c", "background", cmd, ...args] : args;
    return new Promise((resolve) => {
      child.execFile(exe, argv, { timeout, encoding: "utf8",
        maxBuffer: 64 * 1024 * 1024, cwd, env }, (e, out, err) => {
        let code = 1;
        if (e === null) {
          code = 0;
        } else if (typeof e.code === "number") {
          code = e.code;
        }
        const killed = e !== null && (e as { killed?: boolean }).killed ===
          true;
        const sig = e === null
          ? null
          : (e as { signal?: string | null }).signal ?? null;
        let halt: "exit" | "signal" | "timeout" | "spawn" = "exit";
        if (killed) {
          halt = "timeout";
        } else if (e !== null && typeof e.code === "string") {
          halt = "spawn";
        } else if (sig !== null) {
          halt = "signal";
        }
        if (killed && bg) {
          RESCUED.push("note: killed under background QoS beside a live" +
            " perf grid, retried at normal priority: " +
            [cmd, ...args].join(" "));
          resolve(go(false));
        } else if (killed) {
          resolve({ out: "(killed: " + String(Math.round(timeout / 1000)) +
            "s timeout)", err: "", code, sig, halt });
        } else {
          const errs = halt === "spawn" ? String((e as Error).message) : err;
          resolve({ out, err: errs, code, sig, halt });
        }
      });
    });
  };
  return go(perf_live());
}

// Perf
// ====

export function perf_live(): boolean {
  try {
    process.kill(Number(fs.readFileSync(path.join(PERF, "pid"), "utf8")), 0);
    return true;
  } catch {
    return false;
  }
}

// Test
// ====

export function test_blocks(src: string): Block[] {
  const blocks: Block[] = [];
  for (const line of src.split("\n")) {
    if (line.startsWith("$$ ")) {
      blocks.push({ cmd: line.slice(3).trim(), exp: "" });
    } else if (blocks.length > 0) {
      blocks[blocks.length - 1].exp += line + "\n";
    }
  }
  return blocks;
}

export function test_new(name: string, file: string, src: string): Test {
  const t: Test = { name, file, blocks: test_blocks(src), fails: [] };
  const cut = src.search(/^\$\$ /m);
  const head = cut < 0 ? src : src.slice(0, cut);
  const ymark = /^# yellow: (.+)$/m.exec(head);
  if (ymark !== null) {
    t.yellow = ymark[1].trim();
  }
  const rmark = /^# rss < (\d+)$/m.exec(head);
  if (rmark !== null) {
    t.rss = Number(rmark[1]);
  }
  const pins = [...head.matchAll(/^# csrc has: (.+)$/gm)].map((m) => m[1]);
  if (pins.length > 0) {
    t.csrc = pins;
  }
  const bans = [...head.matchAll(/^# csrc not: (.+)$/gm)].map((m) => m[1]);
  if (bans.length > 0) {
    t.cnot = bans;
  }
  return t;
}

export function test_fail(t: Test, cmd: string, exp: string,
  got: string): void {
  t.fails.push("  cmd:      " + cmd);
  t.fails.push("  expected: " + exp.replace(/\n/g, "\\n"));
  t.fails.push("  observed: " + got.replace(/\n/g, "\\n"));
}

export function test_show(t: Test, tag: string = ""): void {
  let mark = "PASS ";
  if (t.fails.length > 0) {
    mark = t.yellow === undefined ? "FAIL " : "YELLOW ";
  }
  const atag = tag === "" ? "" : " [" + tag + "]";
  const ytag = t.yellow === undefined ? "" : " [" + t.yellow + "]";
  console.log(mark + t.name + atag + ytag);
  for (const line of t.fails) {
    console.log(line);
  }
}

export function test_tally(tests: Test[], notes: string[] = []): boolean {
  const pass = tests.filter((t) => t.fails.length === 0).length;
  const yell = tests.filter((t) =>
    t.fails.length > 0 && t.yellow !== undefined).length;
  for (const n of notes) {
    console.log(n);
  }
  const noted = notes.length === 0
    ? ""
    : ", " + String(notes.length) + " noted (rescues, printed above)";
  console.log("\n" + String(pass) + "/" + String(tests.length) +
    " passing, " + String(yell) + " yellow, " +
    String(tests.length - pass - yell) + " red" + noted);
  return pass + yell === tests.length;
}

// Corpus
// ======

export function corpus_tracked(): string[] {
  const got = child.spawnSync("git", ["-C", ROOT, "ls-files", "--", TESTS],
    { encoding: "utf8", maxBuffer: 64 * 1024 * 1024 });
  if (got.status !== 0) {
    throw new Error("cannot establish the tracked set: git ls-files" +
      " failed under " + ROOT);
  }
  return got.stdout.split("\n").filter((l) => l !== "");
}

export function corpus_disk(): string[] {
  const out: string[] = [];
  const walk = (rel: string): void => {
    for (const f of fs.readdirSync(path.join(ROOT, rel))) {
      const at = path.join(rel, f);
      if (fs.statSync(path.join(ROOT, at)).isDirectory()) {
        walk(at);
      } else {
        out.push(at);
      }
    }
  };
  if (fs.existsSync(path.join(ROOT, TESTS))) {
    walk(TESTS);
  }
  return out.sort();
}

export function corpus_scan(): { tests: string[]; golds: string[] } {
  const tracked = corpus_tracked();
  const have = new Set(tracked);
  const disk = corpus_disk();
  const bad: string[] = [];
  for (const f of disk) {
    if (!have.has(f)) {
      bad.push("untracked file under " + TESTS +
        " (git add it or delete it): " + f);
    }
  }
  for (const f of tracked) {
    if (!disk.includes(f)) {
      bad.push("tracked file missing from disk: " + f);
    }
  }
  const tests: string[] = [];
  const golds: string[] = [];
  for (const f of tracked) {
    const rel = path.relative(TESTS, f);
    if (rel === "SKIPPED.txt") {
      continue;
    } else if (/^[a-z0-9_]+\.(?:js|c)$/.test(rel)) {
      continue;
    } else if (/^[a-z0-9_]+\.bend$/.test(rel)) {
      tests.push(f);
    } else if (rel.startsWith("demos" + path.sep) && rel.endsWith(".txt")) {
      golds.push(path.basename(rel, ".txt"));
    } else {
      bad.push("a file " + TESTS + " has no row for: " + f);
    }
  }
  const want = new Set(DEMOS);
  const got = new Set(golds);
  for (const d of DEMOS) {
    if (!got.has(d)) {
      bad.push("demo golden missing: " + path.join(GOLDS, d + ".txt"));
    }
  }
  for (const g of golds) {
    if (!want.has(g)) {
      bad.push("golden without a demo: " + path.join(GOLDS, g + ".txt"));
    }
  }
  if (bad.length > 0) {
    throw new Error(bad.sort().join("\n"));
  }
  return { tests: tests.sort(), golds };
}

// Err
// ===

export function err_text(e: unknown): string {
  if (e !== null && typeof e === "object" && (e as core.Err).$ === "Err") {
    return core.err_show(e as core.Err);
  }
  return String(e);
}

// Base
// ====

export function base_seed(): core.Book {
  if (BASE_BOOK === null) {
    BASE_PATH = fs.realpathSync(path.join(ROOT, "bend2", "base.bend"));
    const b = core.book_nil();
    core.book_load(b, BASE_PATH, "", new Map());
    core.book_valid(b);
    BASE_BOOK = b;
  }
  return BASE_BOOK;
}

export function base_imported(file: string): boolean {
  for (const raw of fs.readFileSync(file, "utf8").split("\n")) {
    const line = raw.trim();
    if (line === "import Base") {
      return true;
    }
    if (line !== "" && !line.startsWith("#") && !/^import\s/.test(line)) {
      return false;
    }
  }
  return false;
}

export function base_names(): Set<string> {
  if (BASE_NAMES === null) {
    BASE_NAMES = new Set(Object.keys(base_seed().tlds));
  }
  return BASE_NAMES;
}

// Book
// ====

export function book_of(file: string): Checked {
  const book = core.book_nil();
  try {
    if (!base_imported(file)) {
      core.book_load(book, file, "", new Map());
      core.book_valid(book);
      return { book };
    }
    const base = base_seed();
    for (const k of Object.keys(base.tlds)) {
      book.tlds[k] = { ...base.tlds[k] };
    }
    Object.assign(book.ctrs, base.ctrs);
    book.order.push(...base.order);
    core.book_load(book, file, "", new Map([[BASE_PATH as string, ""]]));
    const pre = core.book_nil();
    for (const k of base.order) {
      pre.tlds[k] = book.tlds[k];
    }
    Object.assign(pre.ctrs, base.ctrs);
    for (let i = base.order.length; i < book.order.length; i++) {
      const k = book.order[i];
      const tld = book.tlds[k];
      if (tld.$ === "ADT") {
        pre.tlds[k] = tld;
        for (const c of tld.c) {
          pre.ctrs[c.k] = c;
        }
        core.adt_valid(pre, k, tld);
      } else {
        const dec: core.Def = { $: "Def", n: tld.n, T: tld.T, v: null };
        const fin = book.order.lastIndexOf(k) === i;
        pre.tlds[k] = dec;
        core.def_valid(pre, k, fin ? tld : dec);
        pre.tlds[k] = fin ? tld : dec;
      }
    }
    return { book };
  } catch (e) {
    return { err: err_text(e).trim() };
  }
}

export function book_interp(c: Checked): string {
  if (c.err !== undefined) {
    return c.err;
  }
  const book = c.book as core.Book;
  try {
    if (book.tlds["main"] === undefined) {
      return "";
    }
    const A = tocl.io_type(book);
    if (A !== null) {
      const chunks: string[] = [];
      const fsm = require("fs");
      const out = process.stdout.write;
      const err = process.stderr.write;
      const syn = fsm.writeSync;
      const grab = (s: string | Uint8Array): boolean => {
        chunks.push(typeof s === "string" ? s : Buffer.from(s).toString());
        return true;
      };
      const grab_sync = (fd: number, b: Uint8Array, at?: number,
        len?: number): number => {
        if (fd !== 1 && fd !== 2) {
          return syn(fd, b, at, len);
        }
        const lo = at ?? 0;
        const hi = lo + (len ?? b.length - lo);
        chunks.push(Buffer.from(b.slice(lo, hi)).toString());
        return hi - lo;
      };
      process.stdout.write = grab as typeof process.stdout.write;
      process.stderr.write = grab as typeof process.stderr.write;
      fsm.writeSync = grab_sync;
      try {
        tocl.io_run(book);
      } finally {
        process.stdout.write = out;
        process.stderr.write = err;
        fsm.writeSync = syn;
      }
      return chunks.join("").trim();
    }
    const t = core.term_snf(book, core.Ref("main"));
    return core.term_show(core.term_lower(t));
  } catch (e) {
    return err_text(e).trim();
  }
}

export function book_show(c: Checked, file: string, name?: string): string {
  if (c.err !== undefined) {
    return c.err;
  }
  const book = c.book as core.Book;
  try {
    const whole = name === undefined && base_imported(file);
    const start = whole ? base_seed().order.length : 0;
    const keys = name !== undefined
      ? [name]
      : [...new Set(book.order.slice(start))];
    const rows: string[] = [];
    for (const k of keys) {
      const tld = book.tlds[k];
      if (tld === undefined) {
        return "bend: no def named " + k;
      }
      if (tld.$ === "Def" && tld.v !== null) {
        rows.push(k + " = " + core.term_show(core.term_lower(tld.v)));
      }
    }
    return rows.join("\n");
  } catch (e) {
    return err_text(e).trim();
  }
}

export function book_emit(c: Checked,
  kind: "c" | "js"): { src?: string; err?: string } {
  if (c.err !== undefined) {
    return { err: c.err };
  }
  try {
    const emit = kind === "c" ? tocl.compile_book : tocl.js_book;
    return { src: emit(c.book as core.Book) };
  } catch (e) {
    return { err: err_text(e).trim() };
  }
}

export function book_main(c: Checked): string | null {
  const main = c.book?.tlds["main"];
  if (main === undefined || main.$ !== "Def" || main.v === null) {
    return null;
  }
  const A = tocl.io_type(c.book as core.Book);
  if (A !== null) {
    try {
      const payload = core.term_wnf(c.book as core.Book, A);
      const shown = core.term_show(core.term_lower(payload));
      return "IO(" + shown + ")";
    } catch {
      return null;
    }
  }
  try {
    const md = core.tele_unbind(c.book as core.Book, main.T);
    if (md.doms.slice(0, main.n).some(([q]) => q.$ !== "None")) {
      return null;
    }
    const ret = core.term_wnf(c.book as core.Book, md.ret);
    return core.term_show(core.term_lower(ret));
  } catch {
    return null;
  }
}

// Member
// ======

export function member_body(src: string, book: core.Book,
  prefix: string): string {
  const own: string[] = [];
  for (const k of Object.keys(book.tlds)) {
    if (!base_names().has(k)) {
      own.push(k);
      const tld = book.tlds[k];
      if (tld.$ === "ADT") {
        for (const c of tld.c) {
          own.push(c.k);
        }
      }
    }
  }
  let out = src.replace(/^import Base\s*$/m, "");
  own.sort((a, b) => b.length - a.length);
  for (const k of own) {
    const esc = k.replace(/\./g, "\\.");
    const re = new RegExp("(?<![A-Za-z0-9_.])" + esc +
      "(?![A-Za-z0-9_.])", "g");
    out = out.replace(re, prefix + "_" + k);
  }
  return out;
}

// Built
// =====

export async function built_lane(t: Test, kind: "c" | "js", c: Checked,
  tmp: string): Promise<Built> {
  const got = book_emit(c, kind);
  if (got.err !== undefined) {
    if (/Maximum call stack/.test(got.err)) {
      return built_spawn(t, kind, tmp);
    }
    return { err: got.err + "\nexit 1" };
  }
  const base = path.join(tmp, t.name.replace(/[^A-Za-z0-9]/g, "_"));
  const out = base + (kind === "js" ? ".js" : ".c");
  fs.writeFileSync(out, got.src as string);
  if (kind === "js") {
    return { js: out };
  }
  const cc = await exec_run("cc", [...CC, out, "-lpthread", "-o",
    base + ".bin"]);
  if (cc.code !== 0) {
    return { err: "cc: " + (cc.out + cc.err).trim().split("\n")[0] };
  }
  return { bin: base + ".bin" };
}

export async function built_spawn(t: Test, kind: "c" | "js",
  tmp: string): Promise<Built> {
  const base = path.join(tmp, t.name.replace(/[^A-Za-z0-9]/g, "_"));
  const out = base + (kind === "js" ? ".js" : ".c");
  const got = await exec_run(process.execPath, [MAIN, t.file, "--to", out]);
  if (got.code !== 0) {
    return { err: (got.out + got.err).trim() + "\n" + exec_tail(got) };
  }
  if (kind === "js") {
    return { js: out };
  }
  const cc = await exec_run("cc", [...CC, out, "-lpthread", "-o",
    base + ".bin"]);
  if (cc.code !== 0) {
    return { err: "cc: " + (cc.out + cc.err).trim().split("\n")[0] };
  }
  return { bin: base + ".bin" };
}

// Lane
// ====

export async function lane_c(t: Test, blk: Block, built: Built,
  lane: string, tmp: string): Promise<string> {
  if (built.err !== undefined) {
    return built.err;
  }
  const bin = built.bin as string;
  if (lane === "--seq" && t.rss !== undefined) {
    const got = await exec_run("/usr/bin/time", ["-l", bin,
      ...LANES[lane]], tmp);
    const all = got.out + got.err;
    const rss = /(\d+)\s+maximum resident set size/.exec(all);
    const mb = rss === null ? -1 : Number(rss[1]) / (1 << 20);
    if (mb < 0 || mb >= t.rss) {
      test_fail(t, blk.cmd + " # rss < " + String(t.rss),
        "under " + String(t.rss) + " MB resident",
        rss === null ? "(no rss reading)" : mb.toFixed(1) + " MB");
    }
    const noise = new RegExp("\\d+[.,]\\d+\\s+real|maximum resident" +
      "|^\\s+\\d+\\s+\\w|instructions retired|cycles elapsed|peak memory");
    const lines = all.split("\n").filter((l) => !noise.test(l));
    return lines.join("\n").trim() + "\n" + exec_tail(got);
  }
  const got = await exec_run(bin, LANES[lane], tmp);
  return (got.out + got.err).trim() + "\n" + exec_tail(got);
}

export async function lane_js(t: Test, built: Built,
  tmp: string): Promise<string> {
  if (built.err !== undefined) {
    return built.err;
  }
  const got = await exec_run(process.execPath, [built.js as string], tmp);
  return (got.out + got.err).trim() + "\n" + exec_tail(got);
}

// Defer
// =====

export function defer_ok(kind: "c" | "js", exp: string, t: Test,
  key: string | null, src: string): boolean {
  const e = exp.trim();
  const solo = !e.endsWith("\nexit 0") || t.rss !== undefined ||
    t.csrc !== undefined || t.cnot !== undefined || key === null;
  if (solo) {
    return false;
  }
  const real_io = new RegExp("IO\\.(print_err|get_env|die)|File\\.|" +
    "TCP\\.|UDP\\.|Socket\\.|Listener\\.|import \"");
  if (real_io.test(src)) {
    return false;
  }
  if (kind === "js") {
    return true;
  }
  return JOIN[key as string] !== undefined;
}

// File
// ====

export async function file_run(name: string, file: string, src: string,
  tmp: string): Promise<FileRet> {
  const t = test_new(name, file, src);
  const defers: Defer[] = [];
  if (t.blocks.length === 0) {
    t.fails.push("  no $$ command blocks (a test pins something)");
    return { test: t, defers };
  }
  const cut = src.search(/^\$\$ /m);
  const prog_src = cut < 0 ? src : src.slice(0, cut);
  if (!name.startsWith("demos/")) {
    const prog = path.join(tmp, name.replace(/[^A-Za-z0-9]/g, "_") + ".bend");
    fs.writeFileSync(prog, prog_src);
    for (const m of prog_src.matchAll(
      /^\s*import "\.\/([a-z0-9_]+\.(?:js|c))"$/gm)) {
      const eff = path.join(path.dirname(file), m[1]);
      if (fs.existsSync(eff)) {
        fs.copyFileSync(eff, path.join(tmp, m[1]));
      }
    }
    t.file = prog;
  }
  const yellow = t.yellow !== undefined;
  const checked = yellow ? null : book_of(t.file);
  const key = checked === null ? null : book_main(checked);
  if (t.csrc !== undefined || t.cnot !== undefined) {
    let cs: { src?: string; err?: string };
    if (yellow) {
      const out = path.join(tmp,
        name.replace(/[^A-Za-z0-9]/g, "_") + "_pin.c");
      const got = await exec_run(process.execPath,
        [MAIN, t.file, "--to", out]);
      cs = got.code !== 0
        ? { err: (got.out + got.err).trim() }
        : { src: fs.readFileSync(out, "utf8") };
    } else {
      cs = book_emit(checked as Checked, "c");
    }
    for (const pin of t.csrc ?? []) {
      if (cs.src === undefined || !cs.src.includes(pin)) {
        test_fail(t, "# csrc has: " + pin,
          "the emitted C holds it verbatim", cs.err ?? "(absent)");
      }
    }
    for (const ban of t.cnot ?? []) {
      if (cs.src !== undefined && cs.src.includes(ban)) {
        test_fail(t, "# csrc not: " + ban,
          "the emitted C lacks it verbatim", "(present)");
      }
    }
  }
  const prefix = "t_" + name.replace(/[^A-Za-z0-9]/g, "_");
  const mergeable = !name.startsWith("demos/") && !prog_src.includes(prefix);
  let cbuilt: Built | null = null;
  let jbuilt: Built | null = null;
  const cdefer: Block[] = [];
  const jdefer: Block[] = [];
  for (const blk of t.blocks) {
    if (Date.now() > DEADLINE) {
      test_fail(t, blk.cmd, "(run inside the " + String(BUDGET / 1000) +
        "s budget)", "budget spent");
      break;
    }
    const show = /^bend % --show(?: ([A-Za-z0-9_.]+))?$/.exec(blk.cmd);
    const form = show !== null
      ? null
      : /^bend %( --(seq|par|js))?$/.exec(blk.cmd);
    if (show === null && form === null) {
      test_fail(t, blk.cmd, "(the suite runs `bend %` with" +
        " --seq/--par/--js/--show only; it owns the backends)", "");
      continue;
    }
    const lane = form === null || form[1] === undefined ? "" : form[1].trim();
    let got: string | null = null;
    if (show !== null) {
      got = book_show(checked ?? book_of(t.file), t.file, show[1]);
    } else if (lane === "") {
      if (yellow) {
        const ran = await exec_run(process.execPath, [MAIN, t.file]);
        got = (ran.out + ran.err).trim();
      } else {
        got = book_interp(checked as Checked);
        if (/Maximum call stack/.test(got)) {
          const ran = await exec_run(process.execPath, [MAIN, t.file]);
          got = (ran.out + ran.err).trim();
        }
      }
    } else if (lane === "--js") {
      if (!yellow && mergeable && defer_ok("js", blk.exp, t, key, prog_src)) {
        jdefer.push(blk);
      } else {
        if (jbuilt === null) {
          jbuilt = yellow
            ? await built_spawn(t, "js", tmp)
            : await built_lane(t, "js", checked as Checked, tmp);
        }
        got = await lane_js(t, jbuilt, tmp);
      }
    } else {
      if (!yellow && mergeable && defer_ok("c", blk.exp, t, key, prog_src)) {
        cdefer.push(blk);
      } else {
        if (cbuilt === null) {
          cbuilt = yellow
            ? await built_spawn(t, "c", tmp)
            : await built_lane(t, "c", checked as Checked, tmp);
        }
        got = await lane_c(t, blk, cbuilt, lane, tmp);
      }
    }
    if (got !== null && blk.exp.trim() !== got.trim()) {
      test_fail(t, blk.cmd, blk.exp.trim(), got.trim());
    }
  }
  if (cdefer.length > 0 || jdefer.length > 0) {
    const own_src = name.startsWith("demos/")
      ? fs.readFileSync(file, "utf8")
      : prog_src;
    const body = member_body(own_src,
      (checked as Checked).book as core.Book, prefix);
    if (cdefer.length > 0) {
      defers.push({ kind: "c", name, prog: t.file, prefix, body,
        key: key as string, blocks: cdefer });
    }
    if (jdefer.length > 0) {
      defers.push({ kind: "js", name, prog: t.file, prefix, body,
        key: key as string, blocks: jdefer });
    }
  }
  return { test: t, defers };
}

// Shard
// =====

export function shard_patch(csrc: string, fids: string[]): string {
  const edit = (s: string, from: string, to: string): string => {
    if (!s.includes(from)) {
      throw new Error("shard patch anchor missing: " +
        JSON.stringify(from.slice(0, 60)));
    }
    return s.replace(from, to);
  };
  return edit(csrc,
    "  Corpus H  = corpus_setup(metal, thr > 0 ? thr : dflt);\n" +
    "  int code  = io_loop(H, metal, FID_MAIN);\n" +
    "  io_sync();\n" +
    "  return code;",
    [
      "  static const u32 SUITE_FIDS[] = { " + fids.join(", ") + " };",
      "  long thrs = thr > 0 ? thr : dflt;",
      "  for (u32 ti = 0; ti < sizeof(SUITE_FIDS) / sizeof(u32); ti += 1) {",
      "    printf(\"\\n" + SENTINEL + " %u\\n\", ti);",
      "    fflush(stdout);",
      "    memset(ALC, 0, sizeof(ALC));",
      "    Corpus H  = corpus_setup(metal, thrs);",
      "    int code = io_loop(H, metal, SUITE_FIDS[ti]);",
      "    if (code != 0) {",
      "      return code;",
      "    }",
      "    fflush(stdout);",
      "    munmap(CORPUS, (metal ? (1ull << 28) : (1ull << 40)) * 8);",
      "  }",
      "  return 0;",
    ].join("\n"));
}

export function shard_src(members: Defer[], tag: number,
  kind: "c" | "js"): string {
  let src = "import Base\n\n" +
    members.map((m) => m.body).join("\n") + "\n";
  if (kind === "js") {
    return src;
  }
  const [ty, join] = JOIN[members[0].key];
  src += "assert " + join + ":\n  forall a: " + ty + "\n  forall b: " +
    ty + "\n  " + ty + "\n\ndef " + join + "(a, b):\n" +
    "  IO.bind(Unit, Unit, a, u => b)\n\n";
  let layer = members.map((m) => m.prefix + "_main");
  let nid = 0;
  while (layer.length > 1) {
    const next: string[] = [];
    for (let j = 0; j < layer.length; j += 2) {
      if (j + 1 === layer.length) {
        next.push(layer[j]);
        continue;
      }
      const name = "bt_s" + String(tag) + "_" + String(nid++);
      const both = "Both{" + layer[j] + ", " + layer[j + 1] + "}";
      src += "assert " + name + ":\n  " + ty + "\n\ndef " + name +
        "():\n  Both{a, b} = {" + both + " : Par<" + ty + ", " + ty +
        ">}\n  " + join + "(a, b)\n\n";
      next.push(name + "()");
    }
    layer = next;
  }
  return src + "assert main:\n  " + ty + "\n\ndef main():\n  " +
    layer[0] + "\n";
}

export function shard_judge(members: Defer[], cmd: string, stdout: string,
  fails: Fail[]): void {
  const marks = [...stdout.matchAll(
    new RegExp("^" + SENTINEL + " (\\d+)$", "gm"))].map((m) => Number(m[1]));
  const right = marks.length === members.length &&
    marks.every((v, i) => v === i);
  if (!right) {
    throw new Error("shard sentinel boundaries read [" + marks.join(" ") +
      "], not 0.." + String(members.length - 1) +
      ": a member's output forged or lost one");
  }
  const segs = stdout.split(new RegExp("^" + SENTINEL + " \\d+\\n", "m"))
    .slice(1);
  members.forEach((m, i) => {
    for (const blk of m.blocks) {
      if (blk.cmd === cmd) {
        const seen = (segs[i] ?? "").split(m.prefix + "_").join("").trim() +
          "\nexit 0";
        if (blk.exp.trim() !== seen.trim()) {
          fails.push({ name: m.name, cmd: blk.cmd, exp: blk.exp.trim(),
            got: seen.trim() });
        }
      }
    }
  });
}

export async function shard_fallback(members: Defer[],
  tmp: string): Promise<Fail[]> {
  const fails: Fail[] = [];
  for (const m of members) {
    const t: Test = { name: m.name + "_solo", file: m.prog,
      blocks: m.blocks, fails: [] };
    const checked = book_of(m.prog);
    const built = await built_lane(t, m.kind, checked, tmp);
    for (const blk of m.blocks) {
      const lane = blk.cmd.slice("bend % ".length);
      const got = m.kind === "js"
        ? await lane_js(t, built, tmp)
        : await lane_c(t, blk, built, lane, tmp);
      if (blk.exp.trim() !== got.trim()) {
        fails.push({ name: m.name, cmd: blk.cmd, exp: blk.exp.trim(),
          got: got.trim() });
      }
    }
  }
  return fails;
}

export async function shard_build(file: string,
  out: string): Promise<{ src?: string; err?: string }> {
  const env = { ...process.env, BUN_JSC_maxPerThreadStackUsage: SHARD_STACK };
  const got = await exec_run(process.execPath, [MAIN, file, "--to", out],
    undefined, SHARD_TIMEOUT, env);
  if (got.code !== 0) {
    return { err: (got.out + got.err).trim() };
  }
  return { src: fs.readFileSync(out, "utf8") };
}

export async function shard_run(kind: "c" | "js", members: Defer[],
  tag: number, tmp: string): Promise<ShardRet> {
  try {
    if (kind === "c" && members.length < 2) {
      return { fails: await shard_fallback(members, tmp) };
    }
    const base = path.join(tmp, "shard_" + kind + String(tag));
    fs.writeFileSync(base + ".bend", shard_src(members, tag, kind));
    const emitted = await shard_build(base + ".bend",
      base + (kind === "js" ? ".js" : ".c"));
    if (emitted.err !== undefined) {
      throw new Error("shard build: " + emitted.err.split("\n")[0]);
    }
    const fails: Fail[] = [];
    if (kind === "js") {
      let js = emitted.src as string;
      members.forEach((m, i) => {
        js += "\nconsole.log(" +
          JSON.stringify("\n" + SENTINEL + " " + String(i)) +
          ");\nio_run($" + m.prefix + "_main$);";
      });
      const out = base + ".js";
      fs.writeFileSync(out, js);
      const got = await exec_run(process.execPath, [out], tmp,
        SHARD_TIMEOUT);
      if (got.code !== 0 || got.err.trim() !== "") {
        throw new Error("shard run: exit " + String(got.code) + " " +
          got.err.trim().split("\n")[0]);
      }
      shard_judge(members, "bend % --js", got.out, fails);
      return shard_diag(members, fails, tmp);
    }
    const fids = members.map((m) =>
      "FID_" + (m.prefix + "_main").toUpperCase());
    const csrc = shard_patch(emitted.src as string, fids);
    fs.writeFileSync(base + ".c", csrc);
    const cc = await exec_run("cc", [...CC, base + ".c", "-lpthread",
      "-o", base + ".bin"]);
    if (cc.code !== 0) {
      throw new Error("shard cc: " +
        (cc.out + cc.err).trim().split("\n")[0]);
    }
    for (const lane of ["--seq", "--par"]) {
      const has = members.some((m) =>
        m.blocks.some((b) => b.cmd === "bend % " + lane));
      if (!has) {
        continue;
      }
      const got = await exec_run(base + ".bin", LANES[lane], tmp,
        SHARD_TIMEOUT);
      if (got.code !== 0 || got.err.trim() !== "") {
        throw new Error("shard run " + lane + ": exit " +
          String(got.code) + " " + got.err.trim().split("\n")[0]);
      }
      shard_judge(members, "bend % " + lane, got.out, fails);
    }
    return shard_diag(members, fails, tmp);
  } catch (e) {
    const fails = await shard_fallback(members, tmp);
    const who = " [members: " + members.map((m) => m.name).join(" ") + "]";
    fails.push({ name: "shard_" + kind + String(tag),
      cmd: "(merged shard)",
      exp: "(the merged book checks, builds and runs)",
      got: (e instanceof Error ? e.message : String(e)) + who });
    return { fails };
  }
}

export async function shard_diag(members: Defer[], fails: Fail[],
  tmp: string): Promise<ShardRet> {
  if (fails.length === 0) {
    return { fails };
  }
  const bad = members.filter((m) => fails.some((f) => f.name === m.name));
  const solo = await shard_fallback(bad, tmp);
  for (const f of fails) {
    const twice = solo.some((s) => s.name === f.name);
    f.got += twice
      ? " [fails standalone too]"
      : " [passes standalone: a whole-book emission defect]";
  }
  return { fails };
}

// Purity
// ======

export function purity_run(tmp: string): Test {
  const t: Test = { name: "reg_compiler_pure", file: "", blocks: [],
    fails: [] };
  const src = fs.readFileSync(path.join(ROOT, TESTS,
    "reg_borrow_loop.bend"), "utf8");
  const prog = path.join(tmp, "reg_compiler_pure.bend");
  fs.writeFileSync(prog, src.slice(0, src.search(/^\$\$ /m)));
  const one = book_of(prog);
  if (one.err !== undefined) {
    t.fails.push("  " + one.err.split("\n")[0]);
    return t;
  }
  const tld_at = (k: string): Record<string, unknown> =>
    (one.book as core.Book).tlds[k] as unknown as Record<string, unknown>;
  const snap = Object.keys((one.book as core.Book).tlds).map((k) =>
    [k, Object.keys(tld_at(k)).map((f) => tld_at(k)[f])] as const);
  const c1 = book_emit(one, "c");
  const j1 = book_emit(one, "js");
  if (c1.err !== undefined || j1.err !== undefined) {
    test_fail(t, "the purity witness emits",
      "(reg_borrow_loop compiles in both backends: a refusal would" +
      " judge purity on nothing)",
      ((c1.err ?? j1.err) as string).split("\n")[0]);
    return t;
  }
  const i1 = book_interp(one);
  const wrote = snap.flatMap(([k, vs]) =>
    Object.keys(tld_at(k)).filter((f, i) => tld_at(k)[f] !== vs[i])
      .map((f) => k + "." + f));
  if (wrote.length > 0) {
    test_fail(t, "compile_book(checked)",
      "(no tld field written: the book is the compiler's INPUT)",
      String(wrote.length) + " fields replaced (" +
        wrote.slice(0, 3).join(" ") + ")");
  }
  const two = book_of(prog);
  const i2 = book_interp(two);
  const c2 = book_emit(two, "c");
  const j2 = book_emit(two, "js");
  const c3 = book_emit(one, "c");
  const eq = (cmd: string, a: { src?: string; err?: string },
    b: { src?: string; err?: string }): void => {
    const sa = a.err ?? a.src ?? "";
    const sb = b.err ?? b.src ?? "";
    if (sa === sb) {
      return;
    }
    const la = sa.split("\n");
    const lb = sb.split("\n");
    const at = la.findIndex((l, i) => l !== lb[i]);
    test_fail(t, cmd, "(byte-equal)", "line " + String(at + 1) + ": " +
      String(la[at]).slice(0, 60) + " vs " + String(lb[at]).slice(0, 60));
  };
  eq("tocl on a fresh book, second in the process", c1, c2);
  eq("js_book on a fresh book, second in the process", j1, j2);
  eq("tocl again on the once-compiled book", c1, c3);
  eq("the evaluator on a compiled-from book", { src: i1 }, { src: i2 });
  return t;
}

// Load
// ====

export function load_run(tmp: string): Test {
  const t: Test = { name: "reg_import_walls", file: "", blocks: [],
    fails: [] };
  const dir = path.join(tmp, "import_walls");
  fs.mkdirSync(dir, { recursive: true });
  const put = (name: string, lines: string[]): string => {
    const file = path.join(dir, name);
    fs.writeFileSync(file, lines.join("\n") + "\n");
    return file;
  };
  const stub = (name: string, head: string[]): string[] => [...head, "",
    "assert " + name + ":", "  Nat", "", "def " + name + "():", "  0n"];
  const a = put("a.bend", stub("a_one", ["import ./b.bend as B"]));
  put("b.bend", stub("b_one", ["import ./a.bend as A"]));
  const twice = put("twice.bend",
    stub("main", ["import ./x.bend as A", "import ./x.bend as B"]));
  put("x.bend", stub("x_one", []));
  const self = put("self.bend", stub("s_one", ["import ./self.bend as S"]));
  put("mid.bend", stub("m_one", ["import ./x.bend as X"]));
  const clash = put("clash.bend",
    stub("c_one", ["import ./x.bend as Y", "import ./mid.bend as M"]));
  const diamond = put("diamond.bend",
    stub("d_one", ["import Base", "import ./x.bend as X",
      "import ./mid.bend as M"]));
  const wall = (cmd: string, file: string, msg: string): void => {
    const got = book_of(file);
    if (got.err === undefined) {
      test_fail(t, cmd, "a refusal (" + msg + ")", "the book checked");
    } else if (!got.err.includes(msg)) {
      test_fail(t, cmd, "a refusal (" + msg + ")",
        got.err.split("\n").slice(0, 2).join(" ").slice(0, 120));
    }
  };
  wall("bend a.bend (a two-file import cycle)", a,
    "an acyclic import graph");
  wall("bend self.bend (a one-file import cycle)", self,
    "an acyclic import graph");
  wall("bend twice.bend (one file under two namespaces)", twice,
    "one namespace per file");
  wall("bend clash.bend (one namespace from two importers)", clash,
    "one namespace per file");
  const two = book_of(diamond);
  if (two.err !== undefined) {
    test_fail(t, "bend diamond.bend (one file, one namespace, two importers)",
      "the diamond accepted (one realpath loads once)",
      two.err.split("\n").slice(0, 2).join(" ").slice(0, 120));
  }
  return t;
}

// Lint
// ====

export function lint_run(): Test {
  const t: Test = { name: "reg_repo_lint", file: "", blocks: [], fails: [] };
  const rows: [string, string[], boolean, string[], string?, boolean?][] = [
    ["a prose comment", ["// measured on node 12"], false, ["comment"]],
    ["a section marker", ["// Term", "// ===="], false, []],
    ["a subsection marker", ["// Drop", "// ----"], false, []],
    ["the C ADT comment",
      ["// Term ::=", "//   | Wrd(val)", "//   | Ctr(cid, loc)"], false, []],
    ["the effect use directive", ["//! use ./sys.js"], false, []],
    ["a bang note", ["//! measured on node 12"], false, ["comment"]],
    ["an indented use directive", ["  //! use ./sys.js"], false,
      ["comment"]],
    ["a line over 80 columns", ["y".repeat(81)], false, ["width"]],
    ["a trailing space", ["const tail = 1 "], false, ["space"]],
    ["an odd indent", [" go()"], false, ["indent"]],
    ["an indent jump", ["go()", "    on()"], false, ["indent"]],
    ["a one-line block", ["if (a) { go() }"], false, ["block"]],
    ["a braceless body", ["if (a) go()"], false, ["block"]],
    ["an opened block", ["if (a) {", "  go()", "}"], false, []],
    ["two statements", ["go(); on();"], false, ["statements"]],
    ["a comma operator", ["(tick(), tock())"], false, ["comma"]],
    ["a nested ternary", ["const pick = a ? b ? c : d : e"], false,
      ["ternary"]],
    ["a plain ternary", ["const pick = a ? b : c"], false, []],
    ["a control-flow macro", ["#define GO(x) return x"], false, ["macro"]],
    ["a worklist macro", ["#define WL_GO(x) return x"], false, []],
    ["a def outside its section", ["function stray(): void {", "}"], true,
      ["layout"]],
    ["a type outside Types", ["type Stray = number"], true, ["layout"]],
    ["a global outside Constants", ["const stray = 1"], true, ["layout"]],
    ["a sectioned def",
      ["// Boot", "// ====", "", "function boot_run(): void {", "}"], true,
      []],
    ["a subsection def, dodging its section",
      ["// Boot", "// ====", "", "// Warm", "// ----", "",
        "function warm_up(): void {", "}"], true, ["layout"]],
    ["a suffix-fit def",
      ["// Show", "// ====", "", "function term_show(): void {", "}"], true,
      []],
    ["a top-level statement", ["go();"], true, ["layout"]],
    ["a statement in the Main section",
      ["// Main", "// ====", "", "go();"], true, []],
    ["a const arrow posing as a constant",
      ["// Constants", "// =========", "", "const go = (x: b): b => x;"],
      true, ["layout"]],
    ["a name used before its declaration",
      ["// Constants", "// =========", "", "function a_func(): number {",
        "  return CAP;", "}", "const CAP = 1;"], true, ["layout"]],
    ["a backslash continuation",
      ["const cap = 1 \\", "  + 2;"], false, ["continuation"]],
    ["a def without a return type",
      ["// Boot", "// ====", "", "function boot_go(x: number) {", "}"],
      true, ["types"]],
    ["a section with two homes",
      ["// Boot", "// ====", "", "// Tidy", "// ====", "", "// Boot",
        "// ===="], true, ["layout"]],
    ["a _func def", ["function tidy_func(): void {", "}"], true, []],
    ["a Types type", ["// Types", "// =====", "", "type Row = number"], true,
      []],
    ["a Constants global",
      ["// Constants", "// =========", "", "const cap = 1"], true, []],
    ["a C def outside its section",
      ["static void stray_run(void) {", "}"], true, ["layout"], "//",
      true],
    ["a C prototype outside its section",
      ["static void stray_drop(Env e);"], true, [], "//", true],
    ["a C sectioned def",
      ["// Boot", "// ====", "", "static void boot_run(void) {", "}"],
      true, [], "//", true],
    ["a C subsection def, dodging its section",
      ["// Boot", "// ====", "", "// Warm", "// ----", "",
        "INLINE u32 warm_up(u32 x) {", "}"], true, ["layout"], "//", true],
    ["a C attributed def",
      ["// Boot", "// ====", "",
        "static void __attribute__((constructor)) boot_use(void) {", "}"],
      true, [], "//", true],
    ["a C kernel def",
      ["// Boot", "// ====", "", "kernel void boot_dev(Corpus H) {", "}"],
      true, [], "//", true],
    ["a C typedef and global, unbound",
      ["typedef struct {", "  int x;", "} Stray;", "static int stray = 1;"],
      true, [], "//", true],
    ["a C define, unbound", ["#define STRAY_CAP 12"], true, [], "//",
      true],
    ["a C define block, aligned",
      ["#define GO_ONE  1", "#define GO_DEEP 2"], false, [], "//", true],
    ["a C define block, misaligned",
      ["#define GO_ONE 1", "#define GO_DEEP 2"], false, ["align"], "//",
      true],
    ["a C define block, split by a blank line",
      ["#define GO_ONE 1", "", "#define GO_DEEP 2"], false, [], "//",
      true],
    ["a C macro continuation, outside the block",
      ["#define GO_ONE \\", "  1", "#define GO_DEEPER(x) x"], false, [],
      "//", true],
    ["a C globals block, aligned",
      ["static u32  go_one;", "static bool go_deep;"], false, [], "//",
      true],
    ["a C globals block, misaligned",
      ["static u32 go_one;", "static bool go_deep;"], false, ["align"],
      "//", true],
    ["a C ADT block, same-length names",
      ["// Fall ::=", "//   | Done()",
        "//   | Fail(code, text)   code 0 carries no text"], false, [],
      "//", true],
    ["a C ADT block, uneven constructors",
      ["// Tag ::=", "//   | Go(x)", "//   | Stop(y)"], false, ["names"],
      "//", true],
    ["a C ADT block, uneven fields",
      ["// Row ::=", "//   | Row(gen, kind)"], false, ["names"], "//",
      true],
    ["a bend section marker", ["# Word", "# ----"], false, [], "#"],
    ["a bend three-part file",
      ["# Types", "# =====", "", "type Bit:", "  B{}", "", "# Claims",
        "# ======", "", "assert one:", "  Bit", "", "assert two:", "  Bit",
        "", "# Proofs", "# ======", "", "def one():", "  B{}", "",
        "def two():", "  B{}"], true, [], "#"],
    ["a bend type outside its part",
      ["# Claims", "# ======", "", "type Stray:", "  S{}"], true,
      ["layout"], "#"],
    ["a bend def outside its part",
      ["# Claims", "# ======", "", "assert one:", "  Type", "",
        "def one():", "  Type"], true, ["layout"], "#"],
    ["a bend def against the claims' order",
      ["# Claims", "# ======", "", "assert one:", "  Type", "",
        "assert two:", "  Type", "", "# Proofs", "# ======", "",
        "def two():", "  Type", "", "def one():", "  Type"], true,
      ["layout"], "#"],
    ["a bend def filling no claim",
      ["# Proofs", "# ======", "", "def stray():", "  Type"], true,
      ["layout"], "#"],
    ["a bend types assert a field applies",
      ["# Types", "# =====", "", "assert Wrd:", "  forall n: Nat", "  Type",
        "", "type Reg:", "  Reg{data: Wrd(32n)}"], true, [], "#"],
    ["a bend types assert no type applies",
      ["# Types", "# =====", "", "assert Wrd:", "  forall n: Nat",
        "  Type"], true, ["layout"], "#"],
    ["a bend section out of place",
      ["# Proofs", "# ======"], true, ["layout"], "#"],
    ["a bend prose comment", ["# measured on node 12"], false, ["comment"],
      "#"],
    ["a bend argument list", ["(tick(), tock())"], false, [], "#"],
    ["a bend wide line", ["y".repeat(81)], false, ["width"], "#"],
  ];
  for (const [name, lines, layout, want, lead, cee] of rows) {
    const flags = repo.style_lint(lines.join("\n") + "\n", layout,
      lead ?? "//", false, cee ?? false);
    const got = [...new Set(flags.map((f) => f.rule))].sort();
    if (got.join(" ") !== want.join(" ")) {
      test_fail(t, "style_lint on " + name,
        want.join(" ") === "" ? "(clean)" : want.join(" "),
        got.join(" ") === "" ? "(clean)" : got.join(" "));
    }
  }
  return t;
}

// Emit
// ====

export function emit_run(): Test {
  const t: Test = { name: "reg_emit_style", file: "", blocks: [], fails: [] };
  const reps = ["nat_copy", "nat_double", "nat_add", "nat_sub", "nat_mul",
    "nat_divmod", "nat_cmp", "nat_is_lt", "string_append"];
  const want = [...Object.keys(tocl.INTRINSICS), ...reps].sort();
  const got = Object.keys(tocl.JS_INTRINSICS).sort();
  if (got.join(" ") !== want.join(" ")) {
    const extra = got.filter((k) => !want.includes(k));
    const missing = want.filter((k) => !got.includes(k));
    test_fail(t, "the shared intrinsic registry",
      "(the JS renderer keys are tocl's intrinsic inventory plus the" +
      " recursive ops of the native-represented Nat and String)",
      "extra: " + extra.join(" ") + " missing: " + missing.join(" "));
  }
  for (const prog of ["bench/runtime/kmeans.bend", "demos/http_server.bend"]) {
    const book = book_of(path.join(ROOT, prog));
    for (const kind of ["c", "js"] as const) {
      const got = book_emit(book, kind);
      if (got.err !== undefined) {
        test_fail(t, "emit " + prog, "(the program compiles to " + kind + ")",
          got.err.split("\n")[0]);
        continue;
      }
      const flags = repo.style_lint(got.src as string, false, "//", false,
        kind === "c");
      if (flags.length > 0) {
        const f = flags[0];
        test_fail(t, "style_lint on the emitted " + kind + " of " + prog,
          "(clean: PART 4 binds the C and JS the compiler prints)",
          String(flags.length) + " flags, first " + f.rule + " at line " +
            String(f.line) + ": " + f.text.slice(0, 60));
      }
    }
  }
  return t;
}

// Pins
// ====

export function pins_meas(secs: number): perf.Meas {
  return { ms: secs * 1000, rss: 0, output: "7" };
}

export function pins_cell(got: perf.Meas | null, note: string,
  dead: boolean): perf.Cell {
  return { base: "bench", mode: 0, node: 0, dead, got, note };
}

export function pins_pin(secs: (number | null)[],
  out: string | null): Map<string, perf.Pin> {
  return new Map([["bench", { secs, out }]]);
}

export function pins_chk(got: number | null, note: string): perf.Chk {
  return { name: "trees_400", want: 1.0, got, note };
}

export function pins_run(): Test {
  const t: Test = { name: "reg_perf_gate", file: "", blocks: [], fails: [] };
  const rows: [string, perf.Cell[], Map<string, perf.Pin>, string[]][] = [
    ["a cell at its pin", [pins_cell(pins_meas(1.0), "", false)],
      pins_pin([1.0, null, null], null), []],
    ["a cell inside the quantum", [pins_cell(pins_meas(1.04), "", false)],
      pins_pin([1.0, null, null], null), []],
    ["a cell past the quantum", [pins_cell(pins_meas(1.06), "", false)],
      pins_pin([1.0, null, null], null), ["fix the regression"]],
    ["an errored cell", [pins_cell(null, "exit 9 (wedged?)", false)],
      pins_pin([1.0, null, null], null), ["exit 9"]],
    ["a bench with no pin row", [pins_cell(pins_meas(1.0), "", false)],
      new Map(), ["only Taelin writes one"]],
    ["a vanished pinned bench", [], pins_pin([1.0, null, null], null),
      ["may not vanish", "measured nothing"]],
    ["a dead cell with a pinned time", [pins_cell(null, "", true)],
      pins_pin([1.0, null, null], null), ["refuses the bench"]],
    ["a dash row that now runs", [pins_cell(pins_meas(1.0), "", false)],
      pins_pin([null, null, null], null), ["now runs"]],
  ];
  for (const [name, cells, pin, want] of rows) {
    const got = perf.pin_gate(cells, pin);
    const miss = want.filter((w) => !got.some((g) => g.includes(w)));
    if (got.length !== want.length || miss.length > 0) {
      test_fail(t, "pin_gate on " + name,
        want.length === 0 ? "(no fail)" : want.join("; "),
        got.length === 0 ? "(no fail)" : got.join("; "));
    }
  }
  const match = pins_cell(pins_meas(1.0), "", false);
  const clash = pins_cell(pins_meas(1.0), "", false);
  perf.pin_stamp([match], pins_pin([1.0, null, null], "7"));
  perf.pin_stamp([clash], pins_pin([1.0, null, null], "8"));
  if (match.got === null || match.note !== "") {
    test_fail(t, "pin_stamp on the pinned checksum",
      "(the cell keeps its measure)", match.note);
  }
  if (clash.got !== null || !clash.note.includes("checksum 7 != pinned 8")) {
    test_fail(t, "pin_stamp on a checksum clash",
      "checksum 7 != pinned 8 (and the cell's measure dies)", clash.note);
  }
  const checks: [string, perf.Chk[], string[]][] = [
    ["a check inside the quantum", [pins_chk(1.04, "")], []],
    ["a check past the quantum", [pins_chk(1.06, "")],
      ["fix the regression"]],
    ["an errored check", [pins_chk(null, "check: boom")], ["check: boom"]],
    ["no pinned checker bench", [], ["measured nothing"]],
  ];
  for (const [name, cells, want] of checks) {
    const got = perf.check_gate(cells);
    const miss = want.filter((w) => !got.some((g) => g.includes(w)));
    if (got.length !== want.length || miss.length > 0) {
      test_fail(t, "check_gate on " + name,
        want.length === 0 ? "(no fail)" : want.join("; "),
        got.length === 0 ? "(no fail)" : got.join("; "));
    }
  }
  const grid = perf.pin_read();
  const board = ["bitonic", "gameoflife", "kmeans", "mandelbrot", "matmul",
    "merkle", "nbody", "queens", "radix", "raytrace", "symreg", "terrain"];
  for (const name of board) {
    const row = grid.get(name);
    if (row === undefined || row.secs.some((s) => s === null) ||
      row.out === null) {
      test_fail(t, "pin_read " + name,
        "three pinned seconds and a pinned checksum",
        row === undefined ? "(no row parsed)" : JSON.stringify(row));
    }
  }
  const check = perf.check_read();
  for (const name of ["defs_12800", "proofs_3200", "compute_1600",
    "trees_400", "generics_3200"]) {
    const row = check.find((c) => c.name === name);
    if (row === undefined || !(row.want > 0)) {
      test_fail(t, "check_read " + name, "a pinned check time",
        row === undefined ? "(no row parsed)" : JSON.stringify(row));
    }
  }
  return t;
}

// Stack
// =====

export function stack_witness(): string {
  const F = 25;
  const N = 1535;
  const fields = Array.from({ length: F }, (_, i) =>
    "f" + String(i) + ": Bool").join(", ");
  const binds = Array.from({ length: F }, (_, i) =>
    "a" + String(i)).join(", ");
  const fresh = "W{" +
    Array.from({ length: F }, () => "False{}").join(", ") + "}";
  let src = "import Base\n\ntype Wide:\n  W{" + fields + "}\n\n";
  for (let i = N; i >= 1; i -= 1) {
    const call = 2 * i + 1 <= N
      ? "Both{g" + String(2 * i) + "(" + fresh + "), g" +
        String(2 * i + 1) + "(" + fresh + ")}"
      : "Both{1, 1}";
    src += "assert g" + String(i) + ":\n  forall r: Wide\n  U32\n\ndef g" +
      String(i) + "(r):\n  match r:\n    case W{" + binds + "}:\n" +
      "      Both{x, y} = {" + call + " : Par<U32, U32>}\n" +
      "      U32.add(x, y)\n\n";
  }
  return src + "assert main:\n  IO(Unit)\n\ndef main():\n" +
    "  IO.print(U32.show(g1(" + fresh + ")))\n";
}

export async function stack_run(tmp: string): Promise<Test> {
  const t: Test = { name: "reg_worker_stack", file: "", blocks: [],
    fails: [] };
  const prog = path.join(tmp, "reg_worker_stack.bend");
  fs.writeFileSync(prog, stack_witness());
  t.file = prog;
  const built = await built_lane(t, "c", book_of(prog), tmp);
  const exp = "1536\nexit 0";
  for (const lane of ["--seq", "--par"]) {
    const blk: Block = { cmd: "bend % " + lane, exp };
    const got = await lane_c(t, blk, built, lane, tmp);
    if (got.trim() !== exp) {
      test_fail(t, blk.cmd, exp, got.trim());
    }
  }
  if (built.err === undefined) {
    const shcmd = "ulimit -s 600; " +
      JSON.stringify(built.bin as string) + " --parallel off";
    const low = await exec_run("/bin/sh", ["-c", shcmd], tmp);
    const faulted = /bend: error 10/.test(low.out + low.err) ||
      low.halt === "signal" ||
      (low.halt === "exit" && low.code > 128);
    if (!faulted || low.out.includes("1536")) {
      test_fail(t, "bend % --seq # under a 600KB RLIMIT_STACK",
        "a stack fault ('bend: error 10' or a signal death: the frame" +
        " is over the old 512KB worker default)",
        (low.out + low.err).trim() + "\n" + exec_tail(low));
    }
  }
  return t;
}

// Cli
// ===

export async function cli_run(tmp: string): Promise<Test> {
  const t: Test = { name: "cli_surface", file: "", blocks: [], fails: [] };
  const usage = "usage: bend <file.bend> [--to <out.c|out.js>]";
  const ok = path.join(tmp, "cli_ok.bend");
  const bad = path.join(tmp, "cli_bad.bend");
  const absent = path.join(tmp, "cli_absent.bend");
  const out_c = path.join(tmp, "cli_out.c");
  const out_js = path.join(tmp, "cli_out.js");
  fs.writeFileSync(ok,
    "import Base\n\nassert main:\n  IO(Unit)\n\ndef main():\n" +
    "  IO.print(\"ok\")\n");
  fs.writeFileSync(bad, "main : U32<> = 7\n");
  const rows: [string[], string][] = [
    [[], usage + "\nexit 1"],
    [["--help"], usage + "\nexit 0"],
    [["--frobnicate"],
      "bend: unknown option --frobnicate\n" + usage + "\nexit 1"],
    [[ok, "--watch"],
      "bend: unknown option --watch\n" + usage + "\nexit 1"],
    [[ok, "--to"],
      "bend: --to needs an output file\n" + usage + "\nexit 1"],
    [[ok, "--to", "cli_out.txt"],
      "bend: --to expects a .c or a .js file, not cli_out.txt\n" +
        usage + "\nexit 1"],
    [[ok, "--to", out_c, "extra"],
      "bend: too many arguments\n" + usage + "\nexit 1"],
    [[absent],
      "Error: ENOENT: no such file or directory, lstat '" + absent +
        "'\nexit 1"],
    [[bad], "Error:\n- expected : 'def', 'type' or 'assert'\n" +
      "- observed : 'm'\nLocation:\n1>| main : U32<> = 7\n2 |\nexit 1"],
    [[ok], "ok\nexit 0"],
    [[ok, "--to", out_c], "exit 0"],
    [[ok, "--to", out_js], "exit 0"],
  ];
  await Promise.all(rows.map(async ([args, exp]) => {
    const r = await exec_run("bun", [MAIN, ...args], tmp);
    const text = (r.out + r.err).replace(/[ \t]+$/gm, "").trim();
    const got = (text + "\n" + exec_tail(r)).trim();
    if (got !== exp) {
      test_fail(t, ["bend", ...args].join(" "), exp, got);
    }
  }));
  const marks: [string, string][] =
    [[out_c, "// Imports"], [out_js, "function io_run"]];
  for (const [file, mark] of marks) {
    const emitted = fs.existsSync(file) ? fs.readFileSync(file, "utf8") : "";
    if (!emitted.includes(mark)) {
      test_fail(t, "bend cli_ok.bend --to " + path.basename(file),
        mark + " (in the written file)",
        emitted === "" ? "(no file written)" : emitted.slice(0, 60));
    }
  }
  return t;
}

// Knob
// ====

export async function knob_run(tmp: string): Promise<Test> {
  const t: Test = { name: "reg_cli_knobs", file: "", blocks: [], fails: [] };
  const prog = path.join(tmp, "reg_cli_knobs.bend");
  fs.writeFileSync(prog,
    "import Base\n\nassert main:\n  IO(Unit)\n\ndef main():\n" +
    "  IO.print(\"ok\")\n");
  t.file = prog;
  const book = book_of(prog);
  const built = await built_lane(t, "c", book, tmp);
  if (built.err !== undefined) {
    test_fail(t, "bend reg_cli_knobs.bend --to .c", "a built binary",
      built.err);
    return t;
  }
  const bin = built.bin as string;
  const contra = "bend: --parallel off means --threads 1 with --gpu off";
  const help = ["usage: " + bin + " [options]",
    "  --threads N        worker threads, up to 128 (default: the CPU count)",
    "  --parallel on|off  off means one thread and no GPU (default: on)",
    "  --gpu on|off       send ! calls to the GPU (default: on if present)",
    "  --help             show this text",
    "exit 0"].join("\n");
  const rows: [string[], string][] = [
    [["--parallel", "off"], "ok\nexit 0"],
    [["--parallel", "off", "--gpu", "on"], contra + "\nexit 1"],
    [["--parallel", "off", "--threads", "8"], contra + "\nexit 1"],
    [["--threads", "0"],
      "bend: expected a thread count of 1 or more after --threads\nexit 1"],
    [["--threads", "8x"],
      "bend: expected a thread count of 1 or more after --threads\nexit 1"],
    [["--threads", " 4"], "ok\nexit 0"],
    [["--threads", "+1"], "ok\nexit 0"],
    [["--gpu", "maybe"], "bend: expected 'on' or 'off' after --gpu\nexit 1"],
    [["--parallel"],
      "bend: expected 'on' or 'off' after --parallel\nexit 1"],
    [["--frobnicate"], "bend: unknown option --frobnicate\nexit 1"],
    [["--help"], help],
  ];
  await Promise.all(rows.map(async ([args, exp]) => {
    const r = await exec_run(bin, args, tmp);
    const got = ((r.out + r.err).trim() + "\n" + exec_tail(r)).trim();
    if (got !== exp) {
      test_fail(t, ["bend %", ...args].join(" "), exp, got);
    }
  }));
  const bjs = await built_lane(t, "js", book, tmp);
  if (bjs.err !== undefined) {
    test_fail(t, "bend reg_cli_knobs.bend --to .js", "a built program",
      bjs.err);
    return t;
  }
  const js = bjs.js as string;
  const jhelp = ["usage: " + fs.realpathSync(js) + " [options]",
    "  --threads N        worker threads: a JS program runs one",
    "  --parallel on|off  off means one thread and no GPU (default: on)",
    "  --gpu on|off       send ! calls to the GPU (default: on if present)",
    "  --help             show this text",
    "exit 0"].join("\n");
  const jrows: [string[], string][] = [
    [[], "ok\nexit 0"],
    [["--parallel", "off"], "ok\nexit 0"],
    [["--parallel", "on"], "ok\nexit 0"],
    [["--threads", "1"], "ok\nexit 0"],
    [["--gpu", "off"], "ok\nexit 0"],
    [["--parallel", "off", "--gpu", "on"], contra + "\nexit 1"],
    [["--parallel", "off", "--threads", "8"], contra + "\nexit 1"],
    [["--threads", "0"],
      "bend: expected a thread count of 1 or more after --threads\nexit 1"],
    [["--threads", "8x"],
      "bend: expected a thread count of 1 or more after --threads\nexit 1"],
    [["--threads", " 1"], "ok\nexit 0"],
    [["--threads", " 4"],
      "bend: --threads over 1, but a JS program runs one thread\nexit 1"],
    [["--threads", "+1"], "ok\nexit 0"],
    [["--gpu", "maybe"], "bend: expected 'on' or 'off' after --gpu\nexit 1"],
    [["--parallel"],
      "bend: expected 'on' or 'off' after --parallel\nexit 1"],
    [["--frobnicate"], "bend: unknown option --frobnicate\nexit 1"],
    [["--threads", "8"],
      "bend: --threads over 1, but a JS program runs one thread\nexit 1"],
    [["--gpu", "on"],
      "bend: --gpu on, but this binary found no Metal device\nexit 1"],
    [["--help"], jhelp],
  ];
  await Promise.all(jrows.map(async ([args, exp]) => {
    const r = await exec_run(process.execPath, [js, ...args], tmp);
    const got = ((r.out + r.err).trim() + "\n" + exec_tail(r)).trim();
    if (got !== exp) {
      test_fail(t, ["bend % --js", ...args].join(" "), exp, got);
    }
  }));
  return t;
}

// Job
// ===

export async function job_run(job: Job, tmp: string): Promise<Ret> {
  if (job.kind === "file") {
    return { file: await file_run(job.name, job.file, job.src, tmp) };
  }
  if (job.kind === "stack") {
    return { file: { test: await stack_run(tmp), defers: [] } };
  }
  if (job.kind === "cli") {
    return { file: { test: await cli_run(tmp), defers: [] } };
  }
  if (job.kind === "lint") {
    return { file: { test: lint_run(), defers: [] } };
  }
  if (job.kind === "emit") {
    return { file: { test: emit_run(), defers: [] } };
  }
  if (job.kind === "pins") {
    return { file: { test: pins_run(), defers: [] } };
  }
  if (job.kind === "pure") {
    return { file: { test: purity_run(tmp), defers: [] } };
  }
  if (job.kind === "load") {
    return { file: { test: load_run(tmp), defers: [] } };
  }
  if (job.kind === "guard") {
    return { file: { test: await guard_run(), defers: [] } };
  }
  if (job.kind === "knob") {
    return { file: { test: await knob_run(tmp), defers: [] } };
  }
  return shard_run(job.sub, job.members, job.tag, tmp);
}

// Pool
// ====

export function pool_open(ws: Kid[],
  on: (job: Job, r: Ret) => void): Pool {
  const queue: Job[] = [];
  const jobs = new Map<Kid, Job>();
  const idle: Kid[] = [];
  let live = ws.length;
  let open = true;
  let fin!: () => void;
  const done = new Promise<void>((r) => {
    fin = r;
  });
  const feed = (): void => {
    while (idle.length > 0 && queue.length > 0) {
      const w = idle.shift() as Kid;
      const j = queue.shift() as Job;
      jobs.set(w, j);
      w.postMessage(j);
    }
    if (live === 0) {
      while (queue.length > 0) {
        const j = queue.shift() as Job;
        on(j, lost(j, "no live worker left for the queued job"));
      }
    }
    if (!open && jobs.size === 0 && queue.length === 0) {
      for (const w of ws) {
        w.removeAllListeners("message");
        w.removeAllListeners("error");
        w.removeAllListeners("exit");
      }
      fin();
    }
  };
  const lost = (j: Job, why: string): Ret => {
    const one = (name: string): Fail => ({ name, cmd: "(worker)",
      exp: "(a result for every submitted job)", got: why });
    if (j.kind === "shard") {
      return { fails: j.members.map((m) => one(m.name)) };
    }
    if (j.kind === "file") {
      return { fails: [one(j.name)] };
    }
    if (j.kind === "cli") {
      return { fails: [one("cli_surface")] };
    }
    if (j.kind === "lint") {
      return { fails: [one("reg_repo_lint")] };
    }
    if (j.kind === "emit") {
      return { fails: [one("reg_emit_style")] };
    }
    if (j.kind === "pins") {
      return { fails: [one("reg_perf_gate")] };
    }
    if (j.kind === "pure") {
      return { fails: [one("reg_compiler_pure")] };
    }
    if (j.kind === "load") {
      return { fails: [one("reg_import_walls")] };
    }
    if (j.kind === "guard") {
      return { fails: [one("reg_suite_guard")] };
    }
    if (j.kind === "knob") {
      return { fails: [one("reg_cli_knobs")] };
    }
    return { fails: [one("reg_worker_stack")] };
  };
  for (const w of ws) {
    idle.push(w);
    w.on("message", (r: Ret) => {
      const j = jobs.get(w) as Job;
      jobs.delete(w);
      idle.push(w);
      on(j, r);
      feed();
    });
    w.on("error", (e) => {
      const j = jobs.get(w);
      jobs.delete(w);
      if (j !== undefined) {
        on(j, lost(j, String(e)));
      }
      feed();
    });
    w.on("exit", (c) => {
      live -= 1;
      const at = idle.indexOf(w);
      if (at >= 0) {
        idle.splice(at, 1);
      }
      const j = jobs.get(w);
      jobs.delete(w);
      if (j !== undefined) {
        on(j, lost(j, "the worker exited " + String(c) + " mid-job"));
      }
      feed();
    });
  }
  return {
    push: (j, front = false): void => {
      if (front) {
        queue.unshift(j);
      } else {
        queue.push(j);
      }
      feed();
    },
    close: (): void => {
      open = false;
      feed();
    },
    done,
  };
}

// Guard
// =====

export function guard_member(name: string, out: string): Defer {
  return { kind: "c", name, prog: "", prefix: "p_" + name, body: "",
    key: "IO(Unit)",
    blocks: [{ cmd: "bend % --seq", exp: out + "\nexit 0\n" }] };
}

export async function guard_run(): Promise<Test> {
  const t: Test = { name: "reg_suite_guard", file: "", blocks: [],
    fails: [] };
  const ms = [guard_member("one", "1"), guard_member("two", "2")];
  const straight: Fail[] = [];
  shard_judge(ms, "bend % --seq",
    "\n" + SENTINEL + " 0\n1\n\n" + SENTINEL + " 1\n2\n", straight);
  if (straight.length > 0) {
    test_fail(t, "shard_judge on honest boundaries", "(no fail)",
      JSON.stringify(straight[0]));
  }
  const forged = "\n" + SENTINEL + " 0\n1\n" + SENTINEL + " 7\n\n" +
    SENTINEL + " 1\n2\n";
  const short = "\n" + SENTINEL + " 0\n1\n";
  const rows: [string, string][] = [["a forged boundary", forged],
    ["a lost boundary", short]];
  for (const [name, out] of rows) {
    let died = "";
    try {
      shard_judge(ms, "bend % --seq", out, []);
    } catch (e) {
      died = e instanceof Error ? e.message : String(e);
    }
    if (!died.includes("sentinel")) {
      test_fail(t, "shard_judge on " + name,
        "a loud sentinel refusal (the fallback re-runs the members)",
        died === "" ? "(judged silently)" : died);
    }
  }
  const dead = new workers.Worker("", { eval: true });
  const seen: Fail[] = [];
  const pool = pool_open([dead], (_job, r) => {
    seen.push(...(r.fails ?? []));
  });
  pool.push({ kind: "lint" });
  pool.push({ kind: "pins" });
  pool.close();
  await pool.done;
  if (seen.length !== 2) {
    test_fail(t, "pool_open over a dead worker",
      "one red row per submitted job (2)",
      String(seen.length) + " rows: " +
        seen.map((r) => r.got).join(" | "));
  }
  return t;
}

// Tests
// =====

export async function tests_run(): Promise<{ tests: Test[];
  notes: string[] }> {
  const scan = corpus_scan();
  const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "bend-test-"));
  const files: Job[] = [
    ...DEMOS.map((d): Job => ({ kind: "file", name: "demos/" + d,
      file: path.join(ROOT, "demos", d + ".bend"),
      src: fs.readFileSync(path.join(ROOT, GOLDS, d + ".txt"), "utf8") })),
    ...scan.tests.map((f): Job => ({ kind: "file",
      name: path.basename(f, ".bend"), file: path.join(ROOT, f),
      src: fs.readFileSync(path.join(ROOT, f), "utf8") })),
  ];
  const cost = (j: Job): number => {
    if (j.kind !== "file") {
      return 0;
    }
    const gold = j.name.startsWith("demos/") ? fs.statSync(j.file).size : 0;
    return j.src.length + gold;
  };
  files.sort((a, b) => cost(b) - cost(a));
  files.unshift({ kind: "cli" });
  const width = Math.max(1,
    Math.min(WIDTH, os.availableParallelism(), files.length));
  const ws = Array.from({ length: width + 2 }, () =>
    new workers.Worker(import.meta.filename,
      { workerData: { kind: "worker", tmp, deadline: DEADLINE } as Deal }));
  const tests: Test[] = [];
  const notes: string[] = [];
  const touched = new Set<Test>();
  const pools = new Map<string, Defer[]>();
  let tag = 0;
  let files_left = files.length;
  const shard_of = (key: string, members: Defer[]): Job =>
    ({ kind: "shard", sub: key === "js" ? "js" : "c", tag: tag++, members });
  const on = (job: Job, r: Ret): void => {
    if (r.file !== undefined) {
      tests.push(r.file.test);
      test_show(r.file.test);
      for (const d of r.file.defers) {
        const key = d.kind === "js" ? "js" : "c:" + d.key;
        const pool = pools.get(key) ??
          pools.set(key, []).get(key) as Defer[];
        pool.push(d);
        if (pool.length >= SHARD_MAX + 2) {
          const chunk = pool.splice(0, SHARD_MAX)
            .sort((x, y) => (x.name < y.name ? -1 : 1));
          run.push(shard_of(key, chunk), true);
        }
      }
    }
    for (const n of r.notes ?? []) {
      console.log(n);
      notes.push(n);
    }
    for (const f of r.fails ?? []) {
      let t = tests.find((it) => it.name === f.name);
      if (t === undefined) {
        t = { name: f.name, file: "", blocks: [], fails: [] };
        tests.push(t);
      }
      test_fail(t, f.cmd, f.exp, f.got);
      touched.add(t);
    }
    if (job.kind === "file" || job.kind === "cli") {
      files_left -= 1;
      if (files_left === 0) {
        for (const [key, pool] of pools) {
          pool.sort((x, y) => (x.name < y.name ? -1 : 1));
          const cuts = Math.max(1, Math.ceil(pool.length / SHARD_MAX));
          const step = Math.ceil(pool.length / cuts);
          for (let k = 0; k < pool.length; k += step) {
            run.push(shard_of(key, pool.slice(k, k + step)), true);
          }
        }
        run.close();
      }
    }
  };
  const aside = pool_open([ws[width]], on);
  aside.push({ kind: "stack" });
  aside.close();
  const fresh = pool_open([ws[width + 1]], on);
  fresh.push({ kind: "pure" });
  fresh.push({ kind: "emit" });
  fresh.push({ kind: "lint" });
  fresh.push({ kind: "pins" });
  fresh.push({ kind: "load" });
  fresh.push({ kind: "guard" });
  fresh.push({ kind: "knob" });
  fresh.close();
  const run = pool_open(ws.slice(0, width), on);
  for (const f of files) {
    run.push(f);
  }
  await run.done;
  await aside.done;
  await fresh.done;
  for (const t of touched) {
    test_show(t, "compiled");
  }
  await Promise.all(ws.map((w) => w.terminate()));
  fs.rmSync(tmp, { recursive: true, force: true });
  return { tests: tests.sort((a, b) => (a.name < b.name ? -1 : 1)), notes };
}

// Main
// ====

process.env.NO_COLOR = "1";
try {
  os.setPriority(0, 19);
} catch {}

if (!workers.isMainThread && DEAL !== null) {
  workers.parentPort?.on("message", (job: Job) => {
    void job_run(job, DEAL.tmp).then((r) => {
      if (RESCUED.length > 0) {
        r.notes = [...(r.notes ?? []), ...RESCUED.splice(0)];
      }
      workers.parentPort?.postMessage(r);
    });
  });
} else if (import.meta.main) {
  const bomb = setTimeout(() => {
    console.log("the " + String(BUDGET / 1000) +
      "s budget is spent -- a slow suite is a broken suite");
    console.log("FAILED");
    lock_sweep();
    process.exit(1);
  }, Math.max(1, DEADLINE - Date.now()));
  bomb.unref();
  try {
    const { tests, notes } = await tests_run();
    const stale = tests.filter((t) =>
      t.yellow !== undefined && t.fails.length === 0);
    for (const t of stale) {
      t.yellow = undefined;
      t.fails.push("  stale yellow marker: every block passes --" +
        " remove the `# yellow:` pragma");
      test_show(t);
    }
    let ok = test_tally(tests, notes);
    if (ok && Date.now() > DEADLINE) {
      console.log("over the " + String(BUDGET / 1000) +
        "s budget at the verdict -- a slow suite is a broken suite");
      ok = false;
    }
    console.log(ok ? "PASSED" : "FAILED");
    process.exit(ok ? 0 : 1);
  } catch (e) {
    console.log(e instanceof Error ? e.message : String(e));
    console.log("FAILED");
    process.exit(1);
  }
}
