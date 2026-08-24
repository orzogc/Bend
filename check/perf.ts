#!/usr/bin/env bun

import * as child from "node:child_process";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import * as zlib from "node:zlib";
import * as gen from "../bench/check/_gen_.ts";

// Types
// =====

export type Exec = { stdout: string; stderr: string };

export type Range = { dir: string; count: number; size: number; base: number };

export type Job = {
  key: string;
  hop: number;
  run: (node: number) => Promise<void>;
  fail: (node: number, e: unknown) => void;
  retry: (node: number, e: unknown) => void;
};

export type Meas = { ms: number; rss: number; output: string };

export type Pin = { secs: (number | null)[]; out: string | null };

export type Cell = {
  base: string;
  mode: number;
  node: number;
  dead: boolean;
  got: Meas | null;
  note: string;
};

export type Chk = {
  name: string;
  want: number;
  got: number | null;
  note: string;
};

export type Io = { ops: number; note: string };

// Constants
// =========

const HERE = process.argv.includes("--here");

const ROOT = path.join(import.meta.dirname, "..");

const MAIN = path.join(ROOT, "src", "bend.ts");

const BENCH = path.join(ROOT, "bench");

const PIN = path.join(BENCH, "_pin_apple_m4_.txt");

const CHECK_PIN = path.join(BENCH, "check", "_pin_apple_m4_.txt");

const CHECK_RUNS = 3;

const MODES = ["SEQ-CPU", "PAR-CPU", "PAR-GPU"];

const TIMEOUT = HERE ? 30_000 : 180_000;

const DRIFT_NOTE = 10;

const GRACE = 0.05;

const CC = "cc -std=c11 -O3 -fno-slp-vectorize";

const MODE_CC = [
  CC + " b.c -lpthread",
  CC + " b.c -lpthread",
  CC + " -DBEND_METAL=1 -x objective-c -fobjc-arc b.c -lpthread" +
    " -framework Metal -framework Foundation",
];

const NODE_THREADS = "nt=1; while [ $nt -lt $(getconf _NPROCESSORS_ONLN) ]" +
  " && [ $nt -lt 256 ]; do nt=$((nt*2)); done; ";

const MODE_ARGS = ["--parallel off", "--threads $nt --gpu off", "--gpu on"];

const SLOTS = { dir: "/tmp/bend-cluster-slots", count: 4, size: 48, base: 2 };

const STALE = 20 * 60 * 1000;

const DEAD = "/tmp/bend-cluster-dead.json";

const DEAD_KEEP = 60 * 60 * 1000;

const CACHE = "bench/cache";

const CACHE_DAYS = 7;

const MUX_OPTS = ["-o", "BatchMode=yes", "-o", "ControlMaster=auto",
  "-o", "ControlPath=/tmp/bend-cluster-mux", "-o", "ControlPersist=600"];

const OPTS = ["-o", "BatchMode=yes", "-o", "ConnectTimeout=8",
  "-o", "ProxyCommand=ssh " + MUX_OPTS.join(" ") + " -W %h:%p cluster"];

const DROP = new RegExp("Connection (closed|reset)|closed by remote host" +
  "|Broken pipe|kex_exchange_identification|mux_client|Result too large");

const MUX_DROP = new RegExp("Broken pipe|kex_exchange_identification" +
  "|mux_client|Result too large");

const NOISE = new RegExp(" (real|user|sys)\\s|resident set size|average " +
  "|page |swaps|block |messages |signals |context switches" +
  "|instructions retired|cycles elapsed|peak memory|^fnv: ");

let MUX: Promise<Exec> | null = null;

let node_held = "";

const IO_OPS = 1_000_000;

const IO_BAR = 1_000_000;

const IO_SRC = "#[halts]\nimport Base\n\nassert go:\n  forall +n: +U32\n"
  + "  IO(Unit)\n\ndef go(n):\n  match U32.is_eq(n, 0):\n"
  + "    case True{}:\n      IO.pure(Unit, Unit{})\n    case False{}:\n"
  + "      IO.bind(Unit, Unit, IO.write(\"x\"), u => go(U32.sub(n, 1)))\n"
  + "\nassert main:\n  IO(Unit)\n\ndef main():\n  go(" + String(IO_OPS)
  + ")\n";

const VIEW: string[] = [];

let live = process.stdout.isTTY === true;

let drawn = 0;

// Exec
// ====

export function exec_call(
  bin: string, args: string[], input?: string | Buffer): Promise<Exec> {
  return new Promise((ok, no) => {
    const kid = child.spawn(bin, args,
      { cwd: ROOT, stdio: ["pipe", "pipe", "pipe"] });
    let stdout = "";
    let stderr = "";
    let killed = false;
    const timer = setTimeout(() => {
      killed = true;
      kid.kill("SIGKILL");
    }, TIMEOUT);
    kid.stdout.on("data", (d: Buffer) => {
      stdout += d.toString();
    });
    kid.stderr.on("data", (d: Buffer) => {
      stderr += d.toString();
    });
    kid.stdin.on("error", () => {});
    kid.on("error", (e) => {
      clearTimeout(timer);
      no(Object.assign(e, { stdout, stderr, killed }));
    });
    kid.on("close", (code) => {
      clearTimeout(timer);
      if (code === 0) {
        ok({ stdout, stderr });
      } else {
        const err = new Error(bin + " exit " + String(code));
        no(Object.assign(err, { code: code ?? 1, stdout, stderr, killed }));
      }
    });
    kid.stdin.end(input);
  });
}

export async function exec_retry(
  bin: string, args: string[], what: string,
  input?: string | Buffer): Promise<Exec> {
  try {
    return await exec_call(bin, args, input);
  } catch (e) {
    const err = e as { code?: number | string; killed?: boolean;
      stderr?: string };
    if (err.killed === true || !MUX_DROP.test(err.stderr ?? "")) {
      throw e;
    }
    view_log("mux drop at " + what + " (see header): retrying once");
    await new Promise<void>((wake) => {
      setTimeout(wake, 300 + Math.random() * 1200);
    });
    return exec_call(bin, args, input);
  }
}

export function exec_infra(e: unknown): boolean {
  const err = e as { killed?: boolean; code?: number | string;
    stderr?: string };
  return err.killed !== true &&
    (err.code === 255 || DROP.test(err.stderr ?? ""));
}

export function exec_note(e: unknown): string {
  const err = e as { killed?: boolean; code?: number; stderr?: string;
    message?: string };
  const line = (err.stderr ?? "").trim().split("\n")
    .filter((it) => !NOISE.test(it))
    .map((it) => it.trim()).filter((it) => it !== "").pop();
  let text = line ?? "";
  if (err.killed === true) {
    text = "timeout after " + String(TIMEOUT / 1000) + "s (wedged?)";
  } else if (line === undefined) {
    text = err.code !== undefined
      ? "exit " + String(err.code)
      : String(err.message ?? e);
  }
  return text.slice(0, 160);
}

// Node
// ====

export function node_alias(node: number): string {
  return "cluster-" + node.toString(16).padStart(2, "0");
}

export function node_mux(): Promise<Exec> {
  MUX = MUX ?? exec_retry("ssh", [...MUX_OPTS, "cluster", "true"],
    "mux warmup");
  return MUX;
}

export function node_exec(
  node: number, script: string, input?: string | Buffer): Promise<Exec> {
  const alias = node_alias(node);
  return exec_retry("ssh", [...OPTS, alias, script], "ssh " + alias, input);
}

export function node_dead(): Set<number> {
  try {
    const was = JSON.parse(fs.readFileSync(DEAD, "utf8")) as
      Record<string, number>;
    const now = Date.now();
    return new Set(Object.entries(was)
      .filter(([, at]) => now - at < DEAD_KEEP)
      .map(([node]) => Number(node)));
  } catch {
    return new Set();
  }
}

export function node_bury(node: number): void {
  let was: Record<string, number> = {};
  try {
    was = JSON.parse(fs.readFileSync(DEAD, "utf8")) as
      Record<string, number>;
  } catch {}
  const now = Date.now();
  const next = Object.fromEntries(Object.entries(was)
    .filter(([, at]) => now - at < DEAD_KEEP));
  next[String(node)] = now;
  fs.writeFileSync(DEAD + "." + String(process.pid), JSON.stringify(next));
  fs.renameSync(DEAD + "." + String(process.pid), DEAD);
}

export function node_live(nodes: number[]): number[] {
  const dead = node_dead();
  const out = [...nodes];
  for (let i = 0; i < out.length; i++) {
    for (let j = out.length - 1; dead.has(out[i]) && j > i; j--) {
      if (!dead.has(out[j])) {
        out[i] = out[j];
        out[j] = nodes[i];
      }
    }
  }
  return out;
}

export function node_lock(range: Range): number {
  fs.mkdirSync(range.dir, { recursive: true });
  for (let slot = 0; slot < range.count; slot++) {
    const dir = path.join(range.dir, "slot" + String(slot));
    const file = path.join(dir, "lock.json");
    try {
      const lock = JSON.parse(fs.readFileSync(file, "utf8")) as
        { pid: number; time: number };
      const dead = ((): boolean => {
        try {
          process.kill(lock.pid, 0);
          return false;
        } catch {
          return true;
        }
      })();
      if (dead || Date.now() - lock.time > STALE) {
        fs.rmSync(dir, { recursive: true, force: true });
      }
    } catch {}
    try {
      fs.mkdirSync(dir);
      fs.writeFileSync(file, JSON.stringify({ pid: process.pid,
        time: Date.now() }));
      node_held = dir;
      process.on("exit", () => node_free());
      return range.base + range.size * slot;
    } catch {}
  }
  view_log("cluster out of capacity (" + String(range.count) +
    " slot(s) busy on " + range.dir + ")");
  process.exit(2);
}

export function node_free(): void {
  if (node_held !== "") {
    fs.rmSync(node_held, { recursive: true, force: true });
    node_held = "";
  }
}

export async function node_pool(nodes: number[], jobs: Job[]): Promise<void> {
  const queue = [...jobs];
  const spares = nodes.slice(jobs.length);
  await Promise.all(nodes.slice(0, jobs.length).map(async (first) => {
    let node = first;
    while (true) {
      const job = queue.shift();
      if (job === undefined) {
        return;
      }
      try {
        await job.run(node);
      } catch (e) {
        const spare = exec_infra(e) && job.hop < 2
          ? spares.shift()
          : undefined;
        if (spare === undefined) {
          job.fail(node, e);
        } else {
          view_log("failover " + job.key + ": node " + String(node) +
            " -> " + String(spare) + " (" + exec_note(e) + ")");
          node_bury(node);
          job.retry(node, e);
          job.hop++;
          queue.unshift(job);
          node = spare;
        }
      }
    }
  }));
}

// View
// ====

export function view_draw(): void {
  if (!live) {
    return;
  }
  const lines = [...VIEW, ""];
  const wide = Math.max(...lines.map((l) => l.length));
  if (lines.length + 1 > (process.stdout.rows ?? 0) ||
    wide >= (process.stdout.columns ?? 0)) {
    process.stdout.write(drawn > 0 ? "\x1b[" + String(drawn) + "A\x1b[0J" : "");
    live = false;
    drawn = 0;
    return;
  }
  const up = drawn > 0 ? "\x1b[" + String(drawn) + "A" : "";
  process.stdout.write(up + lines.map((l) => "\x1b[2K" + l + "\n").join("") +
    "\x1b[0J");
  drawn = lines.length;
}

export function view_set(lines: string[]): void {
  VIEW.length = 0;
  VIEW.push("# Runtime Benchmark", ...lines);
  view_draw();
}

export function view_log(text: string): void {
  if (live && drawn > 0) {
    process.stdout.write("\x1b[" + String(drawn) + "A\x1b[0J");
    drawn = 0;
  }
  process.stdout.write(text + "\n");
  view_draw();
}

export function view_table(rows: string[], heads: string[],
  cell: (row: string, i: number) => string, pre: string,
  wide: number): string[] {
  const w = Math.max(...rows.map((r) => r.length), "bench".length);
  const pad = (s: string, n: number): string => " " + s.padEnd(n) + " |";
  const out = [
    pre + "|" + pad("bench", w) + heads.map((h) => pad(h, wide)).join(""),
    pre + "|" + "-".repeat(w + 2) +
      heads.map(() => "|" + "-".repeat(wide + 2)).join("") + "|",
  ];
  for (const row of rows) {
    out.push(pre + "|" + pad(row, w) +
      heads.map((_, i) => pad(cell(row, i), wide)).join(""));
  }
  return out;
}

export function view_end(): void {
  if (!live) {
    for (const line of ["# Runtime Benchmark", ...VIEW.slice(1), ""]) {
      process.stdout.write(line + "\n");
    }
  }
  live = false;
  drawn = 0;
}

// Meas
// ====

export function meas_reads(stdout: string, stderr: string): Meas[] {
  const outs = stdout.split("\n").map((l) => l.trim())
    .filter((l) => /^\d+$/.test(l));
  const reals = [...stderr.matchAll(/(\d+[.,]\d+)\s+real/g)];
  const mems = [...stderr.matchAll(/(\d+)\s+maximum resident set size/g)];
  if (outs.length === 0 || reals.length !== outs.length ||
    mems.length !== outs.length) {
    return [];
  }
  return outs.map((out, i) => ({
    ms: Number(reals[i][1].replace(",", ".")) * 1000,
    rss: Number(mems[i][1]),
    output: out,
  }));
}

export function meas_show(got: Meas): string {
  const mb = Math.max(1, Math.round(got.rss / (1 << 20)));
  return (got.ms / 1000).toFixed(3).padStart(7) + "s " +
    String(mb).padStart(6) + "M";
}

// Pin
// ===

export function pin_read(): Map<string, Pin> {
  const pin = new Map<string, Pin>();
  let rows: string[] = [];
  try {
    rows = fs.readFileSync(PIN, "utf8").split("\n");
  } catch {}
  for (const line of rows) {
    const row = /^# \| (\S+)\s*\|(.*)\|$/.exec(line);
    if (row !== null && row[1] !== "bench" && !row[2].startsWith("--")) {
      const cells = row[2].split("|").map((c) => c.trim());
      pin.set(row[1], {
        secs: cells.slice(0, 3).map((c) => {
          const got = /([\d.]+)s/.exec(c);
          return got === null ? null : Number(got[1]);
        }),
        out: /^\d+$/.test(cells[3] ?? "") ? cells[3] : null,
      });
    }
  }
  return pin;
}

export function pin_stamp(cells: Cell[], pin: Map<string, Pin>): void {
  for (const cell of cells) {
    const want = pin.get(cell.base)?.out;
    if (cell.got !== null && want !== null && want !== undefined &&
      cell.got.output !== want) {
      cell_note(cell, "checksum " + cell.got.output + " != pinned " + want);
      cell.got = null;
    }
  }
}

export function pin_gate(cells: Cell[], pin: Map<string, Pin>): string[] {
  const fails: string[] = [];
  for (const cell of cells) {
    if (!cell.dead && cell.got === null) {
      fails.push(cell_key(cell) + ": " + cell.note);
    }
  }
  const bases = new Set(cells.map((c) => c.base));
  for (const name of pin.keys()) {
    if (!bases.has(name)) {
      fails.push(name + ": pin row without bench/" + name +
        ".bend -- a pinned bench may not vanish");
    }
  }
  if (bases.size === 0) {
    fails.push("bench/ holds no benchmark -- the grid measured nothing");
  }
  for (const cell of cells) {
    const row = pin.get(cell.base);
    if (row === undefined) {
      if (cell.mode === (HERE ? 1 : 0)) {
        fails.push(cell.base + ": no pin row -- a new bench needs a pin," +
          " and only Taelin writes one");
      }
      continue;
    }
    const want = row.secs[cell.mode];
    if (cell.got === null) {
      if (cell.dead && want !== null) {
        fails.push(cell_key(cell) + ": pinned " + want.toFixed(2) +
          "s, but the C backend now refuses the bench");
      }
      continue;
    }
    if (want === null) {
      fails.push(cell_key(cell) +
        ": the pin row says `-`, but the bench now runs");
      continue;
    }
    const secs = cell.got.ms / 1000;
    const drift = (secs - want) / want * 100;
    if (secs > want + GRACE) {
      fails.push(cell_key(cell) + ": " + secs.toFixed(2) + "s vs pinned " +
        want.toFixed(2) + "s (+" + drift.toFixed(0) +
        "% over the budget, past the " + GRACE.toFixed(2) +
        "s quantum) -- fix the regression");
    } else if (Math.abs(drift) >= DRIFT_NOTE &&
      Math.abs(secs - want) > GRACE) {
      view_log("drift " + cell_key(cell) + ": " + secs.toFixed(2) +
        "s vs pinned " + want.toFixed(2) + "s (" + (drift > 0 ? "+" : "") +
        drift.toFixed(0) + "%) -- ~10% is noise, accumulation is not");
    }
  }
  return fails;
}

// Cell
// ====

export function cell_grid(bases: string[]): Cell[] {
  return bases.flatMap((base) => MODES.map((_, mode) =>
    ({ base, mode, node: 0, dead: false, got: null, note: "" })));
}

export function cell_key(cell: Cell): string {
  return cell.base + " " + MODES[cell.mode];
}

export function cell_script(cell: Cell, work: string): string {
  const nt = cell.mode === 1 ? NODE_THREADS : "";
  const cc = MODE_CC[cell.mode];
  const key = "k=$( { cat b.c ; echo \"" + cc + "\" ; cc --version ; }" +
    " | md5 ) && c=$HOME/" + CACHE + "/$k";
  const build = key + " && { [ -x $c ] || { mkdir -p $HOME/" + CACHE +
    " && " + cc + " -o $c.tmp && mv $c.tmp $c ; } ; }";
  const run = "$c " + MODE_ARGS[cell.mode];
  const sweep = "pkill -f $HOME/" + CACHE + " >/dev/null 2>&1 ;" +
    " rm -rf bench/run-* ; find $HOME/" + CACHE + " -mtime +" +
    String(CACHE_DAYS) + " -delete 2>/dev/null ; ";
  const warm = " && w=$(" + run + " 2>/dev/null) && /usr/bin/time -l " +
    run + " > t.txt ; e=$? ; cat t.txt 2>/dev/null ;" +
    " [ $e -eq 0 ] && [ \"$w\" != \"$(cat t.txt)\" ] &&" +
    " { echo \"warm run answered [$w], timed run [$(cat t.txt)]\" >&2 ;" +
    " e=9 ; } ; cd ; rm -rf " + work + " ; exit $e";
  return sweep + "mkdir -p " + work + " && cd " + work +
    " && gzip -dc > b.c && " + nt + build + warm;
}

export async function cell_take(
  cell: Cell, node: number, work: string, csrc: string): Promise<void> {
  cell.node = node;
  const gz = zlib.gzipSync(csrc, { level: 6 });
  const got = HERE
    ? await exec_call("sh", ["-c", cell_script(cell, work)], gz)
    : await node_exec(node, cell_script(cell, work), gz);
  const runs = meas_reads(got.stdout, got.stderr);
  if (runs.length !== 1) {
    const seen = (got.stdout + got.stderr).trim().split("\n")
      .filter((l) => !NOISE.test(l)).join(" | ").slice(0, 160);
    throw new Error("unreadable run output: " + seen);
  }
  cell.got = runs[0];
}

export function cell_note(cell: Cell, text: string): void {
  cell.note = (cell.note === "" ? "" : cell.note + "; ") + text;
}

export function cell_fail(cell: Cell, node: number, e: unknown): void {
  cell.node = node;
  cell_note(cell, exec_note(e));
}

// Io
// ==

export function io_fnv(text: string): number {
  let h = 0x811c9dc5;
  for (const c of Buffer.from(text)) {
    h = Math.imul(h ^ c, 0x01000193) >>> 0;
  }
  return h >>> 0;
}

export async function io_cell(): Promise<Io> {
  const dir = fs.mkdtempSync("/tmp/bend-io-");
  try {
    fs.writeFileSync(path.join(dir, "io.bend"), IO_SRC);
    await exec_call(process.execPath, [MAIN, path.join(dir, "io.bend"),
      "--to", path.join(dir, "io.c")]);
    await exec_call("sh", ["-c", CC + " " + path.join(dir, "io.c")
      + " -lpthread -o " + path.join(dir, "io.bin")]);
    const t0 = performance.now();
    const got = await exec_call(path.join(dir, "io.bin"),
      ["--parallel", "off"]);
    const ms = performance.now() - t0;
    const ops = Math.round(IO_OPS / (ms / 1000));
    if (io_fnv(got.stdout) !== io_fnv("x".repeat(IO_OPS))) {
      return { ops, note: "the io loop answered the wrong stdout" };
    }
    if (ops < IO_BAR) {
      return { ops, note: "io throughput " + String(ops)
        + " ops/s under the " + String(IO_BAR) + " bar" };
    }
    return { ops, note: "" };
  } catch (e) {
    return { ops: 0, note: "io bench: " + exec_note(e) };
  } finally {
    fs.rmSync(dir, { recursive: true, force: true });
  }
}

// Grid
// ====

export function grid_bases(): string[] {
  return fs.readdirSync(BENCH).filter((f) => f.endsWith(".bend"))
    .map((f) => path.basename(f, ".bend")).sort();
}

export async function grid_gen(
  cells: Cell[], srcs: Map<string, string>, dir: string): Promise<void> {
  const bases = [...new Set(cells.map((c) => c.base))];
  await Promise.all(bases.map(async (base) => {
    try {
      const out = path.join(dir, base + ".c");
      await exec_call(process.execPath,
        [MAIN, path.join(BENCH, base + ".bend"), "--to", out]);
      srcs.set(base, fs.readFileSync(out, "utf8"));
    } catch (e) {
      const emsg = String((e as { stdout?: string }).stdout ?? "") +
        String((e as { stderr?: string }).stderr ?? "");
      const walled = emsg.includes("a flat of heap-owning elements");
      for (const cell of cells) {
        if (cell.base === base) {
          cell.dead = walled;
          cell.note = walled ? "" : "compile: " + exec_note(e);
        }
      }
    }
  }));
}

export function grid_view(cells: Cell[], foot: string): void {
  const bases = [...new Set(cells.map((c) => c.base))];
  const errs = cells.filter((c) => c.note !== "");
  const show = (base: string, mode: number): string => {
    const cell = cells.find((it) =>
      it.base === base && it.mode === mode) as Cell;
    if (cell.dead) {
      return "-";
    }
    if (cell.got !== null) {
      return meas_show(cell.got);
    }
    if (cell.note === "") {
      return "";
    }
    const mark = cell.note.includes("checksum") ? "WRONG" : "ERR";
    return mark + " [" + String(errs.indexOf(cell) + 1) + "]";
  };
  const where = (cell: Cell): string => HERE
    ? ""
    : " @ " + node_alias(cell.node) + " (node " + String(cell.node) + ")";
  const notes = errs.map((cell, i) => "[" + String(i + 1) + "] " +
    cell_key(cell) + where(cell) + ": " + cell.note);
  const cols = HERE ? [1, 2] : [0, 1, 2];
  const at = (base: string, i: number): string => show(base, cols[i]);
  view_set([...view_table(bases, cols.map((m) => MODES[m]), at, "", 16),
    ...notes, foot]);
}

export async function grid_run(): Promise<{ cells: Cell[]; io: Io;
  chks: Chk[] }> {
  const first = HERE ? 0 : node_lock(SLOTS);
  const work = "bench/run-" + Date.now().toString(36) + "-" +
    String(process.pid);
  const cells = cell_grid(grid_bases()).filter((cell) =>
    !HERE || cell.mode > 0);
  const nodes = HERE
    ? []
    : node_live(Array.from({ length: SLOTS.size }, (_, i) => first + i));
  const srcs = new Map<string, string>();
  const dir = fs.mkdtempSync("/tmp/bend-perf-");
  const start = performance.now();
  const foot = (): string => {
    const done = cells.filter((c) =>
      c.dead || c.got !== null || c.note !== "").length;
    const at = HERE
      ? " cells here"
      : " cells on nodes " + String(first) + "-" +
        String(first + SLOTS.size - 1);
    const secs = ((performance.now() - start) / 1000).toFixed(1);
    return String(done) + "/" + String(cells.length) + at + ", " + secs +
      "s, workdir ~/" + work;
  };
  grid_view(cells, foot());
  try {
    await Promise.all([HERE ? Promise.resolve() : node_mux(),
      grid_gen(cells, srcs, dir)]);
  } catch (e) {
    for (const cell of cells) {
      cell.note = "gen: " + exec_note(e);
    }
  }
  fs.rmSync(dir, { recursive: true, force: true });
  grid_view(cells, foot());
  const jobs: Job[] = cells.filter((cell) =>
    !cell.dead && cell.note === "").map((cell) => ({
    key: cell_key(cell),
    hop: 0,
    run: async (node: number): Promise<void> => {
      await cell_take(cell, node, work, srcs.get(cell.base) as string);
      grid_view(cells, foot());
    },
    fail: (node: number, e: unknown): void => {
      cell_fail(cell, node, e);
      grid_view(cells, foot());
    },
    retry: (node: number, e: unknown): void => {
      cell_note(cell, "left node " + String(node) + ": " + exec_note(e));
    },
  }));
  const grid = (async (): Promise<void> => {
    if (HERE) {
      for (const job of jobs) {
        await job.run(0).catch((e: unknown) => {
          job.fail(0, e);
        });
      }
    } else {
      await node_pool(nodes, jobs);
    }
  })();
  const local = (async (): Promise<{ io: Io; chks: Chk[] }> => {
    if (HERE) {
      await grid;
    }
    const io = await io_cell();
    const chks = await check_run();
    return { io, chks };
  })();
  const [, { io, chks }] = await Promise.all([grid, local]);
  pin_stamp(cells, pin_read());
  view_log("io " + String(io.ops) + " ops/s"
    + (io.note === "" ? "" : " -- " + io.note));
  grid_view(cells, foot());
  node_free();
  return { cells, io, chks };
}

export async function grid_gate(): Promise<string[]> {
  const { cells, io, chks } = await grid_run();
  const fails: string[] = [];
  if (io.note !== "") {
    fails.push(io.note);
  }
  return [...fails, ...pin_gate(cells, pin_read()), ...check_gate(chks)];
}

// Check
// =====

export function check_read(): Chk[] {
  const cells: Chk[] = [];
  let rows: string[] = [];
  try {
    rows = fs.readFileSync(CHECK_PIN, "utf8").split("\n");
  } catch {}
  for (const line of rows) {
    const row = /^# \| (\S+)\s*\| ([\d.]+)s\s*\|$/.exec(line);
    if (row !== null) {
      cells.push({ name: row[1], want: Number(row[2]), got: null, note: "" });
    }
  }
  return cells;
}

export async function check_take(cell: Chk, dir: string): Promise<void> {
  const m = /^([a-z]+)_(\d+)$/.exec(cell.name);
  if (m === null || !gen.BENCHES.includes(m[1] as gen.Bench)) {
    cell.note = "a pin row without a generator in bench/check/_gen_.ts";
    return;
  }
  const file = path.join(dir, cell.name + ".bend");
  fs.writeFileSync(file, gen.gen(m[1] as gen.Bench, Number(m[2])));
  let best = Infinity;
  for (let i = 0; i < CHECK_RUNS; i++) {
    const at = performance.now();
    try {
      const got = await exec_call(process.execPath, [MAIN, file]);
      if (got.stdout !== "") {
        cell.note = "the check printed: " +
          got.stdout.trim().split("\n")[0].slice(0, 120);
        return;
      }
    } catch (e) {
      cell.note = "check: " + exec_note(e);
      return;
    }
    best = Math.min(best, (performance.now() - at) / 1000);
  }
  cell.got = best;
}

export async function check_run(): Promise<Chk[]> {
  const cells = check_read();
  const dir = fs.mkdtempSync("/tmp/bend-check-");
  for (const cell of cells) {
    await check_take(cell, dir);
    const seen = cell.got === null
      ? cell.note
      : cell.got.toFixed(2) + "s, pinned " + cell.want.toFixed(2) + "s";
    view_log("check " + cell.name + ": " + seen);
  }
  fs.rmSync(dir, { recursive: true, force: true });
  return cells;
}

export function check_gate(cells: Chk[]): string[] {
  const fails: string[] = [];
  if (cells.length === 0) {
    fails.push("bench/check holds no pinned checker bench" +
      " -- check time measured nothing");
  }
  for (const cell of cells) {
    if (cell.got === null) {
      fails.push("check " + cell.name + ": " + cell.note);
      continue;
    }
    const drift = (cell.got - cell.want) / cell.want * 100;
    if (cell.got > cell.want + GRACE) {
      fails.push("check " + cell.name + ": " + cell.got.toFixed(2) +
        "s vs pinned " + cell.want.toFixed(2) + "s (+" + drift.toFixed(0) +
        "% over the budget, past the " + GRACE.toFixed(2) +
        "s quantum) -- fix the regression");
    } else if (Math.abs(drift) >= DRIFT_NOTE &&
      Math.abs(cell.got - cell.want) > GRACE) {
      view_log("drift check " + cell.name + ": " + cell.got.toFixed(2) +
        "s vs pinned " + cell.want.toFixed(2) + "s (" +
        (drift > 0 ? "+" : "") + drift.toFixed(0) +
        "%) -- ~10% is noise, accumulation is not");
    }
  }
  return fails;
}

// Here
// ====

export function here_mark(): void {
  const mark = path.join(os.tmpdir(), "bend-perf-here");
  fs.mkdirSync(mark, { recursive: true });
  fs.writeFileSync(path.join(mark, "pid"), String(process.pid));
  process.on("exit", () => {
    try {
      fs.rmSync(mark, { recursive: true, force: true });
    } catch {}
  });
}

// Main
// ====

if (process.argv[1] !== undefined &&
  path.resolve(process.argv[1]) === import.meta.filename) {
  if (process.argv.length > (HERE ? 3 : 2)) {
    process.stderr.write("Usage: bun check/perf.ts [--here]\n");
    process.exit(1);
  }
  if (HERE) {
    here_mark();
  }
  const fails = await grid_gate().catch((e: unknown) =>
    ["perf crashed: " + String((e as Error).stack ?? e)]);
  view_end();
  for (const line of fails) {
    console.log(line);
  }
  console.log(fails.length === 0 ? "PASSED" : "FAILED");
  process.exit(fails.length === 0 ? 0 : 1);
}
