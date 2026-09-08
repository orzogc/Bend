#!/usr/bin/env bun
// Runs the benchmarks on the cluster: every runtime bench in each of its
// three modes on its own mini (48 cells), plus the five checker benches,
// and draws one fixed screen with each measure beside its ratio to the
// pin. A cell passes at 1.15x or under; --pin writes the measures as the
// new pins; --gate prints only the verdict.

import * as child from "node:child_process";
import * as fs from "node:fs";
import * as path from "node:path";

import * as lib from "./_lib";

// Types
// =====

type Cell = {
  bench: string;
  mode: number;
  secs: number | null;
  mem: number | null;
  comp: number | null;
  out: string;
  note: string;
};

type Chk = { bench: string; secs: number | null; note: string };

type Pin = { comp: number; secs: number[]; mems: number[]; out: string };

// Constants
// =========

const PIN = process.argv.includes("--pin");

const RUNTIME = path.join(lib.ROOT, "bench", "runtime");

const CHECKER = path.join(lib.ROOT, "bench", "checker");

const HW = "apple_m4";

const MODES = ["SEQ-CPU", "PAR-CPU", "PAR-GPU"];

const FLAGS = ["--parallel off", "--gpu off", "--gpu on"];

const SLACK = 1.15;

const MARK = "@@B4";

const CLOCK = "perl -MTime::HiRes=time -e 'print time'";

const VIEW: string[] = [];

let drawn = 0;

// Fmt
// ===

function fmt_secs(x: number): string {
  return x < 10 ? x.toFixed(3) + "s" : x < 100 ? x.toFixed(2) + "s"
    : x < 1000 ? x.toFixed(1) + "s" : String(Math.round(x)).padStart(5) + "s";
}

function fmt_mem(mb: number): string {
  return (mb < 10000 ? String(Math.round(mb)).padStart(5) + "M"
    : (mb / 1024).toFixed(2) + "G");
}

function fmt_ratio(got: number, pin: number | undefined): string {
  if (pin === undefined || pin === 0) {
    return "    -";
  }
  const x = got / pin;
  return (x < 10 ? x.toFixed(2) : x < 100 ? x.toFixed(1)
    : String(Math.round(x))).padStart(4) + "x";
}

function fmt_cell(got: number | null, pin: number | undefined,
  fmt: (x: number) => string, note: string): string {
  if (got === null) {
    return note === "" ? "" : "err";
  }
  return fmt(got).padStart(6) + "   " + fmt_ratio(got, pin);
}

// View
// ====

function view_rows(name: string, heads: string[], rows: string[][],
  spaced: boolean): string[] {
  const bar = "-".repeat(13);
  const cbar = "-".repeat(16);
  const line = spaced
    ? "| " + bar + " |" + heads.map(() => " " + cbar + " |").join("")
    : "|" + bar + "--|" + heads.map(() => cbar + "--|").join("");
  return ["| " + "bench".padEnd(13) + " |" + heads.map((h) =>
    " " + h.padEnd(16) + " |").join(""), line, ...rows.map((r) =>
    "| " + r[0].padEnd(13) + " |" + r.slice(1).map((c) =>
      " " + c.padEnd(16) + " |").join(""))];
}

function view_draw(cells: Cell[], chks: Chk[], pins: Map<string, Pin>,
  cpins: Map<string, number>, notes: string[]): void {
  const heads = ["COMPILER TIME", ...MODES.flatMap((m) =>
    [m + " TIME", m + " SPACE"])];
  const benches = [...new Set(cells.map((c) => c.bench))];
  const rows = benches.map((b) => {
    const cs = MODES.map((_, m) => cells.find((c) =>
      c.bench === b && c.mode === m) as Cell);
    const comps = cs.map((c) => c.comp).filter((x) => x !== null);
    const comp = comps.length === 0 ? null
      : [...comps].sort((x, y) => x - y)[Math.floor(comps.length / 2)];
    const pin = pins.get(b);
    return [b, fmt_cell(comp, pin?.comp, fmt_secs, ""), ...cs.flatMap((c) =>
      [fmt_cell(c.secs, pin?.secs[c.mode], fmt_secs, c.note),
        fmt_cell(c.mem, pin?.mems[c.mode], fmt_mem, c.note)])];
  });
  const crow = chks.map((c) => [c.bench,
    fmt_cell(c.secs, cpins.get(c.bench), fmt_secs, c.note)]);
  const lines = [...view_rows("bench", heads, rows, false), "",
    ...view_rows("bench", ["CHECKER TIME"], crow, true), ...notes.length === 0
    ? [] : ["", ...notes]];
  VIEW.splice(0, VIEW.length, ...lines);
  if (process.stdout.isTTY === true && !lib.GATE) {
    const up = drawn > 0 ? "\x1b[" + String(drawn) + "A" : "";
    process.stdout.write(up + lines.map((l) => "\x1b[2K" + l + "\n").join(""));
    drawn = lines.length;
  }
}

// Pin
// ===

function pin_read(): [Map<string, Pin>, Map<string, number>] {
  const pins = new Map<string, Pin>();
  const cpins = new Map<string, number>();
  const rows = (file: string): [string, string[]][] => {
    try {
      return fs.readFileSync(file, "utf8").split("\n").flatMap((line) => {
        const row = /^\| (\S+)\s*\|(.*)\|$/.exec(line);
        return row === null || row[1] === "bench" || row[2].startsWith("-")
          ? [] : [[row[1], row[2].split("|").map((c) => c.trim())]];
      });
    } catch {
      return [];
    }
  };
  const num = (c: string): number => Number(/[\d.]+/.exec(c)?.[0] ?? 0);
  for (const [b, c] of rows(path.join(RUNTIME, "_pin_", HW + ".txt"))) {
    const cell = (i: number): number[] => c[i].split(/\s+/).map(num);
    pins.set(b, { comp: num(c[0]), secs: [1, 2, 3].map((i) => cell(i)[0]),
      mems: [1, 2, 3].map((i) => cell(i)[1]), out: c[4] });
  }
  for (const [b, c] of rows(path.join(CHECKER, "_pin_", HW + ".txt"))) {
    cpins.set(b, num(c[0]));
  }
  return [pins, cpins];
}

function pin_write(cells: Cell[], chks: Chk[]): void {
  const benches = [...new Set(cells.map((c) => c.bench))];
  const w = Math.max(10, ...benches.map((b) => b.length),
    ...chks.map((c) => c.bench.length));
  const bar = (n: number): string => "-".repeat(n + 2);
  const rows = benches.map((b) => {
    const cs = MODES.map((_, m) => cells.find((c) =>
      c.bench === b && c.mode === m) as Cell);
    const comps = cs.map((c) => c.comp ?? 0).sort((x, y) => x - y);
    return "| " + b.padEnd(w) + " | " + fmt_secs(comps[1]).padStart(8)
      + " |" + cs.map((c) => " " + fmt_secs(c.secs ?? 0).padStart(8) + " "
        + fmt_mem(c.mem ?? 0).padStart(7) + " |").join("") + " "
      + cs[0].out.padEnd(10) + " |";
  });
  fs.writeFileSync(path.join(RUNTIME, "_pin_", HW + ".txt"), [
    "| " + "bench".padEnd(w) + " | COMPILER |" + MODES.map((m) =>
      " " + m.padEnd(16) + " |").join("") + " OUTPUT     |",
    "|" + bar(w) + "|" + bar(8) + "|" + MODES.map(() => bar(16) + "|").join("")
      + bar(10) + "|", ...rows, ""].join("\n"));
  fs.writeFileSync(path.join(CHECKER, "_pin_", HW + ".txt"), [
    "| " + "bench".padEnd(w) + " | CHECKER  |", "|" + bar(w) + "|" + bar(8)
      + "|", ...chks.map((c) => "| " + c.bench.padEnd(w) + " | "
      + fmt_secs(c.secs ?? 0).padStart(8) + " |"), ""].join("\n"));
}

// Cell
// ====

function cell_pack(dir: string): Buffer {
  const tmp = fs.mkdtempSync("/tmp/bend-perf-");
  fs.cpSync(path.join(lib.ROOT, "bend2"), path.join(tmp, "bend2"),
    { recursive: true, filter: (p) =>
      !p.includes("/conf") && !p.includes("/docs") });
  fs.copyFileSync(path.join(dir, "main.bend"), path.join(tmp, "main.bend"));
  const tar = child.spawnSync("tar", ["-czf", "-", "-C", tmp, "."],
    { maxBuffer: 1 << 28 });
  fs.rmSync(tmp, { recursive: true, force: true });
  return tar.stdout;
}

function cell_script(tag: string, run: string): string {
  return `d=$HOME/bend-perf/${tag}; rm -rf $d; mkdir -p $d; cd $d; tar -xzf -;`
    + ` t0=$(${CLOCK}); ${lib.BUN} bend2/main.ts main.bend -o main > build.txt`
    + ` 2>&1; b=$?; t1=$(${CLOCK}); echo "${MARK} built $b $t0 $t1"; cat`
    + ` build.txt; if [ $b = 0 ]; then ./main ${run} > /dev/null 2>&1;`
    + ` /usr/bin/time -l ./main ${run} > out.txt 2> time.txt; echo "${MARK}`
    + ` ran $?"; cat out.txt; echo "${MARK} time"; cat time.txt; fi;`
    + ` cd; rm -rf $d`;
}

function cell_note(out: string): string {
  const line = out.trim().split("\n").filter((l) => !l.startsWith(MARK)
    && !/ real | maximum resident|^\s*\d+\s+\w/.test(l)).pop() ?? "";
  return line.slice(0, 100);
}

async function cell_run(c: Cell, node: number): Promise<void> {
  const got = await lib.ssh(node, cell_script(c.bench + "-" + String(c.mode),
    FLAGS[c.mode]), cell_pack(path.join(RUNTIME, c.bench)), 20 * 60 * 1000);
  const built = new RegExp("^" + MARK + " built (\\d+) ([\\d.]+) ([\\d.]+)$",
    "m")
    .exec(got.out);
  const ran = new RegExp("^" + MARK + " ran (\\d+)$", "m").exec(got.out);
  if (built === null) {
    throw new Error("node");
  }
  c.comp = Number(built[3]) - Number(built[2]);
  if (built[1] !== "0" || ran === null || ran[1] !== "0") {
    c.note = c.bench + " " + MODES[c.mode] + ": " + (built[1] !== "0"
      ? "build: " : "exit " + String(ran?.[1] ?? "?") + ": ")
      + cell_note(got.out);
    return;
  }
  const tail = got.out.split(new RegExp("^" + MARK + " ran \\d+\n", "m"))[1];
  const [body, time] = (tail ?? "").split(MARK + " time\n");
  const real = /([\d.,]+)\s+real/.exec(time ?? "");
  const rss = /(\d+)\s+maximum resident set size/.exec(time ?? "");
  c.out = body.split("\n").map((l) => l.trim()).filter((l) => l !== "")
    .pop() ?? "";
  c.secs = real === null ? null : Number(real[1].replace(",", "."));
  c.mem = rss === null ? null : Number(rss[1]) / (1 << 20);
  if (c.secs === null || c.mem === null) {
    c.note = c.bench + " " + MODES[c.mode] + ": unreadable time output";
  }
}

// Chk
// ===

async function chk_run(c: Chk, node: number): Promise<void> {
  const script = `d=$HOME/bend-perf/chk-${c.bench}; rm -rf $d; mkdir -p $d;`
    + ` cd $d; tar -xzf -; for i in 1 2 3; do t0=$(${CLOCK}); ${lib.BUN}`
    + ` bend2/main.ts main.bend > out.txt 2>&1; e=$?; t1=$(${CLOCK}); echo`
    + ` "${MARK} check $e $t0 $t1"; cat out.txt; done; cd; rm -rf $d`;
  const got = await lib.ssh(node, script, cell_pack(path.join(CHECKER,
    c.bench)), 20 * 60 * 1000);
  const runs = [...got.out.matchAll(new RegExp("^" + MARK
    + " check (\\d+) ([\\d.]+) ([\\d.]+)$", "gm"))];
  if (runs.length === 0) {
    throw new Error("node");
  }
  if (runs.some((r) => r[1] !== "0") || !got.out.includes("All terms check.")) {
    c.note = c.bench + ": " + cell_note(got.out);
    return;
  }
  c.secs = Math.min(...runs.map((r) => Number(r[3]) - Number(r[2])));
}

// Main
// ====

if (import.meta.main) {
  const benches = fs.readdirSync(RUNTIME).filter((f) => !f.startsWith("_"))
    .sort();
  const cells: Cell[] = benches.flatMap((bench) => MODES.map((_, mode) =>
    ({ bench, mode, secs: null, mem: null, comp: null, out: "", note: "" })));
  const chks: Chk[] = fs.readdirSync(CHECKER).filter((f) => !f.startsWith("_"))
    .sort().map((bench) => ({ bench, secs: null, note: "" }));
  const [pins, cpins] = PIN
    ? [new Map<string, Pin>(), new Map<string, number>()]
    : pin_read();
  const notes = (): string[] => [...cells, ...chks].map((c) => c.note)
    .filter((n) => n !== "");
  const draw = (): void => view_draw(cells, chks, pins, cpins, notes());
  draw();
  const nodes = await lib.node_lock();
  await lib.node_pool(nodes, [...cells.map((c) => async (node: number) => {
    await cell_run(c, node);
    draw();
  }), ...chks.map((c) => async (node: number) => {
    await chk_run(c, node);
    draw();
  })]);
  if (PIN) {
    pin_write(cells, chks);
  }
  const fits = (got: number | null, pin: number | undefined): boolean =>
    got !== null && (PIN || pin !== undefined && got <= pin * SLACK);
  let pass = 0;
  for (const c of cells) {
    const pin = pins.get(c.bench);
    if (!PIN && pin !== undefined && c.out !== pin.out && c.secs !== null) {
      c.note = c.bench + " " + MODES[c.mode] + ": output " + c.out
        + " differs from the pinned " + pin.out;
      c.secs = null;
    }
    pass += Number(fits(c.secs, pin?.secs[c.mode]))
      + Number(fits(c.mem, pin?.mems[c.mode]));
    if (c.mode === 0) {
      const comps = cells.filter((o) => o.bench === c.bench).map((o) => o.comp)
        .filter((x) => x !== null).sort((x, y) => x - y);
      pass += Number(fits(comps[Math.floor(comps.length / 2)] ?? null,
        pin?.comp));
    }
  }
  for (const c of chks) {
    pass += Number(fits(c.secs, cpins.get(c.bench)));
  }
  draw();
  if (!lib.GATE && process.stdout.isTTY !== true) {
    console.log(VIEW.join("\n"));
  }
  lib.verdict(pass, cells.length * 2 + benches.length + chks.length);
}
