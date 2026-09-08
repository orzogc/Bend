#!/usr/bin/env bun
// The two README images, drawn from the pins. This script measures
// NOTHING: every bar comes from a bench/*/_pin_apple_m4_max_.txt
// file, and those files hold only what gen_pins.ts measured on this
// machine, in this repo, at the stamped commit (see its header for
// the protocol). Repin first, then draw:
//
//   bun .devs/scripts/the record pins
//   bun .devs/scripts/gen_charts.ts
//
// The visual language is bend3's gen_charts.ts, unchanged:
// transparent background, mid-gray ink readable on GitHub light and
// dark, Bend in dark blue, rivals gray, large type, no axis clutter.
// Every panel is linear, scaled to its slowest bar; every bar
// prints its exact seconds. The ONE dashed idiom is a checker
// timeout: hatched, ">5min" above and "timeout" inside, drawn at
// twice the height of the panel's slowest finishing bar (so it
// caps, not crushes, the scale) -- never omitted, never drawn as
// finished, ranking slowest.
//
// docs/assets/checker.svg -- one panel per checker bench family,
// each system checking the SAME generated workload, panels ordered
// by Bend's lead, largest first.
//
// docs/assets/single_core.svg -- one panel per runtime bench:
// single-core Bend against its native twins (C, TypeScript, Lean),
// then the SAME Bend binary on all cores and on the GPU.

import * as fs from "node:fs";
import * as path from "node:path";
import * as os from "node:os";

// Constants
// =========

const ROOT = path.join(import.meta.dirname, "..", "..");
const DOCS = path.join(ROOT, "docs", "assets");
const RUNTIME_PIN = path.join(ROOT, "bench", "runtime", "_pin_",
  "apple_m4_max.txt");
const CHECKER_PIN = path.join(ROOT, "bench", "checker", "_pin_",
  "apple_m4_max.txt");
const CHECK_TIMEOUT = 300;
const CHECK_FAMILIES: Record<string, string> = {
  defs: "plain programs", proofs: "proof libraries",
  trees: "evaluation (smalltt trees)", generics: "generic instantiation",
};
const INK = "#818b98";
const BLUE = "#1a4f8a";
const FONT = "-apple-system, 'Helvetica Neue', Arial, sans-serif";

function say(text: string): void {
  process.stdout.write(text + "\n");
}

// Pins
// ====

type RunRow = { bench: string; seq: number; par: number; gpu: number;
  c: number; ts: number; lean: number };

type CheckRow = { family: string; n: number; lang: string; secs: number;
  over: boolean };

function pin_grid(file: string, heads: string[]): [string, string[]][] {
  const out: [string, string[]][] = [];
  for (const line of fs.readFileSync(file, "utf8").split("\n")) {
    const row = /^\| (\S+)\s*\|(.*)\|$/.exec(line);
    if (row === null) {
      continue;
    }
    const cells = row[2].split("|").map((c) => c.trim());
    if (row[1] === heads[0]) {
      if (cells.join(",") !== heads.slice(1).join(",")) {
        throw new Error(file + ": columns drifted from [" +
          heads.join(", ") + "] -- repin");
      }
      continue;
    }
    out.push([row[1], cells]);
  }
  if (out.length === 0) {
    throw new Error(file + ": no pin rows -- repin");
  }
  return out;
}

function pin_secs(cell: string): number {
  const got = /^(>?)([\d.]+)s/.exec(cell);
  if (got === null) {
    throw new Error("unreadable pin cell: " + cell);
  }
  return Number(got[2]);
}

function pin_runtime(): RunRow[] {
  return pin_grid(RUNTIME_PIN, ["bench", "SEQ-CPU", "PAR-CPU",
    "PAR-GPU", "C", "TS", "Lean"]).map(([bench, c]) => ({
    bench, seq: pin_secs(c[0]), par: pin_secs(c[1]), gpu: pin_secs(c[2]),
    c: pin_secs(c[3]), ts: pin_secs(c[4]), lean: pin_secs(c[5]),
  }));
}

function pin_checker(): CheckRow[] {
  const langs = ["isabelle", "agda", "lean", "rocq", "bend"];
  return pin_grid(CHECKER_PIN, ["bench", "Isabelle", "Agda", "Lean",
    "Rocq", "Bend"]).flatMap(([name, cells]) => {
    const cut = name.lastIndexOf("_");
    const family = name.slice(0, cut);
    const n = Number(name.slice(cut + 1));
    return langs.map((lang, i): CheckRow => ({
      family, n, lang, secs: pin_secs(cells[i]),
      over: cells[i].startsWith(">"),
    }));
  });
}

// Chart
// =====

function chart_write(file: string, width: number, height: number,
  body: string, s = 1): void {
  const svg = `<svg xmlns="http://www.w3.org/2000/svg" width="${width}" height="${height}" viewBox="0 0 ${width} ${height}">
<style>
  text { font-family: ${FONT}; fill: ${INK}; }
  .title { font-size: ${(15 * s).toFixed(1)}px; font-weight: 600; }
  .value { font-size: ${(12.5 * s).toFixed(1)}px; }
  .name  { font-size: ${(11.5 * s).toFixed(1)}px; }
  .sub   { font-size: ${(9.5 * s).toFixed(1)}px; }
  .note  { font-size: ${(19 * s).toFixed(1)}px; opacity: 0.9; }
</style>
${body}</svg>\n`;
  fs.mkdirSync(path.dirname(file), { recursive: true });
  fs.writeFileSync(file, svg);
  say("wrote " + file);
}

function chart_secs(s: number): string {
  return (s >= 100 ? s.toFixed(0) : s >= 10 ? s.toFixed(1) : s.toFixed(2)) + "s";
}

// Bar
// ===

type Bar = { name: string; secs: number; bend?: boolean; over?: boolean };
type Group = { title: string; bars: Bar[] };

const BAR_W = 54;
const BAR_GAP = 14;
const GROUP_GAP = 44;
const PLOT_H = 150;

function bar_groups(file: string, groups: Group[], note: string, opts: { cols?: number } = {}): void {
  const cols = opts.cols ?? groups.length;
  const rows = Math.ceil(groups.length / cols);
  const panelW = groups[0].bars.length * (BAR_W + BAR_GAP) - BAR_GAP;
  const pitch = panelW + GROUP_GAP;
  const width = cols * pitch - GROUP_GAP + 32;
  const s = width / 1200;
  const plotY = 74 * s;
  const nameLines = Math.max(...groups.flatMap((g) => g.bars.map((b) => b.name.split("\n").length)));
  const rowP = PLOT_H + (112 + (nameLines - 1) * 15) * s;
  const height = Math.round(rows * rowP + 46 * s);
  let body = "";
  body += `<pattern id="hatch" width="7" height="7" patternTransform="rotate(45)" patternUnits="userSpaceOnUse"><line x1="0" y1="0" x2="0" y2="7" stroke="${INK}" stroke-opacity="0.45" stroke-width="2.5"/></pattern>\n`;
  groups.forEach((group, g): void => {
    const x0 = 16 + (g % cols) * pitch;
    const y0 = Math.floor(g / cols) * rowP;
    const live = Math.max(...group.bars.filter((b) => b.over !== true)
      .map((b) => b.secs));
    const max = group.bars.some((b) => b.over === true) ? 2 * live : live;
    body += `<text x="${x0 + panelW / 2}" y="${(y0 + 22 * s).toFixed(1)}" text-anchor="middle" class="title">${group.title}</text>\n`;
    body += `<line x1="${x0}" y1="${y0 + plotY + PLOT_H}" x2="${x0 + panelW}" y2="${y0 + plotY + PLOT_H}" stroke="${INK}" stroke-opacity="0.3"/>\n`;
    group.bars.forEach((bar, i): void => {
      const bx = x0 + i * (BAR_W + BAR_GAP);
      const h = Math.round(Math.max(1,
        Math.min(bar.secs, max) / max * PLOT_H) * 10) / 10;
      const by = Math.round((y0 + plotY + PLOT_H - h) * 10) / 10;
      const r = Math.min(5, h / 2);
      const shape = `M ${bx} ${by + h} L ${bx} ${by + r} Q ${bx} ${by} ${bx + r} ${by} L ${bx + BAR_W - r} ${by} Q ${bx + BAR_W} ${by} ${bx + BAR_W} ${by + r} L ${bx + BAR_W} ${by + h} Z`;
      const hue = bar.bend === true ? BLUE : null;
      body += bar.over === true
        ? `<path d="${shape}" fill="url(#hatch)" stroke="${INK}" stroke-opacity="0.5" stroke-dasharray="4 3"/>\n`
        : `<path d="${shape}" fill="${hue ?? INK}"${hue === null ? ` fill-opacity="0.4"` : ""}/>\n`;
      body += `<text x="${bx + BAR_W / 2}" y="${(by - 7 * s).toFixed(1)}" text-anchor="middle" class="value"${hue === null ? "" : ` style="fill: ${hue}"`}>${bar.over === true ? "&gt;" + String(CHECK_TIMEOUT / 60) + "min" : chart_secs(bar.secs)}</text>\n`;
      if (bar.over === true) body += `<text x="${bx + BAR_W / 2}" y="${(by + 17 * s).toFixed(1)}" text-anchor="middle" class="name">timeout</text>\n`;
      bar.name.split("\n").forEach((line, ln): void => {
        body += `<text x="${bx + BAR_W / 2}" y="${(y0 + plotY + PLOT_H + (20 + ln * 15) * s).toFixed(1)}" text-anchor="middle" class="${ln === 0 ? "name" : "sub"}"${hue === null ? "" : ` style="fill: ${hue}"`}>${line}</text>\n`;
      });
    });
  });
  body += `<text x="${width / 2}" y="${(height - 16 * s).toFixed(1)}" text-anchor="middle" class="note">${note}</text>\n`;
  chart_write(file, width, height, body, s);
}

// Charts
// ======

const MACHINE = '<tspan font-weight="bold">Apple M4 Max</tspan>';

// Composition: every bench, a 4-wide grid, best to worst by Bend's
// combined advantage -- (single-core bend/best-twin) x (GPU/PAR-CPU).
function charts_order(rows: RunRow[]): RunRow[] {
  const score = (r: RunRow): number =>
    (r.seq / Math.min(r.c, r.ts, r.lean)) * (r.gpu / r.par);
  return [...rows].sort((a, b) => score(a) - score(b));
}

function charts_checker(rows: CheckRow[]): void {
  const LANGS = ["isabelle", "agda", "lean", "rocq"];
  const NAMES = ["Isabelle", "Agda", "Lean", "Rocq"];
  const groups = Object.keys(CHECK_FAMILIES).map((family): Group => {
    const mine = rows.filter((r) => r.family === family);
    const bend = mine.find((r) => r.lang === "bend");
    if (bend === undefined) throw new Error(family + ": no bend cell");
    const bars = LANGS.map((lang, i): Bar => {
      const r = mine.find((it) => it.lang === lang);
      if (r === undefined) throw new Error(family + "/" + lang + ": missing");
      return { name: NAMES[i], secs: r.over ? CHECK_TIMEOUT : r.secs,
        over: r.over };
    });
    bars.push({ name: "Bend", secs: bend.secs, bend: true });
    return { title: CHECK_FAMILIES[family] + " · n=" + String(bend.n), bars };
  });
  const lead = (g: Group): number => {
    const bd = g.bars.find((b) => b.name === "Bend");
    if (bd === undefined) throw new Error(g.title + ": no bend bar");
    return Math.min(...g.bars.filter((b) => b.name !== "Bend").map((b) => b.secs)) / bd.secs;
  };
  groups.sort((a, b) => lead(b) - lead(a));
  bar_groups(path.join(DOCS, "checker.svg"), groups,
    "cold check of one file, lower is better · " + MACHINE);
}

function charts_single_core(rows: RunRow[]): void {
  let nt = 1;
  while (nt * 2 <= os.cpus().length && nt < 256) {
    nt *= 2;
  }
  const single = charts_order(rows).map((row): Group => ({
    title: row.bench,
    bars: [
      { name: "TypeScript", secs: row.ts },
      { name: "Lean", secs: row.lean },
      { name: "C", secs: row.c },
      { name: "Bend\n1-Core", secs: row.seq, bend: true },
      { name: "Bend\n" + String(nt) + "-Cores", secs: row.par,
        bend: true },
      { name: "Bend\nGPU", secs: row.gpu, bend: true },
    ],
  }));
  bar_groups(path.join(DOCS, "single_core.svg"), single,
    "lower is better · " + MACHINE, { cols: 4 });
}

// Main
// ====

charts_checker(pin_checker());
charts_single_core(pin_runtime());
