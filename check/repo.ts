#!/usr/bin/env bun

import * as child from "node:child_process";
import * as fs from "node:fs";
import * as path from "node:path";

// Types
// =====

export type Flag = { line: number; rule: string; text: string };

export type FlagFn = (line: number, rule: string, text: string) => void;

export type Mask =
  { raw: string[]; code: string[]; note: string[]; open: boolean[] };

export type Frame = { kind: string; quote: string; depth: number };

export type Part = { name: string; src: string; line: number };

// Constants
// =========

const ROOT = path.join(import.meta.dirname, "..");

const BEND = "src/bend.ts";

const CAPS: [string, number][] = [
  ["src/bend.ts", 87689],
  ["src/base.bend", 16000],
  ["BEND_IN_12K.txt", 12000],
];

const CORE_CAP = 40000;

const MARK_COMP = "// Comp\n// ====\n";

const MARK_RUNC = "// RuntimeC\n// ========\n";

const MARK_RUNJ = "// RuntimeJs\n// =========\n";

const MARK_MAIN = "// Main\n// ====\n";

const FENCE_OPEN = "String.raw`\n";

const FENCE_SHUT = "\n`.slice(1);";

const CHECKS: string[] = [
  "check/_ALL_.ts",
  "check/perf.ts",
  "check/repo.ts",
  "check/test.ts",
];

const EFFS: string[] = fs.readdirSync(path.join(ROOT, "src", "effs"))
  .sort().map((f) => "src/effs/" + f);

const STYLED: string[] = ["src/base.bend", ...EFFS, ...CHECKS];

const BENDED: [string, boolean, boolean][] = [
  ["comp", true, false],
  ["runc", false, true],
  ["runj", true, false],
  ["main", true, false],
];

const LAYOUT: string[] = ["src/base.bend", ...EFFS, ...CHECKS];

const PARTS: string[] = ["Types", "Claims", "Proofs"];

const WIDTH = 80;

const SHOWN = 3;

// Ttok
// ====

export function ttok_text(text: string): number {
  const got = child.execFileSync("ttok", [], {
    input: text,
    encoding: "utf8",
  });
  const n = Number(got.trim());
  if (!Number.isFinite(n)) {
    const seen = got.slice(0, 80);
    throw new Error("ttok answered no number: " + seen);
  }
  return n;
}

export function ttok_read(file: string): number {
  return ttok_text(fs.readFileSync(path.join(ROOT, file), "utf8"));
}

// Bend
// ====

export function bend_parts(): Part[] {
  const src = fs.readFileSync(path.join(ROOT, BEND), "utf8");
  const line = (at: number): number => src.slice(0, at).split("\n").length;
  const cut = (mark: string, from: number): number => {
    const found = src.indexOf(mark, from);
    if (found < 0) {
      throw new Error(BEND + " lost its " + mark.split("\n")[0] + " mark");
    }
    return found;
  };
  const comp = cut(MARK_COMP, 0);
  const runc = cut(MARK_RUNC, comp);
  const runj = cut(MARK_RUNJ, runc);
  const main = cut(MARK_MAIN, runj);
  const fence = (beg: number): [string, number] => {
    const open = cut(FENCE_OPEN, beg) + FENCE_OPEN.length;
    const shut = cut(FENCE_SHUT, open);
    return [src.slice(open, shut + 1), line(open)];
  };
  const [ctext, cline] = fence(runc);
  const [jtext, jline] = fence(runj);
  return [
    { name: "comp", src: src.slice(comp, runc), line: line(comp) },
    { name: "runc", src: ctext, line: cline },
    { name: "runj", src: jtext, line: jline },
    { name: "main", src: src.slice(main), line: line(main) },
  ];
}

// Caps
// ====

export function caps_gate(): string[] {
  const fails: string[] = [];
  for (const [file, cap] of CAPS) {
    const n = ttok_read(file);
    if (n <= cap) {
      console.log("PASS " + file + " " + String(n) + " <= " + String(cap) +
        " ttok");
    } else {
      fails.push(file + ": " + String(n) + " ttok over the " + String(cap) +
        " cap");
    }
  }
  const bend = fs.readFileSync(path.join(ROOT, BEND), "utf8");
  const at = bend.indexOf(MARK_COMP);
  if (at < 0) {
    fails.push(BEND + " lost its " + MARK_COMP.split("\n")[0] + " mark");
    return fails;
  }
  const n = ttok_text(bend.slice(0, at));
  if (n <= CORE_CAP) {
    console.log("PASS " + BEND + " core " + String(n) + " <= " +
      String(CORE_CAP) + " ttok");
  } else {
    fails.push(BEND + " core: " + String(n) + " ttok over the " +
      String(CORE_CAP) + " cap");
  }
  return fails;
}

// Mask
// ====

export function mask_read(src: string, lead: string = "//"): Mask {
  const raw = src.split("\n");
  const code: string[] = [];
  const note: string[] = [];
  const open: boolean[] = [];
  const stack: Frame[] = [{ kind: "code", quote: "", depth: 0 }];
  for (const line of raw) {
    const top = stack[stack.length - 1];
    open.push(top.kind === "str" || top.kind === "tmpl");
    let out = "";
    let com = "";
    let i = 0;
    while (i < line.length) {
      const f = stack[stack.length - 1];
      const c = line[i];
      const d = line.slice(i, i + 2);
      if (f.kind === "str" || f.kind === "tmpl") {
        if (c === "\\") {
          out += "  ";
          i += 2;
          continue;
        }
        if (f.kind === "tmpl" && d === "${") {
          stack.push({ kind: "code", quote: "", depth: 0 });
          out += "  ";
          i += 2;
          continue;
        }
        if (c === f.quote) {
          stack.pop();
        }
        out += " ";
        i += 1;
        continue;
      }
      if (f.kind === "blk") {
        if (d === "*/") {
          stack.pop();
          com += d;
          i += 2;
          continue;
        }
        com += c;
        i += 1;
        continue;
      }
      if (line.slice(i, i + lead.length) === lead) {
        com += line.slice(i);
        i = line.length;
        continue;
      }
      if (lead === "//" && d === "/*") {
        stack.push({ kind: "blk", quote: "", depth: 0 });
        com += d;
        i += 2;
        continue;
      }
      if (c === "\"" || c === "'") {
        stack.push({ kind: "str", quote: c, depth: 0 });
        out += " ";
        i += 1;
        continue;
      }
      if (c === "`") {
        stack.push({ kind: "tmpl", quote: "`", depth: 0 });
        out += " ";
        i += 1;
        continue;
      }
      if (c === "{") {
        f.depth += 1;
      }
      if (c === "}") {
        if (f.depth === 0 && stack.length > 1) {
          stack.pop();
          out += " ";
          i += 1;
          continue;
        }
        f.depth -= 1;
      }
      out += c;
      i += 1;
    }
    code.push(out);
    note.push(com);
  }
  return { raw, code, note, open };
}

// Rule
// ====

function rule_notes(m: Mask, flag: FlagFn, lead: string,
  head: boolean): void {
  const word = new RegExp("^\\s*" + lead + " ?[A-Za-z0-9_.]+$");
  const bars = new RegExp("^\\s*" + lead + " ?[=-]{2,}$");
  const adth = new RegExp("^\\s*" + lead + " ?[A-Za-z0-9_.]+ ::=$");
  const adtr = new RegExp("^\\s*" + lead + " ?\\s*\\| .+$");
  const use = new RegExp("^//! use .+$");
  let skip = 0;
  while (head && skip < m.raw.length && m.raw[skip].startsWith(lead)) {
    skip += 1;
  }
  for (let i = skip; i < m.note.length; i += 1) {
    const line = m.raw[i];
    let here = m.note[i];
    if (here === "" && line.trim().startsWith(lead)) {
      here = line.trim();
    }
    if (here === "" || use.test(line)) {
      continue;
    }
    const prev = m.raw[i - 1] ?? "";
    const next = m.raw[i + 1] ?? "";
    const head = word.test(line) && bars.test(next);
    const tail = bars.test(line) && word.test(prev);
    const adt = (adth.test(line) && adtr.test(next)) ||
      (adtr.test(line) && (adth.test(prev) || adtr.test(prev)));
    if (!head && !tail && !adt) {
      flag(i, "comment", here.trim());
    }
  }
}

function rule_layout(m: Mask, flag: FlagFn): void {
  let last = 0;
  for (let i = 0; i < m.raw.length; i += 1) {
    const line = m.raw[i];
    const cd = m.code[i];
    if (line.length > WIDTH) {
      flag(i, "width", String(line.length) + " columns");
    }
    if (/\s$/.test(line)) {
      flag(i, "space", "trailing space");
    }
    if (m.open[i] || line.trim() === "") {
      continue;
    }
    const step = line.length - line.trimStart().length;
    if (step % 2 !== 0) {
      flag(i, "indent", "column alignment: " + String(step) + " spaces");
    }
    if (step - last > 2) {
      flag(i, "indent", String(step - last) + " spaces in one break");
    }
    last = step;
    if (/^#define\s+WL_/.test(cd)) {
      continue;
    }
    const block = /(\)|=>)\s*\{.*\S.*\}/.test(cd) ||
      /\b(else|do|try)\s*\{.*\S.*\}/.test(cd);
    const bare = /^\s*(if|for|while)\s*\(.*\)\s*[A-Za-z_}]/.test(cd) &&
      !cd.includes("{");
    if (block || bare) {
      flag(i, "block", cd.trim());
    }
    let depth = 0;
    let ends = 0;
    for (const c of cd) {
      if (c === "(" || c === "{") {
        depth += 1;
      }
      if (c === ")" || c === "}") {
        depth -= 1;
      }
      if (c === ";" && depth === 0) {
        ends += 1;
      }
    }
    if (ends > 1) {
      flag(i, "statements", cd.trim());
    }
  }
}

function rule_exprs(m: Mask, flag: FlagFn): void {
  for (let i = 0; i < m.code.length; i += 1) {
    const cd = m.code[i];
    if (/\(\s*[A-Za-z_]\w*\(\s*\)\s*,/.test(cd)) {
      flag(i, "comma", cd.trim());
    }
    const ask = cd.replace(/\?\./g, "").replace(/\?\?/g, "")
      .replace(/\?:/g, "");
    if ((ask.split("?").length - 1) > 1 && (ask.split(":").length - 1) > 1) {
      flag(i, "ternary", cd.trim());
    }
    const mac = cd.match(/^#define\s+(\w+)/);
    const run = /\b(if|for|while|goto|return|break|continue)\b/.test(cd);
    if (mac !== null && run && !mac[1].startsWith("WL_")) {
      flag(i, "macro", cd.trim());
    }
  }
}

function rule_files(m: Mask, flag: FlagFn, cee: boolean): void {
  const word = new RegExp("^// ?([A-Za-z0-9_.]+)$");
  const bars = new RegExp("^// ?(=+|-+)$");
  const decl =
    /^(?:export )?(?:async )?(function|type|const|let|var)\s+([A-Za-z0-9_$]+)/;
  const attr = /__attribute__\(\(\w+\)\)\s*/;
  const cdef = /^[A-Za-z_][\w<>,*\s]*?[\s*]([A-Za-z_]\w*)\s*\(/;
  let sec = "";
  let sub = "";
  for (let i = 0; i < m.raw.length; i += 1) {
    if (m.open[i]) {
      continue;
    }
    const mark = word.exec(m.raw[i]);
    const line = bars.exec(m.raw[i + 1] ?? "");
    if (mark !== null && line !== null) {
      if (line[1].startsWith("=")) {
        sec = mark[1];
        sub = "";
      } else {
        sub = mark[1];
      }
      continue;
    }
    const cd = cee ? m.code[i].replace(attr, "") : m.code[i];
    if (cee && (cd.startsWith("#") || cd.startsWith("typedef"))) {
      continue;
    }
    const d = (cee ? cdef : decl).exec(cd);
    if (d === null) {
      continue;
    }
    const kind = cee ? "function" : d[1];
    const name = cee ? d[1] : d[2];
    if (kind === "type") {
      if (sec !== "Types") {
        flag(i, "layout", "type " + name + " outside the Types section");
      }
      continue;
    }
    if (kind !== "function") {
      if (sec !== "Constants") {
        flag(i, "layout", kind + " " + name +
          " outside the Constants section");
      }
      continue;
    }
    const fits = (w: string): boolean =>
      w !== "" &&
      (name === w.toLowerCase() || name.startsWith(w.toLowerCase() + "_"));
    if (!name.endsWith("_func") && !fits(sub) && !fits(sec)) {
      const at = sub === "" ? sec : sub;
      const want = at === "" ? "a section above it" : at.toLowerCase() + "_*";
      flag(i, "layout", "def " + name + " out of place (wants " + want + ")");
    }
  }
}

function rule_align(m: Mask, flag: FlagFn): void {
  const dfn = /^#define\s+([A-Za-z_]\w*(?:\([^)]*\))?)(\s+)\S/;
  const gbl = new RegExp("^((?:static|typedef|CONSTV)\\b[^;=([{]*[\\s*])" +
    "([A-Za-z_]\\w*)[^;(]*;\\s*$");
  let kind = "";
  let cols: [number, number][] = [];
  const flush = (): void => {
    const seen = [...new Set(cols.map(([, c]) => c))];
    if (cols.length >= 2 && seen.length > 1) {
      const word = kind === "define" ? "values" : "names";
      flag(cols[0][0], "align", word + " at columns " + seen.join(", ") +
        " in one block");
    }
    cols = [];
  };
  for (let i = 0; i < m.raw.length; i += 1) {
    const line = m.raw[i];
    if (!m.open[i]) {
      const d = dfn.exec(line);
      if (d !== null && !line.endsWith("\\")) {
        if (kind !== "define") {
          flush();
          kind = "define";
        }
        cols.push([i, 8 + d[1].length + d[2].length]);
        continue;
      }
      const g = gbl.exec(line);
      if (g !== null) {
        if (kind !== "global") {
          flush();
          kind = "global";
        }
        cols.push([i, g[1].length]);
        continue;
      }
    }
    flush();
    kind = "";
  }
  flush();
}

function rule_names(m: Mask, flag: FlagFn): void {
  const head = /^\s*\/\/ ?([A-Za-z0-9_.]+) ::=$/;
  const item = /^\s*\/\/ ?\s*\| ([A-Za-z0-9_.]+)(?:\(([^)]*)\))?/;
  for (let i = 0; i < m.raw.length; i += 1) {
    const h = m.open[i] ? null : head.exec(m.raw[i]);
    if (h === null) {
      continue;
    }
    const ctrs: string[] = [];
    let j = i + 1;
    for (; j < m.raw.length && !m.open[j]; j += 1) {
      const r = item.exec(m.raw[j]);
      if (r === null) {
        break;
      }
      ctrs.push(r[1]);
      const fields = (r[2] ?? "").split(",").map((f) => f.trim())
        .filter((f) => f !== "");
      const sizes = [...new Set(fields.map((f) => f.length))];
      if (sizes.length > 1) {
        flag(j, "names", "fields of " + r[1] + " at lengths " +
          sizes.join(", "));
      }
    }
    const sizes = [...new Set(ctrs.map((c) => c.length))];
    if (sizes.length > 1) {
      flag(i, "names", "constructors of " + h[1] + " at lengths " +
        sizes.join(", "));
    }
    i = j - 1;
  }
}

function rule_parts(m: Mask, flag: FlagFn): void {
  const word = new RegExp("^# ?([A-Za-z0-9_.]+)$");
  const bars = new RegExp("^# ?=+$");
  const decl = /^(type|assert|def)\s+([A-Za-z0-9_.]+)/;
  const claims: string[] = [];
  const lone: [number, string][] = [];
  let body = "";
  let part = "";
  let seen = 0;
  let last = -1;
  for (let i = 0; i < m.raw.length; i += 1) {
    if (m.open[i]) {
      continue;
    }
    const mark = word.exec(m.raw[i]);
    if (mark !== null && bars.test(m.raw[i + 1] ?? "")) {
      if (mark[1] !== PARTS[seen]) {
        flag(i, "layout", "section " + mark[1] + " out of place (wants " +
          (PARTS[seen] ?? "no more sections") + ")");
      }
      part = mark[1];
      seen += 1;
      continue;
    }
    const d = decl.exec(m.code[i]);
    if (d === null) {
      if (part === "Types") {
        body += m.code[i] + "\n";
      }
      continue;
    }
    const kind = d[1];
    const name = d[2];
    if (kind === "type") {
      if (part !== "Types") {
        flag(i, "layout", "type " + name + " outside the Types part");
      }
      continue;
    }
    if (kind === "assert") {
      if (part === "Types") {
        lone.push([i, name]);
      } else if (part !== "Claims") {
        flag(i, "layout", "assert " + name + " outside the Claims part");
      }
      claims.push(name);
      continue;
    }
    if (part !== "Proofs") {
      flag(i, "layout", "def " + name + " outside the Proofs part");
    }
    const at = claims.indexOf(name);
    if (at < 0) {
      flag(i, "layout", "def " + name + " fills no claim");
    } else if (at < last) {
      flag(i, "layout", "def " + name + " out of the claims' order");
    } else {
      last = at;
    }
  }
  for (const [i, name] of lone) {
    const used = new RegExp("\\b" + name.replace(/\./g, "\\.") + "\\(");
    if (!used.test(body)) {
      flag(i, "layout", "assert " + name +
        " in the Types part, which no type there applies");
    }
  }
}

// Style
// =====

export function style_lint(src: string, layout: boolean,
  lead: string = "//", head: boolean = false, cee: boolean = false): Flag[] {
  const mask = mask_read(src, lead);
  const flags: Flag[] = [];
  const flag = (line: number, rule: string, text: string): void => {
    flags.push({ line: line + 1, rule, text });
  };
  rule_notes(mask, flag, lead, head);
  rule_layout(mask, flag);
  if (lead === "//") {
    rule_exprs(mask, flag);
  }
  if (cee) {
    rule_align(mask, flag);
    rule_names(mask, flag);
  }
  if (layout && lead === "#") {
    rule_parts(mask, flag);
  }
  if (layout && lead === "//") {
    rule_files(mask, flag, cee);
  }
  return flags;
}

export function style_report(label: string, file: string, base: number,
  flags: Flag[], fails: string[]): void {
  if (flags.length === 0) {
    console.log("PASS " + label + " style");
    return;
  }
  const rules = [...new Set(flags.map((f) => f.rule))].sort();
  for (const rule of rules) {
    const mine = flags.filter((f) => f.rule === rule);
    fails.push(label + ": " + String(mine.length) + " " + rule);
    for (const f of mine.slice(0, SHOWN)) {
      fails.push("    " + file + ":" + String(base + f.line - 1) + "  " +
        f.text.slice(0, 60));
    }
  }
}

export function style_gate(): string[] {
  const fails: string[] = [];
  for (const file of STYLED) {
    const src = fs.readFileSync(path.join(ROOT, file), "utf8");
    const lead = file.endsWith(".bend") ? "#" : "//";
    const flags = style_lint(src, LAYOUT.includes(file), lead,
      false, file.endsWith(".c"));
    if (file.startsWith("src/effs/") && file.endsWith(".js")) {
      const rows = src.split("\n");
      for (let i = 0; i < rows.length; i += 1) {
        if (/process\.std(out|err)\.write\(/.test(rows[i])) {
          flags.push({ line: i + 1, rule: "stream", text: rows[i].trim() });
        }
      }
    }
    style_report(file, file, 1, flags, fails);
  }
  for (const part of bend_parts()) {
    const [, layout, cee] = BENDED.find((b) => b[0] === part.name) as
      [string, boolean, boolean];
    const flags = style_lint(part.src, layout, "//", false, cee);
    style_report(BEND + " " + part.name, BEND, part.line, flags, fails);
  }
  return fails;
}

// Gate
// ====

export function gate_run(): string[] {
  const caps = caps_gate();
  const style = style_gate();
  return [...caps, ...style];
}

// Main
// ====

if (import.meta.main) {
  const fails = ((): string[] => {
    try {
      return gate_run();
    } catch (e) {
      return ["repo crashed: " + String(e)];
    }
  })();
  for (const line of fails) {
    console.log(line);
  }
  console.log(fails.length === 0 ? "PASSED" : "FAILED");
  process.exit(fails.length === 0 ? 0 : 1);
}
