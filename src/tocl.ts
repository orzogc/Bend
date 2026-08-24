// Bend → C
// ========
//
// Compiles a checked Book into one standalone C program: src/runtime.c with
// its two markers filled (GEN:DEFS: ids + arity tables; GEN:CODE: the user
// functions in the FUN_/PAR_/SEQ_ regions plus fid_call). Same walk as
// tojs.ts — each def's elaboration compiles toward a target, binders consume
// a queue of pending arguments — with the C differences: values are Term
// words; FUN defs print as plain C functions and TASKED defs (DEEP recursion,
// closure application, or a TASKED callee, to a fixpoint) print as Reply
// entries, where a non-tail call CUTS the function into a minted SEQ_
// continuation (frame = TSK; captures found by scanning the continuation's
// text for the parent's locals, exact since locals are unique per family).
// Lambdas LIFT to PAR_ entries applied through clos_call (unary, so one apply
// saturates). Drops are emitted at binds and at the match arms that skip a
// var; usage is read off raw arm terms (Rwt evidence/motive and Ann types
// skipped — a live var mentioned only inside an erased argument would leak,
// which the harness's balance check turns into a fail-stop). Walls, loud:
// fork groups and ! marks (no core surface yet: fid_forks/fid_bangs answer
// false), U32 intro/elim over computed Words, partial def application,
// expression-position matches whose arms cut, main results outside
// String/Bool/Nat/U32/Char.

import * as fs from "fs";
import * as core from "./core.ts";
import { def_get_params, ctr_get_quants } from "./tojs.ts";

// Types
// =====

// Seg: one emitted C function: a FUN def, a PAR def entry, a lifted lambda
// entry, or a minted SEQ continuation. params holds the entry params bound
// at creation; finalize prepends a continuation's captures.
export type Seg = {
  name:   string;
  fid:    string | null;
  region: "fun" | "par" | "seq";
  lines:  string[];
  params: string[];
  arity:  number;
  cut:    Cut | null;
  loop:   boolean;
};

// Cut: the seam between a segment and the segment it spawned: a non-tail
// TASKED call ("call"), a closure application ("apply"), or a lifted lambda
// ("clo"). The parent holds one placeholder line, replaced at finalize by
// the frame/CLO build once the child's captures are known.
export type Cut = {
  parent: Seg;
  at:     number;
  scope:  string[];
  tab:    number;
  kind:   "call" | "apply" | "clo";
  own:    boolean;
  callee: string;
  fn:     string;
  args:   string[];
  hole:   string;
};

// Fact: raw call-graph facts of one def, computed before emission.
export type Fact = {
  calls:    Set<core.Name>;
  selfTail: boolean;
  deep:     boolean;
  applies:  boolean;
  tasked:   boolean;
};

export type File = {
  book:  core.Book;
  segs:  Seg[];
  seg:   Seg;
  fresh: Map<string, number>;
  scope: string[];
  loop:  { name: core.Name; args: string[] } | null;
  own:   boolean;
  spares: Array<{ cls: number; name: string }>;
  defc:  string;
  kn:    number;
  facts: Map<core.Name, Fact>;
  done:  Set<core.Name>;
  queue: core.Name[];
  cids:  Map<string, { id: number; arity: number }>;
  names: Set<string>;
  cname: Map<core.Name, string>;
};

// Native: per base-type ctor, how to build (intr; null = wall), read (elim:
// field exprs, bound eagerly), test (cond), and release the scrutinee node
// (free: a statement after the fields are out; generic ADTs free inline).
export type Native = {
  intr: Record<core.Name, ((xs: string[]) => string) | null>;
  elim: Record<core.Name, ((s: string) => string[]) | null>;
  cond: Record<core.Name, (s: string) => string>;
  free: Record<core.Name, ((s: string) => string) | null>;
};

// Constants
// =========

export const TEMPLATE: string = fs.readFileSync(new URL("./runtime.c", import.meta.url), "utf8");

const IDENT = /^[A-Za-z_][A-Za-z0-9_]*$/;

// ALLOC_COST: worst-case pages per textual call site, for the entry guards
// (small-class allocs take at most one fresh page; dynamic arrays price the
// 2^19-word worst case; overpricing is safe, the host never fails a guard).
const ALLOC_COST: Array<[RegExp, number]> = [
  [/\bheap_alloc\(/g, 1], [/\btask_node\(/g, 1], [/\bheap_swap\(/g, 1], [/\bclos_call\(/g, 1],
  [/\bbool_copy\(/g, 3], [/\bnat_copy\(/g, 3], [/\bu32_copy\(/g, 3],
  [/\bnat_divmod\(/g, 1], [/\bnat_bits\(/g, 1],
  [/\bflat_trade\(/g, 1], [/\bflat_leaf\(/g, 1], [/\bflat_node\(/g, 256],
  [/\bflat_half\(/g, 256],
  [/\bnat_show\(/g, 16], [/\bu32_show\(/g, 10],
  [/\bbool_show\(/g, 8], [/\bchr_show\(/g, 1], [/\bbool_if\(/g, 0],
];

// Natives
// =======

export const NATIVES: Record<core.Name, Native> = {
  Nat: {
    intr: {
      Zero: () => "0",
      Succ: ([p]) => (/^\d+(ull)?$/.test(p) ? (BigInt(p.replace("ull", "")) + 1n) + "ull" : "nat_succ(e, " + p + ")"),
    },
    elim: { Zero: () => [], Succ: (s) => ["(" + s + " - 1)"] },
    cond: { Zero: (s) => s + " == 0", Succ: (s) => s + " != 0" },
    free: { Zero: null, Succ: null },
  },
  Bool: {
    intr: { False: () => "0", True: () => "1" },
    elim: { False: () => [], True: () => [] },
    cond: { False: (s) => s + " == 0", True: (s) => s + " != 0" },
    free: { False: null, True: null },
  },
  U32: {
    intr: { U32: null },   // an all-literal U32 folds before this; computed Words wall
    elim: { U32: null },
    cond: {},
    free: { U32: null },
  },
  Char: {
    intr: { Chr: ([c]) => c },
    elim: { Chr: (s) => [s] },
    cond: {},
    free: { Chr: null },
  },
  Array: {
    intr: { ALeaf: ([v]) => "flat_leaf(e, " + v + ")",
            ANode: ([l, r]) => "flat_node(e, " + l + ", " + r + ")" },
    elim: { ALeaf: (s) => ["flat_take(e.mem, " + s + ")"],
            ANode: (s) => ["flat_half(e, " + s + ", 0)", "flat_half(e, " + s + ", 1)"] },
    cond: { ALeaf: (s) => "term_aux(" + s + ") == 0",
            ANode: (s) => "term_aux(" + s + ") != 0" },
    free: { ALeaf: null,
            ANode: (s) => "heap_free(e.mem, (u32)term_aux(" + s + "), term_loc(" + s + "));" },
  },
};

// Intrinsics
// ==========
//
// One entry per runtime.js function that a def name can resolve to (the
// same lowercase '.' → '_' contract as tojs). Each C expression uses every
// argument exactly once; multi-use semantics are runtime.c functions.

// pv: the raw-scalar-locals baseline, stateless by construction: a pair-
// returning intrinsic destructured ON THE SPOT binds these two component
// expressions eagerly (in order, so effectful components stay ordered)
// instead of building, testing and freeing a Tuple node.
type Comp = string | [string, string];
type Intr = { n: number; e: (fl: File, a: string[]) => string; pv?: (a: string[]) => [Comp, Comp] };

function cmp_cids(fl: File): void {
  cid_reg(fl, "LT", 0); cid_reg(fl, "EQ", 0); cid_reg(fl, "GT", 0);
}

export const INTRINSICS: Record<string, Intr> = {
  bool_not:    { n: 1, e: (_, [a]) => "((u64)(" + a + " == 0))" },
  bool_and:    { n: 2, e: (_, [a, b]) => "(" + a + " & " + b + ")" },
  bool_or:     { n: 2, e: (_, [a, b]) => "(" + a + " | " + b + ")" },
  bool_xor:    { n: 2, e: (_, [a, b]) => "(" + a + " ^ " + b + ")" },
  bool_if:     { n: 3, e: (_, [b, t, f]) => "bool_if(e.mem, " + b + ", " + t + ", " + f + ")" },
  cmp_is_lt:   { n: 1, e: (fl, [c]) => (cmp_cids(fl), "((u64)(term_aux(" + c + ") == CID_LT))") },
  cmp_is_eq:   { n: 1, e: (fl, [c]) => (cmp_cids(fl), "((u64)(term_aux(" + c + ") == CID_EQ))") },
  cmp_is_gt:   { n: 1, e: (fl, [c]) => (cmp_cids(fl), "((u64)(term_aux(" + c + ") == CID_GT))") },
  cmp_is_le:   { n: 1, e: (fl, [c]) => (cmp_cids(fl), "((u64)(term_aux(" + c + ") != CID_GT))") },
  cmp_is_ge:   { n: 1, e: (fl, [c]) => (cmp_cids(fl), "((u64)(term_aux(" + c + ") != CID_LT))") },
  // bool_copy is C-only: tojs compiles Bool.copy structurally; the C form
  // ((b, -), (b, -)) is bit-equal and fuses to two register moves
  bool_copy:   { n: 1, e: (_, [a]) => "bool_copy(e, " + a + ")", pv: ([a]) => [[a, "0"], [a, "0"]] },
  nat_copy:    { n: 1, e: (_, [a]) => "nat_copy(e, " + a + ")", pv: ([a]) => [[a, "0"], [a, "0"]] },
  nat_is_zero: { n: 1, e: (_, [a]) => "((u64)(" + a + " == 0))" },
  nat_pred:    { n: 1, e: (_, [a]) => "nat_pred(" + a + ")" },
  nat_double:  { n: 1, e: (_, [a]) => "nat_double(e, " + a + ")" },
  nat_add:     { n: 2, e: (_, [a, b]) => "nat_add(e, " + a + ", " + b + ")" },
  nat_sub:     { n: 2, e: (_, [a, b]) => "nat_sub(" + a + ", " + b + ")" },
  nat_mul:     { n: 2, e: (_, [a, b]) => "nat_mul(e, " + a + ", " + b + ")" },
  nat_divmod:  { n: 2, e: (_, [a, b]) => "nat_divmod(e, " + a + ", " + b + ")", pv: ([a, b]) => ["nat_div(" + a + ", " + b + ")", "nat_mod(" + a + ", " + b + ")"] },
  nat_div:     { n: 2, e: (_, [a, b]) => "nat_div(" + a + ", " + b + ")" },
  nat_mod:     { n: 2, e: (_, [a, b]) => "nat_mod(" + a + ", " + b + ")" },
  nat_min:     { n: 2, e: (_, [a, b]) => "nat_min(" + a + ", " + b + ")" },
  nat_max:     { n: 2, e: (_, [a, b]) => "nat_max(" + a + ", " + b + ")" },
  nat_cmp:     { n: 2, e: (fl, [a, b]) => (cmp_cids(fl), "cmp_new(" + a + ", " + b + ")") },
  nat_is_eq:   { n: 2, e: (_, [a, b]) => "((u64)(" + a + " == " + b + "))" },
  nat_is_ne:   { n: 2, e: (_, [a, b]) => "((u64)(" + a + " != " + b + "))" },
  nat_is_lt:   { n: 2, e: (_, [a, b]) => "((u64)(" + a + " < " + b + "))" },
  nat_is_le:   { n: 2, e: (_, [a, b]) => "((u64)(" + a + " <= " + b + "))" },
  nat_is_gt:   { n: 2, e: (_, [a, b]) => "((u64)(" + a + " > " + b + "))" },
  nat_is_ge:   { n: 2, e: (_, [a, b]) => "((u64)(" + a + " >= " + b + "))" },
  nat_pow2:    { n: 1, e: (_, [a]) => "nat_pow2(e, " + a + ")" },
  nat_bits:    { n: 1, e: (_, [a]) => "nat_bits(e, " + a + ")", pv: ([a]) => ["(" + a + " & 1)", "(" + a + " >> 1)"] },
  u32_zero:    { n: 0, e: () => "0" },
  u32_one:     { n: 0, e: () => "1" },
  u32_copy:    { n: 1, e: (_, [a]) => "u32_copy(e, " + a + ")", pv: ([a]) => [[a, "0"], [a, "0"]] },
  u32_inc:     { n: 1, e: (_, [a]) => "((u64)(u32)((u32)(" + a + ") + 1u))" },
  u32_add:     { n: 2, e: (_, [a, b]) => "((u64)(u32)((u32)(" + a + ") + (u32)(" + b + ")))" },
  u32_sub:     { n: 2, e: (_, [a, b]) => "((u64)(u32)((u32)(" + a + ") - (u32)(" + b + ")))" },
  u32_mul:     { n: 2, e: (_, [a, b]) => "((u64)(u32)((u32)(" + a + ") * (u32)(" + b + ")))" },
  u32_div:     { n: 2, e: (_, [a, b]) => "((u64)u32_div((u32)(" + a + "), (u32)(" + b + ")))" },
  u32_mod:     { n: 2, e: (_, [a, b]) => "((u64)u32_mod((u32)(" + a + "), (u32)(" + b + ")))" },
  u32_not:     { n: 1, e: (_, [a]) => "((u64)(u32)~(u32)(" + a + "))" },
  u32_and:     { n: 2, e: (_, [a, b]) => "((u64)((u32)(" + a + ") & (u32)(" + b + ")))" },
  u32_or:      { n: 2, e: (_, [a, b]) => "((u64)((u32)(" + a + ") | (u32)(" + b + ")))" },
  u32_xor:     { n: 2, e: (_, [a, b]) => "((u64)((u32)(" + a + ") ^ (u32)(" + b + ")))" },
  u32_shl:     { n: 1, e: (_, [a]) => "((u64)(u32)((u32)(" + a + ") << 1))" },
  u32_shr:     { n: 1, e: (_, [a]) => "((u64)((u32)(" + a + ") >> 1))" },
  u32_shln:    { n: 2, e: (_, [n, a]) => "u32_shln(" + a + ", " + n + ")" },
  u32_shrn:    { n: 2, e: (_, [n, a]) => "u32_shrn(" + a + ", " + n + ")" },
  u32_cmp:     { n: 2, e: (fl, [a, b]) => (cmp_cids(fl), "cmp_new((u32)(" + a + "), (u32)(" + b + "))") },
  u32_is_eq:   { n: 2, e: (_, [a, b]) => "((u64)((u32)(" + a + ") == (u32)(" + b + ")))" },
  u32_is_ne:   { n: 2, e: (_, [a, b]) => "((u64)((u32)(" + a + ") != (u32)(" + b + ")))" },
  u32_is_lt:   { n: 2, e: (_, [a, b]) => "((u64)((u32)(" + a + ") < (u32)(" + b + ")))" },
  u32_is_le:   { n: 2, e: (_, [a, b]) => "((u64)((u32)(" + a + ") <= (u32)(" + b + ")))" },
  u32_is_gt:   { n: 2, e: (_, [a, b]) => "((u64)((u32)(" + a + ") > (u32)(" + b + ")))" },
  u32_is_ge:   { n: 2, e: (_, [a, b]) => "((u64)((u32)(" + a + ") >= (u32)(" + b + ")))" },
  u32_is_zero: { n: 1, e: (_, [a]) => "((u64)((u32)(" + a + ") == 0))" },
  u32_to_nat:  { n: 1, e: (_, [a]) => "((u64)(u32)(" + a + "))" },
  u32_from_nat:{ n: 1, e: (_, [a]) => "((u64)(u32)(" + a + "))" },
  array_swap:     { n: 3, e: (_, [a, i, v]) => "flat_trade(e, " + a + ", " + i + ", " + v + ")",
                    pv: ([a, i, v]) => [a, "((u64)flat_swap(e.mem, " + a + ", flat_clamp(" + a + ", " + i + "), (u32)(" + v + ")))"] },
};

// Names
// =====

function sanitize(k: string): string {
  return k.replace(/[^A-Za-z0-9_]/g, "_");
}

// name_take: a globally unique C identifier for base; uniqueness is
// case-insensitive so the derived FID_/CID_ macros stay unique too.
function name_take(fl: File, base: string): string {
  let name = base;
  let i = 2;
  while (fl.names.has(name.toLowerCase())) {
    name = base + "_" + i++;
  }
  fl.names.add(name.toLowerCase());
  return name;
}

// file_fresh: the C local for binder k: sanitized name + per-family count.
export function file_fresh(fl: File, k: core.Name): string {
  const base = sanitize(k);
  const n = fl.fresh.get(base) ?? 0;
  fl.fresh.set(base, n + 1);
  return base + "_" + n;
}

// def_cname: the stable C stem of def k (main may be remapped by the root).
function def_cname(fl: File, k: core.Name): string {
  let c = fl.cname.get(k);
  if (c === undefined) {
    c = name_take(fl, sanitize(k));
    fl.cname.set(k, c);
  }
  return c;
}

function cid_reg(fl: File, k: core.Name, arity: number): string {
  const got = fl.cids.get(k);
  if (got === undefined) {
    fl.cids.set(k, { id: fl.cids.size, arity });
  }
  return "CID_" + sanitize(k).toUpperCase();
}

function file_push(fl: File, tab: number, line: string): void {
  fl.seg.lines.push("  ".repeat(tab) + line);
}

// drop_push: the braced three-line drop of a possibly-dead local.
function drop_push(fl: File, tab: number, v: string): void {
  file_push(fl, tab, "if (!term_triv(" + v + ")) {");
  file_push(fl, tab + 1, "term_drop(e.mem, " + v + ");");
  file_push(fl, tab, "}");
}

// local_fit: hoist a fat argument into a named local, so composed calls
// never print a giant line (C never sequenced call arguments, so the hoist
// moves nothing observable). Idents and literals pass through.
const EXPR_COLS = 70;

function local_fit(fl: File, tab: number, x: string): string {
  if (IDENT.test(x) || /^\d+(ull)?$/.test(x)) {
    return x;
  }
  const t = file_fresh(fl, "x");
  file_push(fl, tab, "Term " + t + " = " + x + ";");
  fl.scope.push(t);
  return t;
}

function seg_new(fl: File, name: string, region: "fun" | "par" | "seq", params: string[], cut: Cut | null): Seg {
  const seg: Seg = {
    name, region, lines: [], params: params.slice(), arity: params.length, cut, loop: false,
    fid: region === "fun" ? null : "FID_" + name.replace(/^(PAR_|SEQ_)/, "").toUpperCase(),
  };
  fl.segs.push(seg);
  return seg;
}

// intr_low: the intrinsic key of def name k (tojs's compile_name_sat rule).
function intr_low(k: core.Name): string {
  return k.toLowerCase().replace(/\./g, "_");
}

// Facts
// =====
//
// One raw walk per def over def.v: the callees (Ref heads), whether a self
// call sits in saturated tail position, whether any self call does not, and
// whether the body applies a non-Ref head (a closure). Lambda bodies are
// scanned into the same facts — a def that only BUILDS an applying closure
// is over-approximated as TASKED, which costs form, never correctness.

function fact_scan(book: core.Book, k: core.Name, def: core.Def): Fact {
  const fact: Fact = { calls: new Set(), selfTail: false, deep: false, applies: false, tasked: false };
  function walk(tm: core.HTerm, tail: boolean, d: number): void {
    const t = core.term_strip(tm);
    switch (t.$) {
      case "Lam": walk(t.f(hvar("~", d)), tail, d + 1); return;
      case "Let": walk(t.v, false, d); walk(t.f(hvar("~", d)), tail, d + 1); return;
      case "Mat": walk(t.h, tail, d); walk(t.m, tail, d); return;
      case "Rwt": walk(t.f, tail, d); return;
      case "Ctr": for (const x of t.x) walk(x, false, d); return;
      case "App": {
        let args = 0;
        let cur: core.HTerm = t;
        while (cur.$ === "App") {
          walk(cur.x, false, d);
          args += 1;
          cur = core.term_strip(cur.f);
        }
        if (cur.$ === "Ref") {
          if (cur.k === k) {
            if (tail && args === def.n) fact.selfTail = true;
            else fact.deep = true;
          } else if (INTRINSICS[intr_low(cur.k)] === undefined) {
            fact.calls.add(cur.k);
          }
          return;
        }
        if (cur.$ === "Var") { fact.applies = true; return; }
        walk(cur, tail, d);
        return;
      }
      case "Ref": if (t.k !== k && INTRINSICS[intr_low(t.k)] === undefined) fact.calls.add(t.k); return;
      default: return;
    }
  }
  if (def.v !== null) walk(def.v, true, 0);
  return fact;
}

// facts_build: scan from main; DEEP = non-tail self recursion or a mutual
// cycle; TASKED = DEEP or applies, closed over callers to a fixpoint.
export function facts_build(book: core.Book): Map<core.Name, Fact> {
  const facts = new Map<core.Name, Fact>();
  const queue = ["main"];
  while (queue.length > 0) {
    const k = queue.pop()!;
    if (facts.has(k)) continue;
    const tld = book.tlds[k];
    if (tld === undefined || tld.$ !== "Def") continue;
    const fact = fact_scan(book, k, tld);
    facts.set(k, fact);
    for (const g of fact.calls) queue.push(g);
  }
  for (const [k, fact] of facts) {
    if (!fact.deep) {                       // mutual cycle: k reaches k via others
      const seen = new Set<core.Name>();
      const st = [...fact.calls].filter((g) => g !== k);
      while (st.length > 0) {
        const g = st.pop()!;
        if (g === k) { fact.deep = true; break; }
        if (seen.has(g)) continue;
        seen.add(g);
        for (const h of facts.get(g)?.calls ?? []) st.push(h);
      }
    }
    fact.tasked = fact.deep || fact.applies;
  }
  for (let changed = true; changed;) {      // TASKED rises to callers
    changed = false;
    for (const [, fact] of facts) {
      if (!fact.tasked && [...fact.calls].some((g) => facts.get(g)?.tasked)) {
        fact.tasked = true;
        changed = true;
      }
    }
  }
  return facts;
}

// term_vars: the Var names a term mentions, skipping type-only subtrees
// (Rwt evidence and motive, Ann types) — the drop and liveness oracle.
export function term_vars(tm: core.HTerm, d: number, out: Set<string>): Set<string> {
  const t = core.term_force(tm);
  switch (t.$) {
    case "Var": out.add(t.k); return out;
    case "Lam": return term_vars(t.f(hvar("~", d)), d + 1, out);
    case "Let": term_vars(t.v, d, out); return term_vars(t.f(hvar("~", d)), d + 1, out);
    case "Mat": term_vars(t.h, d, out); return term_vars(t.m, d, out);
    case "App": term_vars(t.f, d, out); return term_vars(t.x, d, out);
    case "Ctr": for (const x of t.x) term_vars(x, d, out); return out;
    case "Rwt": return term_vars(t.f, d, out);
    case "Ann": return term_vars(t.x, d, out);
    case "Sub": return term_vars(t.f, d, out);
    default: return out;
  }
}

// Compile
// =======

// hvar: a HOAS Var pinned to HTerm (core.Var's generic infers unknown).
function hvar(k: string, i: number): core.HTerm {
  return core.Var(k, i);
}

function dedup(xs: string[]): string[] {
  return [...new Set(xs)];
}

function fid_of(fl: File, k: core.Name): string {
  return "FID_" + def_cname(fl, k).toUpperCase();
}

// par_mode: the emission mode IS the current segment's region.
function par_mode(fl: File): boolean {
  return fl.seg.region !== "fun";
}

// own_cls / fid_cls: node classes as C constant expressions (fid_arity is
// an INLINE switch over a constant, so the compiler folds these).
function cls_of(words: number): number {
  let c = 0;
  while ((1 << c) < words) c++;
  return c;
}

function fid_cls(fid: string): string {
  return "cls_fit(fid_arity(" + fid + ") + 2)";
}

// ctr_pack: build one CTR node of the given live fields, reusing a parked
// same-class spare when one exists; returns the loc local.
function ctr_pack(fl: File, tab: number, exprs: string[]): string {
  const nd = file_fresh(fl, "nd");
  const at = fl.spares.findIndex((s) => s.cls === cls_of(exprs.length));
  if (at >= 0) {
    file_push(fl, tab, "u64 " + nd + " = " + fl.spares[at].name + ";");
    fl.spares.splice(at, 1);
  } else {
    file_push(fl, tab, "u64 " + nd + " = heap_alloc(e, cls_fit(" + exprs.length + "));");
  }
  fl.scope.push(nd);   // the loc may ride a frame if a later argument cuts
  exprs.forEach((e, j) => file_push(fl, tab, "e.mem[loc_at(" + nd + " + " + j + ")] = " + e + ";"));
  return nd;
}

// spare_flush: free the ctor spares parked on this path (a terminal, a
// loop continue, or a cut boundary ends the path).
function spare_flush(fl: File, tab: number): void {
  for (const s of fl.spares) {
    file_push(fl, tab, "heap_free(e.mem, " + s.cls + ", " + s.name + ");");
  }
  fl.spares = [];
}

// own_close: the entry's own node dies here (every PAR/SEQ path disposes
// it exactly once; REPLY_NEED paths return before it, keeping the replay).
function own_close(fl: File, tab: number): void {
  if (fl.own) {
    file_push(fl, tab, "heap_free(e.mem, " + fid_cls(fl.seg.fid!) + ", a);");
    fl.own = false;
  }
}

// pair_split: is this term a saturated pair-returning intrinsic call? Its
// args alias into locals, so each component uses them at most once.
function pair_split(fl: File, tm: core.HTerm, tab: number, d: number): [string, string] | null {
  const t = core.term_force(tm);
  if (t.$ === "Ann") {
    return pair_split(fl, t.x, tab, d);
  }
  if (t.$ !== "App") {
    return null;
  }
  const qq: core.HTerm[] = [];
  let cur: core.HTerm = t;
  for (;;) {
    const c: core.HTerm = core.term_force(cur);
    if (c.$ === "Ann") {
      cur = c.x;
      continue;
    }
    if (c.$ === "App") {
      const f = core.term_force(c.f);
      if (f.$ !== "Ann") {
        return null;
      }
      const all = core.term_wnf(fl.book, f.T);
      if (all.$ !== "All") {
        return null;
      }
      if (all.q.$ !== "None") {
        qq.unshift(c.x);
      }
      cur = c.f;
      continue;
    }
    if (c.$ === "Ref") {
      const intr = INTRINSICS[intr_low(c.k)];
      if (intr === undefined || intr.pv === undefined || qq.length !== intr.n) {
        return null;
      }
      const args = qq.map((a) => {
        let e = compile_term(fl, a, null, tab, null, [], d);
        if (!IDENT.test(e)) {
          const al = file_fresh(fl, "x");
          file_push(fl, tab, "Term " + al + " = " + e + ";");
          fl.scope.push(al);
          e = al;
        }
        return e;
      });
      return intr.pv(args);
    }
    return null;
  }
}

function ref_need(fl: File, k: core.Name): void {
  if (!fl.done.has(k)) {
    fl.done.add(k);
    fl.queue.push(k);
  }
}

// cut_new: end the current function here — return the callee's TSK chained
// to a minted continuation frame (rem 1) — and steer the remainder of this
// path into the continuation's body. The frame build stays a placeholder in
// the parent until finalize knows the captures.
function cut_new(fl: File, tab: number, kind: "call" | "apply", callee: string, fn: string, args: string[]): string {
  if (!par_mode(fl)) {
    throw new Error("tocl: a task call surfaced inside a FUN def (facts fixpoint broken)");
  }
  spare_flush(fl, tab);
  const hole   = file_fresh(fl, "h");
  const parent = fl.seg;
  const at     = parent.lines.length;
  parent.lines.push("/*CUT*/");
  const seg = seg_new(fl, name_take(fl, "SEQ_" + fl.defc + "_k" + fl.kn++), "seq", [hole], null);
  seg.cut = { parent, at, scope: dedup(fl.scope), tab, kind, own: fl.own, callee, fn, args, hole };
  fl.seg  = seg;
  fl.loop = null;
  fl.own  = true;
  fl.scope.push(hole);
  return hole;
}

// compile_lift: a lambda (or eliminator) value becomes a fresh PAR_ entry
// (captures + one param) plus a CLO word; captures resolve at finalize.
function compile_lift(fl: File, tab: number, x: core.HTerm, ty: core.HTerm | null, d: number): string {
  const pname  = file_fresh(fl, x.$ === "Lam" ? x.k : "s");
  const cl     = file_fresh(fl, "cl");
  const parent = fl.seg;
  const at     = parent.lines.length;
  parent.lines.push("/*CUT*/");
  const seg = seg_new(fl, name_take(fl, "PAR_" + fl.defc + "_f" + fl.kn++), "par", [pname], null);
  seg.cut = { parent, at, scope: dedup(fl.scope), tab, kind: "clo", callee: "", fn: "", args: [], hole: cl };
  const st = { seg: fl.seg, scope: fl.scope, loop: fl.loop, own: fl.own, spares: fl.spares };
  fl.seg    = seg;
  fl.loop   = null;
  fl.own    = true;
  fl.spares = [];
  fl.scope  = st.scope.concat([pname]);
  if (x.$ === "Lam") {
    const body = x.f(hvar(pname, d));
    if (!term_vars(body, d + 1, new Set()).has(pname)) {
      drop_push(fl, 1, pname);
    }
    compile_term(fl, body, null, 1, "return", [], d + 1);
  } else {
    compile_term(fl, x, ty, 1, "return", [hvar(pname, 0)], d);
  }
  fl.seg = st.seg; fl.scope = st.scope; fl.loop = st.loop; fl.own = st.own; fl.spares = st.spares;
  return "term_clos(" + seg.fid + ", " + cl + ")";
}

// compile_term: emit one checked term at indentation tab, toward tgt: a C
// local, "return", or null to get the expression handed back (statement-
// shaped parts hoist into the current segment first). d is the binder depth.
export function compile_term(fl: File, tm: core.HTerm, ty: core.HTerm | null, tab: number, tgt: string | null, q: core.HTerm[], d: number): string {
  function compile_term_put(e: string): string {
    if (tgt === "return") {
      spare_flush(fl, tab);
      if (par_mode(fl)) {
        own_close(fl, tab);
      }
    }
    if (tgt !== null) {
      file_push(fl, tab, (tgt === "return" ? "return " + e : tgt + " = " + e) + ";");
    }
    return e;
  }

  // compile_term_apply: fold closure applications over pending arguments;
  // the last one may inherit the entry's cont/idx (a tail apply).
  function compile_term_apply(f: string, args: core.HTerm[]): string {
    if (!par_mode(fl)) {
      throw new Error("tocl: closure application inside a FUN def (facts fixpoint broken)");
    }
    for (let i = 0; i < args.length; i++) {
      const a = compile_term(fl, args[i], null, tab, null, [], d);
      if (i === args.length - 1 && tgt === "return") {
        spare_flush(fl, tab);
        own_close(fl, tab);
        file_push(fl, tab, "return clos_call(e, " + f + ", " + a + ", cont, idx);");
        return "";
      }
      f = cut_new(fl, tab, "apply", "", f, [a]);
    }
    return compile_term_put(f);
  }

  // compile_term_match: emit a case tree over the queue's head scrutinee;
  // fields bind eagerly, the consumed node frees, dead outer vars drop at
  // the arms that skip them.
  function compile_term_match(x: core.HTerm, T: core.HTerm | null): void {
    // a pair-returning intrinsic destructured on the spot binds its two
    // components as locals; no Tuple is built, tested, or freed
    if (x.$ === "Mat" && x.k === "Tuple") {
      const pv = pair_split(fl, q[0], tab, d);
      if (pv !== null) {
        const rest0: core.HTerm[] = q.slice(1).map((a) => hvar(compile_term(fl, a, null, tab, null, [], d), 0));
        const fields: core.HTerm[] = pv.map((comp) => {
          const fn = file_fresh(fl, "f");
          if (typeof comp === "string") {
            file_push(fl, tab, "Term " + fn + " = " + comp + ";");
          } else {
            cid_reg(fl, "Tuple", 2);
            const nd = ctr_pack(fl, tab, [comp[0], comp[1]]);
            file_push(fl, tab, "Term " + fn + " = term_ctor(CID_TUPLE, " + nd + ");");
          }
          fl.scope.push(fn);
          return hvar(fn, 0);
        });
        compile_term(fl, x.h, null, tab, tgt, [...fields, ...rest0], d);
        return;
      }
    }
    let s = compile_term(fl, q[0], null, tab, null, [], d);
    if (!IDENT.test(s)) {
      const t = file_fresh(fl, "s");
      file_push(fl, tab, "Term " + t + " = " + s + ";");
      s = t;
    }
    const rest: core.HTerm[] = q.slice(1).map((a) => hvar(compile_term(fl, a, null, tab, null, [], d), 0));
    if (x.$ === "Efq") {
      file_push(fl, tab, "err_post(e.mem, ERR_TAGS);");
      file_push(fl, tab, "return " + (par_mode(fl) ? "TERM_HOLE" : "0") + ";");
      return;
    }
    const all = T === null ? null : core.term_wnf(fl.book, T);
    if (all === null || all.$ !== "All") {
      throw new Error("tocl: a match without a function-typed Ann");
    }
    const adt = core.term_wnf(fl.book, all.A);
    if (adt.$ !== "ADT") {
      throw new Error("tocl: a non-datatype match scrutinee");
    }
    const arms: Array<[core.Name, core.HTerm]> = [];
    let cur: core.HTerm = x;
    let m = core.term_strip(cur);
    while (m.$ === "Mat") {
      arms.push([m.k, m.h]);
      cur = m.m;
      m = core.term_strip(cur);
    }
    let end: core.HTerm | null = m.$ !== "Efq" ? cur : null;
    const tld = fl.book.tlds[adt.k];
    if (tld === undefined || tld.$ !== "ADT") {
      throw new Error("tocl: undeclared datatype: " + adt.k);
    }
    if (arms.length === 0 && end !== null) {
      compile_term(fl, end, null, tab, tgt, [hvar(s, 0), ...rest], d);
      return;
    }
    const total = tld.c.length - adt.r.length;
    if (arms.length === total) {
      end = null;
    }
    const native = NATIVES[adt.k];
    // per-branch usage of the outer scope: a var some branch consumes drops
    // at the start of every branch that skips it
    const armsets = arms.map(([, h]) => term_vars(h, d, new Set()));
    const endset  = end !== null ? term_vars(end, d, new Set()) : null;
    const allsets = endset !== null ? [...armsets, endset] : armsets;
    function drops_for(mine: Set<string>): string[] {
      return dedup(fl.scope).filter((v) => v !== s && !mine.has(v) && allsets.some((u) => u.has(v)));
    }
    function arm_emit(h: core.HTerm, k: core.Name, tab2: number, mine: Set<string>): void {
      const ctr = fl.book.ctrs[k];
      if (ctr === undefined) {
        throw new Error("tocl: unknown constructor: " + k);
      }
      const live = ctr_get_quants(fl.book, ctr).filter((u) => u.$ !== "None").length;
      let fexprs: string[];
      if (native !== undefined) {
        const el = native.elim[k];
        if (el === undefined || el === null) {
          throw new Error("tocl: no native elimination for a " + k + " match");
        }
        fexprs = el(s);
      } else {
        cid_reg(fl, k, live);
        fexprs = [];
        for (let j = 0; j < live; j++) {
          fexprs.push("e.mem[loc_at(term_loc(" + s + ") + " + j + ")]");
        }
      }
      const fields: core.HTerm[] = [];
      for (const fe of fexprs) {
        const fn = file_fresh(fl, "f");
        file_push(fl, tab2, "Term " + fn + " = " + fe + ";");
        fl.scope.push(fn);
        fields.push(hvar(fn, 0));
      }
      if (native !== undefined) {
        const fr = native.free[k];
        if (fr !== null && fr !== undefined) {
          file_push(fl, tab2, fr(s));
        }
      } else if (live > 0) {
        const sp = file_fresh(fl, "sp");   // parked: a same-class build reuses it
        file_push(fl, tab2, "u64 " + sp + " = term_loc(" + s + ");");
        fl.spares.push({ cls: cls_of(live), name: sp });
      }
      for (const v of drops_for(mine)) {
        drop_push(fl, tab2, v);
      }
      compile_term(fl, h, null, tab2, tgt, [...fields, ...rest], d);
    }
    if (arms.length === 1 && end === null && total === 1) {
      arm_emit(arms[0][1], arms[0][0], tab, armsets[0]);
      return;
    }
    for (let i = 0; i < arms.length; i++) {
      let cond: string;
      if (native !== undefined) {
        const c = native.cond[arms[i][0]];
        if (c === undefined) {
          throw new Error("tocl: no native test for a " + arms[i][0] + " match");
        }
        cond = c(s);
      } else {
        const ctr = fl.book.ctrs[arms[i][0]];
        const live = ctr === undefined ? 0 : ctr_get_quants(fl.book, ctr).filter((u) => u.$ !== "None").length;
        cond = "term_aux(" + s + ") == " + cid_reg(fl, arms[i][0], live);
      }
      let open = "} else if (" + cond + ") {";
      if (i === 0) {
        open = "if (" + cond + ") {";
      } else if (end === null && i === arms.length - 1 && arms.length === total) {
        open = "} else {";
      }
      file_push(fl, tab, open);
      const st = { seg: fl.seg, scope: fl.scope.slice(), loop: fl.loop, own: fl.own, spares: fl.spares.slice() };
      arm_emit(arms[i][1], arms[i][0], tab + 1, armsets[i]);
      fl.seg = st.seg; fl.scope = st.scope; fl.loop = st.loop; fl.own = st.own; fl.spares = st.spares;
    }
    if (end !== null) {
      file_push(fl, tab, "} else {");
      const st = { seg: fl.seg, scope: fl.scope.slice(), loop: fl.loop, own: fl.own, spares: fl.spares.slice() };
      for (const v of drops_for(endset!)) {
        drop_push(fl, tab + 1, v);
      }
      compile_term(fl, end, null, tab + 1, tgt, [hvar(s, 0), ...rest], d);
      fl.seg = st.seg; fl.scope = st.scope; fl.loop = st.loop; fl.own = st.own; fl.spares = st.spares;
    } else if (arms.length < total) {
      file_push(fl, tab, "} else {");
      file_push(fl, tab + 1, "err_post(e.mem, ERR_TAGS);");
      file_push(fl, tab + 1, "return " + (par_mode(fl) ? "TERM_HOLE" : "0") + ";");
    }
    file_push(fl, tab, "}");
  }

  const x = core.term_force(tm);
  switch (x.$) {
    case "Ann": {
      const e = compile_term(fl, x.x, x.T, tab, tgt, q, d);
      return e;
    }
    case "Var": {
      if (q.length === 0) {
        return compile_term_put(x.k);
      }
      const e = compile_term_apply(x.k, q);
      return e;
    }
    case "Ref": {
      const tld = fl.book.tlds[x.k];
      if (tld === undefined) {
        throw new Error("tocl: unknown name: " + x.k);
      }
      if (tld.$ === "ADT") {
        return compile_term_put("0");
      }
      const exprs = q.map((a) => compile_term(fl, a, null, tab, null, [], d));
      const intr = INTRINSICS[intr_low(x.k)];
      if (intr !== undefined) {
        if (exprs.length < intr.n) {
          throw new Error("tocl: a partial application of the intrinsic " + x.k);
        }
        let e = intr.e(fl, exprs.slice(0, intr.n));
        if (e.length > EXPR_COLS) {
          const fit = exprs.slice(0, intr.n).map((a) => local_fit(fl, tab, a));
          e = intr.e(fl, fit);
        }
        if (exprs.length > intr.n) {
          return compile_term_apply(e, exprs.slice(intr.n).map((a) => hvar(a, 0)));
        }
        return compile_term_put(e);
      }
      if (tld.v === null) {
        throw new Error("tocl: a live call into the unfilled assert " + x.k);
      }
      const live = def_get_params(fl.book, tld).filter(([, u]) => u.$ !== "None").length;
      const lp = fl.loop;
      if (tgt === "return" && lp !== null && lp.name === x.k && exprs.length === live) {
        const moves: Array<[string, string]> = [];
        for (let i = 0; i < exprs.length; i++) {
          if (exprs[i] !== lp.args[i]) {
            const t = file_fresh(fl, "t");
            file_push(fl, tab, "Term " + t + " = " + exprs[i] + ";");
            moves.push([lp.args[i], t]);
          }
        }
        for (const [p, t] of moves) {
          file_push(fl, tab, p + " = " + t + ";");
        }
        spare_flush(fl, tab);
        file_push(fl, tab, "continue;");
        return "";
      }
      if (exprs.length < live) {
        throw new Error("tocl: a partial application of the def " + x.k + " (no curried defs natively)");
      }
      ref_need(fl, x.k);
      const args  = exprs.slice(0, live);
      const extra = exprs.slice(live).map((a) => hvar(a, 0));
      const fact  = fl.facts.get(x.k);
      if (fact === undefined || !fact.tasked) {
        let e = "FUN_" + def_cname(fl, x.k) + "(e" + args.map((a) => ", " + a).join("") + ")";
        if (e.length > EXPR_COLS) {
          const fit = args.map((a) => local_fit(fl, tab, a));
          e = "FUN_" + def_cname(fl, x.k) + "(e" + fit.map((a) => ", " + a).join("") + ")";
        }
        if (extra.length > 0) {
          return compile_term_apply(e, extra);
        }
        return compile_term_put(e);
      }
      const gfid = fid_of(fl, x.k);
      if (extra.length === 0 && tgt === "return" && par_mode(fl)) {
        spare_flush(fl, tab);
        const tk = file_fresh(fl, "tk");   // tail: the callee inherits cont/idx, no frame
        if (fl.own) {
          fl.own = false;
          const co = file_fresh(fl, "co");
          const cn = file_fresh(fl, "cn");
          file_push(fl, tab, "Cls " + co + " = " + fid_cls(fl.seg.fid!) + ";");
          file_push(fl, tab, "Cls " + cn + " = " + fid_cls(gfid) + ";");
          file_push(fl, tab, "u64 " + tk + " = heap_swap(e, a, " + co + ", " + cn + ");");
          file_push(fl, tab, "e.mem[loc_at(" + tk + " + " + args.length + ")] = cont;");
          file_push(fl, tab, "e.mem[loc_at(" + tk + " + " + (args.length + 1) + ")] = fill_new(idx, 0);");
        } else {
          file_push(fl, tab, "u64 " + tk + " = task_node(e, " + gfid + ", cont, idx, 0);");
        }
        args.forEach((a, i) => file_push(fl, tab, "e.mem[loc_at(" + tk + " + " + i + ")] = " + a + ";"));
        file_push(fl, tab, "return term_task(" + gfid + ", " + tk + ");");
        return "";
      }
      const hole = cut_new(fl, tab, "call", gfid, "", args);
      if (extra.length > 0) {
        return compile_term_apply(hole, extra);
      }
      return compile_term_put(hole);
    }
    case "App": {
      const f = core.term_force(x.f);
      if (f.$ !== "Ann") {
        throw new Error("tocl: missing Ann on a call head");
      }
      const all = core.term_wnf(fl.book, f.T);
      if (all.$ !== "All") {
        throw new Error("tocl: a non-function call head");
      }
      const e = compile_term(fl, x.f, null, tab, tgt, all.q.$ === "None" ? q : [x.x, ...q], d);
      return e;
    }
    case "Ctr": {
      const adt = ty === null ? null : core.term_wnf(fl.book, ty);
      if (adt === null || adt.$ !== "ADT") {
        throw new Error("tocl: a Ctr without a datatype-typed Ann: " + x.k);
      }
      if (adt.k === "U32") {
        const u = core.u32_from_term(x);
        if (u !== null) {
          return compile_term_put(String(u) + "ull");
        }
      }
      const ctr = fl.book.ctrs[x.k];
      if (ctr === undefined) {
        throw new Error("tocl: unknown constructor: " + x.k);
      }
      const qs = ctr_get_quants(fl.book, ctr);
      const exprs: string[] = [];
      for (let j = 0; j < x.x.length; j++) {
        if (qs[j].$ !== "None") {
          exprs.push(compile_term(fl, x.x[j], null, tab, null, [], d));
        }
      }
      const native = NATIVES[adt.k];
      if (native !== undefined) {
        const fn = native.intr[x.k];
        if (fn === undefined || fn === null) {
          throw new Error("tocl: no native introduction for a computed " + x.k);
        }
        return compile_term_put(fn(exprs));
      }
      const cid = cid_reg(fl, x.k, exprs.length);
      if (exprs.length === 0) {
        return compile_term_put("term_ctor(" + cid + ", 0)");
      }
      const nd = ctr_pack(fl, tab, exprs);
      return compile_term_put("term_ctor(" + cid + ", " + nd + ")");
    }
    case "Lam": {
      const all = ty === null ? null : core.term_wnf(fl.book, ty);
      if (all === null || all.$ !== "All") {
        throw new Error("tocl: a Lam without a function-typed Ann");
      }
      if (all.q.$ === "None") {
        const e = compile_term(fl, x.f(hvar("0", d)), null, tab, tgt, q, d + 1);
        return e;
      }
      if (q.length === 0) {
        return compile_term_put(compile_lift(fl, tab, x, ty, d));
      }
      let name = compile_term(fl, q[0], null, tab, null, [], d);
      if (!IDENT.test(name)) {
        const alias = file_fresh(fl, x.k);
        file_push(fl, tab, "Term " + alias + " = " + name + ";");
        name = alias;
      }
      fl.scope.push(name);
      const body = x.f(hvar(name, d));
      if (!term_vars(body, d + 1, new Set()).has(name)) {
        drop_push(fl, tab, name);
      }
      const e = compile_term(fl, body, null, tab, tgt, q.slice(1), d + 1);
      return e;
    }
    case "Mat":
    case "Efq": {
      if (q.length === 0) {
        return compile_term_put(compile_lift(fl, tab, x, ty, d));
      }
      if (tgt === null) {
        const t = file_fresh(fl, "t");
        file_push(fl, tab, "Term " + t + " = 0;");
        const before = fl.segs.length;
        compile_term(fl, x, ty, tab, t, q, d);
        for (let i = before; i < fl.segs.length; i++) {
          if (fl.segs[i].cut !== null && fl.segs[i].cut!.kind !== "clo") {
            throw new Error("tocl: an expression-position match with a task call in an arm (restructure the source into statement form)");
          }
        }
        return t;
      }
      compile_term_match(x, ty);
      return "";
    }
    case "Let": {
      if (x.q.$ === "None") {
        const e = compile_term(fl, x.f(hvar("0", d)), null, tab, tgt, q, d + 1);
        return e;
      }
      const name = file_fresh(fl, x.k);
      const v = compile_term(fl, x.v, null, tab, null, [], d);
      file_push(fl, tab, "Term " + name + " = " + v + ";");
      fl.scope.push(name);
      const body = x.f(hvar(name, d));
      if (!term_vars(body, d + 1, new Set()).has(name)) {
        drop_push(fl, tab, name);
      }
      const e = compile_term(fl, body, null, tab, tgt, q, d + 1);
      return e;
    }
    case "Rwt": {
      const e = compile_term(fl, x.f, null, tab, tgt, q, d);
      return e;
    }
    case "Rfl":
    case "Typ":
    case "All":
    case "ADT":
    case "Eql": {
      return compile_term_put("0");
    }
    default: {
      throw new Error("tocl: cannot compile a " + x.$ + " node");
    }
  }
}

// Def
// ===

// compile_def: one def into its segment: a FUN function (a for(;;) when a
// self tail call exists) or a PAR Reply entry, plus whatever continuations
// and lifted lambdas its body mints.
export function compile_def(fl: File, k: core.Name): void {
  const tld = fl.book.tlds[k];
  if (tld === undefined || tld.$ !== "Def" || tld.v === null) {
    return;
  }
  if (INTRINSICS[intr_low(k)] !== undefined) {
    return;
  }
  if (tld.e === undefined) {
    throw new Error("tocl: unelaborated def " + k + ": run book_valid first");
  }
  const fact = fl.facts.get(k);
  if (fact === undefined) {
    throw new Error("tocl: def " + k + " compiled without facts");
  }
  fl.fresh = new Map();
  fl.defc  = def_cname(fl, k);
  fl.kn    = 0;
  const params: string[] = [];
  for (const [n, u] of def_get_params(fl.book, tld)) {
    if (u.$ !== "None") {
      params.push(file_fresh(fl, n));
    }
  }
  const seg = seg_new(fl, name_take(fl, (fact.tasked ? "PAR_" : "FUN_") + fl.defc), fact.tasked ? "par" : "fun", params, null);
  seg.loop = fact.selfTail;
  fl.seg    = seg;
  fl.scope  = params.slice();
  fl.own    = fact.tasked;
  fl.spares = [];
  fl.loop   = seg.loop ? { name: k, args: params } : null;
  const args: core.HTerm[] = params.map((p) => hvar(p, 0));
  compile_term(fl, tld.e, null, seg.loop ? 2 : 1, "return", args, 0);
}

// root_emit: FID_MAIN is the runtime's entry ABI. The user's main owns it
// when it is TASKED and answers a String; otherwise a wrapper owns it and
// shows the answer as a String for the harness (Bool/Nat/U32/Char).
function root_emit(fl: File): void {
  const main = fl.book.tlds["main"];
  if (main === undefined || main.$ !== "Def" || main.v === null) {
    throw new Error("tocl: a compiled program needs a main def with a body");
  }
  let tip = core.term_wnf(fl.book, main.T);
  for (let i = 0; i < main.n && tip.$ === "All"; i++) {
    if (tip.q.$ !== "None") {
      throw new Error("tocl: main must take no live parameters (the harness calls it with none)");
    }
    tip = core.term_wnf(fl.book, tip.B(hvar("~", i)));
  }
  const adt = core.term_wnf(fl.book, tip);
  const tk = adt.$ === "ADT" ? adt.k : "?";
  const SHOW: Record<string, (e: string) => string> = {
    String: (e) => e,
    Bool:   (e) => "bool_show(e, " + e + ")",
    Nat:    (e) => "nat_show(e, " + e + ")",
    U32:    (e) => "u32_show(e, " + e + ")",
    Char:   (e) => "chr_show(e, " + e + ")",
  };
  if (SHOW[tk] === undefined) {
    throw new Error("tocl: main must answer String, Bool, Nat, U32 or Char (got " + core.term_show(core.term_lower(tip)) + ")");
  }
  const fact = fl.facts.get("main");
  const tasked = fact !== undefined && fact.tasked;
  if (tasked && tk === "String") {
    ref_need(fl, "main");   // the user's entry is PAR_main and owns FID_MAIN
    return;
  }
  fl.cname.set("main", name_take(fl, tasked ? "main_v" : "main"));
  const seg = seg_new(fl, name_take(fl, "PAR_main"), "par", [], null);
  if (!tasked) {
    seg.lines.push(
      "  heap_free(e.mem, " + fid_cls(seg.fid!) + ", a);",
      "  return " + SHOW[tk]("FUN_" + def_cname(fl, "main") + "(e)") + ";");
  } else {
    const kseg = seg_new(fl, name_take(fl, "SEQ_main_show"), "seq", ["r_0"], null);
    kseg.lines.push(
      "  heap_free(e.mem, " + fid_cls(kseg.fid!) + ", a);",
      "  return " + SHOW[tk]("r_0") + ";");
    const vfid = fid_of(fl, "main");
    seg.lines.push(
      "  Cls co = " + fid_cls(seg.fid!) + ";",
      "  Cls cn = " + fid_cls(kseg.fid!) + ";",
      "  u64 fr = heap_swap(e, a, co, cn);",
      "  e.mem[loc_at(fr + 0)] = TERM_HOLE;",
      "  e.mem[loc_at(fr + 1)] = cont;",
      "  e.mem[loc_at(fr + 2)] = fill_new(idx, 1);",
      "  u64 tk = task_node(e, " + vfid + ", term_task(" + kseg.fid + ", fr), 0, 0);",
      "  return term_task(" + vfid + ", tk);");
  }
  ref_need(fl, "main");
}

// Finalize
// ========
//
// Resolve the cuts, newest first, so every child's frame build lands in its
// parent's text before the parent's own captures are scanned. A capture is
// exactly: a cut-scope local the continuation's text mentions (locals are
// unique per def family, so a word-boundary scan is exact).
function finalize(fl: File): void {
  for (let i = fl.segs.length - 1; i >= 0; i--) {
    const seg = fl.segs[i];
    const cut = seg.cut;
    if (cut === null) {
      continue;
    }
    const text = seg.lines.join("\n");
    const caps = cut.scope.filter((v) => new RegExp("\\b" + v + "\\b").test(text));
    seg.params = caps.concat(seg.params);
    seg.arity  = seg.params.length;
    const tabs = "  ".repeat(cut.tab);
    const out: string[] = [];
    if (cut.kind === "clo") {
      if (caps.length === 0) {
        out.push(tabs + "u64 " + cut.hole + " = 0;");
      } else {
        out.push(tabs + "u64 " + cut.hole + " = heap_alloc(e, cls_fit(" + caps.length + "));");
        caps.forEach((c, j) => out.push(tabs + "e.mem[loc_at(" + cut.hole + " + " + j + ")] = " + c + ";"));
      }
    } else {
      const fr = cut.hole + "f";
      if (cut.own) {
        out.push(tabs + "Cls " + fr + "o = " + fid_cls(cut.parent.fid!) + ";");
        out.push(tabs + "Cls " + fr + "n = " + fid_cls(seg.fid!) + ";");
        out.push(tabs + "u64 " + fr + " = heap_swap(e, a, " + fr + "o, " + fr + "n);");
        out.push(tabs + "e.mem[loc_at(" + fr + " + " + (caps.length + 1) + ")] = cont;");
        out.push(tabs + "e.mem[loc_at(" + fr + " + " + (caps.length + 2) + ")] = fill_new(idx, 1);");
      } else {
        out.push(tabs + "u64 " + fr + " = task_node(e, " + seg.fid + ", cont, idx, 1);");
      }
      caps.forEach((c, j) => out.push(tabs + "e.mem[loc_at(" + fr + " + " + j + ")] = " + c + ";"));
      out.push(tabs + "e.mem[loc_at(" + fr + " + " + caps.length + ")] = TERM_HOLE;");
      const kcont = "term_task(" + seg.fid + ", " + fr + ")";
      if (cut.kind === "call") {
        const tk = cut.hole + "t";
        out.push(tabs + "u64 " + tk + " = task_node(e, " + cut.callee + ", " + kcont + ", " + caps.length + ", 0);");
        cut.args.forEach((a, j) => out.push(tabs + "e.mem[loc_at(" + tk + " + " + j + ")] = " + a + ";"));
        out.push(tabs + "return term_task(" + cut.callee + ", " + tk + ");");
      } else {
        out.push(tabs + "return clos_call(e, " + cut.fn + ", " + cut.args[0] + ", " + kcont + ", " + caps.length + ");");
      }
    }
    cut.parent.lines[cut.at] = out.join("\n");
  }
}

// Assembly
// ========

function guard_need(text: string): number {
  let n = 0;
  for (const [re, c] of ALLOC_COST) {
    const m = text.match(re);
    if (m !== null) {
      n += m.length * c;
    }
  }
  return n;
}

function seg_proto(seg: Seg): string {
  if (seg.region === "fun") {
    return "static Term " + seg.name + "(Env e" + seg.params.map((p) => ", Term " + p).join("") + ");";
  }
  return "Reply " + seg.name + "(Env e, u64 a, Term cont, u32 idx);";
}

function seg_text(seg: Seg): string {
  const body: string[] = [];
  if (seg.region !== "fun") {
    const need = guard_need(seg.lines.join("\n"));
    if (need > 0) {
      body.push("  if (!heap_guard(e.mem, " + need + ")) {");
      body.push("    return TERM_NEED;");
      body.push("  }");
    }
    seg.params.forEach((p, i) => body.push("  Term " + p + " = e.mem[loc_at(a + " + i + ")];"));
  }
  if (seg.loop) {
    body.push("  for (;;) {");
  }
  body.push(...seg.lines);
  if (seg.loop) {
    body.push("  }");
  }
  const text = body.join("\n");
  function dead(v: string): boolean {
    return !new RegExp("\\b" + v + "\\b").test(text);
  }
  const out: string[] = [];
  if (seg.region === "fun") {
    out.push("static Term " + seg.name + "(Env e" + seg.params.map((p) => ", Term " + p).join("") + ") {");
    if (dead("e")) {
      out.push("  (void)e;");
    }
  } else {
    out.push("Reply " + seg.name + "(Env e, u64 a, Term cont, u32 idx) {");
    for (const v of ["e", "a", "cont", "idx"]) {
      if (dead(v)) {
        out.push("  (void)" + v + ";");
      }
    }
  }
  out.push(...body);
  out.push("}");
  return out.join("\n");
}

function gen_defs(fl: File): string {
  const entries = fl.segs.filter((s) => s.fid !== null);
  const out: string[] = [];
  let maxar = 1;
  for (const s of entries) {
    maxar = Math.max(maxar, s.arity);
  }
  if (maxar > 255) {
    throw new Error("tocl: an entry arity beyond MAX_ARITY's 255 cap");
  }
  out.push("#define MAX_ARITY " + maxar);
  out.push("");
  const seen = new Set<string>();
  const cmacs: Array<[string, number, number]> = [];
  for (const [k, c] of fl.cids) {
    const mac = "CID_" + sanitize(k).toUpperCase();
    if (seen.has(mac)) {
      throw new Error("tocl: two constructors share the C macro " + mac);
    }
    seen.add(mac);
    cmacs.push([mac, c.id, c.arity]);
    if (c.arity > 255) {
      throw new Error("tocl: constructor " + k + " has more than 255 live fields");
    }
  }
  const cwide = Math.max(...cmacs.map(([mac]) => mac.length));
  for (const [mac, id] of cmacs) {
    out.push("#define " + mac.padEnd(cwide) + " " + id);
  }
  out.push("");
  const fwide = Math.max(...entries.map((s) => s.fid!.length));
  entries.forEach((s, i) => {
    if (seen.has(s.fid!)) {
      throw new Error("tocl: two entries share the C macro " + s.fid);
    }
    seen.add(s.fid!);
    out.push("#define " + s.fid!.padEnd(fwide) + " " + i);
  });
  out.push("");
  out.push("INLINE u32 fid_arity(Fid fid) {");
  out.push("  switch (fid) {");
  for (const s of entries) {
    out.push("    case " + (s.fid! + ":").padEnd(fwide + 1) + " return " + s.arity + ";");
  }
  out.push("    default: return 0;");
  out.push("  }");
  out.push("}");
  out.push("");
  out.push("INLINE bool fid_forks(Fid fid) {");
  out.push("  (void)fid;");
  out.push("  return false;");
  out.push("}");
  out.push("");
  out.push("INLINE bool fid_bangs(Fid fid) {");
  out.push("  (void)fid;");
  out.push("  return false;");
  out.push("}");
  out.push("");
  out.push("INLINE u32 cid_arity(Cid cid) {");
  out.push("  switch (cid) {");
  for (const [mac, , arity] of cmacs) {
    if (arity > 0) {
      out.push("    case " + (mac + ":").padEnd(cwide + 1) + " return " + arity + ";");
    }
  }
  out.push("    default: return 0;");
  out.push("  }");
  out.push("}");
  return out.join("\n");
}

function gen_code(fl: File): string {
  const funs = fl.segs.filter((s) => s.region === "fun");
  const pars = fl.segs.filter((s) => s.region === "par");
  const seqs = fl.segs.filter((s) => s.region === "seq");
  const bodies =
    "// Fun\n// ===\n\n" +
    funs.map(seg_text).join("\n\n") +
    "\n\n// Par\n// ===\n\n" +
    pars.map(seg_text).join("\n\n") +
    "\n\n// Seq\n// ===\n\n" +
    seqs.map(seg_text).join("\n\n");
  const protos = fl.segs.map(seg_proto).join("\n");
  const entries = fl.segs.filter((s) => s.fid !== null);
  const fwide = Math.max(...entries.map((s) => s.fid!.length));
  const parcall: string[] = [];
  parcall.push("INLINE Reply fid_call(Env e, Fid fid, Loc a, Term cont, u32 idx) {");
  parcall.push("  switch (fid) {");
  for (const s of entries) {
    parcall.push("    case " + (s.fid! + ":").padEnd(fwide + 1) + " return " + s.name + "(e, a, cont, idx);");
  }
  parcall.push("    default: {");
  parcall.push("      err_post(e.mem, ERR_FIDS);");
  parcall.push("      return TERM_HOLE;");
  parcall.push("    }");
  parcall.push("  }");
  parcall.push("}");
  return protos + "\n\n" + bodies + "\n\n" + parcall.join("\n");
}

// Book
// ====

// compile_book: a checked book into one standalone C program: the runtime
// template with its two markers replaced by the program's tables and code.
export function compile_book(book: core.Book): string {
  const root: Seg = { name: "", fid: null, region: "fun", lines: [], params: [], arity: 0, cut: null, loop: false };
  const fl: File = {
    book, segs: [], seg: root, fresh: new Map(), scope: [], loop: null,
    own: false, spares: [], defc: "", kn: 0, facts: facts_build(book), done: new Set(), queue: [],
    cids: new Map(), names: new Set(), cname: new Map(),
  };
  cid_reg(fl, "Tuple", 2);   // the runtime ABI: CID_TUPLE 0, CID_SNIL 1, CID_SCON 2
  cid_reg(fl, "SNil", 0);
  cid_reg(fl, "SCon", 2);
  cmp_cids(fl);              // Cmp in runtime.c names CID_LT/EQ/GT
  root_emit(fl);
  while (fl.queue.length > 0) {
    compile_def(fl, fl.queue.shift()!);
  }
  finalize(fl);
  // the markers are whole lines (the template's header also SPEAKS of them)
  const out = TEMPLATE.replace(/^\/\/GEN:DEFS\/\/$/m, gen_defs(fl)).replace(/^\/\/GEN:CODE\/\/$/m, gen_code(fl));
  return out;
}
