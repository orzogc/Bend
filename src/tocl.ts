
import { readFileSync } from "fs";
import { ADT, All, Ann, App, Book, Ctr, Def, Emp, HTerm, Lam, Let,
  Lone, Mat, Name, PMap, Quant, Ref, Var, pmap_get, pmap_set,
  pmap_union, tele_unbind, term_force, term_higher, term_lower,
  term_strip, term_wnf, u32_from_term } from "./core.ts";

// Types
// =====

type Unbox = "f32" | "u32" | null;

type Seg = {
  fid:    string;
  def:    Name;
  lines:  string[];
  params: string[];
  frame: { pop: number; base: number } | null;
  refs:   Set<string>;
  dead?:  boolean;
  spin?:  boolean;
  unbox?: Unbox[];
};

type Spine = {
  h:    HTerm;
  t:    HTerm;
  all:  HTerm[];
  args: HTerm[];
};

type Capture = { p: Probe; q: Quant; A: HTerm | null };

type Carb = {
  src:    Book;
  book:   Book;
  mint:   Map<Name, boolean>;
  kn:     number;
  done:   Set<Name>;
  queue:  Name[];
  inl:    Map<Name, HTerm | null>;
  inlrun: Set<Name>;
  bangs:  Set<Name>;
  brw:    Map<Name, boolean[]>;
  clo:    boolean;
};

type Scratch = {
  spares: { words: number; name: string; z: boolean }[];
  fresh: Map<string, number>;
  uses:  Map<Probe, Bind>;
  local: Set<string>;
  brwl:  Set<string>;
  fusing: Set<Name>;
};

type File = Scratch & {
  book:  Book;
  segs:  Seg[];
  seg:   Seg;
  tab:   number;
  cb:    Carb;
  cids:  Map<string, { arity: number; packed: boolean }>;
  shr:   Set<string>;
  tabs:  Map<string, number>;
  spins: string[];
};

type Native = {
  intr:  Record<Name, string | ((xs: string[], ts: HTerm[]) => string)>;
  elim?: Record<Name, string[]>;
  cond: Record<Name, string>;
};

type Of<K> = Extract<HTerm, { $: K }>;

// Constants
// =========

const TEMPLATE =
  readFileSync(new URL("./runtime.c", import.meta.url), "utf8");

const CLO_APPLY = "Clo.apply";

// Natives
// =======

function tpl(t: string): (xs: string[]) => string {
  const ps = t.split(/\$(\d)/);
  return (xs) => ps.map((p, i) => (i % 2 === 1 ? xs[+p] : p)).join("");
}

const NATIVES: Record<Name, Native> = {
  Nat: {
    intr: {
      Zero: "0",
      Succ: ([p], [tm]) => {
        let n = 1;
        let t = term_strip(tm);
        while (t.$ === "Ctr" && t.k === "Succ" && t.x.length === 1) {
          n += 1;
          t = term_strip(t.x[0]);
        }
        if (t.$ === "Ctr" && t.k === "Zero" && t.x.length === 0) {
          return n + "ull";
        }
        return "nat_succ(e, " + p + ")";
      },
    },
    elim: { Succ: ["($0 - 1)"] },
    cond: { Zero: "$0 == 0", Succ: "$0 != 0" },
  },
  Bool: {
    intr: { False: "0", True: "1" },
    cond: { False: "$0 == 0", True: "$0 != 0" },
  },
  Cmp: {
    intr: { LT: "0", EQ: "1", GT: "2" },
    cond: { LT: "$0 == 0", EQ: "$0 == 1", GT: "$0 == 2" },
  },
  Array: {
    intr: {
      ALeaf: "flat_new(e, 0, $0)",
      ANode: "flat_node(e, $0, $1)",
    },
    elim: {
      ALeaf: ["flat_take(e, $0)"],
      ANode: ["flat_half(e, $0, 0)", "flat_rest(e, $0)"],
    },
    cond: {
      ALeaf: "term_aux($0) == 0",
      ANode: "term_aux($0) != 0",
    },
  },
};

const ARR_NATIVE = { ...NATIVES.Array,
  intr: { ...NATIVES.Array.intr, ALeaf: "blk_leaf(e, $0)" } };

// Intrinsics
// ==========

type Intr = {
  e?:     (a: string[], fl: File) => string;
  call?:  boolean;
  parts?: (shr: boolean) => string[];
};

const blk_op = (read: string): Intr => ({
  parts: (shr) =>
    [shr ? "flat_cow(e, $0)" : "$0", read],
});

const INTRINSICS: Record<string, Intr> = {
  array_swap:  blk_op("blk_give(e, $3, $4, $1, $2)"),
  array_get:   blk_op("flat_read(e, $3, $1)"),
  array_new:   { e: tpl("flat_new(e, $0, $1)"), call: true },
  array_copy:  { parts: () => ["term_keep(e, $0)", "$2"] },
  u32_copy:    { e: ([a], fl) => {
    const w  = expr_alias(fl, a, "w");
    const hs = [w, w].map((v) => ctr_build(fl, "Tuple", [v, "0ull"]));
    return ctr_build(fl, "Tuple", hs);
  }, call: true },
};

[NATIVES, INTRINSICS].forEach((t) => Object.setPrototypeOf(t, null));

const WORDS = ["u32_div", "u32_mod", "u32_shln", "u32_shrn", "f32_to_u32",
  "f32_sqrt", "u32_inc", "u32_not", "u32_shl", "u32_shr", "u32_is_zero",
  "u32_to_f32", "u32_to_nat", "u32_from_nat", "bool_or",
  "bool_xor", "u32_and", "u32_or", "u32_xor", "u32_add", "u32_sub",
  "u32_mul", "u32_cmp", "f32_add", "f32_sub", "f32_mul", "f32_div"];

for (const [c, o] of [["eq", "=="], ["ne", "!="], ["lt", "<"], ["le", "<="],
  ["gt", ">"], ["ge", ">="]]) {
  WORDS.push(`u32_is_${c}`);
  INTRINSICS[`f32_is_${c}`] = { e: tpl(`F32_CMP($0, ${o}, $1)`), call: false };
}

WORDS.forEach((k, i) => {
  INTRINSICS[k] = { e: (xs) => `${k}(${xs.join(", ")})`, call: i < 6 };
});

// Names
// =====

function sanitize(k: string): string {
  return k.replace(/[^A-Za-z0-9_]/g, "_");
}

function local_new(fl: File, k: Name): string {
  const base = sanitize(k);
  const n = fl.fresh.get(base) ?? 0;
  fl.fresh.set(base, n + 1);
  const name = base + "_" + n;
  fl.local.add(name);
  return name;
}

function die(m: string): never {
  throw new Error("tocl: " + m + " (report this case)");
}

// Term
// ====

type Probe = Of<"Var">;

type HApp = Of<"App">;

let PIDN = 0;

function probe(k: Name): Probe {
  return Var(k, (PIDN += 1)) as Probe;
}

const DUMMY: HTerm = probe("~");

type HBinder = Of<"Lam" | "Let">;

function open_of(t: HBinder): { p: Probe; b: HTerm } {
  const p = probe(t.k);
  return { p, b: t.f(p) };
}

type Dom = [Quant, Name, HTerm];

const q_live = (q: Quant): boolean => q.$ !== "None";

const dom_live = ([q]: Dom): boolean => q_live(q);

function live_doms(book: Book, tld: Def): Dom[] {
  return tele_unbind(book, tld.T).doms.slice(0, tld.n).filter(dom_live);
}

function term_spine(book: Book, tm: HTerm): Spine {
  const apps: HApp[] = [];
  let h = tm;
  let c = term_force(tm);
  while (c.$ === "Ann" || c.$ === "App") {
    if (c.$ === "App") {
      apps.push(c);
      h = c.f;
    }
    c = term_force(c.$ === "App" ? c.f : c.x);
  }
  apps.reverse();
  const tld = c.$ === "Ref" ? book.tlds[c.k] : undefined;
  let live: (i: number) => boolean;
  if (tld?.$ === "Def") {
    const qs = tele_unbind(book, tld.T).doms;
    live = (i) => i >= qs.length || q_live(qs[i][0]);
  } else {
    live = (i) => app_live(book, apps[i].f);
  }
  const all = apps.map((a) => a.x);
  return { h, t: c, all, args: all.filter((_, i) => live(i)) };
}

function app_live(book: Book, f: HTerm): boolean {
  const all = all_of(book, ann_of(f));
  return all === null || q_live(all.q);
}

const mat_head = (t: HTerm): boolean => t.$ === "Mat" || t.$ === "Efq";

function eta(t: HTerm): HTerm {
  return Lam("x", 0, (y: HTerm) => App(t, y));
}

function term_kids(book: Book, tm: HTerm): HTerm[] {
  const t = term_force(tm);
  switch (t.$) {
    case "Ann": return [t.x];
    case "Lam": return [open_of(t).b];
    case "Let": return q_live(t.q) ? [t.v, open_of(t).b] : [open_of(t).b];
    case "App": {
      const m = term_spine(book, t);
      return [m.h, ...m.args];
    }
    case "Ctr": return term_const(t) ? [] : ctr_flds(book, t.k, t.x);
    case "Mat": return [t.h, t.m];
    case "Rwt": return [t.f];
    default:    return [];
  }
}

function term_any(book: Book, t: HTerm,
  p: (s: HTerm) => boolean): boolean {
  const s = term_force(t);
  return p(s) || term_kids(book, s).some((x) => term_any(book, x, p));
}

function term_const(t: HTerm): boolean {
  const s = term_strip(t);
  return s.$ === "Ctr" && s.x.every(term_const);
}

const probe_of = (t: HTerm): Probe => term_force(t) as Probe;

type UMap = PMap<number>;

const USE0 = Emp<number>();

function uses_at(u: UMap, p: Probe): number {
  return pmap_get(u, p.i) ?? 0;
}

function term_uses(cb: Carb, tm: HTerm): UMap {
  const t = term_force(tm);
  switch (t.$) {
    case "Var": {
      const p = probe_of(t);
      return p === DUMMY ? USE0 : pmap_set(USE0, p.i, 1);
    }
    case "Mat": return pmap_union(term_uses(cb, t.h),
      term_uses(cb, t.m), Math.max);
    default: {
      const ck   = call_kind(cb.book, t);
      const lent = ck && cb.brw.get(ck.k);
      return term_kids(cb.book, t).reduce((u, x, j) =>
        lent?.[j - 1] === true ? u
          : pmap_union(u, term_uses(cb, x), (a, b) => a + b),
        USE0);
    }
  }
}

type Call = {
  k:    Name;
  args: HTerm[];
  bang: boolean;
};

function intr_of(k: Name): Intr | undefined {
  return k.includes(".")
    ? INTRINSICS[k.toLowerCase().replace(/\./g, "_")] : undefined;
}

function call_kind(book: Book, t: HTerm): Call | null {
  const m = term_spine(book, t);
  let dyn = m.t.$ === "Var" && m.args.length > 0;
  if (m.t.$ === "Ref" && intr_of(m.t.k) === undefined) {
    const tld = book.tlds[m.t.k];
    if (def_live(tld)) {
      const live = live_doms(book, tld).length;
      if (m.args.length === live) {
        return { k: m.t.k, args: m.args, bang: m.t.b === true };
      }
      dyn = m.args.length > live;
    }
  }
  if (!dyn) {
    return null;
  }
  let f = term_force(t);
  while (f.$ === "Ann" || (f.$ === "App" && !app_live(book, f.f))) {
    f = term_force(f.$ === "App" ? f.f : f.x);
  }
  const a = f as HApp;
  return { k: CLO_APPLY, args: [a.f, a.x], bang: false };
}

function is_call(cb: Carb, t: HTerm): boolean {
  return call_kind(cb.book, t) !== null;
}

function has_call(cb: Carb, t: HTerm): boolean {
  return term_any(cb.book, t, (s) => is_call(cb, s));
}

function ann_of(t: HTerm): HTerm | null {
  const v = term_force(t);
  return v.$ === "Ann" ? v.T : null;
}

type HAll = Of<"All">;

type HAdt = Of<"ADT">;

function wnf_of(book: Book, ty: HTerm | null): HTerm | null {
  return ty && term_wnf(book, ty);
}

function all_of(book: Book, ty: HTerm | null): HAll | null {
  const w = wnf_of(book, ty);
  return w?.$ === "All" ? w : null;
}

function tele_app(book: Book, T: HTerm, args: HTerm[]): HTerm {
  return args.reduce((T2, a) => (all_of(book, T2) as HAll).B(a), T);
}

// Fork
// ====

type HLet = Of<"Let">;

const HOLES: HTerm[] = [];

function hole(j: number): HTerm {
  return (HOLES[j] ??= probe("*"));
}

function let_chain(t: HTerm, n: number,
  book: Book | null): { ls: HLet[]; rest: HTerm } {
  const ls: HLet[] = [];
  let rest = t;
  while (ls.length < n) {
    const l = term_strip(rest);
    if (l.$ !== "Let" || (book && call_kind(book, l.v) === null)) {
      break;
    }
    ls.push(l);
    rest = l.f(hole(ls.length - 1));
  }
  return { ls, rest };
}

type HLam = Of<"Lam">;

type Forked = { h: HLam; c: Of<"Ctr"> };

function fork_of(t: HTerm): Forked | null {
  const s = term_strip(t);
  if (s.$ !== "App") {
    return null;
  }
  const f = term_strip(s.f);
  const c = term_strip(s.x);
  if (f.$ !== "Mat" || f.k !== "Both"
    || c.$ !== "Ctr" || c.k !== "Both" || c.x.length !== 2) {
    return null;
  }
  const h = term_strip(f.h);
  return h.$ === "Lam" ? { h, c } : null;
}

function fork_span(t: HTerm): number {
  const o = fork_of(t);
  if (o === null) {
    return 0;
  }
  const b = o.h.f(DUMMY);
  const d = fork_span(App(b, o.c.x[1]));
  if (d !== 0) {
    return 1 + d;
  }
  return term_strip(b).$ === "Lam" ? 2 : 0;
}

function fork_grow(t: HTerm, j: number): HTerm {
  const { h, c } = fork_of(t) as Forked;
  return Let(h.k, h.i, c.x[0], (a) => {
    if (j > 2) {
      return fork_grow(App(h.f(a), c.x[1]), j - 1);
    }
    const g = term_strip(h.f(a)) as HLam;
    return Let(g.k, g.i, c.x[1], g.f, g.s);
  }, h.s);
}

function call_ok(cb: Carb, t: HTerm, n: number): Call | null {
  const ck = call_kind(cb.book, t);
  if (ck === null || ck.args.length < n) {
    return null;
  }
  const h = ck.args.length - n;
  if (!ck.args.slice(h).every((a, j) => term_strip(a) === hole(j))) {
    return null;
  }
  return ck.args.slice(0, h).every((a) => !has_call(cb, a)) ? ck : null;
}

// Ctr
// ===

function ctr_tail(book: Book, ctr: Ctr): Dom[] {
  const doms = tele_unbind(book, ctr.T).doms;
  return doms.slice(doms.length - ctr.n);
}

function ctr_doms(book: Book, ctr: Ctr): HTerm[] {
  return ctr_tail(book, ctr).filter(dom_live).map(([, , A]) => A);
}

function ty_w32(book: Book, A: HTerm | null): boolean {
  const t = wnf_of(book, A);
  if (t?.$ === "ADT") {
    return t.k === "U32" || t.k === "Bool" || t.k === "Char";
  }
  return ty_f32(book, A);
}

function ctr_scalar1(book: Book, k: Name): boolean {
  const ctr = book.ctrs[k];
  const fields = ctr === undefined ? [] : ctr_doms(book, ctr);
  return fields.length === 1 && ty_w32(book, fields[0]);
}

function ctr_flds(book: Book, k: Name, xs: HTerm[]): HTerm[] {
  const ctr = book.ctrs[k];
  const qs = ctr && ctr_tail(book, ctr).map(([q]) => q);
  return xs.filter((_, j) => qs?.[j] === undefined || q_live(qs[j]));
}

function ty_f32(book: Book, A: HTerm | null): boolean {
  const t = wnf_of(book, A);
  return t?.$ === "Ref" && t.k === "F32";
}

function native_of(book: Book, adt: HAdt): Native | undefined {
  if (adt.k === "U32") {
    die("a structural view of a machine word");
  }
  if (adt.k !== "Array" || ty_w32(book, adt.x[0])) {
    return NATIVES[adt.k];
  }
  if (["ADT", "All"].includes(term_wnf(book, adt.x[0]).$)) {
    return ARR_NATIVE;
  }
  die("an open Array element type");
}

function adt_triv(book: Book, A: HTerm | null): boolean {
  const adt = wnf_of(book, A);
  if (adt?.$ !== "ADT") {
    return ty_f32(book, A);
  }
  if (adt.k === "U32" || adt.k === "Char" || adt.k === "Nat") {
    return true;
  }
  const tld = book.tlds[adt.k];
  return tld?.$ === "ADT" && tld.c.every((c) =>
    ctr_doms(book, c).length === 0 || ctr_scalar1(book, c.k));
}

// Defunnize
// =========

type Env = Map<HTerm, HTerm>;

type Open = (env: Env) => HTerm;

type Kont = (caps: Capture[], x: Open) => Open;

const PASS: Kont = (_c, x) => x;

const EMPTY: Env = new Map();

function lift(t: HTerm): Open {
  return (env) => env.get(t) ?? t;
}

function app_caps(cs: Capture[], f: Open): Open {
  return (env) => cs.reduce((c, b) => App(c, env.get(b.p) ?? b.p), f(env));
}

function ret_of(cb: Carb, t: HTerm): HTerm {
  const s = term_force(t);
  if (s.$ === "Ann") {
    return s.T;
  }
  if (s.$ === "Let") {
    return ret_of(cb, s.f(DUMMY));
  }
  const m = term_spine(cb.book, s);
  const tld = m.t.$ === "Ref" ? cb.book.tlds[m.t.k] : undefined;
  const T = tld?.$ === "Def" ? tld.T
    : ann_of(m.h) ?? die("a minted definition without a result type");
  return tele_app(cb.book, T, m.all);
}

function mint(cb: Carb, def: Name, stem: string, scope: Capture[],
  seq: boolean, tail: number, build: () => Open, ret: HTerm | null = null,
  extra = 0): Open {
  cb.kn += 1;
  const name = def + "$" + stem + cb.kn;
  const body = build();
  const bt   = body(EMPTY);
  const u    = term_uses(cb, bt);
  const kept = scope.filter((c, i) =>
    i >= scope.length - tail || !q_live(c.q) || uses_at(u, c.p) > 0);
  const T = kept.reduceRight((R, c, i) => All(c.q, c.p.k, i,
    c.A ?? die(`a minted capture without a type: ${name} ${c.p.k}`),
    (_x) => R), ret ?? ret_of(cb, bt));
  const lams = kept.reduceRight<Open>((rest, c, i) =>
    (env) => Lam(c.p.k, i, (x) => rest(new Map(env).set(c.p, x))), body);
  const fn = lams(EMPTY);
  cb.book.tlds[name] =
    { $: "Def", n: kept.length + extra, T, v: fn, e: fn };
  cb.mint.set(name, seq);
  return app_caps(kept.slice(0, kept.length - tail), lift(Ref(name)));
}

// Carbonize
// =========

function carbonize(cb: Carb, def: Name, tld: Def, mint_all = false): HTerm {
  const cut_at = (s: HTerm) =>
    is_call(cb, s) && inl_at(cb, s) === null;
  const has_cut = (t: HTerm) => term_any(cb.book, t, cut_at);
  function bound(caps: Capture[], l: HLet, v: Open,
    rest: (caps: Capture[], body: HTerm) => Open,
    cuts = false): Open {
    const bd = { p: probe(l.k), q: l.q, A: ann_of(v(EMPTY)) };
    const c2 = [...caps, bd];
    const go = () => rest(c2, l.f(bd.p));
    const body = cuts ? mint(cb, def, "k", c2, true, 1, go) : go();
    return (env) => Let(l.k, l.i, v(env), (x) => cuts
      ? App(body(env), x)
      : body(new Map(env).set(bd.p, x)), l.s, l.q);
  }
  function apps(caps: Capture[], t: HTerm, hf: boolean,
    k: Kont): Open {
    type Fill = (caps: Capture[],
      rb: (f: Open) => Open) => Open;
    const m = term_spine(cb.book, t);
    const go = (u: HTerm, k2: Fill): Open => {
      const s = term_force(u);
      if (s.$ === "Ann") {
        return go(s.x, (c2, rb) => k2(c2, (f) => {
          const g = rb(f);
          return (env) => Ann(g(env), s.T, s.s);
        }));
      }
      if (s.$ === "App") {
        const app: Fill = (c2, rb) => expr(c2, s.x, null,
          (c3, x) => k2(c3, (f) => {
            const g = rb(f);
            return (env) => App(g(env), x(env), s.s);
          }));
        if (hf || !is_call(cb, s.f)) {
          return go(s.f, app);
        }
        return expr(caps, s.f, null, (c2, g) => app(c2, () => g));
      }
      return k2(caps, (f) => f);
    };
    return go(t, (c2, rb) =>
      k(c2, rb(hf ? func(c2, m.t, null, m.args.length) : lift(m.t))));
  }
  function many(caps: Capture[], n: number,
    each: (caps: Capture[], j: number, k: Kont) => Open,
    k: (caps: Capture[], xs: Open[]) => Open): Open {
    const go = (c2: Capture[], j: number, xs: Open[]): Open => {
      if (j === n) {
        return k(c2, xs);
      }
      return each(c2, j, (c3, x) => go(c3, j + 1, [...xs, x]));
    };
    return go(caps, 0, []);
  }
  function func(caps: Capture[], t: HTerm, ty: HTerm | null,
    left: number): Open {
    const s = term_force(t);
    const x = term_strip(t);
    if (x.$ !== "Lam" && !mat_head(x)) {
      if (left === 0) {
        return leaf(caps, s);
      }
      const T = ty ?? ann_of(s) ?? die("an untyped point-free arm");
      return func(caps, Ann(eta(s), T), null, left);
    }
    if (left === 0 && s.$ !== "Ann") {
      return expr(caps, s, ty, PASS);
    }
    switch (s.$) {
      case "Ann": {
        const g = func(caps, s.x, s.T, left);
        return (env) => Ann(g(env), s.T, s.s);
      }
      case "Lam": {
        const all  = all_of(cb.book, ty);
        const p    = probe(s.k);
        const cap  = { p, q: all?.q ?? Lone(), A: all?.A ?? null };
        const B    = all && all.B(DUMMY);
        const body = func([...caps, cap], s.f(p), B,
          left - (q_live(cap.q) ? 1 : 0));
        return (env) => Lam(s.k, s.i, (y) => body(new Map(env).set(p, y)),
          s.s);
      }
      case "Mat": {
        const ctr = cb.book.ctrs[s.k];
        const fs  = ctr === undefined ? 0 : ctr_doms(cb.book, ctr).length;
        const h = func(caps, s.h, null, fs + left - 1);
        const m = func(caps, s.m, null, left);
        return (env) => Mat(s.k, h(env), m(env), s.s);
      }
      default: {
        return lift(s);
      }
    }
  }
  function leaf(caps: Capture[], t: HTerm): Open {
    const s = term_strip(t);
    if (s.$ === "Let") {
      if (!q_live(s.q)) {
        return leaf(caps, s.f(s.v));
      }
      if (cut_at(s.v)) {
        return apps(caps, s.v, false, (c2, c) => {
          if (term_strip(s.f(hole(0))) === hole(0)) {
            return c;
          }
          return bound(c2, s, c, leaf, true);
        });
      }
      return expr(caps, s.v, null, (c2, v) => bound(c2, s, v, leaf));
    }
    const n = fork_span(s);
    if (n >= 2) {
      return fork(caps, fork_grow(s, n) as HLet, n);
    }
    const got = inl_at(cb, t);
    if (got !== null) {
      return leaf(caps, got);
    }
    const hf = mat_head(term_spine(cb.book, t).t) && !mat_head(s);
    if (hf || is_call(cb, t)) {
      return apps(caps, t, hf, PASS);
    }
    return expr(caps, t, null, PASS);
  }
  function fork(caps: Capture[], s: HLet, n: number): Open {
    const { ls, rest } = let_chain(s, n, null);
    let jt = rest;
    for (let g; (g = inl_at(cb, jt)) !== null;) {
      jt = g;
    }
    const jc    = call_ok(cb, jt, n);
    const whole = ls.every((l) => is_call(cb, l.v));
    const chain = (c2: Capture[], j: number, vs: Open[],
      t: HTerm): Open => {
      if (j === n) {
        if (!whole || (jc !== null && cb.mint.get(jc.k) !== true)) {
          return leaf(c2, t);
        }
        return app_caps(c2.slice(-n),
          mint(cb, def, "j", c2, false, n, () => leaf(c2, t)));
      }
      const l = term_strip(t) as HLet;
      const cuts = !whole && is_call(cb, vs[j](EMPTY));
      return bound(c2, l, vs[j], (c3, b) => chain(c3, j + 1, vs, b), cuts);
    };
    return many(caps, n, (c2, j, kx) => {
      if (is_call(cb, ls[j].v)) {
        return apps(c2, ls[j].v, false, kx);
      }
      return expr(c2, ls[j].v, null, kx);
    }, (c2, vs) => chain(c2, 0, vs, s));
  }
  function expr(caps: Capture[], t: HTerm, ty: HTerm | null,
    k: Kont): Open {
    if (term_const(t)) {
      return k(caps, lift(t));
    }
    const s = term_force(t);
    if (s.$ === "Ann") {
      return expr(caps, s.x, s.T, (c2, x) =>
        k(c2, (env) => Ann(x(env), s.T, s.s)));
    }
    const got = inl_at(cb, s);
    if (got !== null) {
      return expr(caps, got, ty, k);
    }
    if (is_call(cb, s)) {
      return apps(caps, s, false, (c2, c) => {
        const cx: Open = ty === null ? c : (env) => Ann(c(env), ty);
        const l = Let("h", 0, s, (x) => x) as HLet;
        return bound(c2, l, cx, (c3, b) => k(c3, lift(b)), true);
      });
    }
    switch (s.$) {
      case "App": {
        const m  = term_spine(cb.book, s);
        const hf = mat_head(m.t);
        if (hf && (mint_all || has_cut(m.t))) {
          const T = ann_of(m.h) ?? die("an untyped applied match");
          const g = mint(cb, def, "m", caps, false, 0,
            () => func(caps, m.t, T, m.args.length), T, m.all.length);
          return expr(caps, m.all.reduce((f, x) => App(f, x), g(EMPTY)),
            ty, k);
        }
        if (hf || m.t.$ === "Ref" || m.t.$ === "Var") {
          return apps(caps, s, hf, k);
        }
        die("an application headed by a " + m.t.$ + " inside an expression");
      }
      case "Ctr": {
        return many(caps, s.x.length,
          (c2, j, kx) => expr(c2, s.x[j], null, kx), (c2, xs) =>
          k(c2, (env) => Ctr(s.k, xs.map((x) => x(env)), s.s)));
      }
      case "Lam": {
        const all = all_of(cb.book, ty)
          ?? die(`a lambda value without a type: ${s.k}`);
        const bd = { p: probe(s.k), q: all.q, A: all.A };
        const c2 = [...caps, bd];
        if (!q_live(all.q)) {
          return expr(c2, s.f(bd.p), all.B(bd.p), k);
        }
        return k(caps, mint(cb, def, "c", c2, false, 1,
          () => leaf(c2, s.f(bd.p))));
      }
      case "Let": {
        if (!q_live(s.q)) {
          return expr(caps, s.f(s.v), null, k);
        }
        if (has_call(cb, s.v) || has_cut(s.f(DUMMY))) {
          return expr(caps, s.v, null, (c2, v) =>
            bound(c2, s, v, (c3, b) => expr(c3, b, null, k)));
        }
        const v = expr(caps, s.v, null, PASS);
        return k(caps, bound(caps, s, v,
          (c2, b) => expr(c2, b, null, PASS)));
      }
      case "Mat":
      case "Efq": {
        const T = ty ?? die("an untyped match value");
        return expr(caps, eta(Ann(s, T)), T, k);
      }
      default: {
        return k(caps, lift(s));
      }
    }
  }
  return func([], tld.e as HTerm, tld.T,
    live_doms(cb.book, tld).length)(EMPTY);
}

function carb_refs(cb: Carb, t: HTerm): Set<Name> {
  const out = new Set<Name>();
  term_any(cb.book, t, (s) => {
    if (s.$ === "Ref") {
      if (s.b) {
        cb.bangs.add(s.k);
      }
      if (intr_of(s.k) === undefined) {
        out.add(s.k);
      }
    }
    return false;
  });
  return out;
}

function is_carbo(cb: Carb, t: HTerm): boolean {
  const leaf_ok = (x: HTerm): boolean => {
    const s = term_strip(x);
    if (s.$ === "Let") {
      const { ls, rest } = let_chain(s, Infinity, cb.book);
      if (ls.length >= 1) {
        const jc = call_ok(cb, rest, ls.length);
        if (jc === null || !ls.every((l) => call_ok(cb, l.v, 0) !== null)) {
          return false;
        }
        const seq = cb.mint.get(jc.k) === true;
        return ls.length === 1 ? seq : !seq;
      }
      return !has_call(cb, s.v) && leaf_ok(s.f(DUMMY));
    }
    if (is_call(cb, s)) {
      return call_ok(cb, s, 0) !== null;
    }
    const m = term_spine(cb.book, s);
    if (!mat_head(m.t)) {
      return !has_call(cb, s);
    }
    return func_ok(m.h) && m.args.every((a) => !has_call(cb, a));
  };
  const func_ok = (x: HTerm): boolean => {
    const s = term_strip(x);
    switch (s.$) {
      case "Lam": return func_ok(s.f(DUMMY));
      case "Mat": return func_ok(s.h) && func_ok(s.m);
      case "Efq": return true;
      default:    return leaf_ok(s);
    }
  };
  return func_ok(t);
}

function carb_book(src: Book): Carb {
  const tlds = { ...src.tlds };
  for (const [k, tld] of Object.entries(tlds)) {
    if (tld.$ === "Def" && tld.e !== undefined) {
      tlds[k] = { ...tld, e: term_higher(term_lower(tld.e), Emp()) };
    }
  }
  const book: Book = { ...src, tlds: { ...tlds } };
  const cb: Carb = {
    src: { ...src, tlds },
    book,
    mint:   new Map(),
    kn:     0,
    done:   new Set(),
    queue:  ["main"],
    inl:    new Map(),
    inlrun: new Set(),
    bangs:  new Set(),
    brw:    new Map(),
    clo:    false,
  };
  while (cb.queue.length > 0) {
    const k = cb.queue.shift() as Name;
    if (cb.done.has(k)) {
      continue;
    }
    cb.done.add(k);
    const tld = book.tlds[k];
    if (!def_live(tld)) {
      continue;
    }
    let out = tld.e as HTerm;
    if (!cb.mint.has(k)) {
      if (out === undefined) {
        die("unelaborated def " + k + ": run book_valid first");
      }
      out = carbonize(cb, k, tld);
    }
    if (!is_carbo(cb, out)) {
      out = carbonize(cb, k, tld, true);
    }
    book.tlds[k] = { ...tld, v: out, e: out };
    if (!is_carbo(cb, out)) {
      die("carbonize left def " + k + " outside the Carbo format");
    }
    const refs = carb_refs(cb, out);
    cb.queue.push(...[...refs]
      .sort((a, b) => Number(cb.mint.has(b)) - Number(cb.mint.has(a))));
  }
  return cb;
}

// Inline
// ======

function funcok(cb: Carb, t: HTerm, ty0: HTerm | null): boolean {
  const [s, ty] = ann_peel(t, ty0);
  const all = all_of(cb.book, ty);
  if (s.$ === "Lam") {
    return funcok(cb, s.f(DUMMY), all && all.B(DUMMY));
  }
  if (s.$ === "Mat") {
    if (all === null || !adt_triv(cb.book, all.A)) {
      return false;
    }
    return funcok(cb, s.h, null) && funcok(cb, s.m, ty);
  }
  if (s.$ === "Efq") {
    return true;
  }
  return leafok(s);
  function leafok(x: HTerm): boolean {
    const y = term_force(x);
    if (y.$ === "Lam" || mat_head(y)) {
      return false;
    }
    if (y.$ === "App") {
      const m = term_spine(cb.book, y);
      if (mat_head(m.t)) {
        return funcok(cb, m.h, null) && m.args.every(leafok);
      }
    }
    return term_kids(cb.book, y).every(leafok);
  }
}

function calm_of(cb: Carb, t: HTerm): boolean {
  return funcok(cb, t, null)
    && !term_any(cb.book, t, (s) => fork_span(s) >= 2);
}

function inl_calls(cb: Carb, t: HTerm, self?: Name): boolean {
  return !term_any(cb.book, t, (s) => {
    const ck = call_kind(cb.book, s);
    return ck !== null && ck.k !== self && inl_of(cb, ck.k) === null;
  });
}

function inl_fit(cb: Carb, t: HTerm, self?: Name): boolean {
  const size = (x: HTerm): number => {
    const s = term_strip(x);
    return term_kids(cb.book, s).reduce((n, y) => n + size(y), 1);
  };
  return size(t) <= 128 && calm_of(cb, t) && inl_calls(cb, t, self);
}

function inl_of(cb: Carb, k: Name): HTerm | null {
  const got = cb.inl.get(k);
  if (got !== undefined) {
    return got;
  }
  const tld = cb.src.tlds[k];
  if (cb.inlrun.has(k) || tld?.$ !== "Def" || tld.e === undefined) {
    return null;
  }
  cb.inlrun.add(k);
  const out = inl_fit(cb, tld.e) ? tld.e : null;
  cb.inlrun.delete(k);
  cb.inl.set(k, out);
  return out;
}

function inl_at(cb: Carb, t: HTerm): HTerm | null {
  const m = term_spine(cb.book, t);
  if (m.t.$ !== "Ref") {
    return null;
  }
  const tld = cb.src.tlds[m.t.k];
  if (tld?.$ !== "Def") {
    return null;
  }
  const live = live_doms(cb.book, tld).length;
  const intr = intr_of(m.t.k) !== undefined;
  if (m.t.b) {
    if (intr) {
      die("a banged intrinsic spine of " + m.t.k);
    }
    if (m.args.length < live) {
      die("a banged under-saturated spine of " + m.t.k);
    }
    return null;
  }
  if (m.args.length < (intr ? live : live - 1)) {
    return Ann(eta(t), tele_app(cb.book, tld.T, m.all));
  }
  if (intr || m.all.length !== tld.n) {
    return null;
  }
  const body = inl_of(cb, m.t.k);
  if (body === null) {
    return inl_fold(cb, m.t.k, tld, m.all);
  }
  return inl_splice(cb, body, m.all, 0, null);
}

function inl_fold(cb: Carb, k: Name, tld: Def,
  args: HTerm[]): HTerm | null {
  const raw = tld.e;
  if (cb.inlrun.has(k) || raw === undefined) {
    return null;
  }
  if (args.length === 0 || !term_const(args[0])) {
    return null;
  }
  if (live_doms(cb.book, tld).length !== tld.n) {
    return null;
  }
  if (!adt_triv(cb.book, tele_unbind(cb.book, tld.T).ret)) {
    return null;
  }
  if (!inl_fit(cb, raw, k)) {
    return null;
  }
  const trip = (t: HTerm, d: number): HTerm => {
    const s = term_force(t);
    if (s.$ === "Ann") {
      return Ann(trip(s.x, d), s.T, s.s);
    }
    if (s.$ === "Let") {
      return Let(s.k, s.i, s.v, (x) => trip(s.f(x), d), s.s, s.q);
    }
    const m = term_spine(cb.book, s);
    if (m.t.$ !== "Ref" || m.t.k !== k || m.t.b) {
      return s;
    }
    if (m.all.length !== tld.n || !term_const(m.all[0]) || d >= 32) {
      return s;
    }
    return trip(inl_splice(cb, raw, m.all, 0, null), d + 1);
  };
  cb.inlrun.add(k);
  const out  = trip(inl_splice(cb, raw, args, 0, null), 0);
  const calm = inl_calls(cb, out);
  cb.inlrun.delete(k);
  return calm && calm_of(cb, out) ? out : null;
}

function inl_splice(cb: Carb, t: HTerm, args: HTerm[], i: number,
  ty0: HTerm | null): HTerm {
  if (i === args.length) {
    return t;
  }
  const [s, ty] = ann_peel(t, ty0);
  const all = all_of(cb.book, ty);
  if (s.$ === "Lam") {
    const rest = (x: HTerm) => {
      const B = all && all.B(x);
      return inl_splice(cb, s.f(x), args, i + 1, B);
    };
    if (term_const(args[i])) {
      return rest(args[i]);
    }
    const bare = term_force(args[i]).$ === "Ann" || all === null;
    const v = bare ? args[i] : Ann(args[i], all.A);
    const q = all === null ? Lone() : all.q;
    return Let(s.k, s.i, v, rest, undefined, q);
  }
  const sc = term_strip(args[i]);
  if (term_const(args[i]) && s.$ === "Mat" && sc.$ === "Ctr") {
    for (let w: HTerm = s;;) {
      const f: HTerm = term_force(w);
      if (f.$ === "Ann") {
        w = f.x;
      } else if (f.$ === "Mat" && f.k !== sc.k) {
        w = f.m;
      } else if (f.$ === "Mat") {
        const xs = [...sc.x, ...args.slice(i + 1)];
        return inl_splice(cb, f.h, xs, 0, null);
      } else {
        break;
      }
    }
  }
  let out: HTerm = ty === null ? s : Ann(s, ty);
  for (let j = i; j < args.length; j++) {
    const a = all_of(cb.book, ann_of(out));
    if (a === null) {
      die("a splice applied past its telescope");
    }
    out = Ann(App(out, args[j]), a.B(args[j]));
  }
  return out;
}

// Done
// ====

function def_live(tld: ADT | Def | undefined): tld is Def {
  return tld?.$ === "Def" && tld.v !== null;
}

function done_defs(cb: Carb): [Name, Def][] {
  return [...cb.done].map((k) => [k, cb.book.tlds[k]] as [Name, Def])
    .filter((p) => def_live(p[1]));
}

// Keeps
// =====

function shr_build(cb: Carb): Set<string> {
  const keeps = new Set<string>();
  const sites: (HTerm | null)[] = [];
  const held = (B: HTerm | null, force = false) => {
    const w = wnf_of(cb.book, B);
    if (w?.$ === "Lam") {
      held(w.f(DUMMY), force);
      return;
    }
    if (w?.$ !== "ADT") {
      cb.clo = cb.clo
        || (force && ["All", "Var", "App", "Mat"].includes(w?.$ as string));
      return;
    }
    const tk  = "t:" + w.k;
    const hot = force || keeps.has(tk)
      || (w.k === "Array" && !ty_w32(cb.book, w.x[0]));
    w.x.forEach((x) => held(x, hot));
    if (!hot || keeps.has(tk)) {
      return;
    }
    keeps.add(tk);
    const tld = cb.book.tlds[w.k];
    if (tld?.$ === "ADT") {
      for (const c of tld.c) {
        keeps.add(c.k);
        const T = tele_app(cb.book, c.T, w.x);
        tele_unbind(cb.book, T).doms.filter(dom_live)
          .forEach(([, , A]) => held(A, true));
      }
    }
  };
  const site = (A: HTerm | null, n: number) => {
    sites.push(A);
    const w = wnf_of(cb.book, A);
    if (n <= 1 || adt_triv(cb.book, A)) {
      return;
    }
    if (w?.$ === "ADT") {
      held(w, true);
    } else {
      cb.clo = true;
    }
  };
  const scan = (t: HTerm, ty0: HTerm | null): void => {
    const [s, ty] = ann_peel(t, ty0);
    if (s.$ === "Lam" || s.$ === "Let") {
      const { p, b: body } = open_of(s);
      const n = uses_at(term_uses(cb, body), p);
      if (s.$ === "Let") {
        site(ann_of(s.v), n);
        scan(s.v, null);
        return scan(body, null);
      }
      const all = all_of(cb.book, ty)
        ?? die(`a binder without a type: ${s.k}`);
      if (q_live(all.q)) {
        site(all.A, n);
      }
      return scan(body, all.B(p));
    }
    if (s.$ === "Ref" && intr_of(s.k) === INTRINSICS.array_copy) {
      keeps.add("t:Array");
    }
    for (const kid of term_kids(cb.book, s)) {
      scan(kid, null);
    }
  };
  for (const [, tld] of done_defs(cb)) {
    scan(tld.e as HTerm, tld.T);
  }
  for (let seen = -1; seen < keeps.size + Number(cb.clo);) {
    seen = keeps.size + Number(cb.clo);
    sites.forEach((T) => held(T, cb.clo && !adt_triv(cb.book, T)));
  }
  return keeps;
}

// Borrow
// ======

type Root = [Name, number];

function brw_type(cb: Carb, A: HTerm): boolean {
  const t = term_wnf(cb.book, A);
  return t.$ === "ADT" && NATIVES[t.k] === undefined
    && !adt_triv(cb.book, A);
}

function brw_build(cb: Carb) {
  const brw_scan = (k: Name) => {
    const roots = new Map<Probe, Root>();
    let hit = false;
    const flip = (r: Root | null) => {
      if (r === null) {
        return;
      }
      const bs = cb.brw.get(r[0]);
      if (bs?.[r[1]]) {
        bs[r[1]] = false;
        hit = true;
      }
    };
    const guard = (t: HTerm) => {
      term_any(cb.book, t, (s) => {
        if (s.$ === "Var") {
          flip(roots.get(probe_of(s)) ?? null);
        }
        if (s.$ === "Ref") {
          cb.brw.get(s.k)?.forEach((_, j) => flip([s.k, j]));
        }
        return false;
      });
    };
    const site = (t: HTerm, ct: HTerm | null) => {
      const ck = call_kind(cb.book, t) as Call;
      const lent = cb.brw.get(ck.k);
      ck.args.forEach((a, j) => {
        const v = term_strip(a);
        if (!lent?.[j] || v.$ !== "Var") {
          if (lent?.[j]) {
            flip([ck.k, j]);
          }
          return guard(a);
        }
        const p = probe_of(v);
        const held = ct !== null
          && term_spine(cb.book, ct).args.some((z) => term_strip(z) === p);
        if (!roots.has(p) && !held) {
          flip([ck.k, j]);
        }
      });
    };
    const leaf = (t: HTerm) => {
      const x = term_strip(t);
      if (x.$ === "Let") {
        const { ls, rest } = let_chain(x, Infinity, cb.book);
        if (ls.length >= 2) {
          for (const l of ls) {
            site(l.v, rest);
          }
          return site(rest, null);
        }
        const o = open_of(x);
        if (is_call(cb, x.v)) {
          site(x.v, o.b);
        } else {
          guard(x.v);
        }
        return leaf(o.b);
      }
      if (is_call(cb, x)) {
        return site(x, null);
      }
      const m = term_spine(cb.book, x);
      if (!mat_head(m.t)) {
        return guard(x);
      }
      m.args.forEach(guard);
      walk(m.t, m.args.map(() => null));
    };
    const walk = (t: HTerm, plan: (Root | null)[]) => {
      const x = term_strip(t);
      if (x.$ === "Lam") {
        const o = open_of(x);
        const r = plan[0] ?? null;
        if (r !== null) {
          roots.set(o.p, r);
        }
        return walk(o.b, plan.slice(1));
      }
      if (x.$ !== "Mat" && x.$ !== "Efq") {
        return leaf(x);
      }
      const { arms, end } = mat_arms(x);
      const scr = plan[0] ?? null;
      for (const [c, h] of arms) {
        const ctr = cb.book.ctrs[c];
        const fs  = ctr === undefined ? [] : ctr_tail(cb.book, ctr);
        const fr  = fs.map(([q, , A]) => {
          if (!q_live(q) || adt_triv(cb.book, A)) {
            return null;
          }
          if (!brw_type(cb, A)) {
            flip(scr);
            return null;
          }
          return scr;
        });
        walk(h, [...fr, ...plan.slice(1)]);
      }
      if (end !== null) {
        walk(end, plan);
      }
    };
    const tld = cb.book.tlds[k] as Def;
    let i = -1;
    walk(tld.e as HTerm, tele_unbind(cb.book, tld.T).doms.slice(0, tld.n)
      .map(([q]) => (q_live(q) && (cb.brw.get(k) as boolean[])[(i += 1)]
        ? [k, i] : null)));
    return hit;
  };
  for (const [k, tld] of done_defs(cb)) {
    cb.brw.set(k, live_doms(cb.book, tld).map(([, , A]) => brw_type(cb, A)));
  }
  for (let go = true; go;) {
    go = false;
    for (const k of cb.brw.keys()) {
      go = brw_scan(k) || go;
    }
  }
}

// File
// ====

function cid_mac(k: string): string {
  return `CID_${sanitize(k).toUpperCase()}`;
}

function cid_reg(fl: File, k: Name, abi = 0): string {
  if (!fl.cids.has(k)) {
    const ctr = fl.book.ctrs[k];
    const n = ctr === undefined ? abi : ctr_doms(fl.book, ctr).length;
    fl.cids.set(k, { arity: n, packed: ctr_scalar1(fl.book, k) });
  }
  return cid_mac(k);
}

function file_push(fl: File, line: string) {
  fl.seg.lines.push("  ".repeat(fl.tab) + line);
}

function block(fl: File, open: string, go: () => void) {
  file_push(fl, open);
  fl.tab += 1;
  go();
  fl.tab -= 1;
  file_push(fl, "}");
}

type Parts = { k: Name; vs: string[]; w: boolean };

type Bind = { owed: number; local: string; triv: boolean; parts?: Parts };

function cls_fit(words: number): number {
  return 32 - Math.clz32(words - 1);
}

function spare_free(fl: File, words: number, name: string,
  z: boolean) {
  const fn = z ? "spare_free" : "heap_free";
  file_push(fl, `${fn}(e, cls_fit(${words}), ${name});`);
}

function spare_flush(fl: File) {
  for (const s of fl.spares.reverse()) {
    spare_free(fl, s.words, s.name, s.z);
  }
  fl.spares = [];
}

function use_pop(fl: File, x: HTerm): string {
  const p = probe_of(x);
  const b = fl.uses.get(p);
  if (b === undefined) {
    die(`a use of an unbound binder: ${p.k}`);
  }
  if (b.parts !== undefined) {
    return ctr_build(fl, b.parts.k, b.parts.vs);
  }
  if (b.triv) {
    const u = fl.seg.unbox?.[fl.seg.params.indexOf(b.local)];
    return u == null ? b.local : `${u}_rewrap(${b.local})`;
  }
  if (b.owed <= 1) {
    fl.uses.delete(p);
    return b.local;
  }
  fl.uses.set(p, { ...b, owed: b.owed - 1 });
  file_push(fl, `${b.local} = term_keep(e, ${b.local});`);
  return b.local;
}

function bind_uses(fl: File, local: string, x: HBinder,
  ty: HTerm | null, parts?: Parts): HTerm {
  const o = open_of(x);
  if (parts !== undefined && !parts.w) {
    local = expr_alias(fl, ctr_build(fl, parts.k, parts.vs), x.k);
    parts = undefined;
  }
  const brw  = fl.brwl.has(local);
  const triv = parts !== undefined || brw || adt_triv(fl.book, ty);
  const n = uses_at(term_uses(fl.cb, o.b), o.p);
  if (n === 0 && !brw) {
    if (!triv) {
      file_push(fl, `term_sink(e, ${local});`);
    }
  } else {
    fl.uses.set(o.p, { owed: triv ? 1 : n, local, triv, parts });
  }
  return o.b;
}

function unbox_read(u: Unbox | undefined, x: string): string {
  return u == null ? x : `${u}_unbox(${x})`;
}

function seg_new(fl: File, name: string, seq: boolean,
  params: string[], def = ""): Seg {
  const seg: Seg = { fid: fid_of(name), def, lines: [],
    params, refs: new Set(),
    frame: seq ? { pop: params.length - 1, base: 0 } : null };
  fl.segs.push(seg);
  return seg;
}

function fid_of(k: Name): string {
  return `FID_${sanitize(k).toUpperCase()}`;
}

function seg_ref(fl: File, fid: string): string {
  fl.seg.refs.add(fid);
  return fid;
}

function node_fill(fl: File, k: string, alloc: string,
  exprs: string[], shr = false): string {
  const nd = local_new(fl, k);
  file_push(fl, `u64 ${nd} = ${alloc};`);
  exprs.forEach((w, j) => {
    file_push(fl, `e.mem[${nd} + ${j}] = ${shr ? `rfc_seal(e, ${w})` : w};`);
  });
  return nd;
}

function ctr_build(fl: File, k: Name, exprs: string[]): string {
  const cid = cid_reg(fl, k);
  if (exprs.length === 0) {
    return `term_pack(${cid}, 0)`;
  }
  if (fl.cids.get(k)!.packed) {
    return `term_pack(${cid}, ${exprs[0]})`;
  }
  const shr = fl.shr.has(k);
  const alloc = `heap_alloc(e, cls_fit(${exprs.length}))`;
  const at = fl.spares.findIndex((s) =>
    cls_fit(s.words) === cls_fit(exprs.length));
  let got = alloc;
  if (at >= 0) {
    const s = fl.spares.splice(at, 1)[0];
    got = s.z ? `${s.name} ? ${s.name} : ${alloc}` : s.name;
  }
  return `term_ctor(${cid}, ${node_fill(fl, "nd", got, exprs, shr)})`;
}

// Select
// ======

function eq_set(fl: File, t: HTerm): { p: Probe; ks: number[] } | null {
  const st = term_strip(t);
  if (st.$ === "Let") {
    const v = term_strip(st.v);
    return v.$ === "Var" ? eq_set(fl, st.f(v)) : null;
  }
  const sp = term_spine(fl.book, t);
  if (sp.t.$ === "Mat" && sp.args.length === 1) {
    const bs = Object.fromEntries(mat_arms(sp.t).arms.map(([k2, h2]) =>
      [k2, u32_from_term(h2)]));
    if (bs.False !== 0 || bs.True !== 1) {
      return null;
    }
    return eq_set(fl, sp.args[0]);
  }
  if (sp.t.$ !== "Ref" || sp.args.length !== 2) {
    return null;
  }
  const it = intr_of(sp.t.k);
  if (it === INTRINSICS.bool_or) {
    const l = eq_set(fl, sp.args[0]);
    const r = eq_set(fl, sp.args[1]);
    if (l === null || r === null) {
      return null;
    }
    return l.p === r.p ? { p: l.p, ks: [...l.ks, ...r.ks] } : null;
  }
  if (it === INTRINSICS.u32_is_eq) {
    const vs = sp.args.map(u32_from_term);
    for (const i of [0, 1]) {
      const w  = vs[1 - i];
      const xi = term_strip(sp.args[i]);
      if (xi.$ === "Var" && w !== null) {
        return { p: probe_of(xi), ks: [w] };
      }
    }
  }
  return null;
}

function sel_ok(fl: File, t: HTerm): boolean {
  const x = term_strip(t);
  if (x.$ === "Var") {
    const b = fl.uses.get(probe_of(x));
    return b?.triv === true && b.parts === undefined;
  }
  const m = term_spine(fl.book, x);
  if (m.t.$ === "Ref" && intr_of(m.t.k)?.call === false) {
    return m.args.every((a) => sel_ok(fl, a));
  }
  return u32_from_term(x) !== null;
}

function eq_mask(ks: number[]): { m: number; K: number } | null {
  const u = [...new Set(ks)].sort((p, q) => p - q);
  if (u.length === 1) {
    return { m: 0, K: u[0] };
  }
  if (u.length === 2) {
    const d = u[0] ^ u[1];
    if ((d & (d - 1)) === 0) {
      return { m: d, K: u[1] };
    }
  }
  return null;
}

// Table
// =====

function nat_table(fl: File, x: HTerm, s: string, dst: Dst): boolean {
  const tab_ok = (t: HTerm): boolean => {
    const sp = term_spine(fl.book, t);
    if (sp.t.$ === "Ref" && intr_of(sp.t.k)?.call === false) {
      return sp.args.every(tab_ok);
    }
    return term_const(t);
  };
  const ls: HTerm[] = [];
  let m = term_strip(x);
  while (m.$ === "Mat") {
    const { arms, end } = mat_arms(m);
    const { Zero, Succ } = Object.fromEntries(arms);
    if (end !== null || Zero === undefined || Succ === undefined) {
      return false;
    }
    ls.push(Zero);
    m = term_strip(Succ);
  }
  ls.push(m.$ === "Lam" ? open_of(m).b : m);
  if (ls.length < 3 || !ls.every(tab_ok)) {
    return false;
  }
  const key = exprs_of(fl, ls).join(", ");
  const id  = fl.tabs.get(key) ?? fl.tabs.size;
  fl.tabs.set(key, id);
  const n = ls.length - 1;
  emit_put(fl, dst, `TAB_AT(TAB_${id}, ${s}, ${n})`);
  return true;
}

// Fuse
// ====

function lends(fl: File, k: Name): boolean {
  return (fl.cb.brw.get(k) ?? []).some((b) => b);
}

function fuse_pure(fl: File, k: Name, body: HTerm): boolean {
  return !term_any(fl.book, body, (s) => {
    const c = call_kind(fl.book, s);
    return c !== null && c.k !== k;
  }) && calm_of(fl.cb, body);
}

function fuse_call(fl: File, ck: Call, dst: Dst): boolean {
  if (ck.bang || dst !== null || ck.k === CLO_APPLY || lends(fl, ck.k)) {
    return false;
  }
  const tld  = fl.book.tlds[ck.k] as Def;
  const body = tld.e as HTerm;
  const dead = term_strip(body).$ === "Mat" && term_const(ck.args[0]);
  const loop = fl.fusing.has(ck.k)
    || term_any(fl.book, body, (s) => call_kind(fl.book, s)?.k === ck.k);
  if (loop || dead || !has_call(fl.cb, body)) {
    return false;
  }
  const args = ck.args.map((a) => fuse_arg(fl, a));
  const seen = new Set<Name>([fl.seg.def]);
  let spins = false;
  const walk = (g: Name) => {
    const gb = (fl.book.tlds[g] as Def).e as HTerm;
    spins ||= has_call(fl.cb, gb) && fuse_pure(fl, g, gb);
    for (const h of carb_refs(fl.cb, gb)) {
      if (!seen.has(h)) {
        seen.add(h);
        walk(h);
      }
    }
  };
  walk(ck.k);
  if (seen.has(ck.k) && spins) {
    spare_flush(fl);
    block(fl, "if (DEVICE) {", () => {
      jump_into(fl, args.map((a) => arg_term(fl, a)), ck.k);
    });
  }
  fl.fusing.add(ck.k);
  emit_func(fl, body, tld.T, args, dst);
  fl.fusing.delete(ck.k);
  return true;
}

function fuse_cut(fl: File, ck: Call, km: Call, dst: Dst): boolean {
  if (ck.bang || ck.k === CLO_APPLY || lends(fl, ck.k) || lends(fl, km.k)) {
    return false;
  }
  const tld  = fl.book.tlds[ck.k] as Def;
  const jt   = fl.book.tlds[km.k] as Def;
  const body = tld.e as HTerm;
  const loop = has_call(fl.cb, body);
  const tele = tele_unbind(fl.book, tld.T);
  if (tele.doms.slice(tld.n).some(dom_live)) {
    return false;
  }
  const ret  = tele.ret;
  const word = adt_triv(fl.book, ret);
  const adt  = term_wnf(fl.book, ret);
  const rt   = adt.$ === "ADT" ? fl.book.tlds[adt.k] : undefined;
  const one  = rt?.$ === "ADT" && rt.c.length === 1 ? rt.c[0] : null;
  const doms = one && ctr_doms(fl.book, one);
  const flat = doms !== null && doms.length >= 2
    && doms.every((A) => adt_triv(fl.book, A));
  const rec  = word || !flat ? null
    : { k: (one as Ctr).k, n: (doms as HTerm[]).length };
  if (!fuse_pure(fl, ck.k, body) || !(loop || word || rec !== null)) {
    return false;
  }
  const ps = local_hold(fl, exprs_of(fl, ck.args), "p");
  const caps = exprs_of(fl, km.args.slice(0, -1));
  const vs   = Array.from({ length: rec?.n ?? 1 }, () => local_new(fl, "x"));
  for (const v of vs) {
    file_push(fl, `Term ${v} = 0;`);
  }
  if (loop) {
    spare_flush(fl);
    const at  = fl.seg.lines.length;
    const seg = fl.seg;
    fl.seg = { ...seg, def: ck.k, params: ps, unbox: undefined };
    block(fl, "WL_SPIN", () => {
      emit_func(fl, body, tld.T, ps, vs);
      fl.seg = seg;
      file_push(fl, "break;");
    });
    const spun = fl.seg.lines.splice(at);
    const off  = "  ".repeat(fl.tab - 1);
    const bent = spun.map((l) =>
      "  " + (l.startsWith(off) ? l.slice(off.length) : l));
    const name = seg_ref(fl, "spin_" + fl.spins.length);
    const sig = ps.map((p) => ", Term " + p).join("");
    fl.spins.push([`  static Term ${name}(Env e, THR Term* o${sig}) {`,
      "    u32 wpoll = 0;", ...vs.map((v) => `    Term ${v} = 0;`),
      ...bent, ...vs.map((v, j) => `    o[${j}] = ${v};`),
      "    return 1;", "  }"].join("\n"));
    const o = local_new(fl, "o");
    file_push(fl, "#if DEVICE");
    file_push(fl, `Term ${o}[${vs.length}];`);
    const sa = ["e", o, ...ps].join(", ");
    block(fl, `if (Spin::${name}(${sa}) == 0) {`, () => {
      file_push(fl, "return 0;");
    });
    vs.forEach((v, j) => file_push(fl, `${v} = ${o}[${j}];`));
    file_push(fl, "#else");
    fl.seg.lines.push(...spun);
    file_push(fl, "#endif");
  } else {
    emit_func(fl, body, tld.T, ps, vs);
  }
  emit_func(fl, jt.e as HTerm, jt.T,
    [...caps, rec === null ? vs[0] : { k: rec.k, vs, w: true }], dst);
  return true;
}

// Emission
// ========

function exprs_of(fl: File, xs: HTerm[]): string[] {
  return xs.map((a) => emit_expr(fl, a, null));
}

function local_hold(fl: File, exprs: string[], k: string): string[] {
  return exprs.map((ex) => {
    const al = local_new(fl, k);
    file_push(fl, `Term ${al} = ${ex};`);
    return al;
  });
}

function expr_alias(fl: File, e: string, k: string): string {
  return fl.local.has(e) ? e : local_hold(fl, [e], k)[0];
}

function peek_open(fl: File, v: string): string {
  const bl = local_new(fl, "bl");
  file_push(fl, `u64 ${bl} = term_peek(e, ${v});`);
  return bl;
}

function task_new(fl: File, fid: string, rem: number, words: string[],
  cont = "WL_CONT", idx: string | number = "WL_IDX"): string {
  return node_fill(fl, "t",
    `task_node(e, ${seg_ref(fl, fid)}, ${cont}, ${idx}, ${rem})`, words);
}

function frame_push(fl: File, words: string[], next: string) {
  const n = words.length + 1;
  file_push(fl, `WL_ROOM(${n});`);
  [...words, seg_ref(fl, next)].forEach((w, i) => {
    file_push(fl, `STK(${i}) = ${w};`);
  });
  file_push(fl, `WL_PUSHN(${n});`);
}

function bang_task(fl: File, fid: string, args: string[]) {
  file_push(fl, `return term_task(${fid}, ${task_new(fl, fid, 0, args)});`);
}

function jump_into(fl: File, args: string[], k: Name) {
  if (fl.seg.def !== k) {
    args.forEach((a, i) => file_push(fl, `r${i} = ${a};`));
    return file_push(fl, `WL_JMP(${seg_ref(fl, fid_of(k))});`);
  }
  fl.seg.spin = true;
  local_hold(fl, args, "j").forEach((j, i) => {
    file_push(fl, `${fl.seg.params[i]} = ${unbox_read(fl.seg.unbox?.[i], j)};`);
  });
  file_push(fl, "WL_AGAIN;");
}

function lend_args(fl: File, ck: Call): string[] {
  const lent = fl.cb.brw.get(ck.k);
  return ck.args.map((a, j) => {
    if (!lent?.[j]) {
      return emit_expr(fl, a, null);
    }
    return (fl.uses.get(term_strip(a) as Probe) as Bind).local;
  });
}

function emit_call(fl: File, ck: Call, km: Call | null) {
  const cargs = lend_args(fl, ck);
  const cexps = km === null ? [] : exprs_of(fl, km.args.slice(0, -1));
  spare_flush(fl);
  if (km !== null) {
    const kf = fid_of(km.k);
    file_push(fl, "if (seq) {");
    fl.tab += 1;
    frame_push(fl, cexps, kf);
    fl.tab -= 1;
    block(fl, "} else {", () => {
      file_push(fl,
        `WL_KONT(${kf}, ${task_new(fl, kf, 1, cexps)}, ${cexps.length});`);
      if (ck.bang) {
        bang_task(fl, fid_of(ck.k), cargs);
      }
    });
  } else if (ck.bang) {
    block(fl, "if (!seq) {", () => bang_task(fl, fid_of(ck.k), cargs));
  }
  jump_into(fl, cargs, ck.k);
}

function emit_fork(fl: File, ls: HLet[], rest: HTerm) {
  const tab0 = fl.tab;
  const n = ls.length;
  const calls = ls.map((l) => call_kind(fl.book, l.v) as Call);
  const jc = call_kind(fl.book, rest) as Call;
  const alias = (x: string) => expr_alias(fl, x, "a");
  const margs = calls.map((c) => lend_args(fl, c).map(alias));
  const caps  = exprs_of(fl, jc.args.slice(0, -n)).map(alias);
  spare_flush(fl);
  const m  = caps.length;
  const kj = fid_of(jc.k);
  const fj = calls.map((c) => fid_of(c.k));
  block(fl, "if (!seq) {", () => {
    const jn = task_new(fl, kj, n, caps);
    const jt = `term_task(${kj}, ${jn})`;
    for (let j = 0; j < n; j += 1) {
      const cj = task_new(fl, fj[j], 0, margs[j], jt, m + j);
      file_push(fl, `WL_KID(${jn}, ${m + j}, ${fj[j]}, ${cj});`);
    }
    file_push(fl, `return ${jt};`);
  });
  const w0 = margs.slice(1).reverse().flat().concat(caps);
  const home = fl.seg;
  fl.tab = 2;
  const steps: Seg[] = new Array(n);
  for (let j = n; j >= 1; j -= 1) {
    const pa = (j < n ? margs[j] : caps).map(() => local_new(fl, "a"));
    for (let t = j < n ? 1 : n; t > 0; t -= 1) {
      pa.push(local_new(fl, "x"));
    }
    steps[j - 1] = seg_new(fl, local_new(fl, `${home.def}_s`), true, pa);
  }
  let under = m;
  for (let j = 1; j < n; j += 1) {
    fl.seg = steps[j - 1];
    under += margs[j].length;
    fl.seg.frame = { pop: 0, base: -under };
    const ps = fl.seg.params;
    frame_push(fl, [ps[ps.length - 1]], steps[j].fid);
    jump_into(fl, ps.slice(0, -1), calls[j].k);
    under += 1;
  }
  fl.seg = steps[n - 1];
  fl.seg.frame = { pop: w0.length + n - 1, base: w0.length - m };
  jump_into(fl, fl.seg.params, jc.k);
  fl.seg = home;
  fl.tab = tab0;
  frame_push(fl, w0, steps[0].fid);
  jump_into(fl, margs[0], calls[0].k);
}

type Arms = { arms: [Name, HTerm][]; end: HTerm | null };

function mat_arms(t: HTerm): Arms {
  const arms: [Name, HTerm][] = [];
  let cur = t;
  for (let m = term_strip(cur); m.$ === "Mat"; m = term_strip(cur)) {
    arms.push([m.k, m.h]);
    cur = m.m;
  }
  return { arms, end: term_strip(cur).$ === "Efq" ? null : cur };
}

type Dst = string[] | null;

type Arg = string | Parts;

function arg_term(fl: File, a: Arg): string {
  return typeof a === "string" ? a : ctr_build(fl, a.k, a.vs);
}

function fuse_arg(fl: File, a: HTerm): Arg {
  const [x] = ann_peel(a, null);
  if (x.$ === "Var") {
    const b = fl.uses.get(probe_of(x));
    if (b?.parts !== undefined) {
      return b.parts;
    }
  }
  const m = term_spine(fl.book, x);
  const it = m.t.$ === "Ref" ? intr_of(m.t.k) : undefined;
  if (it?.parts !== undefined) {
    const arr = native_of(fl.book, term_wnf(fl.book,
      ann_of(m.args[0]) ?? die("an untyped block")) as HAdt)
      === ARR_NATIVE ? "1" : "0";
    const as = exprs_of(fl, m.args).map((z) => expr_alias(fl, z, "aw"));
    const vs: string[] = [];
    for (const p of it.parts(fl.shr.has("t:Array"))) {
      vs.push(expr_alias(fl, tpl(p)([...as, arr, ...vs]), "aw"));
    }
    return { k: "Tuple", vs, w: false };
  }
  return emit_expr(fl, a, null);
}

function emit_put(fl: File, dst: Dst, e: string) {
  if (dst === null) {
    spare_flush(fl);
    file_push(fl, `WL_RET(${e});`);
  } else {
    file_push(fl, `${dst[0]} = ${e};`);
  }
}

function let_open(fl: File, x: HLet): HTerm {
  const name = local_new(fl, x.k);
  file_push(fl, `Term ${name} = ${emit_expr(fl, x.v, null)};`);
  return bind_uses(fl, name, x, ann_of(x.v));
}

function ann_peel(tm: HTerm,
  ty: HTerm | null): [HTerm, HTerm | null] {
  let x = term_force(tm);
  while (x.$ === "Ann") {
    ty = x.T;
    x = term_force(x.x);
  }
  return [x, ty];
}

function emit_expr(fl: File, tm: HTerm, ty0: HTerm | null): string {
  const [x, ty] = ann_peel(tm, ty0);
  switch (x.$) {
    case "Var": return use_pop(fl, x);
    case "Ref":
    case "App": {
      const m = term_spine(fl.book, x);
      if (mat_head(m.t)) {
        const t = local_new(fl, "t");
        file_push(fl, `Term ${t} = 0;`);
        emit_matapp(fl, m, [t]);
        return t;
      }
      const g = m.t;
      if (g.$ === "Var" && m.args.length === 0) {
        return use_pop(fl, g);
      }
      if (g.$ !== "Ref") {
        die(`cannot compile a ${g.$}-headed spine`);
      }
      const tld = fl.book.tlds[g.k];
      const intr = intr_of(g.k);
      if (intr === undefined) {
        if (tld?.$ === "Def" && tld.v === null) {
          die(`a live call into the assert ${g.k}`);
        }
        if (m.args.length !== live_doms(fl.book, tld as Def).length - 1) {
          die("an under-applied def value: " + g.k);
        }
        const fid   = seg_ref(fl, fid_of(g.k));
        const exprs = exprs_of(fl, m.args);
        if (exprs.length === 0) {
          return `term_clos(${fid}, 0)`;
        }
        return `term_clos(${fid}, ${node_fill(fl, "nd",
          `heap_alloc(e, cls_fit(${exprs.length}))`, exprs, fl.cb.clo)})`;
      }
      if (intr.parts !== undefined) {
        return arg_term(fl, fuse_arg(fl, x));
      }
      const exprs = exprs_of(fl, m.args);
      return intr.e!(exprs, fl);
    }
    case "Ctr": {
      const adt = term_wnf(fl.book, ty as HTerm);
      if (adt.$ !== "ADT") {
        die(`a constructor at a non-datatype type: ${x.k}`);
      }
      if (adt.k === "U32") {
        const u = u32_from_term(x);
        if (u !== null) {
          return `${u}ull`;
        }
      }
      const flds  = ctr_flds(fl.book, x.k, x.x);
      const exprs = exprs_of(fl, flds);
      const native = native_of(fl.book, adt);
      if (native !== undefined) {
        const fn = native.intr[x.k];
        if (fn === undefined) {
          die(`no native introduction for a computed ${x.k}`);
        }
        return typeof fn === "string" ? tpl(fn)(exprs) : fn(exprs, flds);
      }
      return ctr_build(fl, x.k, exprs);
    }
    case "Let": return emit_expr(fl, let_open(fl, x), null);
    case "Rwt": return emit_expr(fl, x.f, ty);
    case "Rfl": return "0ull";
    default:    die(`cannot compile a ${x.$} node`);
  }
}

function emit_func(fl: File, tm: HTerm, ty0: HTerm | null,
  args: Arg[], dst: Dst): void {
  const [x, ty] = ann_peel(tm, ty0);
  switch (x.$) {
    case "Lam": {
      const all = term_wnf(fl.book, ty as HTerm) as HAll;
      if (!q_live(all.q)) {
        return emit_func(fl, x.f(DUMMY), all.B(DUMMY), args, dst);
      }
      const a0   = args[0];
      const name = typeof a0 === "string" ? expr_alias(fl, a0, x.k) : "";
      const rec  = typeof a0 === "string" ? undefined : a0;
      const body = bind_uses(fl, name, x, all.A, rec);
      return emit_func(fl, body, all.B(DUMMY), args.slice(1), dst);
    }
    case "Mat":
    case "Efq": {
      const a0 = args[0];
      if (typeof a0 !== "string" && x.$ === "Mat") {
        const { arms, end } = mat_arms(x);
        if (arms.length === 1 && end === null && arms[0][0] === a0.k) {
          return emit_func(fl, arms[0][1], null,
            [...a0.vs, ...args.slice(1)], dst);
        }
      }
      const s = expr_alias(fl, arg_term(fl, args[0]), "s");
      return emit_match(fl, x, ty, s,
        args.slice(1).map((a) => arg_term(fl, a)), dst);
    }
    default: return emit_leaf(fl, x, ty, dst);
  }
}

function emit_leaf(fl: File, tm: HTerm, ty0: HTerm | null,
  dst: Dst): void {
  const [x, ty] = ann_peel(tm, ty0);
  if (x.$ === "Let") {
    const { ls, rest } = let_chain(x, Infinity, fl.book);
    if (ls.length >= 2) {
      return emit_fork(fl, ls, rest);
    }
    const vc = call_kind(fl.book, x.v);
    if (vc !== null) {
      const km = call_kind(fl.book, rest) as Call;
      if (!fuse_cut(fl, vc, km, dst)) {
        emit_call(fl, vc, km);
      }
      return;
    }
    return emit_leaf(fl, let_open(fl, x), null, dst);
  }
  const ck = call_kind(fl.book, x);
  if (ck !== null) {
    if (fuse_call(fl, ck, dst)) {
      return;
    }
    return emit_call(fl, ck, null);
  }
  const m = term_spine(fl.book, x);
  if (mat_head(m.t)) {
    return emit_matapp(fl, m, dst);
  }
  if (dst !== null && dst.length > 1) {
    if (x.$ !== "Ctr") {
      const v  = expr_alias(fl, emit_expr(fl, x, ty), "v");
      const bl = peek_open(fl, v);
      dst.forEach((d, j) => {
        file_push(fl, `${d} = e.mem[${bl} + ${j}];`);
      });
      file_push(fl, `term_sink(e, ${v});`);
      return;
    }
    ctr_flds(fl.book, x.k, x.x).forEach((a, j) => {
      file_push(fl, `${dst[j]} = ${emit_expr(fl, a, null)};`);
    });
    return;
  }
  emit_put(fl, dst, emit_expr(fl, x, ty));
}

function emit_matapp(fl: File, m: Spine, dst: Dst) {
  emit_func(fl, m.h, null, [fuse_arg(fl, m.args[0]),
    ...exprs_of(fl, m.args.slice(1))], dst);
}

function emit_match(fl: File, x: HTerm, T: HTerm | null, s: string,
  rest: string[], dst: Dst): void {
  if (x.$ === "Efq") {
    file_push(fl, "err_post(e.mem, ERR_TAGS);");
    return file_push(fl, "return 0;");
  }
  const all = term_wnf(fl.book, T as HTerm) as HAll;
  const adt = term_wnf(fl.book, all.A) as HAdt;
  const { arms, end } = mat_arms(x);
  const total = (fl.book.tlds[adt.k] as ADT).c.length - adt.r.length;
  if (arms.length < total && end === null) {
    die("a partial match");
  }
  if (adt.k === "Bool" && arms.length === 2 && rest.length === 0) {
    const { True: hT, False: hF } = Object.fromEntries(arms);
    const eT = eq_set(fl, hT);
    const eF = eq_set(fl, hF);
    const mT = eT && eq_mask(eT.ks);
    const mF = eF && eq_mask(eF.ks);
    if (mT !== null && mF !== null && mT.K === mF.K && eT!.p === eF!.p) {
      let sel = `${mT.m}u`;
      if (mT.m !== mF.m) {
        sel = `(${s} != 0 ? ${mT.m}u : ${mF.m}u)`;
      }
      return emit_put(fl, dst,
        `u32_is_eq(u32_or(${use_pop(fl, eT!.p)}, ${sel}), ${mT.K}u)`);
    }
    if (sel_ok(fl, hT) && sel_ok(fl, hF)) {
      return emit_put(fl, dst, `(${s} != 0 ? ${emit_expr(fl, hT, null)}`
        + ` : ${emit_expr(fl, hF, null)})`);
    }
  }
  if (adt.k === "Nat" && ty_w32(fl.book, all.B(DUMMY))
    && nat_table(fl, x, s, dst)) {
    return;
  }
  const native = native_of(fl.book, adt);
  const sharable = fl.shr.has("t:" + adt.k);
  const brw = fl.brwl.has(s);
  if (adt.k === "Array" && sharable && !brw) {
    s = expr_alias(fl, `flat_cow(e, ${s})`, "s");
  }
  const armsets = arms.map(([, h]) => term_uses(fl.cb, h));
  const emits = arms.map(([k, h], i) =>
    () => arm_emit(h, k, armsets[i]));
  if (end !== null) {
    armsets.push(term_uses(fl.cb, end));
    emits.push(() => fin(end, armsets[arms.length], [s, ...rest]));
  }
  const mx_of = (p: Probe) =>
    armsets.reduce((m, u) => Math.max(m, uses_at(u, p)), 0);
  function fin(h2: HTerm, mine: UMap, args: string[]) {
    for (const [p, b] of [...fl.uses]) {
      const use = uses_at(mine, p);
      if (b.owed !== Infinity && mx_of(p) > use) {
        if (use === 0) {
          if (!b.triv) {
            file_push(fl, `term_sink(e, ${b.local});`);
          }
          fl.uses.delete(p);
        } else {
          fl.uses.set(p, { ...b, owed: use });
        }
      }
    }
    emit_func(fl, h2, null, args, dst);
  }
  function arm_emit(h: HTerm, k: Name, mine: UMap) {
    let fexprs: string[];
    if (native !== undefined) {
      fexprs = (native.elim?.[k] ?? []).map((t) => tpl(t)([s]));
    } else {
      cid_reg(fl, k);
      const { arity: live, packed } = fl.cids.get(k)!;
      if (packed || live === 0) {
        fexprs = packed ? [`term_loc(${s})`] : [];
      } else if (brw) {
        const bl = peek_open(fl, s);
        fexprs = Array.from({ length: live }, (_, j) => `e.mem[${bl} + ${j}]`);
      } else {
        const sp2 = local_new(fl, "sp");
        const fb = local_new(fl, "fb");
        file_push(fl, `Term ${fb}[${live}];`);
        if (sharable) {
          file_push(fl, `u64 ${sp2} = ctr_take(e, ${s}, ${live}, ${fb});`);
        } else {
          file_push(fl, `u64 ${sp2} = term_loc(${s});`);
          for (let j = 0; j < live; j += 1) {
            file_push(fl, `${fb}[${j}] = e.mem[${sp2} + ${j}];`);
          }
        }
        if (dst === null) {
          fl.spares.push({ words: live, name: sp2, z: sharable });
        } else {
          spare_free(fl, live, sp2, sharable);
        }
        fexprs = Array.from({ length: live }, (_, j) => `${fb}[${j}]`);
      }
    }
    const fields = local_hold(fl, fexprs, "f");
    if (brw) {
      ctr_doms(fl.book, fl.book.ctrs[k] as Ctr).forEach((A, j) => {
        if (!adt_triv(fl.book, A)) {
          fl.brwl.add(fields[j]);
        }
      });
    }
    fin(h, mine, [...fields, ...rest]);
  }
  if (arms.length === 1 && total === 1) {
    return arm_emit(arms[0][1], arms[0][0], armsets[0]);
  }
  const held = [...fl.uses].filter(([p, b]) =>
    !b.triv && b.owed > mx_of(p));
  for (const [p, b] of held) {
    fl.uses.set(p, { ...b, owed: Infinity });
  }
  const cond = (k: Name) => {
    if (native === undefined) {
      return `term_aux(${s}) == ${cid_reg(fl, k)}`;
    }
    const c = native.cond[k];
    if (c === undefined) {
      die(`no native test for a ${k} match`);
    }
    return tpl(c)([s]);
  };
  for (let i = 0; i < emits.length; i++) {
    if (i === emits.length - 1) {
      file_push(fl, "} else {");
    } else {
      file_push(fl, `${i === 0 ? "if" : "} else if"} (${cond(arms[i][0])}) {`);
    }
    fl.tab += 1;
    const spares = fl.spares;
    fl.spares = dst === null ? spares.slice() : [];
    const uses = new Map(fl.uses);
    emits[i]();
    fl.spares = spares;
    fl.uses = uses;
    fl.tab -= 1;
  }
  file_push(fl, "}");
  for (const [p, b] of held) {
    fl.uses.set(p, { ...b, owed: b.owed - mx_of(p) });
  }
}

// Assembly
// ========

function case_text(seg: Seg): string {
  const out: string[] = [`  WL_CASE(${seg.fid})`, "  {"];
  const fr  = seg.frame;
  if (fr !== null && fr.pop > 0) {
    out.push(`    WL_POPN(${fr.pop});`);
  }
  seg.params.forEach((p, i) => {
    let src = `r${i}`;
    if (fr !== null) {
      src = i === seg.params.length - 1 ? "res" : `STK(${fr.base + i})`;
    }
    const u = seg.unbox?.[i];
    out.push(`    ${u ?? "Term"} ${p} = ${unbox_read(u, src)};`);
  });
  if (seg.spin) {
    out.push("    WL_SPIN");
  }
  out.push(...(seg.spin ? seg.lines.map((l) => "  " + l) : seg.lines));
  if (seg.spin) {
    out.push("    WL_SPUN");
  }
  out.push("  }");
  return out.join("\n");
}

function main_show(book: Book): string {
  const main = book.tlds["main"];
  if (!def_live(main)) {
    die("no main def with a body");
  }
  const md = tele_unbind(book, main.T);
  if (md.doms.slice(0, main.n).some(dom_live)) {
    die("main must take no live parameters (the harness calls it with none)");
  }
  const walk = (T: HTerm, root: boolean): string => {
    const t = term_wnf(book, T);
    if (t.$ === "Eql") {
      return "SHOW_DASH";
    }
    if (t.$ === "ADT" && !md.doms.some(dom_live)) {
      if (t.k === "Sigma") {
        return `SHOW_SIGMA, ${walk(App(t.x[1], DUMMY), false)}, `
          + walk(t.x[0], false);
      }
      if (["Nat", "U32", "Char"].includes(t.k) || (root && t.k === "String")) {
        return "SHOW_" + t.k.toUpperCase();
      }
    }
    const k = t.$ === "ADT" ? t.k : "?";
    die(`main must answer a showable value (got ${k})`);
  };
  return walk(md.ret, true);
}

function gen_defs(fl: File): string {
  const clo = fl.segs.some((s) => s.refs.has("FID_CLO_APPLY"));
  const entries = !clo ? fl.segs : [...fl.segs, {
    fid: "FID_CLO_APPLY", def: "", params: ["", ""], frame: null } as Seg];
  const out: string[] =
    [`CONSTV u8 MAIN_PLAN[] = { ${main_show(fl.book)} };`, ""];
  for (const ms of [[...fl.cids.keys()].map((k) => [k, cid_mac(k)]),
    [...entries.map((s) => [s.def, s.fid]), ["exit", "FID_EXIT"]]]) {
    const seen = new Map();
    ms.forEach(([k, m], i) => {
      if (seen.has(m)) {
        die(`${seen.get(m)} and ${k} collide as ${m}`);
      }
      if (i > 65535) {
        die("an id over 65535");
      }
      seen.set(m, k);
      out.push(`#define ${m} ${i}`);
    });
    out.push("");
  }
  const table = (nm: string, vals: number[]) => {
    if (vals.some((v) => v > 255)) {
      die("an arity over 255");
    }
    out.push(`CONSTV u8 ${nm}[] = { ${vals.join(", ")} };`, "");
  };

  table("FID_ARITY_T", entries.map((s) => s.params.length));
  table("FID_BANGS_T", entries.map((s) => Number(fl.cb.bangs.has(s.def))));
  const cb = fl.cb;
  const deps = new Map<Name, Set<Name>>();
  const nofk = new Set<Name>();
  const wild = (s: HTerm) =>
    (s.$ === "Let" && let_chain(s, Infinity, cb.book).ls.length >= 2)
      || call_kind(cb.book, s)?.k === CLO_APPLY;
  for (const [k, tld] of done_defs(cb)) {
    const body = tld.e as HTerm;
    deps.set(k, carb_refs(cb, body));
    if (!term_any(cb.book, body, wild)) {
      nofk.add(k);
    }
  }
  for (let go = true; go;) {
    go = false;
    for (const k of nofk) {
      if ([...deps.get(k)!].some((g) => deps.has(g) && !nofk.has(g))) {
        nofk.delete(k);
        go = true;
      }
    }
  }
  table("FID_NOFK_T", entries.map((s) => Number(nofk.has(s.def))));
  table("FID_SEQK_T", entries.map((s) => Number(s.frame !== null)));
  table("CID_ARITY_T", [...fl.cids.values()].map((c) => c.arity));
  for (const [rows, i] of fl.tabs) {
    out.push(`CONSTV u64 TAB_${i}[] = { ${rows} };`, "");
  }
  const bank = Math.max(1, ...entries.filter((s) => s.frame === null)
    .map((s) => s.params.length));
  const rs = Array.from({ length: bank }, (_, i) => "r" + i).join(", ");
  const load = Array.from({ length: bank }, (_, i) => {
    const r = bank - i - 1;
    return `    case ${r + 1}: r${r} = e.mem[a + ${r}]; \\\n`;
  }).join("");
  if (clo) {
    const pass = Array.from({ length: bank }, (_, i) =>
      `    case ${i}: r${i} = res; \\\n      break; \\\n`).join("");
    out.push(`#define WL_LAST \\\n  switch (war) { \\\n${pass}  }`);
  }
  if (clo || cb.clo) {
    out.push("#define CLO_SHR 1", "");
  }
  out.push(`#define WL_BANK Term ${rs};`, "", "#define WL_LOAD \\\n"
    + `  switch (war) { \\\n${load}  }`, "",
    `#define WL_LABELS ${entries.map((s) =>
      "&&L_" + (s.dead ? "FID_EXIT" : s.fid))
      .join(", ")}, &&L_FID_EXIT`);
  return out.join("\n");
}

// Width
// -----

function width_fold(text: string): string {
  const out: string[] = [];
  for (let line of text.split("\n")) {
    const mac  = line.startsWith("#") || line.endsWith("\\");
    const bent = line.match(/^ */)![0] + "  ";
    while (line.length > 80) {
      const cap = mac ? 78 : 80;
      let end = line.lastIndexOf(" ", cap);
      let cut = end + 1;
      if (end < bent.length) {
        end = line.lastIndexOf("(", cap) + 1;
        cut = end;
        if (end <= bent.length) {
          break;
        }
      }
      out.push(line.slice(0, end) + (mac ? " \\" : ""));
      line = bent + line.slice(cut);
    }
    out.push(line);
  }
  return out.join("\n");
}

// API
// ===

function def_open(): Scratch {
  return {
    fresh:  new Map(),
    spares: [],
    uses:   new Map(),
    local:  new Set(),
    brwl:   new Set(),
    fusing: new Set(),
  };
}

function file_emit(cb: Carb, shr: Set<string>): File {
  const fl: File = {
    book:  cb.book,
    segs:  [],
    seg:   { fid: "", def: "", lines: [], params: [], frame: null,
      refs: new Set() },
    tab:   2,
    cb,
    cids:  new Map(),
    shr,
    tabs:  new Map(),
    spins: [],
    ...def_open(),
  };
  for (const [k, n] of [["Tuple", 2], ["SNil", 0], ["SCon", 2]] as const) {
    cid_reg(fl, k, n);
  }
  for (const [k, tld] of done_defs(cb)) {
    Object.assign(fl, def_open());
    const live   = live_doms(fl.book, tld);
    const params = live.map(([, n]) => local_new(fl, n));
    (fl.cb.brw.get(k) as boolean[]).forEach((b, i) => {
      if (b) {
        fl.brwl.add(params[i]);
      }
    });
    fl.seg = seg_new(fl, k, cb.mint.get(k) === true, params, k);
    fl.fusing.add(k);
    fl.seg.unbox = live.map(([, , A]) => {
      if (ty_f32(fl.book, A)) {
        return "f32";
      }
      return ty_w32(fl.book, A) ? "u32" : null;
    });
    emit_func(fl, tld.e as HTerm, tld.T, params, null);
  }
  const live = new Set<string>();
  const grab = (fid: string) => {
    if (!live.has(fid)) {
      live.add(fid);
      fl.segs.find((s) => s.fid === fid)?.refs.forEach(grab);
    }
  };
  grab(fid_of("main"));
  for (const s of fl.segs) {
    s.dead = !live.has(s.fid);
  }
  fl.spins = fl.spins.filter((_, i) => live.has(`spin_${i}`));
  return fl;
}

export function compile_book(book: Book): string {
  const cb   = carb_book(book);
  brw_build(cb);
  const fl   = file_emit(cb, shr_build(cb));
  const segs = fl.segs.filter((s) => !s.dead).map(case_text).join("\n\n");
  const spins = fl.spins.length === 0 ? "" : "#ifdef __METAL_VERSION__\n"
    + "struct Spin {\n" + fl.spins.join("\n\n") + "\n};\n#endif\n\n";
  return width_fold(TEMPLATE
    .replace(/^\/\/ Book\n\/\/ ====$/m, (m) => m + "\n\n" + gen_defs(fl))
    .replace(/^\/\/ Segments\n\/\/ ========$/m, (m) =>
      m + "\n\n" + spins + segs));
}
