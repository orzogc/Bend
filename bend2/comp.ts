// HUMAN NOTE: this file has two parts: compilers and runtimes (at the end).
// The architecture behind the runtimes was 95% designed by humans, but the file
// itself is significantly AI written and not fully audited. It can have bugs.
// The compiler is 50% designed by humans, 50% by AI, and 100% AI written. I've
// barely audited it, so, it is the most prone to bugs and overfit. In practice,
// there may be benchmarks where Bend significantly under-performs C, due to
// falling into some case that wasn't explicitly optimized for. Rather than
// hoping to cover everything that GCC handled over decades of effort, I'm
// launching it how it is, and will improve, fix bugs, and generalize, as the
// language evolves. In theory, Bend can be arbitrarily fast, for clear logical
// reasons (types, linearity, purity), and as evidenced by the several
// benchmarks and programs we've written. In practice, it will take time for it
// to cover all the shapes that a mature compiler does, and that's expected. I
// also believe I must be in peace with this file being maintained by AI moving
// forward, since this allows it to include more optimizations and features as
// models work on it and get better over time. The critical part, the trusted
// kernel, is human-audited and readable. The compiler doesn't need to be, and
// once the base architecture is designed (as AIs struggle with that), they can
// do a fairly good job at maintaining and extending the file. It is still very
// important that we keep it within a token budget, since larger files cause the
// models to lose control over it, and that's very dangerous. As models get
// larget and more capable, this limit can increase. For now, 64k works well.

import * as fs from "node:fs";

import * as Bend from "./bend.ts";

// Comp
// ====

// Types
// =====

type Kind = "w32" | "w64" | "box";

type Lay = { ks: Kind[]; arms: Arm[] | null };

type Arm = { k: Bend.Name; fs: Field[] };

type Field = { at: number; lay: Lay };

type Val = { ws: string[]; lay: Lay };

type Bind = { val: Val; n: number; A: HTerm | null };

type Dst = Val | null;

type Seg = {
  fid: string;
  def: Bend.Name;
  ret: Lay;
  lines: string[];
  params: string[];
  ks: Kind[];
  frame: { pop: number; at: number[] } | null;
  refs: Set<string>;
  dead?: boolean;
  host?: boolean;
  spin?: boolean;
  fork?: boolean;
};

type Spine = {
  h: HTerm;
  t: HTerm;
  all: HTerm[];
  args: HTerm[];
};

type HTerm = Bend.HTerm;

type Def  = Bend.Def & { h?: HTerm };

type TLD  = Bend.ADT | Def;

type Book = Omit<Bend.Book, "tlds"> & { tlds: Record<Bend.Name, TLD> };

type Carb = {
  book: Book;
  dyn: Set<Bend.Name>;
  bangs: Set<Bend.Name>;
  sites: Map<Bend.Name, number>;
  brw: Map<Bend.Name, boolean[]>;
  hot: Set<Bend.Name>;
  poly: Set<string>;
  own: Map<string, string>;
  lend: Set<string>;
};

type File = Carb & {
  spares: { words: number; name: string; z: boolean }[];
  fresh: Map<string, number>;
  uses: Map<Probe, Bind>;
  local: Set<string>;
  brwl: Map<string, Root>;
  rest: HTerm[];
  def: Bend.Name;
  pi: number;
  segs: Seg[];
  seg: Seg;
  tab: number;
  decl: string;
  cids: Map<string, [number, number]>;
  tabs: Map<string, number>;
  spins: [string, string, Set<string>][];
  spun: Map<string, string>;
  clos: Set<string>;
  reqs: string;
  resw: number;
  fuel: number;
};

type Gen = string | ((xs: string[]) => string);

type Native = {
  intr: Record<Bend.Name, Gen>;
  elim?: Record<Bend.Name, string[]>;
  cond?: Record<Bend.Name, string>;
};

type Optim = { C?: Native; JS?: Native };

type Of<K> = Extract<HTerm, { $: K }>;

type HAll = Of<"All">;

type Probe = Of<"Var">;

type HAdt = Of<"ADT">;

type HLet = Of<"Let">;

type UMap = Bend.PMap<number>;

type Level = [string, HTerm, () => Val[]];

type Chain = [HTerm, number | null][];

type Call = {
  k: Bend.Name;
  args: HTerm[];
  all: HTerm[];
  bang?: boolean;
};

type Root = [Bend.Name, number];

type Intr = {
  C?: Gen;
  parts?: string[];
  call?: boolean;
  JS: Gen;
};

type Dom = [Bend.Quant, Bend.Name, HTerm];

// Constants
// =========

const CLO_APPLY = "Clo.apply";

const ATOM   = /^(?:[A-Za-z_$][A-Za-z0-9_$]*|\d+n?|\d+\.\d+)$/;
const STRLIT = new RegExp("^\"(?:[^\"\\\\]|\\\\.)*\"$");

const NATIVE_DIE = " does not match the native format of its type";

const EXACT = " sqrt exp log log2 log10 sin cos tan pow fmod ";

// A native with this many lines or more is a call on both lanes: the
// device inlines every native into every caller (hvm5 under a bang: 32 s
// of Metal compile, 2.6 s so); at 128 raytrace lost 31% on PAR-CPU.
const SPIN_FAR = 256;

const USE0 = Bend.Emp<number>();

const W32: Lay = { ks: ["w32"], arms: null };

const BOX: Lay = { ks: ["box"], arms: null };

const W64: Lay = { ks: ["w64"], arms: null };

// A closure segment's return: a box owned by no def.
const CLO_RET: Lay = { ks: ["box"], arms: null };

const FLIP = new Error("a borrow flipped");

const WORDS: Record<string, Lay> = { U32: W32, F32: W32, Nat: W64 };

const ERRS = ("|*|*|*|out of memory: run again with a bigger span, as in"
  + " --gpu-memory 8GB|a function the device does not hold|*|a Nat past the"
  + " largest immediate 2^48-1|*|memory fault (machine stack overflow?)|an"
  + " array past the deepest block class 31").split("|")
  .map((e) => e === "*" ? "runtime fail-stop" : e);

// Operations
// ----------

const CMPS = "is_eq:==:=== is_ne:!=:!== is_lt:< is_le:<= is_gt:> is_ge:>=";

const OPERATIONS: Record<string, Intr> = Object.setPrototypeOf({
  ...tpl_ops("u32_", "add:+ sub:- and:& or:| xor:^",
    "U32_BIN($0, $o, $1)", "(($0 $o $1) >>> 0)"),
  ...tpl_ops("u32_", CMPS, "U32_BIN($0, $o, $1)", "($0 $o $1)"),
  u32_mul: {
    C:  "U32_BIN($0, *, $1)",
    JS: "(Math.imul($0, $1) >>> 0)",
  },
  u32_div: {
    C:  "((u32)($1) == 0 ? 0 : U32_BIN($0, /, $1))",
    JS: "($1 === 0 ? 0 : ($0 / $1) >>> 0)",
  },
  u32_mod: {
    C:  "((u32)($1) == 0 ? $0 : U32_BIN($0, %, $1))",
    JS: "($1 === 0 ? $0 : $0 % $1)",
  },
  ...tpl_ops("u32_", "inc:+ shl:<< shr:>>:>>>", "U32_BIN($0, $o, 1)",
    "(($0 $o 1) >>> 0)"),
  ...tpl_ops("u32_", "shln:<< shrn:>>:>>>", "($1 >= 32 ? 0 : U32_BIN($0, $o, $1))",
    "($1 >= 32n ? 0 : ($0 $o Number($1)) >>> 0)"),
  u32_not: {
    C:  "((u64)~(u32)($0))",
    JS: "(~$0 >>> 0)",
  },
  u32_is_zero: {
    C:  "U32_BIN($0, ==, 0)",
    JS: "($0 === 0)",
  },
  u32_cmp: {
    C:  "(U32_BIN($0, >, $1) + U32_BIN($0, >=, $1))",
    JS: "cmp_new($0, $1)",
  },
  u32_to_f32: {
    C:  "f32_rewrap((f32)(u32)($0))",
    JS: "Math.fround($0)",
  },
  u32_to_nat: {
    C:  "$0",
    JS: "BigInt($0)",
  },
  u32_from_nat: {
    C:  "((u64)(u32)($0))",
    JS: "Number($0 & 0xFFFFFFFFn)",
  },
  ...tpl_ops("f32_", "add:+ sub:- mul:* div:/",
    "f32_rewrap(f32_unbox($0) $o f32_unbox($1))", "Math.fround($0 $o $1)"),
  f32_neg: {
    C:  "f32_rewrap(-f32_unbox($0))",
    JS: "(-$0)",
  },
  ...tpl_ops("f32_", CMPS, "((u64)(f32_unbox($0) $o f32_unbox($1)))",
    "($0 $o $1)"),
  ...tpl_ops("f32_", "sqrt exp log log2 log10 sin cos tan asin acos atan"
    + " sinh cosh tanh floor ceil trunc abs:fabs:abs",
    "f32_rewrap((f32)$o(f32_unbox($0)))", "Math.fround(Math.$o($0))"),
  ...tpl_ops("f32_", "pow atan2",
    "f32_rewrap((f32)$o(f32_unbox($0), f32_unbox($1)))",
    "Math.fround(Math.$o($0, $1))"),
  f32_mod: {
    C:  "f32_rewrap((f32)fmod(f32_unbox($0), f32_unbox($1)))",
    JS: "Math.fround($0 % $1)",
  },
  f32_to_u32: {
    C:  "f32_to_u32($0)",
    JS: "($0 >= 1 && $0 < 4294967296 ? Math.floor($0) : 0)",
  },
  f32_bits: {
    C:  "$0",
    JS: "f32_bits($0)",
  },
  f32_show: {
    C:    "f32_show(e, $0)",
    call: true,
    JS:   "f32_show($0)",
  },
  f32_read: {
    C:    "f32_read(e, $0)",
    call: true,
    JS:   "f32_read($0)",
  },
  nat_add: {
    C:  "nat_chk(e, $0 + $1)",
    JS: "nat_chk($0 + $1)",
  },
  nat_sub: {
    C:  "($0 < $1 ? 0 : $0 - $1)",
    JS: "($0 < $1 ? 0n : $0 - $1)",
  },
  nat_mul: {
    C:  "nat_mul(e, $0, $1)",
    JS: "nat_chk($0 * $1)",
  },
  nat_double: {
    C:  "nat_chk(e, $0 + $0)",
    JS: "nat_chk($0 << 1n)",
  },
  nat_cmp: {
    C:  "(($0 > $1) + ($0 >= $1))",
    JS: "cmp_new($0, $1)",
  },
  nat_is_lt: {
    C:  "($0 < $1)",
    JS: "($0 < $1)",
  },
  nat_divmod: {
    parts: ["($1 == 0 ? 0 : $0 / $1)", "($1 == 0 ? $0 : $0 % $1)"],
    call:  true,
    JS:    "nat_divmod($0, $1)",
  },
  ...tpl_ops("bool_", "or:|:|| xor:^:!==", "(($0) $o ($1))", "($0 $o $1)"),
  string_append: {
    JS: "($0 + $1)",
  },
  array_new: {
    call: true,
    JS:   "array_new($0, $1)",
  },
  array_set: {
    call: true,
    JS:   "array_swap($0, $1, $2).fst",
  },
  array_get: {
    call: true,
    JS:   "array_get($0, $1)",
  },
  array_swap: {
    call: true,
    JS:   "array_swap($0, $1, $2)",
  },
  array_size: {
    call: true,
    JS:   "{$: \"Tuple\", fst: $0, snd: array_len($0)}",
  },
  array_clone: {
    parts: ["blk_copy(e, $0)", "$0"],
    call:  true,
    JS:    "{$: \"Tuple\", fst: $0, snd: $0}",
  },
}, null);

// Optimized
// ---------

const OPTIMIZED: Record<Bend.Name, Optim> = Object.setPrototypeOf({
  Nat: {
    C: {
      intr: {
        Zero: "0",
        Succ: tpl_nat("ull", "nat_chk(e, $0 + 1)"),
      },
    },
    JS: {
      intr: {
        Zero: "0n",
        Succ: tpl_nat("n", "nat_chk($0 + 1n)"),
      },
      elim: {
        Succ: ["($0 - 1n)"],
      },
    },
  },
  Bool: {
    JS: {
      intr: {
        False: "false",
        True:  "true",
      },
      cond: {
        False: "!$0",
        True:  "$0",
      },
    },
  },
  U32: {
    C: { intr: { U32: "term_word(e, $0)" } },
    JS: {
      intr: {
        U32: "word_to_u32($0)",
      },
      elim: {
        U32: ["u32_to_word($0)"],
      },
    },
  },
  F32: {
    C: { intr: { F32: "term_word(e, $0)" } },
    JS: {
      intr: {
        F32: "f32_from_bits(word_to_u32($0))",
      },
      elim: {
        F32: ["u32_to_word(f32_bits($0))"],
      },
    },
  },
  Char: {
    JS: {
      intr: {
        Chr: ([c]: string[]) => {
          const n = Number(c);
          return /^\d+$/.test(c)
            && (n < 0xd800 || n >= 0xe000 && n <= 0x10ffff)
            ? JSON.stringify(String.fromCodePoint(n))
            : "char_new(" + c + ")";
        },
      },
      elim: {
        Chr: ["$0.codePointAt(0)"],
      },
    },
  },
  String: {
    JS: {
      intr: {
        SNil: "\"\"",
        SCon: ([h, t]: string[]) => STRLIT.test(h) && STRLIT.test(t)
          ? JSON.stringify(JSON.parse(h) + JSON.parse(t))
          : "(" + h + " + " + t + ")",
      },
      elim: {
        SCon: ["($0.codePointAt(0) > 0xFFFF ? $0.slice(0, 2) : $0[0])",
          "($0.codePointAt(0) > 0xFFFF ? $0.slice(2) : $0.slice(1))"],
      },
      cond: {
        SNil: "$0 === \"\"",
        SCon: "$0 !== \"\"",
      },
    },
  },
}, null);

// Native
// ------

const SHIMS = EXACT.trim().split(" ")
  .map((n) => "#define " + n.padEnd(5) + " precise::" + n).join("\n");

const NATIVE = {
  C: String.raw`
#ifdef __METAL_VERSION__
${SHIMS}
#endif

#define U32_BIN(a, o, b) ((u64)((u32)(a) o (u32)(b)))

INLINE f32 f32_unbox(u64 x) {
  union { u32 u; f32 f; } p = { (u32)x };
  return p.f;
}

INLINE u64 f32_rewrap(f32 x) {
  union { f32 f; u32 u; } p = { x };
  return p.u;
}

INLINE U32 f32_to_u32(U32 a) {
  f32 v = f32_unbox(a);
  return v >= 0.0f && v < 4294967296.0f ? (u32)v : 0;
}

INLINE Nat nat_chk(Env e, Nat n) {
  if (n > NAT_IMM) {
    err_post(e.mem, ERR_NATS);
    return NAT_IMM;
  }
  return n;
}

INLINE Nat nat_mul(Env e, Nat a, Nat b) {
  return nat_chk(e, b != 0 && a > NAT_IMM / b ? NAT_IMM + 1 : a * b);
}

#if DEVICE

#define f32_show(e, x) (err_post(e.mem, ERR_FIDS), 0)
#define f32_read(e, s) (err_post(e.mem, ERR_FIDS), 0)

#else

static Term f32_show(Env e, Term x);
static Term f32_read(Env e, Term s);

#endif
`.slice(1),
  IO: String.raw`
static Term f32_show(Env e, Term x) {
  char buf[40];
  f32  v = f32_unbox(x);
  int  n = 0;
  int  p = 0;
  if (v != v) {
    return io_str(e, "nan", 3);
  }
  for (; p < 9; p += 1) {
    n = snprintf(buf, 40, "%.*e", p, (double)v);
    if (strtof(buf, NULL) == v) {
      break;
    }
  }
  char* ep = strchr(buf, 'e');
  if (ep == NULL) {
    return io_str(e, buf, n);
  }
  int ex = atoi(ep + 1);
  if (ex >= 21 || ex <= -7) {
    n = (int)(ep - buf) + sprintf(ep, "e%c%d", ex < 0 ? '-' : '+', abs(ex));
  } else if (ex <= p) {
    n = snprintf(buf, 40, "%.*f", p - ex, (double)v);
  } else {
    int s = *buf == '-';
    memmove(buf + s + 1, buf + s + 2, p);
    memset(buf + s + 1 + p, '0', ex - p);
    n = s + 1 + ex;
  }
  return io_str(e, buf, n);
}

static Term f32_read(Env e, Term s) {
  u64 n = 0;
  char* text = io_cstr(e, s, &n);
  char* end;
  f32 v = strtof(text, &end);
  Term out = n > 0 && *end == 0 ? io_box(e, CID_SOME, f32_rewrap(v), 0)
    : term_pak(CID_NONE, 0);
  free(text);
  return out;
}
`.slice(1),
  JS: String.raw`
function word_to_u32(w) {
  let x = 0;
  for (let i = 0; w.$ === "WCon"; i++) {
    x |= Number(w.head) << i;
    w = w.tail;
  }
  return x >>> 0;
}

function u32_to_word(x) {
  let w = {$: "WNil"};
  for (let i = 31; i >= 0; i--) {
    w = {$: "WCon", head: ((x >>> i) & 1) === 1, tail: w};
  }
  return w;
}

function cmp_new(a, b) {
  return {$: a < b ? "LT"
    : a === b ? "EQ" : "GT"};
}

function nat_divmod(a, b) {
  return b === 0n ? {$: "Tuple", fst: 0n, snd: a}
    : {$: "Tuple", fst: a / b, snd: a % b};
}

function nat_chk(n) {
  if (n > 281474976710655n) {
    throw "bend: ${ERRS[7]}";
  }
  return n;
}

function f32_show(x) {
  if (x !== x) {
    return "nan";
  }
  if (!Number.isFinite(x) || Object.is(x, -0)) {
    return x < 0 ? "-inf"
      : x === 0 ? "-0" : "inf";
  }
  let s = "x";
  for (let p = 1; p <= 9 && Math.fround(Number(s)) !== x; p += 1) {
    s = String(Number(x.toExponential(p - 1)));
  }
  return s;
}

function f32_bits(x) {
  return new Uint32Array(new Float32Array([x]).buffer)[0];
}

function f32_from_bits(u) {
  return new Float32Array(new Uint32Array([u]).buffer)[0];
}

function f32_read(s) {
  const re = /^\s*[+-]?((\d+\.?\d*|\.\d+)(e[+-]?\d+)?|inf(inity)?|nan)$/i;
  const v = Number(s.replace(/inf\w*/i, "Infinity"));
  return re.test(s) ? {$: "Some", value: Math.fround(v)} : {$: "None"};
}

function char_new(code) {
  if (code > 0x10FFFF || (code >= 0xD800 && code <= 0xDFFF)) {
    throw "bend: " + code + " is not a Unicode scalar value";
  }
  return String.fromCodePoint(code);
}
`.slice(1),
};

// Caches
// ------

const PROBES: Probe[] = [];

const DUMMY = probe("~");

const OPENS: Map<Of<"Lam"> | HLet, { ps: Probe[]; b: HTerm }> = new Map();

const USES: Map<HTerm, UMap> = new Map();

const TELES: Map<HTerm, ReturnType<typeof Bend.tele_unbind>> = new Map();

const REFS: Map<Bend.Name, Set<Bend.Name>> = new Map();

const LOCAL: Map<Bend.Name, string> = new Map();

const FOLDS: Map<HTerm, HTerm | null> = new Map();

const FLATS: Map<Bend.Name, boolean> = new Map();

const INTRS: Map<Bend.Name, Intr | null> = new Map();

const SPINES: Map<HTerm, Spine> = new Map();

const LAYS: Map<HTerm, Lay> = new Map();

const NODES: Map<Bend.Name, Lay> = new Map();

const CYCLES: Map<Bend.Name, boolean> = new Map();

const CONSTS: Map<HTerm, boolean> = new Map();

// Name
// ====

function name_clean(k: string): string {
  return (LOCAL.get(k) ?? k).replace(/[^A-Za-z0-9_]/g, "_");
}

function name_local(fl: File, k: Bend.Name): string {
  const base = name_clean(k);
  const n = fl.fresh.get(base) ?? 0;
  fl.fresh.set(base, n + 1);
  const name = base + "_" + n;
  fl.local.add(name);
  return name;
}

// Die
// ===

function die(m: string): never {
  throw new Error(m);
}

// Tpl
// ===

function tpl_ops(pre: string, names: string, C: string, JS: string):
  Record<string, Intr> {
  const out: Record<string, Intr> = {};
  for (const p of names.split(" ")) {
    const [k, o = k, jo = o] = p.split(":");
    out[pre + k] = { C: C.replaceAll("$o", o), JS: JS.replaceAll("$o", jo) };
  }
  return out;
}

function tpl(t: Gen, xs: string[]): string {
  return typeof t !== "string" ? t(xs)
    : t.split(/\$(\d)/).map((p, i) => (i % 2 === 1 ? xs[+p] : p)).join("");
}

function tpl_nat(u: string, f: string): Gen {
  return ([p]) => /^\d/.test(p) ? (BigInt(parseInt(p)) + 1n) + u
    : tpl(f, [p]);
}

// Memo
// ====

function memo<K, V>(m: Map<K, V>, k: K, f: () => V): V {
  const got = m.get(k);
  if (got !== undefined) {
    return got;
  }
  const out = f();
  m.set(k, out);
  return out;
}

function memo_gc(): void {
  [OPENS, USES, FOLDS, SPINES, CONSTS, LAYS].forEach((m) => m.clear());
}

// Probe
// =====

function probe(k: Bend.Name): Probe {
  const p = Bend.Var(k, PROBES.length) as Probe;
  PROBES.push(p);
  return p;
}

function probe_of(t: HTerm): Probe {
  return PROBES[(Bend.term_force(t) as Probe).i];
}

// Term
// ====

function term_open(t: Of<"Lam"> | HLet): { ps: Probe[]; b: HTerm } {
  return memo(OPENS, t, () => {
    const ps = (t.$ === "Lam" ? [t.k] : t.k).map(probe);
    return { ps, b: t.$ === "Lam" ? t.f(ps[0]) : t.f(ps) };
  });
}

// A let opened ahead: its body `b` over `ps` is never rebuilt.
function let_open(ps: Probe[], vs: HTerm[], b: HTerm): HLet {
  const l = Bend.Let(ps.map((p) => p.k), ps.map(() => 0), vs,
    () => die("a pre-opened let"));
  OPENS.set(l, { ps, b });
  return l;
}

// A let's live binders: an erased or unused one dies with its value.
function let_live(cb: Carb, t: HLet): boolean[] {
  const o = term_open(t);
  const u = term_uses(cb, o.b);
  return t.q.map((q, j) => quant_live(q) && term_use(u, o.ps[j]) > 0);
}

function term_spine(cf: Carb, tm: HTerm): Spine {
  return memo(SPINES, tm, () => {
    const apps: Of<"App">[] = [];
    let h = tm;
    let c = Bend.term_force(tm);
    while (c.$ === "Ann" || c.$ === "App") {
      if (c.$ === "App") {
        apps.push(c);
        h = c.f;
      }
      c = Bend.term_force(c.$ === "App" ? c.f : c.x);
    }
    apps.reverse();
    const tld = c.$ === "Ref" ? cf.book.tlds[c.k] : undefined;
    const T = tld?.$ === "Def" ? tld.T : ty_ann(h);
    const qs = T && tele_unbind(cf.book, T).doms;
    const live = (i: number) => qs === null
      ? call_live(cf.book, apps[i].f)
      : i >= qs.length || quant_live(qs[i][0]);
    const all = apps.map((a) => a.x);
    return { h, t: c, all, args: all.filter((_, i) => live(i)) };
  });
}

function term_eta(book: Bend.Book, t: HTerm, T: HTerm, n: number,
  leaf: (u: HTerm, U: HTerm) => HTerm = (u) => u): HTerm {
  if (n === 0) {
    return leaf(t, T);
  }
  const all = ty_all(book, T) ?? die("an eta past its type");
  return Bend.Ann(Bend.Lam("x", 0, (y) =>
    term_eta(book, Bend.App(t, y), all.B(y), n - 1, leaf)), T);
}

function term_kids(cf: Carb, tm: HTerm): HTerm[] {
  const t = Bend.term_force(tm);
  switch (t.$) {
    case "Ann": return [t.x];
    case "Lam": return [term_open(t).b];
    case "Let": {
      const on = let_live(cf, t);
      return [...t.v.filter((_, j) => on[j]), term_open(t).b];
    }
    case "App": {
      const m = term_spine(cf, t);
      return [m.h, ...m.args];
    }
    case "Ctr": return term_const(t) ? [] : ctr_flds(cf.book, t.k, t.x);
    case "Mat": return [t.h, t.m];
    case "Rwt": return [t.f];
    default: return [];
  }
}

function term_any(cf: Carb, t: HTerm, p: (s: HTerm) => boolean,
  seen: Set<HTerm> = new Set()): boolean {
  const s = Bend.term_force(t);
  if (seen.has(s)) {
    return false;
  }
  seen.add(s);
  return p(s) || term_kids(cf, s).some((x) => term_any(cf, x, p, seen));
}

function term_const(t: HTerm): boolean {
  const s = Bend.term_strip(t);
  return s.$ === "Ctr" && memo(CONSTS, s, () => s.x.every(term_const));
}

function term_use(u: UMap, p: Probe): number {
  return Bend.pmap_get(u, p.i) ?? 0;
}

// The uses of each probe in a term.
function term_uses(cb: Carb, tm: HTerm): UMap {
  return memo(USES, tm, () => {
    const t = Bend.term_force(tm);
    switch (t.$) {
      case "Var": {
        const p = probe_of(t);
        return p === DUMMY ? USE0 : Bend.pmap_set(USE0, p.i, 1);
      }
      case "Mat": return Bend.pmap_union(term_uses(cb, t.h),
        term_uses(cb, t.m), Math.max);
      default: return term_kids(cb, t).reduce((u, x) =>
        Bend.pmap_union(u, term_uses(cb, x), (a, b) => a + b), USE0);
    }
  });
}

function rest_use(cb: Carb, rest: HTerm[], p: Probe): number {
  return rest.reduce((n, r) => n + term_use(term_uses(cb, r), p), 0);
}

// Live
// ====

function live_dom([q]: Dom): boolean {
  return quant_live(q);
}

function live_doms(book: Bend.Book, tld: Bend.Def): Dom[] {
  return def_get_params(book, tld).filter(live_dom);
}

// Intr
// ====

function intr_of(c: Carb, k: Bend.Name, js = false): Intr | undefined {
  const it = memo(INTRS, k, () => {
    const tld = c.book.tlds[k];
    return tld?.$ === "Def" && tld.i === undefined && (tld.b || tld.v === null)
      ? OPERATIONS[eff_name(k)] ?? null : null;
  });
  return it !== null && (js || it.C !== undefined || it.parts !== undefined
    || it.call === true) ? it : undefined;
}

// Call
// ====

function call_live(book: Bend.Book, f: HTerm): boolean {
  const all = ty_all(book, ty_ann(f));
  return all === null || quant_live(all.q);
}

function call_kind(c: Carb, t: HTerm): Call | null {
  const m = term_spine(c, t);
  let dyn = m.t.$ === "Var" && m.args.length > 0;
  if (m.t.$ === "Ref" && intr_of(c, m.t.k) === undefined) {
    const tld = def_body(c, m.t.k);
    if (tld?.$ === "Def" && (done_live(tld) || def_foreign(tld))) {
      const live = def_live(c, tld);
      if (m.args.length === live) {
        return { k: m.t.k, args: m.args, all: m.all, bang: m.t.b };
      }
      dyn = m.args.length > live;
    }
  }
  if (!dyn) {
    return null;
  }
  let f = Bend.term_force(t);
  while (f.$ === "Ann" || (f.$ === "App" && !call_live(c.book, f.f))) {
    f = Bend.term_force(f.$ === "App" ? f.f : f.x);
  }
  const a = f as Of<"App">;
  return { k: CLO_APPLY, args: [a.f, a.x], all: [a.f, a.x] };
}

function call_is(cb: Carb, t: HTerm): boolean {
  return call_kind(cb, t) !== null;
}

function call_eta(cb: Carb, t: HTerm): HTerm | null {
  const m = term_spine(cb, t);
  const pre = m.t.$ === "Ref" ? def_body(cb, m.t.k) : undefined;
  if (m.t.$ !== "Ref" || pre?.$ !== "Def"
    || m.args.length >= live_doms(cb.book, pre).length) {
    return null;
  }
  const T = ty_tele(cb.book, pre.T, m.all);
  const n = pre.n - m.all.length;
  const intr = intr_of(cb, m.t.k) !== undefined;
  const last = live_doms(cb.book, pre).at(-1)?.[2] ?? null;
  const direct = last === null || lay_of(cb.book, last).arms === null;
  if (n === 1 && !intr && direct) {
    cb.dyn.add(m.t.k);
    return null;
  }
  const cut = (u: HTerm, U: HTerm): HTerm => Bend.Let(["r"], [0],
    [Bend.Ann(u, U)], (xs: HTerm[]) => Bend.Ann(xs[0], U));
  return term_eta(cb.book, t, T, n, intr || direct ? undefined : cut);
}

// Tele
// ====

function tele_unbind(book: Bend.Book,
  T: HTerm): ReturnType<typeof Bend.tele_unbind> {
  return memo(TELES, T, () => Bend.tele_unbind(book, T));
}

// Ty
// ==

function ty_ann(t: HTerm): HTerm | null {
  const v = Bend.term_force(t);
  return v.$ === "Ann" ? v.T : null;
}

function ty_wnf(book: Bend.Book, ty: HTerm | null): HTerm | null {
  return ty && Bend.term_wnf(book, ty);
}

function ty_all(book: Bend.Book, ty: HTerm | null): HAll | null {
  return ty && Bend.tele_open(book, ty);
}

function ty_tele(book: Bend.Book, T: HTerm, args: HTerm[]): HTerm {
  return Bend.tele_fill(book, T, args, Bend.ctx_nil());
}

function ty_peel(tm: HTerm,
  ty: HTerm | null): [HTerm, HTerm | null] {
  let x = Bend.term_force(tm);
  while (x.$ === "Ann" || x.$ === "Rwt") {
    ty = x.$ === "Ann" ? x.T : ty;
    x = Bend.term_force(x.$ === "Ann" ? x.x : x.f);
  }
  return [x, ty];
}

function ty_adt(book: Bend.Book, A: HTerm | null): HAdt | null {
  const t = ty_wnf(book, A);
  return t?.$ === "ADT" ? t : null;
}

// A type may hold a closure: a function, a variable or a stuck type, or a
// datatype whose live fields may (walked once per datatype); a word type,
// a quantity (List<&2, U32>) or a kind holds none.
function ty_clo(book: Bend.Book, A: HTerm | null,
  seen = new Set<Bend.Name>()): boolean {
  const t = ty_wnf(book, A);
  switch (t?.$) {
    case "ADT": {
      const tld = book.tlds[t.k];
      return WORDS[t.k] === undefined && (t.x.some((x) =>
        ty_clo(book, x, seen)) || (tld?.$ === "ADT" && !seen.has(t.k)
        && seen.add(t.k) && tld.c.some((c) =>
        ctr_doms(book, c, t.x).some((f) => ty_clo(book, f, seen)))));
    }
    case "Typ": case "Qua": case "Min": case "Eql": return false;
    default: return true;
  }
}

// Lay
// ===

function lay_of(book: Bend.Book, A: HTerm | null): Lay {
  const t = ty_adt(book, A);
  if (t === null) {
    return BOX;
  }
  return memo(LAYS, t, () => {
    const tld = book.tlds[t.k];
    return WORDS[t.k] ?? (t.k === "Array" || tld?.$ !== "ADT"
      || lay_cyclic(book, t.k) ? BOX : lay_pack(tld.c.map((c): Arm =>
      ({ k: c.k, fs: lay_fields(book, ctr_doms(book, c, t.x)) }))));
  });
}

function lay_fields(book: Bend.Book, As: (HTerm | null)[]): Field[] {
  const fs: Field[] = [];
  let at = 0;
  for (const A of As) {
    const lay = lay_of(book, A);
    fs.push({ at, lay });
    at += lay.ks.length;
  }
  return fs;
}

function lay_pack(arms: Arm[]): Lay {
  const tag = arms.length > 1 ? 1 : 0;
  const ks: Kind[] = tag === 1 ? ["w32"] : [];
  for (const arm of arms) {
    for (const f of arm.fs) {
      f.at += tag;
      f.lay.ks.forEach((k, j) => {
        const at = f.at + j;
        const old = ks[at] ?? "w32";
        ks[at] = old === "box" || k === "box" ? "box"
          : old === "w64" || k === "w64" ? "w64" : "w32";
      });
    }
  }
  return { ks, arms };
}

function lay_cyclic(book: Bend.Book, k: Bend.Name): boolean {
  const seen = new Set<Bend.Name>();
  const hits = (A: HTerm): boolean => {
    const a = ty_adt(book, A);
    return a !== null && (a.k === k || a.x.some(hits)
      || (!seen.has(a.k) && seen.add(a.k) && walk(a.k)));
  };
  const walk = (d: Bend.Name): boolean => {
    const tld = book.tlds[d];
    return tld?.$ === "ADT" && WORDS[d] === undefined && d !== "Array"
      && tld.c.some((c) => ctr_doms(book, c).some(hits));
  };
  return memo(CYCLES, k, () => walk(k));
}

function lay_node(book: Bend.Book, k: Bend.Name): Lay {
  return memo(NODES, k, () => {
    const ctr = book.ctrs[k];
    const As = ctr ? ctr_doms(book, ctr) : [];
    return lay_pack([{ k, fs: lay_fields(book, As) }]);
  });
}

function lay_eq(a: Lay, b: Lay): boolean {
  return a === b || JSON.stringify(a) === JSON.stringify(b);
}

function lay_c(k: Kind): string {
  return k === "w32" ? "u32" : "Term";
}

function lay_box(lay: Lay): boolean {
  return lay.arms === null && lay.ks[0] === "box";
}

function lay_arm(lay: Lay, k: Bend.Name): Arm {
  return lay.arms!.find((a) => a.k === k)
    ?? die(`a constructor outside its layout: ${k}`);
}

function lay_arr(lay: Lay): { arr: boolean; lgs: number } {
  return { arr: lay.ks.some((k) => k !== "w32"),
    lgs: cls_fit(Math.max(1, lay.ks.length)) };
}

// Ctr
// ===

function ctr_adt(fl: File, x: Of<"Ctr">,
  ty: HTerm | null): [HAdt, number | null] {
  const ctr = fl.book.ctrs[x.k];
  const T = ty ?? (ctr ? tele_unbind(fl.book, ctr.T).ret : null);
  const adt = ty_adt(fl.book, T);
  if (adt === null || (ty === null && adt.x.length > 0)) {
    die("a constructor outside a datatype");
  }
  const word = adt.k === "U32" || adt.k === "F32";
  return [arr_open(fl.book, adt), word ? Bend.u32_from_term(x, adt.k) : null];
}

function ctr_tail(book: Bend.Book, ctr: Bend.Ctr): Dom[] {
  const doms = tele_unbind(book, ctr.T).doms;
  return doms.slice(doms.length - ctr.n);
}

function ctr_doms(book: Bend.Book, ctr: Bend.Ctr, xs?: HTerm[]): HTerm[] {
  const doms = xs === undefined ? ctr_tail(book, ctr)
    : tele_unbind(book, ty_tele(book, ctr.T, xs)).doms;
  return doms.filter(live_dom).map(([, , A]) => A);
}

function ctr_flds(book: Bend.Book, k: Bend.Name,
  xs: HTerm[]): HTerm[] {
  const ctr = book.ctrs[k];
  const qs = ctr && ctr_tail(book, ctr).map(([q]) => q);
  return xs.filter((_, j) => qs?.[j] === undefined || quant_live(qs[j]));
}

function ctr_build(fl: File, k: Bend.Name, exprs: string[]): string {
  const cid = cid_reg(fl, k);
  const node = lay_node(fl.book, k);
  if (exprs.length === 0 || (node.ks.length === 1 && node.ks[0] === "w32")) {
    return `term_pak(${cid}, ${exprs[0] ?? 0})`;
  }
  const alloc = `heap_alloc(e, cls_fit(${exprs.length}))`;
  const at = fl.spares.findIndex((s) =>
    cls_fit(s.words) === cls_fit(exprs.length));
  const s = at < 0 ? null : fl.spares.splice(at, 1)[0];
  const got = s === null ? alloc : s.z ? `${s.name} ? ${s.name} : ${alloc}`
    : s.name;
  return `term_ctr(${cid}, ${node_fill(fl, "nd", got, exprs,
    fl.hot.has(k))})`;
}

// Mat
// ===

function mat_adt(book: Bend.Book, A: HTerm | null): HAdt {
  return arr_open(book, ty_adt(book, A) ?? die("a match off a datatype"));
}

function mat_head(t: HTerm): boolean {
  return t.$ === "Mat" || t.$ === "Efq";
}

// A function value: a match, or a lambda over a live binder.
function fun_live(book: Bend.Book, x: HTerm, ty: HTerm | null): boolean {
  return mat_head(x) || (x.$ === "Lam"
    && quant_live((ty_all(book, ty) ?? die("an untyped binder")).q));
}

function mat_arms(t: HTerm): { arms: [Bend.Name, HTerm][]; end: HTerm } {
  const arms: [Bend.Name, HTerm][] = [];
  let cur = t;
  for (let m = Bend.term_strip(cur); m.$ === "Mat"; m = Bend.term_strip(cur)) {
    arms.push([m.k, m.h]);
    cur = m.m;
  }
  return { arms, end: cur };
}

// Quant
// =====

function quant_live(q: Bend.Quant): boolean {
  return q.$ !== "None";
}

// Def
// ===

function def_get_params(book: Bend.Book, def: Bend.Def): Dom[] {
  const doms = tele_unbind(book, def.T).doms;
  if (doms.length < def.n) {
    die("a short def type");
  }
  return doms.slice(0, def.n);
}

function def_raise(book: Bend.Book, t: HTerm, left: number): number {
  const s = Bend.term_strip(t);
  if (s.$ === "Lam") {
    const b = term_open(s).b;
    return left > 0 ? def_raise(book, b, left - 1) : 1 + def_raise(book, b, 0);
  }
  if (s.$ === "Mat") {
    const ctr = book.ctrs[s.k];
    const d = ctr === undefined ? 0 : ctr_tail(book, ctr).length;
    return Math.min(def_raise(book, s.h, left - 1 + d),
      def_raise(book, s.m, left));
  }
  return s.$ === "Efq" ? 99 : 0;
}

function def_foreign(tld: Bend.TLD | undefined):
  tld is Bend.Def & { i: string[] } {
  return tld?.$ === "Def" && tld.i !== undefined;
}

function def_live(c: Carb, tld: Bend.Def): number {
  return live_doms(c.book, tld).length + Number(def_foreign(tld));
}

function def_lays(cb: Carb, k: Bend.Name): Lay[] {
  if (k === CLO_APPLY) {
    return [BOX, BOX];
  }
  const tld = cb.book.tlds[k] as Bend.Def;
  const lays = live_doms(cb.book, tld).map(([, , A]) => lay_of(cb.book, A));
  return def_foreign(tld) ? lays.map(() => BOX).concat([BOX]) : lays;
}

function def_ret_type(book: Bend.Book, tld: Bend.Def): HTerm {
  return ty_tele(book, tld.T, Array(tld.n).fill(DUMMY));
}

function def_ret(cb: Carb, k: Bend.Name): Lay {
  const tld = cb.book.tlds[k] as Bend.Def;
  const lay = k === CLO_APPLY || cb.dyn.has(k) || def_foreign(tld) ? BOX
    : lay_of(cb.book, def_ret_type(cb.book, tld));
  return lay.ks.length === 0 ? BOX : lay;
}


// Eff
// ===

function eff_name(k: Bend.Name): string {
  return (LOCAL.get(k) ?? k).toLowerCase().replace(/[./]/g, "_");
}

function eff_src(path: string, seen: Set<string>): string {
  path = fs.realpathSync(path);
  if (seen.has(path)) {
    return "";
  }
  seen.add(path);
  return fs.readFileSync(path, "utf8");
}

// Io
// ==

export function io_base(book: Bend.Book, t: HTerm): HTerm[] | null {
  const io = book.tlds["IO"];
  if (io?.$ !== "Def" || io.b !== true) {
    return null;
  }
  const tlds = { ...book.tlds, IO: { ...io, v: null } };
  const [h, xs] = Bend.term_unapply(Bend.term_wnf({ ...book, tlds }, t));
  return h.$ === "Ref" && h.k === "IO" ? xs : null;
}

export function io_type(book: Bend.Book, k: Bend.Name = "main"): HTerm | null {
  const main = book.tlds[k];
  const xs = main?.$ === "Def" ? io_base(book, main.T) : null;
  if (xs !== null && def_foreign(main as Bend.Def)) {
    die("main must be a filled def: a foreign main cannot anchor IO");
  }
  return xs?.length === 1 ? xs[0] : null;
}

// The program's entry: main when it is IO, else main.io, minted once to
// print main's normal form, taken here: a pure main is a constant.
function io_entry(book: Bend.Book): Bend.Name {
  const main = book.tlds["main"];
  if (main?.$ !== "Def" || (main.v === null && main.i === undefined)
    || book.tlds["IO"] === undefined) {
    die("no main to run");
  }
  if (io_type(book) !== null) {
    return "main";
  }
  if (book.tlds["main.io"] === undefined) {
    const snf = Bend.term_lower(Bend.term_snf(book, main.v as HTerm));
    const text = [...Bend.term_show(snf)].map((c) =>
      Bend.char_show(c.codePointAt(0) as number, '"')).join("");
    const n0 = book.order.length;
    Bend.parse_book(book, "", ["def main.io() -> IO(Unit):",
      `  IO.print("${text}")`, ""].join("\n"));
    Bend.book_valid(book, n0);
  }
  return "main.io";
}

export function io_run(book: Bend.Book): number {
  const src = js_lib(book, ["main"], null) + "\n" + RUNTIME_MAIN
    + "\nreturn io_run(" + js_sat("main") + ");";
  return new Function("require", src)(import.meta.require) as number;
}

// Anf
// ===
// A statement in normal form: a fork, a cut, a let of a value, or a tail.

function anf(cb: Carb, t: HTerm, ty: HTerm | null = null): HTerm {
  const binds: [Probe, HTerm][] = [];
  const cut = (r: HTerm, T: HTerm | null): HTerm => {
    if (!call_is(cb, r) || flat_call(cb, r)) {
      return r;
    }
    const p = probe("h");
    binds.push([p, Bend.Ann(r, T ?? die("an untyped cut"))]);
    return Bend.Ann(p, T as HTerm);
  };
  const go = (u: HTerm, top: boolean, T: HTerm | null): HTerm => {
    const s = Bend.term_force(u);
    if (term_const(s)) {
      return s;
    }
    switch (s.$) {
      case "Ann": {
        const x = go(s.x, top, s.T);
        return x === s.x ? s : Bend.Ann(x, s.T, s.s);
      }
      case "Rwt": return go(s.f, top, T);
      case "Ctr": {
        const on = ctr_flds(cb.book, s.k, s.x);
        const xs = s.x.map((x) => on.includes(x) ? go(x, false, null) : x);
        return xs.every((x, j) => x === s.x[j]) ? s : Bend.Ctr(s.k, xs, s.s);
      }
      case "Ref":
      case "App": {
        const m = term_spine(cb, s);
        // A spine's proper prefix that is a call (an over-application) cuts;
        // an erased application of a variable is the variable.
        const spine = (v: HTerm): HTerm => {
          const f = Bend.term_force(v);
          if (f.$ === "Ann") {
            const x = spine(f.x);
            return x === f.x ? f : Bend.Ann(x, f.T, f.s);
          }
          if (f.$ !== "App") {
            return f;
          }
          if (m.t.$ === "Var" && !m.args.includes(f.x)) {
            return spine(f.f);
          }
          const g = cut(spine(f.f), ty_ann(f.f));
          const x = m.args.includes(f.x) ? go(f.x, false, null) : f.x;
          return g === f.f && x === f.x ? f : Bend.App(g, x, f.s);
        };
        const r = spine(s);
        return top ? r : cut(r, T);
      }
      case "Let": {
        const o = term_open(s);
        const on = let_live(cb, s);
        s.v.forEach((v, j) => on[j] && binds.push([o.ps[j], go(v, true, null)]));
        return go(o.b, top, T);
      }
      case "Lam": {
        const all = ty_all(cb.book, T);
        if (all === null || quant_live(all.q)) {
          return s;
        }
        return Bend.Ann(go(s.f(DUMMY), top, all.B(DUMMY)), all.B(DUMMY));
      }
      default: return s;
    }
  };
  const wrap = (b: HTerm): HTerm =>
    binds.reduceRight((b2, [p, v]) => let_open([p], [v], b2), b);
  const x = Bend.term_force(t);
  if (x.$ !== "Let") {
    const b = go(x, true, ty);
    return wrap(binds.length === 0 || ty === null ? b : Bend.Ann(b, ty));
  }
  const o = term_open(x);
  const on = let_live(cb, x);
  const ps = o.ps.filter((_, j) => on[j]);
  const vs = x.v.filter((_, j) => on[j]);
  if (ps.length === 0) {
    return o.b;
  }
  if (ps.length >= 2 && !vs.every((v) => call_is(cb, v))) {
    return anf(cb, ps.reduceRight((b, p, j) => let_open([p], [vs[j]], b), o.b));
  }
  const ws = vs.map((v) => go(v, true, null));
  return wrap(on.every(Boolean) && ws.every((w, j) => w === x.v[j]) ? x
    : let_open(ps, ws, o.b));
}

// Carb
// ====

function def_body(cb: Carb, k: Bend.Name): TLD | undefined {
  const tld = cb.book.tlds[k];
  if (tld?.$ === "Def" && tld.e !== undefined && tld.h === undefined) {
    const h = Bend.term_higher(tld.e);
    const n = tld.n + Math.min(def_raise(cb.book, h, tld.n),
      tele_unbind(cb.book, tld.T).doms.length - tld.n);
    cb.book.tlds[k] = { ...tld, n, h };
  }
  return cb.book.tlds[k];
}

// The reachable defs (REFS), raised, with the bangs and call-site counts.
function carb_book(src: Bend.Book, roots: Bend.Name[]): Carb {
  [TELES, REFS, NODES, CYCLES, FLATS, INTRS].forEach((m) => m.clear());
  LOCAL.clear();
  for (const [k, tld] of Object.entries(src.tlds)) {
    if (def_foreign(tld)) {
      const src  = tld.T.s?.src ?? "";
      const segs = k.split(".");
      LOCAL.set(k, segs.map((_, i) => segs.slice(i).join(".")).find((own) =>
        new RegExp("^(def|law) " + own.replace(/\./g, "\\.") + "[(:\\s]", "m")
          .test(src)) ?? k);
    }
  }
  const cb: Carb = {
    book: { ...src, tlds: { ...src.tlds } },
    dyn: new Set(roots),
    bangs: new Set(),
    sites: new Map(),
    brw: new Map(),
    hot: new Set(),
    poly: new Set(),
    own: new Map(),
    lend: new Set(),
  };
  for (const queue = roots.slice(); queue.length > 0;) {
    const d = queue.shift() as Bend.Name;
    if (REFS.has(d)) {
      continue;
    }
    memo_gc();
    const tld = def_body(cb, d);
    const refs = new Set<Bend.Name>();
    REFS.set(d, refs);
    if (!done_live(tld)) {
      continue;
    }
    term_any(cb, tld.h as HTerm, (s) => {
      if (s.$ === "Ref") {
        if (s.b) {
          cb.bangs.add(s.k);
        }
        if (intr_of(cb, s.k) === undefined) {
          refs.add(s.k);
          cb.sites.set(s.k, (cb.sites.get(s.k) ?? 0) + 1);
        }
      }
      return false;
    });
    queue.push(...refs);
  }
  return cb;
}

// Flat
// ====

function flat_call(c: Carb, t: HTerm): boolean {
  const ck = call_kind(c, t);
  return ck !== null && ck.bang !== true && ck.k !== CLO_APPLY
    && flat_of(c, ck.k);
}

function flat_tails(cb: Carb, t: HTerm): Bend.Name[] {
  const [s] = ty_peel(t, null);
  switch (s.$) {
    case "Lam": return flat_tails(cb, term_open(s).b);
    case "Mat": return [...flat_tails(cb, s.h), ...flat_tails(cb, s.m)];
    case "Let": return flat_tails(cb, term_open(s).b);
    default: {
      const ck = call_kind(cb, s);
      return ck ? [ck.k] : [];
    }
  }
}

function flat_of(cb: Carb, k: Bend.Name): boolean {
  return memo(FLATS, k, () => {
    const tld = def_body(cb, k);
    if (tld?.$ !== "Def" || tld.h === undefined || def_foreign(tld)) {
      return false;
    }
    const body = tld.h;
    FLATS.set(k, false);
    let selfs = 0;
    const bad = term_any(cb, body, (s) => {
      if (s.$ === "Let" && s.k.length >= 2) {
        return true;
      }
      if (s.$ === "Ann") {
        return false;
      }
      const ck = call_kind(cb, s);
      if (ck === null) {
        return false;
      }
      selfs += Number(ck.k === k);
      return ck.bang === true || ck.k === CLO_APPLY
        || (ck.k !== k && !flat_of(cb, ck.k));
    });
    return !bad && selfs === flat_tails(cb, body).filter((c) => c === k).length;
  });
}

// Done
// ====

function done_live(tld: Bend.TLD | undefined): tld is Bend.Def {
  return tld?.$ === "Def" && tld.v !== null;
}

function done_defs(cb: Carb, live = done_live): [Bend.Name, Def][] {
  return [...REFS.keys()].map((k) => [k, cb.book.tlds[k]] as [Bend.Name, Def])
    .filter((p) => live(p[1]));
}

// Cid
// ===

function cid_mac(k: string): string {
  return "CID_" + name_clean(k).toUpperCase();
}

function cid_reg(fl: File, k: Bend.Name): string {
  if (!fl.cids.has(k)) {
    const ks = lay_node(fl.book, k).ks;
    fl.cids.set(k, [ks.length, ks.lastIndexOf("box") + 1]);
  }
  return cid_mac(k);
}

// File
// ====

function file_new(cb: Carb, decl: string): File {
  return { ...cb, decl, segs: [], seg: seg_new("", BOX, []), tab: 2,
    cids: new Map(), tabs: new Map(), spins: [], spun: new Map(), clos: new Set(),
    reqs: "", resw: 1, fuel: 0, fresh: new Map(), spares: [], uses: new Map(),
    local: new Set(), brwl: new Map(), rest: [], def: "", pi: 0 };
}

function file_push(fl: File, line: string): void {
  fl.seg.lines.push("  ".repeat(fl.tab) + line);
}

// Block
// =====

function block(fl: File, open: string, go: () => void): void {
  file_push(fl, open);
  fl.tab += 1;
  go();
  fl.tab -= 1;
  file_push(fl, "}");
}

// Cls
// ===

function cls_fit(words: number): number {
  return 32 - Math.clz32(words - 1);
}

// Spare
// =====

function spare_free(fl: File, words: number, name: string,
  z: boolean): void {
  file_push(fl,
    `${z ? "spare_free" : "heap_free"}(e, cls_fit(${words}), ${name});`);
}

function spare_flush(fl: File): void {
  for (const s of fl.spares.reverse()) {
    spare_free(fl, s.words, s.name, s.z);
  }
  fl.spares = [];
}

// Seg
// ===

function seg_new(name: string, ret: Lay, params: string[],
  ks: Kind[] = params.map(() => "w64"), frame: Seg["frame"] = null): Seg {
  return { fid: seg_fid(name), def: name, ret, lines: [], params, ks, frame,
    refs: new Set() };
}

function seg_fid(k: Bend.Name): string {
  return "FID_" + name_clean(k).toUpperCase();
}

function seg_ref(fl: File, fid: string): string {
  fl.seg.refs.add(fid);
  return fid;
}

// A closure over `fid` holding `words` (so the device holds `fid`).
function seg_clo(fl: File, fid: string, words: string[]): string {
  fl.clos.add(fid);
  return `term_clo(${seg_ref(fl, fid)}, ${words.length === 0 ? 0 : node_fill(
    fl, "nd", `heap_alloc(e, cls_fit(${words.length}))`, words)})`;
}

function seg_name(fl: File, stem: string): string {
  return fl.seg.def.split("$")[0] + "$" + stem + fl.segs.length;
}

// Opens `name`: takes `live` (per `frame`, else in r0..), then `ks` words.
function seg_open(fl: File, name: string, ret: Lay, frame: Seg["frame"],
  live: [Probe, Bind][], k: string, ks: Kind[], rest: HTerm[]): string[] {
  const olds = live.flatMap(([, b]) => b.val.ws);
  const news = olds.map((w) => name_local(fl, w.replace(/_\d+$/, "")));
  const ts = ks.map(() => name_local(fl, k));
  const seg = seg_new(name, ret, [...news, ...ts],
    [...live.flatMap(([, b]) => b.val.lay.ks), ...ks], frame);
  fl.segs.push(seg);
  Object.assign(fl, { seg, spares: [], tab: 2, uses: new Map() });
  olds.forEach((w, i) =>
    fl.brwl.has(w) && fl.brwl.set(news[i], fl.brwl.get(w)!));
  let i = 0;
  live.forEach(([p, b]) => bind_uses(fl, p,
    val_new(news.slice(i, i += b.val.ws.length), b.val.lay), rest, b.A));
  return ts;
}

// Node
// ====

function node_fill(fl: File, k: string, alloc: string,
  exprs: string[], shr = false): string {
  const nd = name_local(fl, k);
  file_push(fl, `u64 ${nd} = ${alloc};`);
  exprs.forEach((w, j) => {
    file_push(fl, `e.mem[${nd} + ${j}] = ${shr ? `rfc_seal(e, ${w})` : w};`);
  });
  return nd;
}

function node_build(fl: File, k: Bend.Name, at: (j: number) => Val): string {
  const fs = lay_node(fl.book, k).arms![0].fs;
  return ctr_build(fl, k, fs.flatMap((f, j) =>
    val_own(fl, val_to(fl, at(j), f.lay))));
}

function node_fields(fl: File, t: string, node: Lay,
  tail = false): Val[] {
  const n = node.ks.length;
  const fs = node.arms![0].fs;
  if (n === 0 || (n === 1 && node.ks[0] === "w32")) {
    return fs.map((f) => val_new(f.lay.ks.map(() => `term_loc(${t})`), f.lay));
  }
  let ws: string[];
  if (fl.brwl.has(t)) {
    const bl = emit_hold(fl, [`term_peek(e, ${t})`], "bl")[0];
    ws = emit_hold(fl, node.ks.map((_, j) => `e.mem[${bl} + ${j}]`), "f",
      node.ks);
    ws.forEach((w, j) => {
      if (node.ks[j] === "box") {
        fl.brwl.set(w, fl.brwl.get(t)!);
      }
    });
  } else {
    const z = fl.hot.has(node.arms![0].k);
    const sp = name_local(fl, "sp");
    let fb = `e.mem[${sp} + `;
    if (z) {
      fb = name_local(fl, "fb") + "[";
      file_push(fl, `Term ${fb}${n}];`);
      file_push(fl, `u64 ${sp} = ctr_take(e, ${t}, ${n}, ${fb.slice(0, -1)});`);
    } else {
      file_push(fl, `u64 ${sp} = term_loc(${t});`);
    }
    ws = emit_hold(fl, node.ks.map((_, j) => `${fb}${j}]`), "f", node.ks);
    if (tail) {
      fl.spares.push({ words: n, name: sp, z });
    } else {
      spare_free(fl, n, sp, z);
    }
  }
  return fs.map((f) => val_field(val_new(ws, node), f));
}

// Facts
// =====
// The emitter is the analysis. A def's boxed parameters start borrowed
// (brw); a borrowed word (brwl, with the parameter it descends from) used
// as owned flips that parameter; a call site asks its callee to lend a
// parameter when the argument is used later (lend), and a pass ends by
// turning owned every parameter no site asked to lend, so a request wins
// and a dying site keeps its value bound and drops it after the call; an
// owned use of a value used later shares it and heats its type (hot); a
// tail jump between disagreeing returns boxes both defs (dyn); a shared
// value of an erased parameter's type marks the parameter (poly).
// compile_book emits the book until a pass changes nothing.

function facts_hot(cb: Carb, B: HTerm | null, force: boolean): void {
  const w = ty_wnf(cb.book, B);
  if (w?.$ === "Lam") {
    facts_hot(cb, w.f(DUMMY), force);
    return;
  }
  if (w?.$ !== "ADT") {
    if (force && w?.$ === "Var" && cb.own.has(w.k)) {
      cb.poly.add(cb.own.get(w.k)!);
    } else if (force && "All Var App Mat".includes(w?.$!)) {
      cb.hot.add("*");
    }
    return;
  }
  const tk = "t:" + w.k;
  const hot = force || cb.hot.has(tk);
  w.x.forEach((x) => facts_hot(cb, x, hot));
  if (!hot || cb.hot.has(tk)) {
    return;
  }
  cb.hot.add(tk);
  const tld = cb.book.tlds[w.k];
  if (tld?.$ === "ADT") {
    for (const c of tld.c) {
      cb.hot.add(c.k);
      ctr_doms(cb.book, c, w.x).forEach((A) => facts_hot(cb, A, true));
    }
  }
}

// A borrowed parameter turned owned voids the def under emission: its
// counts and words assumed the borrow, so compile_def starts it over.
function facts_flip(fl: File, [k, i]: Root): void {
  const bs = fl.brw.get(k);
  if (bs?.[i]) {
    bs[i] = false;
    throw FLIP;
  }
}

// A value with no heap: a constructor packed into its word.
function facts_packed(cb: Carb, t: HTerm): boolean {
  const s = Bend.term_strip(t);
  return s.$ === "Ctr"
    && ["", "w32"].includes(lay_node(cb.book, s.k).ks.join());
}

// Val
// ===

function val_new(ws: string[], lay: Lay): Val {
  return { ws, lay };
}

function val_field(v: Val, f: Field): Val {
  return val_new(v.ws.slice(f.at, f.at + f.lay.ks.length), f.lay);
}

function val_word(v: Val): string {
  if (v.ws.length !== 1) {
    die(`a ${v.ws.length}-word value where one word was expected`);
  }
  return v.ws[0];
}

function val_hold(fl: File, v: Val, k: string): Val {
  return val_new(v.ws.map((w, j) => emit_alias(fl, w, k, v.lay.ks[j])),
    v.lay);
}

function val_drop(fl: File, v: Val, j: number): void {
  if (v.lay.ks[j] === "box" && !fl.brwl.has(v.ws[j])) {
    file_push(fl, `term_sink(e, ${v.ws[j]});`);
  }
}

function val_own(fl: File, v: Val): string[] {
  v.ws.forEach((w) => fl.brwl.has(w) && facts_flip(fl, fl.brwl.get(w)!));
  return v.ws;
}

function val_sink(fl: File, v: Val): void {
  v.ws.forEach((_, j) => val_drop(fl, v, j));
}

function val_to(fl: File, v: Val, lay: Lay): Val {
  if (lay_eq(v.lay, lay)) {
    return v;
  }
  if (lay_box(lay)) {
    return val_new([val_box(fl, v)], BOX);
  }
  if (lay_box(v.lay)) {
    return val_unbox(fl, v, lay);
  }
  if (lay.arms === null || v.lay.arms === null) {
    die("a layout mismatch");
  }
  return val_arms(fl, lay, v.ws[0], (t, i) => `${t} == ${i}`, (arm) => {
    const from = lay_arm(v.lay, arm.k);
    return arm.fs.map((f, j) => val_to(fl, val_field(v, from.fs[j]), f.lay));
  });
}

function val_arms(fl: File, lay: Lay, sel: string,
  cond: (t: string, i: number) => string, read: (arm: Arm) => Val[],
  stuck = false): Val {
  const arms = lay.arms!;
  if (arms.length <= 1) {
    return val_new(arms.flatMap(read).flatMap((g) => g.ws), lay);
  }
  const out = emit_dst(fl, lay, "o").ws;
  const t = emit_alias(fl, sel, "t");
  const bodies = arms.map((arm, i) => () => {
    file_push(fl, `${out[0]} = ${i};`);
    read(arm).forEach((g, j) => g.ws.forEach((w, n) => {
      file_push(fl, `${out[arm.fs[j].at + n]} = ${w};`);
    }));
  });
  emit_chain(fl, (i) => cond(t, i),
    stuck ? [...bodies, () => emit_stuck(fl)] : bodies);
  return val_new(out, lay);
}

function val_box(fl: File, v: Val): string {
  if (v.lay.arms === null) {
    return val_own(fl, v)[0];
  }
  const arms = v.lay.arms!;
  const build = (arm: Arm): string =>
    node_build(fl, arm.k, (j) => val_field(v, arm.fs[j]));
  if (arms.length <= 1) {
    return arms.map(build)[0] ?? "0";
  }
  const out = emit_hold(fl, ["0"], "b")[0];
  const tag = emit_alias(fl, v.ws[0], "t");
  emit_chain(fl, (i) => `${tag} == ${i}`, arms.map((arm) => () => {
    file_push(fl, `${out} = ${build(arm)};`);
  }));
  return out;
}

function val_unbox(fl: File, v: Val, lay: Lay): Val {
  if (lay.arms === null) {
    return val_new(v.ws, lay);
  }
  const t = emit_alias(fl, v.ws[0], "u");
  return val_arms(fl, lay, t, (_, i) =>
    `term_aux(${t}) == ${cid_reg(fl, lay.arms![i].k)}`, (arm) => {
    const fs = node_fields(fl, t, lay_node(fl.book, arm.k));
    return arm.fs.map((f, j) => val_to(fl, fs[j], f.lay));
  }, true);
}

// Arr
// ===

function arr_open(book: Bend.Book, adt: HAdt): HAdt {
  if (adt.k === "Array" && ty_adt(book, adt.x[0]) === null) {
    die("an open Array element type");
  }
  return adt;
}

function arr_call(fl: Carb, k: Bend.Name, all: HTerm[]): boolean {
  const it = intr_of(fl, k, true);
  const arr = it?.call === true && it.C === undefined && it.parts === undefined;
  if (arr && ty_adt(fl.book, all[0]) === null) {
    die("an open Array element type");
  }
  return arr;
}

function arr_lay(el: Lay): Lay {
  return lay_pack([{ k: "Tuple",
    fs: [{ at: 0, lay: BOX }, { at: 1, lay: el }] }]);
}

function arr_cells(fl: File, a: string, at: string, el: Lay,
  own: boolean): Val {
  const { arr } = lay_arr(el);
  return val_new(emit_hold(fl, el.ks.map((k, j) => k === "box" && !own
    ? `blk_keep(e, term_loc(${a}) + ${at} + ${j})`
    : `blk_read(e.mem, ${Number(arr)}, term_loc(${a}), ${at} + ${j})`), "c",
  el.ks), el);
}

function arr_new(fl: File, d: string, v: Val, el: Lay): string {
  const { arr, lgs } = lay_arr(el);
  const ws = val_own(fl, val_to(fl, v, el));
  const fv = name_local(fl, "fv");
  file_push(fl, `Term ${fv}[${Math.max(1, ws.length)}];`);
  ws.forEach((w, j) => file_push(fl, `${fv}[${j}] = ${w};`));
  return `blk_new(e, ${Number(arr)}, ${d}, ${lgs}, ${ws.length}, ${fv})`;
}

function arr_op(fl: File, k: string, el: Lay, args: Val[]): Val {
  const { arr, lgs } = lay_arr(el);
  switch (k) {
    case "array_new": {
      return val_new([arr_new(fl, val_word(args[0]), args[1], el)], BOX);
    }
    case "array_size": {
      const a = emit_alias(fl, val_own(fl, args[0])[0], "a");
      return val_new([a, `(1ull << (blk_cls(e, ${a}) - ${lgs}))`],
        arr_lay(W32));
    }
    default: {
      const a = emit_alias(fl, val_own(fl, args[0])[0], "a");
      const at = emit_hold(fl,
        [`blk_at(e, ${a}, ${val_word(args[1])}, ${lgs})`], "at")[0];
      if (k === "array_get") {
        return val_new([a, ...arr_cells(fl, a, at, el, false).ws],
          arr_lay(el));
      }
      const old = arr_cells(fl, a, at, el, true);
      val_own(fl, val_to(fl, args[2], el)).forEach((w, j) => {
        file_push(fl, `blk_write(e.mem, ${Number(arr)}, term_loc(${a}), `
          + `${at} + ${j}, ${w});`);
      });
      if (k === "array_swap") {
        return val_new([a, ...old.ws], arr_lay(el));
      }
      val_sink(fl, old);
      return val_new([a], BOX);
    }
  }
}

function arr_leaf(fl: File, s: string, el: Lay): Val {
  const got = arr_cells(fl, s, "0", el, true);
  file_push(fl, `blk_free(e, ${s});`);
  return got;
}

// Bind
// ====

// An owned use: the last takes the value, an earlier one shares it.
function bind_pop(fl: File, x: HTerm): Val {
  const p = probe_of(x);
  const b = fl.uses.get(p) ?? die("an unbound binder: " + p.k);
  if (b.n <= 1) {
    fl.uses.delete(p);
    return b.val;
  }
  fl.uses.set(p, { ...b, n: b.n - 1 });
  return val_new(b.val.ws.map((w, j) => {
    if (b.val.lay.ks[j] === "box" && !fl.brwl.has(w)) {
      file_push(fl, `${w} = term_keep(e, ${w});`);
      facts_hot(fl, b.A, true);
    }
    return w;
  }), b.val.lay);
}

function bind_uses(fl: File, p: Probe, v: Val, rest: HTerm[],
  A: HTerm | null = null): void {
  const n = rest_use(fl, rest, p);
  if (A !== null) {
    const lay = lay_of(fl.book, A);
    // A shared box of a flat type (a closure's or a dyn def's result)
    // unboxes before its first share: its words copy, its node does not.
    if (n > 1 && lay_box(v.lay) && !lay_box(lay)
      && !v.ws.some((w) => fl.brwl.has(w))) {
      v = val_unbox(fl, v, lay);
    }
    facts_hot(fl, A, fl.hot.has("*"));
  }
  if (n > 0) {
    fl.uses.set(p, { val: v, n, A });
  } else if (!v.ws.some((w) => fl.brwl.has(w))) {
    val_sink(fl, v);
  }
}

// A binding with no use in `rest` dies here: a borrow is let go, an
// owned value sunk.
function bind_dead(fl: File, rest: HTerm[]): void {
  for (const [p, b] of [...fl.uses]) {
    const n = rest_use(fl, rest, p);
    if (n === 0) {
      fl.uses.delete(p);
      if (!b.val.ws.some((w) => fl.brwl.has(w))) {
        val_sink(fl, b.val);
      }
    } else if (n < b.n) {
      fl.uses.set(p, { ...b, n });
    }
  }
}

// Emit
// ====

function emit_hold(fl: File, exprs: string[], k: string,
  ks?: Kind[]): string[] {
  return exprs.map((ex, i) => {
    const al = name_local(fl, k);
    const ty = fl.decl !== "Term" ? fl.decl : lay_c(ks?.[i] ?? "w64");
    file_push(fl, `${ty} ${al} = ${ex};`);
    return al;
  });
}

function emit_alias(fl: File, e: string, k: string, kd?: Kind): string {
  return fl.local.has(e) ? e : emit_hold(fl, [e], k, kd && [kd])[0];
}

function emit_task(fl: File, fid: string, rem: number, words: string[],
  cont = "WL_CONT", idx: string | number = "WL_IDX"): string {
  return node_fill(fl, "t",
    `task_node(e, ${seg_ref(fl, fid)}, ${cont}, ${idx}, ${rem})`, words);
}

function emit_frame(fl: File, words: string[], next: string): void {
  const ws = [...words, seg_ref(fl, next)];
  file_push(fl, `WL_ROOM(${ws.length});`);
  ws.forEach((w, i) => file_push(fl, `STK(${i}) = ${w};`));
  file_push(fl, `WL_PUSHN(${ws.length});`);
}

function emit_res(fl: File, ws: string[]): void {
  fl.resw = Math.max(fl.resw, ws.length);
  ws.forEach((w, j) => file_push(fl, `r${j} = ${w};`));
}

// A self-jump reads its parameters back: the device's loop carries them
// typed, not as words (raytrace GPU 1.72x otherwise).
function emit_jump(fl: File, args: string[], k: Bend.Name): void {
  args.forEach((a, i) => file_push(fl, `r${i} = ${a};`));
  if (fl.seg.def !== k) {
    return file_push(fl, `WL_JMP(${seg_ref(fl, seg_fid(k))});`);
  }
  fl.seg.spin = true;
  fl.seg.params.forEach((p, i) => file_push(fl, `${p} = r${i};`));
  file_push(fl, `WL_AGAIN(${fl.seg.fid});`);
}

// A call's arguments: a nested one is evaluated first, the Var ones among
// its later uses; a Var lent to the callee is read in place and asks it to
// lend when the value is used later (by the rest, another argument, or
// its owner: a borrow of this def, unless the callee is the def itself,
// whose own request would keep it), else to own. A call nothing follows
// (a jump, an inlined tail) gives a dying value, as does a temporary with
// a heap (nobody would drop it after the call); a fork's reads are at
// once, so none precedes an owned use.
function emit_vals(fl: File, ck: Call, own = false, fork = false): Val[] {
  const lent = fl.brw.get(ck.k) ?? [];
  ck.all.forEach((a, q) =>
    fl.poly.has(ck.k + "~" + q) && facts_hot(fl, a, true));
  const xs = ck.args.map((a) => Bend.term_strip(a));
  const vars = xs.filter((x) => x.$ === "Var");
  const rest = fl.rest;
  const read = (x: HTerm, i: number): Val => {
    if (lent[i] !== true) {
      return bind_pop(fl, x);
    }
    const p = probe_of(x);
    const b = fl.uses.get(p) ?? die("an unbound binder: " + p.k);
    const r = b.val.ws.map((w) => fl.brwl.get(w)).find((z) => z !== undefined)
      ?? null;
    const held = !own && (vars.filter((y) => probe_of(y) === p).length > 1
      || rest_use(fl, rest, p) > 0);
    if (held || (r !== null && r[0] !== ck.k)) {
      fl.lend.add(ck.k + "~" + i);
    } else if (own && r === null) {
      facts_flip(fl, [ck.k, i]);
    }
    if (!fork) {
      fl.uses.set(p, { ...b, n: Math.max(b.n - 1, 1) });
    }
    return b.val;
  };
  const vs = ck.args.map((a, i): Val | null => {
    if (xs[i].$ === "Var") {
      return null;
    }
    fl.rest = [...xs.slice(i + 1).filter((x) => x.$ !== "Var"), ...vars,
      ...rest];
    if (lent[i] === true && !facts_packed(fl, xs[i])) {
      facts_flip(fl, [ck.k, i]);
    }
    return emit_expr(fl, a, null);
  });
  fl.rest = rest;
  return xs.map((x, i) => vs[i] ?? read(x, i));
}

// Expressions in order, each seeing the later ones as its rest.
function emit_each(fl: File, xs: HTerm[]): Val[] {
  const rest = fl.rest;
  const vs = xs.map((x, i) => {
    fl.rest = [...xs.slice(i + 1), ...rest];
    return emit_expr(fl, x, null);
  });
  fl.rest = rest;
  return vs;
}

function emit_args(fl: File, k: Bend.Name, vs: Val[]): string[] {
  const lent = fl.brw.get(k) ?? [];
  const lays = def_lays(fl, k);
  return vs.flatMap((v, i) => {
    const w = val_to(fl, v, lays[i]);
    return lent[i] === true ? w.ws : val_own(fl, w);
  });
}

// The bindings a continuation holds: every one still bound (a dying
// borrow among them, sunk at its entry), but a borrow of this def's
// caller with no use in `rest`.
function seg_live(fl: File, rest: HTerm[]): [Probe, Bind][] {
  return [...fl.uses].filter(([p, b]) =>
    !b.val.ws.some((w) => fl.brwl.has(w)) || rest_use(fl, rest, p) > 0);
}

// A cut: the call, the live bindings as its continuation's frame or task.
function emit_cut(fl: File, ck: Call, p: Probe, rest: HTerm,
  A: HTerm | null): void {
  fl.rest = [rest];
  const cargs = emit_args(fl, ck.k, emit_vals(fl, ck));
  const live = seg_live(fl, [rest]);
  const ws = live.flatMap(([, b]) => b.val.ws);
  const name = seg_name(fl, "k");
  const kf = seg_fid(name);
  spare_flush(fl);
  emit_chain(fl, () => "seq", [() => emit_frame(fl, ws, kf), () => {
    file_push(fl, `WL_CONT = term_tsk(${kf}, ${emit_task(fl, kf, 1, ws)});`);
    file_push(fl, `WL_IDX = ${ws.length};`);
    if (ck.bang) {
      file_push(fl, `return term_tsk(${seg_fid(ck.k)}, ${
        emit_task(fl, seg_fid(ck.k), 0, cargs)});`);
    }
  }]);
  emit_jump(fl, cargs, ck.k);
  const ret = def_ret(fl, ck.k);
  const rs = seg_open(fl, name, fl.seg.ret, { pop: ws.length,
    at: ws.map((_, i) => i) }, live, p.k, ret.ks, [rest]);
  bind_uses(fl, p, val_new(rs, ret), [rest], A);
}

function emit_put(fl: File, dst: Dst, v: Val): void {
  if (dst === null) {
    spare_flush(fl);
    const ws = val_own(fl, val_to(fl, v, fl.seg.ret));
    emit_res(fl, ws);
    file_push(fl, `WL_RETN(${ws.length});`);
  } else {
    val_own(fl, val_to(fl, v, dst.lay)).forEach((w, j) => {
      file_push(fl, `${dst.ws[j]} = ${w};`);
    });
  }
}

function emit_fuse(fl: File, ck: Call, dst: Dst, tail = false): void {
  const tld = fl.book.tlds[ck.k] as Def;
  const doms = def_get_params(fl.book, tld);
  const ers = ck.all.filter((_, i) =>
    i < doms.length && !quant_live(doms[i][0]));
  const flat = flat_of(fl, ck.k);
  const ws = emit_args(fl, ck.k, emit_vals(fl, ck, tail && !flat));
  if (!flat) {
    const vs = def_lays(fl, ck.k).map((lay) =>
      val_new(ws.splice(0, lay.ks.length), lay));
    const outer = { def: fl.def, pi: fl.pi };
    Object.assign(fl, { def: ck.k, pi: 0 });
    emit_body(fl, tld.h as HTerm, tld.T, ers, vs, dst);
    Object.assign(fl, outer);
    return;
  }
  const out = emit_dst(fl, def_ret(fl, ck.k));
  const name = emit_native(fl, ck, ers);
  const o = name_local(fl, "o");
  file_push(fl, `Term ${o}[${out.ws.length}];`);
  block(fl, `if (${name}(${["e", o, ...ws].join(", ")}) == 0) {`, () => {
    file_push(fl, "return 0;");
  });
  out.ws.forEach((v, j) => file_push(fl, `${v} = ${o}[${j}];`));
  if (tail) {
    bind_dead(fl, []);
  }
  emit_put(fl, dst, out);
}

function emit_params(fl: File, k: Bend.Name): Val[] {
  const lays = def_lays(fl, k);
  const names = live_doms(fl.book, fl.book.tlds[k] as Bend.Def)
    .map(([, n]) => n);
  const vals = lays.map((l, i) =>
    val_new(l.ks.map(() => name_local(fl, names[i])), l));
  const brw = fl.brw.get(k)!;
  vals.forEach((v, i) => v.ws.forEach((w, j) => {
    if (brw[i] && lays[i].ks[j] === "box") {
      fl.brwl.set(w, [k, i]);
    }
  }));
  fl.fuel = 64;
  fl.def = k;
  fl.pi = 0;
  return vals;
}

function emit_native(fl: File, ck: Call, ers: HTerm[]): string {
  const key = [ck.k, ...ers.map((e) => JSON.stringify(lay_of(fl.book, e)))]
    .join("|");
  const got = fl.spun.get(key);
  if (got !== undefined) {
    return seg_ref(fl, got);
  }
  const name = seg_ref(fl, `spin_${fl.spun.size}`);
  fl.spun.set(key, name);
  const tld = fl.book.tlds[ck.k] as Def;
  const ret = def_ret(fl, ck.k);
  const outer = { ...fl };
  Object.assign(fl, { spares: [], tab: 2, uses: new Map() });
  const vals = emit_params(fl, ck.k);
  const seg = seg_new(ck.k, ret, vals.flatMap((v) => v.ws),
    vals.flatMap((v) => v.lay.ks));
  seg.fid = name;
  fl.seg = seg;
  const dst = { ws: ret.ks.map(() => name_local(fl, "v")), lay: ret };
  emit_body(fl, tld.h as HTerm, tld.T, ers, vals, dst);
  fl.spins.push([name, [`${seg.lines.length < SPIN_FAR ? "INLINE" : "FAR"} Term ${name}(Env e, THR Term* o${
    seg.ks.map((k, i) => `, ${lay_c(k)} r${i}`).join("")}) {`,
  "  u32 wpoll = 0;",
  ...dst.ws.map((v, j) => `  ${lay_c(ret.ks[j])} ${v} = 0;`),
  ...seg.params.map((p, i) => `  ${lay_c(seg.ks[i])} ${p} = r${i};`),
  `  WL_SPIN(${name})`, ...seg.lines, "  break;", "  }",
  ...dst.ws.map((v, j) => `  o[${j}] = ${v};`),
  "  return 1;", "}"].join("\n"), seg.refs]);
  Object.assign(fl, outer);
  return name;
}

function emit_dst(fl: File, lay: Lay, k = "v"): Val {
  return { ws: emit_hold(fl, lay.ks.map(() => "0"), k, lay.ks), lay };
}

function emit_intr(fl: File, it: Intr, x: HTerm,
  ty: HTerm | null): Val {
  const m = term_spine(fl, x);
  const k = (m.t as Of<"Ref">).k;
  const args = emit_each(fl, m.args);
  if (arr_call(fl, k, m.all)) {
    const op = eff_name(k);
    const el = lay_of(fl.book, m.all[0]);
    if ("array_get array_new array_clone".includes(op) && el.ks.includes("box")
      && !(op === "array_new" && facts_packed(fl, m.all[2]))) {
      facts_hot(fl, m.all[0], true);
    }
    return arr_op(fl, op, el, args);
  }
  const ws = args.map((v) => val_word(val_new(val_own(fl, v), v.lay)));
  if (it.parts !== undefined) {
    const as = ws.map((z) => emit_alias(fl, z, "a"));
    const vs: string[] = [];
    for (const p of it.parts) {
      vs.push(emit_alias(fl, tpl(p, [...as, ...vs]), "a"));
    }
    return val_new(vs, lay_of(fl.book, ty ?? tele_unbind(fl.book,
      (fl.book.tlds[k] as Bend.Def).T).ret));
  }
  const dup = typeof it.C === "string" && /\$(\d)[^]*\$\1/.test(it.C);
  const out = tpl(it.C!, dup ? ws.map((a) => emit_alias(fl, a, "a")) : ws);
  const lay = lay_of(fl.book, ty);
  return val_new([out], lay.ks.length === 1 ? lay : BOX);
}

// A closure: its captures move into a node (a capture is one use of the
// binding, whatever the closure does with it); its segment takes them,
// then x.
function emit_clo(fl: File, x: HTerm, ty: HTerm | null): Val {
  const u = term_uses(fl, x);
  const live = [...fl.uses].filter(([p]) => term_use(u, p) > 0)
    .map(([p, b]): [Probe, Bind] => {
      fl.uses.set(p, { ...b, n: b.n - term_use(u, p) + 1 });
      return [p, { ...b, val: bind_pop(fl, p) }];
    });
  const words = live.flatMap(([, b]) => val_own(fl, b.val));
  const name = seg_name(fl, "c");
  const clo = seg_clo(fl, seg_fid(name), words);
  const outer = { seg: fl.seg, uses: fl.uses, spares: fl.spares,
    tab: fl.tab, rest: fl.rest };
  const [arg] = seg_open(fl, name, CLO_RET, null, live, "x", ["w64"], [x]);
  emit_body(fl, x, ty, [], [val_new([arg], BOX)], null);
  Object.assign(fl, outer);
  return val_new([clo], BOX);
}

function emit_ctr(fl: File, x: Of<"Ctr">, ty: HTerm | null): Val {
  const [adt, u] = ctr_adt(fl, x, ty);
  if (u !== null) {
    return val_new([`${u}ull`], W32);
  }
  const flds = ctr_flds(fl.book, x.k, x.x);
  const lay = lay_of(fl.book, adt);
  const native = OPTIMIZED[adt.k]?.C;
  if (native !== undefined) {
    const fn = native.intr[x.k] ?? die("no native intro: " + x.k);
    const vs = emit_each(fl, flds);
    return val_new([vs.length === 1 && vs[0].ws.length > 1
      ? `(${vs[0].ws.map((w, i) => `((u64)${w} << ${i})`).join(" | ")})`
      : tpl(fn, vs.map(val_word))], lay);
  }
  if (adt.k === "Array") {
    const el = lay_of(fl.book, adt.x[0]);
    const vs = emit_each(fl, flds);
    return val_new([x.k === "ALeaf" ? arr_new(fl, "0", vs[0], el)
      : `blk_node(e, ${val_own(fl, vs[0])[0]}, ${val_own(fl, vs[1])[0]})`],
    BOX);
  }
  const vs = emit_each(fl, flds);
  if (lay_box(lay)) {
    return val_new([node_build(fl, x.k, (j) => vs[j])], BOX);
  }
  const arm = lay_arm(lay, x.k);
  const ws = lay.ks.map((_, j) => j === 0 && lay.arms!.length > 1
    ? String(lay.arms!.indexOf(arm)) : "0");
  vs.forEach((v, j) => {
    val_to(fl, v, arm.fs[j].lay).ws.forEach((w, n) => {
      ws[arm.fs[j].at + n] = w;
    });
  });
  return val_new(ws, lay);
}

function emit_fold(fl: File, t: HTerm): HTerm | null {
  const s = Bend.term_strip(t);
  const r = memo(FOLDS, s, () => {
    if (term_const(s)) {
      return s;
    }
    const m = term_spine(fl, s);
    const it = m.t.$ === "Ref" ? intr_of(fl, m.t.k) : undefined;
    if (it === undefined) {
      const b = emit_unfold(fl, s);
      fl.fuel -= Number(b !== null);
      return b === null || term_any(fl, b, (y) => {
        if (y.$ === "App" || y.$ === "Ref") {
          emit_fold(fl, y);
        }
        return fl.fuel < 0;
      }) ? null : b;
    }
    const as = m.all.map((a) =>
      m.args.includes(a) ? emit_fold(fl, a) ?? a : a);
    return it.call === true ? null : as.every((a, i) => a === m.all[i]) ? s
      : as.reduce((f, x) => Bend.App(f, x), m.t as HTerm);
  });
  return r === s ? t : r;
}

function emit_unfold(fl: File, s: HTerm): HTerm | null {
  const m = term_spine(fl, s);
  const d = m.t.$ === "Ref" ? fl.book.tlds[m.t.k] : undefined;
  if (m.t.$ !== "Ref" || d?.$ !== "Def" || d.h === undefined
    || m.all.length !== d.n
    || intr_of(fl, m.t.k) !== undefined || !flat_of(fl, m.t.k)) {
    return null;
  }
  const fs = m.all.map((a) => m.args.includes(a) ? emit_fold(fl, a) ?? a : a);
  const walk = (ys: HTerm[]): HTerm | null => {
    let b = d.h as HTerm;
    let xs = ys;
    let hit = m.args.every((a) => term_const(fs[m.all.indexOf(a)]));
    for (let w = Bend.term_strip(b); xs.length > 0; w = Bend.term_strip(b)) {
      if (w.$ === "Lam") {
        b = w.f(xs[0]);
        xs = xs.slice(1);
        continue;
      }
      const c = w.$ === "Mat" ? Bend.term_strip(xs[0]) : null;
      if (c === null || c.$ !== "Ctr" || !term_const(c)) {
        return null;
      }
      const { arms, end } = mat_arms(w);
      const arm = arms.find(([k]) => k === c.k);
      if (arm === undefined && Bend.term_strip(end).$ === "Efq") {
        return null;
      }
      b = arm === undefined ? end : arm[1];
      xs = arm === undefined ? xs
        : [...ctr_flds(fl.book, c.k, c.x), ...xs.slice(1)];
      hit = true;
    }
    return !hit || term_any(fl, b, (y) => y.$ === "Lam" || mat_head(y))
      ? null : b;
  };
  const lent = fl.brw.get(m.t.k) ?? [];
  const doms = def_get_params(fl.book, d);
  const bind = (i: number, ys: HTerm[]): HTerm => {
    const a = fs[i];
    if (i === fs.length) {
      return walk(ys) as HTerm;
    }
    const li = m.args.indexOf(m.all[i]);
    if (li < 0 || term_const(a)
      || (lent[li] === true && Bend.term_strip(a).$ === "Var")) {
      return bind(i + 1, [...ys, a]);
    }
    return Bend.Let(["a"], [0], [Bend.Ann(a, doms[i][2])], (xs: HTerm[]) =>
      bind(i + 1, [...ys, xs[0]]), undefined, [Bend.Many()]);
  };
  return walk(fs) === null ? null : bind(0, []);
}

function emit_expr(fl: File, tm: HTerm, ty0: HTerm | null): Val {
  const [x, ty] = ty_peel(tm, ty0);
  switch (x.$) {
    case "Var": return bind_pop(fl, x);
    case "Ref":
    case "App": {
      const got = emit_fold(fl, x);
      if (got !== null && got !== x) {
        return emit_expr(fl, got, ty);
      }
      const m = term_spine(fl, x);
      const ck = call_kind(fl, x);
      if (ck !== null && flat_call(fl, x)) {
        const dst = emit_dst(fl, def_ret(fl, ck.k));
        emit_fuse(fl, ck, dst);
        return dst;
      }
      const eta = call_eta(fl, x);
      if (eta !== null) {
        return emit_expr(fl, eta, ty);
      }
      const g = m.t as Of<"Ref">;
      if (g.$ !== "Ref" && m.args.length === 0) {
        return emit_expr(fl, m.h, ty);
      }
      const tld = fl.book.tlds[g.k];
      const intr = intr_of(fl, g.k);
      if (intr !== undefined) {
        return emit_intr(fl, intr, x, ty);
      }
      if (tld?.$ === "ADT") {
        const lay = lay_of(fl.book, ty);
        return val_new(lay.ks.map(() => "0ull"), lay);
      }
      if (tld?.$ !== "Def" || (tld.v === null && tld.i === undefined)) {
        die(`a live call into the law ${g.k}`);
      }
      const lays = def_lays(fl, g.k);
      fl.brw.get(g.k)?.forEach((_, j) => facts_flip(fl, [g.k, j]));
      return val_new([seg_clo(fl, seg_fid(g.k), emit_each(fl, m.args)
        .flatMap((v, i) => val_own(fl, val_to(fl, v, lays[i]))))], BOX);
    }
    case "Ctr": return emit_ctr(fl, x, ty);
    case "Let": {
      const o = term_open(x);
      if (let_live(fl, x)[0]) {
        const rest = fl.rest;
        fl.rest = [o.b, ...rest];
        const v = val_hold(fl, emit_expr(fl, x.v[0], null), x.k[0]);
        fl.rest = rest;
        bind_uses(fl, o.ps[0], v, [o.b], ty_ann(x.v[0]));
      }
      return emit_expr(fl, o.b, null);
    }
    case "Lam": case "Mat": case "Efq": return fun_live(fl.book, x, ty)
      ? emit_clo(fl, x, ty) : emit_expr(fl, (x as Of<"Lam">).f(DUMMY),
        (ty_all(fl.book, ty) as HAll).B(DUMMY));
    case "Sub": case "Hol":
      die(`a ${x.$} value`);
    default: {
      const lay = lay_of(fl.book, ty);
      return val_new(lay.ks.map(() => "0ull"), lay);
    }
  }
}

function emit_body(fl: File, tm: HTerm, ty0: HTerm | null,
  ers: HTerm[], args: Val[], dst: Dst): void {
  const [x, ty] = ty_peel(tm, ty0);
  if (args.length === 0 && fun_live(fl.book, x, ty)) {
    return emit_put(fl, dst, emit_clo(fl, x, ty));
  }
  const l = x.$ === "Let" || (args.length === 0 && x.$ !== "Lam")
    ? anf(fl, x, ty) : x;
  if (l !== x) {
    return emit_body(fl, l, ty, ers, args, dst);
  }
  switch (x.$) {
    case "Lam": {
      const all = ty_all(fl.book, ty) ?? die("an untyped binder");
      const i = fl.pi++;
      if (!quant_live(all.q)) {
        const t = ers[0] ?? probe(x.k);
        fl.own.set(x.k, fl.def + "~" + i);
        return emit_body(fl, x.f(t), all.B(t), ers.slice(1), args, dst);
      }
      const o = term_open(x);
      const v = val_hold(fl, val_to(fl, args[0], lay_of(fl.book, all.A)), x.k);
      bind_uses(fl, o.ps[0], v, [o.b], all.A);
      return emit_body(fl, o.b, all.B(DUMMY), ers, args.slice(1), dst);
    }
    case "Mat":
    case "Efq": return emit_match(fl, x, ty, ers, args, dst);
    case "Let": {
      if (x.k.length >= 2) {
        return emit_fork(fl, x);
      }
      const o = term_open(x);
      const vc = call_kind(fl, x.v[0]);
      const A = ty_ann(x.v[0]);
      if (vc !== null && !flat_call(fl, x.v[0])) {
        emit_cut(fl, vc, o.ps[0], o.b, A);
        return emit_body(fl, o.b, null, ers, [], null);
      }
      fl.rest = [o.b];
      const v = val_hold(fl, emit_expr(fl, x.v[0], null), x.k[0]);
      bind_uses(fl, o.ps[0], v, [o.b], A);
      bind_dead(fl, [o.b]);
      return emit_body(fl, o.b, null, ers, [], dst);
    }
    default: {
      if (args.length > 0) {
        return emit_body(fl, term_eta(fl.book, x,
          ty ?? die("an untyped arm"), 1), ty, ers, args, dst);
      }
      fl.rest = [];
      const ck = call_kind(fl, x);
      if (ck === null) {
        const v = emit_expr(fl, x, ty);
        bind_dead(fl, []);
        return emit_put(fl, dst, v);
      }
      const once = fl.sites.get(ck.k) === 1 && !fl.dyn.has(ck.k)
        && !ck.bang && !def_foreign(fl.book.tlds[ck.k]);
      if (fl.seg.def !== ck.k && (flat_call(fl, x) || (dst === null && once))) {
        return emit_fuse(fl, ck, dst, true);
      }
      // A jump's returns must agree: the callee and this segment's def box
      // theirs (a closure's segment returns a box owned by no def).
      if (!lay_eq(fl.seg.ret, def_ret(fl, ck.k))) {
        ck.k === CLO_APPLY || def_foreign(fl.book.tlds[ck.k])
          || fl.dyn.add(ck.k);
        fl.seg.ret === CLO_RET || fl.dyn.add(fl.seg.def.split("$")[0]);
      }
      const cargs = emit_args(fl, ck.k, emit_vals(fl, ck, true));
      spare_flush(fl);
      if (ck.bang) {
        block(fl, "if (!seq) {", () => file_push(fl, `return term_tsk(${
          seg_fid(ck.k)}, ${emit_task(fl, seg_fid(ck.k), 0, cargs)});`));
      }
      emit_jump(fl, cargs, ck.k);
    }
  }
}

// A fork: in parallel a join task and a kid per call; in sequence (the
// emitter wound back) one frame read in place by every step, each pushing
// its result, the last jumping into the joiner. What the parallel join
// holds (hold) every step holds too, so both paths open one joiner.
function emit_fork(fl: File, x: HLet): void {
  const o = term_open(x);
  const calls = x.v.map((v) => call_kind(fl, v) as Call);
  const name = seg_name(fl, "j");
  spare_flush(fl);
  fl.seg.fork = true;
  const uses = new Map(fl.uses);
  let hold: Probe[] = [];
  block(fl, "if (!seq) {", () => {
    const margs = calls.map((c, j) => {
      fl.rest = [...x.v.filter((_, i) => i !== j), o.b];
      return emit_args(fl, c.k, emit_vals(fl, c, false, true));
    });
    const live = seg_live(fl, [o.b]);
    hold = live.map(([p]) => p);
    const caps = live.flatMap(([, b]) => b.val.ws);
    spare_flush(fl);
    const jn = emit_task(fl, seg_fid(name), calls.length, caps);
    const jt = `term_tsk(${seg_fid(name)}, ${jn})`;
    let idx = caps.length;
    calls.forEach((c, j) => {
      const fj = seg_fid(c.k);
      file_push(fl, `e.mem[${jn} + ${idx}] = term_tsk(${fj}, ${
        emit_task(fl, fj, 0, margs[j], jt, idx)});`);
      idx += def_ret(fl, c.k).ks.length;
    });
    file_push(fl, `return ${jt};`);
  });
  fl.uses = uses;
  const chain = calls.map(() => o.b);
  for (let j = calls.length - 2; j >= 0; j -= 1) {
    chain[j] = let_open([o.ps[j + 1]], [x.v[j + 1]], chain[j + 1]);
  }
  const rests = chain.map((c) => [...hold, c]);
  const pos = new Map<Probe, number>();
  let depth = 0;
  calls.forEach((c, i) => {
    fl.rest = [chain[i]];
    const cargs = emit_args(fl, c.k, emit_vals(fl, c, false, true));
    const vs = i === 0 ? seg_live(fl, rests[0])
      : [[o.ps[i - 1], fl.uses.get(o.ps[i - 1]) as Bind] as [Probe, Bind]];
    const kn = seg_name(fl, "k");
    spare_flush(fl);
    emit_frame(fl, vs.flatMap(([p, b]) =>
      (pos.set(p, depth), depth += b.val.ws.length, b.val.ws)), seg_fid(kn));
    emit_jump(fl, cargs, c.k);
    const last = i === calls.length - 1;
    const held = [...fl.uses].filter(([p]) => pos.has(p));
    const at = held.flatMap(([p, b]) => b.val.ws.map((_, j) =>
      (pos.get(p) as number) + j - (last ? 0 : depth)));
    const ret = def_ret(fl, c.k);
    const rs = seg_open(fl, kn, fl.seg.ret, { pop: last ? depth : 0, at },
      held, o.ps[i].k, ret.ks, rests[i]);
    bind_uses(fl, o.ps[i], val_new(rs, ret), rests[i], ty_ann(x.v[i]));
  });
  const live = seg_live(fl, [o.b]);
  if (live.map(([p]) => p.i).join() !== [...hold, ...o.ps].map((p) => p.i)
    .join()) {
    die("a fork's paths hold different values");
  }
  emit_jump(fl, live.flatMap(([, b]) => b.val.ws), name);
  seg_open(fl, name, fl.seg.ret, null, live, "", [], [o.b]);
  emit_body(fl, o.b, null, [], [], null);
}

function emit_row(fl: File, t: HTerm, ty: HTerm | null): string | null {
  let s = Bend.term_strip(t);
  while (s.$ === "Lam") {
    s = Bend.term_strip(term_open(s).b);
  }
  s = emit_fold(fl, s) ?? s;
  if (term_const(s)) {
    return js_expr(fl, s, ty);
  }
  const m = term_spine(fl, s);
  const it = m.t.$ === "Ref" ? intr_of(fl, m.t.k) : undefined;
  if (typeof it?.JS !== "string" || TAB_BAD.test(it.JS)) {
    return null;
  }
  const xs = m.args.map((a) => emit_row(fl, a, null));
  return xs.includes(null) ? null : tpl(it.JS, xs as string[]);
}

function emit_tab(fl: File, rows: Chain | null, ty: HTerm): number | null {
  const ret = lay_of(fl.book, ty);
  const ls = rows === null || ret.ks.length !== 1 || ret.ks[0] === "box"
    ? [null] : rows.map(([t]) => emit_row(fl, t, ty));
  if (ls.includes(null)) {
    return null;
  }
  const key = fl.decl === "const" ? ls.join(", ") : Function("return ["
    + ls + "]")().map((v: number) => (ty_adt(fl.book, ty)?.k === "F32"
    ? Bend.f32_to_bits(v) : BigInt(v)) + "ull").join(", ");
  const id = fl.tabs.get(key) ?? fl.tabs.size;
  fl.tabs.set(key, id);
  return id;
}

function emit_nat(x: HTerm): Chain {
  const ls: Chain = [];
  for (let m = x, n = 0; ; n++) {
    const { arms, end } = mat_arms(m);
    const { Zero, Succ } = Object.fromEntries(arms);
    ls.push([Zero ?? end, Zero ? null : n]);
    m = Bend.term_strip(Succ ?? end);
    if (Succ === undefined || m.$ !== "Mat") {
      return [...ls, [Succ ?? end, Succ ? n + 1 : n]];
    }
  }
}

function emit_match(fl: File, x: Of<"Mat"> | Of<"Efq">,
  ty: HTerm | null, ers: HTerm[], args: Val[], dst: Dst): void {
  if (x.$ === "Efq") {
    return emit_stuck(fl);
  }
  const rest = args.slice(1);
  const all = ty_all(fl.book, ty) ?? die("an untyped match");
  const adt = mat_adt(fl.book, all.A);
  const word = adt.k === "U32" || adt.k === "F32";
  const lay = word ? lay_node(fl.book, adt.k) : lay_of(fl.book, all.A);
  const bits = word ? val_hold(fl, val_to(fl, args[0], W32), "u").ws[0] : "";
  const s = val_hold(fl, word ? val_new(lay.ks.map((_, i) =>
    `((${bits} >> ${i}) & 1)`), lay) : val_to(fl, args[0], lay), "s");
  const total = Bend.book_adt(fl.book, adt, Bend.Emp()).c.length;
  const { arms, end } = mat_arms(x);
  const ret = lay_of(fl.book, all.B(DUMMY));
  const sw = s.ws[0];
  const ls = adt.k === "Nat" ? emit_nat(x) : null;
  const id = emit_tab(fl, ls, all.B(DUMMY));
  if (id !== null) {
    bind_dead(fl, []);
    return emit_put(fl, dst, val_new(
      [`TAB_AT(TAB_${id}, ${sw}, ${ls!.length - 1})`], ret));
  }
  const lv: Level[] = ls !== null
    ? ls.map(([h, n], i): Level => [`${sw} == ${i}`, h, () =>
      n === null ? [] : [val_new([`(${sw} - ${n})`], lay)]])
    : arms.map(([k, h]): Level => {
      if (adt.k === "Array") {
        const el = lay_of(fl.book, adt.x[0]);
        return [`blk_cls(e, ${sw}) ${k === "ALeaf" ? "==" : "!="} ${
          lay_arr(el).lgs}`, h, () => k === "ALeaf" ? [arr_leaf(fl, sw, el)]
          : emit_hold(fl, [0, 1].map((hi) => `blk_half(e, ${sw}, ${hi})`),
            "h").map((w) => val_new([w], BOX))];
      }
      if (lay_box(lay)) {
        return [`term_aux(${sw}) == ${cid_reg(fl, k)}`, h,
          () => node_fields(fl, sw, lay_node(fl.book, k), true)];
      }
      return [`${sw} == ${lay.arms!.indexOf(lay_arm(lay, k))}`, h,
        () => lay_arm(lay, k).fs.map((f) => val_field(s, f))];
    });
  if (ls === null && (arms.length < total
    || Bend.term_strip(end).$ !== "Efq")) {
    lv.push(["", end, () => [s]]);
  }
  const spares = fl.spares;
  const arms2 = lv.map(([, h, fs]) => () => {
    fl.spares = spares.slice();
    const outer = { seg: fl.seg, tab: fl.tab, uses: new Map(fl.uses) };
    bind_dead(fl, [h]);
    emit_body(fl, h, null, ers, [...fs(), ...rest], dst);
    if (dst !== null) {
      spare_flush(fl);
    }
    fl.spares = dst === null ? spares : [];
    Object.assign(fl, outer);
  });
  if (arms2.length === 1 || total === 1) {
    return arms2[0]();
  }
  emit_chain(fl, (i) => lv[i][0], arms2);
}

function emit_stuck(fl: File): void {
  file_push(fl, "err_post(e.mem, ERR_TAGS);");
  file_push(fl, "return 0;");
}

function emit_chain(fl: File, cond: (i: number) => string,
  bodies: (() => void)[]): void {
  bodies.forEach((body, i) => {
    if (i === bodies.length - 1) {
      file_push(fl, "} else {");
    } else {
      file_push(fl, `${i === 0 ? "if" : "} else if"} (${cond(i)}) {`);
    }
    fl.tab += 1;
    body();
    fl.tab -= 1;
  });
  file_push(fl, "}");
}

// Compile
// =======

function compile_def(fl: File, k: Bend.Name, tld: Def): void {
  const undo = { ...fl, segs: fl.segs.slice(), spins: fl.spins.slice(),
    spun: new Map(fl.spun) };
  Object.assign(fl, { fresh: new Map(), spares: [], uses: new Map(),
    local: new Set(), brwl: new Map(), rest: [], tab: 2 });
  memo_gc();
  fl.own.clear();
  const vals = emit_params(fl, k);
  fl.seg = seg_new(k, def_ret(fl, k), vals.flatMap((v) => v.ws),
    vals.flatMap((v) => v.lay.ks));
  fl.segs.push(fl.seg);
  try {
    emit_body(fl, tld.h as HTerm, tld.T, [], vals, null);
  } catch (e) {
    if (e !== FLIP) {
      throw e;
    }
    Object.assign(fl, undo);
    compile_def(fl, k, tld);
  }
}

function compile_reqs(fl: File): void {
  const seen = new Set<string>();
  fl.spares = [];
  for (const [k, tld] of done_defs(fl, def_foreign)) {
    fl.reqs += eff_src(tld.i!.find((x) => x.endsWith(".c"))
      ?? die("no .c import: " + k), seen);
    const qp = [...live_doms(fl.book, tld), [0, "k"]].map(([, n]) =>
      name_local(fl, n as string));
    fl.seg = seg_new(k, BOX, qp);
    fl.segs.push(fl.seg);
    fl.cids.set(k, [qp.length, qp.length]);
    file_push(fl, `r0 = ${ctr_build(fl, k, qp)};`);
    file_push(fl, "WL_RETN(1);");
  }
}

function compile_tables(fl: File, entries: Seg[]): string[] {
  const defs: string[] = [];
  for (const ms of [[...fl.cids.keys()].map(cid_mac),
    [...entries.map((s) => s.fid), "FID_EXIT", "FID_ENTER"]]) {
    const dup = ms.find((m, i) => ms.indexOf(m) < i);
    if (ms.length > 65536 || dup !== undefined) {
      die(dup === undefined ? "an id over 65535"
        : "two names mangle to " + dup);
    }
    defs.push(...ms.map((m, i) => `#define ${m} ${i}`));
  }
  const table = (nm: string, vals: number[]) => {
    if (vals.some((v) => v > 255)) {
      die("an arity over 255");
    }
    defs.push(`CONSTV u8 ${nm}[] = { ${vals.join(", ")} };`);
  };
  table("FID_ARITY_T", entries.map((s) => s.params.length));
  // A segment may fork when it, or one it reaches, does.
  const forky = new Set(["FID_CLO_APPLY",
    ...fl.segs.filter((s) => s.fork).map((s) => s.fid)]);
  for (let n = -1; n !== forky.size;) {
    n = forky.size;
    for (const s of fl.segs) {
      if (!forky.has(s.fid) && [...s.refs].some((r) => forky.has(r))) {
        forky.add(s.fid);
      }
    }
  }
  table("FID_FLAG_T", entries.map((s) => Number(fl.bangs.has(s.def))
    | Number(!forky.has(s.fid)) << 1 | Number(s.frame !== null) << 2));
  table("FID_RESW_T", entries.map((s) =>
    s.frame === null ? 0 : s.params.length - s.frame.at.length));
  table("CID_ARITY_T", [...fl.cids.values()].map((c) => c[0]));
  table("CID_BOXN_T", [...fl.cids.values()].map((c) => c[1]));
  // One bank for both lanes, as wide as the widest segment; rp pads the
  // host's twelfth slot so rax stays free for the tail call.
  const n = Math.max(fl.resw, ...entries.filter((s) => s.frame === null)
    .map((s) => s.params.length));
  const rs = [...Array(n).keys()].map((i) => "r" + i);
  const ws = n > 6 ? [...rs.slice(0, 6), "rp", ...rs.slice(6)] : rs;
  const load = rs.map((r, i) =>
    `    case ${i + 1}: ${r} = e.mem[(A) + ${i}]; \\\n`).reverse().join("");
  const last = rs.map((r, i) =>
    `    case ${i}: ${r} = (X); \\\n      break; \\\n`).join("");
  defs.push(`#define IO_HOTS ${"SCon Tuple Done Fail Con Some".split(" ")
    .reduce((m, k, i) => m | (fl.hot.has(k) ? 1 << i : 0), 0)}`, "",
  `#define WL_RESW ${fl.resw}`, `#define BANGS   ${fl.bangs.size}`, "",
  `#define WL_BANK Term ${ws.join(", ")};`, "",
  `#define WL_LOAD(A, N) \\\n  switch (N) { \\\n${load}  }`, "",
  `#define WL_LAST(X) \\\n  switch (war) { \\\n${last}  }`, "",
  `#define WL_SAVE(V) ${rs.slice(0, fl.resw).map((r, j) =>
    `(V)[${j}] = ${r};`).join(" ")}`, "",
  `#define WL_TAKE(V) ${rs.slice(0, fl.resw).map((r, j) =>
    `${r} = (V)[${j}];`).join(" ")}`, "",
  `#define WL_SIG Env e, Stk sp, u32 seq, u32 rn, ${ws.map((w) =>
    "Term " + w).join(", ")}`, "", `#define WL_ALL e, sp, seq, rn, ${ws
    .join(", ")}`, "",
  `#define WL_TABLE ${entries.map((s) =>
    `WL_X(${s.dead ? "FID_EXIT" : s.fid})`).join(" ")} WL_X(FID_EXIT)`);
  return defs;
}

function compile_segs(fl: File): string {
  return fl.segs.filter((s) => !s.dead).map((seg) => {
    const out: string[] = [`  WL_CASE(${seg.fid})`, "  {"];
    const fr = seg.frame ?? { pop: 0, at: [] };
    if (fr.pop > 0) {
      out.push(`    WL_POPN(${fr.pop});`);
    }
    seg.params.forEach((p, i) => {
      out.push(`    ${lay_c(seg.ks[i])} ${p} = ${i < fr.at.length
        ? `STK(${fr.at[i]})` : `r${i - fr.at.length}`};`);
    });
    out.push("    WL_OPEN", ...seg.spin ? [`    WL_SPIN(${seg.fid})`] : [],
      ...seg.lines, ...seg.spin ? ["    WL_SPUN"] : [], "  }}");
    return (seg.host ? ["#if !DEVICE", ...out, "#endif"] : out).join("\n");
  }).join("\n\n");
}

export function compile_book(book: Bend.Book): string {
  const entry = io_entry(book);
  const cb = carb_book(book, [entry]);
  for (const [k, tld] of done_defs(cb)) {
    cb.brw.set(k, live_doms(cb.book, tld).map(([, , A]) => !cb.dyn.has(k)
      && ty_adt(cb.book, A)?.k !== "Array"
      && lay_of(cb.book, A).ks.includes("box")));
  }
  const facts = () => JSON.stringify([[...cb.brw], [...cb.hot], [...cb.dyn],
    [...cb.poly]]);
  const pass = (defs: [Bend.Name, Def][]): File => {
    cb.lend.clear();
    const fl = file_new(cb, "Term");
    for (const k of ("Tuple SNil SCon Chr Unit WCon Emit Halt Fail Done File"
      + " Socket Listener None Some Window Nil Con Key Mouse Move Close Chan"
      + " True False")
      .split(" ")) {
      cid_reg(fl, k);
    }
    for (const [k, tld] of defs) {
      compile_def(fl, k, tld);
    }
    compile_reqs(fl);
    for (const [k, bs] of cb.brw) {
      bs.forEach((b, i) => {
        if (b && !cb.lend.has(k + "~" + i)) {
          bs[i] = false;
        }
      });
    }
    return fl;
  };
  // Emitted callees first until the facts settle (a borrow only turns
  // owned; hot, dyn and poly only grow), then in the book's order: the
  // kept pass took no borrow as owned.
  let was = "";
  for (; was !== facts(); pass(done_defs(cb).reverse())) {
    was = facts();
  }
  const fl = pass(done_defs(cb));
  if (was !== facts()) {
    die("the facts did not settle");
  }
  const reach = (from: string[], set = new Set<string>()): Set<string> => {
    const grab = (fid: string) => set.has(fid) || (set.add(fid)
      && (fl.segs.find((s) => s.fid === fid)?.refs
        ?? fl.spins.find((s) => s[0] === fid)?.[2])?.forEach(grab));
    from.forEach(grab);
    return set;
  };
  const live = reach([seg_fid(entry)]);
  // The device holds what the bangs reach and, when a bang's parameter
  // may hold a closure (a jump through its fid), every closure.
  const wide = [...fl.bangs].some((k) => live_doms(fl.book,
    fl.book.tlds[k] as Bend.Def).some(([, , A]) => ty_clo(fl.book, A)));
  const dev = reach([...[...fl.bangs].map(seg_fid), ...wide ? fl.clos : []]);
  fl.segs = fl.segs.filter((s) =>
    live.has(s.fid) || def_foreign(cb.book.tlds[s.def]));
  for (const s of fl.segs) {
    s.dead = !live.has(s.fid);
    s.host = !dev.has(s.fid);
  }
  fl.spins = fl.spins.filter(([n]) => live.has(n));
  const entries = [...fl.segs, seg_new("io_emit", BOX, [""]),
    seg_new("clo_apply", BOX, ["", ""])];
  const defs = compile_tables(fl, entries);
  defs.push(`#define MAIN_FID ${seg_fid(entry)}`);
  const fills: [string, string[]][] = [
    ["Tables", [defs.join("\n"), ...[...fl.tabs].map(([r, i]) =>
      `CONSTV u64 TAB_${i}[] = { ${r} };`)]],
    ["Spins", fl.spins.map((s) => s[1])],
    ["Segments", [compile_segs(fl)]],
    ["Requests", [fl.reqs]],
  ];
  const out = fills.reduce((src, [mark, parts]) => src.replace(
    new RegExp("^// " + mark + "\\n// " + "=".repeat(mark.length) + "$", "m"),
    (m) => [m, ...parts].join("\n\n")), TEMPLATE);
  if (/\bundefined\b/.test(out)) {
    die("an unbound name in the emitted C");
  }
  return out;
}

// Js
// ==

function js_sat(k: Bend.Name): string {
  return "$" + k.replace(/[./~]/g, "$") + "$";
}

function js_call(fl: File, k: Bend.Name, args: HTerm[],
  tail: boolean): string {
  let exprs = args.map((x) => js_expr(fl, x, null));
  if (k === CLO_APPLY) {
    const [f, x] = exprs;
    return tail ? "run_tail(" + f + ", " + x + ")" : f + "(" + x + ")";
  }
  const tld = fl.book.tlds[k] ?? die("unknown name: " + k);
  if (tld.$ === "ADT") {
    return "null";
  }
  const intr = intr_of(fl, k, true)?.JS ?? null;
  if (intr === null && tld.v === null && tld.i === undefined) {
    die("a live call into the law " + k);
  }
  const live = def_live(fl, tld);
  const v = exprs.length === live - 1 ? name_local(fl, "x") : "";
  if (v !== "") {
    exprs = [...exprs, v];
  } else if (exprs.length !== live) {
    die("an under-applied def value: " + k);
  }
  const pre = v === "" ? "" : "(" + v + ") => ";
  if (intr !== null) {
    const xs = exprs.map((e) => ATOM.test(e) || STRLIT.test(e)
      ? e : emit_hold(fl, [e], "x")[0]);
    return pre + tpl(intr, xs);
  }
  const call = js_sat(k) + "(" + exprs.join(", ") + ")";
  return def_foreign(tld) ? pre + call
    : v !== "" ? "run_clo(" + pre + call + ")"
    : tail ? "run_jump(" + js_sat(k) + ", [" + exprs.join(", ") + "])"
    : "run_loop(" + call + ")";
}

function js_open(fl: File, x: HLet): HTerm {
  const on = let_live(fl, x);
  return x.f(x.v.map((v, j): HTerm => !on[j] ? v
    : Bend.Var(emit_hold(fl, [js_expr(fl, v, null)], x.k[j])[0], 0)));
}

function js_ctr(fl: File, adt: HAdt, k: Bend.Name):
  { keys: Bend.Name[]; el: string[] | undefined } {
  const ctr = fl.book.ctrs[k] ?? die("unknown constructor: " + k);
  const keys = ctr_tail(fl.book, ctr).filter(live_dom).map(([, n]) => n);
  const native = OPTIMIZED[adt.k]?.JS;
  const el = native?.elim?.[k];
  if (native !== undefined && (el ?? []).length !== keys.length) {
    die(k + NATIVE_DIE);
  }
  return { keys, el };
}

function js_expr(fl: File, tm: HTerm,
  ty0: HTerm | null): string {
  const [x, ty] = ty_peel(tm, ty0);
  switch (x.$) {
    case "Var": return x.k;
    case "Ref":
    case "App": {
      const ck = call_kind(fl, x);
      if (ck !== null) {
        return js_call(fl, ck.k, ck.args, false);
      }
      const eta = call_eta(fl, x);
      if (eta !== null) {
        return js_expr(fl, eta, ty);
      }
      const m = term_spine(fl, x);
      if (m.t.$ === "Var" && m.args.length === 0) {
        return m.t.k;
      }
      if (m.t.$ !== "Ref") {
        die("a " + m.t.$ + "-headed spine in an expression");
      }
      arr_call(fl, m.t.k, m.all);
      return js_call(fl, m.t.k, m.args, false);
    }
    case "Ctr": {
      const [adt, u] = ctr_adt(fl, x, ty);
      if (u !== null) {
        const v = adt.k === "F32" ? Bend.f32_from_bits(u) : u;
        return Object.is(v, -0) ? "-0" : String(v);
      }
      const { keys } = js_ctr(fl, adt, x.k);
      const exprs = ctr_flds(fl.book, x.k, x.x)
        .map((f) => js_expr(fl, f, null));
      const native = OPTIMIZED[adt.k]?.JS;
      if (native !== undefined) {
        return tpl(native.intr[x.k] ?? die(x.k + NATIVE_DIE), exprs);
      }
      return exprs.reduce((e, z, j) => e + ", [\"" + keys[j] + "\"]: " + z,
        "{$: \"" + x.k + "\"") + "}";
    }
    case "Let": return js_expr(fl, js_open(fl, x), ty);
    case "Lam": case "Mat": case "Efq": {
      if (!fun_live(fl.book, x, ty)) {
        return js_expr(fl, (x as Of<"Lam">).f(Bend.Var("null", 0)),
          (ty_all(fl.book, ty) as HAll).B(DUMMY));
      }
      const arg = name_local(fl, "x");
      const seg = fl.seg;
      fl.seg = seg_new("", BOX, []);
      fl.tab += 1;
      js_func(fl, x, ty, [arg]);
      fl.tab -= 1;
      const lines = fl.seg.lines;
      fl.seg = seg;
      return `run_clo((${arg}) => {\n${lines.join("\n")}\n${
        "  ".repeat(fl.tab)}})`;
    }
    case "Sub": case "Hol":
      die("cannot compile a " + x.$ + " node");
    default: return "null";
  }
}

function js_func(fl: File, tm: HTerm, ty0: HTerm | null,
  args: string[]): void {
  const [x, ty] = ty_peel(tm, ty0);
  if (args.length === 0 && fun_live(fl.book, x, ty)) {
    return file_push(fl, "return " + js_expr(fl, x, ty) + ";");
  }
  if (x.$ === "Lam") {
    const all = ty_all(fl.book, ty) ?? die("an untyped lambda");
    const v: HTerm = Bend.Var(!quant_live(all.q) ? "null"
      : emit_alias(fl, args[0], x.k), 0);
    return js_func(fl, x.f(v), all.B(v),
      quant_live(all.q) ? args.slice(1) : args);
  }
  if (mat_head(x)) {
    if (x.$ === "Efq") {
      return file_push(fl, `throw "bend: ${ERRS[3]}";`);
    }
    const s = emit_alias(fl, args[0], "$t");
    const rest = args.slice(1);
    const all = ty_all(fl.book, ty) ?? die("an untyped match");
    const adt = mat_adt(fl.book, all.A);
    const { arms, end } = mat_arms(x);
    const total = Bend.book_adt(fl.book, adt, Bend.Emp()).c.length;
    if (adt.k === "IO.OP") {
      block(fl, "if (" + s + ".$ === \"$FFI\") {", () => {
        file_push(fl, "throw " + s + ";");
      });
    }
    const ls = adt.k === "Nat" ? emit_nat(x) : null;
    const id = emit_tab(fl, ls, all.B(DUMMY));
    if (id !== null) {
      return file_push(fl, `return TAB_${id}[Math.min(Number(${s}), ${
        ls!.length - 1})];`);
    }
    if (ls !== null) {
      return emit_chain(fl, (i) => `${s} === ${i}n`, ls.map(([h, n]) => () =>
        js_func(fl, h, null, n === null ? rest : [`(${s} - ${n}n)`, ...rest])));
    }
    const last = arms.length === total ? null : end;
    const native = OPTIMIZED[adt.k]?.JS;
    const bodies = arms.map(([k, h]) => () => {
      const { keys, el } = js_ctr(fl, adt, k);
      const fields = el?.map((e) => tpl(e, [s]))
        ?? keys.map((n) => s + "." + n);
      js_func(fl, h, null, [...fields, ...rest]);
    });
    if (last !== null) {
      bodies.push(() => js_func(fl, last, null, [s, ...rest]));
    }
    if (bodies.length === 1 && total === 1) {
      return bodies[0]();
    }
    return emit_chain(fl, (i) => native === undefined
      ? s + ".$ === \"" + arms[i][0] + "\""
      : tpl(native.cond?.[arms[i][0]] ?? die(arms[i][0] + NATIVE_DIE), [s]),
    bodies);
  }
  if (x.$ === "Let") {
    return js_func(fl, js_open(fl, x), ty, args);
  }
  if (args.length > 0) {
    return js_func(fl, term_eta(fl.book, x, ty ?? die("an untyped arm"), 1),
      ty, args);
  }
  const ck = call_kind(fl, x);
  file_push(fl, "return " + (ck === null ? js_expr(fl, x, ty)
    : js_call(fl, ck.k, ck.args, true)) + ";");
}

function js_def(fl: File, k: Bend.Name, def: Def): void {
  fl.fresh = new Map();
  fl.fuel = 64;
  if (intr_of(fl, k, true) !== undefined) {
    return;
  }
  const params = live_doms(fl.book, def).map(([, n]) => name_local(fl, n));
  const kont = def.i ? [name_local(fl, "k")] : [];
  block(fl, `function ${js_sat(k)}(${[...params, ...kont].join(", ")}) {`,
    () => {
      if (def.i === undefined) {
        js_func(fl, def.h ?? die("unelaborated def " + k), def.T, params);
      } else if (!def.i.some((p) => p.endsWith(".js"))) {
        die("a foreign def without a .js import: " + k);
      } else {
        const n = eff_name(k);
        file_push(fl, `return { $: "$FFI", run: $0eff.${n}, need: $0eff.${n
          }_need, args: [${params.join(", ")}], kont: ${kont[0]} };`);
      }
    });
  file_push(fl, "");
}

export function js_lib(book: Bend.Book, roots: Bend.Name[],
  outs: Bend.Name[] | null): string {
  const cb = carb_book(book, roots.slice());
  const fl = file_new(cb, "const");
  fl.tab = 0;
  for (const [k, def] of done_defs(cb)) {
    memo_gc();
    js_def(fl, k, def);
  }
  const seen = new Set<string>();
  const srcs: string[] = [];
  const rows: string[] = [];
  for (const [k, tld] of done_defs(cb, def_foreign)) {
    js_def(fl, k, tld);
  }
  for (const k of outs === null ? new Set(book.order) : REFS.keys()) {
    const tld = book.tlds[k];
    const path = tld?.$ === "Def" && tld.i?.find((x) => x.endsWith(".js"));
    if (path) {
      srcs.push(eff_src(path, seen));
      const n = eff_name(k);
      for (const m of [n, n + "_need"]) {
        rows.push(`  ${m}: typeof ${m} === "function" ? ${m} : undefined,`);
      }
    }
  }
  const effs = rows.length === 0 ? "" : "const $0eff = (() => {\n"
    + srcs.join("\n") + "\nreturn {\n" + rows.join("\n") + "\n};\n})();\n\n";
  const tabs = [...fl.tabs].map(([r, i]) => `const TAB_${i} = [${r}];`);
  const lib = outs === null ? "" : "export default {\n" + outs.map((k) =>
    `  "${k}": run_lib(${js_sat(k)}, ${
      def_live(cb, cb.book.tlds[k] as Bend.Def)}),`)
    .join("\n") + "\n};\n";
  return RUNTIME + effs + "// Program\n// =======\n\n"
    + [...fl.seg.lines, ...tabs].join("\n") + lib;
}

export function js_book(book: Bend.Book): string {
  const entry = io_entry(book);
  return js_lib(book, [entry], null) + "\n" + RUNTIME_MAIN
    + "\ncli(process.argv.slice(2));\nio_exit(" + js_sat(entry) + ");";
}

// RuntimeC
// ========

const TEMPLATE = String.raw`

// Imports
// =======

#pragma clang fp contract(off)

#ifdef __METAL_VERSION__
#include <metal_stdlib>
using namespace metal;
#elif !defined(__CUDACC_RTC__)
#ifndef __APPLE__
#define _GNU_SOURCE
#endif
#include <stdint.h>
#include <stdbool.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <pthread.h>
#include <stdatomic.h>
#include <unistd.h>
#include <signal.h>
#include <sys/mman.h>
#include <sys/resource.h>
#include <time.h>
#include <poll.h>
#if BEND_METAL
#import <Metal/Metal.h>
#import <Foundation/Foundation.h>
#include <mach-o/dyld.h>
#elif BEND_CUDA
#include <cuda.h>
#include <nvrtc.h>
#include <fcntl.h>
#include <sys/stat.h>
#endif
#endif

// Dialect
// =======

#ifdef __METAL_VERSION__
#define DEV     device
#define DEVL    device
#define GRP     threadgroup
#define GA32    threadgroup atomic_uint
#define THR     thread
#define INLINE  inline
#define OUTLINE static
#define CONSTV  constant
#define DEVICE  1
#define CLZ(x)  clz(x)
#define A32(p)  ((DEV atomic_uint*)(p))
#define RLX     memory_order_relaxed
#define FENCE() atomic_thread_fence(mem_flags::mem_device, memory_order_seq_cst)
#define BAR()   threadgroup_barrier(mem_flags::mem_threadgroup)
#define BARD()  threadgroup_barrier(mem_flags::mem_device \
  | mem_flags::mem_threadgroup)

#define g32_ini(p)    atomic_store_explicit(p, 0, RLX)
#define g32_add(p, v) atomic_fetch_add_explicit(p, v, RLX)
#define g32_get(p)    atomic_load_explicit(p, RLX)
#else
#define DEVL
#define GRP
#define THR
#define INLINE  static inline
#define CONSTV  static const
#ifdef __CUDACC_RTC__
#define DEV     volatile
#define GA32    __shared__ u32
#define OUTLINE static __attribute__((noinline))
#define DEVICE  1
#define CLZ(x)  (u32)__clz((int)(x))
#define FENCE() __threadfence()
#define BAR()   __syncthreads()
#define BARD()  \
  { __threadfence(); __syncthreads(); }

#define g32_ini(p)    (*(p) = 0)
#define g32_add(p, v) atomicAdd(p, v)
#define g32_get(p)    (*(p))
#else
#define DEV
#define OUTLINE static __attribute__((noinline, cold, preserve_most))
#define DEVICE  0
#define CLZ(x)  (u32)__builtin_clz(x)
#define FENCE() __atomic_thread_fence(__ATOMIC_SEQ_CST)
#endif
#endif
#define FAR static __attribute__((noinline))

// A segment: a case of the device's switch; on the host, a preserve_none
// function (WL_SIG) left by a musttail call, its words fresh at WL_OPEN.
#if DEVICE
#define LOCK(l)
#define UNLOCK(l)
#define WL_CASE(F) case F:
#define WL_OPEN    {
#define WL_JMP(F)  { fid = (F); break; }
#define WL_DYN     WL_JMP
#else
#define LOCK(l)    while (__atomic_exchange_n(&(l), 1, __ATOMIC_ACQUIRE)) {}
#define UNLOCK(l)  __atomic_store_n(&(l), 0, __ATOMIC_RELEASE)
#define WL_FN      static __attribute__((preserve_none, noinline)) Reply
#define WL_CASE(F) WL_FN WL_##F(WL_SIG)
#define WL_OPEN    { WL_BANK u32 rn;
#define WL_JMP(F)  __attribute__((musttail)) return WL_##F(WL_ALL)
#define WL_DYN(F)  __attribute__((musttail)) return wl_tab[F](WL_ALL)
#endif
#define WL_SPIN(F)  for (;;) { if (err_spun(e.mem, &wpoll)) { return 0; }
#define WL_SPUN     } break;
#define WL_AGAIN(F) continue
#define WL_POP()    { sp -= LANE_STEP; WL_DYN((Fid)STK(0)); }

#define LANE_STEP (DEVICE ? (int64_t)CUBE : 1)
#define STK(I)    sp[(int64_t)(I) * LANE_STEP]

#define WL_RETN(N)  { rn = (N); WL_POP(); }
#define WL_CONT     STK(-3)
#define WL_IDX      STK(-2)
#define WL_POPN(N)  sp -= N * LANE_STEP
#define WL_PUSHN(N) sp += N * LANE_STEP
#define WL_FRAME(T) \
  Loc wtl = task_tail(T); \
  u64 wtw = e.mem[wtl + 1]; \
  STK(0) = e.mem[wtl]; \
  STK(1) = (wtw >> 32) & 0xFFFF; \
  STK(2) = FID_EXIT; \
  sp += 3 * LANE_STEP;
#define WL_ARGS(A, N) \
  for (u32 wi = 0; wi + 1 < N; wi += 1) { \
    STK(wi) = e.mem[A + wi]; \
  } \
  sp += (N - 1) * LANE_STEP;
#define WL_ROOM(N) \
  if (DEVICE && sp + (N) * CUBE >= e.mem + HEAP_OFF + CUBE) { \
    err_post(e.mem, ERR_DEEP); \
    return 0; \
  }

// Types
// =====

#ifdef __METAL_VERSION__
typedef ulong u64;
typedef uint  u32;
typedef uchar u8;
typedef float f32;
#elif defined(__CUDACC_RTC__)
typedef unsigned long long u64;
typedef long long          int64_t;
typedef unsigned int       u32;
typedef unsigned char      u8;
typedef float              f32;
#else
typedef uint64_t u64;
typedef uint32_t u32;
typedef uint8_t  u8;
typedef float    f32;
#endif

typedef u64 Loc;
#define LOC_MASK ((1ull << 40) - 1)

typedef u32 Cls;
typedef u32 Fid;

typedef u64 Term;
#define TAG_PAK 1ull
#define TAG_CTR 2ull
#define TAG_CLO 3ull
#define TAG_BUF 4ull
#define TAG_TSK 5ull
#define TAG_ARR 6ull

#define TERM_HOLE (~0ull)

#define RFC_BIT  (1ull << 63)
#define RFC_CNT  ((1u << 24) - 1)

typedef Term Reply;

typedef u32 Err;
#define ERR_FAIL 1
#define ERR_RING 2
#define ERR_TAGS 3
#define ERR_HEAP 4
#define ERR_FIDS 5
#define ERR_LEAK 6
#define ERR_NATS 7
#define ERR_RFCS 8
#define ERR_DEEP 9
#define ERR_ARRS 10

typedef u32 Monk;
typedef u32 Ring;

typedef DEV u64* Corpus;

typedef struct {
  Corpus   mem;
  DEV u64* alc;
} Env;

typedef struct {
  u64 off;
  u32 rd;
  u32 wr;
  u32 top;
} Bank;

typedef DEVL Term* Stk;

typedef Term Nat;
#define NAT_IMM ((1ull << 48) - 1)

typedef Term U32;

#if DEVICE
typedef u32 u32a;
#else
typedef u32 __attribute__((may_alias)) u32a;
#endif

#ifdef __METAL_VERSION__
typedef threadgroup atomic_uint* Cursor;
#define CUR_STEP(c) atomic_fetch_add_explicit(c, 1, RLX)
#elif defined(__CUDACC_RTC__)
typedef u32* Cursor;
#define CUR_STEP(c) atomicAdd(c, 1)
#else
typedef u32* Cursor;
#define CUR_STEP(c) ((*(c))++)
#endif

// Constants
// =========

#define LINE      16
#define PAGE_BITS 7
#define PAGE_LEN  (1ull << PAGE_BITS)
#define CUBE_SIDE 128
#define CUBE      ((u64)CUBE_SIDE * CUBE_SIDE)
#define RING_LEN  (1ull << 10)
#define STAK_LEN  (1ull << 11)
#define NCLS      8
#define NCLS_ALL  32
#define IO_HELP   64

#define ALC_WORDS NCLS_ALL
#define TG_HOLD   2304
#define CHUNK     256
#define CAP_WORDS 32768
#define QUANTUM   (DEVICE ? PAGE_LEN \
  : KEEP_WORDS < 32 * PAGE_LEN ? KEEP_WORDS : 32 * PAGE_LEN)
#if DEVICE
#define KEEP_WORDS CHUNK
#endif
#define RING_WORDS (RING_LEN + 2)

#define H_BUMP       0
#define H_CAP        1
#define H_CURSOR     LINE
#define H_ROOT_DONE  (2 * LINE)
#define H_ERROR_CODE (3 * LINE)
#define H_ROOT_WORD  (4 * LINE)
#define H_BANK       (H_ROOT_WORD + WL_RESW)

#define ALC_OFF  ((H_BANK + 3 * NCLS_ALL + PAGE_LEN - 1) & ~(PAGE_LEN - 1))
#define RING_OFF (ALC_OFF + CUBE * 2 * ALC_WORDS)
#define STAK_OFF (RING_OFF + CUBE * RING_WORDS)
#define HEAP_OFF (STAK_OFF + CUBE * STAK_LEN)

// Globals
// =======

#if !DEVICE

typedef pthread_mutex_t lock;

static Corpus CORPUS;
static u64    CORPUS_SIZE;
static u64    ALC[CUBE_SIDE + 1][3 * ALC_WORDS] __attribute__((aligned(128)));
static u32    KEEP_WORDS;
static u32    bank_lock;

static u32            pool_size;
static _Atomic u32    pool_row;
static bool           pool_grow;
static _Atomic u64    pool_tick;
static _Atomic u32    pool_done;
static lock           pool_lock = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t pool_wake = PTHREAD_COND_INITIALIZER;

// The device program compiles from the binary's own text.
#if BEND_METAL || BEND_CUDA
#pragma clang diagnostic ignored "-Wc23-extensions"
static const char BEND_SRC[] = {
#embed __FILE__
, 0 };
#endif

#if BEND_METAL
static id<MTLDevice>               gpu_dev;
static id<MTLCommandQueue>         gpu_que;
static id<MTLLibrary>              gpu_lib;
static id<MTLComputePipelineState> gpu_pso;
static id<MTLBuffer>               gpu_buf;
#elif BEND_CUDA
static CUdevice   gpu_dev;
static CUmodule   gpu_lib;
static CUfunction gpu_pso;
#endif
static bool io_gpu;
static Stk  io_stk;

static const char* CLI_HELP =
  "usage: %s [options]\n"
  "  --threads N        worker threads, up to 128 (default: the CPU count)\n"
  "  --parallel on|off  off means one thread and no GPU (default: on)\n"
  "  --gpu on|off       send ! calls to the GPU (default: on if present)\n"
  "  --gpu-memory 4GB   device span, in MB or GB (default: 2GB on Metal)\n"
  "  --gpu-build        write the GPU program and exit\n"
  "  --help             show this text\n";

#endif

// Tables
// ======

#define TAB_AT(T, S, I) T[S < I ? S : I]

// Fid
// ===

#define fid_arity(x) ((u32)FID_ARITY_T[x])

#define fid_bangs(x) ((bool)(FID_FLAG_T[x] & 1))

#define fid_nofk(x) ((bool)(FID_FLAG_T[x] & 2))

#define fid_seqk(x) ((bool)(FID_FLAG_T[x] & 4))

#define fid_resw(x) ((u32)FID_RESW_T[x])

// Cid
// ===

#define cid_arity(x) ((u32)CID_ARITY_T[x])

#define cid_boxn(x) ((u32)CID_BOXN_T[x])

// A32
// ===

#ifdef __METAL_VERSION__

#define a32_load(p)      atomic_load_explicit(A32(p), RLX)
#define a32_store(p, v)  atomic_store_explicit(A32(p), v, RLX)
#define a32_add(p, v)    atomic_fetch_add_explicit(A32(p), v, RLX)
#define a32_sub(p, v)    atomic_fetch_sub_explicit(A32(p), v, RLX)
#define a32_swp(p, e, v) \
  atomic_compare_exchange_weak_explicit(A32(p), e, v, RLX, RLX)

#elif defined(__CUDACC_RTC__)

#define a32_load(p)     (*(p))
#define a32_store(p, v) (*(p) = (v))
#define a32_add(p, v)   atomicAdd((u32*)(p), v)
#define a32_sub(p, v)   atomicSub((u32*)(p), v)

INLINE bool a32_swp(DEV u32* p, u32* e, u32 v) {
  u32 x = *e;
  *e = atomicCAS((u32*)p, x, v);
  return *e == x;
}

#endif

#if DEVICE

INLINE u32 a32_sub_rel(DEV u32* p, u32 v) {
  FENCE();
  return a32_sub(p, v);
}

INLINE void a32_store_rel(DEV u32* p, u32 v) {
  FENCE();
  a32_store(p, v);
}

INLINE u32 a32_load_acq(DEV u32* p) {
  u32 v = a32_load(p);
  FENCE();
  return v;
}

#define a32_acq(p) FENCE()

INLINE bool a32_cas(DEV u32* p, THR u32* e, u32 v) {
  FENCE();
  bool ok = a32_swp(p, e, v);
  FENCE();
  return ok;
}

#else

#define a32_load(p)         __atomic_load_n(p, __ATOMIC_RELAXED)
#define a32_store(p, v)     __atomic_store_n(p, v, __ATOMIC_RELAXED)
#define a32_add(p, v)       __atomic_fetch_add(p, v, __ATOMIC_RELAXED)
#define a32_sub(p, v)       __atomic_fetch_sub(p, v, __ATOMIC_RELAXED)
#define a32_sub_rel(p, v)   __atomic_fetch_sub(p, v, __ATOMIC_RELEASE)
#define a32_store_rel(p, v) __atomic_store_n(p, v, __ATOMIC_RELEASE)
#define a32_load_acq(p)     __atomic_load_n(p, __ATOMIC_ACQUIRE)
#define a32_acq(p)          ((void)a32_load_acq(p))

INLINE bool a32_cas(u32* p, u32* e, u32 v) {
  return __atomic_compare_exchange_n(
    p, e, v, 1, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE);
}

#endif

#define a32_at(H, word) ((DEV u32*)&(H)[word])

// Err
// ===

#if DEVICE

INLINE void err_post(Corpus H, Err code) {
  u32 seen = 0;
  while (seen == 0 && !a32_cas(a32_at(H, H_ERROR_CODE), &seen, code)) {}
}

#else

static const char* ERR_TEXT[] = { ${ERRS.map((s) => JSON.stringify(s))
  .join(",\n  ")} };

static void err_fail(Err code, const char* msg) {
  fflush(stdout);
  fprintf(stderr, "bend: %s\n", msg);
  _exit(1);
}

static void err_post(Corpus H, Err code) {
  err_fail(code, ERR_TEXT[code]);
}

static void err_trap(int sig) {
  err_post(NULL, ERR_DEEP);
}

#endif

#define err_seen(H)    (DEVICE && a32_load(a32_at(H, H_ERROR_CODE)) != 0)
#define err_spun(H, n) ((++*(n) & 4095) == 0 && err_seen(H))

${NATIVE.C}
// Cls
// ===

INLINE Cls cls_fit(u32 words) {
  return words > 1 ? 32 - CLZ(words - 1) : 0;
}

// Bank
// ====

// One stack of exact generations per class; 2 heap_words / max(CHUNK,
// 2^c) entries cover the old ones plus a pass of returns. The host
// pops and pushes at rd under bank_lock; a device pass pops down from
// rd and pushes above top, and the host then compacts [top, wr) onto
// rd, so a pass never sees what it handed.

#define bank_at(H, c) ((DEV Bank*)((H) + H_BANK) + (c))

INLINE Loc bank_pop(Corpus H, Cls c) {
  DEV Bank* b = bank_at(H, c);
  Loc got = 0;
  LOCK(bank_lock);
  u32 t = a32_sub(&b->rd, 1);
  if ((int)t > 0) {
    got = H[b->off + t - 1];
  } else {
    a32_add(&b->rd, 1);
  }
  if (!DEVICE) {
    b->wr = b->top = b->rd;
  }
  UNLOCK(bank_lock);
  return got;
}

INLINE void bank_push(Corpus H, Cls c, Loc head) {
  DEV Bank* b = bank_at(H, c);
  LOCK(bank_lock);
  H[b->off + a32_add(&b->wr, 1)] = head;
  if (!DEVICE) {
    b->rd = b->top = b->wr;
  }
  UNLOCK(bank_lock);
}

// Heap
// ====

// Per lane and class (a tile row on the device): HOT, a LIFO chain of
// free slots (word 0 the head it replaced); LEN, its exact length in
// words, off the chain; on the host COLD, one generation. A free is a
// push and an add. A host free at KEEP_WORDS (a slot for a wide class)
// runs heap_hand: COLD to the bank, HOT parked as COLD, generations
// exact. A miss takes COLD, else a bank entry, else a quantum of at
// most a generation, and sets LEN to what it took: no adoption past a
// generation, no list re-aged. A device lane keeps its frees for the
// pass; at the kernel end dev_cut hands its complete generations,
// walking only those. KEEP_WORDS is CAP_WORDS, or CHUNK with the GPU
// (fixed at boot), so a device lane may adopt every host entry.
// Bounds: a host lane and class under 2 max(KEEP_WORDS, 2^c) words, a
// device one under max(CHUNK, 2^c) after each kernel plus its own
// frees within one, bank entries exact. The bump grows only when this
// lane's HOT and COLD and the class's bank are empty. A zero row is an
// empty lane.

#define ALC_AT(e, i)   (e).alc[(i) * LANE_STEP]
#define ALC_LEN(e, c)  ALC_AT(e, ALC_WORDS + (c))
#define ALC_COLD(e, c) ALC_AT(e, 2 * ALC_WORDS + (c))
#define KEEP(c)        (KEEP_WORDS >> (c) ? KEEP_WORDS >> (c) : 1)

OUTLINE void heap_hand(Env e, Cls cls) {
  Loc cold = ALC_COLD(e, cls);
  if (cold) {
    bank_push(e.mem, cls, cold);
  }
  ALC_COLD(e, cls) = ALC_AT(e, cls);
  ALC_AT(e, cls)   = 0;
  ALC_LEN(e, cls)  = 0;
}

OUTLINE Loc heap_alloc_miss(Env e, Cls cls) {
  Corpus H = e.mem;
  Loc  got = 0;
  if (!DEVICE) {
    got = ALC_COLD(e, cls);
    ALC_COLD(e, cls) = 0;
  }
  if (!got) {
    got = bank_pop(H, cls);
  }
  u32 n = got ? KEEP(cls) : cls < NCLS ? QUANTUM >> cls : 1;
  if (!got) {
    u32 pages = (n << cls) >> PAGE_BITS;
    u32 p     = a32_add(a32_at(H, H_BUMP), pages);
    if ((u64)p + pages > a32_load(a32_at(H, H_CAP))) {
      err_post(H, ERR_HEAP);
      p = 0;
    }
    got = HEAP_OFF + ((u64)p << PAGE_BITS);
    for (u32 i = 1; i <= n; i += 1) {
      H[got + ((u64)(i - 1) << cls)] = i < n ? got + ((u64)i << cls) : 0;
    }
  }
  ALC_AT(e, cls)  = H[got];
  ALC_LEN(e, cls) = (u64)(n - 1) << cls;
  return got;
}

INLINE Loc heap_alloc(Env e, Cls cls) {
  Loc h = ALC_AT(e, cls);
  if (h) {
    ALC_AT(e, cls)   = e.mem[h];
    ALC_LEN(e, cls) -= 1ull << cls;
    return h;
  }
  return heap_alloc_miss(e, cls);
}

INLINE void heap_free(Env e, Cls cls, Loc loc) {
  if (err_seen(e.mem)) {
    return;
  }
  e.mem[loc]       = ALC_AT(e, cls);
  ALC_AT(e, cls)   = loc;
  ALC_LEN(e, cls) += 1ull << cls;
  if (!DEVICE && ALC_LEN(e, cls) >= KEEP_WORDS) {
    heap_hand(e, cls);
  }
}

// Spare
// =====

INLINE void spare_free(Env e, Cls cls, Loc loc) {
  if (loc != 0) {
    heap_free(e, cls, loc);
  }
}

// Term
// ====

INLINE Term term_make(u64 tag, u64 aux, Loc loc) {
  return (tag << 56) | (aux << 40) | loc;
}

#define term_ctr(cid, loc) term_make(TAG_CTR, cid, loc)
#define term_pak(cid, loc) term_make(TAG_PAK, cid, loc)
#define term_clo(fid, loc) term_make(TAG_CLO, fid, loc)
#define term_buf(cls, loc) term_make(TAG_BUF, cls, loc)
#define term_tsk(fid, loc) term_make(TAG_TSK, fid, loc)

INLINE Term term_blk(bool arr, Cls cls, Loc loc) {
  return term_buf(cls, loc) | ((u64)arr << 57);
}

INLINE u64 term_tag(Term t) {
  return (t >> 56) & 0x7f;
}

INLINE bool term_rfc(Term t) {
  return (t & RFC_BIT) != 0;
}

INLINE u64 term_aux(Term t) {
  return (t >> 40) & 0xFFFF;
}

INLINE Loc term_loc(Term t) {
  return t & LOC_MASK;
}

INLINE bool term_triv(Term t) {
  return term_tag(t) <= TAG_PAK || t == TERM_HOLE;
}

OUTLINE Term rfc_wrap(Env e, Term t, u32 cnt) {
  if (term_tag(t) == TAG_CLO || term_tag(t) == TAG_TSK) {
    err_post(e.mem, ERR_RFCS);
    return t;
  }
  Loc r = heap_alloc(e, 0);
  e.mem[r] = ((u64)term_loc(t) << 24) | cnt;
  return (t & ~LOC_MASK) | RFC_BIT | r;
}

INLINE Term rfc_seal(Env e, Term t) {
  if (term_tag(t) != TAG_CTR || term_rfc(t)) {
    return t;
  }
  return rfc_wrap(e, t, 1);
}

INLINE u64 rfc_view(Env e, Loc r) {
  DEV u32* w = a32_at(e.mem, r);
  u64 cell = ((u64)a32_load(w + 1) << 32) | a32_load(w);
  if ((cell & RFC_CNT) == 1) {
    a32_acq(w);
  }
  return cell;
}

INLINE void rfc_bump(Env e, Loc r) {
  u32 c = a32_add(a32_at(e.mem, r), 1);
  if ((c & RFC_CNT) >= RFC_CNT - 1) {
    err_post(e.mem, ERR_RFCS);
  }
}

INLINE Term term_keep(Env e, Term t) {
  if (term_rfc(t)) {
    rfc_bump(e, term_loc(t));
    return t;
  }
  if (term_triv(t)) {
    return t;
  }
  return rfc_wrap(e, t, 2);
}

INLINE Loc term_peek(Env e, Term t) {
  if (term_rfc(t)) {
    return rfc_view(e, term_loc(t)) >> 24;
  }
  return term_loc(t);
}

INLINE Cls blk_cls(Env e, Term t) {
  return (u32)term_aux(t) & 31;
}

#define buf_wcls(c) ((c) == 0 ? 0 : (c) - 1)

INLINE Cls blk_span(Env e, Term t) {
  Cls c = blk_cls(e, t);
  return term_tag(t) == TAG_ARR ? c : buf_wcls(c);
}

INLINE void blk_free(Env e, Term t) {
  heap_free(e, blk_span(e, t), term_loc(t));
}

static void term_drop(Env e, Term t) {
  Corpus H = e.mem;
  u64  cur = 0;
  Term c0  = 0;
  u32  step = 0;
  for (;;) {
    if (!term_triv(t) && term_rfc(t)) {
      Loc      r = term_loc(t);
      DEV u32* p = a32_at(H, r);
      if ((a32_sub_rel(p, 1) & RFC_CNT) != 1) {
        t = 0;
      } else {
        a32_acq(p);
        t = (t & ~(RFC_BIT | LOC_MASK)) | (H[r] >> 24);
        heap_free(e, 0, r);
      }
    }
    if (term_tag(t) == TAG_CLO && fid_arity((u32)term_aux(t)) == 1) {
      t = 0;
    }
    if (!term_triv(t)) {
      u64 tag = term_tag(t);
      if (tag == TAG_BUF) {
        blk_free(e, t);
      } else {
        u32 aux = (u32)term_aux(t);
        Loc loc = term_loc(t);
        u32 n   = 0;
        Cls cls;
        if (tag == TAG_ARR) {
          cls = 64 | blk_cls(e, t);
        } else {
          u32 ar;
          if (tag == TAG_CTR) {
            ar = cid_arity(aux);
            n  = cid_boxn(aux);
          } else if (tag == TAG_CLO) {
            ar = fid_arity(aux) - 1;
            n  = ar;
          } else {
            ar = fid_arity(aux);
            n  = ar;
          }
          cls = cls_fit(tag == TAG_TSK ? ar + 2 : ar);
        }
        c0 = H[loc];
        H[loc] = cur;
        cur = loc | ((u64)n << 48) | ((u64)cls << 56);
      }
    }
    for (;;) {
      if (err_spun(H, &step)) {
        return;
      }
      if (cur == 0) {
        return;
      }
      Loc  loc = cur & LOC_MASK;
      u32  i   = (u8)(cur >> 40);
      u32  n   = (u8)(cur >> 48);
      Cls  cls = (u32)(cur >> 56);
      bool arr = cls > 63;
      u32  j   = i;
      if (arr) {
        cls &= 63;
        n   = 1u << cls;
        if (i == 2) {
          j = (u32)H[loc + 1];
        }
      }
      if (j < n) {
        Term c = j == 0 ? c0 : H[loc + j];
        if (arr && j > 0) {
          H[loc + 1] = j + 1;
        }
        if (!arr || i < 2) {
          cur += 1ull << 40;
        }
        if (!term_triv(c)) {
          t = c;
          break;
        }
      } else {
        u64 up = H[loc];
        heap_free(e, cls, loc);
        cur = up;
      }
    }
  }
}

INLINE void term_sink(Env e, Term t) {
  if (!term_triv(t)) {
    term_drop(e, t);
  }
}

OUTLINE void span_fade(Env e, Term t, Loc src, u32 n) {
  for (u32 j = 0; j < n; j += 1) {
    Term f = e.mem[src + j];
    if (term_rfc(f)) {
      rfc_bump(e, term_loc(f));
    } else if (!term_triv(f)) {
      err_post(e.mem, ERR_RFCS);
    }
  }
  term_drop(e, t);
}

INLINE Loc ctr_take(Env e, Term t, u32 n, THR Term* out) {
  Corpus H = e.mem;
  if (!term_rfc(t)) {
    for (u32 j = 0; j < n; j += 1) {
      out[j] = H[term_loc(t) + j];
    }
    return term_loc(t);
  }
  Loc r    = term_loc(t);
  u64 cell = rfc_view(e, r);
  Loc src  = cell >> 24;
  for (u32 j = 0; j < n; j += 1) {
    out[j] = H[src + j];
  }
  if ((cell & RFC_CNT) == 1) {
    heap_free(e, 0, r);
    return src;
  }
  span_fade(e, t, src, n);
  return 0;
}

INLINE Term term_word(Env e, Term w) {
  u32 x = 0;
  Term t = w;
  for (u32 i = 0; i < 32 && term_aux(t) == CID_WCON; i += 1) {
    Loc l = term_peek(e, t);
    x |= (u32)(e.mem[l] & 1) << i;
    t = e.mem[l + 1];
  }
  term_sink(e, w);
  return x;
}

// Blk
// ===

// A block owns one allocation in its physical class (an ARR of class
// c 2^c Terms in 2^c words, a BUF 2^c u32 in 2^buf_wcls(c) words) and
// blk_free returns it there. A match on ANode is blk_half twice: each
// half allocated in its class and copied, the source freed shallow by
// the high call (its elements moved; the emitter binds the low half
// first). ANode{l, r} is blk_node: the merged class, l and r copied
// and freed shallow. Array.clone is blk_copy: a BUF raw, an ARR's
// elements retained through blk_keep. A match to the leaves copies
// O(n log n) words where a view copied none; get, set, swap, size and
// new open no half.

#define BLK_ALLOC(n, w) \
  Loc n = heap_alloc(e, w); \
  if (err_seen(e.mem)) { \
    return term_buf(0, n); \
  }

INLINE DEV u32a* blk_ptr(Corpus H, Loc loc, u32 i) {
  return (DEV u32a*)(H + loc) + i;
}

INLINE Term blk_read(Corpus H, bool arr, Loc loc, u32 i) {
  if (arr) {
    return H[loc + i];
  }
  return (u64)*blk_ptr(H, loc, i);
}

INLINE void blk_write(Corpus H, bool arr, Loc loc, u32 i, Term v) {
  if (arr) {
    H[loc + i] = v;
  } else {
    *blk_ptr(H, loc, i) = (u32)v;
  }
}

INLINE u32 blk_at(Env e, Term a, U32 i, u32 lgs) {
  return ((u32)i & (u32)((1ull << (blk_cls(e, a) - lgs)) - 1)) << lgs;
}

INLINE Term blk_keep(Env e, Loc at) {
  Term w = e.mem[at];
  Term v = term_keep(e, w);
  if (v != w) {
    e.mem[at] = v;
  }
  return v;
}

OUTLINE Term blk_copy(Env e, Term a) {
  Corpus H = e.mem;
  bool arr = term_tag(a) == TAG_ARR;
  Cls cls = blk_span(e, a);
  Loc src = term_loc(a);
  BLK_ALLOC(dst, cls)
  for (u64 j = 0; j < (1ull << cls); j += 1) {
    H[dst + j] = arr ? blk_keep(e, src + j) : H[src + j];
  }
  return term_blk(arr, blk_cls(e, a), dst);
}

INLINE Term blk_node(Env e, Term l, Term r) {
  Corpus H = e.mem;
  bool arr = term_tag(l) == TAG_ARR;
  Cls c = blk_cls(e, l);
  if (c != blk_cls(e, r) || c + 1 >= NCLS_ALL) {
    err_post(H, ERR_TAGS);
    return l;
  }
  Loc pl = term_loc(l);
  Loc pr = term_loc(r);
  BLK_ALLOC(n, arr ? c + 1 : c)
  if (!arr && c == 0) {
    H[n] = (u64)*blk_ptr(H, pl, 0) | ((u64)*blk_ptr(H, pr, 0) << 32);
  } else {
    u64 cw = 1ull << blk_span(e, l);
    for (u64 w = 0; w < cw; w += 1) {
      H[n + w]      = H[pl + w];
      H[n + cw + w] = H[pr + w];
    }
  }
  blk_free(e, l);
  blk_free(e, r);
  return term_blk(arr, c + 1, n);
}

INLINE Term blk_half(Env e, Term a, u32 hi) {
  Corpus H = e.mem;
  bool arr = term_tag(a) == TAG_ARR;
  Cls c = blk_cls(e, a);
  if (c == 0) {
    err_post(H, ERR_TAGS);
    return a;
  }
  c -= 1;
  Cls cw = arr ? c : buf_wcls(c);
  BLK_ALLOC(n, cw)
  if (!arr && c == 0) {
    H[n] = (u64)*blk_ptr(H, term_loc(a), hi);
  } else {
    Loc src = term_loc(a) + ((u64)hi << cw);
    for (u64 w = 0; w < (1ull << cw); w += 1) {
      H[n + w] = H[src + w];
    }
  }
  if (hi) {
    blk_free(e, a);
  }
  return term_blk(arr, c, n);
}

INLINE Term blk_new(Env e, bool arr, Nat d, u32 lgs, u32 n, THR Term* v) {
  Corpus H = e.mem;
  if (d + lgs > 31) {
    err_post(H, ERR_ARRS);
    d = 0;
  }
  Cls c = (u32)d + lgs;
  BLK_ALLOC(l, arr ? c : buf_wcls(c))
  for (u32 j = 0; j < n; j += 1) {
    Term w = v[j];
    if (arr && d > 0 && !term_triv(w)) {
      if (d >= 24) {
        err_post(H, ERR_RFCS);
      } else if (term_rfc(w)) {
        u32 k = (1u << d) - 1;
        u32 got = a32_add(a32_at(H, term_loc(w)), k);
        if ((got & RFC_CNT) >= RFC_CNT - k) {
          err_post(H, ERR_RFCS);
        }
      } else {
        w = rfc_wrap(e, w, 1u << d);
      }
    }
    v[j] = w;
  }
  for (u64 i = 0; i < (1ull << c); i += 1) {
    blk_write(H, arr, l, (u32)i, i % (1u << lgs) < n ? v[i % (1u << lgs)] : 0);
  }
  return term_blk(arr, c, l);
}

// Ring
// ====

#define ring_word(H, r, w) ((H) + RING_OFF + (w) * CUBE + (r))
#define ring_slot(H, r, p) ring_word(H, r, (p) & (RING_LEN - 1))
#define ring_get(H, r)     ((DEV u32*)ring_word(H, r, RING_LEN))
#define ring_put(H, r)     ((DEV u32*)ring_word(H, r, RING_LEN + 1))

INLINE u32 ring_lap(u32 pos) {
  return ~(u32)(pos / RING_LEN) & 1;
}

INLINE void ring_push(Corpus H, Ring r, Term tsk) {
  u32 pos = a32_add(ring_put(H, r), 1);
  if (pos - a32_load(ring_get(H, r)) >= RING_LEN) {
    err_post(H, ERR_RING);
    return;
  }
  DEV u32* lo = (DEV u32*)ring_slot(H, r, pos);
  a32_store(lo, (u32)tsk);
  a32_store_rel(lo + 1, (u32)(tsk >> 32) | (ring_lap(pos) << 31));
}

INLINE Ring ring_flip(u32 i) {
  return i / CUBE_SIDE + CUBE_SIDE * (i % CUBE_SIDE);
}

#define ring_pick(b, s, c) ((b) + (s) * (CUR_STEP(c) & (CUBE_SIDE - 1)))

// Task
// ====

INLINE Loc task_node(Env e, Fid fid, Term cont, u32 idx, u32 rem) {
  u32 ar  = fid_arity(fid);
  Loc loc = heap_alloc(e, cls_fit(ar + 2));
  for (u32 i = 0; rem && i < ar; i += 1) {
    e.mem[loc + i] = TERM_HOLE;
  }
  e.mem[loc + ar]     = cont;
  e.mem[loc + ar + 1] = ((u64)idx << 32) | rem;
  return loc;
}

INLINE Loc task_tail(Term t) {
  return term_loc(t) + fid_arity((u32)term_aux(t));
}

INLINE Term task_deliver(Corpus H, Term cont, u32 idx, THR Term* v, u32 n) {
  Loc at = cont == TERM_HOLE ? H_ROOT_WORD : term_loc(cont) + idx;
  for (u32 j = 0; j < WL_RESW; j += 1) {
    if (j < n) {
      H[at + j] = v[j];
    }
  }
  if (cont == TERM_HOLE) {
    a32_store_rel(a32_at(H, H_ROOT_DONE), n + 1);
    return 0;
  }
  Loc tl = task_tail(cont);
  if (a32_sub_rel(a32_at(H, tl + 1), 1) == 1) {
    a32_acq(a32_at(H, tl + 1));
    return cont;
  }
  return 0;
}

INLINE void task_deal(Corpus H, Term join, u32 base, u32 stride, Cursor cur) {
  Loc loc = term_loc(join);
  u32 ar  = fid_arity((u32)term_aux(join));
  u32 g   = 0;
  if (stride == 0) {
    u32 rem = (u32)H[loc + ar + 1];
    g = a32_add(a32_at(H, H_CURSOR), rem);
  }
  for (u32 i = 0; i < ar; i += 1) {
    Term k = H[loc + i];
    if (term_tag(k) == TAG_TSK) {
      H[loc + i] = TERM_HOLE;
      Ring to;
      if (stride != 0) {
        to = ring_pick(base, stride, cur);
      } else {
        to = ring_flip(g & (u32)(CUBE - 1));
        g += 1;
      }
      ring_push(H, to, k);
    }
  }
}

// Root
// ====

INLINE bool root_done(Corpus H) {
  return a32_load_acq(a32_at(H, H_ROOT_DONE)) != 0;
}

static u32 root_take(Corpus H, THR Term* v) {
  u32 n = a32_load_acq(a32_at(H, H_ROOT_DONE)) - 1;
  for (u32 j = 0; j < n; j += 1) {
    v[j] = H[H_ROOT_WORD + j];
  }
  a32_store(a32_at(H, H_ROOT_DONE), 0);
  return n;
}

// Spins
// =====

// Work
// ====

// A host self-jump is a tail call: as a loop, MachineLICM hoisted eleven
// constants into symreg's entry (3.05 s against 2.51 s).
#if !DEVICE
#undef  WL_SPIN
#undef  WL_SPUN
#undef  WL_AGAIN
#define WL_SPIN(F)
#define WL_SPUN
#define WL_AGAIN(F) __attribute__((musttail)) return WL_##F(WL_ALL)

typedef Reply (__attribute__((preserve_none)) *WlFn)(WL_SIG);
#define WL_X(F) WL_FN WL_##F(WL_SIG);
WL_TABLE WL_X(FID_ENTER)
#undef WL_X
#define WL_X(F) WL_##F,
static const WlFn wl_tab[] = { WL_TABLE };
#undef WL_X
#endif

static Reply work_loop(Env e, Stk sp, Term t, bool seq) {
  WL_BANK
  u32 rn = 0;
  r0 = t;
#if DEVICE
  Fid fid   = FID_ENTER;
  u32 wpoll = 0;
  for (;;) {
  if (err_spun(e.mem, &wpoll)) {
    return 0;
  }
  switch (fid) {
#else
  return WL_FID_ENTER(WL_ALL);
}
#endif

// Segments
// ========

// A task enters through its words: a continuation's results ride r0.. and
// its parameters the stack; any other segment's parameters ride r0...
  WL_CASE(FID_ENTER)
  {
    Term t = r0;
    WL_OPEN
    Fid f   = (u32)term_aux(t);
    Loc a   = term_loc(t);
    u32 war = fid_arity(f);
    WL_FRAME(t)
    if (fid_seqk(f)) {
      u32 rw = fid_resw(f);
      WL_LOAD(a + war - rw, rw)
      WL_ARGS(a, war - rw + 1)
    } else {
      WL_LOAD(a, war)
    }
    heap_free(e, cls_fit(war + 2), a);
    WL_DYN(f);
  }}

  WL_CASE(FID_IO_EMIT)
  {
    Term x = r0;
    WL_OPEN
    Loc l = heap_alloc(e, 0);
    e.mem[l] = x;
    r0 = term_ctr(CID_EMIT, l);
    WL_RETN(1);
  }}

  WL_CASE(FID_CLO_APPLY)
  {
    Term fun = r0;
    Term arg = r1;
    WL_OPEN
    Fid f    = (Fid)term_aux(fun);
    u32 war  = fid_arity(f) - 1;
    Loc a    = term_loc(fun);
    WL_LOAD(a, war)
    spare_free(e, cls_fit(war), a);
    WL_LAST(arg)
    WL_DYN(f);
  }}

  WL_CASE(FID_EXIT)
  {
    u32  n = rn;
    Term rv[WL_RESW];
    WL_SAVE(rv)
    WL_OPEN
    if (err_seen(e.mem)) {
      return 0;
    }
    sp -= 2 * LANE_STEP;
    Term cont = STK(0);
    u32  idx  = (u32)STK(1);
    if (cont != TERM_HOLE && fid_seqk((u32)term_aux(cont))) {
      Fid wf = (u32)term_aux(cont);
      Loc wa = term_loc(cont);
      u32 wn = fid_arity(wf);
      WL_FRAME(cont)
      WL_ARGS(wa, wn - n + 1)
      heap_free(e, cls_fit(wn + 2), wa);
      WL_TAKE(rv)
      WL_DYN(wf);
    }
    return task_deliver(e.mem, cont, idx, rv, n);
  }}

#if DEVICE
  default: {
    err_post(e.mem, ERR_FIDS);
    return 0;
  }
  }
  }
}
#endif

// Monk
// ====

// One turn on a ring: its head task below put0 runs (a growing lane skips
// a fork-free one). The host grows a row ring by ring and works a ring
// until it drains; a device lane does both.
INLINE u32 monk_step(Env e, Stk stk, Ring rg, u32 put0, bool seq, u32 base,
  u32 stride, Cursor cur) {
  Corpus   H   = e.mem;
  DEV u32* get = ring_get(H, rg);
  if (*get == put0) {
    return 0;
  }
  DEV u32* lo = (DEV u32*)ring_slot(H, rg, *get);
  u32      hi = a32_load_acq(lo + 1);
  Term     t  = (((u64)hi << 32) | a32_load(lo)) & ~RFC_BIT;
  if ((hi >> 31) != ring_lap(*get) || (!seq && fid_nofk((u32)term_aux(t)))) {
    return 0;
  }
  a32_store(get, *get + 1);
  u32 spin = 0;
  for (;;) {
    Reply r = work_loop(e, stk, t, seq);
    if (r == 0) {
      return 2;
    }
    if ((u32)H[task_tail(r) + 1] == 0) {
      if (err_spun(H, &spin)) {
        return 2;
      }
      if (stride != 0) {
        ring_push(H, ring_pick(base, stride, cur), r);
        return 2;
      }
      t   = r;
      seq = false;
      continue;
    }
    task_deal(H, r, base, stride, cur);
    return 1;
  }
}

// Dev
// ===

// A kernel reserves TG_HOLD words of threadgroup memory (lane 0's write
// keeps it): one resident threadgroup per Apple core; without it bitonic
// runs 1.35x, kmeans 1.19x, matmul 1.13x. A grow pass runs at most
// CUBE_SIDE rounds, so a program that never fills a group still cuts at
// a kernel end.

#if DEVICE

INLINE void dev_cut(Env e) {
  if (err_seen(e.mem)) {
    return;
  }
  for (Cls c = 0; c < NCLS_ALL; c += 1) {
    u64 gen = (u64)KEEP(c) << c;
    while (ALC_LEN(e, c) >= gen) {
      Loc head = ALC_AT(e, c);
      Loc tail = head;
      for (u32 i = KEEP(c); --i;) {
        tail = e.mem[tail];
      }
      ALC_AT(e, c)    = e.mem[tail];
      ALC_LEN(e, c)  -= gen;
      e.mem[tail]     = 0;
      bank_push(e.mem, c, head);
    }
  }
}

// One kernel, one pipeline: pass 0 grows the frontier (a task a lane a
// turn, votes between barriers), pass 1 works it (a lane drains its
// ring); one call of monk_step, so the program compiles once.
#ifdef __METAL_VERSION__
kernel void bend_dev(Corpus H [[buffer(0)]], constant u32& pass [[buffer(1)]],
  GRP volatile u64* hold [[threadgroup(0)]],
  u32 grids [[threadgroups_per_grid]],
  u32 row [[threadgroup_position_in_grid]],
  u32 lane [[thread_position_in_threadgroup]]) {
#else
extern "C" __global__ void bend_dev(Corpus H, u32 pass) {
  extern __shared__ volatile u64 hold[];
  u32 grids = gridDim.x;
  u32 row   = blockIdx.x;
  u32 lane  = threadIdx.x;
#endif
  u32  stride = grids == 1 ? CUBE_SIDE : 1;
  u32  me     = row * CUBE_SIDE + stride * lane;
  Ring rg     = pass ? ring_flip(me) : me;
  Env  e      = { H, H + ALC_OFF + me };
  Stk  stk    = (Stk)(H + STAK_OFF + me);
  if (lane == 0) {
    hold[0] = 0;
  }
  GA32 tg_cur;
  GA32 tg_grew;
  GA32 tg_has;
  g32_ini(&tg_cur);
  g32_ini(&tg_grew);
  g32_ini(&tg_has);
  BAR();
  u32 put0      = a32_load(ring_put(H, rg));
  u32 seen_has  = 0;
  u32 seen_grew = 0;
  for (u32 turn = 0; pass || turn < CUBE_SIDE; turn += 1) {
    if (pass) {
      if (*ring_get(H, rg) == put0 || err_seen(H)) {
        break;
      }
    } else {
      put0 = a32_load(ring_put(H, rg));
      u32 vote = put0 != a32_load(ring_get(H, rg));
      if (lane == 0 && (err_seen(H) || root_done(H))) {
        vote = CUBE_SIDE;
      }
      g32_add(&tg_has, vote);
      BAR();
      u32 has = g32_get(&tg_has);
      if (has - seen_has >= CUBE_SIDE) {
        break;
      }
      seen_has = has;
    }
    u32 ran = monk_step(e, stk, rg, put0, pass, pass ? rg : row * CUBE_SIDE,
      pass ? 0 : stride, &tg_cur);
    if (!pass) {
      if (ran == 1) {
        g32_add(&tg_grew, 1);
      }
      BARD();
      u32 grew = g32_get(&tg_grew);
      if (grew == seen_grew) {
        break;
      }
      seen_grew = grew;
    }
  }
  dev_cut(e);
}

#endif

#if !DEVICE

// Row
// ===

static void row_grow(Env e, Stk stk, u32 base) {
  Corpus H = e.mem;
  u32 cur = 0;
  for (;;) {
    u32 put0[CUBE_SIDE];
    u32 has = 0;
    for (u32 i = 0; i < CUBE_SIDE; i += 1) {
      put0[i] = *ring_put(H, base + i);
      has += put0[i] != *ring_get(H, base + i);
    }
    if (root_done(H) || has == CUBE_SIDE) {
      return;
    }
    u32 grew = 0;
    u32 ran  = 0;
    for (u32 i = 0; i < CUBE_SIDE && ran != 2; i += 1) {
      ran   = monk_step(e, stk, base + i, put0[i], false, base, 1, &cur);
      grew += ran == 1;
    }
    if (grew == 0) {
      return;
    }
  }
}

// Pool
// ====

static void* pool_mmap(u64 bytes) {
  void* p = mmap(NULL, bytes, PROT_READ | PROT_WRITE,
    MAP_PRIVATE | MAP_ANON | MAP_NORESERVE, -1, 0);
  if (p == MAP_FAILED) {
    err_fail(ERR_HEAP, "reservation failed");
  }
  return p;
}

static Term* pool_stack(void) {
  u64   len = 1ull << 31;
  char* p   = pool_mmap(len + 16384 + SIGSTKSZ);
  if (mprotect(p + len, 16384, PROT_NONE) != 0) {
    err_fail(ERR_HEAP, "stack guard failed");
  }
  stack_t ss = { .ss_sp = p + len + 16384, .ss_size = SIGSTKSZ };
  sigaltstack(&ss, NULL);
  struct sigaction sa = { .sa_handler = err_trap, .sa_flags = SA_ONSTACK };
  sigaction(SIGSEGV, &sa, NULL);
  sigaction(SIGBUS, &sa, NULL);
  return (Term*)p;
}

static void* pool_work(void* arg) {
  Term* stk  = pool_stack();
  u64   seen = 0;
  for (;;) {
    pthread_mutex_lock(&pool_lock);
    while (atomic_load_explicit(&pool_tick, memory_order_acquire) == seen) {
      pthread_cond_wait(&pool_wake, &pool_lock);
    }
    pthread_mutex_unlock(&pool_lock);
    seen = atomic_load_explicit(&pool_tick, memory_order_acquire);
    Env e = { CORPUS, ALC[1 + (u32)(uintptr_t)arg] };
    for (;;) {
      u32 r = atomic_fetch_add_explicit(&pool_row, 1, memory_order_relaxed);
      if (r >= (pool_grow ? CUBE_SIDE : CUBE / LINE)) {
        break;
      }
      if (pool_grow) {
        row_grow(e, stk, r * CUBE_SIDE);
      } else {
        for (u32 i = 0; i < LINE; i += 1) {
          Ring rg   = r * LINE + i;
          u32  put0 = a32_load(ring_put(e.mem, rg));
          while (*ring_get(e.mem, rg) != put0 && !err_seen(e.mem)) {
            monk_step(e, stk, rg, put0, true, rg, 0, NULL);
          }
        }
      }
    }
    u32 done = atomic_fetch_add_explicit(&pool_done, 1, memory_order_release);
    if (done + 1 == pool_size) {
      pthread_mutex_lock(&pool_lock);
      pthread_cond_broadcast(&pool_wake);
      pthread_mutex_unlock(&pool_lock);
    }
  }
}

OUTLINE void pool_open(void) {
  static bool up;
  if (up) {
    return;
  }
  up = true;
  struct rlimit rlim;
  pthread_attr_t attr;
  u64 most = 1ull << 30;
  bool sized = getrlimit(RLIMIT_STACK, &rlim) == 0
    && pthread_attr_init(&attr) == 0
    && pthread_attr_setstacksize(&attr,
      rlim.rlim_cur < most ? rlim.rlim_cur : most) == 0;
  if (!sized) {
    err_fail(ERR_FAIL, "worker stack sizing");
  }
  for (u32 w = 0; w < pool_size; w += 1) {
    pthread_t tid;
    if (pthread_create(&tid, &attr, pool_work, (void*)(uintptr_t)w)) {
      err_fail(ERR_FAIL, "pthread_create");
    }
  }
}

OUTLINE void pool_turn(bool grow) {
  pool_grow = grow;
  atomic_store_explicit(&pool_row, 0, memory_order_relaxed);
  atomic_store_explicit(&pool_done, 0, memory_order_relaxed);
  pthread_mutex_lock(&pool_lock);
  atomic_fetch_add_explicit(&pool_tick, 1, memory_order_release);
  pthread_cond_broadcast(&pool_wake);
  while (atomic_load_explicit(&pool_done, memory_order_acquire) < pool_size) {
    pthread_cond_wait(&pool_wake, &pool_lock);
  }
  pthread_mutex_unlock(&pool_lock);
}

// Gpu
// ===

// gpu_make compiles the device program and, given a path, writes it as
// <binary>.gpu (--gpu-build, run by bend -o): Metal's binary archive
// of the pipeline (keyed by the compiled function, so a wrong file
// misses), CUDA's cubin behind a hash of the text. A launch loads it,
// else notes and compiles (Metal's OS cache keeps that pipeline; CUDA
// writes the file).

static const char* gpu_path(void) {
  static char path[4096];
  u32 n = sizeof path - 8;
#if BEND_METAL
  _NSGetExecutablePath(path, &n);
#else
  path[readlink("/proc/self/exe", path, n)] = 0;
#endif
  return strcat(path, ".gpu");
}

static void gpu_note(const char* path) {
  fprintf(stderr, "bend: compiling the GPU program (%s is missing or"
    " stale)\n", path);
}

#if !BEND_CUDA
#define gpu_map pool_mmap
#endif

#if BEND_METAL

static bool gpu_probe(void) {
  return (gpu_dev = MTLCreateSystemDefaultDevice()) != nil;
}

static MTLComputePipelineDescriptor* gpu_desc(void) {
  NSError* err = nil;
  MTLCompileOptions* opts = [MTLCompileOptions new];
  opts.mathMode = MTLMathModeSafe;
  gpu_lib = [gpu_dev newLibraryWithSource:@(BEND_SRC) options:opts error:&err];
  if (!gpu_lib) {
    err_fail(ERR_FAIL, [[err localizedDescription] UTF8String]);
  }
  MTLComputePipelineDescriptor* d = [MTLComputePipelineDescriptor new];
  d.computeFunction = [gpu_lib newFunctionWithName:@"bend_dev"];
  return d;
}

static bool gpu_make(const char* path) {
  NSError* err = nil;
  id<MTLBinaryArchive> ar = [gpu_dev
    newBinaryArchiveWithDescriptor:[MTLBinaryArchiveDescriptor new] error:&err];
  if (![ar addComputePipelineFunctionsWithDescriptor:gpu_desc() error:&err]) {
    err_fail(ERR_FAIL, [[err localizedDescription] UTF8String]);
  }
  return [ar serializeToURL:[NSURL fileURLWithPath:@(path)] error:&err];
}

static id<MTLComputePipelineState> gpu_pipe(MTLComputePipelineDescriptor* d,
  id<MTLBinaryArchive> ar) {
  NSError* err = nil;
  d.binaryArchives = ar ? @[ar] : @[];
  return [gpu_dev newComputePipelineStateWithDescriptor:d
    options:ar ? MTLPipelineOptionFailOnBinaryArchiveMiss : 0 reflection:nil
    error:&err];
}

static u64 gpu_span(void) {
  u64 span = [gpu_dev recommendedMaxWorkingSetSize];
  u64 most = [gpu_dev maxBufferLength];
  span = span < most ? span : most;
  return span < (2ull << 30) ? span : 2ull << 30;
}

static void gpu_load(u64 bytes) {
  gpu_buf = [gpu_dev newBufferWithBytesNoCopy:CORPUS length:bytes
    options:MTLResourceStorageModeShared
      | MTLResourceHazardTrackingModeUntracked deallocator:nil];
  if (!gpu_buf) {
    err_fail(ERR_HEAP, "--gpu-memory is more than the device has");
  }
  @autoreleasepool {
    gpu_que = [gpu_dev newCommandQueue];
    const char* path = gpu_path();
    MTLBinaryArchiveDescriptor* ad = [MTLBinaryArchiveDescriptor new];
    ad.url = [NSURL fileURLWithPath:@(path)];
    MTLComputePipelineDescriptor* d = gpu_desc();
    id<MTLBinaryArchive> ar = [gpu_dev newBinaryArchiveWithDescriptor:ad
      error:nil];
    gpu_pso = ar ? gpu_pipe(d, ar) : nil;
    if (!gpu_pso) {
      gpu_note(path);
      gpu_pso = gpu_pipe(d, nil);
    }
    if (!gpu_pso) {
      err_fail(ERR_FAIL, "cannot load the GPU program");
    }
  }
}

static void gpu_kernel(id<MTLComputeCommandEncoder> enc, u32 pass,
  u32 groups) {
  [enc setComputePipelineState:gpu_pso];
  [enc setBuffer:gpu_buf offset:0 atIndex:0];
  [enc setBytes:&pass length:sizeof pass atIndex:1];
  [enc setThreadgroupMemoryLength:TG_HOLD * 8 atIndex:0];
  [enc dispatchThreadgroups:MTLSizeMake(groups, 1, 1)
    threadsPerThreadgroup:MTLSizeMake(CUBE_SIDE, 1, 1)];
  [enc memoryBarrierWithScope:MTLBarrierScopeBuffers];
}

static void gpu_pass(u32 f) {
  @autoreleasepool {
    id<MTLCommandBuffer> cb = [gpu_que commandBuffer];
    id<MTLComputeCommandEncoder> enc = [cb computeCommandEncoder];
    if (f < CUBE_SIDE) {
      gpu_kernel(enc, 0, 1);
    }
    if (f < CUBE) {
      gpu_kernel(enc, 0, CUBE_SIDE);
    }
    gpu_kernel(enc, 1, CUBE_SIDE);
    [enc endEncoding];
    [cb commit];
    [cb waitUntilCompleted];
    if ([cb error]) {
      err_fail(ERR_FAIL, [[[cb error] localizedDescription] UTF8String]);
    }
  }
}

#elif BEND_CUDA

static bool gpu_probe(void) {
  int       managed = 0;
  CUcontext ctx;
  if (cuInit(0) == CUDA_SUCCESS && cuDeviceGet(&gpu_dev, 0) == CUDA_SUCCESS) {
    cuDeviceGetAttribute(&managed,
      CU_DEVICE_ATTRIBUTE_CONCURRENT_MANAGED_ACCESS, gpu_dev);
  }
  return managed != 0
    && cuDevicePrimaryCtxRetain(&ctx, gpu_dev) == CUDA_SUCCESS
    && cuCtxSetCurrent(ctx) == CUDA_SUCCESS;
}

static Corpus gpu_map(u64 bytes) {
  CUdeviceptr p = 0;
  if (cuMemAllocManaged(&p, bytes, CU_MEM_ATTACH_GLOBAL) != CUDA_SUCCESS) {
    err_fail(ERR_HEAP, "corpus reservation failed");
  }
  cuMemAdvise(p, bytes, CU_MEM_ADVISE_SET_PREFERRED_LOCATION, gpu_dev);
  return (Corpus)(uintptr_t)p;
}

static u64 gpu_hash(void) {
  u64 key = 14695981039346656037ull;
  for (const char* p = BEND_SRC; *p != 0; p += 1) {
    key = (key ^ (u8)*p) * 1099511628211ull;
  }
  return key;
}

static bool gpu_make(const char* path) {
  int cc[2] = {0, 0};
  cuDeviceGetAttribute(cc,
    CU_DEVICE_ATTRIBUTE_COMPUTE_CAPABILITY_MAJOR, gpu_dev);
  cuDeviceGetAttribute(cc + 1,
    CU_DEVICE_ATTRIBUTE_COMPUTE_CAPABILITY_MINOR, gpu_dev);
  char arch[40];
  snprintf(arch, sizeof arch, "--gpu-architecture=sm_%d%d", cc[0], cc[1]);
  const char* opts[] = { arch, "--fmad=false", "-default-device" };
  nvrtcProgram prog;
  if (nvrtcCreateProgram(&prog, BEND_SRC, "bend.cu", 0, NULL, NULL)
    != NVRTC_SUCCESS) {
    err_fail(ERR_FAIL, "cannot compile the CUDA library");
  }
  if (nvrtcCompileProgram(prog, 3, opts) != NVRTC_SUCCESS) {
    size_t n = 0;
    nvrtcGetProgramLogSize(prog, &n);
    char* log = calloc(n + 1, 1);
    if (log != NULL && nvrtcGetProgramLog(prog, log) == NVRTC_SUCCESS) {
      fprintf(stderr, "%s\n", log);
    }
    err_fail(ERR_FAIL, "cannot compile the CUDA library");
  }
  size_t len = 0;
  nvrtcGetCUBINSize(prog, &len);
  char* bin = malloc(len);
  if (bin == NULL || nvrtcGetCUBIN(prog, bin) != NVRTC_SUCCESS) {
    err_fail(ERR_FAIL, "cannot load the CUDA library");
  }
  nvrtcDestroyProgram(&prog);
  u64   key = gpu_hash();
  FILE* out = path == NULL ? NULL : fopen(path, "wb");
  bool  ok  = out != NULL && fwrite(&key, 8, 1, out) == 1
    && fwrite(bin, 1, len, out) == len && fclose(out) == 0;
  if (cuModuleLoadData(&gpu_lib, bin) != CUDA_SUCCESS) {
    err_fail(ERR_FAIL, "cannot load the CUDA library");
  }
  free(bin);
  return path == NULL || ok;
}

static u64 gpu_span(void) {
  size_t span = 0;
  cuDeviceTotalMem(&span, gpu_dev);
  return span;
}

static void gpu_load(u64 bytes) {
  const char* path = gpu_path();
  int         fd   = open(path, O_RDONLY);
  struct stat st   = { 0 };
  u64         key  = 0;
  char*       bin  = fd < 0 || fstat(fd, &st) != 0 || st.st_size <= 8 ? NULL
    : mmap(NULL, st.st_size, PROT_READ, MAP_PRIVATE, fd, 0);
  if (bin != NULL && bin != MAP_FAILED) {
    memcpy(&key, bin, 8);
  }
  if (key != gpu_hash()
    || cuModuleLoadData(&gpu_lib, bin + 8) != CUDA_SUCCESS) {
    gpu_note(path);
    gpu_make(path);
  }
  if (cuModuleGetFunction(&gpu_pso, gpu_lib, "bend_dev") != CUDA_SUCCESS) {
    err_fail(ERR_FAIL, "cannot load the GPU program");
  }
}

static void gpu_kernel(u32 pass, u32 groups) {
  void* args[] = { &CORPUS, &pass };
  if (cuLaunchKernel(gpu_pso, groups, 1, 1, CUBE_SIDE, 1, 1, TG_HOLD * 8, NULL,
    args, NULL) != CUDA_SUCCESS) {
    err_fail(ERR_FAIL, "device launch failed");
  }
}

static void gpu_pass(u32 f) {
  if (f < CUBE_SIDE) {
    gpu_kernel(0, 1);
  }
  if (f < CUBE) {
    gpu_kernel(0, CUBE_SIDE);
  }
  gpu_kernel(1, CUBE_SIDE);
  if (cuCtxSynchronize() != CUDA_SUCCESS) {
    err_fail(ERR_FAIL, "device fault");
  }
}

#else

#define gpu_probe() false
#define gpu_make(p) true
#define gpu_span()  0
#define gpu_load(b)
#define gpu_pass(f)

#endif

// Cube
// ====

static void cube_run(Corpus H, bool gpu) {
  for (;;) {
    u32 f = a32_load(a32_at(H, H_CURSOR));
    a32_store(a32_at(H, H_CURSOR), 0);
    if (root_done(H)) {
      return;
    }
    if (f == 0) {
      err_fail(ERR_LEAK, "frontier drained without a result");
    }
    if (gpu) {
      gpu_pass(f);
      for (Cls c = 0; c < NCLS_ALL; c += 1) {
        Bank* b = bank_at(H, c);
        u32   n = b->wr - b->top;
        memmove(H + b->off + b->rd, H + b->off + b->top, n * 8);
        b->rd = b->wr = b->top = b->rd + n;
      }
    } else {
      if (f < CUBE) {
        pool_turn(true);
      }
      pool_turn(false);
    }
    u32 ec = a32_load(a32_at(H, H_ERROR_CODE));
    if (ec != 0) {
      err_post(H, ec);
    }
  }
}

// Corpus
// ======

static Corpus corpus_setup(bool gpu, long threads, u64 bytes) {
  io_gpu     = gpu;
  KEEP_WORDS = gpu ? CHUNK : CAP_WORDS;
  u64 dflt   = gpu ? gpu_span() : 1ull << 43;
  CORPUS_SIZE = (gpu && bytes != 0 ? bytes : dflt) & ~16383ull;
  u64 span = CORPUS_SIZE / 8;
  u64 cap  = span > HEAP_OFF ? (span - HEAP_OFF) / (PAGE_LEN + 10) : 0;
  if (cap <= CUBE) {
    err_fail(ERR_HEAP,
      "--gpu-memory is under the rings, stacks and a page per lane");
  }
  cap = cap < ~0u ? cap : ~0u - 1;
  CORPUS = gpu ? gpu_map(CORPUS_SIZE) : pool_mmap(CORPUS_SIZE);
  Corpus H  = CORPUS;
#if BEND_CUDA
  if (gpu) {
    memset(H, 0, STAK_OFF * 8);
  }
#endif
  u64    at = HEAP_OFF + (cap << PAGE_BITS);
  for (u32 c = 0; c < NCLS_ALL; c += 1) {
    bank_at(H, c)->off = at;
    at += 2 * (cap >> ((c < NCLS ? NCLS : c) - PAGE_BITS));
  }
  a32_store(a32_at(H, H_BUMP), 1);
  a32_store(a32_at(H, H_CAP), (u32)cap);
  if (gpu) {
    gpu_load(CORPUS_SIZE);
  }
  pool_size = threads < 1 ? 1
    : threads < CUBE_SIDE ? threads : CUBE_SIDE;
  return H;
}

OUTLINE Term corpus_eval(Corpus H, Term t) {
  Env  e = { H, ALC[0] };
  Term rv[WL_RESW];
  for (;;) {
    Reply r = work_loop(e, io_stk, t, !BANGS);
    if (r == 0) {
      if (root_done(H)) {
        break;
      }
      err_fail(ERR_LEAK, "solo delivery lost");
    }
    if ((u32)H[task_tail(r) + 1] == 0) {
      t = r;
      if (io_gpu && fid_bangs((u32)term_aux(t))) {
        Loc  tl   = task_tail(t);
        Term cont = H[tl];
        u32  idx  = (u32)(H[tl + 1] >> 32) & 0xFFFF;
        H[tl]     = TERM_HOLE;
        a32_store(a32_at(H, H_CURSOR), 1);
        ring_push(H, 0, t);
        cube_run(H, true);
        Term p = task_deliver(H, cont, idx, rv, root_take(H, rv));
        if (root_done(H)) {
          break;
        }
        if (p == 0) {
          err_fail(ERR_LEAK, "seam delivery lost");
        }
        t = p;
      }
      continue;
    }
    task_deal(H, r, 0, 0, (Cursor)0);
    pool_open();
    cube_run(H, false);
    break;
  }
  root_take(H, rv);
  return rv[0];
}

// Io
// ==

#include <arpa/inet.h>
#include <errno.h>
#include <fcntl.h>
#include <netinet/in.h>
#include <sys/socket.h>

#define IO_ROWS 4096
#define IO_FILE 1
#define IO_TCPS 2
#define IO_UDPS 3
#define IO_LSNR 4
#define IO_CHAN 6
#define IO_READ 1
#define IO_TIME 2
#define IO_PARK TERM_HOLE
#define IO_WORK (TERM_HOLE - 1)

// IoHand ::=
//   | IoHand(slot, mint)
typedef struct {
  u32 slot;
  u32 mint;
} IoHand;

// IoFall ::=
//   | IoFall(code, text)
typedef struct {
  u32         code;
  const char* text;
} IoFall;

// IoRow ::=
//   | IoRow(mint, file, kind)
typedef struct {
  u32      mint;
  intptr_t file;
  int      kind;
} IoRow;

struct IoWork;
typedef void (*IoCall)(struct IoWork* w);
typedef Term (*IoPack)(Env e, struct IoWork* w);

// IoWork ::=
//   | IoWork(hand, made, word, size, data, text, fall, call, pack)
typedef struct IoWork {
  IoHand   hand;
  IoHand   made;
  u32      word;
  u64      size;
  char*    data;
  char*    text;
  IoFall   fall;
  IoCall   call;
  IoPack   pack;
} IoWork;

typedef Term (*Effect)(Env e, Term* f, IoWork* w);

// IoEff ::=
//   | IoEff(run, ask)
typedef struct {
  Effect run;
  u32    ask;
} IoEff;

static IoRow io_sys_rows[IO_ROWS];
static u32   io_sys_next;
static u32   io_sys_free = IO_ROWS;
static lock  io_sys_lock = PTHREAD_MUTEX_INITIALIZER;
static IoEff io_eff_rows[1 << 16];
static u32   io_live;

static u64 io_tick(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (u64)ts.tv_sec * 1000000000ull + (u64)ts.tv_nsec;
}

OUTLINE void* io_mem(void* mem) {
  if (mem == NULL) {
    err_fail(ERR_HEAP, "host allocation failed");
  }
  return mem;
}

static IoFall io_sys_fall(u32 code) {
  IoFall out = { code, NULL };
  return out;
}

static int io_sys_mint(int kind, intptr_t fd, IoHand* out) {
  pthread_mutex_lock(&io_sys_lock);
  u32 slot = io_sys_free < IO_ROWS ? io_sys_free : io_sys_next;
  if (slot < IO_ROWS) {
    IoRow* row  = &io_sys_rows[slot];
    io_sys_free = slot == io_sys_free ? (u32)row->file : io_sys_free;
    io_sys_next += slot == io_sys_next;
    row->mint  += 1;
    row->file   = fd;
    row->kind   = kind;
    out->slot   = slot;
    out->mint   = row->mint;
  }
  pthread_mutex_unlock(&io_sys_lock);
  return slot < IO_ROWS ? 0 : -1;
}

#define io_sys_read(h, k) io_sys_take(h, k, false)
#define io_sys_kill(h)    io_sys_take(h, 0, true)

static intptr_t io_sys_take(IoHand hand, int kind, bool kill) {
  pthread_mutex_lock(&io_sys_lock);
  IoRow*   row = hand.slot < IO_ROWS ? &io_sys_rows[hand.slot] : NULL;
  bool     hit = row != NULL && row->mint == hand.mint && row->kind != 0
    && (kind == 0 || row->kind == kind);
  intptr_t fd  = hit ? row->file : -1;
  if (hit && kill) {
    row->file   = io_sys_free;
    row->kind   = 0;
    io_sys_free = hand.slot;
  }
  pthread_mutex_unlock(&io_sys_lock);
  return fd;
}

static int io_sys_addr(const char* host, u32 port, struct sockaddr_in* at) {
  memset(at, 0, sizeof(*at));
  at->sin_family = AF_INET;
  at->sin_port   = htons((uint16_t)port);
  for (const char* p = host; *p != 0; p += 1) {
    bool zero = *p == '0' && p[1] >= '0' && p[1] <= '9';
    if ((p == host || p[-1] == '.') && zero) {
      return -1;
    }
  }
  return port > 65535 || inet_pton(AF_INET, host, &at->sin_addr) != 1
    ? -1 : 0;
}

static void io_eff(u32 fid, u32 cid, Effect run, u32 need) {
  IoEff row = { run, need };
  io_eff_rows[cid] = row;
}

static Term io_work(IoWork* w, IoCall call, IoPack pack) {
  w->call = call;
  w->pack = pack;
  return IO_WORK;
}

static u64 io_sys_end(IoWork* w, ssize_t n) {
  w->fall = io_sys_fall(n < 0 ? (u32)errno : 0);
  return n < 0 ? 0 : (u64)n;
}

static void io_sys_keep(IoWork* w, int kind, int fd) {
  io_sys_end(w, fd);
  if (fd >= 0 && io_sys_mint(kind, fd, &w->made) < 0) {
    close(fd);
    w->fall = io_sys_fall(EMFILE);
  }
}

// IoRun ::=
//   | IoRun(cont, item, next)
typedef struct IoRun {
  Term          cont;
  Term          item;
  struct IoRun* next;
} IoRun;

static IoRun*  io_runs;
static IoRun** io_runs_at = &io_runs;

static IoRun* io_cell(Term cont, Term item) {
  IoRun* r = io_mem(malloc(sizeof(IoRun)));
  r->cont = cont;
  r->item = item;
  r->next = NULL;
  return r;
}

static void io_push(Term op, Term x, bool fresh) {
  IoRun* r = io_cell(op, x);
  *io_runs_at = r;
  io_runs_at  = &r->next;
  io_live    += fresh;
}

OUTLINE void io_out(FILE* h, const char* data, u64 len) {
  if (fwrite(data, 1, len, h) != len) {
    err_fail(ERR_FAIL, "a short write on a standard stream");
  }
}

OUTLINE void io_sync(void) {
  if (fflush(stdout) != 0) {
    err_fail(ERR_FAIL, "a short write on a standard stream");
  }
}

// the edge is UTF-8
OUTLINE char* io_cstr(Env e, Term s, u64* len) {
  u64   cap = 64;
  u64   n   = 0;
  char* buf = io_mem(malloc(cap));
  while (term_aux(s) == CID_SCON) {
    Term fb[2];
    spare_free(e, cls_fit(2), ctr_take(e, s, 2, fb));
    u64 c = fb[0];
    u64 k = c < 0x80 ? 1 : c < 0x800 ? 2 : c < 0x10000 ? 3 : 4;
    if (n + k + 1 > cap) {
      cap *= 2;
      buf = io_mem(realloc(buf, cap));
    }
    for (u64 i = k; i > 1; i -= 1) {
      buf[n + i - 1] = (char)(0x80 | (c & 0x3F));
      c >>= 6;
    }
    buf[n] = (char)(k == 1 ? c : (0xF00 >> k) | c);
    n += k;
    s = fb[1];
  }
  buf[n] = 0;
  *len = n;
  return buf;
}

OUTLINE void io_errs(Env e, Term s) {
  u64   n    = 0;
  char* text = io_cstr(e, s, &n);
  io_sync();
  io_out(stderr, text, n);
  io_out(stderr, "\n", 1);
  free(text);
}

#define io_nul(s, n) (strlen(s) != (n))

#define io_seal(e, t, hot) ((hot) != 0 ? rfc_seal(e, t) : (t))

static Term io_node(Env e, u64 cid, Term a, Term b, int hot) {
  Loc l = heap_alloc(e, 1);
  e.mem[l]     = io_seal(e, a, hot);
  e.mem[l + 1] = io_seal(e, b, hot);
  return term_ctr(cid, l);
}

static Term io_str(Env e, const char* p, u64 n) {
  Term s = term_pak(CID_SNIL, 0);
  while (n > 0) {
    u64 k = 0;
    while (k < 3 && k + 1 < n && ((uint8_t)p[n - 1 - k] & 0xC0) == 0x80) {
      k += 1;
    }
    u64 b   = (uint8_t)p[n - 1 - k];
    u64 len = b < 0xC0 ? 0 : b < 0xE0 ? 2 : b < 0xF0 ? 3 : 4;
    u64 c   = (uint8_t)p[n - 1];
    if (len == k + 1) {
      c = b & (0x7F >> len);
      for (u64 i = 1; i < len; i += 1) {
        c = (c << 6) | ((uint8_t)p[n - len + i] & 0x3F);
      }
    } else {
      len = 1;
    }
    n -= len;
    s = io_node(e, CID_SCON, c, s, IO_HOTS & 1);
  }
  return s;
}

#define io_tup(e, a, b)     io_node(e, CID_TUPLE, a, b, IO_HOTS & 2)
#define io_hand(e, cid, h)  io_node(e, cid, (h).slot, (h).mint, 0)
#define io_done(e, v)       io_box(e, CID_DONE, v, IO_HOTS & 4)

static Term io_box(Env e, u64 cid, Term v, int hot) {
  Loc l = heap_alloc(e, 0);
  e.mem[l] = io_seal(e, v, hot);
  return term_ctr(cid, l);
}

static Term io_fail(Env e, IoFall q) {
  const char* s = q.text != NULL ? q.text : strerror((int)q.code);
  Term t = io_tup(e, (u64)q.code, io_str(e, s, strlen(s)));
  return io_box(e, CID_FAIL, t, IO_HOTS & 8);
}

static IoHand io_hand_p(Env e, Term t) {
  Loc at = term_peek(e, t);
  IoHand h = { (u32)e.mem[at], (u32)e.mem[at + 1] };
  return h;
}

static IoHand io_hand_c(Env e, Term t) {
  IoHand h = io_hand_p(e, t);
  term_drop(e, t);
  return h;
}

// IoJob ::=
//   | IoJob(word, req, time, next, work)
typedef struct IoJob {
  u32           word;
  Term          req;
  u64           time;
  struct IoJob* next;
  IoWork        work;
} IoJob;

static IoJob*         io_park;
static IoJob**        io_park_at = &io_park;
static IoJob*         io_jobs;
static IoJob**        io_jobs_at = &io_jobs;
static lock           io_gate = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t io_bell = PTHREAD_COND_INITIALIZER;
static u32            io_busy;
static u32            io_size;
static int            io_wake_fd[2];

static void io_take(Env e) {
  IoJob*  jobs[64];
  ssize_t n;
  while ((n = read(io_wake_fd[0], jobs, sizeof jobs)) > 0) {
    for (u32 i = 0; i < (u32)n / sizeof(IoJob*); i += 1) {
      io_push(jobs[i]->req, jobs[i]->work.pack(e, &jobs[i]->work), false);
      io_busy -= 1;
      free(jobs[i]);
    }
  }
}

static void* io_help(void* arg) {
  for (;;) {
    pthread_mutex_lock(&io_gate);
    while (io_jobs == NULL) {
      pthread_cond_wait(&io_bell, &io_gate);
    }
    IoJob* job = io_jobs;
    io_jobs    = job->next;
    io_jobs_at = io_jobs == NULL ? &io_jobs : io_jobs_at;
    pthread_mutex_unlock(&io_gate);
    job->work.call(&job->work);
    while (write(io_wake_fd[1], &job, sizeof job) != sizeof job) {
    }
  }
}

static void io_send(IoJob* job) {
  io_busy += 1;
  if (io_busy > io_size && io_size < IO_HELP) {
    pthread_t tid;
    if (pthread_create(&tid, NULL, io_help, NULL)) {
      err_fail(ERR_FAIL, "pthread_create");
    }
    pthread_detach(tid);
    io_size += 1;
  }
  job->next = NULL;
  pthread_mutex_lock(&io_gate);
  *io_jobs_at = job;
  io_jobs_at  = &job->next;
  pthread_cond_signal(&io_bell);
  pthread_mutex_unlock(&io_gate);
}

// Runs the request of job: the effect takes its fields (the node goes)
// and answers a value, IO_PARK (it parked the continuation) or IO_WORK
// (a helper takes the job); else the job goes and *k is the continuation.
static Term io_exec(Env e, IoJob* job, Term* k) {
  Term fs[256];
  u32  c = (u32)term_aux(job->req);
  u32  n = cid_arity(c);
  spare_free(e, cls_fit(n), ctr_take(e, job->req, n, fs));
  Term x = io_eff_rows[c].run(e, fs, &job->work);
  *k = fs[n - 1];
  if (x == IO_WORK) {
    job->req = *k;
    io_send(job);
  } else {
    free(job);
  }
  return x;
}

static void io_wait(Env e) {
  struct pollfd fds[IO_ROWS + 1];
  u32 n    = 1;
  u64 soon = 0;
  int ms   = -1;
  fds[0].fd     = io_wake_fd[0];
  fds[0].events = POLLIN;
  for (IoJob* j = io_park; j != NULL; j = j->next) {
    if (j->time != 0) {
      soon = soon == 0 || j->time < soon ? j->time : soon;
    } else if (n > IO_ROWS) {
      err_fail(ERR_FAIL, "more waits than handles");
    } else {
      fds[n].fd     = (int)j->word;
      fds[n].events = POLLIN;
      n += 1;
    }
  }
  if (soon != 0) {
    u64 now = io_tick();
    u64 gap = soon > now ? (soon - now) / 1000000 + 1 : 0;
    ms = gap > 0x7fffffff ? 0x7fffffff : (int)gap;
  }
  io_sync();
  while (poll(fds, n, ms) < 0) {
    if (errno != EINTR) {
      err_fail(ERR_FAIL, "the poller failed");
    }
  }
  if (fds[0].revents != 0) {
    io_take(e);
  }
  u64     now = io_tick();
  u32     i   = 1;
  IoJob** at  = &io_park;
  while (*at != NULL) {
    IoJob* j   = *at;
    IoJob* nx  = j->next;
    bool   due = j->time == 0 ? fds[i].revents != 0 : j->time <= now;
    i += j->time == 0;
    if (due) {
      *at = nx;
      Term k;
      Term x = io_exec(e, j, &k);
      if (x != IO_WORK && x != IO_PARK) {
        io_push(k, x, false);
      }
    } else {
      at = &j->next;
    }
  }
  io_park_at = at;
}

// Applies the continuation k to x: a request.
static Term io_apply(Env e, Term k, Term x) {
  Loc a = task_node(e, FID_CLO_APPLY, TERM_HOLE, 0, 0);
  e.mem[a]     = k;
  e.mem[a + 1] = x;
  return corpus_eval(e.mem, term_tsk(FID_CLO_APPLY, a));
}

static int io_step(Env e, Term k, Term x) {
  for (;;) {
    Term req = io_apply(e, k, x);
    u32  c   = (u32)term_aux(req);
    Loc  at  = term_peek(e, req);
    if (c == CID_EMIT) {
      term_drop(e, req);
      io_live -= 1;
      return -1;
    }
    if (c == CID_HALT) {
      io_errs(e, e.mem[at + 1]);
      return (int)(u32)e.mem[at];
    }
    if (io_eff_rows[c].run == NULL) {
      err_fail(ERR_FIDS, "an alien request");
    }
    IoJob* job = io_mem(calloc(1, sizeof(IoJob)));
    u32    need = io_eff_rows[c].ask;
    job->req    = req;
    job->word   = (u32)e.mem[at];
    if (need & IO_READ) {
      job->word = (u32)io_sys_read(io_hand_p(e, e.mem[at]), 0);
      need = (int)job->word < 0 ? 0 : need;
    }
    if (need != 0) {
      job->time = need & IO_TIME ? io_tick() + (u64)job->word * 1000000ull : 0;
      *io_park_at = job;
      io_park_at  = &job->next;
      return -1;
    }
    x = io_exec(e, job, &k);
    if (x == IO_WORK || x == IO_PARK) {
      return -1;
    }
  }
}

OUTLINE int io_loop(Corpus H, Fid fid) {
  Env e = { H, ALC[0] };
  io_stk = pool_stack();
  signal(SIGPIPE, SIG_IGN);
  if (pipe(io_wake_fd) | fcntl(io_wake_fd[0], F_SETFL, O_NONBLOCK)) {
    err_fail(ERR_FAIL, "the event loop failed to open");
  }
  Term m = corpus_eval(H, term_tsk(fid, task_node(e, fid, TERM_HOLE, 0, 0)));
  io_push(m, term_clo(FID_IO_EMIT, 0), true);
  for (u32 n = 0;; n += 1) {
    if (io_runs == NULL) {
      if (io_live == 0) {
        return 0;
      }
      if (io_park == NULL && io_busy == 0) {
        io_sync();
        fprintf(stderr, "bend: deadlock: every computation waits on a"
          " channel\n");
        return 1;
      }
      io_wait(e);
      continue;
    }
    if ((n & 63) == 0 && io_busy != 0) {
      io_take(e);
    }
    IoRun* r   = io_runs;
    io_runs    = r->next;
    io_runs_at = io_runs == NULL ? &io_runs : io_runs_at;
    int code   = io_step(e, r->cont, r->item);
    free(r);
    if (code >= 0) {
      return code;
    }
  }
}

${NATIVE.IO}
// Chan
// ====

// ChanRow ::=
//   | ChanRow(room, size, head, shut, ring, wait, last)
typedef struct {
  u32    room;
  u32    size;
  u32    head;
  u32    shut;
  Term*  ring;
  IoRun* wait;
  IoRun* last;
} ChanRow;

#define chan_some(e, v) io_box(e, CID_SOME, v, IO_HOTS & 32)
#define chan_bool(b)    term_pak((b) ? CID_TRUE : CID_FALSE, 0)

static ChanRow* chan_at(IoHand h) {
  intptr_t row = io_sys_read(h, IO_CHAN);
  return row < 0 ? NULL : (ChanRow*)row;
}

static void chan_park(ChanRow* row, Term cont, Term item) {
  IoRun* w = io_cell(cont, item);
  if (row->wait == NULL) {
    row->wait = w;
  } else {
    row->last->next = w;
  }
  row->last = w;
}

static Term chan_wake(ChanRow* row, Term x) {
  IoRun* w = row->wait;
  Term item = w->item;
  row->wait = w->next;
  io_push(w->cont, x, false);
  free(w);
  return item;
}

static Term chan_take(ChanRow* row) {
  Term v = row->ring[row->head];
  row->head = (row->head + 1) % row->room;
  row->size -= 1;
  if (row->wait != NULL) {
    Term item = chan_wake(row, chan_bool(true));
    row->ring[(row->head + row->size) % row->room] = item;
    row->size += 1;
  }
  return v;
}

static void chan_free(IoHand h, ChanRow* row) {
  free(row->ring);
  free(row);
  io_sys_kill(h);
}

static void chan_shut(Env e, IoHand h, ChanRow* row) {
  row->shut = 1;
  while (row->wait != NULL) {
    bool rcv = row->wait->item == TERM_HOLE;
    Term x = rcv ? term_pak(CID_NONE, 0) : chan_bool(false);
    term_sink(e, chan_wake(row, x));
  }
  if (row->size == 0) {
    chan_free(h, row);
  }
}

// Requests
// ========

// Cli
// ===

static void cli_fail(const char* msg, const char* arg) {
  fprintf(stderr, "bend: %s%s\n", msg, arg != NULL ? arg : "");
  exit(1);
}

static bool cli_flag(const char* name, const char* val) {
  bool on = val != NULL && strcmp(val, "on") == 0;
  if (!on && (val == NULL || strcmp(val, "off") != 0)) {
    cli_fail("expected 'on' or 'off' after ", name);
  }
  return on;
}

// Main
// ====

int main(int argc, char** argv) {
  long thr  = 0;
  int  par  = -1;
  int  gpu  = -1;
  u64  mem  = 0;
  for (int i = 1; i < argc; i += 1) {
    const char* a = argv[i];
    const char* v = i + 1 < argc ? argv[i + 1] : NULL;
    i += 1;
    if (strcmp(a, "--help") == 0) {
      printf(CLI_HELP, argv[0]);
      return 0;
    } else if (strcmp(a, "--gpu-build") == 0) {
      if (gpu_probe() && !gpu_make(gpu_path())) {
        cli_fail("cannot write ", gpu_path());
      }
      return 0;
    } else if (strcmp(a, "--threads") == 0) {
      char* end = NULL;
      thr = v != NULL ? strtol(v, &end, 10) : 0;
      if (thr < 1 || end == NULL || *end != '\0') {
        cli_fail("expected a thread count of 1 or more after --threads", NULL);
      }
    } else if (strcmp(a, "--parallel") == 0) {
      par = cli_flag("--parallel", v);
    } else if (strcmp(a, "--gpu") == 0) {
      gpu = cli_flag("--gpu", v);
    } else if (strcmp(a, "--gpu-memory") == 0) {
      char*  end = NULL;
      double n   = v != NULL ? strtod(v, &end) : 0;
      u64    mul = end == NULL ? 0 : strcmp(end, "GB") == 0 ? 1ull << 30
        : strcmp(end, "MB") == 0 ? 1ull << 20 : 0;
      if (mul == 0 || n <= 0) {
        cli_fail("expected a size like 4GB or 512MB after ", "--gpu-memory");
      }
      mem = (u64)(n * (double)mul);
    } else {
      cli_fail("unknown option ", a);
    }
  }
  if (par == 0) {
    if (gpu == 1 || thr > 1) {
      cli_fail("--parallel off means --threads 1 with --gpu off", NULL);
    }
    thr = 1;
    gpu = 0;
  }
  bool dev = gpu != 0 && BANGS != 0 && gpu_probe();
  if (gpu == 1 && BANGS != 0 && !dev) {
    cli_fail("--gpu on, but this binary found no GPU device", NULL);
  }
  long ncpu = sysconf(_SC_NPROCESSORS_ONLN);
  Corpus H  = corpus_setup(dev, thr > 0 ? thr : ncpu, mem);
  int code  = io_loop(H, MAIN_FID);
  io_sync();
  return code;
}

#endif
`.slice(1);

// RuntimeJs
// =========

const RUNTIME: string = String.raw`
${NATIVE.JS}
// Array
// =====

function array_len(a) {
  let n = 1;
  for (let x = a; x.$ === "ANode"; x = x.xs) {
    n *= 2;
  }
  return n;
}

function array_get(a, i) {
  let n = array_len(a);
  i = (i >>> 0) % n;
  let x = a;
  while (x.$ === "ANode") {
    n /= 2;
    if (i < n) {
      x = x.xs;
    } else {
      x = x.ys;
      i -= n;
    }
  }
  return {$: "Tuple", fst: a, snd: x.value};
}

function array_new(d, v) {
  if (d > 31n) {
    throw "bend: ${ERRS[10]}";
  }
  let a = {$: "ALeaf", value: v};
  for (let j = 0n; j < d; j += 1n) {
    a = {$: "ANode", xs: a, ys: a};
  }
  return a;
}

function array_swap_go(a, n, i, v) {
  if (a.$ === "ALeaf") {
    return {$: "Tuple", fst: {$: "ALeaf", value: v}, snd: a.value};
  }
  n /= 2;
  if (i < n) {
    const r = array_swap_go(a.xs, n, i, v);
    return {$: "Tuple", fst: {$: "ANode", xs: r.fst, ys: a.ys}, snd: r.snd};
  }
  const r = array_swap_go(a.ys, n, i - n, v);
  return {$: "Tuple", fst: {$: "ANode", xs: a.xs, ys: r.fst}, snd: r.snd};
}

function array_swap(a, i, v) {
  const n = array_len(a);
  return array_swap_go(a, n, (i >>> 0) % n, v);
}

// Run
// ===

function run_jump(f, x) {
  return {$: "$JMP", f: f, x: x};
}

function run_tail(f, x) {
  return {$: "$JMP", f: f.j?.f === f ? f.j : f, x: [x]};
}

function run_clo(j) {
  const f = (x) => run_loop(j(x));
  f.j = j;
  j.f = f;
  return f;
}

function run_loop(r) {
  while (r !== null && typeof r === "object" && r.$ === "$JMP") {
    r = r.f(...r.x);
  }
  return r;
}

function run_lib(f, n) {
  return (...a) => a.length < n ? run_lib((...b) => f(...a, ...b), n - a.length)
    : run_loop(f(...a));
}
`.slice(1);

const RUNTIME_MAIN: string = String.raw`
// Cli
// ===

function cli_fail(msg) {
  io_errs("bend: " + msg);
  process.exit(1);
}

// A JS program runs one thread and no GPU: it takes no argument.
function cli(argv) {
  if (argv[0] === "--help") {
    io_out(1, io_bytes("usage: " + process.argv[1] + "\n"));
    process.exit(0);
  }
  if (argv.length > 0) {
    cli_fail("unknown option " + argv[0] + " (a JS program runs one thread"
      + " and no GPU)");
  }
}

// Io
// ==

function io_exit(main) {
  try {
    process.exit(io_run(main));
  } catch (e) {
    io_errs(String(e));
    process.exit(1);
  }
}

function io_out(fd, data) {
  const fs = require("fs");
  let at = 0;
  while (at < data.length) {
    try {
      at += fs.writeSync(fd, data, at, data.length - at);
    } catch (e) {
      if (e.code === "EAGAIN" || e.code === "EINTR") {
        continue;
      }
      try {
        fs.writeSync(2, "bend: a short write on a standard stream\n");
      } catch (o) {
      }
      process.exit(1);
    }
  }
}

function io_errs(message) {
  io_out(2, io_bytes(message + "\n"));
}

function io_sys() {
  if (globalThis.BEND_SYS === undefined) {
    const ffi = require("bun:ffi");
    const mac = process.platform === "darwin";
    const err = mac ? "__error" : "__errno_location";
    const T = { i: "i32", u: "u32", U: "u64", I: "i64", p: "ptr",
      c: "cstring" };
    const lib = ffi.dlopen(mac ? "libSystem.dylib" : "libc.so.6",
      Object.fromEntries(("socket:iii>i bind:ipu>i listen:ii>i connect:ipu>i"
        + " accept:ipp>i send:ipUi>I recv:ipUi>I read:ipU>I sendto:ipUipu>I"
        + " recvfrom:ipUipp>I close:i>i poll:pui>i setsockopt:iiipu>i"
        + " strerror:i>c getenv:p>p " + err + ":>p").split(" ").map((s) => {
        const [name, args, ret] = s.split(/[:>]/);
        return [name, { args: [...args].map((a) => T[a]), returns: T[ret] }];
      })));
    globalThis.BEND_SYS = { ...lib.symbols, ptr: ffi.ptr, mac,
      errno: () => ffi.read.i32(lib.symbols[err](), 0) };
  }
  return globalThis.BEND_SYS;
}

function io_fail(code) {
  const text = String(io_sys().strerror(code));
  return { $: "Fail", error: io_tup(code >>> 0, text) };
}

function io_done(value) {
  return { $: "Done", value };
}

function io_tup(...xs) {
  return xs.reduceRight((snd, fst) => ({ $: "Tuple", fst: fst, snd: snd }));
}

function io_bytes(text) {
  return new TextEncoder().encode(text);
}

function io_text(b, n) {
  return new TextDecoder().decode(b.subarray(0, n));
}

function io_row(handle, kind) {
  const row = globalThis.BEND_IO.rows[Number(handle.slot)];
  const hit = row !== undefined && row.gen === Number(handle.gen)
    && row.fd !== null && (kind === undefined || kind.includes(row.kind));
  return hit ? row : null;
}

function io_mint(ctr, kind, fd) {
  const io = globalThis.BEND_IO;
  const slot = io.free.length > 0 ? io.free.pop() : io.rows.length;
  if (slot === 4096) {
    return null;
  }
  const gen = ((io.rows[slot]?.gen ?? 0) + 1) >>> 0;
  io.rows[slot] = { gen, kind, fd };
  return { $: ctr, slot, gen };
}

function io_read(handle, kind) {
  return io_row(handle, kind)?.fd ?? null;
}

function io_kill(handle) {
  const row = io_row(handle);
  if (row === null) {
    return null;
  }
  const fd = row.fd;
  row.fd = null;
  globalThis.BEND_IO.free.push(Number(handle.slot));
  return fd;
}

function io_poll(polls, ms) {
  const sys = io_sys();
  const buf = Int32Array.from(polls.flatMap((w) => [w.fd, 1]));
  const n = sys.poll(sys.ptr(buf), polls.length, ms);
  return polls.filter((w, i) => n > 0 && (buf[2 * i + 1] >>> 16) !== 0);
}

function io_addr(host, port) {
  const part = host.split(".");
  const deci = (p) => /^(0|[1-9]\d{0,2})$/.test(p) && Number(p) < 256;
  if (port > 65535 || part.length !== 4 || !part.every(deci)) {
    return null;
  }
  const b = new Uint8Array(16);
  const head = io_sys().mac ? [16, 2] : [2, 0];
  b.set([...head, port >> 8, port & 255, ...part.map(Number)]);
  return b;
}

function io_push(fun, arg, fresh) {
  const io = globalThis.BEND_IO;
  io.runs.push({ fun: fun, arg: arg });
  io.live += fresh ? 1 : 0;
}

function io_wait(io) {
  const soon = io.waits.reduce((m, w) => Math.min(m, w.at ?? m), Infinity);
  let ms = -1;
  if (soon !== Infinity) {
    ms = Math.ceil(soon - performance.now());
    ms = Math.min(Math.max(0, ms), 2147483647);
  }
  const fds = io.waits.filter((w) => w.fd !== undefined);
  const ready = fds.length === 0 ? [] : io_poll(fds, ms);
  if (fds.length === 0) {
    Bun.sleepSync(ms);
  }
  const now = performance.now();
  const fire = io.waits.filter((w) => ready.includes(w) || w.at <= now);
  io.waits = io.waits.filter((w) => !fire.includes(w));
  for (const w of fire) {
    io_push((o) => o.kont(o.run(...o.args, o.kont)), w.op, false);
  }
}

function io_run(m) {
  const io = { runs: [], live: 0, waits: [], rows: [], free: [] };
  globalThis.BEND_IO = io;
  try {
    io_push(run_loop(m()), (x) => ({ $: "Emit", value: x }), true);
    for (;;) {
      if (io.runs.length === 0) {
        if (io.live === 0) {
          return 0;
        }
        if (io.waits.length === 0) {
          io_errs("bend: deadlock: every computation waits on a channel");
          return 1;
        }
        io_wait(io);
        continue;
      }
      const s = io.runs.shift();
      let op = s.fun(s.arg);
      for (;;) {
        if (op.$ === "Emit") {
          io.live -= 1;
          break;
        }
        if (op.$ === "Halt") {
          io_errs(op.message);
          return op.code;
        }
        const need = op.need?.() ?? {};
        const fd = need.read === undefined ? null
          : io_read(op.args[0], need.read);
        if (need.time || fd !== null) {
          io.waits.push(fd === null
            ? { at: performance.now() + Number(op.args[0]), op: op }
            : { fd: fd, op: op });
          break;
        }
        const x = op.run(...op.args, op.kont);
        if (x === undefined) {
          break;
        }
        op = op.kont(x);
      }
    }
  } catch (req) {
    if (req instanceof RangeError) {
      throw "bend: ${ERRS[9]}";
    }
    if (req?.$ !== "$FFI") {
      throw req;
    }
    io_errs("bend: ${ERRS[3]}");
    return 1;
  }
}

// Chan
// ====

function chan_wake(row, x) {
  const w = row.wait.shift();
  io_push(w.cont, x, false);
  return w.item;
}

function chan_take(row) {
  const v = row.ring.shift();
  if (row.wait.length > 0) {
    row.ring.push(chan_wake(row, true));
  }
  return v;
}

function chan_shut(handle, row) {
  row.shut = true;
  while (row.wait.length > 0) {
    chan_wake(row, row.wait[0].item === null ? { $: "None" } : false);
  }
  if (row.ring.length === 0) {
    io_kill(handle);
  }
}
`.slice(1);

const TAB_BAD = /\b(?!(?:fround|imul|Number|BigInt)\()\w+\(/;
