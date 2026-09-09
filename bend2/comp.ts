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

type Cell = { arr: string; at: string };

type Val = { ws: string[]; lay: Lay; av?: (Cell | null)[] };

type Bind = { val: Val; n: number };

type Dst = Val | null;

type Seg = {
  fid: string;
  def: Bend.Name;
  lines: string[];
  params: string[];
  ks: Kind[];
  frame: { pop: number; resw: number; at: number[] } | null;
  refs: Set<string>;
  dead?: boolean;
  host?: boolean;
  spin?: boolean;
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

type Capture = { p: Probe; q: Bend.Quant; A: HTerm | null };

type Carb = {
  src: Record<Bend.Name, TLD>;
  book: Book;
  mint: Map<Bend.Name, boolean>;
  dyn: Set<Bend.Name>;
  kof: Map<Bend.Name, Bend.Name[]>;
  kept: Map<Bend.Name, Capture[]>;
  forks: Map<Probe, Bend.Name>;
  slots: Map<Bend.Name, { L: Capture[]; last: boolean }>;
  home: Map<Bend.Name, Bend.Name>;
  owner: Bend.Name[];
  kn: number;
  done: Set<Bend.Name>;
  queue: Bend.Name[];
  bangs: Set<Bend.Name>;
  sites: Map<Bend.Name, number>;
  brw: Map<Bend.Name, boolean[]>;
  live: Map<Bend.Name, boolean[][]>;
  hot: Set<Bend.Name>;
  poly: Set<string>;
  own: Map<string, string>;
};

type File = Carb & {
  spares: { words: number; name: string; z: boolean }[];
  fresh: Map<string, number>;
  uses: Map<Probe, Bind>;
  local: Set<string>;
  brwl: Set<string>;
  segs: Seg[];
  seg: Seg;
  tab: number;
  decl: string;
  cids: Map<string, [number, number]>;
  tabs: Map<string, number>;
  spins: [string, string, Set<string>][];
  spun: Map<string, string>;
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

type Open = (env: Map<HTerm, HTerm>) => HTerm;

type Kont = (caps: Capture[], x: Open) => Open;

type Root = [Bend.Name, number];

type Slot = { p: number; at: number; lay: Lay; root: Root | null } | null;

type Intr = {
  C?: Gen;
  parts?: string[];
  call?: boolean;
  JS: Gen;
};

type Dom = [Bend.Quant, Bend.Name, HTerm];

type Show = {
  book: Bend.Book;
  pre: string;
  ns: string;
  defs: Map<string, string>;
  src: string[];
};

// Constants
// =========

const CLO_APPLY = "Clo.apply";

const ATOM   = /^(?:[A-Za-z_$][A-Za-z0-9_$]*|\d+n?|\d+\.\d+)$/;
const STRLIT = new RegExp("^\"(?:[^\"\\\\]|\\\\.)*\"$");

const NATIVE_DIE = " does not match the native format of its type";

const EXACT = " sqrt exp log log2 log10 sin cos tan pow fmod ";

const USE0 = Bend.Emp<number>();

const EMPTY = new Map<HTerm, HTerm>();

const W32: Lay = { ks: ["w32"], arms: null };

const BOX: Lay = { ks: ["box"], arms: null };

const W64: Lay = { ks: ["w64"], arms: null };

const WORDS: Record<string, Lay> = { U32: W32, F32: W32, Nat: W64 };

const SHOWN: Record<string, (st: Show) => string> = {
  Nat: (st) => show_once(st, st.pre + ".nat", () => {
    show_def(st, st.pre + ".nat", "(x: Nat) -> String",
      [`Nat.show(x) ++ "n"`]);
  }),
  U32: show_u32,
  F32: (st) => show_once(st, st.pre + ".f32", () => {
    show_def(st, st.pre + ".f32", "(x: F32) -> String",
      [`"F32{" ++ ${show_word(st)}(32n, F32.bits(x)) ++ "}"`]);
  }),
  Char: show_chr,
  String: show_str,
};

const ERRS = ["", "runtime fail-stop", "runtime fail-stop",
  "runtime fail-stop", "out of memory: run again with a bigger span, as in"
  + " --gpu-memory 8GB", "a host call on the device", "runtime fail-stop",
  "a Nat past the largest immediate 2^48-1", "runtime fail-stop",
  "memory fault (machine stack overflow?)",
  "an array past the deepest block class 31"];

// Operations
// ----------

const CMPS = "is_eq:==:=== is_ne:!=:!== is_lt:< is_le:<= is_gt:> is_ge:>=";

export const OPERATIONS: Record<string, Intr> = Object.setPrototypeOf({
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
  u32_shln: {
    C:  "($1 >= 32 ? 0 : U32_BIN($0, <<, $1))",
    JS: "($1 >= 32n ? 0 : ($0 << Number($1)) >>> 0)",
  },
  u32_shrn: {
    C:  "($1 >= 32 ? 0 : U32_BIN($0, >>, $1))",
    JS: "($1 >= 32n ? 0 : $0 >>> Number($1))",
  },
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
    + " sinh cosh tanh floor ceil trunc",
    "f32_rewrap((f32)$k(f32_unbox($0)))", "Math.fround(Math.$k($0))"),
  ...tpl_ops("f32_", "pow atan2",
    "f32_rewrap((f32)$k(f32_unbox($0), f32_unbox($1)))",
    "Math.fround(Math.$k($0, $1))"),
  f32_abs: {
    C:  "f32_rewrap((f32)fabs(f32_unbox($0)))",
    JS: "Math.abs($0)",
  },
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
  char buf[32];
  char out[40];
  char dig[16];
  f32  v  = f32_unbox(x);
  int  p  = 1;
  int  nd = 0;
  int  k  = 0;
  if (v != v) {
    return io_str(e, "nan", 3);
  }
  for (; p < 9; p += 1) {
    snprintf(buf, 32, "%.*e", p - 1, (double)v);
    if (strtof(buf, NULL) == v) {
      break;
    }
  }
  int n = snprintf(buf, 32, "%.*e", p - 1, (double)v);
  if (!isfinite(v)) {
    return io_str(e, buf, n);
  }
  char* m  = buf + (*buf == '-');
  char* ep = strchr(m, 'e');
  int   ex = atoi(ep + 1);
  for (char* c = m; c < ep; c += 1) {
    if (*c != '.') {
      dig[nd++] = *c;
    }
  }
  while (nd > 1 && dig[nd - 1] == '0') {
    nd -= 1;
  }
  if (*buf == '-') {
    out[k++] = '-';
  }
  if (ex >= 21 || ex <= -7) {
    out[k++] = dig[0];
    if (nd > 1) {
      out[k++] = '.';
      memcpy(out + k, dig + 1, nd - 1);
      k += nd - 1;
    }
    k += sprintf(out + k, "e%c%d", ex < 0 ? '-' : '+', abs(ex));
  } else if (ex < 0) {
    k += sprintf(out + k, "0.");
    for (int i = 1; i < -ex; i += 1) {
      out[k++] = '0';
    }
    memcpy(out + k, dig, nd);
    k += nd;
  } else {
    for (int i = 0; i <= ex; i += 1) {
      out[k++] = i < nd ? dig[i] : '0';
    }
    if (nd > ex + 1) {
      out[k++] = '.';
      memcpy(out + k, dig + ex + 1, nd - ex - 1);
      k += nd - ex - 1;
    }
  }
  return io_str(e, out, k);
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

let PIDN = 0;

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

function name_own(book: Bend.Book, k: Bend.Name): string {
  const src = (book.tlds[k] as Bend.Def).T.s?.src ?? "";
  const segs = k.split(".");
  for (let i = 1; i < segs.length; i += 1) {
    const own = segs.slice(i).join(".");
    if (new RegExp("^(def|law) " + own.replace(/\./g, "\\.") + "[(:\\s]", "m")
      .test(src)) {
      return own;
    }
  }
  return k;
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
    const [k, o, jo = o] = p.split(":");
    const fill = (t: string, op: string): string =>
      t.replaceAll("$k", k).replaceAll("$o", op);
    out[pre + k] = { C: fill(C, o), JS: fill(JS, jo) };
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
  return Bend.Var(k, (PIDN += 1)) as Probe;
}

function probe_of(t: HTerm): Probe {
  return Bend.term_force(t) as Probe;
}

// Term
// ====

function term_open(t: Of<"Lam"> | HLet): { ps: Probe[]; b: HTerm } {
  return memo(OPENS, t, () => {
    const ps = (t.$ === "Lam" ? [t.k] : t.k).map(probe);
    return { ps, b: t.$ === "Lam" ? t.f(ps[0]) : t.f(ps) };
  });
}

function term_split(t: HLet, j = 0, xs: HTerm[] = []): HTerm {
  if (j === t.k.length) {
    return t.f(xs);
  }
  return Bend.Let([t.k[j]], [t.i[j]], [t.v[j]],
    (x: HTerm[]) => term_split(t, j + 1, [...xs, x[0]]), t.s, [t.q[j]]);
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
    case "Let": return [...t.v.filter((_, j) => quant_live(t.q[j])),
      term_open(t).b];
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
      default: {
        const ck = call_kind(cb, t);
        const lent = ck && cb.brw.get(ck.k);
        return term_kids(cb, t).reduce((u, x, j) =>
          lent?.[j - 1] ? u
            : Bend.pmap_union(u, term_uses(cb, x), (a, b) => a + b),
          USE0);
      }
    }
  });
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
  const it = memo(INTRS, k, () =>
    def_own(c.book.tlds[k]) ? OPERATIONS[eff_name(k)] ?? null : null);
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
    const tld = carb_fresh(c, m.t.k) ?? c.book.tlds[m.t.k];
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
  const pre = m.t.$ === "Ref" ? carb_fresh(cb, m.t.k) : undefined;
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
  while (x.$ === "Ann") {
    ty = x.T;
    x = Bend.term_force(x.x);
  }
  return [x, ty];
}

function ty_adt(book: Bend.Book, A: HTerm | null): HAdt | null {
  const t = ty_wnf(book, A);
  return t?.$ === "ADT" ? t : null;
}

// Lay
// ===

function lay_of(book: Bend.Book, A: HTerm | null): Lay {
  const t = ty_adt(book, A);
  if (t === null) {
    return BOX;
  }
  return memo(LAYS, t, () => lay_adt(book, t));
}

function lay_adt(book: Bend.Book, t: HAdt): Lay {
  const word = WORDS[t.k];
  if (word !== undefined) {
    return word;
  }
  const tld = book.tlds[t.k];
  if (t.k === "Array" || tld?.$ !== "ADT" || lay_cyclic(book, t.k)) {
    return BOX;
  }
  return lay_pack(tld.c.map((c): Arm =>
    ({ k: c.k, fs: lay_fields(book, ctr_doms(book, c, t.x)) })));
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

function def_own(tld: Bend.TLD | undefined): boolean {
  return tld?.$ === "Def" && tld.i === undefined && (tld.b || tld.v === null);
}

function def_lays(cb: Carb, k: Bend.Name): Lay[] {
  if (k === CLO_APPLY) {
    return [BOX, BOX];
  }
  const tld = cb.book.tlds[k] as Bend.Def;
  const lays = live_doms(cb.book, tld).map(([, , A]) => lay_of(cb.book, A));
  if (def_foreign(tld)) {
    return lays.map(() => BOX).concat([BOX]);
  }
  (cb.kof.get(k) ?? []).forEach((c, i, of) => {
    lays[lays.length - of.length + i] = def_ret(cb, c);
  });
  return lays;
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

function io_ports(book: Bend.Book, ext: string,
  probe: (m: [string, Bend.Name]) => void): [string, Bend.Name][] {
  const names = [...new Set(book.order)].filter((k) => {
    const tld = book.tlds[k];
    return /(^|\.)main$/.test(k) && tld.$ === "Def" && "IO" in book.tlds
      && (tld.v !== null || tld.i !== undefined);
  });
  const mains = names.flatMap((k): [string, Bend.Name][] => {
    try {
      return [[k.slice(0, Math.max(0, k.length - 5)), io_entry(book, k)]];
    } catch (e) {
      if (names.length === 1) {
        throw e;
      }
      return [];
    }
  });
  carb_book(book, mains.map(([, k]) => k));
  const fits = (k: Bend.Name, seen: Set<Bend.Name>): boolean => {
    const tld = book.tlds[k];
    if (def_foreign(tld) && !tld.i.some((p) => p.endsWith(ext))) {
      return false;
    }
    return seen.has(k) || (seen.add(k)
      && [...REFS.get(k) ?? []].every((g) => fits(g, seen)));
  };
  const kept = mains.filter(([, k]) => fits(k, new Set())).filter((m) => {
    try {
      probe(m);
      return true;
    } catch {
      return names.length === 1;
    }
  });
  if (kept.length === 0) {
    die("no main to run");
  }
  return kept;
}

export function io_entry(book: Bend.Book, k: Bend.Name): Bend.Name {
  if (io_type(book, k) !== null) {
    return k;
  }
  const io = k + ".io";
  if (book.tlds[io] === undefined) {
    const main = book.tlds[k] as Bend.Def;
    const ns = k.slice(0, -4);
    const st: Show = { book, pre: k + ".show", ns, defs: new Map(), src: [] };
    const show = main.n > 0 ? null : show_of(st, main.T);
    const bytes = (): string => JSON.stringify(Buffer.from(show_name(st,
      show_text(Bend.term_snf(book, main.v as HTerm)))).toString("latin1"));
    const mint = (text: string, src: string[]): void => {
      const n0 = book.order.length;
      try {
        Bend.parse_book(book, "", [...src, `def ${io}() -> IO(Unit):`,
          `  IO.print(${text})`, ""].join("\n"));
        Bend.book_valid(book, n0);
      } catch (e) {
        for (const d of book.order.splice(n0)) {
          delete book.tlds[d];
        }
        if (src.length === 0) {
          throw e;
        }
        mint(bytes(), []);
      }
    };
    mint(show === null ? bytes() : show + "(" + k + "())",
      show === null ? [] : st.src);
  }
  return io;
}

export function io_run(book: Bend.Book): number {
  const src = js_lib(book, ["main"], null) + "\n" + RUNTIME_MAIN
    + "\nreturn io_run(" + js_sat("main") + ");";
  return new Function("require", src)(import.meta.require) as number;
}

// Show
// ====
// A pure main prints its value through a printer written in Bend, one def
// per type under main's type, spelled as term_show spells a value; what
// it cannot walk (a function, a Type, an erased or dependent field, a
// main with parameters) prints its normal form, taken here.

function show_text(t: HTerm): string {
  return Bend.term_show(Bend.term_lower(t));
}

function show_name(st: Show, text: string): string {
  return st.ns === "" ? text : text.replace(new RegExp("(?<![A-Za-z0-9_.])"
    + st.ns.replace(/\./g, "\\."), "g"), "");
}

function show_def(st: Show, name: string, sig: string,
  body: string[]): string {
  st.src.push(`def ${name}${sig}:`, ...body.map((l) => "  " + l), "");
  return name;
}

function show_once(st: Show, name: string, mint: () => void): string {
  if (!st.defs.has(name)) {
    st.defs.set(name, name);
    mint();
  }
  return name;
}

function show_word(st: Show): string {
  const p = st.pre;
  return show_once(st, p + ".word", () => {
    show_def(st, p + ".bit", "(b: Bool, t: String) -> String", ["match b:",
      "  case False{}:", `    "WCon{False{}, " ++ t ++ "}"`,
      "  case True{}:", `    "WCon{True{}, " ++ t ++ "}"`]);
    show_def(st, p + ".word", "(n: Nat, +x: U32) -> String", ["match n:",
      "  case 0n:", `    "WNil{}"`, "  case 1n+p:",
      `    ${p}.bit(U32.is_eq(U32.and(x, 1), 1), ${p}.word(p, U32.shr(x)))`]);
  });
}

function show_chr(st: Show): string {
  const p = st.pre;
  return show_once(st, p + ".chr", () => {
    show_def(st, p + ".ok", "(+c: U32) -> Bool",
      ["U32.is_eq(c, 0) || U32.is_eq(c, 9) || U32.is_eq(c, 10)",
        "  || U32.is_eq(c, 13) || (U32.is_ge(c, 32) && U32.is_ne(c, 127)",
        "  && (U32.is_lt(c, 55296) || U32.is_gt(c, 57343))",
        "  && U32.is_le(c, 1114111))"]);
    show_def(st, p + ".utf8.go", "(+c: U32, n: Nat, lead: U32, t: String)"
      + " -> String", ["match n:", "  case 0n:", "    SCon{Chr{U32.or(lead, c)}"
      + ", t}", "  case 1n+k:", `    ${p}.utf8.go(U32.shrn(c, 6n), k, lead,`
      + " SCon{Chr{U32.or(128, U32.and(c, 63))}, t})"]);
    show_def(st, p + ".utf8", "(+c: U32) -> String",
      ["match U32.is_lt(c, 128):", "  case True{}:",
        `    ${p}.utf8.go(c, 0n, 0, SNil{})`, "  case False{}:",
        "    match U32.is_lt(c, 2048):", "      case True{}:",
        `        ${p}.utf8.go(c, 1n, 192, SNil{})`, "      case False{}:",
        "        match U32.is_lt(c, 65536):", "          case True{}:",
        `            ${p}.utf8.go(c, 2n, 224, SNil{})`,
        "          case False{}:",
        `            ${p}.utf8.go(c, 3n, 240, SNil{})`]);
    show_def(st, p + ".esc.go", "(+c: U32, n: Nat, q: Bool) -> String",
      ["match n:", `  case 10n:`, `    "\\\\n"`, `  case 9n:`, `    "\\\\t"`,
        `  case 13n:`, `    "\\\\r"`, `  case 0n:`, `    "\\\\0"`,
        `  case 92n:`, `    "\\\\\\\\"`, "  case k:", "    match q:",
        "      case True{}:", `        "\\\\" ++ ${p}.utf8(c)`,
        "      case False{}:", `        ${p}.utf8(c)`]);
    show_def(st, p + ".esc", "(+c: U32, q: U32) -> String",
      [`${p}.esc.go(c, U32.to_nat(c), U32.is_eq(c, q))`]);
    show_u32(st);
    show_def(st, p + ".chr.go", "(+c: U32, ok: Bool) -> String",
      ["match ok:", "  case True{}:", `    "'" ++ ${p}.esc(c, 39) ++ "'"`,
        "  case False{}:", `    "Chr{" ++ ${p}.u32(c) ++ "}"`]);
    show_def(st, p + ".chr", "(x: Char) -> String", ["match x:",
      "  case Chr{c}:", "    +d = c", `    ${p}.chr.go(d, ${p}.ok(d))`]);
  });
}

function show_str(st: Show): string {
  const p = st.pre;
  return show_once(st, p + ".str", () => {
    show_chr(st);
    show_def(st, p + ".str.fin", "(h: Char, r: String & Bool) -> String & Bool",
      ["match h:", "  case Chr{c}:", "    (t, ok) = r", "    +d = c",
        `    (SCon{Chr{d}, t}, ok && ${p}.ok(d))`]);
    show_def(st, p + ".str.all", "(x: String) -> String & Bool",
      ["match x:", "  case SNil{}:", "    (SNil{}, True{})",
        "  case SCon{h, t}:", `    ${p}.str.fin(h, ${p}.str.all(t))`]);
    show_def(st, p + ".str.ok", "(x: String) -> String & Bool",
      ["match x:", "  case SNil{}:", "    (SNil{}, False{})",
        "  case SCon{h, t}:", `    ${p}.str.fin(h, ${p}.str.all(t))`]);
    show_def(st, p + ".str.esc.fin", "(h: Char, t: String) -> String",
      ["match h:", "  case Chr{c}:", `    ${p}.esc(c, 34) ++ t`]);
    show_def(st, p + ".str.esc", "(x: String) -> String",
      ["match x:", "  case SNil{}:", "    SNil{}", "  case SCon{h, t}:",
        `    ${p}.str.esc.fin(h, ${p}.str.esc(t))`]);
    show_def(st, p + ".str.raw", "(x: String) -> String",
      ["match x:", "  case SNil{}:", `    "SNil{}"`, "  case SCon{h, t}:",
        `    "SCon{" ++ ${p}.chr(h) ++ ", " ++ ${p}.str.raw(t) ++ "}"`]);
    show_def(st, p + ".str.go", "(r: String & Bool) -> String",
      ["(s, ok) = r", "match ok:", "  case True{}:",
        `    "\\"" ++ ${p}.str.esc(s) ++ "\\""`, "  case False{}:",
        `    ${p}.str.raw(s)`]);
    show_def(st, p + ".str", "(x: String) -> String",
      [`${p}.str.go(${p}.str.ok(x))`]);
  });
}

function show_u32(st: Show): string {
  return show_once(st, st.pre + ".u32", () => {
    show_def(st, st.pre + ".u32", "(x: U32) -> String",
      [`"U32{" ++ ${show_word(st)}(32n, x) ++ "}"`]);
  });
}

function show_of(st: Show, T: HTerm): string | null {
  const t = ty_wnf(st.book, T) as HTerm;
  const p = st.pre;
  if (t.$ === "ADT" && t.r.length === 0 && t.k in SHOWN) {
    return SHOWN[t.k](st);
  }
  const key = show_text(t);
  const got = st.defs.get(key);
  if (got !== undefined) {
    return got;
  }
  const name = p + ".t" + st.defs.size;
  st.defs.set(key, name);
  const sig = `(x: ${key}) -> String`;
  if (t.$ === "Eql") {
    return show_def(st, name, sig, [`"{==}"`]);
  }
  const adt = t.$ === "ADT" && t.r.length === 0 ? t : null;
  const tld = adt === null ? null : st.book.tlds[adt.k];
  const ctrs = tld?.$ === "ADT" ? tld.c : [];
  const nat = ctrs.some((c) => /^(Succ|Zero)$/.test(show_name(st, c.k)));
  const body = ["match x:"];
  for (const c of ctrs) {
    const doms = tele_unbind(st.book, ty_tele(st.book, c.T, adt!.x)).doms;
    const fs = doms.map((d) => live_dom(d) ? show_of(st, d[2]) : null);
    const vs = doms.map((_, j) => "f" + j);
    const parts = vs.map((v, j) => nat && fs[j] === name
      ? `${name}.go(${v}, 0n)` : `${fs[j]}(${v})`).join(' ++ ", " ++ ');
    if (fs.some((f) => f === null)) {
      break;
    }
    const nm = show_name(st, c.k);
    const at = nm === "Succ" && fs.length === 1 ? fs[0] === name
      ? `${name}.go(f0, Succ{n})` : `Nat.show(Succ{n}) ++ "n+" ++ ${parts}`
      : nm === "Zero" && fs.length === 0 ? `Nat.show(n) ++ "n"` : null;
    const pre = nat ? `${p}.chain(n) ++ ` : "";
    body.push(`  case ${c.k}{${vs.join(", ")}}:`, at !== null ? `    ${at}`
      : parts === "" ? `    ${pre}"${nm}{}"`
      : `    ${pre}"${nm}{" ++ ${parts} ++ "}"`);
  }
  if (tld?.$ !== "ADT" || body.length !== 1 + 2 * tld.c.length) {
    st.defs.delete(key);
    return null;
  }
  if (!nat) {
    return show_def(st, name, sig, body);
  }
  show_once(st, p + ".chain", () => {
    show_def(st, p + ".chain", "(n: Nat) -> String", ["match n:",
      "  case Zero{}:", `    ""`, "  case Succ{k}:",
      `    Nat.show(Succ{k}) ++ "n+"`]);
  });
  show_def(st, name + ".go", `(x: ${key}, n: Nat) -> String`, body);
  return show_def(st, name, sig, [`${name}.go(x, 0n)`]);
}

// Mint
// ====

function mint_lift(t: HTerm): Open {
  return (env) => env.get(t) ?? t;
}

function mint_caps(cs: Capture[], f: Open): Open {
  return (env) => cs.reduce((c, b) => Bend.App(c, env.get(b.p) ?? b.p), f(env));
}

function mint_ret(cb: Carb, t: HTerm): HTerm {
  const s = Bend.term_force(t);
  if (s.$ === "Ann" || s.$ === "Let") {
    return s.$ === "Ann" ? s.T : mint_ret(cb, s.f(s.v.map(() => DUMMY)));
  }
  const m = term_spine(cb, s);
  const tld = m.t.$ === "Ref" ? cb.book.tlds[m.t.k] : undefined;
  return ty_tele(cb.book, tld?.$ === "Def" ? tld.T
    : ty_ann(m.h) ?? die("a minted result type"), m.all);
}

function mint(cb: Carb, def: Bend.Name, stem: string, scope: Capture[],
  tail: number, build: () => Open, ext = 0, of?: Bend.Name[]): Open {
  cb.kn += 1;
  const name = def + "$" + stem + cb.kn;
  const clo = stem === "c";
  const seq = stem === "k";
  if (clo) {
    cb.dyn.add(name);
    cb.owner.push(name);
  } else {
    cb.home.set(name, cb.owner[cb.owner.length - 1]);
  }
  cb.kof.set(name, of ?? (clo ? [CLO_APPLY] : []));
  const body = build();
  if (clo) {
    cb.owner.pop();
  }
  const bt = body(EMPTY);
  const kept = scope.filter((c, i) => i >= scope.length - tail
    || !quant_live(c.q) || term_use(term_uses(cb, bt), c.p) > 0);
  cb.kept.set(name, kept);
  const T = kept.reduceRight<HTerm>((R, c, i) =>
    Bend.All<Bend.HBody>(c.q, c.p.k, i,
    c.A ?? die("an untyped capture"),
    (_x) => R), mint_ret(cb, bt));
  const lams = kept.reduceRight<Open>((rest, c, i) =>
    (env) => Bend.Lam(c.p.k, i, (x) => rest(new Map(env).set(c.p, x))), body);
  const fn = lams(EMPTY);
  cb.book.tlds[name] =
    { $: "Def", n: kept.length + ext, T, v: fn, h: fn };
  cb.mint.set(name, seq);
  return mint_caps(kept.slice(0, kept.length - tail),
    mint_lift(Bend.Ref(name)));
}

// Carb
// ====

function carb_fresh(cb: Carb, k: Bend.Name): TLD | undefined {
  const tld = cb.src[k];
  if (tld?.$ === "Def" && tld.e !== undefined && tld.h === undefined) {
    const h = Bend.term_higher(tld.e);
    const n = tld.n + Math.min(def_raise(cb.book, h, tld.n),
      tele_unbind(cb.book, tld.T).doms.length - tld.n);
    cb.src[k] = { ...tld, n, h };
  }
  return cb.src[k];
}

function carb_book(src: Bend.Book, roots: Bend.Name[]): Carb {
  [TELES, REFS, NODES, CYCLES, FLATS, INTRS].forEach((m) => m.clear());
  LOCAL.clear();
  for (const [k, tld] of Object.entries(src.tlds)) {
    if (def_foreign(tld)) {
      LOCAL.set(k, name_own(src, k));
    }
  }
  memo_gc();
  const book: Book = { ...src, tlds: { ...src.tlds } };
  const cb: Carb = {
    src: { ...src.tlds },
    book,
    mint: new Map(),
    dyn: new Set(roots),
    kof: new Map(),
    kept: new Map(),
    forks: new Map(),
    slots: new Map(),
    home: new Map(),
    owner: [],
    kn: 0,
    done: new Set(),
    queue: roots,
    bangs: new Set(),
    sites: new Map(),
    brw: new Map(),
    live: new Map(),
    hot: new Set(),
    poly: new Set(),
    own: new Map(),
  };
  let d: Bend.Name = "";

  const PASS: Kont = (_c, x) => x;

  function bind(caps: Capture[], l: HLet, v: Open,
    rest: (caps: Capture[], body: HTerm) => Open, cut = false): Open {
    const { ps: [p], b } = term_open(l);
    const c2 = [...caps, { p, q: l.q[0], A: ty_ann(v(EMPTY)) }];
    const body = cut ? mint_caps(c2.slice(-1), mint(cb, d, "k", c2, 1,
      () => rest(c2, b), 0, [call_kind(cb, v(EMPTY))!.k])) : rest(c2, b);
    return (env) => Bend.Let(l.k, l.i, [v(env)],
      (x) => body(new Map(env).set(p, x[0])), l.s, l.q);
  }

  function apps(caps: Capture[], t: HTerm, k: Kont): Open {
    type Fill = (caps: Capture[],
      rb: (f: Open) => Open) => Open;
    const m = term_spine(cb, t);
    const go = (u: HTerm, k2: Fill): Open => {
      const s = Bend.term_force(u);
      if (s.$ === "Ann") {
        return go(s.x, (c2, rb) => k2(c2, (f) =>
          (env) => Bend.Ann(rb(f)(env), s.T, s.s)));
      }
      if (s.$ === "App") {
        if (!m.args.includes(s.x) && m.t.$ === "Var") {
          return go(s.f, k2);
        }
        const app: Fill = (c2, rb) => m.args.includes(s.x)
          ? expr(c2, s.x, null, (c3, x) => k2(c3, (f) =>
            (env) => Bend.App(rb(f)(env), x(env), s.s)))
          : k2(c2, (f) => (env) => Bend.App(rb(f)(env), s.x, s.s));
        if (!m.args.includes(s.x) || !call_is(cb, s.f)) {
          return go(s.f, app);
        }
        return expr(caps, s.f, null, (c2, g) => app(c2, () => g));
      }
      return k2(caps, (f) => f);
    };
    return go(t, (c2, rb) => k(c2, rb(mint_lift(m.t))));
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
    const s = Bend.term_force(t);
    const x = Bend.term_strip(t);
    if (x.$ !== "Lam" && !mat_head(x)) {
      if (left === 0) {
        return leaf(caps, s);
      }
      const T = ty ?? ty_ann(s) ?? die("an untyped arm");
      return func(caps, term_eta(cb.book, s, T, 1), null, left);
    }
    if (left === 0 && s.$ !== "Ann") {
      return expr(caps, s, ty, PASS);
    }
    switch (s.$) {
      case "Ann": {
        const g = func(caps, s.x, s.T, left);
        return (env) => Bend.Ann(g(env), s.T, s.s);
      }
      case "Lam": {
        const all = ty_all(cb.book, ty);
        const { ps: [p], b } = term_open(s);
        const cap = { p, q: all?.q ?? Bend.Lone(), A: all?.A ?? null };
        const B = all && all.B(DUMMY);
        const body = func([...caps, cap], b, B,
          left - (quant_live(cap.q) ? 1 : 0));
        return (env) => Bend.Lam(s.k, s.i,
          (y) => body(new Map(env).set(p, y)), s.s);
      }
      case "Mat": {
        const ctr = cb.book.ctrs[s.k];
        const h = func(caps, s.h, null, left - 1
          + (ctr ? ctr_doms(cb.book, ctr).length : 0));
        const m = func(caps, s.m, null, left);
        return (env) => Bend.Mat(s.k, h(env), m(env), s.s);
      }
      default: {
        return mint_lift(s);
      }
    }
  }

  function alive(s: HLet): HLet {
    const o = term_open(s);
    const u = term_uses(cb, o.b);
    const on = s.q.map((q, j) => quant_live(q) && term_use(u, o.ps[j]) > 0);
    const pick = <T>(xs: T[]): T[] => xs.filter((_, j) => on[j]);
    return Bend.Let(pick(s.k), pick(s.i), pick(s.v), (xs) => {
      let i = 0;
      return s.f(s.v.map((v, j) => on[j] ? xs[i++] : v));
    }, s.s, pick(s.q));
  }

  function leaf(caps: Capture[], t: HTerm): Open {
    const s = Bend.term_strip(t);
    if (s.$ === "Rwt") {
      return leaf(caps, s.f);
    }
    if (s.$ === "Let") {
      const l = alive(s);
      if (l.k.length === 0) {
        return leaf(caps, l.f([]));
      }
      if (l.k.length >= 2) {
        return l.v.every((v) => call_is(cb, v)) ? fork(caps, l)
          : leaf(caps, term_split(l));
      }
      if (call_is(cb, l.v[0]) && !flat_call(cb, l.v[0])) {
        return apps(caps, l.v[0], (c2, c) =>
          bind(c2, l, c, (c3, b) => leaf(c3, b), true));
      }
      return expr(caps, l.v[0], null, (c2, v) =>
        bind(c2, l, v, (c3, b) => leaf(c3, b)));
    }
    const got = call_eta(cb, t);
    if (got !== null) {
      return leaf(caps, got);
    }
    if (call_is(cb, t)) {
      return apps(caps, t, PASS);
    }
    return expr(caps, t, null, PASS);
  }

  function fork(caps: Capture[], s: HLet): Open {
    const n = s.k.length;
    const o = term_open(s);
    const next = (stem: string): Bend.Name => d + "$" + stem + (cb.kn + 1);
    const arg_caps = (ck: Call): Capture[] => {
      const tld = cb.book.tlds[ck.k];
      const doms = tld?.$ === "Def" ? live_doms(cb.book, tld) : [];
      return ck.args.map((_, i) => ({ p: probe("a"), q: Bend.Lone(),
        A: doms[i]?.[2] ?? Bend.Typ(Bend.Qua(Bend.Lone())) }));
    };
    return many(caps, n, (c2, j, kx) => apps(c2, s.v[j], kx), (c2, vs) => {
      const cks = vs.map((v) => call_kind(cb, v(EMPTY))!);
      const xs = vs.map((v, j): Capture =>
        ({ p: o.ps[j], q: s.q[j], A: ty_ann(v(EMPTY)) }));
      const jn = next("j");
      const jl = mint(cb, d, "j", [...c2, ...xs], n,
        () => leaf([...c2, ...xs], o.b), 0, cks.map((c) => c.k));
      const jcaps = (cb.kept.get(jn) as Capture[]).slice(0, -n);
      const args = cks.map(arg_caps);
      const rs = xs.map((x, j) => ({ ...x, p: probe(s.k[j]) }));
      const frame = (i: number): Capture[] =>
        [...args.slice(1).flat(), ...jcaps, ...rs.slice(0, i - 1)];
      const scope = (i: number): Capture[] =>
        [...args.slice(i).flat(), ...jcaps, ...rs.slice(0, i)];
      const call = (j: number): Open => (env) => {
        const ps = args[j].map((c) => env.get(c.p) ?? c.p);
        if (cks[j].k === CLO_APPLY) {
          return Bend.App(ps[0], ps[1]);
        }
        const m = term_spine(cb, vs[j](EMPTY));
        const h: HTerm = Bend.Ref(cks[j].k, undefined, cks[j].bang);
        return m.all.reduce((f, x) =>
          Bend.App(f, m.args.includes(x) ? ps.shift() as HTerm : x), h);
      };
      const step = (i: number): Open => {
        const kn = next("k");
        cb.slots.set(kn, { L: frame(i), last: i === n });
        const body = (): Open => {
          if (i === n) {
            return mint_caps(rs, jl);
          }
          const then = step(i + 1);
          return (env) => Bend.Let([s.k[i]], [s.i[i]], [call(i)(env)],
            (x) => then(new Map(env).set(rs[i].p, x[0])), s.s, [s.q[i]]);
        };
        return mint_caps(scope(i), mint(cb, d, "k", scope(i),
          scope(i).length, body, 0, [cks[i - 1].k]));
      };
      const k1 = next("k");
      step(1);
      cb.queue.push(k1);
      const body = mint_caps(xs, jl);
      return (env) => Bend.Let(s.k, s.i, vs.map((v) => v(env)), (ys) => {
        const e2 = new Map(env);
        ys.forEach((y, j) => e2.set(o.ps[j], y));
        cb.forks.set(ys[0] as Probe, k1);
        return body(e2);
      }, s.s, s.q);
    });
  }

  function expr(caps: Capture[], t: HTerm, ty: HTerm | null, k: Kont): Open {
    if (term_const(t)) {
      return k(caps, mint_lift(t));
    }
    const s = Bend.term_force(t);
    if (s.$ === "Ann") {
      return expr(caps, s.x, s.T, (c2, x) =>
        k(c2, (env) => Bend.Ann(x(env), s.T, s.s)));
    }
    const got = call_eta(cb, s);
    if (got !== null) {
      return expr(caps, got, ty, k);
    }
    if (call_is(cb, s) && !flat_call(cb, s)) {
      const l = Bend.Let(["h"], [0], [s], (x: HTerm[]) => x[0]);
      return apps(caps, s, (c2, c) => bind(c2, l,
        ty === null ? c : (env) => Bend.Ann(c(env), ty),
        (c3, b) => k(c3, mint_lift(b)), true));
    }
    switch (s.$) {
      case "App": {
        const m = term_spine(cb, s);
        if (m.t.$ === "Ref" || m.t.$ === "Var") {
          return apps(caps, s, k);
        }
        die("a " + m.t.$ + "-headed app");
      }
      case "Ctr": {
        const ctr = cb.book.ctrs[s.k];
        const live = ctr ? ctr_tail(cb.book, ctr).map(live_dom) : [];
        return many(caps, s.x.length, (c2, j, kx) => live[j]
          ? expr(c2, s.x[j], null, kx) : kx(c2, () => s.x[j]),
        (c2, xs) => k(c2, (env) => Bend.Ctr(s.k, xs.map((x) => x(env)), s.s)));
      }
      case "Lam": {
        const all = ty_all(cb.book, ty)
          ?? die("an untyped lambda");
        const { ps: [p], b } = term_open(s);
        const bd = { p, q: all.q, A: all.A };
        const c2 = [...caps, bd];
        if (!quant_live(all.q)) {
          return expr(c2, b, all.B(p), k);
        }
        return k(caps, mint(cb, d, "c", c2, 1, () => leaf(c2, b)));
      }
      case "Let": {
        const l = alive(s);
        if (l.k.length === 0) {
          return expr(caps, l.f([]), ty, k);
        }
        if (l.k.length >= 2) {
          return expr(caps, term_split(l), ty, k);
        }
        return expr(caps, l.v[0], null, (c2, v) =>
          bind(c2, l, v, (c3, b) => expr(c3, b, ty, k)));
      }
      case "Mat":
      case "Efq": {
        const T = ty ?? die("an untyped match");
        return k(caps, mint(cb, d, "c", caps, 0,
          () => func(caps, Bend.Ann(s, T), null, 1), 1));
      }
      case "Rwt": {
        return expr(caps, s.f, ty, k);
      }
      default: {
        return k(caps, mint_lift(s));
      }
    }
  }

  while (cb.queue.length > 0) {
    d = cb.queue.shift() as Bend.Name;
    if (cb.done.has(d)) {
      continue;
    }
    cb.done.add(d);
    memo_gc();
    const tld = book.tlds[d];
    if (!done_live(tld)) {
      continue;
    }
    let out = tld.h as HTerm;
    if (!cb.mint.has(d)) {
      if (tld.e === undefined) {
        die("unelaborated " + d);
      }
      const fr = carb_fresh(cb, d) as Def;
      cb.owner = [d];
      out = func([], fr.h as HTerm, fr.T, live_doms(cb.book, fr).length)(EMPTY);
    }
    book.tlds[d] = { ...(cb.src[d] as Def | undefined) ?? tld, h: out };
    const refs = new Set<Bend.Name>();
    term_any(cb, out, (s) => {
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
    REFS.set(d, refs);
    cb.queue.push(...[...refs]
      .sort((a, b) => Number(cb.mint.has(b)) - Number(cb.mint.has(a))));
  }
  const ret = (k: Bend.Name) => lay_of(cb.book,
    def_ret_type(cb.book, cb.book.tlds[k] as Bend.Def));
  const edges = [...cb.home, ...done_defs(cb).flatMap(([k, tld]) =>
    flat_tails(cb, tld.h!).map((k2) => [k, k2]))];
  for (let n = -1; n !== cb.dyn.size;) {
    n = cb.dyn.size;
    for (const [k, k2] of edges) {
      if (k2 === CLO_APPLY || def_foreign(cb.book.tlds[k2])) {
        cb.dyn.add(k);
      } else if (cb.dyn.has(k) !== cb.dyn.has(k2) || !lay_eq(ret(k), ret(k2))) {
        cb.dyn.add(k);
        cb.dyn.add(k2);
      }
    }
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
  const s = Bend.term_force(t);
  switch (s.$) {
    case "Ann": return flat_tails(cb, s.x);
    case "Lam": return flat_tails(cb, term_open(s).b);
    case "Mat": return [...flat_tails(cb, s.h), ...flat_tails(cb, s.m)];
    case "Let": return s.k.length === 1 ? flat_tails(cb, term_open(s).b) : [];
    default: {
      const ck = call_kind(cb, s);
      return ck ? [ck.k] : [];
    }
  }
}

function flat_of(cb: Carb, k: Bend.Name): boolean {
  return memo(FLATS, k, () => {
    const tld = cb.mint.has(k) ? cb.book.tlds[k] : carb_fresh(cb, k);
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
  return [...cb.done].map((k) => [k, cb.book.tlds[k]] as [Bend.Name, Def])
    .filter((p) => live(p[1]));
}

// Cid
// ===

function cid_mac(k: string): string {
  return "CID_" + name_clean(k).toUpperCase();
}

function cid_reg(fl: File, k: Bend.Name, abi = -1): string {
  if (!fl.cids.has(k)) {
    const ks = lay_node(fl.book, k).ks;
    fl.cids.set(k, abi >= 0 ? [abi, abi]
      : [ks.length, ks.lastIndexOf("box") + 1]);
  }
  return cid_mac(k);
}

// File
// ====

function file_new(cb: Carb, decl: string): File {
  return { ...cb, decl, segs: [], seg: seg_new("", false, []), tab: 2,
    cids: new Map(), tabs: new Map(), spins: [], spun: new Map(),
    reqs: "", resw: 1, fuel: 0, fresh: new Map(), spares: [], uses: new Map(),
    local: new Set(), brwl: new Set() };
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

function seg_new(name: string, seq: boolean, params: string[], resw = 1,
  ks: Kind[] = params.map(() => "w64")): Seg {
  const pop = params.length - resw;
  return { fid: seg_fid(name), def: name, lines: [], params, ks,
    refs: new Set(), frame: seq ? { pop, resw,
      at: params.slice(0, pop).map((_, i) => i - pop) } : null };
}

function seg_fid(k: Bend.Name): string {
  return "FID_" + name_clean(k).toUpperCase();
}

// The first BANK arguments ride named locals; the rest ride rx[].
const BANK = 16;

function reg(i: number): string {
  return i < BANK ? "r" + i : "rx[" + (i - BANK) + "]";
}

function seg_ref(fl: File, fid: string): string {
  fl.seg.refs.add(fid);
  return fid;
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

function node_fields(fl: File, t: string, node: Lay, v: Val,
  tail = false): Val[] {
  const n = node.ks.length;
  const fs = node.arms![0].fs;
  if (n === 0 || (n === 1 && node.ks[0] === "w32")) {
    return fs.map((f) => val_new(f.lay.ks.map(() => `term_loc(${t})`), f.lay));
  }
  const cell = val_cell(v, 0);
  const lent = cell !== null || fl.brwl.has(t);
  let ws: string[];
  if (lent) {
    const bl = emit_hold(fl, [`term_peek(e, ${t})`], "bl")[0];
    ws = emit_hold(fl, node.ks.map((_, j) => `e.mem[${bl} + ${j}]`), "f",
      node.ks);
    ws.forEach((w, j) => {
      if (node.ks[j] === "box" && cell === null) {
        fl.brwl.add(w);
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
  const av = node.ks.map((k, j): Cell | null => k === "box" && cell !== null
    ? { arr: cell.arr, at: `term_peek(e, ${t}) + ${j}` } : null);
  return fs.map((f) => val_field(val_new(ws, node, av), f));
}

// Facts
// =====

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

function facts_lend(cb: Carb, A: HTerm): boolean {
  const t = ty_adt(cb.book, A);
  return t !== null && t.k !== "Array"
    && lay_of(cb.book, A).ks.includes("box");
}

function facts_scan(cb: Carb, k: Bend.Name, sites: (HTerm | null)[],
  first: boolean): boolean {
  memo_gc();
  const np = cb.poly.size;
  let pi = 0;
  cb.own.clear();
  const tld = cb.book.tlds[k] as Def;
  const lays = def_lays(cb, k);
  const live = cb.live.get(k)!;
  const env = new Map<Probe, Slot>();
  let hit = false;
  const flip = (r: Root | null) => {
    const bs = r && cb.brw.get(r[0]);
    if (bs?.[r![1]]) {
      bs[r![1]] = false;
      hit = true;
    }
  };
  const mark = (s: Slot, ws?: boolean[]) => {
    for (let j = 0; s !== null && s.p >= 0 && j < s.lay.ks.length; j += 1) {
      if ((ws === undefined || ws[j]) && !live[s.p][s.at + j]) {
        live[s.p][s.at + j] = true;
        hit = true;
      }
    }
  };
  const site_hot = (A: HTerm | null, n: number) => {
    if (first) {
      sites.push(A);
    }
    if (n > 1 && lay_of(cb.book, A).ks.includes("box")) {
      facts_hot(cb, A, true);
    }
  };
  const packed = (v: HTerm): boolean => v.$ === "Ctr"
    && ["", "w32"].includes(lay_node(cb.book, v.k).ks.join());
  const guard = (t: HTerm): void => {
    const s = Bend.term_force(t);
    if (call_is(cb, s)) {
      return site(s, null);
    }
    if (s.$ === "Var") {
      const slot = env.get(probe_of(s)) ?? null;
      flip(slot?.root ?? null);
      mark(slot);
    } else if (s.$ === "Ref") {
      cb.brw.get(s.k)?.forEach((_, j) => flip([s.k, j]));
    } else if (s.$ === "App") {
      const m = term_spine(cb, s);
      const it = m.t.$ === "Ref" ? intr_of(cb, m.t.k) : undefined;
      const pk = packed(it === OPERATIONS.array_new
        ? Bend.term_strip(m.all[2]) : s);
      if ((it === OPERATIONS.array_get || it === OPERATIONS.array_new
        || it === OPERATIONS.array_clone)
        && lay_of(cb.book, m.all[0]).ks.includes("box") && !pk) {
        facts_hot(cb, m.all[0], true);
      }
    }
    term_kids(cb, s).forEach(guard);
  };
  const site = (t: HTerm, ct: HTerm | null): void => {
    const ck = call_kind(cb, t) as Call;
    const lent = cb.brw.get(ck.k) ?? [];
    const clive = cb.live.get(ck.k);
    const clays = def_lays(cb, ck.k);
    ck.args.forEach((a, j) => {
      const v = Bend.term_strip(a);
      const s = v.$ === "Var" && env.get(probe_of(v));
      if (!s) {
        if (!packed(v)) {
          flip(lent[j] ? [ck.k, j] : null);
        }
        return guard(a);
      }
      const held = ct !== null
        && term_spine(cb, ct).args.some((z) => Bend.term_strip(z) === v);
      if (!lent[j]) {
        flip(s.root);
      } else if (s.root === null && !held) {
        flip([ck.k, j]);
      }
      mark(s, clive && lay_eq(s.lay, clays[j]) ? clive[j] : undefined);
    });
    ck.all.forEach((a, p) =>
      cb.poly.has(ck.k + "~" + p) && facts_hot(cb, a, true));
  };
  const walk = (t: HTerm, ty0: HTerm | null, args: Slot[]): void => {
    const [x, ty] = ty_peel(t, ty0);
    switch (x.$) {
      case "Lam": {
        const all = ty_all(cb.book, ty) ?? die("an untyped binder");
        const i = pi++;
        if (!quant_live(all.q)) {
          cb.own.set(x.k, k + "~" + i);
          walk(x.f(probe(x.k)), all.B(probe(x.k)), args);
          return;
        }
        const o = term_open(x);
        env.set(o.ps[0], args[0] ?? null);
        site_hot(all.A, term_use(term_uses(cb, o.b), o.ps[0]));
        walk(o.b, all.B(DUMMY), args.slice(1));
        return;
      }
      case "Mat":
      case "Efq": {
        const s = args[0] ?? null;
        const { arms, end } = mat_arms(x);
        const flat = s !== null && s.lay.arms !== null;
        if (!flat || s.lay.arms!.length > 1) {
          mark(s, flat ? [true] : undefined);
        }
        for (const [c, h] of arms) {
          const ctr = cb.book.ctrs[c];
          const As = ctr ? ctr_doms(cb.book, ctr) : [];
          const arm = flat ? lay_arm(s.lay, c) : null;
          const fs = As.map((A, f): Slot => {
            let root: Root | null = null;
            if (s !== null && lay_of(cb.book, A).ks.includes("box")) {
              if (facts_lend(cb, A)) {
                root = s.root;
              } else {
                flip(s.root);
              }
            }
            if (arm === null) {
              return root && { p: -1, at: 0, lay: BOX, root };
            }
            const { p, at } = s!;
            return { p, at: at + arm.fs[f].at, lay: arm.fs[f].lay, root };
          });
          walk(h, null, [...fs, ...args.slice(1)]);
        }
        if (Bend.term_strip(end).$ !== "Efq") {
          walk(end, null, args);
        }
        return;
      }
      case "Let": {
        const o = term_open(x);
        x.v.forEach((v, j) => {
          if (call_is(cb, v)) {
            site(v, o.b);
          } else {
            guard(v);
          }
          site_hot(ty_ann(v), term_use(term_uses(cb, o.b), o.ps[j]));
          env.set(o.ps[j], null);
        });
        walk(o.b, null, args);
        return;
      }
      default: {
        if (call_is(cb, x)) {
          site(x, null);
        } else {
          guard(x);
        }
      }
    }
  };
  walk(tld.h!, tld.T, lays.map((lay, p): Slot => ({ p, at: 0,
    lay, root: cb.brw.get(k)![p] ? [k, p] : null })));
  return hit || cb.poly.size !== np;
}

function facts_build(cb: Carb): void {
  for (const [k, tld] of done_defs(cb)) {
    cb.brw.set(k, live_doms(cb.book, tld).map(([, , A]) =>
      !cb.dyn.has(k) && facts_lend(cb, A)));
    cb.live.set(k, def_lays(cb, k).map((l) => l.ks.map(() =>
      cb.dyn.has(k))));
  }
  const sites: (HTerm | null)[] = [];
  let first = true;
  for (let go = true; go;) {
    go = false;
    for (const k of cb.brw.keys()) {
      go = facts_scan(cb, k, sites, first) || go;
    }
    first = false;
  }
  for (let seen = -1; seen < cb.hot.size;) {
    seen = cb.hot.size;
    sites.forEach((T) => facts_hot(cb, T, cb.hot.has("*")));
  }
}

// Val
// ===

function val_new(ws: string[], lay: Lay, av?: (Cell | null)[]): Val {
  return { ws, lay, av: av?.some((c) => c !== null) ? av : undefined };
}

function val_cell(v: Val, j: number): Cell | null {
  return v.av?.[j] ?? null;
}

function val_split(ws: string[], lays: Lay[]): Val[] {
  return lays.map((lay) => val_new(ws.splice(0, lay.ks.length), lay));
}

function val_field(v: Val, f: Field): Val {
  const end = f.at + f.lay.ks.length;
  return val_new(v.ws.slice(f.at, end), f.lay, v.av?.slice(f.at, end));
}

function val_word(v: Val): string {
  if (v.ws.length !== 1) {
    die(`a ${v.ws.length}-word value where one word was expected`);
  }
  return v.ws[0];
}

function val_hold(fl: File, v: Val, k: string): Val {
  return val_new(v.ws.map((w, j) => emit_alias(fl, w, k, v.lay.ks[j])),
    v.lay, v.av);
}

function val_keep(fl: File, cell: Cell): string {
  return emit_hold(fl, [`blk_keep(e, ${cell.at})`], "k")[0];
}

function val_drop(fl: File, v: Val, j: number): void {
  if (v.lay.ks[j] === "box" && !fl.brwl.has(v.ws[j])
    && val_cell(v, j) === null) {
    arr_flush(fl, v.ws[j]);
    file_push(fl, `term_sink(e, ${v.ws[j]});`);
  }
}

function val_own(fl: File, v: Val, live?: boolean[]): string[] {
  const kept = v.ws.map((w, j) => {
    const cell = val_cell(v, j);
    return cell !== null && live?.[j] !== false ? val_keep(fl, cell) : w;
  });
  return kept.map((w, j) => {
    if (live && !live[j]) {
      val_drop(fl, v, j);
      return "0";
    }
    if (v.lay.ks[j] === "box" && val_cell(v, j) === null) {
      if (fl.brwl.has(w)) {
        die("an owned use of a borrow");
      }
      arr_flush(fl, w);
    }
    return w;
  });
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
    const gs = arms.flatMap(read);
    return val_new(gs.flatMap((g) => g.ws), lay,
      gs.flatMap((g) => g.ws.map((_, n) => val_cell(g, n))));
  }
  const out = emit_dst(fl, lay, "o").ws;
  const t = emit_alias(fl, sel, "t");
  const cells = arms.map((): (Cell | null)[] => out.map(() => null));
  const bodies = arms.map((arm, i) => () => {
    file_push(fl, `${out[0]} = ${i};`);
    read(arm).forEach((g, j) => g.ws.forEach((w, n) => {
      const at = arm.fs[j].at + n;
      file_push(fl, `${out[at]} = ${w};`);
      cells[i][at] = val_cell(g, n);
    }));
  });
  emit_chain(fl, (i) => cond(t, i),
    stuck ? [...bodies, () => emit_stuck(fl)] : bodies);
  const av = out.map((o, at): Cell | null => {
    const cs = cells.map((c) => c[at]);
    const one = cs[0];
    if (one !== null && cs.every((c) => c?.arr === one.arr
      && c.at === one.at)) {
      return one;
    }
    cs.forEach((c, i) => {
      if (c !== null) {
        block(fl, `if (${cond(t, i)}) {`,
          () => file_push(fl, `${o} = blk_keep(e, ${c.at});`));
      }
    });
    return null;
  });
  return val_new(out, lay, av);
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
    return val_new(v.ws, lay, v.av);
  }
  const t = emit_alias(fl, v.ws[0], "u");
  return val_arms(fl, lay, t, (_, i) =>
    `term_aux(${t}) == ${cid_reg(fl, lay.arms![i].k)}`, (arm) => {
    const fs = node_fields(fl, t, lay_node(fl.book, arm.k), v);
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

function arr_flush(fl: File, a: string): void {
  for (const [p, b] of fl.uses) {
    const av = b.val.av ?? [];
    if (av.some((c) => c?.arr === a)) {
      const ws = b.val.ws.map((w, j) => av[j]?.arr === a
        ? val_keep(fl, av[j] as Cell) : w);
      fl.uses.set(p, { ...b, val: val_new(ws, b.val.lay,
        av.map((c) => c?.arr === a ? null : c)) });
    }
  }
}

function arr_lay(el: Lay): Lay {
  return lay_pack([{ k: "Tuple",
    fs: [{ at: 0, lay: BOX }, { at: 1, lay: el }] }]);
}

function arr_cells(fl: File, a: string, at: string, el: Lay,
  own: boolean): Val {
  const { arr } = lay_arr(el);
  const ws = emit_hold(fl, el.ks.map((_, j) =>
    `blk_read(e.mem, ${Number(arr)}, term_loc(${a}), ${at} + ${j})`), "c",
  el.ks);
  const av = el.ks.map((k, j): Cell | null => k === "box" && !own
    ? { arr: a, at: `term_loc(${a}) + ${at} + ${j}` } : null);
  return val_new(ws, el, av);
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
        const got = arr_cells(fl, a, at, el, false);
        return val_new([a, ...got.ws], arr_lay(el), [null, ...got.av ?? []]);
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

function bind_pop(fl: File, x: HTerm): Val {
  const p = probe_of(x);
  const b = fl.uses.get(p);
  if (b === undefined) {
    die("an unbound binder: " + p.k);
  }
  if (!b.val.lay.ks.includes("box")) {
    return b.val;
  }
  if (b.n <= 1) {
    fl.uses.delete(p);
    return b.val;
  }
  fl.uses.set(p, { ...b, n: b.n - 1 });
  return val_new(b.val.ws.map((w, j) => {
    const cell = val_cell(b.val, j);
    if (cell !== null) {
      return val_keep(fl, cell);
    }
    if (b.val.lay.ks[j] === "box" && !fl.brwl.has(w)) {
      file_push(fl, `${w} = term_keep(e, ${w});`);
    }
    return w;
  }), b.val.lay);
}

function bind_uses(fl: File, p: Probe, v: Val, b: HTerm): HTerm {
  const n = term_use(term_uses(fl, b), p);
  if (n === 0 && v.ws.length > 0 && !v.ws.some((w) => fl.brwl.has(w))) {
    val_sink(fl, v);
  } else {
    fl.uses.set(p, { val: v, n: Math.max(n, 1) });
  }
  return b;
}

function bind_arm(fl: File, h: HTerm, hs: HTerm[]): void {
  for (const [p, b] of [...fl.uses]) {
    const use = term_use(term_uses(fl, h), p);
    const mx = hs.reduce((m, h2) =>
      Math.max(m, term_use(term_uses(fl, h2), p)), 0);
    if (mx > use) {
      if (use === 0) {
        val_sink(fl, b.val);
        fl.uses.delete(p);
      } else {
        fl.uses.set(p, { ...b, n: use });
      }
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

function emit_frame(fl: File, words: string[], next: string | null): void {
  const ws = [...words, ...next === null ? [] : [seg_ref(fl, next)]];
  file_push(fl, `WL_ROOM(${ws.length});`);
  ws.forEach((w, i) => file_push(fl, `STK(${i}) = ${w};`));
  file_push(fl, `WL_PUSHN(${ws.length});`);
}

function emit_held(fl: File): Set<string> {
  return new Set(fl.seg.params.slice(0,
    fl.seg.params.length - (fl.seg.frame?.resw ?? 0)));
}

function emit_res(fl: File, ws: string[]): void {
  fl.resw = Math.max(fl.resw, ws.length);
  ws.forEach((w, j) => file_push(fl, `res[${j}] = ${w};`));
}

function emit_step(fl: File, ck: Call): void {
  const vs = emit_vals(fl, ck.k, ck.args);
  const n = vs.length - 1;
  const ws = emit_args(fl, ck.k, vs.slice(0, n), emit_held(fl));
  const rs = val_own(fl, val_to(fl, vs[n], def_lays(fl, ck.k)[n]));
  spare_flush(fl);
  emit_frame(fl, ws, null);
  emit_res(fl, rs);
  file_push(fl, `WL_JMP(${seg_ref(fl, seg_fid(ck.k))});`);
}

function emit_bang(fl: File, ck: Call, args: string[]): void {
  const fid = seg_fid(ck.k);
  file_push(fl, `return term_tsk(${fid}, ${emit_task(fl, fid, 0, args)});`);
}

function emit_jump(fl: File, args: string[], k: Bend.Name): void {
  if (fl.seg.def !== k) {
    args.forEach((a, i) => file_push(fl, `${reg(i)} = ${a};`));
    return file_push(fl, `WL_JMP(${seg_ref(fl, seg_fid(k))});`);
  }
  fl.seg.spin = true;
  emit_hold(fl, args, "j", fl.seg.ks).forEach((j, i) => {
    file_push(fl, `${fl.seg.params[i]} = ${j};`);
  });
  file_push(fl, "WL_AGAIN;");
}

function emit_vals(fl: File, k: Bend.Name, args: HTerm[]): Val[] {
  const lent = fl.brw.get(k) ?? [];
  return args.map((a, i) => {
    const x = Bend.term_strip(a);
    const b = lent[i] === true && x.$ === "Var"
      ? fl.uses.get(probe_of(x)) : undefined;
    return b === undefined ? emit_expr(fl, a, null) : b.val;
  });
}

function emit_args(fl: File, k: Bend.Name, vs: Val[],
  skip = new Set<string>()): string[] {
  const lent = fl.brw.get(k) ?? [];
  const lays = def_lays(fl, k);
  const live = fl.live.get(k);
  return vs.flatMap((v, i) => {
    if (skip.size > 0 && v.ws.every((x) => skip.has(x))) {
      return [];
    }
    const w = val_to(fl, v, lays[i]);
    return lent[i] === true ? w.ws : val_own(fl, w, live?.[i]);
  });
}

function emit_call(fl: File, ck: Call, km: Call | null): void {
  const cargs = emit_args(fl, ck.k, emit_vals(fl, ck.k, ck.args));
  const step = fl.slots.has(km?.k as string);
  const cexps = km ? emit_args(fl, km.k, emit_vals(fl, km.k,
    km.args.slice(0, -1)), step ? emit_held(fl) : new Set()) : [];
  spare_flush(fl);
  if (km !== null && step) {
    emit_frame(fl, cexps, seg_fid(km.k));
  } else if (km !== null) {
    const kf = seg_fid(km.k);
    emit_chain(fl, () => "seq", [() => emit_frame(fl, cexps, kf), () => {
      file_push(fl,
        `WL_CONT = term_tsk(${kf}, ${emit_task(fl, kf, 1, cexps)});`);
      file_push(fl, `WL_IDX = ${cexps.length};`);
      if (ck.bang) {
        emit_bang(fl, ck, cargs);
      }
    }]);
  } else if (ck.bang) {
    block(fl, "if (!seq) {", () => emit_bang(fl, ck, cargs));
  }
  emit_jump(fl, cargs, ck.k);
}

function emit_put(fl: File, dst: Dst, v: Val): void {
  if (dst === null) {
    spare_flush(fl);
    const ws = val_own(fl, val_to(fl, v, def_ret(fl, fl.seg.def)));
    emit_res(fl, ws);
    file_push(fl, `WL_RETN(${ws.length});`);
  } else {
    val_own(fl, val_to(fl, v, dst.lay)).forEach((w, j) => {
      file_push(fl, `${dst.ws[j]} = ${w};`);
    });
  }
}

function emit_open(fl: File, x: HLet): HTerm {
  const o = term_open(x);
  x.k.forEach((k, j) => {
    const v = val_hold(fl, emit_expr(fl, x.v[j], null), k);
    bind_uses(fl, o.ps[j], v, o.b);
  });
  return o.b;
}

function emit_fuse(fl: File, ck: Call, dst: Dst): void {
  const tld = fl.book.tlds[ck.k] as Def;
  const doms = def_get_params(fl.book, tld);
  const ers = ck.all.filter((_, i) =>
    i < doms.length && !quant_live(doms[i][0]));
  const args = emit_vals(fl, ck.k, ck.args);
  if (!flat_of(fl, ck.k)) {
    const lent = fl.brw.get(ck.k) ?? [];
    const vs = fl.mint.has(ck.k) ? args
      : val_split(emit_args(fl, ck.k, args), def_lays(fl, ck.k));
    const mine = vs.flatMap((v, i) => lent[i] !== true ? [] : v.ws.filter(
      (w, j) => v.lay.ks[j] === "box" && !fl.brwl.has(w)));
    mine.forEach((w) => fl.brwl.add(w));
    emit_body(fl, tld.h as HTerm, tld.T, ers, vs, dst);
    return mine.forEach((w) => fl.brwl.delete(w));
  }
  const out = emit_dst(fl, def_ret(fl, ck.k));
  const name = emit_native(fl, ck, ers);
  const ws = emit_args(fl, ck.k, args);
  const o = name_local(fl, "o");
  file_push(fl, `Term ${o}[${out.ws.length}];`);
  block(fl, `if (${name}(${["e", o, ...ws].join(", ")}) == 0) {`, () => {
    file_push(fl, "return 0;");
  });
  out.ws.forEach((v, j) => file_push(fl, `${v} = ${o}[${j}];`));
  emit_put(fl, dst, out);
}

function emit_params(fl: File, k: Bend.Name): Val[] {
  const lays = def_lays(fl, k);
  const names = live_doms(fl.book, fl.book.tlds[k] as Bend.Def)
    .map(([, n]) => n);
  const vals = val_split(lays.flatMap((l, i) =>
    l.ks.map(() => name_local(fl, names[i]))), lays);
  const brw = fl.brw.get(k)!;
  vals.forEach((v, i) => v.ws.forEach((w, j) => {
    if (brw[i] && lays[i].ks[j] === "box") {
      fl.brwl.add(w);
    }
  }));
  fl.fuel = 64;
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
  Object.assign(fl, { spares: [], tab: 2, uses: new Map(),
    brwl: new Set(fl.brwl) });
  const vals = emit_params(fl, ck.k);
  const seg = seg_new(ck.k, false, vals.flatMap((v) => v.ws), 1,
    vals.flatMap((v) => v.lay.ks));
  fl.seg = seg;
  const dst = { ws: ret.ks.map(() => name_local(fl, "v")), lay: ret };
  emit_body(fl, tld.h as HTerm, tld.T, ers, vals, dst);
  fl.spins.push([name, [`HOT Term ${name}(Env e, THR Term* o${
    seg.params.map((p, i) => `, ${lay_c(seg.ks[i])} ${p}`).join("")}) {`,
  "  u32 wpoll = 0;",
  ...dst.ws.map((v, j) => `  ${lay_c(ret.ks[j])} ${v} = 0;`),
  "  WL_SPIN", ...seg.lines, "    break;", "  }",
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
  const args = m.args.map((a) => emit_expr(fl, a, null));
  if (arr_call(fl, k, m.all)) {
    return arr_op(fl, eff_name(k), lay_of(fl.book, m.all[0]), args);
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
    const vs = flds.map((f) => emit_expr(fl, f, null));
    return val_new([vs.length === 1 && vs[0].ws.length > 1
      ? `(${vs[0].ws.map((w, i) => `((u64)${w} << ${i})`).join(" | ")})`
      : tpl(fn, vs.map(val_word))], lay);
  }
  if (adt.k === "Array") {
    const el = lay_of(fl.book, adt.x[0]);
    const vs = flds.map((f) => emit_expr(fl, f, null));
    return val_new([x.k === "ALeaf" ? arr_new(fl, "0", vs[0], el)
      : `blk_node(e, ${val_own(fl, vs[0])[0]}, ${val_own(fl, vs[1])[0]})`],
    BOX);
  }
  if (lay_box(lay)) {
    return val_new([node_build(fl, x.k, (j) =>
      emit_expr(fl, flds[j], null))], BOX);
  }
  const arm = lay_arm(lay, x.k);
  const ws = lay.ks.map((_, j) => j === 0 && lay.arms!.length > 1
    ? String(lay.arms!.indexOf(arm)) : "0");
  const av: (Cell | null)[] = lay.ks.map(() => null);
  flds.forEach((f, j) => {
    const v = val_to(fl, emit_expr(fl, f, null), arm.fs[j].lay);
    v.ws.forEach((w, n) => {
      ws[arm.fs[j].at + n] = w;
      av[arm.fs[j].at + n] = val_cell(v, n);
    });
  });
  return val_new(ws, lay, av);
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
      const b = fl.fuel > 0 ? emit_unfold(fl, s) : null;
      fl.fuel -= Number(b !== null);
      return b;
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
      const g = m.t;
      if (g.$ !== "Ref" && m.args.length === 0) {
        return emit_expr(fl, g, ty);
      }
      if (g.$ !== "Ref") {
        die(`a ${g.$}-headed spine`);
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
      if (tld?.$ === "Def" && tld.v === null && tld.i === undefined) {
        die(`a live call into the law ${g.k}`);
      }
      if (m.args.length !== def_live(fl, tld as Bend.Def) - 1) {
        die("an under-applied def value: " + g.k);
      }
      const fid = seg_ref(fl, seg_fid(g.k));
      const lays = def_lays(fl, g.k);
      const exprs = m.args.flatMap((a, i) =>
        val_own(fl, val_to(fl, emit_expr(fl, a, null), lays[i])));
      return val_new([`term_clo(${fid}, ${exprs.length === 0 ? 0 : node_fill(
        fl, "nd", `heap_alloc(e, cls_fit(${exprs.length}))`, exprs)})`], BOX);
    }
    case "Ctr": return emit_ctr(fl, x, ty);
    case "Let": return emit_expr(fl, emit_open(fl, x), null);
    case "Sub": case "Lam": case "Mat": case "Efq": case "Rwt": case "Hol":
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
  switch (x.$) {
    case "Lam": {
      const all = ty_all(fl.book, ty) ?? die("an untyped binder");
      if (!quant_live(all.q)) {
        const t = ers[0] ?? DUMMY;
        return emit_body(fl, x.f(t), all.B(t), ers.slice(1), args, dst);
      }
      const o = term_open(x);
      const v = val_hold(fl, val_to(fl, args[0], lay_of(fl.book, all.A)), x.k);
      return emit_body(fl, bind_uses(fl, o.ps[0], v, o.b), all.B(DUMMY), ers,
        args.slice(1), dst);
    }
    case "Mat":
    case "Efq": {
      return emit_match(fl, x, ty, ers, args, dst);
    }
    case "Let": {
      if (x.k.length >= 2) {
        return emit_fork(fl, x);
      }
      const vc = call_kind(fl, x.v[0]);
      if (vc !== null && !flat_call(fl, x.v[0])) {
        return emit_call(fl, vc, call_kind(fl, term_open(x).b)!);
      }
      return emit_body(fl, emit_open(fl, x), null, ers, [], dst);
    }
    default: {
      const ck = call_kind(fl, x);
      if (ck === null) {
        return emit_put(fl, dst, emit_expr(fl, x, ty));
      }
      const self = fl.seg.def === ck.k;
      if (dst === null && fl.slots.has(ck.k)) {
        return emit_step(fl, ck);
      }
      const par = dst === null && fl.mint.get(ck.k) === false;
      const once = fl.mint.get(ck.k) === true || (fl.sites.get(ck.k)
        === 1 && !fl.mint.has(ck.k) && !fl.dyn.has(ck.k)
        && ck.bang !== true && !def_foreign(fl.book.tlds[ck.k]));
      if (!self && !par && (flat_call(fl, x) || (dst === null && once))) {
        return emit_fuse(fl, ck, dst);
      }
      return emit_call(fl, ck, null);
    }
  }
}

function emit_fork(fl: File, x: HLet): void {
  const n = x.k.length;
  const o = term_open(x);
  const calls = x.v.map((v) => call_kind(fl, v)!);
  const jc = call_kind(fl, o.b) as Call;
  const k1 = fl.forks.get(o.ps[0]) as Bend.Name;
  const alias = (w: string) => emit_alias(fl, w, "a");
  const margs = calls.map((c) =>
    emit_args(fl, c.k, emit_vals(fl, c.k, c.args)).map(alias));
  const caps = emit_args(fl, jc.k,
    emit_vals(fl, jc.k, jc.args.slice(0, -n))).map(alias);
  spare_flush(fl);
  const kj = seg_fid(jc.k);
  block(fl, "if (!seq) {", () => {
    const jn = emit_task(fl, kj, n, caps);
    const jt = `term_tsk(${kj}, ${jn})`;
    let idx = caps.length;
    calls.forEach((c, j) => {
      const fj = seg_fid(c.k);
      file_push(fl, `e.mem[${jn} + ${idx}] = term_tsk(${fj}, ${
        emit_task(fl, fj, 0, margs[j], jt, idx)});`);
      idx += def_ret(fl, c.k).ks.length;
    });
    file_push(fl, `return ${jt};`);
  });
  emit_frame(fl, [...margs.slice(1).flat(), ...caps], seg_fid(k1));
  emit_jump(fl, margs[0], calls[0].k);
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
          () => node_fields(fl, sw, lay_node(fl.book, k), s, true)];
      }
      return [`${sw} == ${lay.arms!.indexOf(lay_arm(lay, k))}`, h,
        () => lay_arm(lay, k).fs.map((f) => val_field(s, f))];
    });
  if (ls === null && (arms.length < total
    || Bend.term_strip(end).$ !== "Efq")) {
    lv.push(["", end, () => [s]]);
  }
  const hs = lv.map(([, h]) => h);
  const spares = fl.spares;
  const arms2 = lv.map(([, h, fs]) => () => {
    fl.spares = spares.slice();
    const uses = new Map(fl.uses);
    bind_arm(fl, h, hs);
    emit_body(fl, h, null, ers, [...fs(), ...rest], dst);
    if (dst !== null) {
      spare_flush(fl);
    }
    fl.spares = dst === null ? spares : [];
    fl.uses = uses;
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
  fl.fresh = new Map();
  fl.spares = [];
  fl.uses = new Map();
  fl.local = new Set();
  fl.brwl = new Set();
  memo_gc();
  const vals = emit_params(fl, k);
  const seq = fl.mint.get(k) === true;
  const resw = seq ? vals.at(-1)?.ws.length ?? 0 : 0;
  fl.seg = seg_new(k, seq, vals.flatMap((v) => v.ws), resw,
    vals.flatMap((v) => v.lay.ks));
  fl.segs.push(fl.seg);
  const st = fl.slots.get(k);
  if (st !== undefined) {
    const live = (cs: Capture[]) => cs.filter((c) => quant_live(c.q));
    const pos = new Map<Probe, number>();
    const depth = live(st.L).reduce((n, c) =>
      (pos.set(c.p, n), n + lay_of(fl.book, c.A).ks.length), 0);
    fl.seg.frame = { resw, pop: st.last ? depth : 0,
      at: live((fl.kept.get(k) as Capture[]).slice(0, -1)).flatMap((c) =>
        lay_of(fl.book, c.A).ks.map((_, j) =>
        pos.get(c.p)! + j - depth)) };
  }
  fl.tab = 3;
  emit_body(fl, tld.h as HTerm, tld.T, [], vals, null);
  fl.tab = 2;
  if (fl.seg.spin) {
    fl.seg.lines = ["    WL_SPIN", ...fl.seg.lines, "    WL_SPUN"];
  } else {
    fl.seg.lines = fl.seg.lines.map((l) => l.slice(2));
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
    fl.seg = seg_new(k, false, qp);
    fl.segs.push(fl.seg);
    cid_reg(fl, k, qp.length);
    file_push(fl, `res[0] = ${ctr_build(fl, k, qp)};`);
    file_push(fl, "WL_RETN(1);");
  }
}

function compile_tables(fl: File, entries: Seg[]): string[] {
  const defs: string[] = [];
  for (const ms of [[...fl.cids.keys()].map(cid_mac),
    [...entries.map((s) => s.fid), "FID_EXIT"]]) {
    const dup = ms.find((m, i) => ms.indexOf(m) < i);
    if (ms.length > 65536 || dup !== undefined) {
      die(dup === undefined ? "an id over 65535"
        : "two names mangle to " + dup);
    }
    const w = Math.max(...ms.map((m) => m.length));
    defs.push(...ms.map((m, i) => `#define ${m.padEnd(w)} ${i}`), "");
  }
  const table = (nm: string, vals: number[]) => {
    if (vals.some((v) => v > 255)) {
      die("an arity over 255");
    }
    defs.push(`CONSTV u8 ${nm}[] = { ${vals.join(", ")} };`, "");
  };
  table("FID_ARITY_T", entries.map((s) => s.params.length));
  table("FID_BANGS_T", entries.map((s) => Number(fl.bangs.has(s.def))));
  const nofk = new Set(done_defs(fl).filter(([, tld]) => !term_any(fl,
    tld.h as HTerm, (s) => (s.$ === "Let" && s.k.length >= 2)
      || call_kind(fl, s)?.k === CLO_APPLY)).map(([k]) => k));
  for (let n = -1; n !== nofk.size;) {
    n = nofk.size;
    for (const k of nofk) {
      for (const g of REFS.get(k) as Set<Bend.Name>) {
        if (REFS.has(g) && !nofk.has(g)) {
          nofk.delete(k);
        }
      }
    }
  }
  table("FID_NOFK_T", entries.map((s) => Number(nofk.has(s.def))));
  table("FID_SEQK_T", entries.map((s) => Number(s.frame !== null)));
  table("FID_RESW_T", entries.map((s) => s.frame?.resw ?? 0));
  table("CID_ARITY_T", [...fl.cids.values()].map((c) => c[0]));
  table("CID_BOXN_T", [...fl.cids.values()].map((c) => c[1]));
  const bank = (segs: Seg[]): string[] => {
    const n = Math.max(1, ...segs.filter((s) => s.frame === null)
      .map((s) => s.params.length));
    const ns = [...Array(Math.min(n, BANK)).keys()];
    const load = [...ns].reverse().map((r) =>
      `    case ${r + 1}: r${r} = e.mem[a + ${r}]; \\\n`).join("");
    const pass = ns.map((i) =>
      `    case ${i}: r${i} = res[0]; \\\n      break; \\\n`).join("");
    const rx = n > BANK;
    return [`#define WL_BANK Term ${ns.map((i) => "r" + i).join(", ")};`
      + (rx ? ` Term rx[${n - BANK}];` : ""), "",
      `#define WL_LOAD \\\n` + (rx ? `  for (u32 wi = ${BANK}; wi < war;`
      + ` wi += 1) { \\\n    rx[wi - ${BANK}] = e.mem[a + wi]; \\\n  } \\\n`
      : "") + `  switch (war < ${BANK} ? war : ${BANK}) { \\\n${load}  }`, "",
      `#define WL_LAST \\\n` + (rx ? `  if (war >= ${BANK}) { \\\n`
      + `    rx[war - ${BANK}] = res[0]; \\\n  } \\\n` : "")
      + `  switch (war) { \\\n${pass}  }`, ""];
  };
  defs.push(`#define IO_HOTS ${"SCon Tuple Done Fail Con Some".split(" ")
    .reduce((m, k, i) => m | (fl.hot.has(k) ? 1 << i : 0), 0)}`, "");
  defs.push(`#define WL_RESW ${fl.resw}`,
    `#define BANGS   ${fl.bangs.size}`, "");
  defs.push("#if DEVICE", ...bank(entries.filter((s) => !s.host)), "#else",
    ...bank(entries), "#endif", "",
    `#define WL_LABELS ${entries.map((s) =>
      "&&L_" + (s.dead ? "FID_EXIT" : s.fid))
      .join(", ")}, &&L_FID_EXIT`);
  return defs;
}

function compile_segs(fl: File): string {
  return fl.segs.filter((s) => !s.dead).map((seg) => {
    const out: string[] = [`  WL_CASE(${seg.fid})`, "  {"];
    const fr = seg.frame;
    if (fr !== null && fr.pop > 0) {
      out.push(`    WL_POPN(${fr.pop});`);
    }
    const n = seg.params.length;
    seg.params.forEach((p, i) => {
      let src = reg(i);
      if (fr !== null) {
        src = i >= n - fr.resw ? `res[${i - (n - fr.resw)}]`
          : `STK(${fr.at[i] + fr.pop})`;
      }
      out.push(`    ${lay_c(seg.ks[i])} ${p} = ${src};`);
    });
    out.push(...seg.lines);
    out.push("  }");
    return (seg.host ? ["#if !DEVICE", ...out, "#endif"] : out).join("\n");
  }).join("\n\n");
}

export function compile_book(book: Bend.Book,
  mains = io_ports(book, ".c", (m) => compile_book(book, [m]))): string {
  const cb = carb_book(book, mains.map(([, k]) => k));
  facts_build(cb);
  const fl = file_new(cb, "Term");
  for (const k of ("Tuple SNil SCon Chr Unit WCon Emit Halt Fail Done File"
    + " Socket Listener None Some Window Nil Con Key Mouse Move Close Chan"
    + " True False")
    .split(" ")) {
    cid_reg(fl, k);
  }
  for (const [k, tld] of done_defs(cb)) {
    compile_def(fl, k, tld);
  }
  compile_reqs(fl);
  const reach = (from: Bend.Name[], set = new Set<string>()): Set<string> => {
    const grab = (fid: string) => set.has(fid) || (set.add(fid)
      && (fl.segs.find((s) => s.fid === fid)?.refs
        ?? fl.spins.find((s) => s[0] === fid)?.[2])?.forEach(grab));
    from.forEach((k) => grab(seg_fid(k)));
    return set;
  };
  const roots = mains.map(([, k]) => k);
  const live = reach(roots);
  const dev = reach([...fl.bangs, ...[...fl.dyn].filter((k) =>
    !roots.includes(k))]);
  fl.segs = fl.segs.filter((s) =>
    live.has(s.fid) || def_foreign(cb.book.tlds[s.def]));
  const clo = live.has("FID_CLO_APPLY");
  for (const s of fl.segs) {
    s.dead = !live.has(s.fid) || (!clo && def_foreign(cb.book.tlds[s.def]));
    s.host = !dev.has(s.fid);
  }
  fl.spins = fl.spins.filter(([n]) => live.has(n));
  const entries = [...fl.segs, { ...seg_new("io_emit", false, [""]),
    dead: !clo }, ...clo ? [seg_new("clo_apply", false, ["", ""])] : []];
  const defs = compile_tables(fl, entries);
  defs.push("#if !DEVICE", `static const char* MAIN_NAMES[] = { ${mains.map(
    ([n]) => JSON.stringify(n)).join(", ")} };`,
  `static const Fid MAIN_FIDS[] = {
    ${mains.map(([, k]) => seg_fid(k)).join(", ")} };`, "#endif");
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
  return x.f(x.v.map((v, j): HTerm => {
    if (!quant_live(x.q[j])) {
      return v;
    }
    return Bend.Var(emit_hold(fl, [js_expr(fl, v, null)], x.k[j])[0], 0);
  }));
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
    case "Sub": case "Lam": case "Mat": case "Efq": case "Rwt": case "Hol":
      die("cannot compile a " + x.$ + " node");
    default: return "null";
  }
}

function js_func(fl: File, tm: HTerm, ty0: HTerm | null,
  args: string[]): void {
  const [x, ty] = ty_peel(tm, ty0);
  if (x.$ === "Lam") {
    const all = ty_all(fl.book, ty) ?? die("an untyped lambda");
    const v: HTerm = Bend.Var(!quant_live(all.q) ? "null"
      : emit_alias(fl, args[0] ?? die("a lambda past its arity"), x.k), 0);
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
  const ck = call_kind(fl, x);
  file_push(fl, "return " + (ck === null ? js_expr(fl, x, ty)
    : js_call(fl, ck.k, ck.args, true)) + ";");
}

function js_def(fl: File, k: Bend.Name, def: Def): void {
  fl.fresh = new Map();
  fl.fuel = 64;
  if (intr_of(fl, k.split("$")[0], true) !== undefined) {
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
  for (const k of outs === null ? new Set(book.order) : cb.done) {
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

export function js_book(book: Bend.Book,
  mains = io_ports(book, ".js", (m) => js_book(book, [m]))): string {
  return js_lib(book, mains.map(([, k]) => k), null) + "\n" + RUNTIME_MAIN
    + "\nio_exit({" + mains.map(([n, k]) => JSON.stringify(n) + ": "
      + js_sat(k)).join(", ") + "}, cli(process.argv.slice(2)));";
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
#elif BEND_CUDA
#include <cuda.h>
#include <nvrtc.h>
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
#define HOT     inline
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
#elif defined(__CUDACC_RTC__)
#define DEV     volatile
#define DEVL
#define GRP
#define GA32    __shared__ u32
#define THR
#define INLINE  static inline
#define HOT     static inline
#define OUTLINE static __attribute__((noinline))
#define CONSTV  static const
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
#define DEVL
#define GRP
#define THR
#define INLINE  static inline
#define HOT     static inline __attribute__((always_inline))
#define OUTLINE static __attribute__((noinline, cold))
#define CONSTV  static const
#define DEVICE  0
#define CLZ(x)  (u32)__builtin_clz(x)
#define FENCE() __atomic_thread_fence(__ATOMIC_SEQ_CST)
#endif

#if DEVICE
#define LOCK(l)
#define UNLOCK(l)
#define WL_CASE(F) case F:
#define WL_JMP(F)  { fid = (F); break; }
#define WL_DYN     WL_JMP
#define WL_SPIN \
  for (;;) { \
    if (err_spun(e.mem, &wpoll)) { \
      return 0; \
    }
#define WL_SPUN    } break;
#else
#define LOCK(l)    while (__atomic_exchange_n(&(l), 1, __ATOMIC_ACQUIRE)) {}
#define UNLOCK(l)  __atomic_store_n(&(l), 0, __ATOMIC_RELEASE)
#define WL_CASE(F) L_##F: ;
#define WL_JMP(F)  goto L_##F
#define WL_DYN(F)  { fid = (F); __asm__ volatile("" :: "i"(__LINE__)); \
  goto *wl_lbl[fid]; }
#define WL_SPIN    for (;;) {
#define WL_SPUN    }
#endif
#define WL_AGAIN   continue
#define WL_POP()   { sp -= LANE_STEP; WL_DYN((Fid)STK(0)); }

#define LANE_STEP (DEVICE ? (int64_t)CUBE : 1)
#define STK(I)    sp[(int64_t)(I) * LANE_STEP]

#define WL_RETN(N)  { resn = (N); WL_POP(); }
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

#if BEND_METAL
static id<MTLDevice>               gpu_dev;
static id<MTLCommandQueue>         gpu_que;
static id<MTLLibrary>              gpu_lib;
static id<MTLComputePipelineState> gpu_grow_pso;
static id<MTLComputePipelineState> gpu_work_pso;
static id<MTLBuffer>               gpu_buf;
#elif BEND_CUDA
static CUdevice   gpu_dev;
static CUmodule   gpu_lib;
static CUfunction gpu_grow_pso;
static CUfunction gpu_work_pso;
#endif
static bool io_gpu;
static Stk  io_stk;

static const char* CLI_HELP =
  "usage: %s [program] [options]\n"
  "  --threads N        worker threads, up to 128 (default: the CPU count)\n"
  "  --parallel on|off  off means one thread and no GPU (default: on)\n"
  "  --gpu on|off       send ! calls to the GPU (default: on if present)\n"
  "  --gpu-memory 4GB   device span, in MB or GB (default: 2GB on Metal)\n"
  "  --help             show this text\n";

#endif

// Tables
// ======

#define TAB_AT(T, S, I) T[S < I ? S : I]

// Fid
// ===

#define fid_arity(x) ((u32)FID_ARITY_T[x])

#define fid_bangs(x) ((bool)FID_BANGS_T[x])

#define fid_nofk(x) ((bool)FID_NOFK_T[x])

#define fid_seqk(x) ((bool)FID_SEQK_T[x])

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
#define a32_xor(p, v)    atomic_fetch_xor_explicit(A32(p), v, RLX)
#define a32_swp(p, e, v) \
  atomic_compare_exchange_weak_explicit(A32(p), e, v, RLX, RLX)

#elif defined(__CUDACC_RTC__)

#define a32_load(p)     (*(p))
#define a32_store(p, v) (*(p) = (v))
#define a32_add(p, v)   atomicAdd((u32*)(p), v)
#define a32_sub(p, v)   atomicSub((u32*)(p), v)
#define a32_xor(p, v)   atomicXor((u32*)(p), v)

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
#define a32_xor(p, v)       __atomic_fetch_xor(p, v, __ATOMIC_RELAXED)
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

HOT Loc heap_alloc(Env e, Cls cls) {
  Loc h = ALC_AT(e, cls);
  if (h) {
    ALC_AT(e, cls)   = e.mem[h];
    ALC_LEN(e, cls) -= 1ull << cls;
    return h;
  }
  return heap_alloc_miss(e, cls);
}

HOT void heap_free(Env e, Cls cls, Loc loc) {
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

HOT void spare_free(Env e, Cls cls, Loc loc) {
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

INLINE Term rfc_out(Env e, Term t) {
  Loc      r = term_loc(t);
  DEV u32* p = a32_at(e.mem, r);
  if ((a32_sub_rel(p, 1) & RFC_CNT) != 1) {
    return 0;
  }
  a32_acq(p);
  Term s = (t & ~(RFC_BIT | LOC_MASK)) | (e.mem[r] >> 24);
  heap_free(e, 0, r);
  return s;
}

INLINE void rfc_bump(Env e, Loc r) {
  u32 c = a32_add(a32_at(e.mem, r), 1);
  if ((c & RFC_CNT) >= RFC_CNT - 1) {
    err_post(e.mem, ERR_RFCS);
  }
}

HOT Term term_keep(Env e, Term t) {
  if (term_rfc(t)) {
    rfc_bump(e, term_loc(t));
    return t;
  }
  if (term_triv(t)) {
    return t;
  }
  return rfc_wrap(e, t, 2);
}

HOT Loc term_peek(Env e, Term t) {
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
      t = rfc_out(e, t);
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

HOT void term_sink(Env e, Term t) {
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

HOT Loc ctr_take(Env e, Term t, u32 n, THR Term* out) {
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

INLINE void ring_skip(Corpus H, Ring r) {
  DEV u32* get = ring_get(H, r);
  a32_store(get, *get + 1);
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

INLINE Term ring_head(Corpus H, Ring r) {
  u32 get = *ring_get(H, r);
  DEV u32* lo = (DEV u32*)ring_slot(H, r, get);
  u32 hi = a32_load_acq(lo + 1);
  if ((hi >> 31) != ring_lap(get)) {
    return 0;
  }
  return (((u64)hi << 32) | a32_load(lo)) & ~RFC_BIT;
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

static Reply work_loop(Env e, Stk sp, Term t, bool seq) {
  Fid  fid;
  Term res[WL_RESW];
  u32  resn = 0;
  WL_BANK
  {
  fid = (u32)term_aux(t);
  Loc a   = term_loc(t);
  u32 war = fid_arity(fid);
  WL_FRAME(t)
  if (fid_seqk(fid)) {
    u32 rw = fid_resw(fid);
    for (u32 j = 0; j < WL_RESW; j += 1) {
      if (j < rw) {
        res[j] = e.mem[a + war - rw + j];
      }
    }
    WL_ARGS(a, war - rw + 1)
  } else {
    WL_LOAD
  }
  heap_free(e, cls_fit(war + 2), a);
  }
#if DEVICE
  u32 wpoll = 0;
  for (;;) {
  if (err_spun(e.mem, &wpoll)) {
    return 0;
  }
  switch (fid) {
#else
  static const void* wl_lbl[] = {
    WL_LABELS
  };
  goto *wl_lbl[fid];
#endif

// Segments
// ========

#ifdef FID_CLO_APPLY
  WL_CASE(FID_IO_EMIT)
  {
    Loc l = heap_alloc(e, 0);
    e.mem[l] = r0;
    res[0] = term_ctr(CID_EMIT, l);
    WL_RETN(1);
  }
#endif

#ifdef FID_CLO_APPLY
  WL_CASE(FID_CLO_APPLY)
  {
    Term fun = r0;
    res[0]   = r1;
    fid      = (Fid)term_aux(fun);
    u32 war  = fid_arity(fid) - 1;
    Loc a    = term_loc(fun);
    WL_LOAD
    if (war > 0) {
      heap_free(e, cls_fit(war), a);
    }
    WL_LAST
    WL_DYN(fid);
  }
#endif

  WL_CASE(FID_EXIT)
  {
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
      WL_ARGS(wa, wn - resn + 1)
      heap_free(e, cls_fit(wn + 2), wa);
      WL_DYN(wf);
    }
    Term rv[WL_RESW];
    for (u32 j = 0; j < WL_RESW; j += 1) {
      rv[j] = res[j];
    }
    return task_deliver(e.mem, cont, idx, rv, resn);
  }

#if DEVICE
  default: {
    err_post(e.mem, ERR_FIDS);
    return 0;
  }
  }
  }
#else
  err_post(e.mem, ERR_FIDS);
  return 0;
#endif
}

// Monk
// ====

INLINE u32 monk_run(Env e, Stk stk, Term t, bool seq, u32 base,
  u32 stride, Cursor cur) {
  u32 spin = 0;
  for (;;) {
    Reply r = work_loop(e, stk, t, seq);
    if (r == 0) {
      return 2;
    }
    if ((u32)e.mem[task_tail(r) + 1] == 0) {
      if (err_spun(e.mem, &spin)) {
        return 2;
      }
      if (stride != 0) {
        ring_push(e.mem, ring_pick(base, stride, cur), r);
        return 2;
      }
      t   = r;
      seq = false;
      continue;
    }
    task_deal(e.mem, r, base, stride, cur);
    return 1;
  }
}

INLINE u32 monk_grow(Env e, Stk stk, Ring rg, u32 put0, u32 base, u32 stride,
  Cursor cur) {
  Corpus H = e.mem;
  if (*ring_get(H, rg) == put0) {
    return 0;
  }
  Term t = ring_head(H, rg);
  if (t == 0 || fid_nofk((u32)term_aux(t))) {
    return 0;
  }
  ring_skip(H, rg);
  return monk_run(e, stk, t, false, base, stride, cur);
}

static void monk_work(Env e, Stk stk, Ring r) {
  Corpus H = e.mem;
  u32 put0 = a32_load(ring_put(H, r));
  while (*ring_get(H, r) != put0) {
    if (err_seen(H)) {
      return;
    }
    Term t = ring_head(H, r);
    if (t == 0) {
      continue;
    }
    ring_skip(H, r);
    monk_run(e, stk, t, true, r, 0, (Cursor)0);
  }
}

// Dev
// ===

// A kernel reserves TG_HOLD words of threadgroup memory, a length the
// host sets at each dispatch: one resident threadgroup per Apple core,
// the occupancy the pins were measured under (bitonic PAR-GPU 2.81 s
// -> 1.87 s; 2.85 s again with no threadgroup argument, lane 0's write
// keeps it). grow_dev runs at most CUBE_SIDE rounds, so a program that
// never fills a group still cuts at a kernel end.

#if DEVICE

INLINE void dev_hold(GRP volatile u64* hold, u32 lane) {
  if (lane == 0) {
    hold[0] = 0;
  }
}

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

#ifdef __METAL_VERSION__
kernel void grow_dev(Corpus H [[buffer(0)]],
  GRP volatile u64* hold [[threadgroup(0)]],
  u32 grids [[threadgroups_per_grid]],
  u32 row [[threadgroup_position_in_grid]],
  u32 lane [[thread_position_in_threadgroup]]) {
#else
extern "C" __global__ void grow_dev(Corpus H) {
  extern __shared__ volatile u64 hold[];
  u32 grids = gridDim.x;
  u32 row   = blockIdx.x;
  u32 lane  = threadIdx.x;
#endif
  u32  stride = grids == 1 ? CUBE_SIDE : 1;
  Ring rg  = row * CUBE_SIDE + stride * lane;
  Env  e   = { H, H + ALC_OFF + rg };
  dev_hold(hold, lane);
  GA32 tg_cur;
  GA32 tg_grew;
  GA32 tg_has;
  g32_ini(&tg_cur);
  g32_ini(&tg_grew);
  g32_ini(&tg_has);
  BAR();
  u32 seen_has  = 0;
  u32 seen_grew = 0;
  for (u32 turn = 0; turn < CUBE_SIDE; turn += 1) {
    u32 put0 = a32_load(ring_put(H, rg));
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
    if (monk_grow(e, (Stk)(H + STAK_OFF + rg), rg, put0, row * CUBE_SIDE,
      stride, &tg_cur) == 1) {
      g32_add(&tg_grew, 1);
    }
    BARD();
    u32 grew = g32_get(&tg_grew);
    if (grew == seen_grew) {
      break;
    }
    seen_grew = grew;
  }
  dev_cut(e);
}

#ifdef __METAL_VERSION__
kernel void work_dev(Corpus H [[buffer(0)]],
  GRP volatile u64* hold [[threadgroup(0)]],
  u32 tid [[thread_position_in_grid]],
  u32 lane [[thread_position_in_threadgroup]]) {
#else
extern "C" __global__ void work_dev(Corpus H) {
  extern __shared__ volatile u64 hold[];
  u32 lane = threadIdx.x;
  u32 tid  = blockIdx.x * CUBE_SIDE + lane;
#endif
  Env e = { H, H + ALC_OFF + tid };
  dev_hold(hold, lane);
  monk_work(e, (Stk)(H + STAK_OFF + tid), ring_flip(tid));
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
      ran   = monk_grow(e, stk, base + i, put0[i], base, 1, &cur);
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
          monk_work(e, stk, r * LINE + i);
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

#if !BEND_CUDA
#define gpu_map pool_mmap
#endif

#if BEND_METAL

static bool gpu_probe(void) {
  return (gpu_dev = MTLCreateSystemDefaultDevice()) != nil;
}

static id<MTLComputePipelineState> gpu_pipe(const char* name) {
  NSError* err = nil;
  id<MTLFunction> fn =
    [gpu_lib newFunctionWithName:[NSString stringWithUTF8String:name]];
  if (!fn) {
    err_fail(ERR_FAIL, name);
  }
  id<MTLComputePipelineState> pso =
    [gpu_dev newComputePipelineStateWithFunction:fn error:&err];
  if (!pso) {
    err_fail(ERR_FAIL, [[err localizedDescription] UTF8String]);
  }
  if ([pso maxTotalThreadsPerThreadgroup] < CUBE_SIDE) {
    err_fail(ERR_FAIL, "threadgroup too small");
  }
  return pso;
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
    NSError* err = nil;
    NSString* text = [NSString stringWithContentsOfFile:@__FILE__
      encoding:NSUTF8StringEncoding error:nil];
    if (!text) {
      err_fail(ERR_FAIL, "cannot read own source");
    }
    MTLCompileOptions* opts = [MTLCompileOptions new];
    opts.mathMode = MTLMathModeSafe;
    gpu_lib = [gpu_dev newLibraryWithSource:text options:opts error:&err];
    if (!gpu_lib) {
      err_fail(ERR_FAIL, [[err localizedDescription] UTF8String]);
    }
    gpu_grow_pso = gpu_pipe("grow_dev");
    gpu_work_pso = gpu_pipe("work_dev");
  }
}

static void gpu_kernel(id<MTLComputeCommandEncoder> enc,
  id<MTLComputePipelineState> pso, u32 groups) {
  [enc setComputePipelineState:pso];
  [enc setBuffer:gpu_buf offset:0 atIndex:0];
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
      gpu_kernel(enc, gpu_grow_pso, 1);
    }
    if (f < CUBE) {
      gpu_kernel(enc, gpu_grow_pso, CUBE_SIDE);
    }
    gpu_kernel(enc, gpu_work_pso, CUBE_SIDE);
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

static CUfunction gpu_pipe(const char* name) {
  CUfunction pso;
  if (cuModuleGetFunction(&pso, gpu_lib, name) != CUDA_SUCCESS) {
    err_fail(ERR_FAIL, name);
  }
  return pso;
}

static Corpus gpu_map(u64 bytes) {
  CUdeviceptr p = 0;
  if (cuMemAllocManaged(&p, bytes, CU_MEM_ATTACH_GLOBAL) != CUDA_SUCCESS) {
    err_fail(ERR_HEAP, "corpus reservation failed");
  }
  cuMemAdvise(p, bytes, CU_MEM_ADVISE_SET_PREFERRED_LOCATION, gpu_dev);
  return (Corpus)(uintptr_t)p;
}

static char* gpu_slurp(const char* path, long* len) {
  FILE* f = fopen(path, "rb");
  *len = f != NULL && fseek(f, 0, SEEK_END) == 0 ? ftell(f) : -1;
  char* buf = *len > 0 ? calloc((u64)*len + 1, 1) : NULL;
  bool  ok = buf != NULL && fseek(f, 0, SEEK_SET) == 0
    && fread(buf, 1, (u64)*len, f) == (u64)*len;
  if (f != NULL) {
    fclose(f);
  }
  if (!ok) {
    free(buf);
  }
  return ok ? buf : NULL;
}

static void gpu_stash(const char* path, const char* bin, size_t len) {
  FILE* out = fopen(path, "wb");
  if (out != NULL) {
    fwrite(bin, 1, len, out);
    fclose(out);
  }
}

static char* gpu_nvrtc(const char* text, const char* arch, size_t* len) {
  const char* opts[] = { arch, "--fmad=false", "-default-device" };
  nvrtcProgram prog;
  if (nvrtcCreateProgram(&prog, text, "bend.cu", 0, NULL, NULL)
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
  nvrtcGetCUBINSize(prog, len);
  char* bin = malloc(*len);
  if (bin == NULL || nvrtcGetCUBIN(prog, bin) != NVRTC_SUCCESS) {
    err_fail(ERR_FAIL, "cannot load the CUDA library");
  }
  nvrtcDestroyProgram(&prog);
  return bin;
}

static u64 gpu_span(void) {
  size_t span = 0;
  cuDeviceTotalMem(&span, gpu_dev);
  return span;
}

static void gpu_load(u64 bytes) {
  (void)bytes;
  long  len = 0;
  char* text = gpu_slurp(__FILE__, &len);
  if (text == NULL) {
    err_fail(ERR_FAIL, "cannot read own source");
  }
  int cc[2] = {0, 0};
  cuDeviceGetAttribute(cc,
    CU_DEVICE_ATTRIBUTE_COMPUTE_CAPABILITY_MAJOR, gpu_dev);
  cuDeviceGetAttribute(cc + 1,
    CU_DEVICE_ATTRIBUTE_COMPUTE_CAPABILITY_MINOR, gpu_dev);
  char arch[40];
  snprintf(arch, sizeof arch, "--gpu-architecture=sm_%d%d", cc[0], cc[1]);
  u64 key = 14695981039346656037ull;
  for (long i = 0; i < len; i += 1) {
    key = (key ^ (u8)text[i]) * 1099511628211ull;
  }
  const char* home = getenv("HOME") != NULL ? getenv("HOME") : ".";
  char path[4096];
  snprintf(path, sizeof path, "%s/.cache", home);
  mkdir(path, 0755);
  snprintf(path, sizeof path, "%s/.cache/bend", home);
  mkdir(path, 0755);
  snprintf(path, sizeof path, "%s/.cache/bend/%016llx_sm_%d%d.cubin",
    home, (unsigned long long)key, cc[0], cc[1]);
  long  bin_len = 0;
  char* bin = gpu_slurp(path, &bin_len);
  bool  hit = bin != NULL
    && cuModuleLoadDataEx(&gpu_lib, bin, 0, NULL, NULL) == CUDA_SUCCESS;
  if (!hit) {
    free(bin);
    size_t made = 0;
    bin = gpu_nvrtc(text, arch, &made);
    gpu_stash(path, bin, made);
    if (cuModuleLoadDataEx(&gpu_lib, bin, 0, NULL, NULL) != CUDA_SUCCESS) {
      err_fail(ERR_FAIL, "cannot load the CUDA library");
    }
  }
  free(text);
  free(bin);
  gpu_grow_pso = gpu_pipe("grow_dev");
  gpu_work_pso = gpu_pipe("work_dev");
}

static void gpu_kernel(CUfunction pso, u32 groups) {
  void* args[] = { &CORPUS };
  if (cuLaunchKernel(pso, groups, 1, 1, CUBE_SIDE, 1, 1, TG_HOLD * 8, NULL,
    args, NULL) != CUDA_SUCCESS) {
    err_fail(ERR_FAIL, "device launch failed");
  }
}

static void gpu_pass(u32 f) {
  if (f < CUBE_SIDE) {
    gpu_kernel(gpu_grow_pso, 1);
  }
  if (f < CUBE) {
    gpu_kernel(gpu_grow_pso, CUBE_SIDE);
  }
  gpu_kernel(gpu_work_pso, CUBE_SIDE);
  if (cuCtxSynchronize() != CUDA_SUCCESS) {
    err_fail(ERR_FAIL, "device fault");
  }
}

#else

#define gpu_probe() false
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
#define IO_EFFS 1024
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
//   | IoEff(fid, cid, run, ask)
typedef struct {
  u32    fid;
  u32    cid;
  Effect run;
  u32    ask;
} IoEff;

static IoRow io_sys_rows[IO_ROWS];
static u32   io_sys_next;
static u32   io_sys_free = IO_ROWS;
static lock  io_sys_lock = PTHREAD_MUTEX_INITIALIZER;
static IoEff io_eff_rows[IO_EFFS];
static u32   io_eff_len;
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
  if (io_eff_len >= IO_EFFS) {
    err_fail(ERR_FIDS, "the effect registry is full");
  }
  IoEff row = { fid, cid, run, need };
  io_eff_rows[io_eff_len] = row;
  io_eff_len += 1;
}

static IoEff* io_eff_at(bool clo, u32 key) {
  for (u32 i = 0; i < io_eff_len; i += 1) {
    IoEff* row = &io_eff_rows[i];
    if ((clo ? row->fid : row->cid) == key) {
      return row;
    }
  }
  return NULL;
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

OUTLINE char* io_cstr(Env e, Term s, u64* len) {
  u64   cap = 64;
  u64   n   = 0;
  char* buf = io_mem(malloc(cap));
  while (term_aux(s) == CID_SCON) {
    Term fb[2];
    spare_free(e, cls_fit(2), ctr_take(e, s, 2, fb));
    if (n + 2 > cap) {
      cap *= 2;
      buf = io_mem(realloc(buf, cap));
    }
    buf[n] = (char)fb[0];
    n += 1;
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
    n -= 1;
    s = io_node(e, CID_SCON, (uint8_t)p[n], s, IO_HOTS & 1);
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
//   | IoJob(what, word, cont, time, next, work, args)
typedef struct IoJob {
  IoEff*        what;
  u32           word;
  Term          cont;
  u64           time;
  struct IoJob* next;
  IoWork        work;
  Term          args[];
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
      io_push(jobs[i]->cont, jobs[i]->work.pack(e, &jobs[i]->work), false);
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

static void io_fire(Env e, IoJob* job) {
  Term x = job->what->run(e, job->args, &job->work);
  if (x == IO_WORK) {
    io_send(job);
    return;
  }
  if (x != IO_PARK) {
    io_push(job->cont, x, false);
  }
  free(job);
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
      io_fire(e, j);
    } else {
      at = &j->next;
    }
  }
  io_park_at = at;
}

static int io_step(Env e, Term op, Term x) {
  for (;;) {
    Term fs[257];
    u32  c   = (u32)term_aux(op);
    bool clo = term_tag(op) == TAG_CLO;
    u32  n   = clo ? fid_arity(c) - 1 : cid_arity(c);
    if (term_tag(op) == TAG_TSK) {
      op = corpus_eval(e.mem, op);
      continue;
    }
    IoEff* eff = io_eff_at(clo, c);
    spare_free(e, cls_fit(n), ctr_take(e, op, n, fs));
    if (c == (clo ? FID_IO_EMIT : CID_EMIT)) {
      term_drop(e, clo ? x : fs[0]);
      io_live -= 1;
      return -1;
    }
    if (!clo && c == CID_HALT) {
      io_errs(e, fs[1]);
      return (int)(u32)fs[0];
    }
    if (eff == NULL) {
      if (!clo) {
        err_fail(ERR_FIDS, "an alien request");
      }
      Loc a = task_node(e, c, TERM_HOLE, 0, 0);
      memcpy(e.mem + a, fs, n * sizeof(Term));
      e.mem[a + n] = x;
      op = corpus_eval(e.mem, term_tsk(c, a));
      continue;
    }
    n -= !clo;
    if (clo) {
      fs[n] = x;
    }
    u32 need = eff->ask;
    u32 word = (u32)fs[0];
    if (need & IO_READ) {
      word = (u32)io_sys_read(io_hand_p(e, fs[0]), 0);
      need = (int)word < 0 ? 0 : need;
    }
    IoWork w = { 0 };
    if (need == 0 && (x = eff->run(e, fs, &w)) != IO_WORK) {
      op = fs[n];
      if (x == IO_PARK) {
        return -1;
      }
      continue;
    }
    IoJob* job = io_mem(malloc(sizeof(IoJob) + (n + 1) * sizeof(Term)));
    job->what = eff;
    job->word = word;
    job->cont = fs[n];
    job->work = w;
    if (need == 0) {
      io_send(job);
      return -1;
    }
    memcpy(job->args, fs, (n + 1) * sizeof(Term));
    job->time = need & IO_TIME ? io_tick() + (u64)word * 1000000ull : 0;
    job->next = NULL;
    *io_park_at = job;
    io_park_at  = &job->next;
    return -1;
  }
}

OUTLINE int io_loop(Corpus H, Fid fid) {
  Env e = { H, ALC[0] };
  io_stk = pool_stack();
  signal(SIGPIPE, SIG_IGN);
  if (pipe(io_wake_fd) | fcntl(io_wake_fd[0], F_SETFL, O_NONBLOCK)) {
    err_fail(ERR_FAIL, "the event loop failed to open");
  }
  io_push(term_tsk(fid, task_node(e, fid, TERM_HOLE, 0, 0)),
    term_clo(FID_IO_EMIT, 0), true);
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

static u64 cli_size(const char* val) {
  char*  end = NULL;
  double n   = val != NULL ? strtod(val, &end) : 0;
  u64    mul = end == NULL ? 0
    : strcmp(end, "GB") == 0 ? 1ull << 30
    : strcmp(end, "MB") == 0 ? 1ull << 20 : 0;
  if (mul == 0 || n <= 0) {
    cli_fail("expected a size like 4GB or 512MB after ", "--gpu-memory");
  }
  return (u64)(n * (double)mul);
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
  const char* prog = "";
  for (int i = 1; i < argc; i += 1) {
    const char* a = argv[i];
    const char* v = i + 1 < argc ? argv[i + 1] : NULL;
    if (a[0] != '-') {
      prog = a;
      continue;
    }
    i += 1;
    if (strcmp(a, "--help") == 0) {
      printf(CLI_HELP, argv[0]);
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
      mem = cli_size(v);
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
  bool dev = gpu != 0 && BANGS && gpu_probe();
  if (gpu == 1 && BANGS && !dev) {
    cli_fail("--gpu on, but this binary found no GPU device", NULL);
  }
  u32 at = 0;
  while (at < sizeof(MAIN_FIDS) / sizeof(Fid)
    && strcmp(MAIN_NAMES[at], prog) != 0) {
    at += 1;
  }
  if (at == sizeof(MAIN_FIDS) / sizeof(Fid)) {
    cli_fail("no program named ", prog);
  }
  long ncpu = sysconf(_SC_NPROCESSORS_ONLN);
  Corpus H  = corpus_setup(dev, thr > 0 ? thr : ncpu, mem);
  int code  = io_loop(H, MAIN_FIDS[at]);
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

function cli_flag(name, val) {
  if (val !== "on" && val !== "off") {
    cli_fail("expected 'on' or 'off' after " + name);
  }
  return val === "on";
}

function cli(argv) {
  let thr = 0;
  let par = -1;
  let gpu = -1;
  let prog = "";
  for (let i = 0; i < argv.length; i += 1) {
    const a = argv[i];
    const v = argv[i + 1] ?? "";
    if (!a.startsWith("-")) {
      prog = a;
      continue;
    }
    i += 1;
    if (a === "--help") {
      io_out(1, io_bytes([
        "usage: " + process.argv[1] + " [program] [options]",
        "  --threads N        worker threads: a JS program runs one",
        "  --parallel on|off  off means one thread and no GPU (default: on)",
        "  --gpu on|off       send ! calls to the GPU (default: on if present)",
        "  --gpu-memory 4GB   device span: a JS program uses the JS heap",
        "  --help             show this text",
        "",
      ].join("\n")));
      process.exit(0);
    } else if (a === "--threads") {
      thr = /^[ \t\n\v\f\r]*\+?\d+$/.test(v) ? Number(v) : 0;
      if (thr < 1) {
        cli_fail("expected a thread count of 1 or more after --threads");
      }
    } else if (a === "--parallel") {
      par = cli_flag("--parallel", v) ? 1 : 0;
    } else if (a === "--gpu") {
      gpu = cli_flag("--gpu", v) ? 1 : 0;
    } else if (a === "--gpu-memory") {
      if (!/^[ \t\n\v\f\r]*\+?(\d+\.?\d*|\.\d+)(GB|MB)$/.test(v)
        || Number.parseFloat(v) <= 0) {
        cli_fail("expected a size like 4GB or 512MB after --gpu-memory");
      }
    } else {
      cli_fail("unknown option " + a);
    }
  }
  if (par === 0 && (gpu === 1 || thr > 1)) {
    cli_fail("--parallel off means --threads 1 with --gpu off");
  }
  if (gpu === 1) {
    cli_fail("--gpu on, but this binary found no GPU device");
  }
  if (thr > 1) {
    cli_fail("--threads over 1, but a JS program runs one thread");
  }
  return prog;
}

// Io
// ==

function io_exit(mains, prog) {
  if (mains[prog] === undefined) {
    cli_fail("no program named " + prog);
  }
  try {
    process.exit(io_run(mains[prog]));
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
  return Uint8Array.from([...text], (c) => c.codePointAt(0) & 255);
}

function io_text(b, n) {
  return Array.from(b.subarray(0, n), (c) => String.fromCharCode(c)).join("");
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
