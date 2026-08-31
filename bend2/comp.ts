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
// to cover all the case that a mature compiler does, and that's expected.

import * as fs from "node:fs";

import * as Bend from "./bend.ts";

// Comp
// ====

// Types
// =====

type Seg = {
  fid: string;
  def: Bend.Name;
  lines: string[];
  params: string[];
  frame: { pop: number; base: number } | null;
  refs: Set<string>;
  dead?: boolean;
  spin?: boolean;
  unbox?: ("f32" | "u32" | null)[];
};

type Spine = {
  h: Bend.HTerm;
  t: Bend.HTerm;
  all: Bend.HTerm[];
  args: Bend.HTerm[];
};

type Comp = Carb | File | Js;

type Def  = Bend.Def & { h?: Bend.HTerm };

type TLD  = Bend.ADT | Def;

type Book = Omit<Bend.Book, "tlds"> & { tlds: Record<Bend.Name, TLD> };

type Capture = { p: Probe; q: Bend.Quant; A: Bend.HTerm | null };

type Carb = {
  src: Record<Bend.Name, TLD>;
  book: Book;
  mint: Map<Bend.Name, boolean>;
  kn: number;
  done: Set<Bend.Name>;
  queue: Bend.Name[];
  inl: Map<Bend.Name, Bend.HTerm | null>;
  inlrun: Set<Bend.Name>;
  bangs: Set<Bend.Name>;
  brw: Map<Bend.Name, boolean[]>;
  clo: boolean;
};

type File = {
  spares: { words: number; name: string; z: boolean }[];
  fresh: Map<string, number>;
  uses: Map<Probe, Bind>;
  local: Set<string>;
  brwl: Set<string>;
  fusing: Set<Bend.Name>;
  book: Book;
  segs: Seg[];
  seg: Seg;
  tab: number;
  decl: "Term";
  cb: Carb;
  cids: Map<string, { arity: number; packed: boolean }>;
  shr: Set<string>;
  tabs: Map<string, number>;
  spins: string[];
  reqs: string;
};

type Gen = string | ((xs: string[]) => string);

type Native = {
  intr: Record<Bend.Name, Gen>;
  elim?: Record<Bend.Name, string[]>;
  cond?: Record<Bend.Name, string>;
};

type Optim = { C?: Native; JS?: Native };

type Of<K> = Extract<Bend.HTerm, { $: K }>;

type Probe = Of<"Var">;

type HAll = Of<"All">;

type HAdt = Of<"ADT">;

type HLet = Of<"Let">;

type UMap = Bend.PMap<number>;

type Call = {
  k: Bend.Name;
  args: Bend.HTerm[];
  bang?: boolean;
};

type Open = (env: Map<Bend.HTerm, Bend.HTerm>) => Bend.HTerm;

type Kont = (caps: Capture[], x: Open) => Open;

type Root = [Bend.Name, number];

type Parts = { k: Bend.Name; vs: string[]; w: boolean };

type Bind = { owed: number; local: string; triv: boolean; parts?: Parts };

type Dst = string[] | null;

type Arg = string | Parts;

type Intr = {
  C?: Gen;
  parts?: string[];
  flg?: number;
  call?: boolean;
  JS: Gen;
};

type Js = {
  book:  Book;
  cb:    Carb;
  seg:   { lines: string[] };
  tab:   number;
  decl:  "const";
  fresh: Map<string, number>;
};

type Dom = [Bend.Quant, Bend.Name, Bend.HTerm];

// Constants
// =========

const CLO_APPLY = "Clo.apply";

const IDENT  = /^[A-Za-z_$][A-Za-z0-9_$]*$/;
const ATOM   = /^(?:[A-Za-z_$][A-Za-z0-9_$]*|\d+n?|\d+\.\d+)$/;
const STRLIT = new RegExp("^\"(?:[^\"\\\\]|\\\\.)*\"$");

const NATIVE_DIE = " does not match the native format of its type";

const EXACT = " sqrt exp log log2 log10 sin cos tan pow ";

const USE0 = Bend.Emp<number>();

const EMPTY = new Map<Bend.HTerm, Bend.HTerm>();

// Operations
// ----------

export const OPERATIONS: Record<string, Intr> = Object.setPrototypeOf({
  u32_add: {
    C:  "U32_BIN($0, +, $1)",
    JS: "(($0 + $1) >>> 0)",
  },
  u32_sub: {
    C:  "U32_BIN($0, -, $1)",
    JS: "(($0 - $1) >>> 0)",
  },
  u32_mul: {
    C:  "U32_BIN($0, *, $1)",
    JS: "(Math.imul($0, $1) >>> 0)",
  },
  u32_div: {
    C:  "(u32_unbox($1) == 0 ? 0 : U32_BIN($0, /, $1))",
    JS: "($1 === 0 ? 0 : ($0 / $1) >>> 0)",
  },
  u32_mod: {
    C:  "(u32_unbox($1) == 0 ? $0 : U32_BIN($0, %, $1))",
    JS: "($1 === 0 ? $0 : $0 % $1)",
  },
  u32_inc: {
    C:  "U32_BIN($0, +, 1)",
    JS: "(($0 + 1) >>> 0)",
  },
  u32_shl: {
    C:  "U32_BIN($0, <<, 1)",
    JS: "(($0 << 1) >>> 0)",
  },
  u32_shr: {
    C:  "U32_BIN($0, >>, 1)",
    JS: "($0 >>> 1)",
  },
  u32_shln: {
    C:  "($1 >= 32 ? 0 : U32_BIN($0, <<, $1))",
    JS: "($1 >= 32n ? 0 : ($0 << Number($1)) >>> 0)",
  },
  u32_shrn: {
    C:  "($1 >= 32 ? 0 : U32_BIN($0, >>, $1))",
    JS: "($1 >= 32n ? 0 : $0 >>> Number($1))",
  },
  u32_and: {
    C:  "U32_BIN($0, &, $1)",
    JS: "(($0 & $1) >>> 0)",
  },
  u32_or: {
    C:  "U32_BIN($0, |, $1)",
    JS: "(($0 | $1) >>> 0)",
  },
  u32_xor: {
    C:  "U32_BIN($0, ^, $1)",
    JS: "(($0 ^ $1) >>> 0)",
  },
  u32_not: {
    C:  "u32_rewrap(~u32_unbox($0))",
    JS: "(~$0 >>> 0)",
  },
  u32_is_zero: {
    C:  "U32_BIN($0, ==, 0)",
    JS: "($0 === 0)",
  },
  u32_is_eq: {
    C:  "U32_BIN($0, ==, $1)",
    JS: "($0 === $1)",
  },
  u32_is_ne: {
    C:  "U32_BIN($0, !=, $1)",
    JS: "($0 !== $1)",
  },
  u32_is_lt: {
    C:  "U32_BIN($0, <, $1)",
    JS: "($0 < $1)",
  },
  u32_is_le: {
    C:  "U32_BIN($0, <=, $1)",
    JS: "($0 <= $1)",
  },
  u32_is_gt: {
    C:  "U32_BIN($0, >, $1)",
    JS: "($0 > $1)",
  },
  u32_is_ge: {
    C:  "U32_BIN($0, >=, $1)",
    JS: "($0 >= $1)",
  },
  u32_cmp: {
    C:  "(U32_BIN($0, >, $1) + U32_BIN($0, >=, $1))",
    JS: "cmp_new($0, $1)",
  },
  u32_to_f32: {
    C:  "f32_rewrap((f32)u32_unbox($0))",
    JS: "Math.fround($0)",
  },
  u32_to_nat: {
    C:  "$0",
    JS: "BigInt($0)",
  },
  u32_from_nat: {
    C:  "u32_rewrap(u32_unbox($0))",
    JS: "Number($0 & 0xFFFFFFFFn)",
  },
  f32_add: {
    C:  "F32_BIN($0, +, $1)",
    JS: "Math.fround($0 + $1)",
  },
  f32_sub: {
    C:  "F32_BIN($0, -, $1)",
    JS: "Math.fround($0 - $1)",
  },
  f32_mul: {
    C:  "F32_BIN($0, *, $1)",
    JS: "Math.fround($0 * $1)",
  },
  f32_div: {
    C:  "F32_BIN($0, /, $1)",
    JS: "Math.fround($0 / $1)",
  },
  f32_neg: {
    C:  "f32_rewrap(-f32_unbox($0))",
    JS: "(-$0)",
  },
  f32_is_eq: {
    C:  "F32_CMP($0, ==, $1)",
    JS: "($0 === $1)",
  },
  f32_is_ne: {
    C:  "F32_CMP($0, !=, $1)",
    JS: "($0 !== $1)",
  },
  f32_is_lt: {
    C:  "F32_CMP($0, <, $1)",
    JS: "($0 < $1)",
  },
  f32_is_le: {
    C:  "F32_CMP($0, <=, $1)",
    JS: "($0 <= $1)",
  },
  f32_is_gt: {
    C:  "F32_CMP($0, >, $1)",
    JS: "($0 > $1)",
  },
  f32_is_ge: {
    C:  "F32_CMP($0, >=, $1)",
    JS: "($0 >= $1)",
  },
  f32_sqrt: {
    C:  "f32_rewrap(sqrtf(f32_unbox($0)))",
    JS: "Math.fround(Math.sqrt($0))",
  },
  f32_exp: {
    C:  "f32_rewrap(expf(f32_unbox($0)))",
    JS: "Math.fround(Math.exp($0))",
  },
  f32_log: {
    C:  "f32_rewrap(logf(f32_unbox($0)))",
    JS: "Math.fround(Math.log($0))",
  },
  f32_log2: {
    C:  "f32_rewrap(log2f(f32_unbox($0)))",
    JS: "Math.fround(Math.log2($0))",
  },
  f32_log10: {
    C:  "f32_rewrap(log10f(f32_unbox($0)))",
    JS: "Math.fround(Math.log10($0))",
  },
  f32_sin: {
    C:  "f32_rewrap(sinf(f32_unbox($0)))",
    JS: "Math.fround(Math.sin($0))",
  },
  f32_cos: {
    C:  "f32_rewrap(cosf(f32_unbox($0)))",
    JS: "Math.fround(Math.cos($0))",
  },
  f32_tan: {
    C:  "f32_rewrap(tanf(f32_unbox($0)))",
    JS: "Math.fround(Math.tan($0))",
  },
  f32_asin: {
    C:  "f32_rewrap(asinf(f32_unbox($0)))",
    JS: "Math.fround(Math.asin($0))",
  },
  f32_acos: {
    C:  "f32_rewrap(acosf(f32_unbox($0)))",
    JS: "Math.fround(Math.acos($0))",
  },
  f32_atan: {
    C:  "f32_rewrap(atanf(f32_unbox($0)))",
    JS: "Math.fround(Math.atan($0))",
  },
  f32_sinh: {
    C:  "f32_rewrap(sinhf(f32_unbox($0)))",
    JS: "Math.fround(Math.sinh($0))",
  },
  f32_cosh: {
    C:  "f32_rewrap(coshf(f32_unbox($0)))",
    JS: "Math.fround(Math.cosh($0))",
  },
  f32_tanh: {
    C:  "f32_rewrap(tanhf(f32_unbox($0)))",
    JS: "Math.fround(Math.tanh($0))",
  },
  f32_floor: {
    C:  "f32_rewrap(floorf(f32_unbox($0)))",
    JS: "Math.fround(Math.floor($0))",
  },
  f32_ceil: {
    C:  "f32_rewrap(ceilf(f32_unbox($0)))",
    JS: "Math.fround(Math.ceil($0))",
  },
  f32_trunc: {
    C:  "f32_rewrap(truncf(f32_unbox($0)))",
    JS: "Math.fround(Math.trunc($0))",
  },
  f32_pow: {
    C:  "f32_rewrap(powf(f32_unbox($0), f32_unbox($1)))",
    JS: "Math.fround(Math.pow($0, $1))",
  },
  f32_atan2: {
    C:  "f32_rewrap(atan2f(f32_unbox($0), f32_unbox($1)))",
    JS: "Math.fround(Math.atan2($0, $1))",
  },
  f32_abs: {
    C:  "f32_rewrap(fabsf(f32_unbox($0)))",
    JS: "Math.abs($0)",
  },
  f32_mod: {
    C:  "f32_rewrap(fmodf(f32_unbox($0), f32_unbox($1)))",
    JS: "Math.fround($0 % $1)",
  },
  f32_to_u32: {
    C:  "f32_to_u32($0)",
    JS: "($0 >= 1 && $0 < 4294967296 ? Math.floor($0) : 0)",
  },
  f32_show: {
    C:    "f32_show(e, $0)",
    call: true,
    JS:   "String(Number(($0).toPrecision(6)))",
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
  bool_or: {
    C:  "(($0) | ($1))",
    JS: "($0 || $1)",
  },
  bool_xor: {
    C:  "(($0) ^ ($1))",
    JS: "($0 !== $1)",
  },
  string_append: {
    JS: "($0 + $1)",
  },
  array_new: {
    C:    "buf_new(e, $2, $0, $1)",
    flg:  1,
    call: true,
    JS:   "array_new($0, $1)",
  },
  array_set: {
    C:    "blk_set(e, $3, $0, $1, $2)",
    flg:  0,
    call: true,
    JS:   "array_set($0, $1, $2)",
  },
  array_get: {
    parts: ["$0", "blk_get(e, $2, $3, $1)"],
    flg:   0,
    call:  true,
    JS:    "array_get($0, $1)",
  },
  array_swap: {
    parts: ["$0", "blk_give(e, $3, $4, $1, $2)"],
    flg:   0,
    call:  true,
    JS:    "array_swap($0, $1, $2)",
  },
  array_size: {
    parts: ["$0", "(1ull << blk_cls(e, $2))"],
    call:  true,
    JS:    "array_size($0)",
  },
  array_clone: {
    parts: ["blk_copy(e, $0)", "$0"],
    call:  true,
    JS:    "array_clone($0)",
  },
}, null);

// Optimized
// ---------

const OPTIMIZED: Record<Bend.Name, Optim> = Object.setPrototypeOf({
  Nat: {
    C: {
      intr: {
        Zero: "0",
        Succ: ([p]: string[]) => /^\d+(?:ull)?$/.test(p)
          ? (BigInt(p.replace("ull", "")) + 1n) + "ull"
          : `nat_chk(e, ${p} + 1)`,
      },
      elim: {
        Succ: ["($0 - 1)"],
      },
      cond: {
        Zero: "$0 == 0",
        Succ: "$0 != 0",
      },
    },
    JS: {
      intr: {
        Zero: "0n",
        Succ: ([p]: string[]) => /^\d+n$/.test(p)
          ? (BigInt(p.slice(0, -1)) + 1n) + "n"
          : "nat_chk(" + p + " + 1n)",
      },
      elim: {
        Succ: ["($0 - 1n)"],
      },
      cond: {
        Zero: "$0 === 0n",
        Succ: "$0 !== 0n",
      },
    },
  },
  Array: {
    C: {
      intr: {
        ALeaf: "buf_new(e, $1, 0, $0)",
        ANode: "blk_node(e, $0, $1)",
      },
      elim: {
        ALeaf: ["blk_take(e, $0)"],
        ANode: ["blk_half(e, $0, 0)", "blk_half(e, $0, 1)"],
      },
      cond: {
        ALeaf: "term_aux($0) == 0",
        ANode: "term_aux($0) != 0",
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
    JS: {
      intr: {},
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

const SHIMS = Object.values(OPERATIONS)
  .flatMap((it) => typeof it.C === "string"
    ? [...it.C.matchAll(/(\w+)f\(/g)].map((m) => m[1]) : [])
  .filter((n, i, ns) => ns.indexOf(n) === i)
  .map((n) => "#define " + (n + "f").padEnd(7) + " "
    + (EXACT.includes(` ${n} `) ? "precise::" : "") + n).join("\n");

const NATIVE = {
  C: String.raw`
#ifdef __METAL_VERSION__
${SHIMS}
#endif

#define f32_unbox(x)  __builtin_bit_cast(f32, (u32)(x))
#define u32_unbox(x)  ((u32)(x))
#define f32_rewrap(x) ((u64)__builtin_bit_cast(u32, (f32)(x)))
#define u32_rewrap(x) ((u64)(x))

#define U32_BIN(a, o, b) u32_rewrap(u32_unbox(a) o u32_unbox(b))
#define F32_BIN(a, o, b) f32_rewrap(f32_unbox(a) o f32_unbox(b))
#define F32_CMP(a, o, b) u32_rewrap(f32_unbox(a) o f32_unbox(b))

static void err_post(Corpus H, Err code);

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
  return io_str(e, buf, snprintf(buf, 32, "%g", (double)f32_unbox(x)));
}

static Term f32_read(Env e, Term s) {
  u64 n = 0;
  char* text = io_cstr(e, s, &n);
  char* end;
  f32 v = strtof(text, &end);
  Term out = term_pak(CID_NONE, 0);
  if (n > 0 && *end == 0) {
    Loc l = heap_alloc(e, 0);
    e.mem[l] = f32_rewrap(v);
    out = term_ctr(CID_SOME, l);
  }
  free(text);
  return out;
}
`,
  JS: String.raw`
function word_to_u32(w) {
  let x = 0;
  for (let i = 0; w.$ === "WCon"; i++) {
    x |= (w.$0 ? 1 : 0) << i;
    w = w.$1;
  }
  return x >>> 0;
}

function u32_to_word(x) {
  let w = {$: "WNil"};
  for (let i = 31; i >= 0; i--) {
    w = {$: "WCon", $0: ((x >>> i) & 1) === 1, $1: w};
  }
  return w;
}

function cmp_new(a, b) {
  if (a < b) {
    return {$: "LT"};
  }
  if (a === b) {
    return {$: "EQ"};
  }
  return {$: "GT"};
}

function nat_divmod(a, b) {
  const q = b === 0n ? 0n : a / b;
  return {$: "Tuple", $0: q, $1: b === 0n ? a : a % b};
}

function array_clone(a) {
  return {$: "Tuple", $0: a, $1: a};
}

function nat_chk(n) {
  if (n > 281474976710655n) {
    throw new Error("nat: " + n + " is past the largest immediate 2^48-1");
  }
  return n;
}

function f32_read(s) {
  const v = s === "" ? NaN : Number(s);
  return Number.isNaN(v) ? {$: "None"} : {$: "Some", $0: Math.fround(v)};
}

function char_new(code) {
  if (code > 0x10FFFF || (code >= 0xD800 && code <= 0xDFFF)) {
    throw new Error("char_new: " + code + " is not a Unicode scalar value");
  }
  return String.fromCodePoint(code);
}
`.slice(1),
};

// Caches
// ------

let PIDN = 0;

const DUMMY = probe("~");

const OPENS: Map<Of<"Lam">, { p: Probe; b: Bend.HTerm }> = new Map();

const LOPENS: Map<HLet, { ps: Probe[]; b: Bend.HTerm }> = new Map();

const USES: Map<Bend.HTerm, UMap> = new Map();

const TELES: Map<Bend.HTerm, ReturnType<typeof Bend.tele_unbind>> = new Map();

const REFS: Map<Bend.Name, Set<Bend.Name>> = new Map();

const FRESH: Set<Bend.Name> = new Set();

const FACTS: Map<Bend.HTerm, number> = new Map();

const SHARE: Map<Bend.HTerm, Probe | null> = new Map();

const DEEPS: Map<Bend.Name, boolean> = new Map();

const NULLS: Map<Bend.Name, Native | undefined> = new Map();

const SPINES: Map<Bend.HTerm, Spine> = new Map();

const PURES: Map<Bend.HTerm, boolean> = new Map();

const CONSTS: Map<Bend.HTerm, boolean> = new Map();

// Name
// ====

function name_clean(k: string): string {
  return k.replace(/[^A-Za-z0-9_]/g, "_");
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

function tpl(t: string): (xs: string[]) => string {
  const ps = t.split(/\$(\d)/);
  return (xs) => ps.map((p, i) => (i % 2 === 1 ? xs[+p] : p)).join("");
}

function tpl_run(t: Gen, xs: string[]): string {
  return typeof t === "string" ? tpl(t)(xs) : t(xs);
}

function tpl_dup(t: Gen): boolean {
  const ps = typeof t === "string"
    ? t.split(/\$(\d)/).filter((_, i) => i % 2 === 1) : [];
  return new Set(ps).size !== ps.length;
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
  [OPENS, LOPENS, USES, FACTS, SHARE, DEEPS, PURES, SPINES, CONSTS]
    .forEach((m) => m.clear());
}

// Probe
// =====

function probe(k: Bend.Name): Probe {
  return Bend.Var(k, (PIDN += 1)) as Probe;
}

function probe_of(t: Bend.HTerm): Probe {
  return Bend.term_force(t) as Probe;
}

// Term
// ====

function term_open(t: Of<"Lam">): { p: Probe; b: Bend.HTerm } {
  return memo(OPENS, t, () => {
    const p = probe(t.k);
    return { p, b: t.f(p) };
  });
}

function term_lets(t: HLet): { ps: Probe[]; b: Bend.HTerm } {
  return memo(LOPENS, t, () => {
    const ps = t.k.map(probe);
    return { ps, b: t.f(ps) };
  });
}

function term_split(t: HLet, j = 0, xs: Bend.HTerm[] = []): Bend.HTerm {
  if (j === t.k.length) {
    return t.f(xs);
  }
  return Bend.Let([t.k[j]], [t.i[j]], [t.v[j]],
    (x: Bend.HTerm[]) => term_split(t, j + 1, [...xs, x[0]]), t.s, [t.q[j]]);
}

function term_spine(cf: Comp, tm: Bend.HTerm): Spine {
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
    const qs = tld?.$ === "Def" ? tele_unbind(cf.book, tld.T).doms : null;
    const live = (i: number) => qs === null
      ? call_live(cf.book, apps[i].f)
      : i >= qs.length || quant_live(qs[i][0]);
    const all = apps.map((a) => a.x);
    return { h, t: c, all, args: all.filter((_, i) => live(i)) };
  });
}

function term_eta(t: Bend.HTerm): Bend.HTerm {
  return Bend.Lam("x", 0, (y) => Bend.App(t, y));
}

function term_kids(cf: Comp, tm: Bend.HTerm): Bend.HTerm[] {
  const t = Bend.term_force(tm);
  switch (t.$) {
    case "Ann": return [t.x];
    case "Lam": return [term_open(t).b];
    case "Let": return [...t.v.filter((_, j) => quant_live(t.q[j])),
      term_lets(t).b];
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

function term_any(cf: Comp, t: Bend.HTerm, p: (s: Bend.HTerm) => boolean,
  seen: Set<Bend.HTerm> = new Set()): boolean {
  const s = Bend.term_force(t);
  if (seen.has(s)) {
    return false;
  }
  seen.add(s);
  return p(s) || term_kids(cf, s).some((x) => term_any(cf, x, p, seen));
}

function term_const(t: Bend.HTerm): boolean {
  const s = Bend.term_strip(t);
  return s.$ === "Ctr" && memo(CONSTS, s, () => s.x.every(term_const));
}

function term_use(u: UMap, p: Probe): number {
  return Bend.pmap_get(u, p.i) ?? 0;
}

function term_uses(cb: Carb, tm: Bend.HTerm): UMap {
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

function live_doms(c: Comp, tld: Bend.Def): Dom[] {
  return def_get_params(c.book, tld).filter(live_dom);
}

// Intr
// ====

function intr_of(c: Comp, k: Bend.Name): Intr | undefined {
  const it = def_own(c.book.tlds[k]) ? OPERATIONS[eff_name(k)] : undefined;
  return it !== undefined && (it.C !== undefined || it.parts !== undefined)
    ? it : undefined;
}

// Call
// ====

function call_live(book: Bend.Book, f: Bend.HTerm): boolean {
  const all = ty_all(book, ty_ann(f));
  return all === null || quant_live(all.q);
}

function call_kind(c: Comp, t: Bend.HTerm): Call | null {
  const m = term_spine(c, t);
  let dyn = m.t.$ === "Var" && m.args.length > 0;
  if (m.t.$ === "Ref" && intr_of(c, m.t.k) === undefined) {
    const tld = c.book.tlds[m.t.k];
    if (done_live(tld) || def_foreign(tld)) {
      const live = def_live(c, tld);
      if (m.args.length === live) {
        return { k: m.t.k, args: m.args, bang: m.t.b };
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
  return { k: CLO_APPLY, args: [a.f, a.x] };
}

function call_is(cb: Carb, t: Bend.HTerm): boolean {
  return call_kind(cb, t) !== null;
}

function call_has(cb: Carb, t: Bend.HTerm): boolean {
  return (call_fact(cb, t) & 1) !== 0;
}

function call_fact(cb: Carb, tm: Bend.HTerm): number {
  const t = Bend.term_force(tm);
  return memo(FACTS, t, () => {
    let f = 0;
    if ((t.$ === "App" || t.$ === "Ref") && call_is(cb, t)) {
      f = inl_at(cb, t) !== null ? 1
        : call_fuse(cb, t) !== null ? 0 : 3;
    }
    for (const x of term_kids(cb, t)) {
      if (f !== 3) {
        f |= call_fact(cb, x);
      }
    }
    return f;
  });
}

function call_fuse(c: Comp, t: Bend.HTerm): Call | null {
  const ck = call_kind(c, t);
  if (ck === null || fuse_ban(ck) || ck.args.length === 0) {
    return null;
  }
  const cb = "cb" in c ? c.cb : c;
  return inl_of(cb, ck.k) === null ? null : ck;
}

// Tele
// ====

function tele_unbind(book: Bend.Book,
  T: Bend.HTerm): ReturnType<typeof Bend.tele_unbind> {
  return memo(TELES, T, () => Bend.tele_unbind(book, T));
}

// Ty
// ==

function ty_ann(t: Bend.HTerm): Bend.HTerm | null {
  const v = Bend.term_force(t);
  return v.$ === "Ann" ? v.T : null;
}

function ty_wnf(book: Bend.Book, ty: Bend.HTerm | null): Bend.HTerm | null {
  return ty && Bend.term_wnf(book, ty);
}

function ty_all(book: Bend.Book, ty: Bend.HTerm | null): HAll | null {
  const w = ty_wnf(book, ty);
  return w?.$ === "All" ? w : null;
}

function ty_tele(book: Bend.Book, T: Bend.HTerm,
  args: Bend.HTerm[]): Bend.HTerm {
  return args.reduce((T2, a) => (ty_all(book, T2) as HAll).B(a), T);
}

function ty_peel(tm: Bend.HTerm,
  ty: Bend.HTerm | null): [Bend.HTerm, Bend.HTerm | null] {
  let x = Bend.term_force(tm);
  while (x.$ === "Ann") {
    ty = x.T;
    x = Bend.term_force(x.x);
  }
  return [x, ty];
}

function ty_w32(book: Bend.Book, A: Bend.HTerm | null): boolean {
  const t = ty_wnf(book, A);
  if (t?.$ !== "ADT") {
    return false;
  }
  return t.k === "U32" || t.k === "F32" || t.k === "Char"
    || native_nullary(book, t.k) !== undefined;
}

function ty_f32(book: Bend.Book, A: Bend.HTerm | null): boolean {
  const t = ty_wnf(book, A);
  return t?.$ === "ADT" && t.k === "F32";
}

// Arr
// ===

function arr_elem(book: Bend.Book, A: Bend.HTerm): Bend.HTerm {
  const w = ty_wnf(book, A);
  return w?.$ === "ADT" && w.k === "Array" ? w.x[0] : A;
}

function arr_flag(book: Bend.Book, el: Bend.HTerm): boolean {
  if (ty_w32(book, el)) {
    return false;
  }
  const w = ty_wnf(book, el);
  if (w?.$ === "ADT" || w?.$ === "All") {
    return true;
  }
  die("an open Array element type");
}

// Ctr
// ===

function ctr_adt(fl: File | Js, x: Of<"Ctr">,
  ty: Bend.HTerm | null): [HAdt, number | null] {
  const ctr = fl.book.ctrs[x.k];
  const T = ty ?? (ctr === undefined ? null : tele_unbind(fl.book, ctr.T).ret);
  const adt = ty_wnf(fl.book, T);
  if (adt?.$ !== "ADT" || (ty === null && adt.x.length > 0)) {
    die(`a constructor at a non-datatype type: ${x.k}`);
  }
  const word = adt.k === "U32" || adt.k === "F32";
  return [adt, word ? Bend.u32_from_term(x, adt.k) : null];
}

function ctr_tail(book: Bend.Book, ctr: Bend.Ctr): Dom[] {
  const doms = tele_unbind(book, ctr.T).doms;
  return doms.slice(doms.length - ctr.n);
}

function ctr_doms(book: Bend.Book, ctr: Bend.Ctr): Bend.HTerm[] {
  return ctr_tail(book, ctr).filter(live_dom).map(([, , A]) => A);
}

function ctr_scalar1(book: Bend.Book, k: Bend.Name): boolean {
  const ctr = book.ctrs[k];
  const fields = ctr === undefined ? [] : ctr_doms(book, ctr);
  return fields.length === 1 && ty_w32(book, fields[0]);
}

function ctr_flds(book: Bend.Book, k: Bend.Name,
  xs: Bend.HTerm[]): Bend.HTerm[] {
  const ctr = book.ctrs[k];
  const qs = ctr && ctr_tail(book, ctr).map(([q]) => q);
  return xs.filter((_, j) => qs?.[j] === undefined || quant_live(qs[j]));
}

function ctr_build(fl: File, k: Bend.Name, exprs: string[]): string {
  const cid = cid_reg(fl, k);
  if (exprs.length === 0 || fl.cids.get(k)!.packed) {
    return `term_pak(${cid}, ${exprs[0] ?? 0})`;
  }
  const alloc = `heap_alloc(e, cls_fit(${exprs.length}))`;
  const at = fl.spares.findIndex((s) =>
    cls_fit(s.words) === cls_fit(exprs.length));
  let got = alloc;
  if (at >= 0) {
    const s = fl.spares.splice(at, 1)[0];
    got = s.z ? `${s.name} ? ${s.name} : ${alloc}` : s.name;
  }
  return `term_ctr(${cid}, ${node_fill(fl, "nd", got, exprs,
    fl.shr.has(k))})`;
}

// Native
// ======

function native_nullary(book: Bend.Book, k: Bend.Name): Native | undefined {
  return memo(NULLS, k, () => {
    const tld = book.tlds[k];
    if (tld?.$ !== "ADT" || tld.c.length === 0
      || !tld.c.every((c) => ctr_doms(book, c).length === 0)) {
      return undefined;
    }
    return {
      intr: Object.fromEntries(tld.c.map((c, i) => [c.k, String(i)])),
      cond: Object.fromEntries(tld.c.map((c, i) => [c.k, `$0 == ${i}`])),
    };
  });
}

function native_of(book: Bend.Book, adt: HAdt): Native | undefined {
  if (adt.k === "U32" || adt.k === "F32") {
    die("a structural view of a machine word");
  }
  if (adt.k === "Array") {
    arr_flag(book, adt.x[0]);
  }
  return OPTIMIZED[adt.k]?.C ?? native_nullary(book, adt.k);
}

// Adt
// ===

function adt_triv(book: Bend.Book, A: Bend.HTerm | null): boolean {
  const adt = ty_wnf(book, A);
  if (adt?.$ !== "ADT") {
    return false;
  }
  if (["U32", "F32", "Char", "Nat"].includes(adt.k)) {
    return true;
  }
  const tld = book.tlds[adt.k];
  return tld?.$ === "ADT" && tld.c.every((c) =>
    ctr_doms(book, c).length === 0 || ctr_scalar1(book, c.k));
}

// Mat
// ===

function mat_head(t: Bend.HTerm): boolean {
  return t.$ === "Mat" || t.$ === "Efq";
}

function mat_arms(t: Bend.HTerm):
  { arms: [Bend.Name, Bend.HTerm][]; end: Bend.HTerm | null } {
  const arms: [Bend.Name, Bend.HTerm][] = [];
  let cur = t;
  for (let m = Bend.term_strip(cur); m.$ === "Mat"; m = Bend.term_strip(cur)) {
    arms.push([m.k, m.h]);
    cur = m.m;
  }
  return { arms, end: Bend.term_strip(cur).$ === "Efq" ? null : cur };
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
    die("a def type shorter than its parameters");
  }
  return doms.slice(0, def.n);
}

function def_foreign(tld: Bend.TLD | undefined): tld is Bend.Def {
  return tld?.$ === "Def" && tld.i !== undefined;
}

function def_live(c: Comp, tld: Bend.Def): number {
  return live_doms(c, tld).length + Number(def_foreign(tld));
}

function def_own(tld: Bend.TLD | undefined): boolean {
  return tld?.$ === "Def" && tld.i === undefined && (tld.b || tld.v === null);
}

// Eff
// ===

function eff_name(k: Bend.Name): string {
  return k.toLowerCase().replace(/\./g, "_");
}

function eff_src(path: string, seen: Set<string>): string {
  path = fs.realpathSync(path);
  if (seen.has(path)) {
    return "";
  }
  seen.add(path);
  const src = fs.readFileSync(path, "utf8");
  const dir = path.slice(0, path.lastIndexOf("/") + 1);
  let out = "";
  for (const m of src.matchAll(/^\/\/! use (.+)$/gm)) {
    out += eff_src(dir + m[1], seen);
  }
  return out + src;
}

// Io
// ==

function io_base(book: Bend.Book, t: Bend.HTerm): Bend.HTerm[] | null {
  const io = book.tlds["IO"];
  if (io?.$ !== "Def" || io.b !== true) {
    return null;
  }
  const tlds = { ...book.tlds, IO: { ...io, v: null } };
  const [h, xs] = Bend.term_unapply(Bend.term_wnf({ ...book, tlds }, t));
  return h.$ === "Ref" && h.k === "IO" ? xs : null;
}

export function io_type(book: Bend.Book): Bend.HTerm | null {
  const main = book.tlds["main"];
  if (main?.$ !== "Def") {
    return null;
  }
  const xs = io_base(book, main.T);
  if (xs === null) {
    return null;
  }
  if (def_foreign(main)) {
    die("main must be a filled def: a foreign main cannot anchor IO");
  }
  return xs.length === 1 ? xs[0] : null;
}

export function io_run(book: Bend.Book): number {
  const src = js_text(book)
    + "\nreturn io_run(" + js_sat("main") + ");";
  return new Function("require", src)(import.meta.require) as number;
}

// Mint
// ====

function mint_lift(t: Bend.HTerm): Open {
  return (env) => env.get(t) ?? t;
}

function mint_caps(cs: Capture[], f: Open): Open {
  return (env) => cs.reduce((c, b) => Bend.App(c, env.get(b.p) ?? b.p), f(env));
}

function mint_ret(cb: Carb, t: Bend.HTerm): Bend.HTerm {
  const s = Bend.term_force(t);
  if (s.$ === "Ann") {
    return s.T;
  }
  if (s.$ === "Let") {
    return mint_ret(cb, s.f(s.v.map(() => DUMMY)));
  }
  const m = term_spine(cb, s);
  const tld = m.t.$ === "Ref" ? cb.book.tlds[m.t.k] : undefined;
  const T = tld?.$ === "Def" ? tld.T
    : ty_ann(m.h) ?? die("a minted definition without a result type");
  return ty_tele(cb.book, T, m.all);
}

function mint(cb: Carb, def: Bend.Name, stem: string, scope: Capture[],
  seq: boolean, tail: number, build: () => Open, ext = 0): Open {
  cb.kn += 1;
  const name = def + "$" + stem + cb.kn;
  const body = build();
  const bt = body(EMPTY);
  const kept = scope.filter((c, i) => i >= scope.length - tail
    || !quant_live(c.q) || term_use(term_uses(cb, bt), c.p) > 0);
  const T = kept.reduceRight<Bend.HTerm>((R, c, i) =>
    Bend.All<Bend.HBody>(c.q, c.p.k, i,
    c.A ?? die(`a minted capture without a type: ${name} ${c.p.k}`),
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
  if (!FRESH.has(k)) {
    FRESH.add(k);
    if (tld?.$ === "Def" && tld.e !== undefined) {
      cb.src[k] = { ...tld, h: Bend.term_higher(tld.e) };
    }
  }
  return cb.src[k];
}

function carb_book(src: Bend.Book, roots: Bend.Name[]): Carb {
  [TELES, REFS, FRESH, NULLS].forEach((m) => m.clear());
  memo_gc();
  const book: Book = { ...src, tlds: { ...src.tlds } };
  const cb: Carb = {
    src: { ...src.tlds },
    book,
    mint: new Map(),
    kn: 0,
    done: new Set(),
    queue: roots,
    inl: new Map(),
    inlrun: new Set(),
    bangs: new Set(),
    brw: new Map(),
    clo: false,
  };
  while (cb.queue.length > 0) {
    const d = cb.queue.shift() as Bend.Name;
    if (cb.done.has(d)) {
      continue;
    }
    cb.done.add(d);
    memo_gc();
    const tld = book.tlds[d];
    if (!done_live(tld)) {
      continue;
    }
    let out = tld.h as Bend.HTerm;
    if (!cb.mint.has(d)) {
      if (tld.e === undefined) {
        die("unelaborated def " + d);
      }
      const fr = carb_fresh(cb, d) as Def;
      const PASS: Kont = (_c, x) => x;
      function bound(caps: Capture[], l: HLet, v: Open,
        rest: (caps: Capture[], body: Bend.HTerm) => Open,
        cuts = false): Open {
        const bd = { p: term_lets(l).ps[0], q: l.q[0], A: ty_ann(v(EMPTY)) };
        const c2 = [...caps, bd];
        const go = () => rest(c2, term_lets(l).b);
        const body = cuts ? mint(cb, d, "k", c2, true, 1, go) : go();
        return (env) => Bend.Let(l.k, l.i, [v(env)], (x) => cuts
          ? Bend.App(body(env), x[0])
          : body(new Map(env).set(bd.p, x[0])), l.s, l.q);
      }
      function apps(caps: Capture[], t: Bend.HTerm, k: Kont): Open {
        type Fill = (caps: Capture[],
          rb: (f: Open) => Open) => Open;
        const m = term_spine(cb, t);
        const go = (u: Bend.HTerm, k2: Fill): Open => {
          const s = Bend.term_force(u);
          if (s.$ === "Ann") {
            return go(s.x, (c2, rb) => k2(c2, (f) =>
              (env) => Bend.Ann(rb(f)(env), s.T, s.s)));
          }
          if (s.$ === "App") {
            const app: Fill = (c2, rb) => expr(c2, s.x, null,
              (c3, x) => k2(c3, (f) =>
                (env) => Bend.App(rb(f)(env), x(env), s.s)));
            if (!call_is(cb, s.f)) {
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
      function func(caps: Capture[], t: Bend.HTerm, ty: Bend.HTerm | null,
        left: number): Open {
        const s = Bend.term_force(t);
        const x = Bend.term_strip(t);
        if (x.$ !== "Lam" && !mat_head(x)) {
          if (left === 0) {
            return leaf(caps, s);
          }
          const T = ty ?? ty_ann(s) ?? die("an untyped point-free arm");
          return func(caps, Bend.Ann(term_eta(s), T), null, left);
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
            const { p, b } = term_open(s);
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
              + (ctr === undefined ? 0 : ctr_doms(cb.book, ctr).length));
            const m = func(caps, s.m, null, left);
            return (env) => Bend.Mat(s.k, h(env), m(env), s.s);
          }
          default: {
            return mint_lift(s);
          }
        }
      }
      function leaf(caps: Capture[], t: Bend.HTerm): Open {
        const s = Bend.term_strip(t);
        if (s.$ === "Let") {
          if (s.k.length >= 2) {
            if (s.v.every((v) => call_is(cb, v))) {
              return fork(caps, s);
            }
            return leaf(caps, term_split(s));
          }
          if (!quant_live(s.q[0])) {
            return leaf(caps, s.f(s.v));
          }
          if (call_is(cb, s.v[0]) && inl_at(cb, s.v[0]) === null
            && call_fuse(cb, s.v[0]) === null) {
            return apps(caps, s.v[0], (c2, c) =>
              bound(c2, s, c, leaf, true));
          }
          return expr(caps, s.v[0], null, (c2, v) => bound(c2, s, v, leaf));
        }
        const got = inl_at(cb, t);
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
        const o = term_lets(s);
        let jt = o.b;
        for (let g; (g = inl_at(cb, jt)) !== null;) {
          jt = g;
        }
        const ck = call_kind(cb, jt);
        const h = ck === null ? -1 : ck.args.length - o.ps.length;
        const jc = ck !== null && h >= 0
          && ck.args.slice(h).every((a, j) => Bend.term_strip(a) === o.ps[j])
          && ck.args.slice(0, h).every((a) => !call_has(cb, a)) ? ck : null;
        return many(caps, n, (c2, j, kx) => apps(c2, s.v[j], kx),
          (c2, vs) => {
            const c3 = [...c2, ...vs.map((v, j) =>
              ({ p: o.ps[j], q: s.q[j], A: ty_ann(v(EMPTY)) }))];
            const body = jc !== null && !cb.mint.get(jc.k)
              ? leaf(c3, o.b)
              : mint_caps(c3.slice(-n),
                mint(cb, d, "j", c3, false, n, () => leaf(c3, o.b)));
            return (env) => Bend.Let(s.k, s.i, vs.map((v) => v(env)), (xs) => {
              const e2 = new Map(env);
              xs.forEach((x, j) => e2.set(o.ps[j], x));
              return body(e2);
            }, s.s, s.q);
          });
      }
      function expr(caps: Capture[], t: Bend.HTerm, ty: Bend.HTerm | null,
        k: Kont): Open {
        if (term_const(t)) {
          return k(caps, mint_lift(t));
        }
        if (t.$ === "Var" && t.i < 0 && SHARE.has(t)) {
          const p = SHARE.get(t);
          if (p != null && caps.some((c) => c.p === p)) {
            return k(caps, mint_lift(p));
          }
          const l = Bend.Let(["s"], [0], [t], (x: Bend.HTerm[]) => x[0],
            undefined, [Bend.Many()]) as HLet;
          SHARE.set(t, term_lets(l).ps[0]);
          return expr(caps, Bend.term_force(t), ty, (c2, v) =>
            bound(c2, l, v, (c3, b) => k(c3, mint_lift(b))));
        }
        const s = Bend.term_force(t);
        if (s.$ === "Ann") {
          return expr(caps, s.x, s.T, (c2, x) =>
            k(c2, (env) => Bend.Ann(x(env), s.T, s.s)));
        }
        const got = inl_at(cb, s);
        if (got !== null) {
          return expr(caps, got, ty, k);
        }
        if (call_is(cb, s) && call_fuse(cb, s) === null) {
          return apps(caps, s, (c2, c) => {
            const l = Bend.Let(["h"], [0], [s],
              (x: Bend.HTerm[]) => x[0]) as HLet;
            return bound(c2, l,
              ty === null ? c : (env) => Bend.Ann(c(env), ty),
              (c3, b) => k(c3, mint_lift(b)), true);
          });
        }
        switch (s.$) {
          case "App": {
            const m = term_spine(cb, s);
            if (m.t.$ === "Ref" || m.t.$ === "Var") {
              return apps(caps, s, k);
            }
            die("a " + m.t.$ + "-headed app in an expression");
          }
          case "Ctr": {
            return many(caps, s.x.length,
              (c2, j, kx) => expr(c2, s.x[j], null, kx), (c2, xs) =>
              k(c2, (env) => Bend.Ctr(s.k, xs.map((x) => x(env)), s.s)));
          }
          case "Lam": {
            const all = ty_all(cb.book, ty)
              ?? die(`a lambda value without a type: ${s.k}`);
            const { p, b } = term_open(s);
            const bd = { p, q: all.q, A: all.A };
            const c2 = [...caps, bd];
            if (!quant_live(all.q)) {
              return expr(c2, b, all.B(p), k);
            }
            return k(caps, mint(cb, d, "c", c2, false, 1,
              () => leaf(c2, b)));
          }
          case "Let": {
            if (s.k.length >= 2) {
              return expr(caps, term_split(s), ty, k);
            }
            if (!quant_live(s.q[0])) {
              return expr(caps, s.f(s.v), null, k);
            }
            if (call_has(cb, s.v[0])
              || (call_fact(cb, term_lets(s).b) & 2) !== 0) {
              return expr(caps, s.v[0], null, (c2, v) =>
                bound(c2, s, v, (c3, b) => expr(c3, b, null, k)));
            }
            const v = expr(caps, s.v[0], null, PASS);
            return k(caps, bound(caps, s, v,
              (c2, b) => expr(c2, b, null, PASS)));
          }
          case "Mat":
          case "Efq": {
            const T = ty ?? die("an untyped match value");
            return k(caps, mint(cb, d, "c", caps, false, 0,
              () => func(caps, Bend.Ann(s, T), null, 1), 1));
          }
          default: {
            return k(caps, mint_lift(s));
          }
        }
      }
      out = func([], fr.h as Bend.HTerm, fr.T, live_doms(cb, fr).length)(EMPTY);
    }
    book.tlds[d] = { ...tld, h: out };
    const refs = new Set<Bend.Name>();
    term_any(cb, out, (s) => {
      if (s.$ === "Ref") {
        if (s.b) {
          cb.bangs.add(s.k);
        }
        if (intr_of(cb, s.k) === undefined) {
          refs.add(s.k);
        }
      }
      return false;
    });
    REFS.set(d, refs);
    cb.queue.push(...[...refs]
      .sort((a, b) => Number(cb.mint.has(b)) - Number(cb.mint.has(a))));
  }
  return cb;
}

// Calm
// ====

function calm_func(cb: Carb, t: Bend.HTerm, ty0: Bend.HTerm | null): boolean {
  const [s, ty] = ty_peel(t, ty0);
  const all = ty_all(cb.book, ty);
  if (s.$ === "Lam") {
    return calm_func(cb, s.f(DUMMY), all && all.B(DUMMY));
  }
  if (s.$ === "Mat") {
    return all !== null && adt_triv(cb.book, all.A)
      && calm_func(cb, s.h, null) && calm_func(cb, s.m, ty);
  }
  if (s.$ === "Efq") {
    return true;
  }
  return !term_any(cb, s, (y) => y.$ === "Lam" || mat_head(y));
}

function calm_of(cb: Carb, t: Bend.HTerm): boolean {
  return calm_func(cb, t, null)
    && !term_any(cb, t, (s) => s.$ === "Let" && s.k.length >= 2);
}

// Inl
// ===

function inl_calls(cb: Carb, t: Bend.HTerm, self?: Bend.Name): boolean {
  return !term_any(cb, t, (s) => {
    const ck = call_kind(cb, s);
    return ck !== null && (ck.bang === true
      || (ck.k !== self && inl_of(cb, ck.k) === null));
  });
}

function inl_fit(cb: Carb, t: Bend.HTerm, self?: Bend.Name): boolean {
  let size = 0;
  term_any(cb, t, (s) => s.$ !== "Ann" && (size += 1) > 128);
  return size <= 128 && calm_of(cb, t) && inl_calls(cb, t, self);
}

function inl_of(cb: Carb, k: Bend.Name): Bend.HTerm | null {
  const got = cb.inl.get(k);
  if (got !== undefined) {
    return got;
  }
  const tld = carb_fresh(cb, k);
  if (cb.inlrun.has(k) || tld?.$ !== "Def" || tld.h === undefined) {
    return null;
  }
  cb.inlrun.add(k);
  const out = inl_fit(cb, tld.h) ? tld.h : null;
  cb.inlrun.delete(k);
  cb.inl.set(k, out);
  return out;
}

function inl_at(cb: Carb, t: Bend.HTerm): Bend.HTerm | null {
  const m = term_spine(cb, t);
  if (m.t.$ !== "Ref") {
    return null;
  }
  const pre = cb.src[m.t.k];
  if (pre?.$ !== "Def") {
    return null;
  }
  const live = live_doms(cb, pre).length;
  const intr = intr_of(cb, m.t.k) !== undefined;
  if (m.args.length < (intr ? live : live - 1)) {
    return Bend.Ann(term_eta(t), ty_tele(cb.book, pre.T, m.all));
  }
  if (m.t.b || intr || m.all.length !== pre.n) {
    return null;
  }
  const k = m.t.k;
  const tld = carb_fresh(cb, k) as Def;
  const raw = tld.h;
  if (raw === undefined || cb.inlrun.has(k)) {
    return null;
  }
  const tele = tele_unbind(cb.book, tld.T);
  if (inl_of(cb, k) === null && !(m.all.length > 0
    && term_const(m.all[0]) && live === tld.n
    && tele.doms.length === tld.n && adt_triv(cb.book, tele.ret)
    && inl_fit(cb, raw, k))) {
    return null;
  }
  let fuel = 32;
  const sp = { ...tld, v: raw };
  const tlds = { get [k](): Bend.TLD | undefined {
    return (fuel -= 1) >= 0 ? sp : undefined;
  } } as Bend.Book["tlds"];
  const fb = { ...cb.book, tlds };
  const out = Bend.term_wnf(fb,
    m.all.reduce((f, x) => Bend.App(f, x), m.t as Bend.HTerm));
  const [h, hx] = Bend.term_unapply(Bend.term_strip(out));
  if ((h.$ === "Ref" && h.k === k && hx.length === tld.n)
    || !inl_calls(cb, out) || !calm_of(cb, out)) {
    return null;
  }
  inl_tally(cb, fb, out, new Set());
  return Bend.Ann(out, ty_tele(cb.book, tld.T, m.all));
}

function inl_tally(cb: Carb, fb: Bend.Book, t: Bend.HTerm,
  seen: Set<Bend.HTerm>): void {
  if (t.$ === "Var" && t.i < 0) {
    if (seen.has(t)) {
      SHARE.set(t, SHARE.get(t) ?? null);
      return;
    }
    seen.add(t);
    Bend.term_wnf(fb, t);
  }
  const s = Bend.term_force(t);
  if (seen.has(s)) {
    return;
  }
  seen.add(s);
  for (const x of term_kids(cb, s)) {
    inl_tally(cb, fb, x, seen);
  }
}

// Done
// ====

function done_live(tld: Bend.TLD | undefined): tld is Bend.Def {
  return tld?.$ === "Def" && tld.v !== null;
}

function done_defs(cb: Carb): [Bend.Name, Def][] {
  return [...cb.done].map((k) => [k, cb.book.tlds[k]] as [Bend.Name, Def])
    .filter((p) => done_live(p[1]));
}

// Brw
// ===

function brw_type(cb: Carb, A: Bend.HTerm): boolean {
  const t = Bend.term_wnf(cb.book, A);
  return t.$ === "ADT" && OPTIMIZED[t.k]?.C === undefined
    && !adt_triv(cb.book, A);
}

// Cid
// ===

function cid_mac(k: string): string {
  return `CID_${name_clean(k).toUpperCase()}`;
}

function cid_reg(fl: File, k: Bend.Name, abi = 0): string {
  if (!fl.cids.has(k)) {
    const ctr = fl.book.ctrs[k];
    fl.cids.set(k, { packed: ctr_scalar1(fl.book, k),
      arity: ctr === undefined ? abi : ctr_doms(fl.book, ctr).length });
  }
  return cid_mac(k);
}

// File
// ====

function file_push(fl: File | Js, line: string): void {
  fl.seg.lines.push("  ".repeat(fl.tab) + line);
}

// Block
// =====

function block(fl: File | Js, open: string, go: () => void): void {
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

// Bind
// ====

function bind_pop(fl: File, x: Bend.HTerm): string {
  const p = probe_of(x);
  const b = fl.uses.get(p);
  if (b === undefined) {
    die(`an unbound binder: ${p.k}`);
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
  } else {
    fl.uses.set(p, { ...b, owed: b.owed - 1 });
    file_push(fl, `${b.local} = term_keep(e, ${b.local});`);
  }
  return b.local;
}

function bind_uses(fl: File, local: string, p: Probe, b: Bend.HTerm,
  ty: Bend.HTerm | null, parts?: Parts): Bend.HTerm {
  if (parts !== undefined && !parts.w) {
    local = emit_alias(fl, ctr_build(fl, parts.k, parts.vs), p.k);
    parts = undefined;
  }
  const brw = fl.brwl.has(local);
  const triv = parts !== undefined || brw || adt_triv(fl.book, ty);
  const n = term_use(term_uses(fl.cb, b), p);
  if (n === 0 && !brw) {
    if (parts !== undefined) {
      parts.vs.forEach((v) => file_push(fl, `term_sink(e, ${v});`));
    } else if (!triv) {
      file_push(fl, `term_sink(e, ${local});`);
    }
  } else {
    fl.uses.set(p, { owed: triv ? 1 : n, local, triv, parts });
  }
  return b;
}

// Seg
// ===

function seg_new(fl: File, name: string, seq: boolean,
  params: string[], def = ""): Seg {
  const seg: Seg = { fid: seg_fid(name), def, lines: [],
    params, refs: new Set(),
    frame: seq ? { pop: params.length - 1, base: 0 } : null };
  fl.segs.push(seg);
  return seg;
}

function seg_fid(k: Bend.Name): string {
  return `FID_${name_clean(k).toUpperCase()}`;
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

// Eq
// ==

function eq_set(fl: File, t: Bend.HTerm): { p: Probe; ks: number[] } | null {
  const st = Bend.term_strip(t);
  if (st.$ === "Let") {
    const v = Bend.term_strip(st.v[0]);
    return st.k.length === 1 && v.$ === "Var" ? eq_set(fl, st.f([v])) : null;
  }
  const sp = term_spine(fl, t);
  if (sp.t.$ === "Ref" && sp.args.length === 1) {
    const b = inl_of(fl.cb, sp.t.k);
    const w = b === null ? null : Bend.term_strip(b);
    if (w?.$ === "Mat") {
      const bs = Object.fromEntries(mat_arms(w).arms.map(([k2, h2]) =>
        [k2, Bend.u32_from_term(h2)]));
      if (bs.False === 0 && bs.True === 1) {
        return eq_set(fl, sp.args[0]);
      }
    }
  }
  if (sp.t.$ !== "Ref" || sp.args.length !== 2) {
    return null;
  }
  const it = intr_of(fl, sp.t.k);
  if (it === OPERATIONS.bool_or) {
    const l = eq_set(fl, sp.args[0]);
    const r = eq_set(fl, sp.args[1]);
    return l !== null && r !== null && l.p === r.p
      ? { p: l.p, ks: [...l.ks, ...r.ks] } : null;
  }
  if (it === OPERATIONS.u32_is_eq) {
    const vs = sp.args.map((a) => Bend.u32_from_term(a));
    for (const i of [0, 1]) {
      const w = vs[1 - i];
      const xi = Bend.term_strip(sp.args[i]);
      if (xi.$ === "Var" && w !== null) {
        return { p: probe_of(xi), ks: [w] };
      }
    }
  }
  return null;
}

function eq_mask(ks: number[]): { m: number; K: number } | null {
  const u = [...new Set(ks)].sort((p, q) => p - q);
  const d = u.length === 2 ? u[0] ^ u[1] : 0;
  return (u.length === 1 || u.length === 2) && (d & (d - 1)) === 0
    ? { m: d, K: u[u.length - 1] } : null;
}

// Sel
// ===

function sel_walk(fl: File, t: Bend.HTerm,
  leaf: (x: Bend.HTerm) => boolean): boolean {
  const m = term_spine(fl, t);
  const it = m.t.$ === "Ref" ? intr_of(fl, m.t.k) : undefined;
  if (it !== undefined && !it.call) {
    return m.args.every((a) => sel_walk(fl, a, leaf));
  }
  return leaf(t);
}

function sel_ok(fl: File, t: Bend.HTerm): boolean {
  return sel_walk(fl, t, (y) => {
    const x = Bend.term_strip(y);
    if (x.$ === "Var") {
      const b = fl.uses.get(probe_of(x));
      return b?.triv === true && b.parts === undefined;
    }
    return Bend.u32_from_term(x) !== null;
  });
}

// Fuse
// ====

function fuse_ban(ck: Call): boolean {
  return ck.bang === true || ck.k === CLO_APPLY;
}

function fuse_lends(fl: File, k: Bend.Name): boolean {
  return def_foreign(fl.book.tlds[k])
    || (fl.cb.brw.get(k) ?? []).some(Boolean);
}

function fuse_ret(fl: File, k: Bend.Name):
  { rec: { k: Bend.Name; n: number } | null } | null {
  const tld = fl.book.tlds[k];
  if (tld?.$ !== "Def" || tld.h === undefined) {
    return null;
  }
  const tele = tele_unbind(fl.book, tld.T);
  if (tele.doms.slice(tld.n).some(live_dom)) {
    return null;
  }
  const word = adt_triv(fl.book, tele.ret);
  const adt = Bend.term_wnf(fl.book, tele.ret);
  const rt = adt.$ === "ADT" ? fl.book.tlds[adt.k] : undefined;
  const one = rt?.$ === "ADT" && rt.c.length === 1 ? rt.c[0] : null;
  const doms = one && ctr_doms(fl.book, one);
  const rec = word || doms === null || doms.length < 2 ? null
    : { k: (one as Bend.Ctr).k, n: doms.length };
  const ok = word || rec !== null || call_has(fl.cb, tld.h as Bend.HTerm);
  return ok ? { rec } : null;
}

function fuse_lets(fl: File, s: Bend.HTerm, k: Bend.Name | null): boolean {
  return s.$ === "Let" && s.v.some((v) => {
    const c2 = call_kind(fl, v);
    return c2 !== null && (c2.k === k || (call_fuse(fl, v) === null
      && fuse_ret(fl, c2.k) === null));
  });
}

function fuse_deep(fl: File, k: Bend.Name,
  path: Map<Bend.Name, boolean>): boolean {
  const got = DEEPS.get(k) ?? path.get(k);
  if (got !== undefined) {
    return got;
  }
  const tld = fl.book.tlds[k];
  path.set(k, false);
  const ok = tld?.$ === "Def" && tld.h !== undefined && !fuse_lends(fl, k)
    && !term_any(fl, tld.h as Bend.HTerm, (s) => {
      if ((s.$ === "Let" && s.k.length >= 2) || fuse_lets(fl, s, null)) {
        return true;
      }
      const c = call_kind(fl, s);
      return c !== null && call_fuse(fl, s) === null
        && (fuse_ban(c) || !fuse_deep(fl, c.k, path));
    });
  DEEPS.set(k, ok);
  return ok;
}

function fuse_leaf(fl: File, ck: Call, dst: Dst): boolean {
  if (fuse_ban(ck) || inl_of(fl.cb, ck.k) === null) {
    return false;
  }
  const tld = fl.book.tlds[ck.k] as Def;
  const lent = fl.cb.brw.get(ck.k);
  const mine: string[] = [];
  const args: Arg[] = ck.args.map((a, j) => {
    if (lent?.[j] !== true) {
      return arg_fuse(fl, a);
    }
    const local = arg_local(fl, a);
    if (!fl.brwl.has(local)) {
      mine.push(local);
      fl.brwl.add(local);
    }
    return local;
  });
  emit_func(fl, tld.h as Bend.HTerm, tld.T, args, dst);
  mine.forEach((l) => fl.brwl.delete(l));
  return true;
}

// Arg
// ===

function arg_term(fl: File, a: Arg): string {
  return typeof a === "string" ? a : ctr_build(fl, a.k, a.vs);
}

function arg_local(fl: File, a: Bend.HTerm): string {
  return (fl.uses.get(Bend.term_strip(a) as Probe) as Bind).local;
}

function arg_lend(fl: File, ck: Call): string[] {
  const lent = fl.cb.brw.get(ck.k);
  return ck.args.map((a, j) =>
    lent?.[j] ? arg_local(fl, a) : emit_expr(fl, a, null));
}

function arg_arr(fl: File, a: Bend.HTerm): string {
  const el = arr_elem(fl.book, ty_ann(a) ?? die("an untyped block"));
  return arr_flag(fl.book, el) ? "1" : "0";
}

function arg_fuse(fl: File, a: Bend.HTerm): Arg {
  const x = Bend.term_strip(a);
  if (x.$ === "Var") {
    const b = fl.uses.get(probe_of(x));
    if (b?.parts !== undefined) {
      return b.parts;
    }
  }
  const m = term_spine(fl, x);
  const it = m.t.$ === "Ref" ? intr_of(fl, m.t.k) : undefined;
  if (it?.parts !== undefined) {
    const arr = it.flg === undefined ? "0" : arg_arr(fl, m.args[it.flg]);
    const as = emit_exprs(fl, m.args).map((z) => emit_alias(fl, z, "aw"));
    const vs: string[] = [];
    for (const p of it.parts) {
      vs.push(emit_alias(fl, tpl(p)([...as, arr, ...vs]), "aw"));
    }
    return { k: "Tuple", vs, w: false };
  }
  return emit_expr(fl, a, null);
}

// Emit
// ====

function emit_exprs(fl: File, xs: Bend.HTerm[]): string[] {
  return xs.map((a) => emit_expr(fl, a, null));
}

function emit_hold(fl: File | Js, exprs: string[], k: string): string[] {
  return exprs.map((ex) => {
    const al = fl.decl === "Term" ? name_local(fl, k) : js_fresh(fl, k);
    file_push(fl, `${fl.decl} ${al} = ${ex};`);
    return al;
  });
}

function emit_alias(fl: File | Js, e: string, k: string): string {
  const atom = fl.decl === "Term" ? fl.local.has(e) : IDENT.test(e);
  return atom ? e : emit_hold(fl, [e], k)[0];
}

function emit_take(fl: File, v: string, n: number,
  z: boolean): { fb: string; sp: string } {
  const fb = name_local(fl, "fb");
  const sp = name_local(fl, "sp");
  file_push(fl, `Term ${fb}[${n}];`);
  if (z) {
    file_push(fl, `u64 ${sp} = ctr_take(e, ${v}, ${n}, ${fb});`);
  } else {
    file_push(fl, `u64 ${sp} = term_loc(${v});`);
    for (let j = 0; j < n; j += 1) {
      file_push(fl, `${fb}[${j}] = e.mem[${sp} + ${j}];`);
    }
  }
  return { fb, sp };
}

function emit_task(fl: File, fid: string, rem: number, words: string[],
  cont = "WL_CONT", idx: string | number = "WL_IDX"): string {
  return node_fill(fl, "t",
    `task_node(e, ${seg_ref(fl, fid)}, ${cont}, ${idx}, ${rem})`, words);
}

function emit_frame(fl: File, words: string[], next: string): void {
  const n = words.length + 1;
  file_push(fl, `WL_ROOM(${n});`);
  [...words, seg_ref(fl, next)].forEach((w, i) => {
    file_push(fl, `STK(${i}) = ${w};`);
  });
  file_push(fl, `WL_PUSHN(${n});`);
}

function emit_bang(fl: File, ck: Call, args: string[]): void {
  const fid = seg_fid(ck.k);
  file_push(fl, `return term_tsk(${fid}, ${emit_task(fl, fid, 0, args)});`);
}

function emit_jump(fl: File, args: string[], k: Bend.Name): void {
  if (fl.seg.def !== k) {
    args.forEach((a, i) => file_push(fl, `r${i} = ${a};`));
    return file_push(fl, `WL_JMP(${seg_ref(fl, seg_fid(k))});`);
  }
  fl.seg.spin = true;
  emit_hold(fl, args, "j").forEach((j, i) => {
    const u = fl.seg.unbox?.[i];
    file_push(fl,
      `${fl.seg.params[i]} = ${u == null ? j : `${u}_unbox(${j})`};`);
  });
  file_push(fl, "WL_AGAIN;");
}

function emit_call(fl: File, ck: Call, km: Call | null): void {
  const cargs = arg_lend(fl, ck);
  const cexps = km === null ? [] : emit_exprs(fl, km.args.slice(0, -1));
  spare_flush(fl);
  if (km !== null) {
    const kf = seg_fid(km.k);
    emit_chain(fl, () => "seq", [() => emit_frame(fl, cexps, kf), () => {
      file_push(fl,
        `WL_KONT(${kf}, ${emit_task(fl, kf, 1, cexps)}, ${cexps.length});`);
      if (ck.bang) {
        emit_bang(fl, ck, cargs);
      }
    }]);
  } else if (ck.bang) {
    block(fl, "if (!seq) {", () => emit_bang(fl, ck, cargs));
  }
  emit_jump(fl, cargs, ck.k);
}

function emit_put(fl: File, dst: Dst, e: string): void {
  if (dst === null) {
    spare_flush(fl);
    file_push(fl, `WL_RET(${e});`);
  } else {
    file_push(fl, `${dst[0]} = ${e};`);
  }
}

function emit_open(fl: File, x: HLet): Bend.HTerm {
  const o = term_lets(x);
  x.k.forEach((k, j) => {
    const name = name_local(fl, k);
    file_push(fl, `Term ${name} = ${emit_expr(fl, x.v[j], null)};`);
    bind_uses(fl, name, o.ps[j], o.b, ty_ann(x.v[j]));
  });
  return o.b;
}

function emit_expr(fl: File, tm: Bend.HTerm, ty0: Bend.HTerm | null): string {
  const [x, ty] = ty_peel(tm, ty0);
  switch (x.$) {
    case "Var": return bind_pop(fl, x);
    case "Ref":
    case "App": {
      const m = term_spine(fl, x);
      const ck = call_fuse(fl, x);
      if (ck !== null) {
        const t = emit_hold(fl, ["0"], "t")[0];
        if (!fuse_leaf(fl, ck, [t])) {
          die("an unfusable call in an expression: " + ck.k);
        }
        return t;
      }
      const g = m.t;
      if (g.$ === "Var" && m.args.length === 0) {
        return bind_pop(fl, g);
      }
      if (g.$ !== "Ref") {
        die(`cannot compile a ${g.$}-headed spine`);
      }
      const tld = fl.book.tlds[g.k];
      const intr = intr_of(fl, g.k);
      if (intr === undefined) {
        if (tld?.$ === "Def" && tld.v === null && tld.i === undefined) {
          die(`a live call into the assert ${g.k}`);
        }
        if (m.args.length !== def_live(fl, tld as Bend.Def) - 1) {
          die("an under-applied def value: " + g.k);
        }
        const fid = seg_ref(fl, seg_fid(g.k));
        const exprs = emit_exprs(fl, m.args);
        return `term_clo(${fid}, ${exprs.length === 0 ? 0 : node_fill(fl,
          "nd", `heap_alloc(e, cls_fit(${exprs.length}))`, exprs,
          fl.cb.clo)})`;
      }
      if (intr.parts !== undefined) {
        return arg_term(fl, arg_fuse(fl, x));
      }
      const args = emit_exprs(fl, m.args);
      const exprs = tpl_dup(intr.C!)
        ? args.map((a) => emit_alias(fl, a, "a")) : args;
      if (intr.flg !== undefined) {
        exprs.push(arg_arr(fl, m.args[intr.flg]));
      }
      return tpl_run(intr.C!, exprs);
    }
    case "Ctr": {
      const [adt, u] = ctr_adt(fl, x, ty);
      if (u !== null) {
        return `${u}ull`;
      }
      const exprs = emit_exprs(fl, ctr_flds(fl.book, x.k, x.x));
      const native = native_of(fl.book, adt);
      if (native !== undefined) {
        const fn = native.intr[x.k];
        if (fn === undefined) {
          die(`no native introduction for a computed ${x.k}`);
        }
        if (adt.k === "Array") {
          exprs.push(arr_flag(fl.book, adt.x[0]) ? "1" : "0");
        }
        return tpl_run(fn, exprs);
      }
      return ctr_build(fl, x.k, exprs);
    }
    case "Let": return emit_expr(fl, emit_open(fl, x), null);
    case "Rwt": return emit_expr(fl, x.f, ty);
    case "Sub": case "Lam": case "Mat": case "Efq":
      die(`cannot compile a ${x.$} node`);
    default: return "0ull";
  }
}

function emit_func(fl: File, tm: Bend.HTerm, ty0: Bend.HTerm | null,
  args: Arg[], dst: Dst): void {
  const [x, ty] = ty_peel(tm, ty0);
  switch (x.$) {
    case "Lam": {
      const all = Bend.term_wnf(fl.book, ty as Bend.HTerm) as HAll;
      if (!quant_live(all.q)) {
        return emit_func(fl, x.f(DUMMY), all.B(DUMMY), args, dst);
      }
      const a0 = args[0];
      const name = typeof a0 === "string" ? emit_alias(fl, a0, x.k) : "";
      const rec = typeof a0 === "string" ? undefined : a0;
      const o = term_open(x);
      return emit_func(fl, bind_uses(fl, name, o.p, o.b, all.A, rec),
        all.B(DUMMY), args.slice(1), dst);
    }
    case "Mat":
    case "Efq": {
      const a0 = args[0];
      const { arms, end } = mat_arms(x);
      if (typeof a0 !== "string" && x.$ === "Mat" && arms.length === 1
        && end === null && arms[0][0] === a0.k) {
        return emit_func(fl, arms[0][1], null,
          [...a0.vs, ...args.slice(1)], dst);
      }
      const s = emit_alias(fl, arg_term(fl, args[0]), "s");
      const rest = args.slice(1).map((a) => arg_term(fl, a));
      if (x.$ === "Efq") {
        return emit_stuck(fl);
      }
      const all = Bend.term_wnf(fl.book, ty as Bend.HTerm) as HAll;
      const adt = Bend.term_wnf(fl.book, all.A) as HAdt;
      const total = Bend.book_adt(fl.book, adt, Bend.Emp()).c.length;
      if (adt.k === "IO.OP") {
        block(fl, `if (term_aux(${s}) > CID_HALT) {`, () => emit_stuck(fl));
      }
      if (adt.k === "Bool" && arms.length === 2 && rest.length === 0) {
        const { True: hT, False: hF } = Object.fromEntries(arms);
        const eT = eq_set(fl, hT);
        const eF = eq_set(fl, hF);
        const mT = eT && eq_mask(eT.ks);
        const mF = eF && eq_mask(eF.ks);
        if (mT !== null && mF !== null && mT.K === mF.K && eT!.p === eF!.p) {
          const sel = mT.m === mF.m ? `${mT.m}u`
            : `(${s} != 0 ? ${mT.m}u : ${mF.m}u)`;
          return emit_put(fl, dst, `U32_BIN(U32_BIN(${bind_pop(fl, eT!.p)}`
            + `, |, ${sel}), ==, ${mT.K}u)`);
        }
        if (sel_ok(fl, hT) && sel_ok(fl, hF)) {
          return emit_put(fl, dst, `(${s} != 0 ? ${emit_expr(fl, hT, null)}`
            + ` : ${emit_expr(fl, hF, null)})`);
        }
      }
      if (adt.k === "Nat" && ty_w32(fl.book, all.B(DUMMY))) {
        const tab_ok = (t: Bend.HTerm): boolean => sel_walk(fl, t, term_const);
        const ls: Bend.HTerm[] = [];
        let m = Bend.term_strip(x);
        while (m.$ === "Mat") {
          const { arms, end } = mat_arms(m);
          const { Zero, Succ } = Object.fromEntries(arms);
          if (end !== null || Zero === undefined || Succ === undefined) {
            break;
          }
          ls.push(Zero);
          m = Bend.term_strip(Succ);
        }
        if (m.$ !== "Mat") {
          ls.push(m.$ === "Lam" ? term_open(m).b : m);
          if (ls.length >= 3 && ls.every(tab_ok)) {
            const key = emit_exprs(fl, ls).join(", ");
            const id = fl.tabs.get(key) ?? fl.tabs.size;
            fl.tabs.set(key, id);
            return emit_put(fl, dst,
              `TAB_AT(TAB_${id}, ${s}, ${ls.length - 1})`);
          }
        }
      }
      const native = native_of(fl.book, adt);
      const sharable = fl.shr.has("t:" + adt.k);
      const brw = fl.brwl.has(s);
      const hs = arms.map(([, h]) => h);
      const emits = arms.map(([k, h]) => () => arm_emit(h, k));
      if (end !== null || arms.length < total) {
        const last: Bend.HTerm = end ?? Bend.Efq();
        hs.push(last);
        emits.push(() => fin(last, [s, ...rest]));
      }
      const mx_of = (p: Probe) => hs.reduce((m, h) =>
        Math.max(m, term_use(term_uses(fl.cb, h), p)), 0);
      function fin(h2: Bend.HTerm, args: string[]) {
        for (const [p, b] of [...fl.uses]) {
          const use = term_use(term_uses(fl.cb, h2), p);
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
      function arm_emit(h: Bend.HTerm, k: Bend.Name) {
        let fexprs: string[];
        if (native !== undefined) {
          fexprs = (native.elim?.[k] ?? []).map((t) => tpl(t)([s]));
        } else {
          cid_reg(fl, k);
          const { arity: live, packed } = fl.cids.get(k)!;
          if (packed || live === 0) {
            fexprs = packed ? [`term_loc(${s})`] : [];
          } else if (brw) {
            const bl = name_local(fl, "bl");
            file_push(fl, `u64 ${bl} = term_peek(e, ${s});`);
            fexprs = Array.from({ length: live },
              (_, j) => `e.mem[${bl} + ${j}]`);
          } else {
            const { fb, sp } = emit_take(fl, s, live, sharable);
            if (dst === null) {
              fl.spares.push({ words: live, name: sp, z: sharable });
            } else {
              spare_free(fl, live, sp, sharable);
            }
            fexprs = Array.from({ length: live }, (_, j) => `${fb}[${j}]`);
          }
        }
        const fields = emit_hold(fl, fexprs, "f");
        if (brw) {
          ctr_doms(fl.book, fl.book.ctrs[k] as Bend.Ctr).forEach((A, j) => {
            if (!adt_triv(fl.book, A)) {
              fl.brwl.add(fields[j]);
            }
          });
        }
        fin(h, [...fields, ...rest]);
      }
      if (arms.length === 1 && total === 1) {
        return arm_emit(arms[0][1], arms[0][0]);
      }
      const held = [...fl.uses].filter(([p, b]) =>
        !b.triv && b.owed > mx_of(p));
      for (const [p, b] of held) {
        fl.uses.set(p, { ...b, owed: Infinity });
      }
      emit_chain(fl, (i) => {
        const k = arms[i][0];
        if (native === undefined) {
          return `term_aux(${s}) == ${cid_reg(fl, k)}`;
        }
        const c = native.cond?.[k] ?? die(`no native test for a ${k} match`);
        return tpl(c)([s]);
      }, emits.map((go) => () => {
        const spares = fl.spares;
        fl.spares = dst === null ? spares.slice() : [];
        const uses = new Map(fl.uses);
        go();
        fl.spares = spares;
        fl.uses = uses;
      }));
      for (const [p, b] of held) {
        fl.uses.set(p, { ...b, owed: b.owed - mx_of(p) });
      }
      return;
    }
    case "Let": {
      if (x.k.length >= 2) {
        const tab0 = fl.tab;
        const n = x.k.length;
        const calls = x.v.map((v) => call_kind(fl, v) as Call);
        const jc = call_kind(fl, term_lets(x).b) as Call;
        const alias = (x: string) => emit_alias(fl, x, "a");
        const margs = calls.map((c) => arg_lend(fl, c).map(alias));
        const caps = emit_exprs(fl, jc.args.slice(0, -n)).map(alias);
        spare_flush(fl);
        const m = caps.length;
        const kj = seg_fid(jc.k);
        const fj = calls.map((c) => seg_fid(c.k));
        block(fl, "if (!seq) {", () => {
          const jn = emit_task(fl, kj, n, caps);
          const jt = `term_tsk(${kj}, ${jn})`;
          for (let j = 0; j < n; j += 1) {
            file_push(fl, `WL_KID(${jn}, ${m + j}, ${fj[j]}, ${
              emit_task(fl, fj[j], 0, margs[j], jt, m + j)});`);
          }
          file_push(fl, `return ${jt};`);
        });
        const w0 = margs.slice(1).reverse().flat().concat(caps);
        const home = fl.seg;
        fl.tab = 2;
        const steps: Seg[] = new Array(n);
        for (let j = n; j >= 1; j -= 1) {
          const pa = (j < n ? margs[j] : caps).map(() => name_local(fl, "a"));
          for (let t = j < n ? 1 : n; t > 0; t -= 1) {
            pa.push(name_local(fl, "x"));
          }
          steps[j - 1] = seg_new(fl, name_local(fl, `${home.def}_s`), true, pa);
        }
        let under = m;
        for (let j = 1; j < n; j += 1) {
          fl.seg = steps[j - 1];
          under += margs[j].length;
          fl.seg.frame = { pop: 0, base: -under };
          const ps = fl.seg.params;
          emit_frame(fl, [ps[ps.length - 1]], steps[j].fid);
          emit_jump(fl, ps.slice(0, -1), calls[j].k);
          under += 1;
        }
        fl.seg = steps[n - 1];
        fl.seg.frame = { pop: w0.length + n - 1, base: w0.length - m };
        emit_jump(fl, fl.seg.params, jc.k);
        fl.seg = home;
        fl.tab = tab0;
        emit_frame(fl, w0, steps[0].fid);
        emit_jump(fl, margs[0], calls[0].k);
        return;
      }
      const vc = call_kind(fl, x.v[0]);
      if (vc !== null && call_fuse(fl, x.v[0]) === null) {
        const km = call_kind(fl, term_lets(x).b) as Call;
        const fr = fuse_ban(vc) || fuse_lends(fl, vc.k) || fuse_lends(fl, km.k)
          ? null : fuse_ret(fl, vc.k);
        if (fr === null) {
          return emit_call(fl, vc, km);
        }
        const tld = fl.book.tlds[vc.k] as Def;
        const jt = fl.book.tlds[km.k] as Def;
        const body = tld.h as Bend.HTerm;
        const pure = memo(PURES, body, () => !term_any(fl, body, (s) => {
          if (fuse_lets(fl, s, vc.k)) {
            return true;
          }
          const c = call_kind(fl, s);
          return c !== null && c.k !== vc.k && call_fuse(fl, s) === null
            && !fuse_deep(fl, c.k, new Map([[vc.k, false]]));
        }) && calm_of(fl.cb, body));
        if (!(pure || fuse_deep(fl, vc.k, new Map()))) {
          return emit_call(fl, vc, km);
        }
        const rec = fr.rec;
        const sp = term_any(fl, body, (s) => call_kind(fl, s)?.k === vc.k)
          ? emit_hold(fl, emit_exprs(fl, vc.args), "p") : null;
        const ps = sp ?? vc.args.map((a) => Bend.term_strip(a).$ === "Var"
          ? emit_expr(fl, a, null) : arg_fuse(fl, a));
        const caps = emit_exprs(fl, km.args.slice(0, -1));
        const vs = emit_hold(fl,
          Array.from({ length: rec?.n ?? 1 }, () => "0"), "x");
        if (sp !== null) {
          const spares = fl.spares;
          fl.spares = [];
          const at = fl.seg.lines.length;
          const seg = fl.seg;
          fl.seg = { ...seg, def: vc.k, params: sp, unbox: undefined };
          block(fl, "WL_SPIN", () => {
            emit_func(fl, body, tld.T, sp, vs);
            fl.seg = seg;
            file_push(fl, "break;");
          });
          const spun = fl.seg.lines.splice(at);
          const off = "  ".repeat(fl.tab - 1);
          const bent = spun.map((l) =>
            "  " + (l.startsWith(off) ? l.slice(off.length) : l));
          const name = seg_ref(fl, "spin_" + fl.spins.length);
          fl.spins.push([`  static Term ${name}(Env e, THR Term* o${
            sp.map((p) => ", Term " + p).join("")}) {`,
            "    u32 wpoll = 0;", ...vs.map((v) => `    Term ${v} = 0;`),
            ...bent, ...vs.map((v, j) => `    o[${j}] = ${v};`),
            "    return 1;", "  }"].join("\n"));
          const o = name_local(fl, "o");
          file_push(fl, "#if DEVICE");
          file_push(fl, `Term ${o}[${Math.max(vs.length, sp.length)}];`);
          block(fl,
            `if (Spin::${name}(${["e", o, ...sp].join(", ")}) == 0) {`, () => {
            file_push(fl, "return 0;");
          });
          vs.forEach((v, j) => file_push(fl, `${v} = ${o}[${j}];`));
          file_push(fl, "#else");
          fl.seg.lines.push(...spun);
          file_push(fl, "#endif");
          fl.spares = spares;
        } else {
          emit_func(fl, body, tld.T, ps, vs);
        }
        emit_func(fl, jt.h as Bend.HTerm, jt.T,
          [...caps, rec === null ? vs[0] : { k: rec.k, vs, w: true }], dst);
        return;
      }
      return emit_func(fl, emit_open(fl, x), null, [], dst);
    }
    default: {
      const ck = call_kind(fl, x);
      if (ck !== null) {
        if (fuse_leaf(fl, ck, dst)) {
          return;
        }
        if (!fuse_ban(ck) && !fuse_lends(fl, ck.k)
          && (dst === null || fuse_deep(fl, ck.k, new Map()))) {
          const tld = fl.book.tlds[ck.k] as Def;
          const body = tld.h as Bend.HTerm;
          const loop = fl.fusing.has(ck.k)
            || term_any(fl, body, (s) => call_kind(fl, s)?.k === ck.k);
          if (!loop
            && !term_any(fl, body, (s) => s.$ === "Let" && s.k.length >= 2)
            && (dst !== null
            || (!(Bend.term_strip(body).$ === "Mat" && term_const(ck.args[0]))
            && call_has(fl.cb, body)))) {
            const args = ck.args.map((a) => arg_fuse(fl, a));
            fl.fusing.add(ck.k);
            emit_func(fl, body, tld.T, args, dst);
            fl.fusing.delete(ck.k);
            return;
          }
        }
        return emit_call(fl, ck, null);
      }
      if (dst !== null && dst.length > 1) {
        if (x.$ !== "Ctr") {
          const a = arg_fuse(fl, x);
          if (typeof a !== "string") {
            a.vs.forEach((v, j) => file_push(fl, `${dst[j]} = ${v};`));
            return;
          }
          const v = emit_alias(fl, a, "v");
          const { fb, sp } = emit_take(fl, v, dst.length, true);
          spare_free(fl, dst.length, sp, true);
          dst.forEach((d, j) => {
            file_push(fl, `${d} = ${fb}[${j}];`);
          });
          return;
        }
        ctr_flds(fl.book, x.k, x.x).forEach((a, j) => {
          file_push(fl, `${dst[j]} = ${emit_expr(fl, a, null)};`);
        });
        return;
      }
      return emit_put(fl, dst, emit_expr(fl, x, ty));
    }
  }
}

function emit_stuck(fl: File): void {
  file_push(fl, "err_post(e.mem, ERR_TAGS);");
  file_push(fl, "return 0;");
}

function emit_chain(fl: File | Js, cond: (i: number) => string,
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

// Width
// =====

function width_fold(text: string, cee: boolean): string {
  const seam_at = (line: string, cap: number): number => {
    let seam = 0;
    let text = false;
    for (let i = 0; i < cap && i < line.length; i += 1) {
      const c = line[i];
      if (text) {
        if (c === "\\") {
          i += 1;
        } else if (c === "\"") {
          text = false;
        }
        continue;
      }
      if (c === "\"") {
        text = true;
      } else if (c === "(" || c === "{" || c === ",") {
        seam = i + 1;
      } else if ((c === "?" || c === ":") && line[i + 1] === " ") {
        seam = i + 1;
      } else if (c === ">" && line[i - 1] === "=") {
        seam = i + 1;
      } else if (cee && c === " ") {
        seam = i + 1;
      }
    }
    return seam;
  };
  const out: string[] = [];
  for (let line of text.split("\n")) {
    const mac = cee && (line.startsWith("#") || line.endsWith("\\"));
    const bent = line.match(/^ */)![0] + "  ";
    while (line.length > 80) {
      const seam = seam_at(line, mac ? 78 : 80);
      if (seam <= bent.length) {
        break;
      }
      out.push(line.slice(0, seam).trimEnd() + (mac ? " \\" : ""));
      line = bent + line.slice(seam).trimStart();
    }
    out.push(line);
  }
  return out.join("\n");
}

// Compile
// =======

export function compile_book(book: Bend.Book): string {
  if (io_type(book) === null) {
    die("main must answer IO<T>");
  }
  const cb = carb_book(book, ["main"]);
  const brw_scan = (k: Bend.Name) => {
    memo_gc();
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
    const guard = (t: Bend.HTerm) => {
      term_any(cb, t, (s) => {
        if (s.$ === "Var") {
          flip(roots.get(probe_of(s)) ?? null);
        }
        if (s.$ === "Ref") {
          cb.brw.get(s.k)?.forEach((_, j) => flip([s.k, j]));
        }
        return false;
      });
    };
    const site = (t: Bend.HTerm, ct: Bend.HTerm | null) => {
      const ck = call_kind(cb, t) as Call;
      const lent = cb.brw.get(ck.k);
      ck.args.forEach((a, j) => {
        const v = Bend.term_strip(a);
        if (!lent?.[j] || v.$ !== "Var") {
          if (lent?.[j]) {
            flip([ck.k, j]);
          }
          return guard(a);
        }
        const p = probe_of(v);
        const held = ct !== null
          && term_spine(cb, ct).args.some((z) => Bend.term_strip(z) === p);
        if (!roots.has(p) && !held) {
          flip([ck.k, j]);
        }
      });
    };
    const leaf = (t: Bend.HTerm) => {
      const x = Bend.term_strip(t);
      if (x.$ === "Let") {
        const o = term_lets(x);
        if (x.k.length >= 2) {
          for (const v of x.v) {
            site(v, o.b);
          }
          return site(o.b, null);
        }
        if (call_is(cb, x.v[0])) {
          site(x.v[0], o.b);
        } else {
          guard(x.v[0]);
        }
        return leaf(o.b);
      }
      if (call_is(cb, x)) {
        return site(x, null);
      }
      return guard(x);
    };
    const walk = (t: Bend.HTerm, plan: (Root | null)[]) => {
      const x = Bend.term_strip(t);
      if (x.$ === "Lam") {
        const o = term_open(x);
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
        const fr = (ctr === undefined ? [] : ctr_tail(cb.book, ctr))
          .map(([q, , A]) => {
          if (!quant_live(q) || adt_triv(cb.book, A)) {
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
    walk(tld.h as Bend.HTerm, def_get_params(cb.book, tld)
      .map(([q]) => (quant_live(q) && (cb.brw.get(k) as boolean[])[(i += 1)]
        ? [k, i] : null)));
    return hit;
  };
  for (const [k, tld] of done_defs(cb)) {
    cb.brw.set(k, live_doms(cb, tld).map(([, , A]) => brw_type(cb, A)));
  }
  for (let go = true; go;) {
    go = false;
    for (const k of cb.brw.keys()) {
      go = brw_scan(k) || go;
    }
  }
  const keeps = new Set<string>();
  const sites: (Bend.HTerm | null)[] = [];
  const held = (B: Bend.HTerm | null, force = false) => {
    const w = ty_wnf(cb.book, B);
    if (w?.$ === "Lam") {
      held(w.f(DUMMY), force);
      return;
    }
    if (w?.$ !== "ADT") {
      cb.clo = cb.clo
        || (force && ["All", "Var", "App", "Mat"].includes(w?.$ as string));
      return;
    }
    const tk = "t:" + w.k;
    const hot = force || keeps.has(tk);
    w.x.forEach((x) => held(x, hot));
    if (!hot || keeps.has(tk)) {
      return;
    }
    keeps.add(tk);
    const tld = cb.book.tlds[w.k];
    if (tld?.$ === "ADT") {
      for (const c of tld.c) {
        keeps.add(c.k);
        const T = ty_tele(cb.book, c.T, w.x);
        tele_unbind(cb.book, T).doms.filter(live_dom)
          .forEach(([, , A]) => held(A, true));
      }
    }
  };
  const site = (A: Bend.HTerm | null, n: number) => {
    sites.push(A);
    const w = ty_wnf(cb.book, A);
    if (n <= 1 || adt_triv(cb.book, A)) {
      return;
    }
    if (w?.$ === "ADT") {
      held(w, true);
    } else {
      cb.clo = true;
    }
  };
  const scan = (t: Bend.HTerm, ty0: Bend.HTerm | null): void => {
    const [s, ty] = ty_peel(t, ty0);
    if (s.$ === "Let") {
      const o = term_lets(s);
      const u = term_uses(cb, o.b);
      s.v.forEach((v, j) => {
        site(ty_ann(v), term_use(u, o.ps[j]));
        scan(v, null);
      });
      return scan(o.b, null);
    }
    if (s.$ === "Lam") {
      const { p, b: body } = term_open(s);
      const n = term_use(term_uses(cb, body), p);
      const all = ty_all(cb.book, ty)
        ?? die(`a binder without a type: ${s.k}`);
      if (quant_live(all.q)) {
        site(all.A, n);
      }
      return scan(body, all.B(p));
    }
    if (s.$ === "App") {
      const m = term_spine(cb, s);
      const it = m.t.$ === "Ref" ? intr_of(cb, m.t.k) : undefined;
      if (it === OPERATIONS.array_get || it === OPERATIONS.array_new) {
        const A = ty_ann(m.args[it.flg as number]);
        const el = A === null ? null : arr_elem(cb.book, A);
        if (el !== null && !ty_w32(cb.book, el)) {
          held(el, true);
        }
      }
    }
    for (const kid of term_kids(cb, s)) {
      scan(kid, null);
    }
  };
  for (const [, tld] of done_defs(cb)) {
    memo_gc();
    scan(tld.h as Bend.HTerm, tld.T);
  }
  for (let seen = -1; seen < keeps.size + Number(cb.clo);) {
    seen = keeps.size + Number(cb.clo);
    sites.forEach((T) => held(T, cb.clo && !adt_triv(cb.book, T)));
  }
  const fl: File = {
    book: cb.book,
    segs: [],
    seg: { fid: "", def: "", lines: [], params: [], frame: null,
      refs: new Set() },
    tab: 2,
    decl: "Term",
    cb,
    cids: new Map(),
    shr: keeps,
    tabs: new Map(),
    spins: [],
    reqs: "",
    fresh: new Map(),
    spares: [],
    uses: new Map(),
    local: new Set(),
    brwl: new Set(),
    fusing: new Set(),
  };
  for (const k of ("Tuple SNil SCon Chr Unit Emit Halt Fail Done File"
    + " Socket Listener None Some").split(" ")) {
    cid_reg(fl, k);
  }
  for (const [k, tld] of done_defs(cb)) {
    fl.fresh = new Map();
    fl.spares = [];
    fl.uses = new Map();
    fl.local = new Set();
    fl.brwl = new Set();
    fl.fusing = new Set();
    memo_gc();
    const live = live_doms(fl, tld);
    const params = live.map(([, n]) => name_local(fl, n));
    (cb.brw.get(k) as boolean[]).forEach((b, i) => {
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
    emit_func(fl, tld.h as Bend.HTerm, tld.T, params, null);
  }
  const seen = new Set<string>();
  fl.reqs += eff_src(new URL("./effs/sys.c", import.meta.url).pathname, seen);
  fl.reqs += NATIVE.IO;
  fl.spares = [];
  for (const k of cb.done) {
    const tld = cb.book.tlds[k];
    if (!def_foreign(tld)) {
      continue;
    }
    fl.reqs += eff_src(tld.i!.find((x) => x.endsWith(".c"))
      ?? die(`a foreign def without a .c import: ${k}`), seen);
    const qp = [...live_doms(fl, tld).map(([, n]) => name_local(fl, n)),
      name_local(fl, "k")];
    fl.seg = seg_new(fl, k, false, qp, k);
    cid_reg(fl, k, qp.length);
    file_push(fl, `WL_RET(${ctr_build(fl, k, qp)});`);
  }
  const live = new Set<string>();
  const grab = (fid: string) => {
    if (!live.has(fid)) {
      live.add(fid);
      fl.segs.find((s) => s.fid === fid)?.refs.forEach(grab);
    }
  };
  grab(seg_fid("main"));
  fl.segs = fl.segs.filter((s) =>
    live.has(s.fid) || def_foreign(cb.book.tlds[s.def]));
  const clo = fl.segs.some((s) => s.refs.has("FID_CLO_APPLY"));
  for (const s of fl.segs) {
    s.dead = !live.has(s.fid) || (!clo && def_foreign(cb.book.tlds[s.def]));
  }
  fl.spins = fl.spins.filter((_, i) => live.has(`spin_${i}`));
  const entries = [...fl.segs,
    { fid: "FID_IO_EMIT", params: [""], frame: null, dead: !clo } as Seg,
    ...clo ? [{ fid: "FID_CLO_APPLY", params: ["", ""],
      frame: null } as Seg] : []];
  const defs: string[] = [];
  for (const ms of [[...fl.cids.keys()].map((k) => [k, cid_mac(k)]),
    [...entries.map((s) => [s.def, s.fid]), ["exit", "FID_EXIT"]]]) {
    const seen = new Map();
    if (ms.length > 65536) {
      die("an id over 65535");
    }
    const w = Math.max(...ms.map((p) => p[1].length));
    ms.forEach(([k, m], i) => {
      if (seen.has(m)) {
        die(`${seen.get(m)} and ${k} collide as ${m}`);
      }
      seen.set(m, k);
      defs.push(`#define ${m.padEnd(w)} ${i}`);
    });
    defs.push("");
  }
  const table = (nm: string, vals: number[]) => {
    if (vals.some((v) => v > 255)) {
      die("an arity over 255");
    }
    defs.push(`CONSTV u8 ${nm}[] = { ${vals.join(", ")} };`, "");
  };
  table("FID_ARITY_T", entries.map((s) => s.params.length));
  table("FID_BANGS_T", entries.map((s) => Number(cb.bangs.has(s.def))));
  const nofk = new Set<Bend.Name>();
  for (const [k, tld] of done_defs(cb)) {
    memo_gc();
    if (!term_any(cb, tld.h as Bend.HTerm, (s) =>
      (s.$ === "Let" && s.k.length >= 2
        && s.v.every((v) => call_kind(cb, v) !== null))
        || call_kind(cb, s)?.k === CLO_APPLY)) {
      nofk.add(k);
    }
  }
  for (let go = true; go;) {
    go = false;
    for (const k of nofk) {
      if ([...REFS.get(k)!].some((g) => REFS.has(g) && !nofk.has(g))) {
        nofk.delete(k);
        go = true;
      }
    }
  }
  table("FID_NOFK_T", entries.map((s) => Number(nofk.has(s.def))));
  table("FID_SEQK_T", entries.map((s) => Number(s.frame !== null)));
  table("CID_ARITY_T", [...fl.cids.values()].map((c) => c.arity));
  for (const [rows, i] of fl.tabs) {
    defs.push(`CONSTV u64 TAB_${i}[] = { ${rows} };`, "");
  }
  const bank = Math.max(1, ...entries.filter((s) => s.frame === null)
    .map((s) => s.params.length));
  const ns = [...Array(bank).keys()];
  const rs = ns.map((i) => "r" + i).join(", ");
  const load = [...ns].reverse().map((r) =>
    `    case ${r + 1}: r${r} = e.mem[a + ${r}]; \\\n`).join("");
  defs.push(`#define IO_HOTS ${"SCon Tuple Done Fail".split(" ")
    .reduce((m, k, i) => m | (fl.shr.has(k) ? 1 << i : 0), 0)}`, "");
  const pass = ns.map((i) =>
    `    case ${i}: r${i} = res; \\\n      break; \\\n`).join("");
  defs.push(`#define WL_LAST \\\n  switch (war) { \\\n${pass}  }`);
  if (cb.clo) {
    defs.push("#define CLO_SHR 1", "");
  }
  defs.push(`#define WL_BANK Term ${rs};`, "", "#define WL_LOAD \\\n"
    + `  switch (war) { \\\n${load}  }`, "",
    `#define WL_LABELS ${entries.map((s) =>
      "&&L_" + (s.dead ? "FID_EXIT" : s.fid))
      .join(", ")}, &&L_FID_EXIT`);
  const segs = fl.segs.filter((s) => !s.dead).map((seg) => {
    const out: string[] = [`  WL_CASE(${seg.fid})`, "  {"];
    const fr = seg.frame;
    if (fr !== null && fr.pop > 0) {
      out.push(`    WL_POPN(${fr.pop});`);
    }
    seg.params.forEach((p, i) => {
      let src = `r${i}`;
      if (fr !== null) {
        src = i === seg.params.length - 1 ? "res" : `STK(${fr.base + i})`;
      }
      const u = seg.unbox?.[i];
      out.push(`    ${u ?? "Term"} ${p} = `
        + `${u == null ? src : `${u}_unbox(${src})`};`);
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
  }).join("\n\n");
  const spins = fl.spins.length === 0 ? "" :
    "#if DEVICE\nstruct Spin {\n"
    + fl.spins.join("\n\n") + "\n};\n#endif\n\n";
  return width_fold(TEMPLATE
    .replace(/^\/\/ Tables\n\/\/ ======$/m,
      (m) => m + "\n\n" + defs.join("\n"))
    .replace(/^\/\/ Segments\n\/\/ ========$/m, (m) =>
      m + "\n\n" + spins + segs)
    .replace(/^\/\/ Requests\n\/\/ ========$/m, (m) => m + "\n\n" + fl.reqs),
  true);
}

// Js
// ==

function js_fresh(fl: Js, k: Bend.Name): string {
  const n = fl.fresh.get(k) ?? 0;
  fl.fresh.set(k, n + 1);
  return k.replace(/\./g, "$") + "$" + n;
}

function js_sat(k: Bend.Name): string {
  return "$" + k.replace(/\./g, "$") + "$";
}

function js_f32(bits: number): string {
  const v = Bend.f32_from_bits(bits);
  return Object.is(v, -0) ? "-0" : String(v);
}

function js_intr(book: Bend.Book, k: Bend.Name): Gen | null {
  return def_own(book.tlds[k]) ? OPERATIONS[eff_name(k)]?.JS ?? null : null;
}

function js_call(fl: Js, k: Bend.Name, args: Bend.HTerm[],
  tail: boolean): string {
  let exprs = args.map((x) => js_expr(fl, x, null));
  if (k === CLO_APPLY) {
    const [f, x] = exprs;
    return tail ? "run_jump(" + f + ", [" + x + "])" : f + "(" + x + ")";
  }
  const tld = fl.book.tlds[k] ?? die("unknown name: " + k);
  if (tld.$ === "ADT") {
    return "null";
  }
  const intr = js_intr(fl.book, k);
  if (intr === null && tld.v === null && tld.i === undefined) {
    die("a live call into the assert " + k);
  }
  const live = def_live(fl, tld);
  let pre = "";
  if (exprs.length === live - 1) {
    const v = js_fresh(fl, "x");
    pre = "(" + v + ") => ";
    exprs = [...exprs, v];
  } else if (exprs.length !== live) {
    die("an under-applied def value: " + k);
  }
  if (intr !== null) {
    const xs = exprs.map((e) => ATOM.test(e) || STRLIT.test(e)
      ? e : emit_hold(fl, [e], "x")[0]);
    return pre + tpl_run(intr, xs);
  }
  const all = exprs.join(", ");
  if (def_foreign(tld)) {
    return pre + js_sat(k) + "(" + all + ")";
  }
  if (pre === "" && tail) {
    return "run_jump(" + js_sat(k) + ", [" + all + "])";
  }
  return pre + "run_loop(" + js_sat(k) + "(" + all + "))";
}

function js_open(fl: Js, x: HLet): Bend.HTerm {
  return x.f(x.v.map((v, j): Bend.HTerm => {
    if (!quant_live(x.q[j])) {
      return v;
    }
    const ck = call_kind(fl.cb, v);
    const e = ck === null ? js_expr(fl, v, null)
      : js_call(fl, ck.k, ck.args, false);
    return Bend.Var(emit_hold(fl, [e], x.k[j])[0], 0);
  }));
}

function js_expr(fl: Js, tm: Bend.HTerm,
  ty0: Bend.HTerm | null): string {
  const [x, ty] = ty_peel(tm, ty0);
  switch (x.$) {
    case "Var": return x.k;
    case "Ref":
    case "App": {
      const m = term_spine(fl.cb, x);
      if (m.t.$ === "Var" && m.args.length === 0) {
        return m.t.k;
      }
      if (m.t.$ !== "Ref") {
        die("a " + m.t.$ + "-headed spine in an expression");
      }
      return js_call(fl, m.t.k, m.args, false);
    }
    case "Ctr": {
      const [adt, u] = ctr_adt(fl, x, ty);
      if (u !== null) {
        return adt.k === "F32" ? js_f32(u) : String(u);
      }
      if (fl.book.ctrs[x.k] === undefined) {
        die("unknown constructor: " + x.k);
      }
      const exprs = ctr_flds(fl.book, x.k, x.x)
        .map((f) => js_expr(fl, f, null));
      const native = OPTIMIZED[adt.k]?.JS;
      if (native !== undefined) {
        const it = native.intr[x.k];
        if (it === undefined
          || (native.elim?.[x.k] ?? []).length !== exprs.length) {
          die(x.k + NATIVE_DIE);
        }
        return tpl_run(it, exprs);
      }
      return exprs.reduce((e, z, j) => e + ", $" + j + ": " + z,
        "{$: \"" + x.k + "\"") + "}";
    }
    case "Let": return js_expr(fl, js_open(fl, x), ty);
    case "Rwt": return js_expr(fl, x.f, ty);
    case "Sub": case "Lam": case "Mat": case "Efq":
      die("cannot compile a " + x.$ + " node");
    default: return "null";
  }
}

function js_func(fl: Js, tm: Bend.HTerm, ty0: Bend.HTerm | null,
  args: string[]): void {
  const [x, ty] = ty_peel(tm, ty0);
  if (x.$ === "Lam") {
    const all = ty_all(fl.book, ty)
      ?? die("a Lam without a function-typed Ann");
    if (!quant_live(all.q)) {
      const nul: Bend.HTerm = Bend.Var("null", 0);
      return js_func(fl, x.f(nul), all.B(nul), args);
    }
    if (args.length === 0) {
      die("a function layer past its arity");
    }
    const v: Bend.HTerm = Bend.Var(emit_alias(fl, args[0], x.k), 0);
    return js_func(fl, x.f(v), all.B(v), args.slice(1));
  }
  if (mat_head(x)) {
    if (x.$ === "Efq") {
      file_push(fl, "throw new Error(\"unreachable\");");
      return;
    }
    const s = emit_alias(fl, args[0], "$t");
    const rest = args.slice(1);
    const all = ty_all(fl.book, ty)
      ?? die("a match without a function-typed Ann");
    const adt = Bend.term_wnf(fl.book, all.A);
    if (adt.$ !== "ADT") {
      die("a non-datatype match scrutinee");
    }
    const { arms, end } = mat_arms(x);
    const total = Bend.book_adt(fl.book, adt, Bend.Emp()).c.length;
    if (adt.k === "IO.OP") {
      block(fl, "if (" + s + ".$ === \"$FFI\") {", () => {
        file_push(fl, "throw " + s + ";");
      });
    }
    const last = arms.length === total ? null : end ?? Bend.Efq();
    const native = OPTIMIZED[adt.k]?.JS;
    const arm = (h: Bend.HTerm, k: Bend.Name): void => {
      const ctr = fl.book.ctrs[k] ?? die("unknown constructor: " + k);
      const live = ctr_doms(fl.book, ctr).length;
      let fields: string[];
      if (native !== undefined) {
        const el = native.elim?.[k] ?? [];
        if (el.length !== live) {
          die(k + NATIVE_DIE);
        }
        fields = el.map((e) => tpl(e)([s]));
      } else {
        fields = Array.from({ length: live }, (_, j) => s + ".$" + j);
      }
      js_func(fl, h, null, [...fields, ...rest]);
    };
    if (arms.length === 1 && last === null && total === 1) {
      return arm(arms[0][1], arms[0][0]);
    }
    const bodies = arms.map(([k, h]) => () => arm(h, k));
    if (last !== null) {
      bodies.push(() => js_func(fl, last, null, [s, ...rest]));
    }
    emit_chain(fl, (i) => {
      if (native === undefined) {
        return s + ".$ === \"" + arms[i][0] + "\"";
      }
      const cn = native.cond?.[arms[i][0]] ?? die(arms[i][0] + NATIVE_DIE);
      return tpl(cn)([s]);
    }, bodies);
    return;
  }
  if (x.$ === "Let") {
    return js_func(fl, js_open(fl, x), ty, args);
  }
  const ck = call_kind(fl.cb, x);
  file_push(fl, "return " + (ck === null ? js_expr(fl, x, ty)
    : js_call(fl, ck.k, ck.args, true)) + ";");
}

function js_def(fl: Js, k: Bend.Name, def: Def): void {
  fl.fresh = new Map();
  if (js_intr(fl.book, k.split("$")[0]) !== null) {
    return;
  }
  const params = live_doms(fl, def).map(([, n]) => js_fresh(fl, n));
  const kont = def.i === undefined ? [] : [js_fresh(fl, "k")];
  block(fl, "function " + js_sat(k) + "("
    + [...params, ...kont].join(", ") + ") {", () => {
    if (def.i !== undefined) {
      if (def.i.find((p) => p.endsWith(".js")) === undefined) {
        die("a foreign def without a .js import: " + k);
      }
      file_push(fl, "return { $: \"$FFI\", run: () => $0eff." + eff_name(k)
        + "(" + params.join(", ") + "), kont: " + kont[0] + " };");
    } else {
      js_func(fl, def.h ?? die("unelaborated def " + k), def.T, params);
    }
  });
  file_push(fl, "");
}

function js_text(book: Bend.Book): string {
  const roots: Bend.Name[] = [];
  if (book.tlds["main"] !== undefined) {
    roots.push("main");
  } else {
    for (const k of new Set(book.order)) {
      const tld = book.tlds[k];
      if (tld.$ === "Def" && tld.v !== null
        && io_base(book, tld.T) !== null) {
        roots.push(k);
      }
    }
  }
  const cb = carb_book(book, roots);
  const fl: Js = { book: cb.book, cb, seg: { lines: [] }, tab: 0,
    decl: "const", fresh: new Map() };
  for (const [k, def] of done_defs(cb)) {
    memo_gc();
    js_def(fl, k, def);
  }
  for (const k of cb.done) {
    const tld = cb.book.tlds[k];
    if (def_foreign(tld)) {
      js_def(fl, k, tld);
    }
  }
  const seen = new Set<string>();
  const srcs: string[] = [];
  const names: string[] = [];
  for (const k of new Set(book.order)) {
    const tld = book.tlds[k];
    const path = def_foreign(tld)
      ? tld.i!.find((x) => x.endsWith(".js")) : undefined;
    if (path === undefined) {
      continue;
    }
    const src = eff_src(path, seen);
    if (src !== "") {
      srcs.push(src);
    }
    names.push(eff_name(k));
  }
  let effs = "";
  if (srcs.length > 0) {
    const rows = names.map((n) => "  " + n + ": typeof " + n
      + " === \"function\" ? " + n + " : undefined,");
    effs = "const $0eff = (() => {\n" + srcs.join("\n") + "\n"
      + "return {\n" + width_fold(rows.join("\n"), false) + "\n};\n"
      + "})();\n\n";
  }
  const out = RUNTIME + effs + "// Program\n// =======\n\n"
    + width_fold(fl.seg.lines.join("\n"), false);
  const main = book.tlds["main"];
  if (main !== undefined) {
    if (main.$ !== "Def" || main.v === null
      || def_get_params(book, main).some(live_dom)) {
      die("main must be a filled def with no live parameters");
    }
    if (io_type(book) === null) {
      die("main must answer IO<T>");
    }
  }
  return out;
}

export function js_book(book: Bend.Book): string {
  return js_text(book) + (book.tlds["main"] === undefined ? ""
    : "\ncli(process.argv.slice(2));\nio_exit(" + js_sat("main") + ");");
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
#define GRPV    threadgroup
#define GA32    threadgroup atomic_uint
#define THR     thread
#define INLINE  inline
#define HOT     inline
#define OUTLINE static
#define CONSTV  constant
#define DEVICE  1
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
#define GRPV    __shared__
#define GA32    __shared__ u32
#define THR
#define INLINE  static inline
#define HOT     static inline
#define OUTLINE static __attribute__((noinline))
#define CONSTV  static const
#define DEVICE  1
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
#define THR
#define INLINE  static inline
#define HOT     static inline __attribute__((always_inline))
#define OUTLINE static __attribute__((noinline))
#define CONSTV  static const
#define DEVICE  0
#define FENCE() __atomic_thread_fence(__ATOMIC_SEQ_CST)

#define BEND_GPU (BEND_METAL || BEND_CUDA)
#endif

#if DEVICE
#define WL_CASE(F) case F:
#define WL_JMP(F)  { fid = (F); break; }
#define WL_DYN     WL_JMP
#define WL_SPIN \
  for (;;) { \
    if (err_spun(e.mem, &wpoll, 4095)) { \
      return 0; \
    }
#define WL_SPUN    } break;
#else
#define WL_CASE(F) L_##F: ;
#define WL_JMP(F)  goto L_##F
#define WL_DYN(F)  { fid = (F); goto *wl_lbl[fid]; }
#define WL_SPIN    for (;;) {
#define WL_SPUN    }
#endif
#define WL_AGAIN   continue
#define WL_POP()   { sp -= LANE_STEP; WL_DYN((Fid)STK(0)); }

#if DEVICE
#define LANE_STEP CUBE
#else
#define LANE_STEP 1
#endif
#define STK(I) sp[(int64_t)(I) * LANE_STEP]

#define WL_RET(V)          { res = (V); WL_POP(); }
#define WL_CONT            STK(-3)
#define WL_IDX             STK(-2)
#define WL_POPN(N)         sp -= N * LANE_STEP
#define WL_PUSHN(N)        sp += N * LANE_STEP
#define WL_KONT(F, T, I)   WL_CONT = term_tsk(F, T); WL_IDX = I
#define WL_KID(J, A, F, C) e.mem[J + A] = term_tsk(F, C)
#define WL_FRAME(T) \
  Loc wtl = task_tail(T); \
  STK(0) = e.mem[wtl]; \
  STK(1) = e.mem[wtl + 1] >> 32; \
  STK(2) = FID_EXIT; \
  sp += 3 * LANE_STEP;
#define WL_ARGS(A, N) \
  for (u32 wi = 0; wi + 1 < N; wi += 1) { \
    STK(wi) = e.mem[A + wi]; \
  } \
  sp += (N - 1) * LANE_STEP;
#define TAB_AT(T, S, I) T[S < I ? S : I]

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
typedef u32 Cid;

// Term ::=
//   | Wrd(val)
//   | Ctr(cid, loc)
//   | Clo(fid, loc)
//   | Arr(cls, loc)
//   | Buf(cls, loc)
//   | Tsk(fid, loc)
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
#define ERR_HEAP 5
#define ERR_FIDS 6
#define ERR_LEAK 7
#define ERR_NATS 8
#define ERR_RFCS 9
#define ERR_DEEP 10
#define ERR_TICK ((1u << 20) - 1)

typedef u32 Page;
#define PAGE_NIL 0xFFFFFFFEu

typedef u32 Monk;
#define M_RING_PUT         0
#define M_RING_GET         1
#define M_HEAD             2
#define M_HUGE             (2 + 2 * NCLS)
#define M_SNAP             (3 + 2 * NCLS)
#define monk_word(H, m, w) ((H) + MONK_OFF + (u64)(w) * CUBE + (m))

typedef u32 Ring;

#define MONK_OFF 96ull
#define RING_OFF (MONK_OFF + CUBE * MONK_WORDS)
#define STAK_OFF (RING_OFF + CUBE * RING_LEN)

#define H_PAGE_BUMP  0ull
#define H_PAGE_CAP   8ull
#define H_HUGE_FREE  32ull
#define H_ROOT_WORD  56ull
#define H_ROOT_DONE  57ull
#define H_CURSOR     58ull
#define H_ERROR_CODE 64ull

#define HEAP_OFF  (STAK_OFF + CUBE * STAK_LEN)

typedef DEV u64* Corpus;

typedef struct {
  Corpus   mem;
  Monk     mnk;
#if DEVICE
  GRP u64* alc;
#endif
} Env;

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

#define PAGE_BITS    7
#define QUANTUM_BITS (DEVICE ? PAGE_BITS : 12)
#define CUBE_SIDE    128
#define CUBE         (1ull << 14)
#define RING_LEN     (1ull << 10)
#define STAK_LEN     (1ull << 11)
#define MONK_WORDS   32ull
#define NCLS         9
#define HUGE_CLS     (32 - NCLS)
#define ALC_WORDS    (2 * NCLS)

// Globals
// =======

#if !DEVICE

typedef _Atomic u32     au32;
typedef _Atomic u64     au64;
typedef pthread_mutex_t lock;
typedef pthread_cond_t  cond;

static Corpus CORPUS;
static u64    CORPUS_SIZE;

static u32  pool_size;
static au32 pool_row;
static bool pool_grow;
static au64 pool_tick;
static au32 pool_done;
static lock pool_lock = PTHREAD_MUTEX_INITIALIZER;
static cond pool_wake = PTHREAD_COND_INITIALIZER;

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
#if BEND_GPU
static u64 gpu_cap;
#endif

static u64 ALC[CUBE_SIDE][ALC_WORDS];

static bool io_gpu;
static Stk  io_stk;

static const char* CLI_HELP =
  "usage: %s [options]\n"
  "  --threads N        worker threads, up to 128 (default: the CPU count)\n"
  "  --parallel on|off  off means one thread and no GPU (default: on)\n"
  "  --gpu on|off       send ! calls to the GPU (default: on if present)\n"
  "  --gpu-memory 4GB   device span, in MB or GB (default: 2GB on Metal)\n"
  "  --help             show this text\n";

#endif

${NATIVE.C}
// Tables
// ======

// Fid
// ===

INLINE u32 fid_arity(Fid fid) {
  return (u32)FID_ARITY_T[fid];
}

INLINE bool fid_bangs(Fid fid) {
  return (bool)FID_BANGS_T[fid];
}

INLINE bool fid_nofk(Fid fid) {
  return (bool)FID_NOFK_T[fid];
}

INLINE bool fid_seqk(Fid fid) {
  return (bool)FID_SEQK_T[fid];
}

// Cid
// ===

INLINE u32 cid_arity(Cid cid) {
  return (u32)CID_ARITY_T[cid];
}

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
  u32 old = atomicCAS((u32*)p, *e, v);
  bool ok = old == *e;
  *e = old;
  return ok;
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
  if (ok) {
    FENCE();
  }
  return ok;
}

#else

#define a32_load(p)         __atomic_load_n(p, __ATOMIC_RELAXED)
#define a32_store(p, v)     __atomic_store_n(p, v, __ATOMIC_RELAXED)
#define a32_add(p, v)       __atomic_fetch_add(p, v, __ATOMIC_RELAXED)
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
  while (!a32_cas(a32_at(H, H_ERROR_CODE), &seen, code)) {
    if (seen != 0) {
      return;
    }
  }
}

#else

static void err_fail(Err code, const char* msg) {
  fprintf(stderr, "bend: error %u: %s\n", code, msg);
  abort();
}

static void err_post(Corpus H, Err code) {
  err_fail(code, code == ERR_HEAP ? "out of memory" : "runtime fail-stop");
}

static void err_trap(int sig) {
  err_fail(ERR_DEEP, "memory fault (machine stack overflow?)");
}

#endif

INLINE bool err_seen(Corpus H) {
  return a32_load(a32_at(H, H_ERROR_CODE)) != 0;
}

INLINE bool err_spun(Corpus H, THR u32* n, u32 mask) {
  bool tick = (++*n & mask) == 0;
  return tick && err_seen(H);
}

// Cls
// ===

INLINE Cls cls_fit(u32 words) {
  Cls c = 0;
  while ((1u << c) < words) {
    c += 1;
  }
  return c;
}

// Page
// ====

#define page_loc(p) (HEAP_OFF + ((u64)(p) << PAGE_BITS))

INLINE Page page_claim(Corpus H, u32 span) {
  Page cap = a32_load(a32_at(H, H_PAGE_CAP));
  Page p   = DEVICE && err_seen(H) ? cap
    : a32_add(a32_at(H, H_PAGE_BUMP), span);
  if ((u64)p + span > cap) {
    err_post(H, ERR_HEAP);
    p = 0;
  }
  return p;
}

#define BLK_ALLOC(n, w) \
  Loc n = heap_alloc(e, w); \
  if (DEVICE && err_seen(e.mem)) { \
    return term_buf(0, n); \
  }

INLINE Page page_stack_pop(Corpus H, DEV u32* head) {
  for (;;) {
    u32 e = a32_load_acq(head);
    if (e == PAGE_NIL || (DEVICE && err_seen(H))) {
      return PAGE_NIL;
    }
    if (e != (u32)-1 && a32_cas(head, &e, (u32)-1)) {
      u32 next = a32_load(a32_at(H, page_loc(e)));
      a32_store_rel(head, next);
      return e;
    }
  }
}

INLINE void page_stack_push(Corpus H, Cls cls, Loc loc) {
  Page p = (u32)((loc - HEAP_OFF) >> PAGE_BITS);
  DEV u32* head = a32_at(H, H_HUGE_FREE + (cls - NCLS));
  DEV u32* link = a32_at(H, page_loc(p));
  u32 e = a32_load(head);
  for (;;) {
    if (DEVICE && err_seen(H)) {
      return;
    }
    if (e == (u32)-1) {
      e = a32_load(head);
      continue;
    }
    a32_store(link, e);
    if (a32_cas(head, &e, p)) {
      return;
    }
  }
}

// Alc
// ===

#if DEVICE
#define ALC_AT(e, i) (e).alc[(i) * CUBE_SIDE]

INLINE void alc_open(Env e) {
  for (u32 i = 0; i < ALC_WORDS; i += 1) {
    ALC_AT(e, i) = *monk_word(e.mem, e.mnk, M_HEAD + i);
  }
}
INLINE void alc_close(Env e) {
  for (u32 i = 0; i < ALC_WORDS; i += 1) {
    *monk_word(e.mem, e.mnk, M_HEAD + i) = ALC_AT(e, i);
  }
}
#else
#define ALC_AT(e, i) ALC[(e).mnk][i]
#endif

INLINE u64 alc_load(Env e, u32 ride, Cls c) {
  return ALC_AT(e, ride * NCLS + c);
}
INLINE void alc_store(Env e, u32 ride, Cls c, u64 v) {
  ALC_AT(e, ride * NCLS + c) = v;
}

#define cls_quantum(cls) (1u << ((cls) > QUANTUM_BITS ? (cls) : QUANTUM_BITS))

// Heap
// ====

HOT void heap_free_huge(Env e, Cls cls, Loc loc) {
  if (!DEVICE) {
    page_stack_push(e.mem, cls, loc);
    return;
  }
  DEV u64* held = monk_word(e.mem, e.mnk, M_HUGE);
  u64 prev = *held;
  *held = ((u64)cls << 40) | loc;
  if (prev != 0) {
    page_stack_push(e.mem, (u32)(prev >> 40), prev & LOC_MASK);
  }
}

OUTLINE Loc heap_alloc_miss(Env e, Cls cls) {
  Corpus H = e.mem;
  if (cls >= NCLS) {
    if (DEVICE) {
      DEV u64* held = monk_word(H, e.mnk, M_HUGE);
      u64 prev = *held;
      if ((prev >> 40) == cls) {
        *held = 0;
        return prev & LOC_MASK;
      }
    }
    DEV u32* head = a32_at(H, H_HUGE_FREE + (cls - NCLS));
    Page got = page_stack_pop(H, head);
    if (got != PAGE_NIL) {
      return page_loc(got);
    }
    return page_loc(page_claim(H, 1u << (cls - PAGE_BITS)));
  }
  Page p = page_claim(H, cls_quantum(cls) >> PAGE_BITS);
  alc_store(e, 1, cls, ((u64)(1u << cls) << 32) | (p + 1));
  return page_loc(p);
}

HOT Loc heap_alloc(Env e, Cls cls) {
  Corpus H = e.mem;
  if (cls < NCLS) {
    u64 h = alc_load(e, 0, cls);
    if (h != 0) {
      alc_store(e, 0, cls, H[h]);
      return h;
    }
    u64 own  = alc_load(e, 1, cls);
    u32 used = (u32)(own >> 32);
    if ((u32)own != 0 && used < cls_quantum(cls)) {
      alc_store(e, 1, cls, own + ((u64)(1u << cls) << 32));
      return page_loc((u32)own - 1) + used;
    }
  }
  return heap_alloc_miss(e, cls);
}

HOT void heap_free(Env e, Cls cls, Loc loc) {
  Corpus H = e.mem;
  if (DEVICE && err_seen(H)) {
    return;
  }
  if (cls < NCLS) {
    H[loc] = alc_load(e, 0, cls);
    alc_store(e, 0, cls, loc);
  } else {
    heap_free_huge(e, cls, loc);
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

static void term_drop(Env e, Term t);

INLINE Term rfc_wrap(Env e, Term t, u32 cnt) {
  #ifdef CLO_SHR
  if (term_tag(t) == TAG_TSK) {
  #else
  if (term_tag(t) == TAG_CLO || term_tag(t) == TAG_TSK) {
  #endif
    err_post(e.mem, ERR_RFCS);
    return t;
  }
  Loc r = heap_alloc(e, 0);
  e.mem[r] = ((u64)term_loc(t) << 24) | cnt;
  return (t & ~LOC_MASK) | RFC_BIT | r;
}

INLINE Term rfc_seal(Env e, Term t) {
  if (term_triv(t) || term_rfc(t)
    || term_tag(t) == TAG_BUF || term_tag(t) == TAG_ARR) {
    return t;
  }
  return rfc_wrap(e, t, 1);
}

INLINE Term rfc_sole(Env e, Term t) {
  Loc  r = term_loc(t);
  Term s = (t & ~(RFC_BIT | LOC_MASK)) | (e.mem[r] >> 24);
  heap_free(e, 0, r);
  return s;
}

INLINE u64 rfc_view(Env e, Loc r) {
  DEV u32* w = a32_at(e.mem, r);
  u64 cell = ((u64)a32_load(w + 1) << 32) | a32_load(w);
  if ((cell & RFC_CNT) == 1) {
    a32_acq(w);
  }
  return cell;
}

INLINE bool rfc_out(Env e, Loc r) {
  DEV u32* p = a32_at(e.mem, r);
  if ((a32_sub_rel(p, 1) & RFC_CNT) != 1) {
    return false;
  }
  a32_acq(p);
  return true;
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

INLINE Cls blk_cls(Env e, Term t) {
  Cls c = (u32)term_aux(t);
  if (c > 31) {
    err_post(e.mem, ERR_TAGS);
    return 0;
  }
  return c;
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
      t = rfc_out(e, term_loc(t)) ? rfc_sole(e, t) : 0;
    }
    if (!term_triv(t) && term_tag(t) == TAG_CLO
      && fid_arity((u32)term_aux(t)) == 1) {
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
          if (tag == TAG_CTR) {
            n = cid_arity(aux);
          } else if (tag == TAG_CLO) {
            n = fid_arity(aux) - 1;
          } else {
            n = fid_arity(aux);
          }
          cls = cls_fit(tag == TAG_TSK ? n + 2 : n);
        }
        c0 = H[loc];
        H[loc] = cur;
        cur = loc | ((u64)n << 48) | ((u64)cls << 56);
      }
    }
    for (;;) {
      if (err_spun(H, &step, ERR_TICK)) {
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

// Blk
// ===

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

INLINE u32 blk_at(Env e, Term a, U32 i) {
  return (u32)i & (u32)((1ull << blk_cls(e, a)) - 1);
}

OUTLINE Term blk_copy(Env e, Term a) {
  Corpus H = e.mem;
  Cls cls = blk_span(e, a);
  Loc src = term_loc(a);
  BLK_ALLOC(dst, cls)
  for (u64 j = 0; j < (1ull << cls); j += 1) {
    H[dst + j] = H[src + j];
  }
  return (a & ~LOC_MASK) | dst;
}

INLINE Term blk_node(Env e, Term l, Term r) {
  Corpus H = e.mem;
  bool arr = term_tag(l) == TAG_ARR;
  Cls c = blk_cls(e, l);
  if (c != blk_cls(e, r) || c > 30) {
    err_post(H, ERR_TAGS);
    return l;
  }
  Loc pl = term_loc(l);
  Loc pr = term_loc(r);
  Cls ps = arr ? c + 1 : c;
  u64 cw = 0;
  if (arr || c != 0) {
    cw = 1ull << (arr ? c : c - 1);
  }
  if (cw != 0 && pr == pl + cw
    && (ps < NCLS || ((pl - HEAP_OFF) & ((1u << PAGE_BITS) - 1)) == 0)) {
    return term_blk(arr, c + 1, pl);
  }
  BLK_ALLOC(n, ps)
  if (cw == 0) {
    H[n] = (u64)*blk_ptr(H, pl, 0) | ((u64)*blk_ptr(H, pr, 0) << 32);
  } else {
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
  Loc pa = term_loc(a);
  if (!arr && c == 0) {
    u64 v = (u64)*blk_ptr(H, pa, hi);
    if (hi) {
      heap_free(e, 0, pa);
    }
    BLK_ALLOC(n, 0)
    H[n] = v;
    return term_buf(0, n);
  }
  Loc off = 0;
  if (hi) {
    off = 1ull << (arr ? c : c - 1);
  }
  return term_blk(arr, c, pa + off);
}

INLINE Term blk_take(Env e, Term a) {
  Term v = blk_read(e.mem, term_tag(a) == TAG_ARR, term_loc(a), 0);
  heap_free(e, 0, term_loc(a));
  return v;
}

INLINE Term blk_give(Env e, bool arr, Term a, U32 i, Term v) {
  u32 at = blk_at(e, a, i);
  Term old = blk_read(e.mem, arr, term_loc(a), at);
  blk_write(e.mem, arr, term_loc(a), at, v);
  return old;
}

INLINE Term blk_set(Env e, bool arr, Term a, U32 i, Term v) {
  Term old = blk_give(e, arr, a, i, v);
  if (arr) {
    term_sink(e, old);
  }
  return a;
}

HOT Term blk_get(Env e, bool arr, Term a, U32 i) {
  Corpus H = e.mem;
  u32 at = blk_at(e, a, i);
  Term v = blk_read(H, arr, term_loc(a), at);
  if (arr) {
    v = term_keep(e, v);
    blk_write(H, arr, term_loc(a), at, v);
  }
  return v;
}

// Buf
// ===

INLINE Term buf_new(Env e, bool arr, Nat d, Term v) {
  Corpus H = e.mem;
  if (d > 31) {
    err_post(H, ERR_NATS);
    d = 0;
  }
  Cls c = (u32)d;
  BLK_ALLOC(n, arr ? c : buf_wcls(c))
  if (!arr) {
    for (u64 i = 0; i < (1ull << buf_wcls(c)); i += 1) {
      H[n + i] = (u64)(u32)v * 0x100000001ull;
    }
    return term_buf(c, n);
  }
  if (c > 0 && !term_triv(v)) {
    if (c >= 24) {
      err_post(H, ERR_RFCS);
    } else if (term_rfc(v)) {
      u32 k = (1u << c) - 1;
      u32 w = a32_add(a32_at(H, term_loc(v)), k);
      if ((w & RFC_CNT) >= RFC_CNT - k) {
        err_post(H, ERR_RFCS);
      }
    } else {
      v = rfc_wrap(e, v, 1u << c);
    }
  }
  for (u64 i = 0; i < (1ull << c); i += 1) {
    H[n + i] = v;
  }
  return term_blk(1, c, n);
}

// Ring
// ====

INLINE DEV u64* ring_slot(Corpus H, Ring r, u64 pos) {
  return H + RING_OFF + (pos & (RING_LEN - 1)) * CUBE + r;
}

INLINE DEV u32* ring_put(Corpus H, Ring r) {
  return (DEV u32*)monk_word(H, r, M_RING_PUT);
}

INLINE DEV u32* ring_get(Corpus H, Ring r) {
  return (DEV u32*)monk_word(H, r, M_RING_GET);
}

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

INLINE Term ring_head(Corpus H, Ring r) {
  u32 get = *ring_get(H, r);
  DEV u32* lo = (DEV u32*)ring_slot(H, r, get);
  u32 hi = a32_load_acq(lo + 1);
  if ((hi >> 31) != ring_lap(get)) {
    return 0;
  }
  return (((u64)hi << 32) | a32_load(lo)) & ~RFC_BIT;
}

INLINE void ring_skip(Corpus H, Ring r) {
  DEV u32* get = ring_get(H, r);
  a32_store(get, *get + 1);
}

INLINE Ring ring_flip(u32 i) {
  return i / CUBE_SIDE + CUBE_SIDE * (i % CUBE_SIDE);
}

#define ring_pick(b, s, c) \
  ((s) == 0 ? (b) : (b) + (s) * (CUR_STEP(c) & (CUBE_SIDE - 1)))

// Task
// ====

INLINE Loc task_node(Env e, Fid fid, Term cont, u32 idx, u32 rem) {
  u32 ar  = fid_arity(fid);
  Loc loc = heap_alloc(e, cls_fit(ar + 2));
  e.mem[loc + ar]     = cont;
  e.mem[loc + ar + 1] = ((u64)idx << 32) | rem;
  return loc;
}

INLINE Loc task_tail(Term t) {
  return term_loc(t) + fid_arity((u32)term_aux(t));
}

INLINE Term task_deliver(Corpus H, Term cont, u32 idx, Term v) {
  if (cont == TERM_HOLE) {
    H[H_ROOT_WORD] = v;
    a32_store_rel(a32_at(H, H_ROOT_DONE), 1);
    return 0;
  }
  Loc tl = task_tail(cont);
  H[term_loc(cont) + idx] = v;
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

INLINE bool task_runs(Corpus H, Reply r) {
  return (u32)H[task_tail(r) + 1] == 0;
}

// Root
// ====

INLINE bool root_done(Corpus H) {
  return a32_load_acq(a32_at(H, H_ROOT_DONE)) != 0;
}

static Term root_take(Corpus H) {
  Term v = H[H_ROOT_WORD];
  a32_store(a32_at(H, H_ROOT_DONE), 0);
  return v;
}

// Stack
// =====

#if DEVICE
#define WL_ROOM(N) \
  if (sp + (N) * CUBE > e.mem + STAK_OFF + e.mnk + CUBE * STAK_LEN) { \
    err_post(e.mem, ERR_DEEP); \
    return 0; \
  }
#else
#define WL_ROOM(N)
#endif

// Work
// ====

static Reply work_loop(Env e, Stk sp, Term t, bool seq) {
  Fid  fid;
  Term res = 0;
  WL_BANK
  {
  fid = (u32)term_aux(t);
  Loc a   = term_loc(t);
  u32 war = fid_arity(fid);
  WL_FRAME(t)
  if (fid_seqk(fid)) {
    res = e.mem[a + war - 1];
    WL_ARGS(a, war)
  } else {
    WL_LOAD
  }
  heap_free(e, cls_fit(war + 2), a);
  }
#if DEVICE
  u32 wpoll = 0;
  for (;;) {
  if (err_spun(e.mem, &wpoll, 255)) {
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
    WL_RET(term_ctr(CID_EMIT, l));
  }
#endif

#ifdef FID_CLO_APPLY
  WL_CASE(FID_CLO_APPLY)
  {
    Term fun = r0;
    res      = r1;
    fid      = (Fid)term_aux(fun);
    u32 war  = fid_arity(fid) - 1;
    Loc a    = term_loc(fun);
    u64 cnt  = 0;
    if (term_rfc(fun)) {
      u64 cell = rfc_view(e, a);
      cnt = cell & RFC_CNT;
      a   = cell >> 24;
    }
    WL_LOAD
    if (cnt > 1) {
      span_fade(e, fun, a, war);
    } else {
      if (cnt == 1) {
        heap_free(e, 0, term_loc(fun));
      }
      if (war > 0) {
        heap_free(e, cls_fit(war), a);
      }
    }
    WL_LAST
    WL_DYN(fid);
  }
#endif

  WL_CASE(FID_EXIT)
  {
    if (DEVICE && err_seen(e.mem)) {
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
      WL_ARGS(wa, wn)
      heap_free(e, cls_fit(wn + 2), wa);
      WL_DYN(wf);
    }
    return task_deliver(e.mem, cont, idx, res);
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
    if (task_runs(e.mem, r)) {
      if (err_spun(e.mem, &spin, ERR_TICK)) {
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

static void monk_work(Env e, Stk stk, Monk m) {
  Corpus H = e.mem;
#if DEVICE
  u32 put0 = a32_load(ring_put(H, m));
#else
  u32 put0 = (u32)*monk_word(H, m, M_SNAP);
#endif
  while (*ring_get(H, m) != put0) {
    if (err_seen(H)) {
      return;
    }
    Term t = ring_head(H, m);
    if (t == 0) {
      continue;
    }
    ring_skip(H, m);
    monk_run(e, stk, t, true, m, 0, (Cursor)0);
  }
}

// Dev
// ===

#if DEVICE

#ifdef __METAL_VERSION__
kernel void grow_dev(Corpus H [[buffer(0)]],
  u32 grids [[threadgroups_per_grid]],
  u32 row [[threadgroup_position_in_grid]],
  u32 lane [[thread_position_in_threadgroup]]) {
#else
extern "C" __global__ void grow_dev(Corpus H) {
  u32 grids = gridDim.x;
  u32 row   = blockIdx.x;
  u32 lane  = threadIdx.x;
#endif
  u32  stride = grids == 1 ? CUBE_SIDE : 1;
  Ring rg  = (row << 7) + stride * lane;
  GRPV u64 tg_alc[CUBE_SIDE * ALC_WORDS];
  Env  e   = { H, rg, tg_alc + lane };
  alc_open(e);
  GA32 tg_cur;
  GA32 tg_grew;
  GA32 tg_has;
  g32_ini(&tg_cur);
  g32_ini(&tg_grew);
  g32_ini(&tg_has);
  BAR();
  u32 seen_has  = 0;
  u32 seen_grew = 0;
  for (;;) {
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
    if (monk_grow(e, (Stk)(H + STAK_OFF + rg), rg, put0, row << 7, stride,
      &tg_cur) == 1) {
      g32_add(&tg_grew, 1);
    }
    BARD();
    u32 grew = g32_get(&tg_grew);
    if (grew == seen_grew) {
      break;
    }
    seen_grew = grew;
  }
  alc_close(e);
}

#ifdef __METAL_VERSION__
kernel void work_dev(Corpus H [[buffer(0)]],
  u32 tid [[thread_position_in_grid]],
  u32 lane [[thread_position_in_threadgroup]]) {
#else
extern "C" __global__ void work_dev(Corpus H) {
  u32 lane = threadIdx.x;
  u32 tid  = blockIdx.x * CUBE_SIDE + lane;
#endif
  GRPV u64 tg_alc[CUBE_SIDE * ALC_WORDS];
  Env e = { H, tid, tg_alc + lane };
  alc_open(e);
  monk_work(e, (Stk)(H + STAK_OFF + tid), ring_flip(tid));
  alc_close(e);
}

#endif

#if !DEVICE

// Row
// ===

static void row_grow(Env e, Stk stk, u32 base, u32 stride) {
  Corpus H = e.mem;
  u32 cur = 0;
  for (;;) {
    u32 put0[CUBE_SIDE];
    u32 has = 0;
    for (u32 i = 0; i < CUBE_SIDE; i += 1) {
      Ring rg = base + stride * i;
      put0[i] = *ring_put(H, rg);
      has += put0[i] != *ring_get(H, rg);
    }
    if (root_done(H) || has == CUBE_SIDE) {
      return;
    }
    u32 grew = 0;
    u32 ran  = 0;
    for (u32 i = 0; i < CUBE_SIDE && ran != 2; i += 1) {
      Ring rg = base + stride * i;
      ran     = monk_grow(e, stk, rg, put0[i], base, stride, &cur);
      grew += ran == 1;
    }
    if (grew == 0) {
      return;
    }
  }
}

// Pool
// ====

static Term* pool_stack(void) {
  u64   len = 1ull << 31;
  void* p   = mmap(NULL, len + 16384 + SIGSTKSZ, PROT_READ | PROT_WRITE,
    MAP_PRIVATE | MAP_ANON | MAP_NORESERVE, -1, 0);
  if (p == MAP_FAILED || mprotect((char*)p + len, 16384, PROT_NONE) != 0) {
    err_fail(ERR_HEAP, "machine stack reservation failed");
  }
  stack_t ss = { .ss_sp = (char*)p + len + 16384, .ss_size = SIGSTKSZ };
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
    Env e = { CORPUS, (u32)(uintptr_t)arg };
    for (;;) {
      u32 r = atomic_fetch_add_explicit(&pool_row, 1, memory_order_relaxed);
      if (r >= CUBE_SIDE) {
        break;
      }
      if (pool_grow) {
        row_grow(e, stk, r << 7, 1);
      } else {
        for (u32 c = 0; c < CUBE_SIDE; c += 1) {
          monk_work(e, stk, ring_flip((r << 7) + c));
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
#define gpu_map corpus_mmap
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

#define MEM_DFLT (2ull << 30)

static u64 gpu_span(void) {
  u64 span = [gpu_dev recommendedMaxWorkingSetSize];
  u64 most = [gpu_dev maxBufferLength];
  span = span < most ? span : most;
  return span < MEM_DFLT ? span : MEM_DFLT;
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
  if (cuLaunchKernel(pso, groups, 1, 1, CUBE_SIDE, 1, 1, 0, NULL, args, NULL)
    != CUDA_SUCCESS) {
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

#endif

#if BEND_GPU

static void gpu_round(Corpus H, u32 f) {
  gpu_pass(f);
  u32 ec = a32_load(a32_at(H, H_ERROR_CODE));
  if (ec > ERR_DEEP || (u64)a32_load(a32_at(H, H_PAGE_BUMP)) > gpu_cap) {
    ec = ERR_HEAP;
  }
  if (ec) {
    err_fail(ec, ec == ERR_DEEP ? "device stack exceeded"
      : ec == ERR_FIDS ? "a host call on the device"
      : ec == ERR_HEAP ? "out of memory: run again with a bigger span,"
        " as in --gpu-memory 8GB" : "device error");
  }
}

#else

#define gpu_probe() false
#define gpu_span()  0
#define gpu_load(b)

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
      #if BEND_GPU
      gpu_round(H, f);
      #endif
    } else {
      if (f < CUBE) {
        pool_turn(true);
      }
      for (Ring r = 0; r < CUBE; r += 1) {
        *monk_word(H, r, M_SNAP) = *ring_put(H, r);
      }
      pool_turn(false);
    }
  }
}

// Corpus
// ======

static Corpus corpus_mmap(u64 bytes) {
  Corpus H = mmap(NULL, bytes, PROT_READ | PROT_WRITE,
    MAP_PRIVATE | MAP_ANON | MAP_NORESERVE, -1, 0);
  if (H == MAP_FAILED) {
    err_fail(ERR_HEAP, "corpus reservation failed");
  }
  return H;
}

static void corpus_seed(Corpus H) {
  for (u64 i = 0; i < HUGE_CLS; i += 1) {
    H[H_HUGE_FREE + i] = PAGE_NIL;
  }
}

static Corpus corpus_setup(bool gpu, long threads, u64 bytes) {
  u64 dflt = gpu ? gpu_span() : 1ull << 43;
  u64 want = gpu ? bytes : 0;
  CORPUS_SIZE = (want != 0 ? want : dflt) & ~16383ull;
  u64 span = CORPUS_SIZE / 8;
  u64 room = span > HEAP_OFF ? (span - HEAP_OFF) >> PAGE_BITS : 0;
  u64 cap  = room < PAGE_NIL ? room : PAGE_NIL;
  if (cap == 0) {
    char text[80];
    snprintf(text, sizeof text, "--gpu-memory is under the %lluMB of lane"
      " stacks and rings", (unsigned long long)(HEAP_OFF >> 17) + 1);
    err_fail(ERR_HEAP, text);
  }
  CORPUS = gpu ? gpu_map(CORPUS_SIZE) : corpus_mmap(CORPUS_SIZE);
  Corpus H = CORPUS;
  corpus_seed(H);
  a32_store(a32_at(H, H_PAGE_CAP), (u32)cap);
#if BEND_GPU
  gpu_cap = cap;
#endif
  if (gpu) {
    gpu_load(CORPUS_SIZE);
  }
  pool_size = (u32)(threads < CUBE_SIDE ? threads : CUBE_SIDE);
  return H;
}

OUTLINE Term corpus_eval(Corpus H, Term t) {
  Env e = { H, 0 };
  for (;;) {
    Reply r = work_loop(e, io_stk, t, false);
    if (r == 0) {
      if (root_done(H)) {
        break;
      }
      err_fail(ERR_LEAK, "solo delivery lost");
    }
    if (task_runs(H, r)) {
      t = r;
      if (io_gpu && fid_bangs((u32)term_aux(t))) {
        Loc  tl   = task_tail(t);
        Term cont = H[tl];
        u32  idx  = (u32)(H[tl + 1] >> 32);
        H[tl]     = TERM_HOLE;
        H[tl + 1] = 0;
        a32_store(a32_at(H, H_CURSOR), 1);
        ring_push(H, 0, t);
        cube_run(H, true);
        Term p = task_deliver(H, cont, idx, root_take(H));
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
  return root_take(H);
}

// Requests
// ========

// Io
// ==

OUTLINE int io_loop(Corpus H, bool gpu, Fid fid) {
  Env e = { H, 0 };
  io_gpu = gpu;
  io_stk = pool_stack();
  Term op = corpus_eval(H, term_tsk(fid, task_node(e, fid, TERM_HOLE, 0, 0)));
  Term x = term_clo(FID_IO_EMIT, 0);
  for (;;) {
    Term fs[256];
    u32 c = (u32)term_aux(op);
    if (term_tag(op) == TAG_CLO) {
      if (c == FID_IO_EMIT) {
        return 0;
      }
      u32 war = fid_arity(c);
      if (war > 1) {
        spare_free(e, cls_fit(war - 1), ctr_take(e, op, war - 1, fs));
      }
      Effect run = io_eff_at(io_eff_fids, c);
      if (run != NULL) {
        op = x;
        x = run(e, fs);
        continue;
      }
      Loc a = task_node(e, c, TERM_HOLE, 0, 0);
      for (u32 i = 0; i + 1 < war; i += 1) {
        e.mem[a + i] = fs[i];
      }
      e.mem[a + war - 1] = x;
      op = corpus_eval(H, term_tsk(c, a));
      continue;
    }
    if (c == CID_EMIT) {
      return 0;
    }
    if (c == CID_HALT) {
      spare_free(e, cls_fit(2), ctr_take(e, op, 2, fs));
      int code = (int)(u32)fs[0];
      io_errs(e, fs[1]);
      return code;
    }
    Effect run = term_tag(op) == TAG_CTR ? io_eff_at(io_eff_cids, c) : NULL;
    if (run == NULL) {
      err_fail(ERR_FIDS, "an alien request");
    }
    u32 n = cid_arity(c);
    spare_free(e, cls_fit(n), ctr_take(e, op, n, fs));
    op = fs[n - 1];
    x = run(e, fs);
  }
}

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
  long thr = 0;
  int  par = -1;
  int  gpu = -1;
  u64  mem = 0;
  for (int i = 1; i < argc; i += 1) {
    const char* a = argv[i];
    const char* v = i + 1 < argc ? argv[i + 1] : NULL;
    if (strcmp(a, "--help") == 0) {
      printf(CLI_HELP, argv[0]);
      return 0;
    } else if (strcmp(a, "--threads") == 0) {
      char* end = NULL;
      thr = v != NULL ? strtol(v, &end, 10) : 0;
      if (thr < 1 || end == NULL || *end != '\0') {
        cli_fail("expected a thread count of 1 or more after --threads", NULL);
      }
      i += 1;
    } else if (strcmp(a, "--parallel") == 0) {
      par = cli_flag("--parallel", v);
      i += 1;
    } else if (strcmp(a, "--gpu") == 0) {
      gpu = cli_flag("--gpu", v);
      i += 1;
    } else if (strcmp(a, "--gpu-memory") == 0) {
      mem = cli_size(v);
      i += 1;
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
  bool dev = gpu != 0 && gpu_probe();
  if (gpu == 1 && !dev) {
    cli_fail("--gpu on, but this binary found no GPU device", NULL);
  }
  long ncpu = sysconf(_SC_NPROCESSORS_ONLN);
  long dflt = ncpu > 0 ? ncpu : 1;
  Corpus H  = corpus_setup(dev, thr > 0 ? thr : dflt, mem);
  int code  = io_loop(H, dev, FID_MAIN);
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
  for (let x = a; x.$ === "ANode"; x = x.$0) {
    n *= 2;
  }
  return n;
}

function array_size(a) {
  return {$: "Tuple", $0: a, $1: array_len(a)};
}

function array_get(a, i) {
  let n = array_len(a);
  i = (i >>> 0) % n;
  let x = a;
  while (x.$ === "ANode") {
    n /= 2;
    if (i < n) {
      x = x.$0;
    } else {
      x = x.$1;
      i -= n;
    }
  }
  return {$: "Tuple", $0: a, $1: x.$0};
}

function array_new(d, v) {
  if (d > 31n) {
    throw new Error("array_new: " + d + " is past the deepest block class 31");
  }
  let a = {$: "ALeaf", $0: v};
  for (let j = 0n; j < d; j += 1n) {
    a = {$: "ANode", $0: a, $1: a};
  }
  return a;
}

function array_swap_go(a, n, i, v) {
  if (a.$ === "ALeaf") {
    return {$: "Tuple", $0: {$: "ALeaf", $0: v}, $1: a.$0};
  }
  n /= 2;
  if (i < n) {
    const r = array_swap_go(a.$0, n, i, v);
    return {$: "Tuple", $0: {$: "ANode", $0: r.$0, $1: a.$1}, $1: r.$1};
  }
  const r = array_swap_go(a.$1, n, i - n, v);
  return {$: "Tuple", $0: {$: "ANode", $0: a.$0, $1: r.$0}, $1: r.$1};
}

function array_swap(a, i, v) {
  const n = array_len(a);
  return array_swap_go(a, n, (i >>> 0) % n, v);
}

function array_set(a, i, v) {
  return array_swap(a, i, v).$0;
}

// Cli
// ===

function cli_fail(msg) {
  require("fs").writeSync(2, "bend: " + msg + "\n");
  process.exit(1);
}

function cli_flag(name, val) {
  if (val === "on") {
    return true;
  }
  if (val !== "off") {
    cli_fail("expected 'on' or 'off' after " + name);
  }
  return false;
}

function cli_size(val) {
  const txt = val !== null ? val.replace(/^[ \t\n\v\f\r]*\+?/, "") : "";
  if (!/^(\d+\.?\d*|\.\d+)(GB|MB)$/.test(txt) || Number.parseFloat(txt) <= 0) {
    cli_fail("expected a size like 4GB or 512MB after --gpu-memory");
  }
}

function cli_help() {
  const text = [
    "usage: " + process.argv[1] + " [options]",
    "  --threads N        worker threads: a JS program runs one",
    "  --parallel on|off  off means one thread and no GPU (default: on)",
    "  --gpu on|off       send ! calls to the GPU (default: on if present)",
    "  --gpu-memory 4GB   device span: a JS program uses the JS heap",
    "  --help             show this text",
    "",
  ].join("\n");
  require("fs").writeSync(1, text);
  process.exit(0);
}

function cli(argv) {
  let thr = 0;
  let par = -1;
  let gpu = -1;
  for (let i = 0; i < argv.length; i += 1) {
    const a = argv[i];
    const v = i + 1 < argv.length ? argv[i + 1] : null;
    if (a === "--help") {
      cli_help();
    } else if (a === "--threads") {
      thr = v !== null && /^[ \t\n\v\f\r]*\+?\d+$/.test(v) ? Number(v) : 0;
      if (thr < 1) {
        cli_fail("expected a thread count of 1 or more after --threads");
      }
      i += 1;
    } else if (a === "--parallel") {
      par = cli_flag("--parallel", v) ? 1 : 0;
      i += 1;
    } else if (a === "--gpu") {
      gpu = cli_flag("--gpu", v) ? 1 : 0;
      i += 1;
    } else if (a === "--gpu-memory") {
      cli_size(v);
      i += 1;
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
}

// Run
// ===

function run_jump(f, x) {
  return {$: "$JMP", f: f, x: x};
}

function run_loop(r) {
  while (r !== null && typeof r === "object" && r.$ === "$JMP") {
    r = r.f(...r.x);
  }
  return r;
}

// Io
// ==

function io_exit(m) {
  let code;
  try {
    code = io_run(m);
  } catch (e) {
    require("fs").writeSync(2, String(e) + "\n");
    process.exit(1);
  }
  process.exit(code);
}

function io_run(m) {
  let op;
  try {
    op = run_loop(m())((x) => ({ $: "Emit", $0: x }));
    while (op.$ === "$FFI") {
      op = op.kont(op.run());
    }
  } catch (req) {
    if (req instanceof RangeError) {
      throw "bend: error 10: memory fault (machine stack overflow?)";
    }
    if (req === null || typeof req !== "object" || req.$ !== "$FFI") {
      throw req;
    }
    const msg = "bend: a request decoded outside the event loop";
    op = { $: "Halt", $0: 1, $1: msg };
  }
  if (op.$ !== "Halt") {
    return 0;
  }
  const fs = require("fs");
  const data = [];
  for (const c of op.$1) {
    data.push(c.codePointAt(0) & 255);
  }
  data.push(10);
  const buf = Uint8Array.from(data);
  let at = 0;
  while (at < buf.length) {
    try {
      at += fs.writeSync(2, buf, at, buf.length - at);
    } catch (e) {
      if (e.code === "EAGAIN" || e.code === "EINTR") {
        continue;
      }
      const line = "bend: error 1: a short write on a standard stream\n";
      try {
        fs.writeSync(2, line);
      } catch (o) {
      }
      process.exit(1);
    }
  }
  return op.$0;
}
`.slice(1);
