// Bend JS Runtime
// ================
//
// The static half of every compiled Bend program. tojs.ts appends the
// compiled defs (and the main call) after this text; nothing here changes
// from compilation to compilation.
//
// Value representation (one type = one format):
//
//   Nat          BigInt (unbounded)
//   Bool         boolean
//   U32          number (unsigned, via >>> 0)
//   Char         string (one codepoint)
//   String       string
//   Word(n)      structural ctor objects (the honest spec view)
//   other ADTs   {$: "Ctor", $0: f0, $1: f1, ...} (erased fields absent)
//   closures     curried JS functions
//   erased data  null (types, proofs, {==})
//
// Every function here must equal its structural base.bend def bit for
// bit: the def is the spec, this file is the machine. One documented
// deviation: Char codes must be Unicode scalar values (char_new
// fail-stops on lone surrogates and codes past 0x10FFFF, which JS
// strings cannot represent).
//
// Naming is a contract: a function named <type>_<op> IS the intrinsic
// of the base def Type.op — the compiler wires any def whose
// lowercased name ('.' → '_') appears here straight to it, emitting no
// body. A helper that implements no def must therefore use a name no
// def has (cmp_new, u32_to_word, value_show, ...).

// Bool
// ====

function bool_not(a) {
  return !a;
}

function bool_and(a, b) {
  return a && b;
}

function bool_or(a, b) {
  return a || b;
}

function bool_xor(a, b) {
  return a !== b;
}

function bool_if(b, t, f) {
  return b ? t : f;
}

// Cmp
// ===

function cmp_new(a, b) {
  return a < b ? {$: "LT"} : a === b ? {$: "EQ"} : {$: "GT"};
}

function cmp_is_lt(c) {
  return c.$ === "LT";
}

function cmp_is_eq(c) {
  return c.$ === "EQ";
}

function cmp_is_gt(c) {
  return c.$ === "GT";
}

function cmp_is_le(c) {
  return c.$ !== "GT";
}

function cmp_is_ge(c) {
  return c.$ !== "LT";
}

// Nat
// ===

function nat_copy(n) {
  return {$: "Tuple", $0: {$: "Tuple", $0: n, $1: null}, $1: {$: "Tuple", $0: n, $1: null}};
}

function nat_is_zero(n) {
  return n === 0n;
}

function nat_pred(n) {
  return n === 0n ? 0n : n - 1n;
}

function nat_double(n) {
  return n << 1n;
}

function nat_add(a, b) {
  return a + b;
}

function nat_sub(a, b) {
  return a < b ? 0n : a - b;
}

function nat_mul(a, b) {
  return a * b;
}

function nat_divmod(a, b) {
  return b === 0n ? {$: "Tuple", $0: 0n, $1: a} : {$: "Tuple", $0: a / b, $1: a % b};
}

function nat_div(a, b) {
  return b === 0n ? 0n : a / b;
}

function nat_mod(a, b) {
  return b === 0n ? a : a % b;
}

function nat_min(a, b) {
  return a < b ? a : b;
}

function nat_max(a, b) {
  return a < b ? b : a;
}

function nat_cmp(a, b) {
  return cmp_new(a, b);
}

function nat_is_eq(a, b) {
  return a === b;
}

function nat_is_ne(a, b) {
  return a !== b;
}

function nat_is_lt(a, b) {
  return a < b;
}

function nat_is_le(a, b) {
  return a <= b;
}

function nat_is_gt(a, b) {
  return a > b;
}

function nat_is_ge(a, b) {
  return a >= b;
}

function nat_pow2(n) {
  return 1n << n;
}

function nat_bits(m) {
  return {$: "Tuple", $0: (m & 1n) === 1n, $1: m >> 1n};
}

// Word
// ====
//
// Structural words surface only when a native U32 is introduced or
// eliminated through its wrapper constructor; ops never build them.

function u32_to_word(x) {
  let w = {$: "WNil"};
  for (let i = 31; i >= 0; i--) {
    w = {$: "WCon", $0: ((x >>> i) & 1) === 1, $1: w};
  }
  return w;
}

function word_to_u32(w) {
  let x = 0;
  for (let i = 0; w.$ === "WCon"; i++) {
    x |= (w.$0 ? 1 : 0) << i;
    w = w.$1;
  }
  return x >>> 0;
}

// U32
// ===

function u32_zero() {
  return 0;
}

function u32_one() {
  return 1;
}

function u32_copy(a) {
  return {$: "Tuple", $0: {$: "Tuple", $0: a, $1: null}, $1: {$: "Tuple", $0: a, $1: null}};
}

function u32_inc(a) {
  return (a + 1) >>> 0;
}

function u32_add(a, b) {
  return (a + b) >>> 0;
}

function u32_sub(a, b) {
  return (a - b) >>> 0;
}

function u32_mul(a, b) {
  return Math.imul(a, b) >>> 0;
}

function u32_div(a, b) {
  return b === 0 ? 0 : (a / b) >>> 0;
}

function u32_mod(a, b) {
  return b === 0 ? 0 : a % b;
}

function u32_not(a) {
  return (~a) >>> 0;
}

function u32_and(a, b) {
  return (a & b) >>> 0;
}

function u32_or(a, b) {
  return (a | b) >>> 0;
}

function u32_xor(a, b) {
  return (a ^ b) >>> 0;
}

function u32_shl(a) {
  return (a << 1) >>> 0;
}

function u32_shr(a) {
  return a >>> 1;
}

function u32_shln(n, a) {
  return n >= 32n ? 0 : (a << Number(n)) >>> 0;
}

function u32_shrn(n, a) {
  return n >= 32n ? 0 : a >>> Number(n);
}

function u32_cmp(a, b) {
  return cmp_new(a, b);
}

function u32_is_eq(a, b) {
  return a === b;
}

function u32_is_ne(a, b) {
  return a !== b;
}

function u32_is_lt(a, b) {
  return a < b;
}

function u32_is_le(a, b) {
  return a <= b;
}

function u32_is_gt(a, b) {
  return a > b;
}

function u32_is_ge(a, b) {
  return a >= b;
}

function u32_is_zero(a) {
  return a === 0;
}

function u32_to_nat(a) {
  return BigInt(a);
}

function u32_from_nat(n) {
  return Number(n & 0xFFFFFFFFn);
}

// Char
// ====

// A Char must be a Unicode scalar value: JS strings cannot carry lone
// surrogates or codes past 0x10FFFF without merging or throwing, so the
// JS backend fail-stops loudly on them (a documented deviation from the
// structural spec, which admits any U32 code).
function char_new(code) {
  if (code > 0x10FFFF || (code >= 0xD800 && code <= 0xDFFF)) {
    throw new Error("char_new: " + code + " is not a Unicode scalar value");
  }
  return String.fromCodePoint(code);
}

function char_code(c) {
  return c.codePointAt(0);
}

// String
// ======

function string_head(s) {
  return s.codePointAt(0) > 0xFFFF ? s.slice(0, 2) : s[0];
}

function string_tail(s) {
  return s.codePointAt(0) > 0xFFFF ? s.slice(2) : s.slice(1);
}

function string_append(a, b) {
  return a + b;
}

// Array
// =====

function array_swap(a, i, v) {
  if (a.$ === "ALeaf") {
    return {$: "Tuple", $0: {$: "ALeaf", $0: v}, $1: a.$0};
  }
  const r = (i & 1) === 0 ? array_swap(a.$0, i >>> 1, v) : array_swap(a.$1, i >>> 1, v);
  const b = (i & 1) === 0 ? {$: "ANode", $0: r.$0, $1: a.$1} : {$: "ANode", $0: a.$0, $1: r.$0};
  return {$: "Tuple", $0: b, $1: r.$1};
}

// F32
// ===
//
// IEEE-754 binary32 (the F32 axioms of Base): every op rounds through
// Math.fround; F32 -> U32 truncates, out-of-range inputs answer 0.

function u32_to_f32(a) {
  return Math.fround(a);
}

function f32_to_u32(a) {
  return a >= 1 && a < 4294967296 ? Math.floor(a) : 0;
}

function f32_add(a, b) {
  return Math.fround(a + b);
}

function f32_sub(a, b) {
  return Math.fround(a - b);
}

function f32_mul(a, b) {
  return Math.fround(a * b);
}

function f32_div(a, b) {
  return Math.fround(a / b);
}

function f32_sqrt(a) {
  return Math.fround(Math.sqrt(a));
}

function f32_is_eq(a, b) {
  return a === b;
}

function f32_is_ne(a, b) {
  return a !== b;
}

function f32_is_lt(a, b) {
  return a < b;
}

function f32_is_le(a, b) {
  return a <= b;
}

function f32_is_gt(a, b) {
  return a > b;
}

function f32_is_ge(a, b) {
  return a >= b;
}

// Show
// ====

function value_show(x) {
  if (typeof x === "bigint") {
    return x.toString() + "n";
  }
  if (typeof x === "number") {
    return x.toString();
  }
  if (typeof x === "boolean") {
    return x ? "True{}" : "False{}";
  }
  if (typeof x === "string") {
    return JSON.stringify(x);
  }
  if (x === null) {
    return "-";
  }
  if (typeof x === "function") {
    return "<closure>";
  }
  if (Array.isArray(x)) {
    return "[" + x.map(value_show).join(", ") + "]";
  }
  let out = x.$ + "{";
  for (let i = 0; ("$" + i) in x; i++) {
    out += (i === 0 ? "" : ", ") + value_show(x["$" + i]);
  }
  return out + "}";
}
