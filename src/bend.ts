// Bend
// ====
// 
// SYNTAX
// ------
//
// Quant ::=
//   | "-"
//   | ""
//   | "+"
//
// Bind ::=
//   | Quant Name ":" Term
//
// Term ::=
//   | Var ::= Name
//   | Ref ::= Name
//   | Let ::= Quant Name "=" Term ";"? Term
//   | Ann ::= "{" Term ":" Term "}"
//   | Typ ::= "Type"
//   | All ::= "@" Bind "->" Term
//   | Lam ::= Name "=>" Term
//   | App ::= Term "(" [Term ","?] ")"
//   | ADT ::= Name "<" [Term ","?] ">"
//   | Ctr ::= Name "{" [Term ","?] "}"
//   | Mat ::= "\" "{" Name ":" Term ";"? Term "}"
//   | Efq ::= "\" "{" "}"
//   | Eql ::= "{" Term "==" Term ":" Term "}"
//   | Rfl ::= "{" "==" "}"
//   | Rwt ::= "%" (Name "@")? Term ":" Term ";"? Term
//   | Cop ::= "+" Term ("~" Term)?
//   | Grp ::= "(" Term ")"
//
// Case   ::= "case" [Term] ":" Body
// Cell   ::= Term | Name ":" Term "=" Term
// Match  ::= "match" [Cell] ":" [Case] ("return" Term)?
// Local  ::= Term "=" Term ";"? Body
// Reply  ::= Term
// Body   ::= Match | Local | Reply
// Ctr    ::= Name "{" [Bind ","?] "}"
// ADT    ::= "type" Name ("<" [Bind ","?] ">")? ":" [Ctr]
// Clause ::= ("forall" Quant | "exists") Name ":" Term ("where" Term)?
// Assert ::= "assert" Name ":" [Clause] Term
// Def    ::= "def" Name "(" [Name ","?] ")" ":" (Body | ["import" STRING]+)
// TLD    ::= ADT | Assert | Def
// Import ::= "import" "Base" | "import" Path "as" Name
// Book   ::= [Import] [TLD]
//
// SUGARS
// ------
// 
// Name    | Grammar               | Term
// ------- | --------------------- | ----
// Arrow   | A "->" B              | @_:A -> B
// Exists  | "&" Name ":" A "->" B | Sigma<A, x => B>
// Pair    | A "&" B               | Pair(A, B)
// Either  | A "|" B               | Either<A, B>
// Tuple   | "(" A ("," B)+ ")"    | Tuple{A, Tuple{B, ...}}
// LitZero | "0n"                  | Zero{}
// LitSucc | NUMBER "n+" Term      | Succ{...Succ{pred}}
// LitNat  | NUMBER "n"            | Succ{Succ{...Zero{}}}
// LitU32  | NUMBER                | U32{bits}
// LitChr  | "'" CHAR "'"          | Chr{U32{bits}}
// LitStr  | "\"" [CHAR] "\""      | SCon{x, SCon{y,...SNil{}}}
// CopWit  | "+" T                 | + T ~ T.copy, structurally
//
// a literal expands to one node per unit, unbounded by design. Arrow is
// right-associative; the domain of a written @ or & binder stops at the
// first bare "->", so an arrow (or a nested binder) there needs parens.
// infix "&" and "|" are right-associative, share one precedence, and
// bind tighter than "->". a rewrite "%e@E : P; f" binds e and "_" inside
// its motive P; "%E : P; f" is the nameless form: the equation binder is
// spelled "" and cannot be referenced.
//
// Do-Notation
// -----------
//
// DoBlock ::=
//   | "do" Name "<" [Term ","?] ">" ":" [DoStmt]
//
// DoStmt ::=
//   | DoLet  ::= Name ":" Term "=" Term ";"? DoStmt
//   | DoExec ::= Term "<-" Term ";"? DoStmt
//   | DoBind ::= Name ":" Term "<-" Term ";"? DoStmt
//   | DoPure ::= "return" Term
//   | DoRetr ::= Term
//
// Example:
//   do Result<E, R>:
//     x : A <- foo
//     return g(y)
// Becomes:
//   Result.bind(E, A, R, foo, x =>
//   Result.pure(E, R, g(y)))
//
// An empty list (do M<>:) drops the result type: pure/bind lose R.
// 
// THEORY
// ------
//
// Bend is a dependent affine calculus: two checking modes (dead and
// live) and a well-founded descent judgment on live recursion. a live
// variable is consumed at most once unless a Cop licenses it, every
// live self-call descends, and no dead inhabitant is promoted to live
// evidence. this wall permits Type : Type, impredicativity and negative
// recursive types with no universe hierarchy and no positivity check.
// quantities None | Lone | Many (-x, x, +x) add sequentially (two live
// uses saturate to Many) and join pointwise-max across branches; Many
// needs a Cop type + T ~ C, well-formed iff C : Copiable(T), unless the
// book is #[halts]; Sigma, Copy and Copiable are locked in book_valid.
// a type position, an erased (-) argument, an equality endpoint or a
// motive checks dead: it may diverge and inhabit Empty; no rule coerces
// dead to live. datatype fields never carry a license, a -field is
// absent from storage and dead, and a pattern binder takes its quantity
// from the elimination site. the checker is authoritative about cost: a
// compiler may drop a cost the source spelled, never add a clone or
// retain the source did not. equality is intensional; elimination is
// the J axiom, %e@E : P; f, and a stuck rewrite fires only when its
// evidence reaches {==}. conversion is up to eta. every live self-call
// descends on a strict subterm in its own case tree, live columns
// compared EQ left to right, erased columns skipped. trusted claims:
// subject reduction, progress, weak normalization of closed live
// terms, no closed live inhabitant of Empty.

declare global {
  interface ImportMeta {
    main: boolean;
    require(id: string): unknown;
  }
}

declare const process: {
  argv: string[];
  exit(code?: number): never;
};

const fs = import.meta.require("fs") as {
  readFileSync(path: string | URL, enc: "utf8"): string;
  writeFileSync(path: string, data: string): void;
  realpathSync(path: string): string;
};

const { readFileSync, realpathSync } = fs;

const { fileURLToPath } = import.meta.require("url") as {
  fileURLToPath(url: URL): string;
};

// Core
// ====

// Types
// =====

export type Bool = boolean;
export type U32  = number;
export type Name = string;

export type Cmp =
  | "LT"
  | "EQ"
  | "GT";

// PMap
export type PMap<Item> =
  | { $: "Emp" }
  | { $: "Bin"; v: Item | null; l: PMap<Item>; r: PMap<Item> };

// Quant
export type Quant =
  | { $: "None" }
  | { $: "Lone" }
  | { $: "Many" };

// Uses
export type Uses = PMap<Quant>;

// Term
export type BodyOf<B> = B extends [infer T] ? T : B;
export type TermOf<B> = (
  | { $: "Var"; k: Name; i: number; v?: TermOf<B> }                        // x
  | { $: "Ref"; k: Name; b?: Bool }                                        // x
  | { $: "Sub"; i: number; v: TermOf<B>; f: TermOf<B> }                    // x <- v; f
  | { $: "Let"; k: Name; i: number; q: Quant; v: TermOf<B>; f: BodyOf<B> } // x = v; f
  | { $: "Typ" }                                                           // Type
  | { $: "All"; q: Quant; k: Name; i: number; A: TermOf<B>; B: BodyOf<B> } // @x:A -> B
  | { $: "Lam"; k: Name; i: number; f: BodyOf<B> }                         // x => f
  | { $: "App"; f: TermOf<B>; x: TermOf<B> }                               // f(x)
  | { $: "ADT"; k: Name; x: TermOf<B>[]; r: Name[] }                       // A<x0,x1,...>
  | { $: "Ctr"; k: Name; x: TermOf<B>[] }                                  // A{x0,x1,...}
  | { $: "Mat"; k: Name; h: TermOf<B>; m: TermOf<B> }                      // \{A: h; m}
  | { $: "Efq" }                                                           // \{}
  | { $: "Eql"; a: TermOf<B>; b: TermOf<B>; T: TermOf<B> }                 // {a == b : T}
  | { $: "Rfl" }                                                           // {==}
  | { $: "Rwt"; e: TermOf<B>; p: TermOf<B>; f: TermOf<B> }                 // %e@E : P; f (p = _ => e => P)
  | { $: "Cop"; T: TermOf<B>; c: TermOf<B> }                               // + T ~ c
  | { $: "Ann"; x: TermOf<B>; T: TermOf<B> }                               // {x : T}
  | { $: "Laz"; f: () => TermOf<B>; x?: TermOf<B> }                        // x
) & { s?: Span };

export type LTerm = TermOf<[LTerm]>;
export type HBody = (x: HTerm) => HTerm;
export type HTerm = TermOf<HBody>;

// Env
export type Env = PMap<HTerm>;

// Definitions & Book
export type Ctr  = { k: Name; n: number; T: HTerm }
export type Ctrs = Array<Ctr>;
export type ADT  = { $: "ADT"; n: number; T: HTerm; c: Ctrs; };
export type Def  = { $: "Def"; n: number; T: HTerm; v: HTerm | null; e?: HTerm; b?: Bool; i?: string[]; };
export type TLD  = ADT | Def;
export type Book = { tlds: Record<Name, TLD>; ctrs: Record<Name, Ctr>; order: Name[]; halts: boolean; };

// Context
export type Ann = { q: Quant; k: Name; T: HTerm };
export type Ctx = PMap<Ann>;

// Body
export type PVar  = { $: "PVar"; k: Name; i: number; s?: Span };
export type PCtr  = { $: "PCtr"; k: Name; x: Patt[]; s?: Span };
export type Patt  = PVar | PCtr;
export type Case  = { $: "Case"; p: Patt[]; f: Body };
export type Rows  = Array<Case>;
export type Cell  = { $: "Cell"; k: Name; i: number; A: LTerm | null; v: LTerm; s?: Span };
export type Match = { $: "Match"; e: Cell[]; P: LTerm | null; r: Rows; s?: Span };
export type Local = { $: "Local"; k: Patt; q: Quant; v: LTerm; f: Body };
export type Reply = { $: "Reply"; x: LTerm; s?: Span };
export type Body  = Match | Local | Reply

// Parser
export type Loc   = { pos: number; lin: number; col: number; };
export type Parse = { str: string; loc: Loc; env: Name[]; ids: Record<Name, number[]>; frs: number; book: Book; ns: string; gtd: number; bs: Bool; dir: string; };
export type Span  = { src: string; beg: Loc; end: Loc; };

// Machine
export type LHS   = { t: HTerm; n: number; def: Name; qs: Quant[] };
export type Frame =
  | { $: "APP"; x: HTerm }                                                   // _(x)
  | { $: "MAT"; t: Extract<HTerm, { $: "Mat" }>; e: HTerm; lhs: LHS | null } // \{c:h;m}(_)
  | { $: "LAZ"; l: Extract<HTerm, { $: "Laz" }> }                            // a thunk being filled

// Error
export type Expr = HTerm | string;
export type Err  = { $: "Err"; bok: Book; exp: Expr; obs?: Expr; ctx: Ctx; def?: Name; spn?: Span; };

// Constructors
// ============

// Term
// ----

export function Var<X>(k: Name, i: number, s?: Span, v?: TermOf<X>): TermOf<X> {
  return { $: "Var", k, i, s, v };
}

export function Ref<X>(k: Name, s?: Span, b?: Bool): TermOf<X> {
  return { $: "Ref", k, s, b };
}

export function Sub<X>(i: number, v: TermOf<X>, f: TermOf<X>, s?: Span): TermOf<X> {
  return { $: "Sub", i, v, f, s };
}

export function Let<X>(k: Name, i: number, v: NoInfer<TermOf<[X]>>, f: X, s?: Span, q?: Quant): TermOf<[X]> {
  return { $: "Let", k, i, q: q ?? Lone(), v, f, s };
}

export function Typ<X>(s?: Span): TermOf<X> {
  return { $: "Typ", s };
}

export function All<X>(q: Quant, k: Name, i: number, A: NoInfer<TermOf<[X]>>, B: X, s?: Span): TermOf<[X]> {
  return { $: "All", q, k, i, A, B, s };
}

export function Lam<X>(k: Name, i: number, f: X, s?: Span): TermOf<[X]> {
  return { $: "Lam", k, i, f, s };
}

export function App<X>(f: TermOf<X>, x: TermOf<X>, s?: Span): TermOf<X> {
  return { $: "App", f, x, s };
}

export function ADT<X>(k: Name, x: TermOf<X>[], s?: Span, r: Name[] = []): TermOf<X> {
  return { $: "ADT", k, x, r, s };
}

export function Ctr<X>(k: Name, x: TermOf<X>[], s?: Span): TermOf<X> {
  return { $: "Ctr", k, x, s };
}

export function Mat<X>(k: Name, h: TermOf<X>, m: TermOf<X>, s?: Span): TermOf<X> {
  return { $: "Mat", k, h, m, s };
}

export function Efq<X>(s?: Span): TermOf<X> {
  return { $: "Efq", s };
}

export function Eql<X>(a: TermOf<X>, b: TermOf<X>, T: TermOf<X>, s?: Span): TermOf<X> {
  return { $: "Eql", a, b, T, s };
}

export function Rfl<X>(s?: Span): TermOf<X> {
  return { $: "Rfl", s };
}

export function Rwt<X>(e: TermOf<X>, p: TermOf<X>, f: TermOf<X>, s?: Span): TermOf<X> {
  return { $: "Rwt", e, p, f, s };
}

export function Cop<X>(T: TermOf<X>, c: TermOf<X>, s?: Span): TermOf<X> {
  return { $: "Cop", T, c, s };
}

export function Ann<X>(x: TermOf<X>, T: TermOf<X>, s?: Span): TermOf<X> {
  return { $: "Ann", x, T, s };
}

export function Laz<X>(f: () => TermOf<X>, s?: Span, x?: TermOf<X>): TermOf<X> {
  return { $: "Laz", f, x, s };
}

// PMap
// ----

export function Emp<T>(): PMap<T> {
  return { $: "Emp" };
}

export function Bin<T>(v: T | null, l: PMap<T>, r: PMap<T>): PMap<T> {
  return { $: "Bin", v, l, r };
}

// Quant
// -----

export function None(): Quant {
  return { $: "None" };
}

export function Lone(): Quant {
  return { $: "Lone" };
}

export function Many(): Quant {
  return { $: "Many" };
}

// Err
// ---

export function Err(bok: Book, ctx: Ctx, exp: Expr, obs?: Expr, spn?: Span, def?: Name): Err {
  return { $: "Err", bok, ctx, exp, obs, spn, def };
}

// Char
// ====

export function char_is_head(c: string): boolean {
  return /[A-Za-z_]/.test(c);
}

export function char_is_name(c: string): boolean {
  return /[A-Za-z0-9_.]/.test(c);
}

// PMap
// ====

export function pmap_get<T>(map: PMap<T>, key: U32): T | null {
  let m = map;
  let k = key;
  while (true) {
    switch (m.$) {
      case "Emp": {
        return null;
      }
      case "Bin": {
        if (k === 0) {
          return m.v;
        }
        const odd = k % 2 === 1;
        m = odd ? m.l : m.r;
        k = odd ? (k - 1) / 2 : (k - 2) / 2;
        break;
      }
    }
  }
}

export function pmap_set<T>(map: PMap<T>, key: U32, val: T): PMap<T> {
  switch (map.$) {
    case "Emp": {
      const bin = Bin<T>(null, map, map);
      const out = pmap_set(bin, key, val);
      return out;
    }
    case "Bin": {
      if (key === 0) {
        return Bin(val, map.l, map.r);
      }
      if (key % 2 === 1) {
        const l = pmap_set(map.l, (key - 1) / 2, val);
        return Bin(map.v, l, map.r);
      }
      const r = pmap_set(map.r, (key - 2) / 2, val);
      return Bin(map.v, map.l, r);
    }
  }
}

export function pmap_union<T>(a: PMap<T>, b: PMap<T>, f: (x: T, y: T) => T): PMap<T> {
  switch (a.$) {
    case "Emp": {
      return b;
    }
    case "Bin": {
      switch (b.$) {
        case "Emp": {
          return a;
        }
        case "Bin": {
          const v = a.v === null ? b.v : b.v === null ? a.v : f(a.v, b.v);
          const l = pmap_union(a.l, b.l, f);
          const r = pmap_union(a.r, b.r, f);
          return Bin(v, l, r);
        }
      }
    }
  }
}

export function pmap_map<A, B>(map: PMap<A>, f: (x: A) => B): PMap<B> {
  switch (map.$) {
    case "Emp": {
      return Emp<B>();
    }
    case "Bin": {
      const v = map.v === null ? null : f(map.v);
      const l = pmap_map(map.l, f);
      const r = pmap_map(map.r, f);
      return Bin(v, l, r);
    }
  }
}

export function pmap_to_array<T>(map: PMap<T>, acc: U32 = 0, scl: U32 = 1): Array<[U32, T]> {
  switch (map.$) {
    case "Emp": {
      return [];
    }
    case "Bin": {
      const v: Array<[U32, T]> = map.v === null ? [] : [[acc, map.v]];
      const l = pmap_to_array(map.l, acc + scl * 1, scl * 2);
      const r = pmap_to_array(map.r, acc + scl * 2, scl * 2);
      return v.concat(l, r);
    }
  }
}

// Quant
// =====

export function quant_add(a: Quant, b: Quant): Quant {
  switch (a.$) {
    case "None": {
      return b;
    }
    default: {
      switch (b.$) {
        case "None": {
          return a;
        }
        default: {
          return Many();
        }
      }
    }
  }
}

export function quant_join(a: Quant, b: Quant): Quant {
  switch (a.$) {
    case "None": {
      return b;
    }
    case "Lone": {
      switch (b.$) {
        case "Many": {
          return Many();
        }
        default: {
          return Lone();
        }
      }
    }
    case "Many": {
      return Many();
    }
  }
}

export function quant_dem(q: Quant, qt: Quant): Quant {
  if (q.$ === "None") {
    return None();
  } else {
    return qt;
  }
}

export function quant_valid(book: Book, q: Quant, A: HTerm): boolean {
  return q.$ !== "Many" || book.halts || term_wnf(book, A).$ === "Cop";
}

// Uses
// ====

export function uses_nil(): Uses {
  return Emp<Quant>();
}

export function uses_one(k: U32, q: Quant): Uses {
  return pmap_set(uses_nil(), k, q);
}

export function uses_get(u: Uses, k: U32): Quant {
  return pmap_get(u, k) ?? None();
}

export function uses_add(a: Uses, b: Uses): Uses {
  return pmap_union(a, b, quant_add);
}

export function uses_join(a: Uses, b: Uses): Uses {
  return pmap_union(a, b, quant_join);
}

export function uses_del(u: Uses, k: U32): Uses {
  return pmap_set(u, k, None());
}

// LHS
// ===

export function lhs_ext(lhs: HTerm, k: Name, n: number, xs: HTerm[] = []): HTerm {
  if (n === 0) {
    return term_apply(lhs, Ctr(k, xs));
  } else {
    return Lam("_", 0, (x: HTerm) => {
      return lhs_ext(lhs, k, n - 1, xs.concat([x]));
    });
  }
}

// Term
// ====

export function term_apply(fn: HTerm, tm: HTerm): HTerm {
  let f = fn;
  while (true) {
    switch (f.$) {
      case "Ann": {
        f = f.x;
        break;
      }
      case "Laz": {
        f = term_force(f);
        break;
      }
      case "Lam": {
        return f.f(tm);
      }
      default: {
        return App(f, tm);
      }
    }
  }
}

export function term_unapply(tm: HTerm): [HTerm, HTerm[]] {
  const xs: HTerm[] = [];
  let cur = tm;
  while (true) {
    switch (cur.$) {
      case "Laz": {
        cur = term_force(cur);
        break;
      }
      case "App": {
        xs.push(cur.x);
        cur = cur.f;
        break;
      }
      default: {
        xs.reverse();
        return [cur, xs];
      }
    }
  }
}

export function term_force<X>(t: TermOf<X>): TermOf<X> {
  let out: TermOf<X> | null = null;
  let x = t;
  while (true) {
    switch (x.$) {
      case "Laz": {
        const l = x;
        const v = l.f();
        l.f = () => out ?? v;
        l.x = undefined;
        x = v;
        break;
      }
      default: {
        out = x;
        return x;
      }
    }
  }
}

export function term_strip<X>(tm: TermOf<X>): TermOf<X> {
  let t = term_force(tm);
  while (t.$ === "Ann") {
    t = term_force(t.x);
  }
  return t;
}

export function term_higher(tm: LTerm, env: Env): HTerm {
  switch (tm.$) {
    case "Var": {
      const v = pmap_get(env, tm.i);
      if (v === null) {
        return Ref(tm.k, tm.s);
      } else {
        return v;
      }
    }
    case "Ref": {
      return Ref(tm.k, tm.s, tm.b);
    }
    case "Sub": {
      const v = term_higher(tm.v, env);
      const f = term_higher(tm.f, pmap_set(env, tm.i, v));
      return f;
    }
    case "Let": {
      const b = tm;
      const v = term_higher(b.v, env);
      return Let(b.k, b.i, v, (x: HTerm) => {
        return term_higher(b.f, pmap_set(env, b.i, x));
      }, b.s, b.q);
    }
    case "Typ": {
      return Typ(tm.s);
    }
    case "All": {
      const b = tm;
      const A = term_higher(b.A, env);
      return All(b.q, b.k, b.i, A, (x: HTerm) => {
        return term_higher(b.B, pmap_set(env, b.i, x));
      }, b.s);
    }
    case "Lam": {
      const b = tm;
      return Lam(b.k, b.i, (x: HTerm) => {
        return term_higher(b.f, pmap_set(env, b.i, x));
      }, b.s);
    }
    case "App": {
      const f = term_higher(tm.f, env);
      const x = term_higher(tm.x, env);
      return App(f, x, tm.s);
    }
    case "ADT": {
      const xs = tm.x.map((x) => term_higher(x, env));
      return ADT(tm.k, xs, tm.s, tm.r);
    }
    case "Ctr": {
      const xs = tm.x.map((x) => term_higher(x, env));
      return Ctr(tm.k, xs, tm.s);
    }
    case "Mat": {
      const h = term_higher(tm.h, env);
      const m = term_higher(tm.m, env);
      return Mat(tm.k, h, m, tm.s);
    }
    case "Efq": {
      return Efq(tm.s);
    }
    case "Eql": {
      const a = term_higher(tm.a, env);
      const b = term_higher(tm.b, env);
      const T = term_higher(tm.T, env);
      return Eql(a, b, T, tm.s);
    }
    case "Rfl": {
      return Rfl(tm.s);
    }
    case "Rwt": {
      const e = term_higher(tm.e, env);
      const p = term_higher(tm.p, env);
      const f = term_higher(tm.f, env);
      return Rwt(e, p, f, tm.s);
    }
    case "Cop": {
      const T = term_higher(tm.T, env);
      const c = term_higher(tm.c, env);
      return Cop(T, c, tm.s);
    }
    case "Ann": {
      const x = term_higher(tm.x, env);
      const T = term_higher(tm.T, env);
      return Ann(x, T, tm.s);
    }
    case "Laz": {
      const t = term_higher(term_force(tm), env);
      return t;
    }
  }
}

// loop_run drives a generator whose recursive calls are yielded as
// requests, on an explicit stack of generator frames: a result deeper
// than the host stack still normalizes, lowers and prints. The print
// path (snf, lower, show) runs on it; a fresh generator's first next
// ignores its argument, so one resume call serves both entry and return.

export function loop_run<Q, R>(go: (q: Q) => Generator<Q, R, R>, q: Q): R {
  const stk = [go(q)];
  let val = undefined as R;
  while (true) {
    const r = stk[stk.length - 1].next(val);
    if (r.done) {
      stk.pop();
      val = r.value;
      if (stk.length === 0) {
        return val;
      }
    } else {
      stk.push(go(r.value));
    }
  }
}

export function term_lower(term: HTerm, dep: number = 0): LTerm {
  type Q = [HTerm, number];
  function* go([t0, d]: Q): Generator<Q, LTerm, LTerm> {
    let tm = t0;
    while (tm.$ === "Laz") {
      tm = term_force(tm);
    }
    switch (tm.$) {
      case "Var": {
        return Var(tm.k, tm.i, tm.s);
      }
      case "Ref": {
        return Ref(tm.k, tm.s, tm.b);
      }
      case "Sub": {
        return Sub(tm.i, yield [tm.v, d], yield [tm.f, d], tm.s);
      }
      case "Let": {
        const x: HTerm = Var(tm.k, d, undefined, tm.v);
        return Let(tm.k, d, yield [tm.v, d], yield [tm.f(x), d + 1], tm.s, tm.q);
      }
      case "Typ": {
        return Typ(tm.s);
      }
      case "All": {
        const x: HTerm = Var(tm.k, d);
        return All(tm.q, tm.k, d, yield [tm.A, d], yield [tm.B(x), d + 1], tm.s);
      }
      case "Lam": {
        const x: HTerm = Var(tm.k, d);
        return Lam(tm.k, d, yield [tm.f(x), d + 1], tm.s);
      }
      case "App": {
        return App(yield [tm.f, d], yield [tm.x, d], tm.s);
      }
      case "ADT": {
        const xs: LTerm[] = [];
        for (const x of tm.x) {
          xs.push(yield [x, d]);
        }
        return ADT(tm.k, xs, tm.s, tm.r);
      }
      case "Ctr": {
        const xs: LTerm[] = [];
        for (const x of tm.x) {
          xs.push(yield [x, d]);
        }
        return Ctr(tm.k, xs, tm.s);
      }
      case "Mat": {
        return Mat(tm.k, yield [tm.h, d], yield [tm.m, d], tm.s);
      }
      case "Efq": {
        return Efq(tm.s);
      }
      case "Eql": {
        return Eql(yield [tm.a, d], yield [tm.b, d], yield [tm.T, d], tm.s);
      }
      case "Rfl": {
        return Rfl(tm.s);
      }
      case "Rwt": {
        return Rwt(yield [tm.e, d], yield [tm.p, d], yield [tm.f, d], tm.s);
      }
      case "Cop": {
        return Cop(yield [tm.T, d], yield [tm.c, d], tm.s);
      }
      case "Ann": {
        return Ann(yield [tm.x, d], yield [tm.T, d], tm.s);
      }
    }
  }
  return loop_run(go, [term, dep]);
}

export function term_compare(arg: HTerm, col: HTerm): Cmp {
  let a = term_strip(arg);
  while (a.$ === "Var" && a.v !== undefined) {
    a = term_strip(a.v);
  }
  const p = term_strip(col);
  switch (p.$) {
    case "Var": {
      if (a.$ === "Var" && a.i === p.i) {
        return "EQ";
      } else {
        return "GT";
      }
    }
    case "Ctr": {
      if (a.$ === "Ctr" && a.k === p.k && a.x.length === p.x.length) {
        let ord: Cmp = "EQ";
        for (let j = 0; j < a.x.length && ord !== "GT"; j++) {
          const fld = term_compare(a.x[j], p.x[j]);
          ord = fld === "EQ" ? ord : fld;
        }
        if (ord !== "GT") {
          return ord;
        }
      }
      for (const q of p.x) {
        const sub = term_compare(a, q);
        if (sub !== "GT") {
          return "LT";
        }
      }
      return "GT";
    }
    default: {
      return "GT";
    }
  }
}

// Ctx
// ===

export function ctx_nil(): Ctx {
  return Emp<Ann>();
}

export function ctx_bind(ctx: Ctx, i: number, q: Quant, k: Name, T: HTerm): Ctx {
  return pmap_set(ctx, i, { q, k, T });
}

export function ctx_dead(book: Book, ctx: Ctx): boolean {
  for (const [, a] of pmap_to_array(ctx)) {
    if (a.q.$ === "None") {
      continue;
    }
    const t = term_wnf(book, a.T);
    if (t.$ === "ADT" && book_adt(book, t, ctx).c.length === 0) {
      return true;
    }
  }
  return false;
}

export function ctx_scope(ctx: Ctx): Name[] {
  const anns = pmap_to_array(ctx);
  anns.sort((a, b) => a[0] - b[0]);
  const bnd: Name[] = [];
  for (const [i, a] of anns) {
    while (bnd.length < i) {
      bnd.push("_");
    }
    bnd.push(a.k);
  }
  return bnd;
}

// Ctrs
// ====

export function ctrs_find(cs: Ctrs, k: Name): Ctr | null {
  for (const c of cs) {
    if (c.k === k) {
      return c;
    }
  }
  return null;
}

// Book
// ====

export function book_nil(): Book {
  return { tlds: Object.create(null), ctrs: Object.create(null), order: [], halts: false };
}

export function book_ctr(book: Book, k: Name): Ctr | null {
  return book.ctrs[k] ?? null;
}

export function book_adt(book: Book, tm: Extract<HTerm, { $: "ADT" }>, ctx: Ctx, def?: Name): ADT {
  const tld = book.tlds[tm.k];
  if (tld === undefined || tld.$ !== "ADT") {
    throw Err(book, ctx, "a declared datatype (unknown: " + tm.k + ")", undefined, tm.s, def);
  }
  if (tm.r.length === 0) {
    return tld;
  }
  return { $: "ADT", n: tld.n, T: tld.T, c: tld.c.filter((c) => !tm.r.includes(c.k)) };
}

// Tele
// ====

export function tele_bind(tele: Array<[Quant, Name, number, LTerm]>, end: LTerm): LTerm {
  let out = end;
  for (let j = tele.length - 1; j >= 0; j--) {
    const [q, k, i, T] = tele[j];
    out = All(q, k, i, T, out);
  }
  return out;
}

export function tele_open(book: Book, tel: HTerm): Extract<HTerm, { $: "All" }> | null {
  const t = term_wnf(book, tel);
  return t.$ === "All" ? t : null;
}

export function tele_head(book: Book, tel: HTerm, ctx: Ctx, def?: Name, s?: Span): Extract<HTerm, { $: "All" }> {
  const t = tele_open(book, tel);
  if (t === null) {
    throw Err(book, ctx, "unreachable (a telescope binds its parameters and fields)", undefined, s, def);
  }
  return t;
}

export function tele_unbind(book: Book, T: HTerm): { doms: Array<[Quant, Name, HTerm]>; ret: HTerm } {
  const doms: Array<[Quant, Name, HTerm]> = [];
  let tel = T;
  for (let t = tele_open(book, tel); t !== null; t = tele_open(book, tel)) {
    doms.push([t.q, t.k, t.A]);
    tel = t.B(Var(t.k, doms.length - 1));
  }
  return { doms, ret: term_wnf(book, tel) };
}

// Nat
// ===

export function nat_to_term(n: U32, end: LTerm, s?: Span): LTerm {
  let out = end;
  for (let i = 0; i < n; i++) {
    out = Ctr("Succ", [out], s);
  }
  return out;
}

// U32
// ===

export function u32_to_term(n: U32, s?: Span): LTerm {
  let out: LTerm = Ctr("WNil", [], s);
  for (let i = 31; i >= 0; i--) {
    const bit = (n >>> i) & 1;
    out = Ctr("WCon", [Ctr(bit === 1 ? "True" : "False", [], s), out], s);
  }
  return Ctr("U32", [out], s);
}

export function u32_from_term<X>(tm: TermOf<X>): number | null {
  function strip(x: TermOf<X>): TermOf<X> {
    let t = term_force(x);
    while (t.$ === "Ann") {
      t = term_force(t.x);
    }
    return t;
  }
  const t = strip(tm);
  if (t.$ !== "Ctr" || t.k !== "U32" || t.x.length !== 1) {
    return null;
  }
  let n = 0;
  let i = 0;
  let w = strip(t.x[0]);
  while (w.$ === "Ctr" && w.k === "WCon" && w.x.length === 2) {
    const b = strip(w.x[0]);
    if (b.$ !== "Ctr" || b.x.length !== 0 || (b.k !== "True" && b.k !== "False")) {
      return null;
    }
    if (b.k === "True") {
      n += 2 ** i;
    }
    i += 1;
    w = strip(w.x[1]);
  }
  if (i !== 32 || w.$ !== "Ctr" || w.k !== "WNil" || w.x.length !== 0) {
    return null;
  }
  return n;
}

// Show
// ====

export function quant_show(q: Quant): string {
  switch (q.$) {
    case "None": return "-";
    case "Lone": return "";
    case "Many": return "+";
  }
}

export function char_show(n: U32, quote: string): string | null {
  if (n === 10) {
    return "\\n";
  }
  if (n === 9) {
    return "\\t";
  }
  if (n === 13) {
    return "\\r";
  }
  if (n === 0) {
    return "\\0";
  }
  if (n === 92) {
    return "\\\\";
  }
  if (n === quote.codePointAt(0)) {
    return "\\" + quote;
  }
  if (n < 32 || n === 127 || (n >= 0xd800 && n <= 0xdfff) || n > 0x10ffff) {
    return null;
  }
  return String.fromCodePoint(n);
}

export function term_show(term: LTerm, top: number = 0, bnd: Name[] = []): string {
  type Q = [LTerm, number];
  function* term_show_sugar_exi(tm: LTerm, prc: number): Generator<Q, string | null, string> {
    const t = term_force(tm);
    if (t.$ !== "ADT" || t.k !== "Sigma" || t.x.length !== 2) {
      return null;
    }
    const b = term_force(t.x[1]);
    if (b.$ !== "Lam") {
      return null;
    }
    const A = yield [t.x[0], 2];
    bnd.push(b.k);
    const f = yield [b.f, 1];
    bnd.pop();
    const s = "&" + b.k + ":" + A + " -> " + f;
    return prc > 1 ? "(" + s + ")" : s;
  }
  function* term_show_sugar_nat(tm: LTerm, prc: number): Generator<Q, string | null, string> {
    let n = 0;
    let t = term_force(tm);
    while (t.$ === "Ctr" && t.k === "Succ" && t.x.length === 1) {
      n += 1;
      t = term_force(t.x[0]);
    }
    if (t.$ === "Ctr" && t.k === "Zero" && t.x.length === 0) {
      return String(n) + "n";
    }
    if (n === 0) {
      return null;
    }
    const k = yield [t, 1];
    const s = String(n) + "n+" + k;
    return prc > 1 ? "(" + s + ")" : s;
  }
  function term_show_sugar_chr(tm: LTerm, quote: string): string | null {
    const t = term_force(tm);
    if (t.$ !== "Ctr" || t.k !== "Chr" || t.x.length !== 1) {
      return null;
    }
    const n = u32_from_term(t.x[0]);
    if (n === null || n > 0x10ffff) {
      return null;
    }
    return char_show(n, quote);
  }
  function term_show_sugar_str(tm: LTerm): string | null {
    let out = "";
    let t = term_force(tm);
    while (t.$ === "Ctr" && t.k === "SCon" && t.x.length === 2) {
      const c = term_show_sugar_chr(t.x[0], "\"");
      if (c === null) {
        return null;
      }
      out += c;
      t = term_force(t.x[1]);
    }
    if (out === "" || t.$ !== "Ctr" || t.k !== "SNil" || t.x.length !== 0) {
      return null;
    }
    return "\"" + out + "\"";
  }
  function* go([tm, prc]: Q): Generator<Q, string, string> {
    switch (tm.$) {
      case "Var": {
        return bnd.lastIndexOf(tm.k) === tm.i ? tm.k : tm.k + "^" + String(tm.i);
      }
      case "Ref": {
        return bnd.includes(tm.k) ? tm.k + "^" : tm.k;
      }
      case "Sub": {
        return yield [tm.f, prc];
      }
      case "Let": {
        const v = yield [tm.v, 1];
        bnd.push(tm.k);
        const f = yield [tm.f, 0];
        bnd.pop();
        const s = quant_show(tm.q) + tm.k + " = " + v + "; " + f;
        return prc > 0 ? "(" + s + ")" : s;
      }
      case "Typ": {
        return "Type";
      }
      case "All": {
        const A = yield [tm.A, 2];
        bnd.push(tm.k);
        const B = yield [tm.B, 1];
        bnd.pop();
        const s = "@" + quant_show(tm.q) + tm.k + ":" + A + " -> " + B;
        return prc > 1 ? "(" + s + ")" : s;
      }
      case "Lam": {
        bnd.push(tm.k);
        const f = yield [tm.f, 0];
        bnd.pop();
        const s = tm.k + " => " + f;
        return prc > 0 ? "(" + s + ")" : s;
      }
      case "App": {
        const xs: LTerm[] = [];
        let h: LTerm = tm;
        while (h.$ === "App") {
          xs.push(h.x);
          h = term_force(h.f);
        }
        xs.reverse();
        const hs = yield [h, 2];
        const as: string[] = [];
        for (const x of xs) {
          as.push(yield [x, 0]);
        }
        return hs + "(" + as.join(", ") + ")";
      }
      case "ADT": {
        const sug = yield* term_show_sugar_exi(tm, prc);
        if (sug !== null) {
          return sug;
        }
        const as: string[] = [];
        for (const x of tm.x) {
          as.push(yield [x, 0]);
        }
        const rs = tm.r.map((c) => " - " + c + "{}").join("");
        const s  = tm.k + (as.length === 0 && rs === "" ? "" : "<" + as.join(", ") + ">") + rs;
        return rs !== "" && prc > 1 ? "(" + s + ")" : s;
      }
      case "Ctr": {
        const chr = term_show_sugar_chr(tm, "'");
        const sug = (yield* term_show_sugar_nat(tm, prc))
                 ?? (chr !== null ? "'" + chr + "'" : null)
                 ?? term_show_sugar_str(tm);
        if (sug !== null) {
          return sug;
        }
        const as: string[] = [];
        for (const x of tm.x) {
          as.push(yield [x, 0]);
        }
        return tm.k + "{" + as.join(", ") + "}";
      }
      case "Mat": {
        const arms: string[] = [];
        let m: LTerm = tm;
        while (m.$ === "Mat") {
          arms.push(m.k + ": " + (yield [m.h, 1]));
          m = term_force(m.m);
        }
        if (m.$ !== "Efq") {
          arms.push(yield [m, 1]);
        }
        return "\\{" + arms.join("; ") + "}";
      }
      case "Efq": {
        return "\\{}";
      }
      case "Eql": {
        return "{" + (yield [tm.a, 1]) + " == " + (yield [tm.b, 1]) + " : " + (yield [tm.T, 1]) + "}";
      }
      case "Rfl": {
        return "{==}";
      }
      case "Rwt": {
        const e = yield [tm.e, 1];
        let mp = term_force(tm.p);
        while (mp.$ === "Ann") {
          mp = term_force(mp.x);
        }
        if (mp.$ === "Lam") {
          let mb = term_force(mp.f);
          while (mb.$ === "Ann") {
            mb = term_force(mb.x);
          }
          if (mb.$ === "Lam") {
            bnd.push(mp.k);
            bnd.push(mb.k);
            const P = yield [mb.f, 1];
            bnd.pop();
            bnd.pop();
            const f = yield [tm.f, 0];
            const n = mb.k === "" ? "" : mb.k + "@";
            const s = "%" + n + e + " : " + P + "; " + f;
            return prc > 0 ? "(" + s + ")" : s;
          }
        }
        const P = yield [tm.p, 1];
        const f = yield [tm.f, 0];
        const s = "%" + e + " : " + P + "; " + f;
        return prc > 0 ? "(" + s + ")" : s;
      }
      case "Cop": {
        const s = "+" + (yield [tm.T, 2]) + " ~ " + (yield [tm.c, 2]);
        return prc > 1 ? "(" + s + ")" : s;
      }
      case "Ann": {
        return "{" + (yield [tm.x, 1]) + " : " + (yield [tm.T, 1]) + "}";
      }
      case "Laz": {
        return yield [term_force(tm), prc];
      }
    }
  }
  return loop_run(go, [term, top]);
}

export function expr_show(book: Book, x: Expr, bnd: Name[] = []): string {
  if (typeof x === "string") {
    return x;
  } else {
    const t = term_lower(term_snf(book, x), bnd.length);
    return term_show(t, 0, bnd);
  }
}

export function ctx_show(book: Book, ctx: Ctx): string {
  const anns = pmap_to_array(ctx);
  anns.sort((a, b) => a[0] - b[0]);
  const bnd = ctx_scope(ctx);
  let wid = 0;
  for (const [, a] of anns) {
    wid = Math.max(wid, a.k.length);
  }
  let out = anns.length === 0 ? "" : "\nContext:";
  for (const [i, a] of anns) {
    const T = term_show(term_lower(term_snf(book, a.T), i), 0, bnd.slice(0, i));
    out += "\n- " + a.k.padEnd(wid) + " : " + T;
  }
  return out;
}

export function span_show(s: Span): string {
  const lns = s.src.split("\n");
  const beg = Math.max(1, s.beg.lin - 1);
  const end = Math.min(lns.length, s.beg.lin + 1);
  const out: string[] = [];
  for (let lin = beg; lin <= end; lin++) {
    const bar = lin === s.beg.lin ? ">| " : " | ";
    out.push(String(lin).padStart(String(end).length) + bar + (lns[lin - 1] ?? ""));
  }
  return out.join("\n");
}

export function err_show(err: Err): string {
  const bnd = ctx_scope(err.ctx);
  const msg = err.obs === undefined
    ? "\n- message  : " + expr_show(err.bok, err.exp, bnd)
    : "\n- expected : " + expr_show(err.bok, err.exp, bnd) + "\n- observed : " + expr_show(err.bok, err.obs, bnd);
  const def = err.def === undefined ? "" : " " + err.def;
  const spn = err.spn === undefined ? "" : "\n" + span_show(err.spn);
  const loc = def === "" && spn === "" ? "" : "\nLocation:" + def + spn;
  return "Error:" + msg + ctx_show(err.bok, err.ctx) + loc;
}

// Parse
// =====

const IS_KEYWORD: Record<Name, Bool> = {
  "def"   : true, "type": true, "match": true,
  "case"  : true, "do"  : true, "return": true,
  "Type"  : true, "if"  : true, "elif"  : true,
  "else"  : true,
};

export function parse_new(str: string, book: Book, ns: string, bs: Bool = false, dir: string = ""): Parse {
  return { str, loc: { pos: 0, lin: 1, col: 1 }, env: [], ids: Object.create(null), frs: 0, book, ns, gtd: 0, bs, dir };
}

export function parse_loc(p: Parse): Loc {
  return { pos: p.loc.pos, lin: p.loc.lin, col: p.loc.col };
}

export function parse_span(p: Parse, beg: Loc): Span {
  return { src: p.str, beg, end: parse_loc(p) };
}

export function parse_fail(p: Parse, exp: string): never {
  const here = parse_loc(p);
  const obs  = p.loc.pos < p.str.length ? "'" + p.str[p.loc.pos] + "'" : "end of input";
  throw Err(p.book, ctx_nil(), exp, obs, { src: p.str, beg: here, end: here });
}

export function parse_peek(p: Parse): string {
  return p.loc.pos < p.str.length ? p.str[p.loc.pos] : "";
}

export function parse_bump(p: Parse): string {
  const c = parse_peek(p);
  p.loc.pos += 1;
  if (c === "\n") {
    p.loc.lin += 1;
    p.loc.col = 1;
  } else {
    p.loc.col += 1;
  }
  return c;
}

export function parse_at(p: Parse, s: string): boolean {
  return p.str.startsWith(s, p.loc.pos);
}

export function parse_take(p: Parse, s: string): boolean {
  if (!parse_at(p, s)) {
    return false;
  }
  for (let i = 0; i < s.length; i++) {
    parse_bump(p);
  }
  return true;
}

export function parse_skip(p: Parse): void {
  while (true) {
    const c = parse_peek(p);
    if (c === " " || c === "\n" || c === "\r" || c === "\t") {
      parse_bump(p);
      continue;
    }
    if (c === "#") {
      while (parse_peek(p) !== "" && parse_peek(p) !== "\n") {
        parse_bump(p);
      }
      continue;
    }
    return;
  }
}

export function parse_eat(p: Parse, s: string): void {
  parse_skip(p);
  if (!parse_take(p, s)) {
    parse_fail(p, "'" + s + "'");
  }
}

export function parse_at_word(p: Parse, w: string): boolean {
  parse_skip(p);
  if (!parse_at(p, w)) {
    return false;
  }
  const nxt = p.str[p.loc.pos + w.length] ?? "";
  return nxt === "" || !char_is_name(nxt);
}

export function parse_word(p: Parse, w: string): boolean {
  if (!parse_at_word(p, w)) {
    return false;
  }
  parse_take(p, w);
  return true;
}

export function parse_lexeme(p: Parse): Name {
  parse_skip(p);
  if (!char_is_head(parse_peek(p))) {
    parse_fail(p, "a name");
  }
  let k = "";
  while (char_is_name(parse_peek(p))) {
    k += parse_bump(p);
  }
  if (k.endsWith(".")) {
    parse_fail(p, "a name (a name cannot end in '.')");
  }
  return k;
}

export function parse_name(p: Parse): Name {
  const k = parse_lexeme(p);
  if (IS_KEYWORD[k] === true) {
    parse_fail(p, "a name (got the keyword '" + k + "')");
  }
  return k;
}

export function parse_char(p: Parse): U32 {
  if (parse_take(p, "\\")) {
    const c = parse_bump(p);
    switch (c) {
      case "n":  return 10;
      case "t":  return 9;
      case "r":  return 13;
      case "0":  return 0;
      case "\\": return 92;
      case "'":  return 39;
      case '"':  return 34;
      default: {
        parse_fail(p, "an escape (\\n \\t \\r \\0 \\\\ \\' \\\")");
      }
    }
  }
  const n = p.str.codePointAt(p.loc.pos);
  if (n === undefined) {
    parse_fail(p, "a character");
  }
  parse_bump(p);
  if (n > 0xffff) {
    parse_bump(p);
  }
  return n;
}

// Binders
// -------

export function parse_open(p: Parse, k: Name): number {
  const i = p.frs++;
  if (k !== "_") {
    p.env.push(k);
    (p.ids[k] ?? (p.ids[k] = [])).push(i);
  }
  return i;
}

export function parse_close(p: Parse, n: number): void {
  while (p.env.length > n) {
    const k = p.env.pop() as Name;
    p.ids[k].pop();
  }
}

export function parse_var(p: Parse, k: Name, s?: Span): LTerm {
  const st = p.ids[k];
  if (st !== undefined && st.length > 0) {
    return Var(k, st[st.length - 1], s);
  }
  const q = parse_qual(p, k);
  if (q !== k && p.book.tlds[q] !== undefined) {
    return Ref(q, s);
  }
  if (k.includes(".")) {
    return Ref(k, s);
  }
  return Var(k, p.frs++, s);
}

export function parse_qual(p: Parse, k: Name): Name {
  return p.ns === "" ? k : p.ns + "." + k;
}

// Quant
// -----

export function parse_quant(p: Parse): Quant {
  parse_skip(p);
  if (parse_take(p, "-")) {
    return None();
  }
  if (parse_take(p, "+")) {
    return Many();
  }
  return Lone();
}

// Patt
// ----

export function parse_patt(p: Parse, book: Book, t: LTerm): Patt {
  switch (t.$) {
    case "Var": {
      if (book_ctr(book, t.k) !== null || book_ctr(book, parse_qual(p, t.k)) !== null) {
        throw Err(book, ctx_nil(), "a braced constructor pattern (" + t.k + " is a constructor: write " + t.k + "{}, or rename the binder)", undefined, t.s);
      }
      const i = parse_open(p, t.k);
      return { $: "PVar", k: t.k, i, s: t.s };
    }
    case "Ctr": {
      const ctr = book_ctr(book, t.k);
      if (ctr === null) {
        throw Err(book, ctx_nil(), "a declared constructor (unknown: " + t.k + ")", undefined, t.s);
      }
      if (ctr.n !== t.x.length) {
        throw Err(book, ctx_nil(), "a " + t.k + " pattern with " + String(ctr.n) + (ctr.n === 1 ? " field" : " fields"), undefined, t.s);
      }
      const xs: Patt[] = [];
      for (const x of t.x) {
        const px = parse_patt(p, book, x);
        xs.push(px);
      }
      return { $: "PCtr", k: t.k, x: xs, s: t.s };
    }
    default: {
      throw Err(book, ctx_nil(), "a pattern (a binder or a constructor)", term_show(term_lower(term_higher(t, Emp<HTerm>()), 0)), t.s);
    }
  }
}

// Term
// ----

export function parse_term(p: Parse): LTerm {
  parse_skip(p);
  const beg  = parse_loc(p);
  const base = parse_term_base(p);
  if (base.s === undefined) {
    base.s = parse_span(p, beg);
  }
  const out = parse_term_suff(p, base);
  if (out.s === undefined) {
    out.s = parse_span(p, beg);
  }
  return out;
}

export function parse_term_dom(p: Parse): LTerm {
  return parse_term_lvl(p, 0);
}

export function parse_term_lvl(p: Parse, lvl: number): LTerm {
  parse_skip(p);
  const beg  = parse_loc(p);
  const base = parse_term_base(p);
  if (base.s === undefined) {
    base.s = parse_span(p, beg);
  }
  const out = parse_term_infx(p, base, lvl);
  if (out.s === undefined) {
    out.s = parse_span(p, beg);
  }
  return out;
}

export function parse_term_base(p: Parse): LTerm {
  parse_skip(p);
  const beg = parse_loc(p);
  const c   = parse_peek(p);
  if (char_is_head(c)) {
    const k = parse_lexeme(p);
    const t = parse_term_base_word(p, k, beg);
    return t;
  }
  if (/[0-9]/.test(c)) {
    const t = parse_term_num(p);
    return t;
  }
  switch (c) {
    case "@": {
      const t = parse_term_all(p);
      return t;
    }
    case "&": {
      const t = parse_term_exi(p);
      return t;
    }
    case "\\": {
      parse_bump(p);
      parse_eat(p, "{");
      const g = p.gtd;
      p.gtd = 0;
      const t = parse_term_mat(p);
      p.gtd = g;
      return t;
    }
    case "%": {
      const t = parse_term_rwt(p, beg);
      return t;
    }
    case "{": {
      const g = p.gtd;
      p.gtd = 0;
      const t = parse_term_brc(p);
      p.gtd = g;
      return t;
    }
    case "(": {
      parse_bump(p);
      const g = p.gtd;
      p.gtd = 0;
      const t = parse_term_tup(p, beg);
      p.gtd = g;
      return t;
    }
    case "[": {
      parse_bump(p);
      const xs  = parse_term_args(p, "]");
      const spn = parse_span(p, beg);
      let t: LTerm = Ctr("Nil", [], spn);
      for (let i = xs.length - 1; i >= 0; i--) {
        t = Ctr("Con", [xs[i], t], spn);
      }
      return t;
    }
    case "'": {
      const t = parse_term_chr(p);
      return t;
    }
    case '"': {
      const t = parse_term_str(p);
      return t;
    }
    case "-": {
      parse_bump(p);
      const k = parse_name(p);
      parse_eat(p, "=");
      const t = parse_term_let(p, k, None(), parse_span(p, beg));
      return t;
    }
    case "+": {
      const t = parse_term_cop(p, beg);
      return t;
    }
    default: {
      parse_fail(p, "a term");
    }
  }
}

export function parse_term_base_word(p: Parse, k: Name, beg: Loc): LTerm {
  switch (k) {
    case "Type": {
      return Typ(parse_span(p, beg));
    }
    case "do": {
      return parse_term_do(p);
    }
    case "match": {
      parse_fail(p, "a term (a match heads a def body, not a term)");
    }
    case "if": {
      return parse_term_if(p);
    }
    case "elif":
    case "else": {
      parse_fail(p, "an if heading this " + k);
    }
    case "case": {
      parse_fail(p, "a match heading this case (this case is orphaned)");
    }
    case "return": {
      parse_fail(p, "a do-block heading this return");
    }
    default: {
      if (IS_KEYWORD[k] === true) {
        parse_fail(p, "a term (the keyword '" + k + "' cannot head one)");
      }
      if (parse_at(p, "{")) {
        parse_bump(p);
        const xs = parse_term_args(p, "}");
        const q  = parse_qual(p, k);
        return Ctr(q !== k && book_ctr(p.book, q) !== null ? q : k, xs, parse_span(p, beg));
      }
      if (parse_at(p, "<") && !parse_at(p, "<-") && !parse_at(p, "<>") && !parse_at(p, "<=") && !parse_at(p, "<<") && !parse_at(p, "<.")) {
        parse_bump(p);
        const xs = parse_term_args(p, ">");
        const q  = parse_qual(p, k);
        return ADT(q !== k && p.book.tlds[q] !== undefined ? q : k, xs, parse_span(p, beg));
      }
      const v = parse_var(p, k, parse_span(p, beg));
      return v;
    }
  }
}

// infix table: token, level (higher binds tighter), right-assoc, target.
// levels follow bend3's ladder: types < || < && < compares < <> ++ <
// .|. < .^. < .&. < shifts < additive < multiplicative. tokens are
// longest-first so prefixes never shadow; "" targets are special forms.
const INFIX_OPS: Array<[string, number, Bool, Name]> = [
  ["==.",  4, false, "F32.is_eq"], ["!=.",  4, false, "F32.is_ne"],
  ["<=.",  4, false, "F32.is_le"], [">=.",  4, false, "F32.is_ge"],
  ["<.",   4, false, "F32.is_lt"], [">.",   4, false, "F32.is_gt"],
  [".|.",  6, false, "U32.or"],    [".^.",  7, false, "U32.xor"],
  [".&.",  8, false, "U32.and"],   ["+.",  10, false, "F32.add"],
  ["-.",  10, false, "F32.sub"],   ["*.",  11, false, "F32.mul"],
  ["/.",  11, false, "F32.div"],   ["||",   2, false, "Bool.or"],
  ["&&",   3, false, "Bool.and"],  ["<=",   4, false, "U32.is_le"],
  [">=",   4, false, "U32.is_ge"], ["<>",   5, true,  ""],
  ["++",   5, true,  "String.append"],
  ["<<",   9, false, "U32.shln"],  [">>",   9, false, "U32.shrn"],
  ["&",    1, true,  ""],          ["|",    1, true,  ""],
  ["<",    4, false, "U32.is_lt"], [">",    4, false, "U32.is_gt"],
  ["+n",  10, false, "Nat.add"],
  ["+",   10, false, "U32.add"],   ["-",   10, false, "U32.sub"],
  ["*",   11, false, "U32.mul"],   ["/",   11, false, "U32.div"],
];

export function parse_infx_find(p: Parse): [string, number, Bool, Name] | null {
  for (const op of INFIX_OPS) {
    if (!parse_at(p, op[0])) {
      continue;
    }
    const nx = p.str[p.loc.pos + op[0].length] ?? "";
    if ((op[0] === "-" || op[0] === "+") && (nx === ">" || char_is_head(nx))) {
      continue;
    }
    if (op[0] === "+n" && char_is_name(nx)) {
      continue;
    }
    if (op[0] === "<" && nx === "-") {
      continue;
    }
    if (p.gtd > 0 && (op[0] === ">" || op[0] === ">=" || op[0] === ">>" || op[0] === ">.")) {
      continue;
    }
    return op;
  }
  return null;
}

export function parse_term_infx(p: Parse, tm: LTerm, lvl: number = 0): LTerm {
  let out = tm;
  while (true) {
    if (parse_at(p, "!(")) {
      if (out.$ === "Var" && (p.ids[out.k] ?? []).length === 0) {
        out = Ref(out.k, out.s);
      }
      if (out.$ !== "Ref") {
        parse_fail(p, "a named def before ! (only f!(..) offloads)");
      }
      parse_bump(p);
      out.b = true;
      continue;
    }
    if (parse_at(p, "(")) {
      parse_bump(p);
      const xs = parse_term_args(p, ")");
      const s  = out.s === undefined ? undefined : parse_span(p, out.s.beg);
      for (const x of xs) {
        out = App(out, x, s);
      }
      continue;
    }
    if (parse_at(p, "[")) {
      parse_bump(p);
      const g = p.gtd;
      p.gtd = 0;
      const ix = parse_term(p);
      parse_eat(p, "]");
      p.gtd = g;
      const s   = out.s === undefined ? undefined : parse_span(p, out.s.beg);
      const bk2 = parse_loc(p);
      parse_skip(p);
      if (parse_take(p, "<-")) {
        const v = parse_term_lvl(p, 2);
        out = App(App(App(Ref("Array.set", s), out, s), ix, s), v, s);
      } else {
        p.loc = bk2;
        out = App(App(Ref("Array.get", s), out, s), ix, s);
      }
      continue;
    }
    const bak = parse_loc(p);
    parse_skip(p);
    const op = parse_infx_find(p);
    if (op === null || op[1] < lvl) {
      p.loc = bak;
      return out;
    }
    parse_take(p, op[0]);
    const b = parse_term_lvl(p, op[2] ? op[1] : op[1] + 1);
    const s = out.s === undefined ? undefined : parse_span(p, out.s.beg);
    if (op[0] === "&") {
      out = App(App(Ref("Pair", s), out, s), b, s);
    } else if (op[0] === "|") {
      out = ADT("Either", [out, b], s);
    } else if (op[0] === "<>") {
      out = Ctr("Con", [out, b], s);
    } else if (op[1] === 9) {
      out = App(App(Ref(op[3], s), b, s), out, s);
    } else {
      out = App(App(Ref(op[3], s), out, s), b, s);
    }
  }
}

export function parse_term_suff(p: Parse, tm: LTerm): LTerm {
  const out = parse_term_infx(p, tm);
  const bak = parse_loc(p);
  parse_skip(p);
  if (parse_take(p, "=>")) {
    if (out.$ !== "Var") {
      parse_fail(p, "a lambda binder (one name: k => body)");
    }
    const n0 = p.env.length;
    const i  = parse_open(p, out.k);
    const f  = parse_term(p);
    parse_close(p, n0);
    return Lam(out.k, i, f, out.s);
  }
  if (parse_take(p, "->")) {
    const B = parse_term(p);
    return All(Lone(), "_", parse_open(p, "_"), out, B);
  }
  if (parse_at(p, "=") && !parse_at(p, "==")) {
    if (out.$ !== "Var") {
      p.loc = bak;
      return out;
    }
    parse_bump(p);
    const t = parse_term_let(p, out.k, Lone(), out.s);
    return t;
  }
  p.loc = bak;
  return out;
}

export function parse_term_let(p: Parse, k: Name, q: Quant, s?: Span): LTerm {
  const v = parse_term(p);
  parse_skip(p);
  parse_take(p, ";");
  const n0 = p.env.length;
  const i  = parse_open(p, k);
  const f  = parse_term(p);
  parse_close(p, n0);
  return Let(k, i, v, f, s, q);
}

export function parse_at_let(p: Parse): boolean {
  const bak = parse_loc(p);
  parse_skip(p);
  let ok = char_is_head(parse_peek(p));
  if (ok) {
    const k = parse_lexeme(p);
    parse_skip(p);
    ok = IS_KEYWORD[k] !== true && parse_at(p, "=") && !parse_at(p, "==");
  }
  p.loc = bak;
  return ok;
}

export function parse_term_cop(p: Parse, beg: Loc): LTerm {
  parse_bump(p);
  if (parse_at_let(p)) {
    const k = parse_name(p);
    parse_eat(p, "=");
    return parse_term_let(p, k, Many(), parse_span(p, beg));
  }
  const T = parse_term_lvl(p, 2);
  parse_skip(p);
  const c = parse_take(p, "~") ? parse_term_lvl(p, 2) : parse_term_cop_wit(p, T);
  return Cop(T, c, parse_span(p, beg));
}

export function parse_term_cop_wit(p: Parse, T: LTerm): LTerm {
  const xs: LTerm[] = [];
  let h = T;
  while (h.$ === "App") {
    xs.push(h.x);
    h = h.f;
  }
  xs.reverse();
  if (h.$ === "ADT" && xs.length === 0) {
    for (const x of h.x) {
      xs.push(x);
    }
  } else if (h.$ !== "Var" && h.$ !== "Ref") {
    parse_fail(p, "a copy witness (spell + T ~ C for this type)");
  }
  let c = parse_var(p, h.k + ".copy", h.s);
  for (const x of xs) {
    c = App(c, parse_term_cop_wit(p, x), h.s);
  }
  return c;
}

export function parse_term_args(p: Parse, close: string): LTerm[] {
  const xs: LTerm[] = [];
  const g = p.gtd;
  p.gtd = close === ">" ? g + 1 : 0;
  while (true) {
    parse_skip(p);
    if (parse_take(p, close)) {
      p.gtd = g;
      return xs;
    }
    const x = parse_term(p);
    xs.push(x);
    parse_skip(p);
    parse_take(p, ",");
  }
}

export function parse_term_all(p: Parse): LTerm {
  parse_bump(p);
  const q = parse_quant(p);
  const k = parse_name(p);
  parse_eat(p, ":");
  const A = parse_term_dom(p);
  parse_eat(p, "->");
  const n0 = p.env.length;
  const i  = parse_open(p, k);
  const B  = parse_term(p);
  parse_close(p, n0);
  return All(q, k, i, A, B);
}

export function parse_term_exi(p: Parse): LTerm {
  parse_bump(p);
  const k = parse_name(p);
  parse_eat(p, ":");
  const A = parse_term_dom(p);
  parse_skip(p);
  if (parse_take(p, "->")) {
    const n0 = p.env.length;
    const i  = parse_open(p, k);
    const B  = parse_term(p);
    parse_close(p, n0);
    return ADT("Sigma", [A, Lam(k, i, B)]);
  }
  parse_eat(p, "=");
  const ks: Name[]  = [k];
  const As: LTerm[] = [A];
  const vs: LTerm[] = [parse_term_lvl(p, 2)];
  while (true) {
    parse_skip(p);
    if (!parse_take(p, "&")) {
      break;
    }
    ks.push(parse_name(p));
    parse_eat(p, ":");
    As.push(parse_term_dom(p));
    parse_eat(p, "=");
    vs.push(parse_term_lvl(p, 2));
  }
  if (ks.length < 2) {
    parse_fail(p, "a second fork binding (a fork pairs: & x: A = v & y: B = w; body)");
  }
  parse_take(p, ";");
  const n0 = p.env.length;
  const is = ks.map(kk => parse_open(p, kk));
  const f  = parse_term(p);
  parse_close(p, n0);
  let T = As[As.length - 1];
  let v = vs[vs.length - 1];
  for (let j = ks.length - 2; j >= 0; j--) {
    T = ADT("Par", [As[j], T]);
    v = Ctr("Both", [vs[j], v]);
  }
  const weave = (j: number): LTerm => {
    if (j === ks.length - 2) {
      return Lam(ks[j], is[j], Lam(ks[j + 1], is[j + 1], f));
    }
    const r = p.frs++;
    return Lam(ks[j], is[j], Lam("_", r, App(Mat("Both", weave(j + 1), Efq()), Var("_", r))));
  };
  return App(Mat("Both", weave(0), Efq()), Ann(v, T));
}

export function parse_term_tup(p: Parse, beg: Loc): LTerm {
  const a = parse_term(p);
  parse_skip(p);
  if (parse_take(p, ",")) {
    const b = parse_term_tup(p, beg);
    return Ctr("Tuple", [a, b], parse_span(p, beg));
  }
  parse_eat(p, ")");
  return a;
}

export function parse_term_mat(p: Parse): LTerm {
  const arms: Array<[Name, LTerm]> = [];
  let tail: LTerm = Efq();
  while (true) {
    parse_skip(p);
    if (parse_take(p, "}")) {
      break;
    }
    const beg = parse_loc(p);
    if (char_is_head(parse_peek(p))) {
      const k = parse_lexeme(p);
      const bak = parse_loc(p);
      parse_skip(p);
      if (parse_take(p, ":")) {
        if (IS_KEYWORD[k] === true) {
          parse_fail(p, "a constructor name (got the keyword '" + k + "')");
        }
        const h = parse_term(p);
        const q = parse_qual(p, k);
        arms.push([q !== k && book_ctr(p.book, q) !== null ? q : k, h]);
        parse_skip(p);
        parse_take(p, ";");
        continue;
      }
      p.loc = bak;
      tail = parse_term_suff(p, parse_term_base_word(p, k, beg));
    } else {
      tail = parse_term(p);
    }
    parse_skip(p);
    parse_take(p, ";");
    parse_eat(p, "}");
    break;
  }
  let out = tail;
  for (let i = arms.length - 1; i >= 0; i--) {
    out = Mat(arms[i][0], arms[i][1], out);
  }
  return out;
}

export function parse_term_rwt(p: Parse, beg: Loc): LTerm {
  parse_bump(p);
  parse_skip(p);
  let k = "";
  if (char_is_head(parse_peek(p))) {
    const bak = parse_loc(p);
    const nm  = parse_lexeme(p);
    parse_skip(p);
    if (parse_take(p, "@")) {
      if (IS_KEYWORD[nm] === true) {
        parse_fail(p, "a name (got the keyword '" + nm + "')");
      }
      k = nm;
    } else {
      p.loc = bak;
    }
  }
  const e = parse_term(p);
  parse_eat(p, ":");
  const n0 = p.env.length;
  const xi = p.frs++;
  p.env.push("_");
  (p.ids["_"] ?? (p.ids["_"] = [])).push(xi);
  const ei = k === "" ? p.frs++ : parse_open(p, k);
  const P  = parse_term(p);
  parse_close(p, n0);
  parse_skip(p);
  parse_take(p, ";");
  const f = parse_term(p);
  const s = parse_span(p, beg);
  return Rwt(e, Lam("_", xi, Lam(k, ei, P), s), f, s);
}

export function parse_term_if(p: Parse): LTerm {
  const c = parse_term(p);
  parse_eat(p, ":");
  const t = parse_term(p);
  parse_skip(p);
  parse_take(p, ";");
  let f: LTerm;
  if (parse_word(p, "elif")) {
    f = parse_term_if(p);
  } else {
    if (!parse_word(p, "else")) {
      parse_fail(p, "an 'elif' or 'else' (an if chain ends in else)");
    }
    parse_eat(p, ":");
    f = parse_term(p);
  }
  return App(Mat("True", t, Mat("False", f, Efq())), c);
}

export function parse_term_brc(p: Parse): LTerm {
  parse_bump(p);
  parse_skip(p);
  if (parse_take(p, "==")) {
    parse_eat(p, "}");
    return Rfl();
  }
  const a = parse_term(p);
  parse_skip(p);
  if (parse_take(p, "==")) {
    const b = parse_term(p);
    parse_eat(p, ":");
    const T = parse_term(p);
    parse_eat(p, "}");
    return Eql(a, b, T);
  }
  if (parse_take(p, "!=")) {
    const b = parse_term(p);
    parse_eat(p, ":");
    const T = parse_term(p);
    parse_eat(p, "}");
    return All(Lone(), "_", parse_open(p, "_"), Eql(a, b, T), ADT("Empty", []));
  }
  parse_eat(p, ":");
  const T = parse_term(p);
  parse_eat(p, "}");
  return Ann(a, T);
}

export function parse_term_num(p: Parse): LTerm {
  const beg = parse_loc(p);
  let s = "";
  while (/[0-9]/.test(parse_peek(p))) {
    s += parse_bump(p);
  }
  if (!parse_take(p, "n")) {
    if (parse_at(p, ".") && /[0-9]/.test(p.str[p.loc.pos + 1] ?? "")) {
      parse_bump(p);
      let fr = "";
      while (/[0-9]/.test(parse_peek(p))) {
        fr += parse_bump(p);
      }
      const m = Number(s + fr);
      const d = Math.pow(10, fr.length);
      if (m > 0xffffffff || d > 0xffffffff) {
        parse_fail(p, "a float literal with digits and scale under 2^32 (got " + s + "." + fr + ")");
      }
      const spn = parse_span(p, beg);
      return App(App(Ref("F32.make", spn), u32_to_term(m, spn), spn), u32_to_term(d, spn), spn);
    }
    if (char_is_name(parse_peek(p))) {
      parse_fail(p, "a numeric literal (NUMBER is U32, NUMBER n is Nat)");
    }
    const w = Number(s);
    if (w > 0xffffffff) {
      parse_fail(p, "a u32 literal up to 4294967295 (got " + s + ")");
    }
    return u32_to_term(w, parse_span(p, beg));
  }
  const n = Number(s);
  if (n > Number.MAX_SAFE_INTEGER) {
    parse_fail(p, "a nat literal up to " + Number.MAX_SAFE_INTEGER + "n (got " + s + "n)");
  }
  let out: LTerm;
  if (parse_take(p, "+")) {
    out = parse_term(p);
  } else {
    if (char_is_name(parse_peek(p))) {
      parse_fail(p, "a nat literal (NUMBER n)");
    }
    out = Ctr("Zero", [], parse_span(p, beg));
  }
  const spn = parse_span(p, beg);
  return nat_to_term(n, out, spn);
}

export function parse_term_chr(p: Parse): LTerm {
  const beg = parse_loc(p);
  parse_bump(p);
  const n = parse_char(p);
  if (parse_peek(p) !== "'") {
    parse_fail(p, "a closing '");
  }
  parse_bump(p);
  const spn = parse_span(p, beg);
  return Ctr("Chr", [u32_to_term(n, spn)], spn);
}

export function parse_term_str(p: Parse): LTerm {
  const beg = parse_loc(p);
  parse_bump(p);
  const cs: U32[] = [];
  while (parse_peek(p) !== '"') {
    if (p.loc.pos >= p.str.length) {
      parse_fail(p, "a closing \"");
    }
    cs.push(parse_char(p));
  }
  parse_bump(p);
  const spn = parse_span(p, beg);
  let out: LTerm = Ctr("SNil", [], spn);
  for (let i = cs.length - 1; i >= 0; i--) {
    out = Ctr("SCon", [Ctr("Chr", [u32_to_term(cs[i], spn)], spn), out], spn);
  }
  return out;
}

export function parse_term_do(p: Parse): LTerm {
  const m = parse_name(p);
  parse_eat(p, "<");
  const ts = parse_term_args(p, ">");
  parse_eat(p, ":");
  const t = parse_term_do_stmt(p, m, ts.slice(0, -1), ts.length === 0 ? null : ts[ts.length - 1]);
  return t;
}

export function parse_term_do_stmt(p: Parse, m: Name, ls: LTerm[], R: LTerm | null): LTerm {
  function parse_term_do_call(op: Name, xs: LTerm[], s: Span): LTerm {
    const q = parse_qual(p, m + "." + op);
    let fn: LTerm = Ref(p.book.tlds[q] !== undefined ? q : m + "." + op, s);
    for (const l of ls) {
      fn = App(fn, l, s);
    }
    for (const x of xs) {
      fn = App(fn, x, s);
    }
    return fn;
  }
  parse_skip(p);
  const beg = parse_loc(p);
  if (parse_word(p, "return")) {
    const e = parse_term(p);
    return parse_term_do_call("pure", R === null ? [e] : [R, e], parse_span(p, beg));
  }
  const t = parse_term(p);
  const bak = parse_loc(p);
  parse_skip(p);
  if (t.$ === "Var" && parse_take(p, ":")) {
    const A   = parse_term_dom(p);
    parse_skip(p);
    const asg = parse_at(p, "=") && !parse_at(p, "==");
    if (asg) {
      parse_bump(p);
    } else {
      parse_eat(p, "<-");
    }
    const v = parse_term(p);
    parse_skip(p);
    parse_take(p, ";");
    const s  = parse_span(p, beg);
    const n0 = p.env.length;
    const i  = parse_open(p, t.k);
    const f  = parse_term_do_stmt(p, m, ls, R);
    parse_close(p, n0);
    return asg ? Let(t.k, i, Ann(v, A, s), f, s) : parse_term_do_call("bind", R === null ? [A, v, Lam(t.k, i, f, s)] : [A, R, v, Lam(t.k, i, f, s)], s);
  }
  if (parse_take(p, "<-")) {
    const v = parse_term(p);
    parse_skip(p);
    parse_take(p, ";");
    const s = parse_span(p, beg);
    const i = parse_open(p, "_");
    const f = parse_term_do_stmt(p, m, ls, R);
    return parse_term_do_call("bind", R === null ? [t, v, Lam("_", i, f, s)] : [t, R, v, Lam("_", i, f, s)], s);
  }
  p.loc = bak;
  return t;
}

// Body
// ----

export function parse_body(p: Parse, book: Book, col: number = 0): Body {
  parse_skip(p);
  const beg = parse_loc(p);
  if (parse_at_word(p, "match")) {
    const t = parse_match(p, book, col);
    return t;
  }
  const q = parse_quant(p);
  if (q.$ === "None" || (q.$ === "Many" && parse_at_let(p))) {
    const k = parse_name(p);
    const ks = parse_span(p, beg);
    parse_eat(p, "=");
    const v = parse_term(p);
    parse_skip(p);
    parse_take(p, ";");
    const n0 = p.env.length;
    const i  = parse_open(p, k);
    const f  = parse_body(p, book, col);
    parse_close(p, n0);
    return { $: "Local", k: { $: "PVar", k, i, s: ks }, q, v, f };
  }
  if (q.$ === "Many") {
    p.loc = beg;
  }
  if (char_is_head(parse_peek(p))) {
    const bak = parse_loc(p);
    let k = "";
    while (char_is_name(parse_peek(p))) {
      k += parse_bump(p);
    }
    parse_skip(p);
    if (IS_KEYWORD[k] !== true && !k.includes(".") && parse_at(p, "=") && !parse_at(p, "==") && !parse_at(p, "=>")) {
      const ks = parse_span(p, bak);
      parse_bump(p);
      const v = parse_term(p);
      parse_skip(p);
      parse_take(p, ";");
      const n0 = p.env.length;
      const i  = parse_open(p, k);
      const f  = parse_body(p, book, col);
      parse_close(p, n0);
      return { $: "Local", k: { $: "PVar", k, i, s: ks }, q, v, f };
    }
    p.loc = bak;
  }
  const t = parse_term(p);
  parse_skip(p);
  if (parse_at(p, "=") && !parse_at(p, "==")) {
    parse_bump(p);
    const v = parse_term(p);
    parse_skip(p);
    parse_take(p, ";");
    const n0 = p.env.length;
    const k  = parse_patt(p, book, t);
    const f  = parse_body(p, book, col);
    parse_close(p, n0);
    return { $: "Local", k, q, v, f };
  }
  return { $: "Reply", x: t, s: parse_span(p, beg) };
}

export function parse_match(p: Parse, book: Book, col: number): Match {
  parse_skip(p);
  const beg = parse_loc(p);
  parse_word(p, "match");
  const es: Cell[] = [];
  let fr = false;
  while (true) {
    const e = parse_term(p);
    parse_skip(p);
    if (!parse_take(p, ":")) {
      es.push(term_cell(e));
      parse_take(p, ",");
      continue;
    }
    parse_skip(p);
    if (p.loc.pos >= p.str.length || parse_at_word(p, "case") || parse_at_word(p, "return") || parse_at_word(p, "def") || parse_at_word(p, "type") || parse_at_word(p, "assert")) {
      es.push(term_cell(e));
      break;
    }
    if (e.$ !== "Var") {
      parse_fail(p, "a case, or a framed scrutinee (x : A = v)");
    }
    const A = parse_term_dom(p);
    parse_eat(p, "=");
    const v = parse_term(p);
    es.push({ $: "Cell", k: e.k, i: parse_open(p, e.k), A, v, s: e.s });
    fr = true;
    parse_skip(p);
    if (parse_take(p, ":")) {
      break;
    }
    parse_take(p, ",");
  }
  if (fr) {
    for (const c of es) {
      if (c.A === null) {
        parse_fail(p, "a uniform match (frame every scrutinee, or none)");
      }
    }
  }
  parse_skip(p);
  const ccol = p.loc.col;
  const rows: Rows = [];
  while (ccol > col && parse_at_word(p, "case") && p.loc.col >= ccol) {
    const rcol = p.loc.col;
    parse_word(p, "case");
    const qs: LTerm[] = [];
    while (true) {
      const q = parse_term(p);
      qs.push(q);
      parse_skip(p);
      if (parse_take(p, ":")) {
        break;
      }
      parse_take(p, ",");
    }
    if (qs.length !== es.length) {
      parse_fail(p, String(es.length) + " patterns (one per scrutinee)");
    }
    const n0 = p.env.length;
    const pp: Patt[] = [];
    for (const q of qs) {
      const pq = parse_patt(p, book, q);
      pp.push(pq);
    }
    const f = parse_body(p, book, rcol);
    parse_close(p, n0);
    rows.push({ $: "Case", p: pp, f });
  }
  let P: LTerm | null = null;
  if (fr) {
    if (!parse_word(p, "return")) {
      parse_fail(p, "'return' (a framed match states its motive)");
    }
    P = parse_term(p);
  }
  return { $: "Match", e: es, P, r: rows, s: parse_span(p, beg) };
}

// Tele
// ----

export function parse_tele(p: Parse, close: string): Array<[Quant, Name, number, LTerm]> {
  const tele: Array<[Quant, Name, number, LTerm]> = [];
  const g = p.gtd;
  p.gtd = close === ">" ? g + 1 : 0;
  while (true) {
    parse_skip(p);
    if (parse_take(p, close)) {
      p.gtd = g;
      return tele;
    }
    const q = parse_quant(p);
    const k = parse_name(p);
    parse_eat(p, ":");
    const T = parse_term(p);
    tele.push([q, k, parse_open(p, k), T]);
    parse_skip(p);
    parse_take(p, ",");
  }
}

// Book
// ----

export function parse_def(p: Parse, book: Book): void {
  parse_skip(p);
  p.frs = 0;
  parse_word(p, "def");
  const k   = parse_qual(p, parse_name(p));
  const tld = book.tlds[k];
  if (tld !== undefined && tld.$ === "Def" && tld.v === null) {
    parse_def_fill(p, book, k, tld);
    return;
  }
  if (tld !== undefined) {
    parse_fail(p, "a fresh name (duplicate declaration: " + k + ")");
  }
  parse_fail(p, "a prior assert for " + k + " (an assert holds the type, a def fills the body)");
}

export function parse_def_fill(p: Parse, book: Book, k: Name, def: Def): void {
  const n0 = p.env.length;
  parse_eat(p, "(");
  const vars: PVar[] = [];
  while (true) {
    parse_skip(p);
    if (parse_take(p, ")")) {
      break;
    }
    const c = parse_name(p);
    vars.push({ $: "PVar", k: c, i: parse_open(p, c) });
    parse_skip(p);
    parse_take(p, ",");
  }
  parse_eat(p, ":");
  if (parse_at_word(p, "import")) {
    def.i = [];
    while (parse_word(p, "import")) {
      parse_eat(p, "\"");
      let path = "";
      while (parse_peek(p) !== "\"" && parse_peek(p) !== "") {
        path += parse_bump(p);
      }
      parse_eat(p, "\"");
      if (!/\.(c|js)$/.test(path)) {
        parse_fail(p, "a .c or .js path");
      }
      def.i.push(p.dir + path);
    }
    parse_close(p, n0);
    book.order.push(k);
    return;
  }
  const b = parse_body(p, book);
  parse_close(p, n0);
  const v  = body_flatten(b, vars, p.frs);
  const hv = term_higher(v, Emp<HTerm>());
  def.n = vars.length;
  def.v = hv;
  book.order.push(k);
}

export function parse_assert(p: Parse, book: Book): void {
  parse_skip(p);
  p.frs = 0;
  parse_word(p, "assert");
  const k = parse_qual(p, parse_name(p));
  if (book.tlds[k] !== undefined) {
    parse_fail(p, "a fresh name (duplicate declaration: " + k + ")");
  }
  parse_eat(p, ":");
  const n0  = p.env.length;
  const cls: Array<[Bool, Quant, Name, number, LTerm]> = [];
  while (parse_at_word(p, "forall") || parse_at_word(p, "exists")) {
    const all = parse_word(p, "forall");
    if (!all) {
      parse_word(p, "exists");
    }
    const q = all ? parse_quant(p) : Lone();
    const c = parse_name(p);
    parse_eat(p, ":");
    let A = parse_term(p);
    if (parse_word(p, "where")) {
      const n1 = p.env.length;
      const i  = parse_open(p, c);
      const w  = parse_term(p);
      parse_close(p, n1);
      A = ADT("Sigma", [A, Lam(c, i, w)]);
    }
    cls.push([all, q, c, parse_open(p, c), A]);
  }
  let T = parse_term(p);
  for (let j = cls.length - 1; j >= 0; j--) {
    const [all, q, c, i, A] = cls[j];
    T = all ? All(q, c, i, A, T) : ADT("Sigma", [A, Lam(c, i, T)]);
  }
  parse_close(p, n0);
  let n = 0;
  while (n < cls.length && cls[n][0]) {
    n += 1;
  }
  const hT = term_higher(T, Emp<HTerm>());
  book.tlds[k] = { $: "Def", n, T: hT, v: null, b: p.bs };
  book.order.push(k);
}

export function parse_adt(p: Parse, book: Book): void {
  parse_skip(p);
  p.frs = 0;
  parse_word(p, "type");
  const k = parse_qual(p, parse_name(p));
  if (book.tlds[k] !== undefined) {
    parse_fail(p, "a fresh name (duplicate declaration: " + k + ")");
  }
  const n0 = p.env.length;
  let params: Array<[Quant, Name, number, LTerm]> = [];
  parse_skip(p);
  if (parse_take(p, "<")) {
    params = parse_tele(p, ">");
  }
  parse_eat(p, ":");
  const sig = tele_bind(params, Typ());
  const hs  = term_higher(sig, Emp<HTerm>());
  const cs: Ctrs = [];
  book.tlds[k] = { $: "ADT", n: params.length, T: hs, c: cs };
  while (true) {
    parse_skip(p);
    if (p.loc.pos >= p.str.length || !char_is_head(parse_peek(p))) {
      break;
    }
    if (parse_at_word(p, "def") || parse_at_word(p, "type") || parse_at_word(p, "assert")) {
      break;
    }
    const c = parse_qual(p, parse_name(p));
    if (book_ctr(book, c) !== null) {
      parse_fail(p, "a fresh constructor name (duplicate declaration: " + c + ")");
    }
    parse_eat(p, "{");
    const n1 = p.env.length;
    const fs = parse_tele(p, "}");
    const target: LTerm = ADT(k, params.map((cell) => Var(cell[1], cell[2])));
    const T  = tele_bind(params.concat(fs), target);
    const hT = term_higher(T, Emp<HTerm>());
    parse_close(p, n1);
    const ctr = { k: c, n: fs.length, T: hT };
    cs.push(ctr);
    book.ctrs[c] = ctr;
  }
  parse_close(p, n0);
  book.order.push(k);
}

export function parse_book(src: string, book: Book = book_nil(), ns: string = "", bs: Bool = false, dir: string = ""): Book {
  const p = parse_new(src, book, ns, bs, dir);
  book.halts = book.halts || src.split("\n", 1)[0].trim() === "#[halts]";
  while (true) {
    parse_skip(p);
    if (p.loc.pos >= p.str.length) {
      return book;
    }
    if (parse_at_word(p, "def")) {
      parse_def(p, book);
      continue;
    }
    if (parse_at_word(p, "type")) {
      parse_adt(p, book);
      continue;
    }
    if (parse_at_word(p, "assert")) {
      parse_assert(p, book);
      continue;
    }
    parse_fail(p, "'def', 'type' or 'assert'");
  }
}

// Import
// ------

export function book_load(book: Book, file: string, ns: string, seen: Map<string, string | null>, root: boolean = true): void {
  const real = fs.realpathSync(file);
  const done = seen.get(real);
  if (done === null) {
    throw Err(book, ctx_nil(), "an acyclic import graph (a cycle reaches " + file + ")");
  }
  if (done !== undefined) {
    if (done !== ns) {
      throw Err(book, ctx_nil(), "one namespace per file (" + file + " is both '" + done + "' and '" + ns + "')");
    }
    return;
  }
  seen.set(real, null);
  const dir   = file.slice(0, file.lastIndexOf("/") + 1);
  const lines = fs.readFileSync(file, "utf8").split("\n");
  if ((lines[0] ?? "").trim() === "#[halts]") {
    if (root) {
      book.halts = true;
    } else if (!book.halts) {
      throw Err(book, ctx_nil(), "a #[halts] opt-in at the root (" + file + " declares #[halts]; add #[halts] to the entry file to accept it)");
    }
  }
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i].trim();
    const m = line.match(/^import(\s.*|)$/);
    if (m !== null) {
      const h = m[1].match(/^\s+(\S+)(?:\s+as\s+([A-Za-z_][A-Za-z0-9_]*))?\s*(?:#.*)?$/);
      if (h === null || (h[2] === undefined && h[1] !== "Base")) {
        throw Err(book, ctx_nil(), "an import ('import Base', or 'import <path> as <Name>')");
      }
      if (h[2] === undefined) {
        book_load(book, fileURLToPath(new URL("./base.bend", import.meta.url)), "", seen, false);
      } else {
        book_load(book, h[1].startsWith("/") ? h[1] : dir + h[1], h[2], seen, false);
      }
      lines[i] = "";
      continue;
    }
    if (line !== "" && !line.startsWith("#")) {
      break;
    }
  }
  BASE_BEND ??= fs.realpathSync(fileURLToPath(new URL("./base.bend", import.meta.url)));
  parse_book(lines.join("\n"), book, ns, real === BASE_BEND, dir);
  seen.set(real, ns);
}

let BASE_BEND: string | null = null;

// Flatten
// =======
// https://gist.github.com/VictorTaelin/82264b517a1ab7d2ffe17f13deba9c68
// match_flatten compiles nested ctr/var patterns into a tree of lambda-
// matches and binders: first row wins, uncovered cases become \{}; guards,
// literals, or/as and column heuristics are out by design. binders are
// identities and ctrs structural, so substitution cannot capture; a ctr
// row makes its column strict even under an earlier catch-all. scus (the
// vars, duplicate-free, in order, one pattern each) is the precondition.
// a framed match meets it by construction: its cells' fresh binders are
// the scus, and its leaf binds each cell as a sequential annotated let
// and returns the tree annotated with the written telescope and applied
// to the cell variables, so a later cell's reference to an earlier one
// resolves to the cell, never past it. a computed scrutinee takes
// one internal binder and the same flatten, and its leaf returns the
// bare tree applied to the value; the derived check-app-mat rule closes
// it against the ambient goal.

export function term_cell(t: LTerm): Cell {
  if (t.$ === "Var") {
    return { $: "Cell", k: t.k, i: t.i, A: null, v: t, s: t.s };
  } else {
    return { $: "Cell", k: "_", i: 0, A: null, v: t, s: t.s };
  }
}

export function body_sub(b: Body, i: number, v: LTerm): Body {
  function scrut(e: LTerm): LTerm {
    if (e.$ === "Var") {
      return e.i === i ? v : e;
    } else {
      return Sub(i, v, e);
    }
  }
  switch (b.$) {
    case "Match": {
      const es = b.e.map((c): Cell => ({ $: "Cell", k: c.k, i: c.i, A: c.A === null ? null : Sub(i, v, c.A), v: scrut(c.v), s: c.s }));
      const rs = b.r.map((row): Case => ({ $: "Case", p: row.p, f: body_sub(row.f, i, v) }));
      const P  = b.P === null ? null : Sub(i, v, b.P);
      return { $: "Match", e: es, P, r: rs, s: b.s };
    }
    case "Local": {
      const w = scrut(b.v);
      const f = body_sub(b.f, i, v);
      return { $: "Local", k: b.k, q: b.q, v: w, f };
    }
    case "Reply": {
      const x = Sub(i, v, b.x);
      return { $: "Reply", x, s: b.s };
    }
  }
}

export function match_flatten(m: Match, vars: PVar[], d: number): LTerm {
  if (m.e.length > 0 && m.e[0].A !== null) {
    const xs = m.e.map((c): PVar => ({ $: "PVar", k: c.k, i: c.i, s: c.s }));
    const t  = match_flatten({ $: "Match", e: xs.map((q) => term_cell(patt_term(q))), P: null, r: m.r, s: m.s }, xs, d);
    const T  = tele_bind(m.e.map((c): [Quant, Name, number, LTerm] => [Lone(), c.k, c.i, c.A as LTerm]), m.P as LTerm);
    let x: LTerm = Ann(t, T, m.s);
    for (const c of m.e) {
      x = App(x, Var(c.k, c.i, c.s), m.s);
    }
    for (let j = m.e.length - 1; j >= 0; j--) {
      const c = m.e[j];
      x = Let(c.k, c.i, Ann(c.v, c.A as LTerm, c.s), x, c.s, Lone());
    }
    const f = body_flatten({ $: "Reply", x, s: m.s }, vars, d);
    return f;
  }
  if (m.e.length === 0 && m.r.length > 0) {
    const t = body_flatten(m.r[0].f, vars, d);
    return t;
  } else if (m.e.length === 0) {
    throw Err(book_nil(), ctx_nil(), "a case (this match has no row to return)", undefined, m.s);
  } else if (vars.length === 0) {
    let e = m.e[0].v;
    while (e.$ === "Sub") {
      e = e.f;
    }
    switch (e.$) {
      case "Var": {
        throw Err(book_nil(), ctx_nil(), "match scrutinees in binder order (this variable is unbound, consumed, or out of order: reorder the match)", undefined, e.s);
      }
      case "Ctr": {
        throw Err(book_nil(), ctx_nil(), "an undestructed scrutinee (this value is already a constructor: bind its fields directly; if an outer match destructed it, fold the pattern into the outer case)", undefined, m.s);
      }
      default: {
        const x: PVar = { $: "PVar", k: m.e[0].k, i: d, s: m.e[0].s };
        const xe = [term_cell(patt_term(x))].concat(m.e.slice(1));
        const t  = match_flatten({ $: "Match", e: xe, P: null, r: m.r, s: m.s }, [x], d + 1);
        return App(t, m.e[0].v, m.s);
      }
    }
  } else {
    const x   = vars[0];
    const scu = m.e[0].v;
    if (scu.$ === "Var" && scu.i === x.i) {
      if (m.r.length === 0) {
        return Efq(m.s);
      } else {
        const c = rows_find_ctr(m.r);
        if (c === null) {
          const rs = rows_bind_var(m.r, x);
          const t  = match_flatten({ $: "Match", e: m.e.slice(1), P: null, r: rs, s: m.s }, vars, d);
          return t;
        } else {
          const xs = patt_binds(c.x, d);
          const ps = rows_pick_ctr(m.r, x, c.k, xs);
          const pe = xs.map((q) => term_cell(patt_term(q))).concat(m.e.slice(1));
          const pv = xs.concat(vars.slice(1));
          const pt = match_flatten({ $: "Match", e: pe, P: null, r: ps, s: m.s }, pv, d + xs.length);
          const ds = rows_drop_ctr(m.r, c.k);
          const dt = match_flatten({ $: "Match", e: m.e, P: null, r: ds, s: m.s }, vars, d);
          return Mat(c.k, pt, dt, c.s);
        }
      }
    } else {
      const t = match_flatten(m, vars.slice(1), d);
      return Lam(x.k, x.i, t, x.s);
    }
  }
}

export function rows_pick_ctr(rows: Rows, x: PVar, k: Name, xs: Patt[]): Rows {
  return rows.flatMap((row): Rows => {
    const p0 = row.p[0];
    switch (p0.$) {
      case "PCtr": {
        if (p0.k !== k) {
          return [];
        } else if (p0.x.length !== xs.length) {
          throw Err(book_nil(), ctx_nil(), "a " + k + " pattern with " + String(xs.length) + " fields", undefined, p0.s);
        } else {
          const f = body_sub(row.f, x.i, patt_term(p0));
          return [{ $: "Case", p: p0.x.concat(row.p.slice(1)), f }];
        }
      }
      case "PVar": {
        const g = body_sub(row.f, p0.i, patt_term(x));
        const f = body_sub(g, x.i, patt_term({ $: "PCtr", k, x: xs }));
        return [{ $: "Case", p: xs.concat(row.p.slice(1)), f }];
      }
    }
  });
}

export function rows_drop_ctr(rows: Rows, k: Name): Rows {
  return rows.filter((row) => {
    const p0 = row.p[0];
    if (p0.$ === "PCtr") {
      return p0.k !== k;
    } else {
      return true;
    }
  });
}

export function rows_bind_var(rows: Rows, x: PVar): Rows {
  return rows.map((row): Case => {
    const p0 = row.p[0];
    if (p0.$ === "PVar") {
      const f = body_sub(row.f, p0.i, patt_term(x));
      return { $: "Case", p: row.p.slice(1), f };
    } else {
      throw Err(book_nil(), ctx_nil(), "a variable pattern (this column has no constructor row)", undefined, p0.s);
    }
  });
}

export function rows_find_ctr(rows: Rows): PCtr | null {
  if (rows.length === 0) {
    return null;
  } else {
    const p0 = rows[0].p[0];
    if (p0.$ === "PCtr") {
      return p0;
    } else {
      const c = rows_find_ctr(rows.slice(1));
      return c;
    }
  }
}

export function patt_binds(qs: Patt[], d: number): PVar[] {
  return qs.map((q, j): PVar => {
    if (q.$ === "PVar") {
      return q;
    } else {
      return { $: "PVar", k: "_" + String(d + j), i: d + j, s: q.s };
    }
  });
}

export function patt_term(q: Patt): LTerm {
  switch (q.$) {
    case "PVar": {
      return Var(q.k, q.i, q.s);
    }
    case "PCtr": {
      const xs = q.x.map(patt_term);
      return Ctr(q.k, xs, q.s);
    }
  }
}

export function body_flatten(b: Body, vars: PVar[], d: number): LTerm {
  switch (b.$) {
    case "Reply": {
      if (vars.length === 0) {
        return b.x;
      } else {
        const v = vars[0];
        const f = body_flatten(b, vars.slice(1), d);
        return Lam(v.k, v.i, f, v.s);
      }
    }
    case "Local": {
      const w = b.k;
      switch (w.$) {
        case "PVar": {
          const f = body_flatten(b.f, [w], d);
          const g = f.$ === "Lam" ? f.f : App(f, Var(w.k, w.i, w.s), b.v.s);
          const x = Let(w.k, w.i, b.v, g, w.s, b.q);
          const t = body_flatten({ $: "Reply", x }, vars, d);
          return t;
        }
        case "PCtr": {
          const r: Case = { $: "Case", p: [w], f: b.f };
          const t = match_flatten({ $: "Match", e: [term_cell(b.v)], P: null, r: [r], s: b.v.s }, vars, d);
          return t;
        }
      }
    }
    case "Match": {
      const t = match_flatten(b, vars, d);
      return t;
    }
  }
}

// WNF
// ===
// term_wnf gives weak head normal form: sound, weak (arguments, fields,
// arms raw), idempotent, partial exactly on terms with no whnf. a
// saturated def unfolds raw, a stuck one returns its ref applied, an
// underapplied one stays. a family Ref never unfolds: a nullary one
// steps to its canonical ADT node, a parameterized one is stuck (the
// one spelling is D<..>, and infer-ref rejects a bare family head).
// substitutions and demanded match fields bind memoized thunks, so
// shared work runs once; a var steps into its let value; tree nodes
// inside a leaf are plain values. a rewrite demands its evidence and
// steps to its body on {==}, else sticks as a value.

export function term_wnf(book: Book, term: HTerm): HTerm {
  const frs: Frame[] = [];
  let tm: HTerm = term;
  let lhs: LHS | null = null;
  main: while (true) {
    focus: switch (tm.$) {
      case "Var": {
        if (tm.v === undefined) {
          break focus;
        } else {
          lhs = null;
          tm = tm.v;
          continue main;
        }
      }
      case "Laz": {
        lhs = null;
        if (tm.x === undefined) {
          tm = term_force(tm);
        } else {
          frs.push({ $: "LAZ", l: tm });
          tm = tm.x;
        }
        continue main;
      }
      case "Ann": {
        tm = tm.x;
        continue main;
      }
      case "Let": {
        const v = tm.v;
        tm = tm.f(Laz(() => term_wnf(book, v), undefined, v));
        continue main;
      }
      case "App": {
        const x = tm.x;
        frs.push({ $: "APP", x: x.$ === "Laz" ? x : Laz(() => term_wnf(book, x), undefined, x) });
        if (lhs !== null) {
          const t0: HTerm = lhs.t;
          const t: HTerm = Lam("_", 0, (_x: HTerm) => { return t0; });
          lhs = { t, n: lhs.n + 1, def: lhs.def, qs: lhs.qs };
        }
        tm = tm.f;
        continue main;
      }
      case "Lam": {
        if (frs.length === 0 || frs[frs.length - 1].$ !== "APP") {
          break focus;
        } else {
          const fr = frs.pop() as Extract<Frame, { $: "APP" }>;
          if (lhs !== null) {
            lhs = lhs.n === 0 ? null : { t: term_apply(lhs.t, fr.x), n: lhs.n - 1, def: lhs.def, qs: lhs.qs };
          }
          tm = tm.f(fr.x);
          continue main;
        }
      }
      case "Mat": {
        if (frs.length === 0 || frs[frs.length - 1].$ !== "APP") {
          break focus;
        } else {
          const fr = frs.pop() as Extract<Frame, { $: "APP" }>;
          frs.push({ $: "MAT", t: tm, e: fr.x, lhs });
          tm = fr.x;
          lhs = null;
          continue main;
        }
      }
      case "Efq": {
        if (lhs !== null && frs.length > 0 && frs[frs.length - 1].$ === "APP") {
          tm = lhs.t;
        }
        break focus;
      }
      case "Rwt": {
        const e = term_wnf(book, tm.e);
        if (e.$ === "Rfl") {
          tm = tm.f;
          continue main;
        }
        break focus;
      }
      case "Ref": {
        const tld = book.tlds[tm.k];
        if (tld === undefined) {
          break focus;
        }
        if (tld.$ === "ADT") {
          if (tld.n === 0) {
            tm = ADT(tm.k, [], tm.s);
          }
          break focus;
        }
        let run = 0;
        while (run < tld.n && run < frs.length && frs[frs.length - 1 - run].$ === "APP") {
          run += 1;
        }
        if (run < tld.n || tld.v === null) {
          break focus;
        }
        lhs = { t: tm, n: tld.n, def: tm.k, qs: [] };
        tm = tld.v;
        continue main;
      }
      default: {
        break focus;
      }
    }
    lhs = null;
    back: while (true) {
      const fr = frs.pop();
      if (fr === undefined) {
        return tm;
      } else {
        switch (fr.$) {
          case "LAZ": {
            const v = tm;
            fr.l.f = () => v;
            fr.l.x = undefined;
            continue main;
          }
          case "APP": {
            tm = term_apply(tm, fr.x);
            continue back;
          }
          case "MAT": {
            if (tm.$ === "Ctr") {
              const ctr = tm;
              let t: HTerm = fr.t;
              walk: while (true) {
                switch (t.$) {
                  case "Ann": {
                    t = t.x;
                    continue walk;
                  }
                  case "Laz": {
                    t = term_force(t);
                    continue walk;
                  }
                  case "Mat": {
                    if (t.k === ctr.k) {
                      if (fr.lhs === null) {
                        lhs = null;
                      } else {
                        lhs = { t: lhs_ext(fr.lhs.t, ctr.k, ctr.x.length), n: fr.lhs.n - 1 + ctr.x.length, def: fr.lhs.def, qs: fr.lhs.qs };
                      }
                      for (let j = ctr.x.length - 1; j >= 0; j--) {
                        const x = ctr.x[j];
                        if (x.$ !== "Laz") {
                          ctr.x[j] = Laz(() => term_wnf(book, x), undefined, x);
                        }
                        frs.push({ $: "APP", x: ctr.x[j] });
                      }
                      tm = t.h;
                      continue main;
                    } else {
                      t = t.m;
                      continue walk;
                    }
                  }
                  case "Efq": {
                    tm = term_apply(fr.lhs === null ? fr.t : fr.lhs.t, fr.e);
                    continue back;
                  }
                  default: {
                    lhs = fr.lhs;
                    frs.push({ $: "APP", x: ctr });
                    tm = t;
                    continue main;
                  }
                }
              }
            } else {
              tm = term_apply(fr.lhs === null ? fr.t : fr.lhs.t, fr.e);
              continue back;
            }
          }
        }
      }
    }
  }
}

export function term_uncop(book: Book, term: HTerm): HTerm {
  let tm = term_wnf(book, term);
  while (tm.$ === "Cop") {
    tm = term_wnf(book, tm.T);
  }
  return tm;
}

// SNF
// ===

export function term_snf(book: Book, term: HTerm): HTerm {
  function* go(t0: HTerm): Generator<HTerm, HTerm, HTerm> {
    let tm = term_wnf(book, t0);
    while (tm.$ === "Laz") {
      tm = term_wnf(book, term_force(tm));
    }
    switch (tm.$) {
      case "Var": {
        return Var(tm.k, tm.i, tm.s);
      }
      case "Ref": {
        return Ref(tm.k, tm.s, tm.b);
      }
      case "Sub": {
        return Sub(tm.i, yield tm.v, yield tm.f, tm.s);
      }
      case "Let": {
        const b = tm;
        return Let(b.k, b.i, yield b.v, (x: HTerm) => {
          return term_snf(book, b.f(x));
        }, b.s, b.q);
      }
      case "Typ": {
        return Typ(tm.s);
      }
      case "All": {
        const b = tm;
        return All(b.q, b.k, b.i, yield b.A, (x: HTerm) => {
          return term_snf(book, b.B(x));
        }, b.s);
      }
      case "Lam": {
        const b = tm;
        return Lam(b.k, b.i, (x: HTerm) => {
          return term_snf(book, b.f(x));
        }, b.s);
      }
      case "App": {
        return App(yield tm.f, yield tm.x, tm.s);
      }
      case "ADT": {
        const xs: HTerm[] = [];
        for (const x of tm.x) {
          xs.push(yield x);
        }
        return ADT(tm.k, xs, tm.s, tm.r);
      }
      case "Ctr": {
        const xs: HTerm[] = [];
        for (const x of tm.x) {
          xs.push(yield x);
        }
        return Ctr(tm.k, xs, tm.s);
      }
      case "Mat": {
        return Mat(tm.k, yield tm.h, yield tm.m, tm.s);
      }
      case "Efq": {
        return Efq(tm.s);
      }
      case "Eql": {
        return Eql(yield tm.a, yield tm.b, yield tm.T, tm.s);
      }
      case "Rfl": {
        return Rfl(tm.s);
      }
      case "Rwt": {
        return Rwt(yield tm.e, yield tm.p, yield tm.f, tm.s);
      }
      case "Cop": {
        return Cop(yield tm.T, yield tm.c, tm.s);
      }
      case "Ann": {
        return Ann(yield tm.x, yield tm.T, tm.s);
      }
    }
  }
  return loop_run(go, term);
}

// Equal
// =====

export function term_equal(book: Book, lhs: HTerm, rhs: HTerm, dep: number = 0): boolean {
  if (lhs === rhs) {
    return true;
  }
  const a = term_wnf(book, lhs);
  const b = term_wnf(book, rhs);
  if (a === b) {
    return true;
  }
  if (a.$ === "Cop" || b.$ === "Cop") {
    return term_equal(book, a.$ === "Cop" ? a.T : a, b.$ === "Cop" ? b.T : b, dep);
  }
  if (a.$ === "Lam" || b.$ === "Lam") {
    const k = a.$ === "Lam" ? a.k : (b as Extract<HTerm, { $: "Lam" }>).k;
    const x: HTerm = Var(k, dep);
    const eq = term_equal(book, term_apply(a, x), term_apply(b, x), dep + 1);
    return eq;
  }
  switch (a.$) {
    case "Var": {
      if (b.$ === "Var") {
        return a.i === b.i;
      } else {
        return false;
      }
    }
    case "Ref": {
      if (b.$ === "Ref") {
        return a.k === b.k;
      } else {
        return false;
      }
    }
    case "Typ": {
      return b.$ === "Typ";
    }
    case "All": {
      if (b.$ === "All" && a.q.$ === b.q.$) {
        const x: HTerm = Var(a.k, dep);
        return term_equal(book, a.A, b.A, dep)
            && term_equal(book, a.B(x), b.B(x), dep + 1);
      } else {
        return false;
      }
    }
    case "App": {
      if (b.$ === "App") {
        return term_equal(book, a.f, b.f, dep)
            && term_equal(book, a.x, b.x, dep);
      } else {
        return false;
      }
    }
    case "ADT": {
      if (b.$ === "ADT" && a.k === b.k && a.x.length === b.x.length) {
        let eq = true;
        for (let j = 0; j < a.x.length; j++) {
          eq = eq && term_equal(book, a.x[j], b.x[j], dep);
        }
        return eq;
      } else {
        return false;
      }
    }
    case "Ctr": {
      if (b.$ === "Ctr" && a.k === b.k && a.x.length === b.x.length) {
        let eq = true;
        for (let j = 0; j < a.x.length; j++) {
          eq = eq && term_equal(book, a.x[j], b.x[j], dep);
        }
        return eq;
      } else {
        return false;
      }
    }
    case "Mat": {
      if (b.$ === "Mat" && a.k === b.k) {
        return term_equal(book, a.h, b.h, dep)
            && term_equal(book, a.m, b.m, dep);
      } else {
        return false;
      }
    }
    case "Efq": {
      return b.$ === "Efq";
    }
    case "Eql": {
      if (b.$ === "Eql") {
        return term_equal(book, a.a, b.a, dep)
            && term_equal(book, a.b, b.b, dep)
            && term_equal(book, a.T, b.T, dep);
      } else {
        return false;
      }
    }
    case "Rfl": {
      return b.$ === "Rfl";
    }
    case "Rwt": {
      if (b.$ === "Rwt") {
        return term_equal(book, a.e, b.e, dep)
            && term_equal(book, a.p, b.p, dep)
            && term_equal(book, a.f, b.f, dep);
      } else {
        return false;
      }
    }
    default: {
      return false;
    }
  }
}

// Check
// =====
// one bidirectional pass. qt is the demand: None checks dead, Lone live;
// there is no third demand, since nothing licenses a second live use. us
// is the measured usage: a binder validates measured <= declared on close,
// and a Lone binder measured Many (consumed more than once) fails there.
// a dead check measures only None, so a rule drops the measure of a
// premise it itself checks dead; only demanded premises add.
// ordinary typing never consults the usage measure: resource accounting
// rides alongside the type judgment, it does not steer it. a checked term
// returns Ann-wrapped, lazily re-checking bodies, for a compiler that does
// not exist yet; goals always compute on source terms. lhs is the def's
// own equation, rebuilt as the tree walks; lhs.qs holds the def's
// parameter quantities, read off its type once, so descent can skip
// erased columns.

export type HAnn  = Extract<HTerm, { $: "Ann" }>;
export type Infer = { tm: HTerm; us: Uses };
export type Check = { tm: HTerm; us: Uses };

// A == Copiable(_)
// Γ ⊢ c :& A ~ u
// where every use in u is a live binder or an erased Copiable one
// --------------------------------------------------------- cop-wit
// Γ ⊢ c :- A ~ {}

export function cop_goal(book: Book, A: HTerm, d: number): boolean {
  const a = term_uncop(book, A);
  if (a.$ === "All") {
    return term_equal(book, A, App(Ref("Copiable"), a.A), d);
  }
  const [h] = term_unapply(a);
  return h.$ === "Ref" && h.k === "Copiable";
}

export function cop_wit(book: Book, lhs: LHS | null, tm: HTerm, ty: HTerm, ctx: Ctx, d: number): Check {
  const def = lhs === null ? undefined : lhs.def;
  const chk = term_check(book, lhs, tm, Lone(), ty, ctx, d);
  for (const [i, q] of pmap_to_array(chk.us)) {
    if (q.$ === "None") {
      continue;
    }
    const ann = pmap_get(ctx, i);
    if (ann === null) {
      throw Err(book, ctx, "unreachable (a metered use names a bound variable)", undefined, tm.s, def);
    }
    if (ann.q.$ === "None" && !cop_goal(book, ann.T, d)) {
      throw Err(book, ctx, "a grounded Cop witness (a dead hypothesis cannot license contraction)", Var(ann.k, i), tm.s, def);
    }
  }
  return { tm: chk.tm, us: uses_nil() };
}

export function term_infer(book: Book, lhs: LHS | null, tm: HTerm, qt: Quant, ctx: Ctx, d: number): Infer {
  const def = lhs === null ? undefined : lhs.def;
  switch (tm.$) {
    // Γ[x] = q A
    // ----------------- infer-var
    // Γ ⊢ x : A ~ {x:q}
    case "Var": {
      const ann = pmap_get(ctx, tm.i);
      if (ann === null) {
        throw Err(book, ctx, "a bound variable", tm, tm.s, def);
      } else {
        var us = uses_one(tm.i, qt);
        var tm = Ann(tm, ann.T);
        return { tm, us };
      }
    }
    // Book(k) : T
    // where k is not the lhs head in a live region
    //       (a live self-call enters whole, through infer-app)
    //       k has a body in a live region, unless base declared it
    //       (an unfilled assert is a dead claim; base's are native)
    //       k is not a parameterized family: D<..> is the one
    //       spelling, a bare family head is an error
    // -------------------------------------------------------- infer-ref
    // Γ ⊢ k : T ~ {}
    case "Ref": {
      const tld = book.tlds[tm.k];
      if (tld === undefined) {
        throw Err(book, ctx, "a defined name", tm, tm.s, def);
      }
      if (qt.$ !== "None" && tm.k === def && !book.halts) {
        throw Err(book, ctx, "a whole, decreasing self-call (a live self-reference cannot escape as a value)", tm, tm.s, def);
      }
      if (qt.$ !== "None" && tld.$ === "Def" && tld.v === null && tld.b !== true && !tld.i && !book.halts) {
        throw Err(book, ctx, "a filled definition (an unfilled assert is a dead claim: live code cannot use it)", tm, tm.s, def);
      }
      if (tld.$ === "ADT" && tld.n > 0) {
        throw Err(book, ctx, "a family instance (write " + tm.k + "<..>)", tm, tm.s, def);
      }
      const T: HTerm = tld.$ === "ADT" ? Typ(tm.s) : tld.T;
      var tm = Ann(tm, T);
      var us = uses_nil();
      return { tm, us };
    }
    // ∅
    // --------------- infer-typ
    // Γ ⊢ Type : Type
    case "Typ": {
      var tm = Ann<HBody>(tm, Typ(tm.s));
      var us = uses_nil();
      return { tm, us };
    }
    // Γ ⊢ A : Type
    // Γ , x : qA ⊢ B(x) : Type
    // where a + binder's A is a Cop, outside #[halts]
    // ----------------------------------------------- infer-all
    // Γ ⊢ @q x:A -> B : Type
    case "All": {
      const b = tm;
      const B_ctx = ctx_bind(ctx, d, tm.q, tm.k, tm.A);
      const A_chk = term_check(book, lhs, tm.A, None(), Typ(tm.s), ctx, d);
      if (!quant_valid(book, tm.q, tm.A)) {
        throw Err(book, ctx, "a copiable type (a + binder needs a + T ~ C type, or #[halts])", tm, tm.s, def);
      }
      term_check(book, lhs, tm.B(Var(tm.k, d)), None(), Typ(tm.s), B_ctx, d+1);
      var tm = All(b.q, b.k, b.i, A_chk.tm, (y: HTerm) => Laz(() => term_check(book, lhs, b.B(y), None(), Typ(), B_ctx, d+1).tm), b.s);
      var tm = Ann(tm, Typ(tm.s));
      var us = uses_nil();
      return { tm, us };
    }
    // Γ ⊢ f : @q x:A -> B ~ fu
    // Γ ⊢ a : A ~ au
    // where a is dead if q is -, and consumed exactly once otherwise
    //       (an argument is never scaled: v1 has no multiplication)
    //       a family head is not a function: infer-ref rejects it,
    //       so D(x) is an error and D<x> the one spelling
    //       a live lhs-headed spine is whole (lhs.n = 0, one argument
    //       per column) and descends: live columns compare EQ left to
    //       right until one is LT; an erased (-) column is skipped
    //       the head is the bare Ref, syntactically: an Ann-wrapped
    //       head falls to infer-ref, which rejects
    // --------------------------------------------------------------- infer-app
    // Γ ⊢ f(a) : B(a) ~ fu + au
    case "App": {
      const [fun, arg] = term_unapply(tm);
      let f_inf: Infer;
      if (!book.halts && lhs !== null && qt.$ !== "None" && fun.$ === "Ref" && fun.k === def) {
        const tld = book.tlds[fun.k];
        if (tld === undefined) {
          throw Err(book, ctx, "a defined name", fun, tm.s, def);
        }
        const cols = term_unapply(lhs.t)[1];
        if (lhs.n !== 0 || arg.length < cols.length) {
          throw Err(book, ctx, "a whole self-call (one argument per parameter, inside the case tree)", tm, tm.s, def);
        }
        let ord: Cmp = "EQ";
        for (let j = 0; j < cols.length && ord === "EQ"; j++) {
          const q = lhs.qs[j];
          if (q !== undefined && q.$ === "None") {
            continue;
          }
          ord = term_compare(arg[j], cols[j]);
        }
        if (ord !== "LT") {
          throw Err(book, ctx, "a decreasing self-call (some live argument must shrink)", tm, tm.s, def);
        }
        f_inf = { tm: Ann(fun, tld.T), us: uses_nil() };
      } else {
        f_inf = term_infer(book, lhs, fun, qt, ctx, d);
      }
      for (const x of arg) {
        const f_ann = f_inf.tm as HAnn;
        const f_wnf = term_uncop(book, f_ann.T);
        if (f_wnf.$ !== "All") {
          throw Err(book, ctx, "a function type", f_ann.T, tm.s, def);
        }
        const f_dem = quant_dem(f_wnf.q, qt);
        const x_chk = term_check(book, lhs, x, f_dem, f_wnf.A, ctx, d);
        f_inf = { tm: Ann(App(f_inf.tm, x_chk.tm, tm.s), Laz(() => f_wnf.B(x))), us: uses_add(f_inf.us, x_chk.us) };
      }
      return f_inf;
    }
    // book[k].T = @q1 p1:K1 -> .. -> Type
    // Γ ⊢ xi : Ki ~ ui
    // where xi is dead if qi is -
    // ----------------------------------------- infer-adt
    // Γ ⊢ k<x1, .., xn> : Type ~ u1 + .. + un
    case "ADT": {
      const adt = book_adt(book, tm, ctx, def);
      if (tm.x.length !== adt.n) {
        throw Err(book, ctx, tm.k + " with " + String(adt.n) + (adt.n === 1 ? " parameter" : " parameters"), tm, tm.s, def);
      }
      const xs: HTerm[] = [];
      let tel: HTerm = adt.T;
      var us = uses_nil();
      for (const x of tm.x) {
        const t_all = tele_head(book, tel, ctx, def, tm.s);
        const t_dem = quant_dem(t_all.q, qt);
        const x_chk = term_check(book, lhs, x, t_dem, t_all.A, ctx, d);
        xs.push(x_chk.tm);
        us = uses_add(us, x_chk.us);
        tel = t_all.B(x);
      }
      var tm = Ann(ADT(tm.k, xs, tm.s, tm.r), Typ(tm.s));
      return { tm, us };
    }
    // Γ ⊢ A : Type    Γ ⊢ a : A    Γ ⊢ b : A
    // where A, a and b are dead
    // --------------------------------------- infer-eql
    // Γ ⊢ {a == b : A} : Type ~ {}
    case "Eql": {
      const T_chk = term_check(book, lhs, tm.T, None(), Typ(tm.s), ctx, d);
      const a_chk = term_check(book, lhs, tm.a, None(), tm.T, ctx, d);
      const b_chk = term_check(book, lhs, tm.b, None(), tm.T, ctx, d);
      var tm = Eql(a_chk.tm, b_chk.tm, T_chk.tm, tm.s);
      var tm = Ann(tm, Typ(tm.s));
      var us = uses_nil();
      return { tm, us };
    }
    // Γ ⊢ T : Type    Γ ⊢ c : Copiable(T)
    // where T and c are dead; + T ~ c converts with T
    // ----------------------------------------------- infer-cop
    // Γ ⊢ + T ~ c : Type ~ {}
    case "Cop": {
      const T_chk = term_check(book, lhs, tm.T, None(), Typ(tm.s), ctx, d);
      const c_chk = term_check(book, lhs, tm.c, None(), App(Ref("Copiable", tm.s), tm.T, tm.s), ctx, d);
      var tm = Ann(Cop(T_chk.tm, c_chk.tm, tm.s), Typ(tm.s));
      var us = uses_nil();
      return { tm, us };
    }
    // Γ ⊢ T : Type
    // Γ ⊢ x : T ~ u
    // where T is dead
    // ------------------- infer-ann
    // Γ ⊢ {x : T} : T ~ u
    case "Ann": {
      term_check(book, lhs, tm.T, None(), Typ(tm.s), ctx, d);
      const x_chk = term_check(book, lhs, tm.x, qt, tm.T, ctx, d);
      var tm = x_chk.tm;
      var us = x_chk.us;
      return { tm, us };
    }
    // Γ ⊢ force(x) : T ~ u
    // --------------------- infer-laz
    // Γ ⊢ x : T ~ u
    case "Laz": {
      const t = term_infer(book, lhs, term_force(tm), qt, ctx, d);
      return t;
    }
    // x is a Lam, Let, Ctr, Mat, Efq, Rfl or Rwt
    // ------------------------------------------- infer-err
    // Γ ⊢ x : ⊥ (a goal is needed)
    default: {
      if (tm.$ === "Ctr" && book_ctr(book, tm.k) === null) {
        throw Err(book, ctx, "a declared constructor", tm, tm.s, def);
      }
      throw Err(book, ctx, "an annotated term (cannot infer)", tm, tm.s, def);
    }
  }
}

export function term_check(book: Book, lhs: LHS | null, tm: HTerm, qt: Quant, ty: HTerm, ctx: Ctx, d: number): Check {
  const def = lhs === null ? undefined : lhs.def;
  if (qt.$ === "None" && !book.halts && cop_goal(book, ty, d)) {
    return cop_wit(book, lhs, tm, ty, ctx, d);
  }
  switch (tm.$) {
    // T == @q x:A -> B
    // Γ , x : qA ⊢ f(x) : B(x) ~ u
    // where u[x] <= q
    //       lhs steps by x while a parameter remains
    // ---------------------------------------------- check-lam
    // Γ ⊢ x => f : T ~ u - x
    case "Lam": {
      const b     = tm;
      const t_wnf = term_uncop(book, ty);
      if (t_wnf.$ !== "All") {
        throw Err(book, ctx, ty, tm, tm.s, def);
      }
      const x: HTerm = Var(tm.k, d);
      const f_lhs = (a: HTerm) => lhs !== null && lhs.n > 0 ? { t: term_apply(lhs.t, a), n: lhs.n - 1, def: lhs.def, qs: lhs.qs } : lhs;
      const f_ctx = ctx_bind(ctx, d, t_wnf.q, tm.k, t_wnf.A);
      const f_chk = term_check(book, f_lhs(x), tm.f(x), qt, t_wnf.B(x), f_ctx, d+1);
      const f_use = uses_get(f_chk.us, d);
      if (quant_join(f_use, t_wnf.q).$ !== t_wnf.q.$) {
        const obs = f_use.$ === "Many" ? tm.k + " (consumed more than once)" : quant_show(f_use) + tm.k;
        throw Err(book, ctx, quant_show(t_wnf.q) + tm.k, obs, tm.s, def);
      }
      var tm = Lam(b.k, b.i, (y: HTerm) => Laz(() => term_check(book, f_lhs(y), b.f(y), qt, t_wnf.B(y), f_ctx, d+1).tm), b.s);
      var tm = Ann(tm, ty);
      var us = uses_del(f_chk.us, d);
      return { tm, us };
    }
    // Γ ⊢ v : A ~ vu
    // Γ , x : qA ⊢ f(x) : T ~ fu
    // where a + binder's A is a Cop, outside #[halts]
    //       v is dead if q is -
    //       fu[x] <= q
    //       the elaborated let re-checks its body lazily; a bare
    //       opened variable takes the value back, so a forcer's
    //       probe cannot flip a verdict validation already passed
    // ----------------------------------------------- check-let
    // Γ ⊢ q x = v; f : T ~ vu + fu - x
    case "Let": {
      const b = tm;
      const v_dem = quant_dem(tm.q, qt);
      const v_inf = term_infer(book, lhs, tm.v, v_dem, ctx, d);
      const v_ann = v_inf.tm as HAnn;
      if (v_dem.$ === "None" && !book.halts && cop_goal(book, v_ann.T, d)) {
        cop_wit(book, lhs, tm.v, v_ann.T, ctx, d);
      }
      if (!quant_valid(book, tm.q, v_ann.T)) {
        throw Err(book, ctx, "a copiable type (a + binder needs a + T ~ C type, or #[halts])", tm, tm.s, def);
      }
      const x: HTerm = Var(tm.k, d, tm.s, tm.v);
      const f_ctx = ctx_bind(ctx, d, tm.q, tm.k, v_ann.T);
      const f_chk = term_check(book, lhs, tm.f(x), qt, ty, f_ctx, d+1);
      const f_use = uses_get(f_chk.us, d);
      if (quant_join(f_use, tm.q).$ !== tm.q.$) {
        const obs = f_use.$ === "Many" ? tm.k + " (consumed more than once)" : quant_show(f_use) + tm.k;
        throw Err(book, ctx, quant_show(tm.q) + tm.k, obs, tm.s, def);
      }
      const f_val = (y: HTerm): HTerm => y.$ === "Var" && y.v === undefined ? Var(y.k, y.i, y.s, b.v) : y;
      var tm = Let(b.k, b.i, v_inf.tm, (y: HTerm) => Laz(() => term_check(book, lhs, b.f(f_val(y)), qt, ty, f_ctx, d+1).tm), b.s, b.q);
      var tm = Ann(tm, (f_chk.tm as HAnn).T);
      var us = uses_add(v_inf.us, uses_del(f_chk.us, d));
      return { tm, us };
    }
    // T == D<p1, .., pm>
    // D.c[k] = @q1 x1:F1 -> .. -> D<p1, .., pm>
    // Γ ⊢ xi : Fi ~ ui
    // where xi is dead if qi is -
    // ------------------------------------------ check-ctr
    // Γ ⊢ k{x1, .., xn} : T ~ u1 + .. + un
    case "Ctr": {
      const t_wnf = term_uncop(book, ty);
      if (t_wnf.$ !== "ADT") {
        throw Err(book, ctx, ty, tm, tm.s, def);
      }
      const adt = book_adt(book, t_wnf, ctx, def);
      const ctr = ctrs_find(adt.c, tm.k);
      if (ctr === null) {
        if (book_ctr(book, tm.k) === null) {
          throw Err(book, ctx, "a declared constructor (" + t_wnf.k + " declares " + adt.c.map((c) => c.k).join(", ") + ")", tm, tm.s, def);
        }
        throw Err(book, ctx, ty, tm, tm.s, def);
      }
      if (tm.x.length !== ctr.n) {
        throw Err(book, ctx, tm.k + " with " + String(ctr.n) + (ctr.n === 1 ? " field" : " fields"), tm, tm.s, def);
      }
      let tel: HTerm = ctr.T;
      for (const p of t_wnf.x) {
        const p_all = tele_head(book, tel, ctx, def, tm.s);
        tel = p_all.B(p);
      }
      const xs: HTerm[] = [];
      var us = uses_nil();
      for (const x of tm.x) {
        const f_all = tele_head(book, tel, ctx, def, tm.s);
        const f_dem = quant_dem(f_all.q, qt);
        const x_chk = term_check(book, lhs, x, f_dem, f_all.A, ctx, d);
        xs.push(x_chk.tm);
        us  = uses_add(us, x_chk.us);
        tel = f_all.B(x);
      }
      var tm = Ann(Ctr(tm.k, xs, tm.s), ty);
      return { tm, us };
    }
    // T == @q s:D<p..> -> P
    // D.c[k] = @r1 x1:F1 -> .. -> D<p..>
    // Γ ⊢ h : @s1 x1:F1 -> .. -> P(k{x1, .., xn}) ~ hu
    // Γ ⊢ m : @q s:(D - k)<p..> -> P ~ mu
    // where q is not - in a live region
    //       si = - if ri is -, q otherwise
    //       h's lhs steps by k{x1, .., xn} while a parameter remains
    // -------------------------------------------------------------- check-mat
    // Γ ⊢ \ {k: h; m} : T ~ hu | mu
    case "Mat": {
      const b     = tm;
      const t_wnf = term_uncop(book, ty);
      if (t_wnf.$ !== "All") {
        throw Err(book, ctx, ty, tm, tm.s, def);
      }
      const t_all = t_wnf;
      if (qt.$ !== "None" && t_all.q.$ === "None") {
        throw Err(book, ctx, "a live scrutinee (a - scrutinee matches only in a dead region)", undefined, tm.s, def);
      }
      const a_wnf = term_uncop(book, t_all.A);
      if (a_wnf.$ !== "ADT") {
        throw Err(book, ctx, "a datatype", t_all.A, tm.s, def);
      }
      const rem = book_adt(book, a_wnf, ctx, def).c;
      const ctr = ctrs_find(rem, tm.k);
      if (ctr === null) {
        throw Err(book, ctx, "a constructor of " + a_wnf.k + " (missing, or already matched)", tm, tm.s, def);
      }
      let tel: HTerm = ctr.T;
      for (const p of a_wnf.x) {
        const p_all = tele_head(book, tel, ctx, def, tm.s);
        tel = p_all.B(p);
      }
      function term_check_mat_goal(cur: HTerm, n: number, xs: HTerm[]): HTerm {
        if (n === 0) {
          return t_all.B(Ctr(b.k, xs, b.s));
        } else {
          const c_all = tele_head(book, cur, ctx, def, b.s);
          const c_dem = quant_dem(c_all.q, t_all.q);
          return All(c_dem, c_all.k, c_all.i, c_all.A, (x: HTerm) => {
            return term_check_mat_goal(c_all.B(x), n - 1, xs.concat([x]));
          }, b.s);
        }
      }
      const h_lhs = lhs !== null && lhs.n > 0 ? { t: lhs_ext(lhs.t, tm.k, ctr.n), n: lhs.n - 1 + ctr.n, def: lhs.def, qs: lhs.qs } : lhs;
      const h_chk = term_check(book, h_lhs, tm.h, qt, term_check_mat_goal(tel, ctr.n, []), ctx, d);
      const m_gol = All(t_all.q, t_all.k, t_all.i, ADT(a_wnf.k, a_wnf.x, tm.s, a_wnf.r.concat([ctr.k])), t_all.B, tm.s);
      const m_chk = term_check(book, lhs, tm.m, qt, m_gol, ctx, d);
      var tm = Ann(Mat(tm.k, h_chk.tm, m_chk.tm, tm.s), ty);
      var us = uses_join(h_chk.us, m_chk.us);
      return { tm, us };
    }
    // T == @q s:D<p..> -> P    D.c = [] or live x:E ∈ Γ with E.c = []
    // where q is not - in a live region; a LIVE binder at an emptied
    //       ADT makes the region unreachable (a flattened match's
    //       default chain past its last constructor) - an erased one
    //       proves nothing, dead code inhabits it - so residue is dead
    // ------------------------------------------------------------- check-efq
    // Γ ⊢ \ {} : T ~ {}
    case "Efq": {
      const t_wnf = term_uncop(book, ty);
      if (t_wnf.$ !== "All") {
        throw Err(book, ctx, ty, tm, tm.s, def);
      }
      if (qt.$ !== "None" && t_wnf.q.$ === "None") {
        throw Err(book, ctx, "a live scrutinee (a - scrutinee matches only in a dead region)", undefined, tm.s, def);
      }
      const a_wnf = term_uncop(book, t_wnf.A);
      if (a_wnf.$ !== "ADT") {
        throw Err(book, ctx, "a datatype", t_wnf.A, tm.s, def);
      }
      const rem = book_adt(book, a_wnf, ctx, def).c;
      if (rem.length !== 0 && !ctx_dead(book, ctx)) {
        throw Err(book, ctx, "cases for " + rem.map((c) => c.k).join(", "), tm, tm.s, def);
      }
      var tm = Ann(tm, ty);
      var us = uses_nil();
      return { tm, us };
    }
    // T == {a == b : A}    a == b
    // ---------------------------- check-rfl
    // Γ ⊢ {==} : T ~ {}
    case "Rfl": {
      const t_wnf = term_uncop(book, ty);
      if (t_wnf.$ !== "Eql") {
        throw Err(book, ctx, ty, tm, tm.s, def);
      }
      if (!term_equal(book, t_wnf.a, t_wnf.b, d)) {
        throw Err(book, ctx, t_wnf.a, t_wnf.b, tm.s, def);
      }
      var tm = Ann(tm, ty);
      var us = uses_nil();
      return { tm, us };
    }
    // Γ ⊢ E : {a == b : A} ~ eu
    // Γ ⊢ P : @x:A -> @e:{a == x : A} -> Type    P(b, E) == T
    // Γ ⊢ f : P(a, {==}) ~ fu
    // where P is dead; this is the J axiom: elimination
    //       specializes both the equation and its second endpoint
    // ------------------------------------------------------------ check-rwt
    // Γ ⊢ %e@E : P; f : T ~ eu + fu
    case "Rwt": {
      const e_inf = term_infer(book, lhs, tm.e, qt, ctx, d);
      const e_ann = e_inf.tm as HAnn;
      const e_wnf = term_uncop(book, e_ann.T);
      if (e_wnf.$ !== "Eql") {
        throw Err(book, ctx, "an equation {a == b : T}", e_ann.T, tm.s, def);
      }
      const p_typ = All<HBody>(Lone(), "_", 0, e_wnf.T, (x: HTerm) => All<HBody>(Lone(), "e", 0, Eql(e_wnf.a, x, e_wnf.T), () => Typ(), tm.s), tm.s);
      const p_chk = term_check(book, lhs, tm.p, None(), p_typ, ctx, d);
      const b_gol = term_apply(term_apply(tm.p, e_wnf.b), tm.e);
      if (!term_equal(book, b_gol, ty, d)) {
        throw Err(book, ctx, ty, b_gol, tm.s, def);
      }
      const a_gol = term_apply(term_apply(tm.p, e_wnf.a), Rfl<HBody>(tm.s));
      const f_chk = term_check(book, lhs, tm.f, qt, a_gol, ctx, d);
      var tm = Ann(Rwt(e_inf.tm, p_chk.tm, f_chk.tm, tm.s), ty);
      var us = uses_add(e_inf.us, f_chk.us);
      return { tm, us };
    }
    // Γ ⊢ vi : Ai ~ vui
    // Γ ⊢ \{..} : @_:A1 -> .. -> @_:An -> T ~ mu
    // where the head is a bare Mat or Efq (an annotated head
    //       goes through infer-app)
    //       the motive is the ambient goal, constant
    // --------------------------------------------------- check-app-mat (derived)
    // Γ ⊢ (\{..})(v1, .., vn) : T ~ mu + vu1 + .. + vun
    case "App": {
      const [fun, arg] = term_unapply(tm);
      if (fun.$ !== "Mat" && fun.$ !== "Efq") {
        break;
      }
      const xs = arg.map((x) => term_infer(book, lhs, x, qt, ctx, d));
      const gls: HTerm[] = [];
      let gol: HTerm = ty;
      for (let j = xs.length - 1; j >= 0; j--) {
        gls.push(gol);
        const A = (xs[j].tm as HAnn).T;
        const B = gol;
        gol = All<HBody>(Lone(), "_", 0, A, () => B, tm.s);
      }
      const f_chk = term_check(book, lhs, fun, qt, gol, ctx, d);
      var us = f_chk.us;
      let ap: HTerm = f_chk.tm;
      for (let j = 0; j < xs.length; j++) {
        ap = Ann(App(ap, xs[j].tm, tm.s), gls[xs.length - 1 - j]);
        us = uses_add(us, xs[j].us);
      }
      var tm = ap;
      return { tm, us };
    }
    // Γ ⊢ force(x) : T ~ u
    // --------------------- check-laz
    // Γ ⊢ x : T ~ u
    case "Laz": {
      const t = term_check(book, lhs, term_force(tm), qt, ty, ctx, d);
      return t;
    }
    // Γ ⊢ x : A ~ u    A == T
    // --------------------------- check-any
    // Γ ⊢ x : T ~ u
    default: {
      break;
    }
  }
  const x_inf = term_infer(book, lhs, tm, qt, ctx, d);
  const x_ann = x_inf.tm as HAnn;
  if (term_equal(book, x_ann.T, ty, d)) {
    var tm = Ann(x_ann.x, ty);
    var us = x_inf.us;
    return { tm, us };
  }
  throw Err(book, ctx, ty, x_ann.T, tm.s, def);
}

// Valid
// =====
// book_valid throws the first Err; an order entry is an event: an
// asserted name declares (bodiless, type checked) at its assert and
// defines at its fill, so it is visible and stuck between the two and
// unfolds after; a plain def or ADT does both at once. each event checks
// against the book so far, so a forward reference fails as undefined,
// and a live reference to a bodiless def errs (infer-ref), so mutual
// recursion cannot bypass the wall. a def is declared, body null, until
// its check passes: an unchecked body never unfolds, a declared ref is
// stuck. a def checks its type against Type, then its tree against it,
// entering with { t: Ref k, n: Def.n, qs: the parameter quantities read
// off T }; an ADT checks its signature against Type, then every
// constructor telescope (parameters, then fields) domain by domain
// against Type, and requires the tip to be the family applied to its
// own parameters, in order. one telescope per declaration: there is no
// second face and no speculative pass.

export function adt_valid(book: Book, k: Name, adt: ADT): void {
  term_check(book, null, adt.T, None(), Typ(), ctx_nil(), 0);
  for (const ctr of adt.c) {
    let tel: HTerm = ctr.T;
    let ctx = ctx_nil();
    for (let d = 0; d < adt.n + ctr.n; d++) {
      const t_all = tele_head(book, tel, ctx, ctr.k);
      const A_chk = term_check(book, null, t_all.A, None(), Typ(), ctx, d);
      if (!quant_valid(book, t_all.q, t_all.A)) {
        throw Err(book, ctx, "a copiable type (a + binder needs a + T ~ C type, or #[halts])", undefined, undefined, ctr.k);
      }
      const A_srt = term_wnf(book, (A_chk.tm as HAnn).T);
      if (A_srt.$ !== "Typ") {
        throw Err(book, ctx, Typ<HBody>(), t_all.A, undefined, ctr.k);
      }
      ctx = ctx_bind(ctx, d, t_all.q, t_all.k, t_all.A);
      tel = t_all.B(Var(t_all.k, d));
    }
    const exp = "a telescope tipped at " + k + " applied to its own parameters";
    const tip = term_wnf(book, tel);
    if (tip.$ !== "ADT" || tip.k !== k || tip.x.length !== adt.n || tip.r.length !== 0) {
      throw Err(book, ctx, exp, tip, undefined, ctr.k);
    }
    for (let d = 0; d < adt.n; d++) {
      const x = term_wnf(book, tip.x[d]);
      if (x.$ !== "Var" || x.i !== d) {
        throw Err(book, ctx, exp, tip, undefined, ctr.k);
      }
    }
  }
}

export function def_valid(book: Book, k: Name, def: Def): void {
  term_check(book, null, def.T, None(), Typ(), ctx_nil(), 0);
  if (def.i) {
    let tel = term_strip(def.T);
    while (tel.$ === "All") {
      tel = term_strip(tel.B(tel.A));
    }
    const [h] = term_unapply(tel);
    const io  = book.tlds["IO"];
    const ok  = h.$ === "Ref" && h.k === "IO" && io !== undefined && io.$ === "Def" && io.b === true;
    if (!ok) {
      throw Err(book, ctx_nil(), "a foreign definition answering base's IO", k);
    }
  }
  if (def.v !== null) {
    const qs: Quant[] = [];
    let tel: HTerm = def.T;
    while (qs.length < def.n) {
      const t = term_wnf(book, tel);
      if (t.$ !== "All") {
        break;
      }
      qs.push(t.q);
      tel = t.B(Var(t.k, qs.length - 1));
    }
    while (qs.length < def.n) {
      qs.push(Lone());
    }
    def.e = term_check(book, { t: Ref(k), n: def.n, def: k, qs }, def.v, Lone(), def.T, ctx_nil(), 0).tm;
  }
}

// the locked trio: a declared Sigma, Copy or Copiable must convert
// with these, even without Base. Copiable's pair is spelled on Sigma,
// not on the unlocked Pair def, so a forged Pair cannot reshape it.
const LOCK_SRC = `
type Sigma<-A: Type, -B: @-x: A -> Type>:
  Tuple{fst: A, snd: B(fst)}
assert Copy:
  forall -A: Type
  forall -x: A
  Type
def Copy(A, x):
  &y: A -> {x == y : A}
assert Copiable:
  forall -T: Type
  Type
def Copiable(T):
  @x: T -> Sigma<Copy(T, x), _ => Copy(T, x)>
`;

let lock_book: Book | null = null;

export function lock_valid(book: Book, k: Name, tld: TLD): void {
  if (k !== "Sigma" && k !== "Copy" && k !== "Copiable") {
    return;
  }
  if (lock_book === null) {
    lock_book = parse_book(LOCK_SRC);
  }
  const law = lock_book.tlds[k];
  const exp = "the locked definition of " + k + " (a forged " + k + " would inhabit Empty)";
  if (tld.$ === "ADT" && law.$ === "ADT") {
    let ok = tld.n === law.n && tld.c.length === law.c.length && term_equal(book, tld.T, law.T);
    for (let j = 0; ok && j < law.c.length; j++) {
      ok = tld.c[j].k === law.c[j].k && tld.c[j].n === law.c[j].n && term_equal(book, tld.c[j].T, law.c[j].T);
    }
    if (!ok) {
      throw Err(book, ctx_nil(), exp);
    }
    return;
  }
  if (tld.$ !== "Def" || law.$ !== "Def" || tld.i !== undefined || !term_equal(book, tld.T, law.T)) {
    throw Err(book, ctx_nil(), exp);
  }
  if (tld.v !== null && !term_equal(book, tld.v, law.v as HTerm)) {
    throw Err(book, ctx_nil(), exp);
  }
}

export function book_valid(book: Book): void {
  const seen = book_nil();
  const last = new Map<Name, number>();
  for (let i = 0; i < book.order.length; i++) {
    last.set(book.order[i], i);
  }
  for (let i = 0; i < book.order.length; i++) {
    const k = book.order[i];
    const tld = book.tlds[k];
    const scope = book.halts ? book : seen;
    switch (tld.$) {
      case "ADT": {
        seen.tlds[k] = tld;
        for (const c of tld.c) {
          seen.ctrs[c.k] = c;
        }
        adt_valid(scope, k, tld);
        lock_valid(scope, k, tld);
        break;
      }
      case "Def": {
        const dec: Def = { $: "Def", n: tld.n, T: tld.T, v: null, b: tld.b };
        const fin = last.get(k) === i;
        if (fin && tld.v === null && tld.b !== true && !tld.i && !book.halts) {
          throw Err(book, ctx_nil(), "a filled definition for '" + k + "' (an unfilled assert is an error outside base and #[halts])");
        }
        seen.tlds[k] = dec;
        def_valid(scope, k, fin ? tld : dec);
        lock_valid(scope, k, fin ? tld : dec);
        seen.tlds[k] = fin ? tld : dec;
        break;
      }
    }
  }
}

// Comp
// ====

// Types
// =====

type Unbox = "f32" | "u32" | null;

type Seg = {
  fid: string;
  def: Name;
  lines: string[];
  params: string[];
  frame: { pop: number; base: number } | null;
  refs: Set<string>;
  dead?: boolean;
  spin?: boolean;
  unbox?: Unbox[];
};

type Spine = {
  h: HTerm;
  t: HTerm;
  all: HTerm[];
  args: HTerm[];
};

type Comp = Carb | File | Js;

type Capture = { p: Probe; q: Quant; A: HTerm | null };

type Carb = {
  src: Book;
  book: Book;
  mint: Map<Name, boolean>;
  kn: number;
  done: Set<Name>;
  queue: Name[];
  inl: Map<Name, HTerm | null>;
  inlrun: Set<Name>;
  bangs: Set<Name>;
  brw: Map<Name, boolean[]>;
  clo: boolean;
};

type Scratch = {
  spares: { words: number; name: string; z: boolean }[];
  fresh: Map<string, number>;
  uses: Map<Probe, Bind>;
  local: Set<string>;
  brwl: Set<string>;
  fusing: Set<Name>;
};

type File = Scratch & {
  book: Book;
  segs: Seg[];
  seg: Seg;
  tab: number;
  cb: Carb;
  cids: Map<string, { arity: number; packed: boolean }>;
  shr: Set<string>;
  tabs: Map<string, number>;
  spins: string[];
  reqs: string;
};

type Native = {
  intr: Record<Name, string | ((xs: string[], ts: HTerm[]) => string)>;
  elim?: Record<Name, string[]>;
  cond: Record<Name, string>;
};

type Of<K> = Extract<HTerm, { $: K }>;

type Probe = Of<"Var">;

type HBinder = Of<"Lam" | "Let">;

type HAll = Of<"All">;

type HAdt = Of<"ADT">;

type HLet = Of<"Let">;

type HLam = Of<"Lam">;

type Forked = { h: HLam; c: Of<"Ctr"> };

type UMap = PMap<number>;

type Call = {
  k: Name;
  args: HTerm[];
  bang: boolean;
};

type Subs = Map<HTerm, HTerm>;

type Open = (env: Subs) => HTerm;

type Kont = (caps: Capture[], x: Open) => Open;

type Root = [Name, number];

type Parts = { k: Name; vs: string[]; w: boolean };

type Bind = { owed: number; local: string; triv: boolean; parts?: Parts };

type Dst = string[] | null;

type Arg = string | Parts;

type Intr = {
  e?: (a: string[], fl: File) => string;
  call?: boolean;
  parts?: (shr: boolean) => string[];
};

type Js = {
  book:  Book;
  cb:    Carb;
  lines: string[];
  fresh: Map<string, number>;
};

type JsNative = {
  intr: Record<Name, (xs: string[]) => string>;
  elim: Record<Name, (s: string) => string[]>;
  cond: Record<Name, (s: string) => string>;
};

type Arms = { arms: [Name, HTerm][]; end: HTerm | null };

type Dom = [Quant, Name, HTerm];

// Constants
// =========

const CLO_APPLY = "Clo.apply";

const tpl = (t: string): ((xs: string[]) => string) => {
  const ps = t.split(/\$(\d)/);
  return (xs) => ps.map((p, i) => (i % 2 === 1 ? xs[+p] : p)).join("");
};

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
      ALeaf: "buf_new(e, 0, $0)",
      ANode: "blk_node(e, $0, $1)",
    },
    elim: {
      ALeaf: ["blk_take(e, $0)"],
      ANode: ["blk_half(e, $0, 0)", "blk_rest(e, $0)"],
    },
    cond: {
      ALeaf: "term_aux($0) == 0",
      ANode: "term_aux($0) != 0",
    },
  },
};

const ARR_NATIVE = { ...NATIVES.Array,
  intr: { ...NATIVES.Array.intr, ALeaf: "blk_leaf(e, $0)" } };

const blk_op = (read: string): Intr => ({
  parts: (shr) =>
    [shr ? "blk_cow(e, $0)" : "$0", read],
});

export const INTRINSICS: Record<string, Intr> = {
  u32_show: { e: tpl("u32_show(e, $0)"), call: true },
  array_swap: blk_op("blk_give(e, $3, $4, $1, $2)"),
  array_get: blk_op("buf_read(e, $3, $1)"),
  array_new: { e: tpl("buf_new(e, $0, $1)"), call: true },
  array_copy: { parts: () => ["term_keep(e, $0)", "$2"] },
  u32_copy: { e: ([a], fl) => {
    const w = emit_alias(fl, a, "w");
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

let PIDN = 0;

const DUMMY = probe("~");

const live_dom = ([q]: Dom): boolean => quant_live(q);

const mat_head = (t: HTerm): boolean => t.$ === "Mat" || t.$ === "Efq";

const probe_of = (t: HTerm): Probe => term_force(t) as Probe;

const USE0 = Emp<number>();

const HOLES: HTerm[] = [];

const PASS: Kont = (_c, x) => x;

const EMPTY: Subs = new Map();

const copy_pair = ([a]: string[]): string => {
  const half = "{$: \"Tuple\", $0: " + a + ", $1: null}";
  return "{$: \"Tuple\", $0: " + half + ", $1: " + half + "}";
};

export const JS_INTRINSICS: Record<string, string | ((xs: string[]) =>
  string)> = {
  u32_inc:      "(($0 + 1) >>> 0)",
  u32_mul:      "(Math.imul($0, $1) >>> 0)",
  u32_div:      "($1 === 0 ? 0 : ($0 / $1) >>> 0)",
  u32_mod:      "($1 === 0 ? $0 : $0 % $1)",
  u32_not:      "(~$0 >>> 0)",
  u32_shl:      "(($0 << 1) >>> 0)",
  u32_shr:      "($0 >>> 1)",
  u32_shln:     "($0 >= 32n ? 0 : ($1 << Number($0)) >>> 0)",
  u32_shrn:     "($0 >= 32n ? 0 : $1 >>> Number($0))",
  u32_is_zero:  "($0 === 0)",
  u32_to_nat:   "BigInt($0)",
  u32_from_nat: "Number($0 & 0xFFFFFFFFn)",
  u32_to_f32:   "Math.fround($0)",
  u32_show:     "String($0)",
  u32_cmp:      "cmp_new($0, $1)",
  u32_copy:     copy_pair,
  bool_or:      "($0 || $1)",
  bool_xor:     "($0 !== $1)",
  nat_copy:     copy_pair,
  nat_double:   "($0 << 1n)",
  nat_add:      "($0 + $1)",
  nat_sub:      "($0 < $1 ? 0n : $0 - $1)",
  nat_mul:      "($0 * $1)",
  nat_divmod:   ([a, b]) => "(" + b + " === 0n"
    + " ? {$: \"Tuple\", $0: 0n, $1: " + a + "}"
    + " : {$: \"Tuple\", $0: " + a + " / " + b
    + ", $1: " + a + " % " + b + "})",
  nat_cmp:      "cmp_new($0, $1)",
  nat_is_lt:    "($0 < $1)",
  string_append: "($0 + $1)",
  f32_to_u32:   "($0 >= 1 && $0 < 4294967296 ? Math.floor($0) : 0)",
  f32_sqrt:     "Math.fround(Math.sqrt($0))",
  array_copy:   ([a]) => "{$: \"Tuple\", $0: " + a + ", $1: " + a + "}",
  array_get:    "array_get($0, $1)",
  array_new:    "array_new($0, $1)",
  array_swap:   "array_swap($0, $1, $2)",
};

for (const [c, o] of [["eq", "==="], ["ne", "!=="], ["lt", "<"],
  ["le", "<="], ["gt", ">"], ["ge", ">="]]) {
  JS_INTRINSICS["u32_is_" + c] = "($0 " + o + " $1)";
  JS_INTRINSICS["f32_is_" + c] = "($0 " + o + " $1)";
}

for (const [c, o] of [["add", "+"], ["sub", "-"], ["and", "&"],
  ["or", "|"], ["xor", "^"]]) {
  JS_INTRINSICS["u32_" + c] = "(($0 " + o + " $1) >>> 0)";
}

for (const [c, o] of [["add", "+"], ["sub", "-"], ["mul", "*"],
  ["div", "/"]]) {
  JS_INTRINSICS["f32_" + c] = "Math.fround($0 " + o + " $1)";
}

Object.setPrototypeOf(JS_INTRINSICS, null);

const char_scalar = (n: number): boolean =>
  n < 0xd800 || (n >= 0xe000 && n <= 0x10ffff);

const JS_NATIVES: Record<Name, JsNative> = {
  Nat: {
    intr: {
      Zero: () => "0n",
      Succ: ([p]) => {
        if (/^\d+n$/.test(p)) {
          return (BigInt(p.slice(0, -1)) + 1n) + "n";
        }
        return "(" + p + " + 1n)";
      },
    },
    elim: {
      Zero: () => [],
      Succ: (s) => ["(" + s + " - 1n)"],
    },
    cond: {
      Zero: (s) => s + " === 0n",
      Succ: (s) => s + " !== 0n",
    },
  },
  Bool: {
    intr: {
      False: () => "false",
      True: () => "true",
    },
    elim: {
      False: () => [],
      True: () => [],
    },
    cond: {
      False: (s) => "!" + s,
      True: (s) => s,
    },
  },
  U32: {
    intr: {
      U32: ([w]) => "word_to_u32(" + w + ")",
    },
    elim: {
      U32: (s) => ["u32_to_word(" + s + ")"],
    },
    cond: {},
  },
  Char: {
    intr: {
      Chr: ([c]) => {
        const n = Number(c);
        if (/^\d+$/.test(c) && char_scalar(n)) {
          return JSON.stringify(String.fromCodePoint(n));
        }
        return "char_new(" + c + ")";
      },
    },
    elim: {
      Chr: (s) => [s + ".codePointAt(0)"],
    },
    cond: {},
  },
  String: {
    intr: {
      SNil: () => "\"\"",
      SCon: ([h, t]) => {
        if (STRLIT.test(h) && STRLIT.test(t)) {
          return JSON.stringify(JSON.parse(h) + JSON.parse(t));
        }
        return "(" + h + " + " + t + ")";
      },
    },
    elim: {
      SNil: () => [],
      SCon: (s) => [
        "(" + s + ".codePointAt(0) > 0xFFFF ? "
          + s + ".slice(0, 2) : " + s + "[0])",
        "(" + s + ".codePointAt(0) > 0xFFFF ? "
          + s + ".slice(2) : " + s + ".slice(1))",
      ],
    },
    cond: {
      SNil: (s) => s + " === \"\"",
      SCon: (s) => s + " !== \"\"",
    },
  },
};

const IDENT  = /^[A-Za-z_$][A-Za-z0-9_$]*$/;
const ATOM   = /^(?:[A-Za-z_$][A-Za-z0-9_$]*|\d+n?|\d+\.\d+)$/;
const STRLIT = new RegExp("^\"(?:[^\"\\\\]|\\\\.)*\"$");

const NATIVE_DIE = " does not match the native format of its type";

// Name
// ====

function name_clean(k: string): string {
  return k.replace(/[^A-Za-z0-9_]/g, "_");
}

function name_local(fl: File, k: Name): string {
  const base = name_clean(k);
  const n = fl.fresh.get(base) ?? 0;
  fl.fresh.set(base, n + 1);
  const name = base + "_" + n;
  fl.local.add(name);
  return name;
}

// Die
// ---

function die(m: string): never {
  throw new Error("tocl: " + m + " (report this case)");
}

// Term
// ====

// Probe
// -----

function probe(k: Name): Probe {
  return Var(k, (PIDN += 1)) as Probe;
}

function term_open(t: HBinder): { p: Probe; b: HTerm } {
  const p = probe(t.k);
  return { p, b: t.f(p) };
}

// Live
// ----

function live_doms(c: Comp, tld: Def): Dom[] {
  return def_get_params(c.book, tld).filter(live_dom);
}

function term_spine(cf: Comp, tm: HTerm): Spine {
  const apps: Of<"App">[] = [];
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
  const tld = c.$ === "Ref" ? cf.book.tlds[c.k] : undefined;
  const qs = tld?.$ === "Def" ? tele_unbind(cf.book, tld.T).doms : null;
  const live = (i: number) => qs === null
    ? call_live(cf.book, apps[i].f)
    : i >= qs.length || quant_live(qs[i][0]);
  const all = apps.map((a) => a.x);
  return { h, t: c, all, args: all.filter((_, i) => live(i)) };
}

function term_eta(t: HTerm): HTerm {
  return Lam("x", 0, (y) => App(t, y));
}

function term_kids(cf: Comp, tm: HTerm): HTerm[] {
  const t = term_force(tm);
  switch (t.$) {
    case "Ann": return [t.x];
    case "Lam": return [term_open(t).b];
    case "Let": return quant_live(t.q)
      ? [t.v, term_open(t).b] : [term_open(t).b];
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

function term_any(cf: Comp, t: HTerm,
  p: (s: HTerm) => boolean): boolean {
  const s = term_force(t);
  return p(s) || term_kids(cf, s).some((x) => term_any(cf, x, p));
}

function term_const(t: HTerm): boolean {
  const s = term_strip(t);
  return s.$ === "Ctr" && s.x.every(term_const);
}

function term_use(u: UMap, p: Probe): number {
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
      const ck = call_kind(cb, t);
      const lent = ck && cb.brw.get(ck.k);
      return term_kids(cb, t).reduce((u, x, j) =>
        lent?.[j - 1] === true ? u
          : pmap_union(u, term_uses(cb, x), (a, b) => a + b),
        USE0);
    }
  }
}

// Intr
// ----

function intr_of(c: Comp, k: Name): Intr | undefined {
  return def_own(c.book.tlds[k])
    ? INTRINSICS[eff_name(k)] : undefined;
}

// Call
// ----

function call_live(book: Book, f: HTerm): boolean {
  const all = ty_all(book, ty_ann(f));
  return all === null || quant_live(all.q);
}

function call_kind(c: Comp, t: HTerm): Call | null {
  const m = term_spine(c, t);
  let dyn = m.t.$ === "Var" && m.args.length > 0;
  if (m.t.$ === "Ref" && intr_of(c, m.t.k) === undefined) {
    const tld = c.book.tlds[m.t.k];
    if (done_live(tld) || def_foreign(tld)) {
      const live = def_live(c, tld);
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
  while (f.$ === "Ann" || (f.$ === "App" && !call_live(c.book, f.f))) {
    f = term_force(f.$ === "App" ? f.f : f.x);
  }
  const a = f as Of<"App">;
  return { k: CLO_APPLY, args: [a.f, a.x], bang: false };
}

function call_is(cb: Carb, t: HTerm): boolean {
  return call_kind(cb, t) !== null;
}

function call_has(cb: Carb, t: HTerm): boolean {
  return term_any(cb, t, (s) => call_is(cb, s));
}

// Ty
// --

function ty_ann(t: HTerm): HTerm | null {
  const v = term_force(t);
  return v.$ === "Ann" ? v.T : null;
}

function ty_wnf(book: Book, ty: HTerm | null): HTerm | null {
  return ty && term_uncop(book, ty);
}

function ty_all(book: Book, ty: HTerm | null): HAll | null {
  const w = ty_wnf(book, ty);
  return w?.$ === "All" ? w : null;
}

function ty_tele(book: Book, T: HTerm, args: HTerm[]): HTerm {
  return args.reduce((T2, a) => (ty_all(book, T2) as HAll).B(a), T);
}

function ty_peel(tm: HTerm,
  ty: HTerm | null): [HTerm, HTerm | null] {
  let x = term_force(tm);
  while (x.$ === "Ann") {
    ty = x.T;
    x = term_force(x.x);
  }
  return [x, ty];
}

// Fork
// ====

function fork_hole(j: number): HTerm {
  return (HOLES[j] ??= probe("*"));
}

function fork_chain(t: HTerm, n: number,
  c: Comp | null): { ls: HLet[]; rest: HTerm } {
  const ls: HLet[] = [];
  let rest = t;
  while (ls.length < n) {
    const l = term_strip(rest);
    if (l.$ !== "Let" || (c && call_kind(c, l.v) === null)) {
      break;
    }
    ls.push(l);
    rest = l.f(fork_hole(ls.length - 1));
  }
  return { ls, rest };
}

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

// Call
// ----

function call_ok(cb: Carb, t: HTerm, n: number): Call | null {
  const ck = call_kind(cb, t);
  if (ck === null || ck.args.length < n) {
    return null;
  }
  const h = ck.args.length - n;
  if (!ck.args.slice(h).every((a, j) => term_strip(a) === fork_hole(j))) {
    return null;
  }
  return ck.args.slice(0, h).every((a) => !call_has(cb, a)) ? ck : null;
}

// Ctr
// ===

function ctr_tail(book: Book, ctr: Ctr): Dom[] {
  const doms = tele_unbind(book, ctr.T).doms;
  return doms.slice(doms.length - ctr.n);
}

function ctr_doms(book: Book, ctr: Ctr): HTerm[] {
  return ctr_tail(book, ctr).filter(live_dom).map(([, , A]) => A);
}

function ctr_scalar1(book: Book, k: Name): boolean {
  const ctr = book.ctrs[k];
  const fields = ctr === undefined ? [] : ctr_doms(book, ctr);
  return fields.length === 1 && ty_w32(book, fields[0]);
}

function ctr_flds(book: Book, k: Name, xs: HTerm[]): HTerm[] {
  const ctr = book.ctrs[k];
  const qs = ctr && ctr_tail(book, ctr).map(([q]) => q);
  return xs.filter((_, j) => qs?.[j] === undefined || quant_live(qs[j]));
}

// Ty
// --

function ty_w32(book: Book, A: HTerm | null): boolean {
  const t = ty_wnf(book, A);
  if (t?.$ === "ADT") {
    return t.k === "U32" || t.k === "Bool" || t.k === "Char";
  }
  return ty_f32(book, A);
}

function ty_f32(book: Book, A: HTerm | null): boolean {
  const t = ty_wnf(book, A);
  return t?.$ === "Ref" && t.k === "F32";
}

// Native
// ------

function native_of(book: Book, adt: HAdt): Native | undefined {
  if (adt.k === "U32") {
    die("a structural view of a machine word");
  }
  if (adt.k !== "Array" || ty_w32(book, adt.x[0])) {
    return NATIVES[adt.k];
  }
  if (["ADT", "All"].includes(term_uncop(book, adt.x[0]).$)) {
    return ARR_NATIVE;
  }
  die("an open Array element type");
}

// Adt
// ---

function adt_triv(book: Book, A: HTerm | null): boolean {
  const adt = ty_wnf(book, A);
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

// Mat
// ===

function mat_total(book: Book,
  adt: Extract<HTerm, { $: "ADT" }>): number {
  const tld = book.tlds[adt.k];
  if (tld === undefined || tld.$ !== "ADT") {
    js_die("undeclared datatype: " + adt.k);
  }
  return tld.c.length - adt.r.length;
}

function mat_arms(t: HTerm): Arms {
  const arms: [Name, HTerm][] = [];
  let cur = t;
  for (let m = term_strip(cur); m.$ === "Mat"; m = term_strip(cur)) {
    arms.push([m.k, m.h]);
    cur = m.m;
  }
  return { arms, end: term_strip(cur).$ === "Efq" ? null : cur };
}

// Quant
// =====

function quant_live(q: Quant): boolean {
  return q.$ !== "None";
}

// Def
// ===

function def_get_params(book: Book, def: Def): Dom[] {
  const doms = tele_unbind(book, def.T).doms;
  if (doms.length < def.n) {
    js_die("a def type shorter than its parameters");
  }
  return doms.slice(0, def.n);
}

function def_foreign(tld: TLD | undefined): tld is Def {
  return tld !== undefined && tld.$ === "Def" && tld.i !== undefined;
}

function def_live(c: Comp, tld: Def): number {
  return live_doms(c, tld).length + Number(def_foreign(tld));
}

function def_own(tld: TLD | undefined): boolean {
  return tld !== undefined && tld.$ === "Def" && tld.i === undefined
    && (tld.b === true || tld.v === null);
}

// Eff
// ===

function eff_name(k: Name): string {
  return k.toLowerCase().replace(/\./g, "_");
}

function eff_src(path: string, seen: Set<string>): string {
  path = realpathSync(path);
  if (seen.has(path)) {
    return "";
  }
  seen.add(path);
  const src = readFileSync(path, "utf8");
  const dir = path.slice(0, path.lastIndexOf("/") + 1);
  let out = "";
  for (const m of src.matchAll(/^\/\/! use (.+)$/gm)) {
    const rel = m[1].startsWith("./") ? m[1].slice(2) : m[1];
    out += eff_src(dir + rel, seen);
  }
  return out + src;
}

function eff_srcs(book: Book): [string[], string[]] {
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
  return [srcs, names];
}

// Io
// ==

function io_base(book: Book, t: HTerm): HTerm[] | null {
  while (true) {
    const [h, xs] = term_unapply(term_strip(t));
    if (h.$ !== "Ref") {
      return null;
    }
    const tld = book.tlds[h.k];
    if (tld === undefined || tld.$ !== "Def") {
      return null;
    }
    if (h.k === "IO" && tld.b === true) {
      return xs;
    }
    if (tld.v === null || xs.length < tld.n) {
      return null;
    }
    t = xs.reduce(term_apply, tld.v);
  }
}

export function io_type(book: Book): HTerm | null {
  const main = book.tlds["main"];
  if (main === undefined || main.$ !== "Def") {
    return null;
  }
  const xs = io_base(book, main.T);
  if (xs === null) {
    return null;
  }
  if (def_foreign(main)) {
    throw new Error("main must be a filled def: "
      + "a foreign import cannot anchor the event loop");
  }
  return xs.length === 1 ? xs[0] : null;
}

export function io_run(book: Book): number {
  const src = js_text(book)
    + "\nreturn io_run(" + js_sat("main") + ");";
  const run = new Function("require", src);
  return run(import.meta.require) as number;
}

// Defunnize
// =========

// Lift
// ----

function lift(t: HTerm): Open {
  return (env) => env.get(t) ?? t;
}

// App
// ---

function app_caps(cs: Capture[], f: Open): Open {
  return (env) => cs.reduce((c, b) => App(c, env.get(b.p) ?? b.p), f(env));
}

// Ret
// ---

function ret_of(cb: Carb, t: HTerm): HTerm {
  const s = term_force(t);
  if (s.$ === "Ann") {
    return s.T;
  }
  if (s.$ === "Let") {
    return ret_of(cb, s.f(DUMMY));
  }
  const m = term_spine(cb, s);
  const tld = m.t.$ === "Ref" ? cb.book.tlds[m.t.k] : undefined;
  const T = tld?.$ === "Def" ? tld.T
    : ty_ann(m.h) ?? die("a minted definition without a result type");
  return ty_tele(cb.book, T, m.all);
}

// Mint
// ----

function mint(cb: Carb, def: Name, stem: string, scope: Capture[],
  seq: boolean, tail: number, build: () => Open, ret: HTerm | null = null,
  extra = 0): Open {
  cb.kn += 1;
  const name = def + "$" + stem + cb.kn;
  const body = build();
  const bt = body(EMPTY);
  const u = term_uses(cb, bt);
  const kept = scope.filter((c, i) =>
    i >= scope.length - tail || !quant_live(c.q) || term_use(u, c.p) > 0);
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
    call_is(cb, s) && inl_at(cb, s) === null;
  const has_cut = (t: HTerm) => term_any(cb, t, cut_at);
  function bound(caps: Capture[], l: HLet, v: Open,
    rest: (caps: Capture[], body: HTerm) => Open,
    cuts = false): Open {
    const bd = { p: probe(l.k), q: l.q, A: ty_ann(v(EMPTY)) };
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
    const m = term_spine(cb, t);
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
        if (hf || !call_is(cb, s.f)) {
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
      const T = ty ?? ty_ann(s) ?? die("an untyped point-free arm");
      return func(caps, Ann(term_eta(s), T), null, left);
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
        const all = ty_all(cb.book, ty);
        const p = probe(s.k);
        const cap = { p, q: all?.q ?? Lone(), A: all?.A ?? null };
        const B = all && all.B(DUMMY);
        const body = func([...caps, cap], s.f(p), B,
          left - (quant_live(cap.q) ? 1 : 0));
        return (env) => Lam(s.k, s.i, (y) => body(new Map(env).set(p, y)),
          s.s);
      }
      case "Mat": {
        const ctr = cb.book.ctrs[s.k];
        const fs = ctr === undefined ? 0 : ctr_doms(cb.book, ctr).length;
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
      if (!quant_live(s.q)) {
        return leaf(caps, s.f(s.v));
      }
      if (cut_at(s.v)) {
        return apps(caps, s.v, false, (c2, c) =>
          bound(c2, s, c, leaf, true));
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
    const hf = mat_head(term_spine(cb, t).t) && !mat_head(s);
    if (hf || call_is(cb, t)) {
      return apps(caps, t, hf, PASS);
    }
    return expr(caps, t, null, PASS);
  }
  function fork(caps: Capture[], s: HLet, n: number): Open {
    const { ls, rest } = fork_chain(s, n, null);
    let jt = rest;
    for (let g; (g = inl_at(cb, jt)) !== null;) {
      jt = g;
    }
    const jc = call_ok(cb, jt, n);
    const whole = ls.every((l) => call_is(cb, l.v));
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
      const cuts = !whole && call_is(cb, vs[j](EMPTY));
      return bound(c2, l, vs[j], (c3, b) => chain(c3, j + 1, vs, b), cuts);
    };
    return many(caps, n, (c2, j, kx) => {
      if (call_is(cb, ls[j].v)) {
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
    if (call_is(cb, s)) {
      return apps(caps, s, false, (c2, c) => {
        const cx: Open = ty === null ? c : (env) => Ann(c(env), ty);
        const l = Let("h", 0, s, (x) => x) as HLet;
        return bound(c2, l, cx, (c3, b) => k(c3, lift(b)), true);
      });
    }
    switch (s.$) {
      case "App": {
        const m = term_spine(cb, s);
        const hf = mat_head(m.t);
        if (hf && (mint_all || has_cut(m.t))) {
          const T = ty_ann(m.h) ?? die("an untyped applied match");
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
        const all = ty_all(cb.book, ty)
          ?? die(`a lambda value without a type: ${s.k}`);
        const bd = { p: probe(s.k), q: all.q, A: all.A };
        const c2 = [...caps, bd];
        if (!quant_live(all.q)) {
          return expr(c2, s.f(bd.p), all.B(bd.p), k);
        }
        return k(caps, mint(cb, def, "c", c2, false, 1,
          () => leaf(c2, s.f(bd.p))));
      }
      case "Let": {
        if (!quant_live(s.q)) {
          return expr(caps, s.f(s.v), null, k);
        }
        if (call_has(cb, s.v) || has_cut(s.f(DUMMY))) {
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
        return expr(caps, term_eta(Ann(s, T)), T, k);
      }
      default: {
        return k(caps, lift(s));
      }
    }
  }
  return func([], tld.e as HTerm, tld.T,
    live_doms(cb, tld).length)(EMPTY);
}

// Carb
// ----

function carb_refs(cb: Carb, t: HTerm): Set<Name> {
  const out = new Set<Name>();
  term_any(cb, t, (s) => {
    if (s.$ === "Ref") {
      if (s.b) {
        cb.bangs.add(s.k);
      }
      if (intr_of(cb, s.k) === undefined) {
        out.add(s.k);
      }
    }
    return false;
  });
  return out;
}

function carb_ok(cb: Carb, t: HTerm): boolean {
  const leaf_ok = (x: HTerm): boolean => {
    const s = term_strip(x);
    if (s.$ === "Let") {
      const { ls, rest } = fork_chain(s, Infinity, cb);
      if (ls.length >= 1) {
        const jc = call_ok(cb, rest, ls.length);
        if (jc === null || !ls.every((l) => call_ok(cb, l.v, 0) !== null)) {
          return false;
        }
        const seq = cb.mint.get(jc.k) === true;
        return ls.length === 1 ? seq : !seq;
      }
      return !call_has(cb, s.v) && leaf_ok(s.f(DUMMY));
    }
    if (call_is(cb, s)) {
      return call_ok(cb, s, 0) !== null;
    }
    const m = term_spine(cb, s);
    if (!mat_head(m.t)) {
      return !call_has(cb, s);
    }
    return func_ok(m.h) && m.args.every((a) => !call_has(cb, a));
  };
  const func_ok = (x: HTerm): boolean => {
    const s = term_strip(x);
    switch (s.$) {
      case "Lam": return func_ok(s.f(DUMMY));
      case "Mat": return func_ok(s.h) && func_ok(s.m);
      case "Efq": return true;
      default: return leaf_ok(s);
    }
  };
  return func_ok(t);
}

function carb_book(src: Book, roots: Name[]): Carb {
  const tlds = { ...src.tlds };
  for (const [k, tld] of Object.entries(tlds)) {
    if (tld.$ === "Def" && tld.e !== undefined) {
      tlds[k] = { ...tld, e: term_higher(term_lower(tld.e), Emp<HTerm>()) };
    }
  }
  const book: Book = { ...src, tlds: { ...tlds } };
  const cb: Carb = {
    src: { ...src, tlds },
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
    const k = cb.queue.shift() as Name;
    if (cb.done.has(k)) {
      continue;
    }
    cb.done.add(k);
    const tld = book.tlds[k];
    if (!done_live(tld)) {
      continue;
    }
    let out = tld.e as HTerm;
    if (!cb.mint.has(k)) {
      if (out === undefined) {
        die("unelaborated def " + k);
      }
      out = carbonize(cb, k, tld);
    }
    if (!carb_ok(cb, out)) {
      out = carbonize(cb, k, tld, true);
    }
    book.tlds[k] = { ...tld, v: out, e: out };
    if (!carb_ok(cb, out)) {
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

// Calm
// ----

function calm_func(cb: Carb, t: HTerm, ty0: HTerm | null): boolean {
  const [s, ty] = ty_peel(t, ty0);
  const all = ty_all(cb.book, ty);
  if (s.$ === "Lam") {
    return calm_func(cb, s.f(DUMMY), all && all.B(DUMMY));
  }
  if (s.$ === "Mat") {
    if (all === null || !adt_triv(cb.book, all.A)) {
      return false;
    }
    return calm_func(cb, s.h, null) && calm_func(cb, s.m, ty);
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
      const m = term_spine(cb, y);
      if (mat_head(m.t)) {
        return calm_func(cb, m.h, null) && m.args.every(leafok);
      }
    }
    return term_kids(cb, y).every(leafok);
  }
}

function calm_of(cb: Carb, t: HTerm): boolean {
  return calm_func(cb, t, null)
    && !term_any(cb, t, (s) => fork_span(s) >= 2);
}

// Inl
// ---

function inl_calls(cb: Carb, t: HTerm, self?: Name): boolean {
  return !term_any(cb, t, (s) => {
    const ck = call_kind(cb, s);
    return ck !== null && ck.k !== self && inl_of(cb, ck.k) === null;
  });
}

function inl_fit(cb: Carb, t: HTerm, self?: Name): boolean {
  const size = (x: HTerm): number => {
    const s = term_strip(x);
    return term_kids(cb, s).reduce((n, y) => n + size(y), 1);
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
  const m = term_spine(cb, t);
  if (m.t.$ !== "Ref") {
    return null;
  }
  const tld = cb.src.tlds[m.t.k];
  if (tld?.$ !== "Def") {
    return null;
  }
  const live = live_doms(cb, tld).length;
  const intr = intr_of(cb, m.t.k) !== undefined;
  if (m.args.length < (intr ? live : live - 1)) {
    return Ann(term_eta(t), ty_tele(cb.book, tld.T, m.all));
  }
  if (m.t.b) {
    return null;
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
  if (live_doms(cb, tld).length !== tld.n) {
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
    const m = term_spine(cb, s);
    if (m.t.$ !== "Ref" || m.t.k !== k || m.t.b) {
      return s;
    }
    if (m.all.length !== tld.n || !term_const(m.all[0]) || d >= 32) {
      return s;
    }
    return trip(inl_splice(cb, raw, m.all, 0, null), d + 1);
  };
  cb.inlrun.add(k);
  const out = trip(inl_splice(cb, raw, args, 0, null), 0);
  const calm = inl_calls(cb, out);
  cb.inlrun.delete(k);
  return calm && calm_of(cb, out) ? out : null;
}

function inl_splice(cb: Carb, t: HTerm, args: HTerm[], i: number,
  ty0: HTerm | null): HTerm {
  if (i === args.length) {
    return t;
  }
  const [s, ty] = ty_peel(t, ty0);
  const all = ty_all(cb.book, ty);
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
    const a = ty_all(cb.book, ty_ann(out));
    if (a === null) {
      die("a splice applied past its telescope");
    }
    out = Ann(App(out, args[j]), a.B(args[j]));
  }
  return out;
}

// Done
// ====

function done_live(tld: ADT | Def | undefined): tld is Def {
  return tld?.$ === "Def" && tld.v !== null;
}

function done_defs(cb: Carb): [Name, Def][] {
  return [...cb.done].map((k) => [k, cb.book.tlds[k]] as [Name, Def])
    .filter((p) => done_live(p[1]));
}

// Shr
// ===

function shr_build(cb: Carb): Set<string> {
  const keeps = new Set<string>();
  const sites: (HTerm | null)[] = [];
  const held = (B: HTerm | null, force = false) => {
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
        const T = ty_tele(cb.book, c.T, w.x);
        tele_unbind(cb.book, T).doms.filter(live_dom)
          .forEach(([, , A]) => held(A, true));
      }
    }
  };
  const site = (A: HTerm | null, n: number) => {
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
  const scan = (t: HTerm, ty0: HTerm | null): void => {
    const [s, ty] = ty_peel(t, ty0);
    if (s.$ === "Lam" || s.$ === "Let") {
      const { p, b: body } = term_open(s);
      const n = term_use(term_uses(cb, body), p);
      if (s.$ === "Let") {
        site(ty_ann(s.v), n);
        scan(s.v, null);
        return scan(body, null);
      }
      const all = ty_all(cb.book, ty)
        ?? die(`a binder without a type: ${s.k}`);
      if (quant_live(all.q)) {
        site(all.A, n);
      }
      return scan(body, all.B(p));
    }
    if (s.$ === "Ref" && intr_of(cb, s.k) === INTRINSICS.array_copy) {
      keeps.add("t:Array");
    }
    for (const kid of term_kids(cb, s)) {
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

// Brw
// ===

function brw_type(cb: Carb, A: HTerm): boolean {
  const t = term_uncop(cb.book, A);
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
    const site = (t: HTerm, ct: HTerm | null) => {
      const ck = call_kind(cb, t) as Call;
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
          && term_spine(cb, ct).args.some((z) => term_strip(z) === p);
        if (!roots.has(p) && !held) {
          flip([ck.k, j]);
        }
      });
    };
    const leaf = (t: HTerm) => {
      const x = term_strip(t);
      if (x.$ === "Let") {
        const { ls, rest } = fork_chain(x, Infinity, cb);
        if (ls.length >= 2) {
          for (const l of ls) {
            site(l.v, rest);
          }
          return site(rest, null);
        }
        const o = term_open(x);
        if (call_is(cb, x.v)) {
          site(x.v, o.b);
        } else {
          guard(x.v);
        }
        return leaf(o.b);
      }
      if (call_is(cb, x)) {
        return site(x, null);
      }
      const m = term_spine(cb, x);
      if (!mat_head(m.t)) {
        return guard(x);
      }
      m.args.forEach(guard);
      walk(m.t, m.args.map(() => null));
    };
    const walk = (t: HTerm, plan: (Root | null)[]) => {
      const x = term_strip(t);
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
        const fs = ctr === undefined ? [] : ctr_tail(cb.book, ctr);
        const fr = fs.map(([q, , A]) => {
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
    walk(tld.e as HTerm, def_get_params(cb.book, tld)
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
}

// File
// ====

// Cid
// ---

function cid_mac(k: string): string {
  return `CID_${name_clean(k).toUpperCase()}`;
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

// Block
// -----

function block(fl: File, open: string, go: () => void) {
  file_push(fl, open);
  fl.tab += 1;
  go();
  fl.tab -= 1;
  file_push(fl, "}");
}

// Cls
// ---

function cls_fit(words: number): number {
  return 32 - Math.clz32(words - 1);
}

// Spare
// -----

function spare_free(fl: File, words: number, name: string,
  z: boolean) {
  file_push(fl,
    `${z ? "spare_free" : "heap_free"}(e, cls_fit(${words}), ${name});`);
}

function spare_flush(fl: File) {
  for (const s of fl.spares.reverse()) {
    spare_free(fl, s.words, s.name, s.z);
  }
  fl.spares = [];
}

// Bind
// ----

function bind_pop(fl: File, x: HTerm): string {
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
  const o = term_open(x);
  if (parts !== undefined && !parts.w) {
    local = emit_alias(fl, ctr_build(fl, parts.k, parts.vs), x.k);
    parts = undefined;
  }
  const brw = fl.brwl.has(local);
  const triv = parts !== undefined || brw || adt_triv(fl.book, ty);
  const n = term_use(term_uses(fl.cb, o.b), o.p);
  if (n === 0 && !brw) {
    if (!triv) {
      file_push(fl, `term_sink(e, ${local});`);
    }
  } else {
    fl.uses.set(o.p, { owed: triv ? 1 : n, local, triv, parts });
  }
  return o.b;
}

// Seg
// ---

function seg_new(fl: File, name: string, seq: boolean,
  params: string[], def = ""): Seg {
  const seg: Seg = { fid: seg_fid(name), def, lines: [],
    params, refs: new Set(),
    frame: seq ? { pop: params.length - 1, base: 0 } : null };
  fl.segs.push(seg);
  return seg;
}

function seg_fid(k: Name): string {
  return `FID_${name_clean(k).toUpperCase()}`;
}

function seg_ref(fl: File, fid: string): string {
  fl.seg.refs.add(fid);
  return fid;
}

// Node
// ----

function node_fill(fl: File, k: string, alloc: string,
  exprs: string[], shr = false): string {
  const nd = name_local(fl, k);
  file_push(fl, `u64 ${nd} = ${alloc};`);
  exprs.forEach((w, j) => {
    file_push(fl, `e.mem[${nd} + ${j}] = ${shr ? `rfc_seal(e, ${w})` : w};`);
  });
  return nd;
}

// Ctr
// ---

function ctr_build(fl: File, k: Name, exprs: string[]): string {
  const cid = cid_reg(fl, k);
  if (exprs.length === 0 || fl.cids.get(k)!.packed) {
    return `term_pak(${cid}, ${exprs[0] ?? 0})`;
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
  return `term_ctr(${cid}, ${node_fill(fl, "nd", got, exprs, shr)})`;
}

// Select
// ======

// Eq
// --

function eq_set(fl: File, t: HTerm): { p: Probe; ks: number[] } | null {
  const st = term_strip(t);
  if (st.$ === "Let") {
    const v = term_strip(st.v);
    return v.$ === "Var" ? eq_set(fl, st.f(v)) : null;
  }
  const sp = term_spine(fl, t);
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
  const it = intr_of(fl, sp.t.k);
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
      const w = vs[1 - i];
      const xi = term_strip(sp.args[i]);
      if (xi.$ === "Var" && w !== null) {
        return { p: probe_of(xi), ks: [w] };
      }
    }
  }
  return null;
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

// Sel
// ---

function sel_ok(fl: File, t: HTerm): boolean {
  const x = term_strip(t);
  if (x.$ === "Var") {
    const b = fl.uses.get(probe_of(x));
    return b?.triv === true && b.parts === undefined;
  }
  const m = term_spine(fl, x);
  if (m.t.$ === "Ref" && intr_of(fl, m.t.k)?.call === false) {
    return m.args.every((a) => sel_ok(fl, a));
  }
  return u32_from_term(x) !== null;
}

// Nat
// ===

function nat_table(fl: File, x: HTerm, s: string, dst: Dst): boolean {
  const tab_ok = (t: HTerm): boolean => {
    const sp = term_spine(fl, t);
    if (sp.t.$ === "Ref" && intr_of(fl, sp.t.k)?.call === false) {
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
  ls.push(m.$ === "Lam" ? term_open(m).b : m);
  if (ls.length < 3 || !ls.every(tab_ok)) {
    return false;
  }
  const key = emit_exprs(fl, ls).join(", ");
  const id = fl.tabs.get(key) ?? fl.tabs.size;
  fl.tabs.set(key, id);
  emit_put(fl, dst, `TAB_AT(TAB_${id}, ${s}, ${ls.length - 1})`);
  return true;
}

// Fuse
// ====

function fuse_lends(fl: File, k: Name): boolean {
  return def_foreign(fl.book.tlds[k])
    || (fl.cb.brw.get(k) ?? []).some(Boolean);
}

function fuse_pure(fl: File, k: Name, body: HTerm): boolean {
  return !term_any(fl, body, (s) => {
    const c = call_kind(fl, s);
    return c !== null && c.k !== k;
  }) && calm_of(fl.cb, body);
}

function fuse_call(fl: File, ck: Call, dst: Dst): boolean {
  if (ck.bang || dst !== null || ck.k === CLO_APPLY || fuse_lends(fl, ck.k)) {
    return false;
  }
  const tld = fl.book.tlds[ck.k] as Def;
  const body = tld.e as HTerm;
  const loop = fl.fusing.has(ck.k)
    || term_any(fl, body, (s) => call_kind(fl, s)?.k === ck.k);
  if (loop || (term_strip(body).$ === "Mat" && term_const(ck.args[0]))
    || !call_has(fl.cb, body)) {
    return false;
  }
  const args = ck.args.map((a) => arg_fuse(fl, a));
  const seen = new Set<Name>([fl.seg.def]);
  let spins = false;
  const walk = (g: Name) => {
    const gt = fl.book.tlds[g] as Def;
    if (gt.i !== undefined) {
      return;
    }
    const gb = gt.e as HTerm;
    spins ||= call_has(fl.cb, gb) && fuse_pure(fl, g, gb);
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
      emit_jump(fl, args.map((a) => arg_term(fl, a)), ck.k);
    });
  }
  fl.fusing.add(ck.k);
  emit_func(fl, body, tld.T, args, dst);
  fl.fusing.delete(ck.k);
  return true;
}

function fuse_cut(fl: File, ck: Call, km: Call, dst: Dst): boolean {
  if (ck.bang || ck.k === CLO_APPLY || fuse_lends(fl, ck.k)
    || fuse_lends(fl, km.k)) {
    return false;
  }
  const tld = fl.book.tlds[ck.k] as Def;
  const jt = fl.book.tlds[km.k] as Def;
  const body = tld.e as HTerm;
  const loop = call_has(fl.cb, body);
  const tele = tele_unbind(fl.book, tld.T);
  if (tele.doms.slice(tld.n).some(live_dom)) {
    return false;
  }
  const ret = tele.ret;
  const word = adt_triv(fl.book, ret);
  const adt = term_uncop(fl.book, ret);
  const rt = adt.$ === "ADT" ? fl.book.tlds[adt.k] : undefined;
  const one = rt?.$ === "ADT" && rt.c.length === 1 ? rt.c[0] : null;
  const doms = one && ctr_doms(fl.book, one);
  const flat = doms !== null && doms.length >= 2
    && doms.every((A) => adt_triv(fl.book, A));
  const rec = word || !flat ? null
    : { k: (one as Ctr).k, n: (doms as HTerm[]).length };
  let size = 0;
  term_any(fl, body, () => (size += 1) < 0);
  if (!(!loop && word && size <= 50
    && fl.seg.def.split("$")[0] === "main")
    && (!fuse_pure(fl, ck.k, body) || !(loop || word || rec !== null))) {
    return false;
  }
  const ps = emit_hold(fl, emit_exprs(fl, ck.args), "p");
  const caps = emit_exprs(fl, km.args.slice(0, -1));
  const vs = Array.from({ length: rec?.n ?? 1 }, () => name_local(fl, "x"));
  for (const v of vs) {
    file_push(fl, `Term ${v} = 0;`);
  }
  if (loop) {
    spare_flush(fl);
    const at = fl.seg.lines.length;
    const seg = fl.seg;
    fl.seg = { ...seg, def: ck.k, params: ps, unbox: undefined };
    block(fl, "WL_SPIN", () => {
      emit_func(fl, body, tld.T, ps, vs);
      fl.seg = seg;
      file_push(fl, "break;");
    });
    const spun = fl.seg.lines.splice(at);
    const off = "  ".repeat(fl.tab - 1);
    const bent = spun.map((l) =>
      "  " + (l.startsWith(off) ? l.slice(off.length) : l));
    const name = seg_ref(fl, "spin_" + fl.spins.length);
    const sig = ps.map((p) => ", Term " + p).join("");
    fl.spins.push([`  static Term ${name}(Env e, THR Term* o${sig}) {`,
      "    u32 wpoll = 0;", ...vs.map((v) => `    Term ${v} = 0;`),
      ...bent, ...vs.map((v, j) => `    o[${j}] = ${v};`),
      "    return 1;", "  }"].join("\n"));
    const o = name_local(fl, "o");
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

// Emit
// ====

function emit_exprs(fl: File, xs: HTerm[]): string[] {
  return xs.map((a) => emit_expr(fl, a, null));
}

function emit_hold(fl: File, exprs: string[], k: string): string[] {
  return exprs.map((ex) => {
    const al = name_local(fl, k);
    file_push(fl, `Term ${al} = ${ex};`);
    return al;
  });
}

function emit_alias(fl: File, e: string, k: string): string {
  return fl.local.has(e) ? e : emit_hold(fl, [e], k)[0];
}

function emit_peek(fl: File, v: string): string {
  const bl = name_local(fl, "bl");
  file_push(fl, `u64 ${bl} = term_peek(e, ${v});`);
  return bl;
}

function emit_task(fl: File, fid: string, rem: number, words: string[],
  cont = "WL_CONT", idx: string | number = "WL_IDX"): string {
  return node_fill(fl, "t",
    `task_node(e, ${seg_ref(fl, fid)}, ${cont}, ${idx}, ${rem})`, words);
}

function emit_frame(fl: File, words: string[], next: string) {
  const n = words.length + 1;
  file_push(fl, `WL_ROOM(${n});`);
  [...words, seg_ref(fl, next)].forEach((w, i) => {
    file_push(fl, `STK(${i}) = ${w};`);
  });
  file_push(fl, `WL_PUSHN(${n});`);
}

function emit_bang(fl: File, ck: Call, args: string[]) {
  const fid = seg_fid(ck.k);
  file_push(fl, `return term_tsk(${fid}, ${emit_task(fl, fid, 0, args)});`);
}

function emit_jump(fl: File, args: string[], k: Name) {
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

function emit_call(fl: File, ck: Call, km: Call | null) {
  const cargs = arg_lend(fl, ck);
  const cexps = km === null ? [] : emit_exprs(fl, km.args.slice(0, -1));
  spare_flush(fl);
  if (km !== null) {
    const kf = seg_fid(km.k);
    file_push(fl, "if (seq) {");
    fl.tab += 1;
    emit_frame(fl, cexps, kf);
    fl.tab -= 1;
    block(fl, "} else {", () => {
      file_push(fl,
        `WL_KONT(${kf}, ${emit_task(fl, kf, 1, cexps)}, ${cexps.length});`);
      if (ck.bang) {
        emit_bang(fl, ck, cargs);
      }
    });
  } else if (ck.bang) {
    block(fl, "if (!seq) {", () => emit_bang(fl, ck, cargs));
  }
  emit_jump(fl, cargs, ck.k);
}

function emit_fork(fl: File, ls: HLet[], rest: HTerm) {
  const tab0 = fl.tab;
  const n = ls.length;
  const calls = ls.map((l) => call_kind(fl, l.v) as Call);
  const jc = call_kind(fl, rest) as Call;
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
      const cj = emit_task(fl, fj[j], 0, margs[j], jt, m + j);
      file_push(fl, `WL_KID(${jn}, ${m + j}, ${fj[j]}, ${cj});`);
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
}

// Arg
// ---

function arg_term(fl: File, a: Arg): string {
  return typeof a === "string" ? a : ctr_build(fl, a.k, a.vs);
}

function arg_lend(fl: File, ck: Call): string[] {
  const lent = fl.cb.brw.get(ck.k);
  return ck.args.map((a, j) => {
    if (!lent?.[j]) {
      return emit_expr(fl, a, null);
    }
    return (fl.uses.get(term_strip(a) as Probe) as Bind).local;
  });
}

function arg_fuse(fl: File, a: HTerm): Arg {
  const [x] = ty_peel(a, null);
  if (x.$ === "Var") {
    const b = fl.uses.get(probe_of(x));
    if (b?.parts !== undefined) {
      return b.parts;
    }
  }
  const m = term_spine(fl, x);
  const it = m.t.$ === "Ref" ? intr_of(fl, m.t.k) : undefined;
  if (it?.parts !== undefined) {
    const arr = native_of(fl.book, term_uncop(fl.book,
      ty_ann(m.args[0]) ?? die("an untyped block")) as HAdt)
      === ARR_NATIVE ? "1" : "0";
    const as = emit_exprs(fl, m.args).map((z) => emit_alias(fl, z, "aw"));
    const vs: string[] = [];
    for (const p of it.parts(fl.shr.has("t:Array"))) {
      vs.push(emit_alias(fl, tpl(p)([...as, arr, ...vs]), "aw"));
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

function emit_open(fl: File, x: HLet): HTerm {
  const name = name_local(fl, x.k);
  file_push(fl, `Term ${name} = ${emit_expr(fl, x.v, null)};`);
  return bind_uses(fl, name, x, ty_ann(x.v));
}

function emit_expr(fl: File, tm: HTerm, ty0: HTerm | null): string {
  const [x, ty] = ty_peel(tm, ty0);
  switch (x.$) {
    case "Var": return bind_pop(fl, x);
    case "Ref":
    case "App": {
      const m = term_spine(fl, x);
      if (mat_head(m.t)) {
        const t = name_local(fl, "t");
        file_push(fl, `Term ${t} = 0;`);
        emit_matapp(fl, m, [t]);
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
        if (m.args.length !== def_live(fl, tld as Def) - 1) {
          die("an under-applied def value: " + g.k);
        }
        const fid = seg_ref(fl, seg_fid(g.k));
        const exprs = emit_exprs(fl, m.args);
        if (exprs.length === 0) {
          return `term_clo(${fid}, 0)`;
        }
        return `term_clo(${fid}, ${node_fill(fl, "nd",
          `heap_alloc(e, cls_fit(${exprs.length}))`, exprs, fl.cb.clo)})`;
      }
      if (intr.parts !== undefined) {
        return arg_term(fl, arg_fuse(fl, x));
      }
      const exprs = emit_exprs(fl, m.args);
      return intr.e!(exprs, fl);
    }
    case "Ctr": {
      const adt = term_uncop(fl.book, ty as HTerm);
      if (adt.$ !== "ADT") {
        die(`a constructor at a non-datatype type: ${x.k}`);
      }
      if (adt.k === "U32") {
        const u = u32_from_term(x);
        if (u !== null) {
          return `${u}ull`;
        }
      }
      const flds = ctr_flds(fl.book, x.k, x.x);
      const exprs = emit_exprs(fl, flds);
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
    case "Let": return emit_expr(fl, emit_open(fl, x), null);
    case "Rwt": return emit_expr(fl, x.f, ty);
    case "Rfl": return "0ull";
    default: die(`cannot compile a ${x.$} node`);
  }
}

function emit_func(fl: File, tm: HTerm, ty0: HTerm | null,
  args: Arg[], dst: Dst): void {
  const [x, ty] = ty_peel(tm, ty0);
  switch (x.$) {
    case "Lam": {
      const all = term_uncop(fl.book, ty as HTerm) as HAll;
      if (!quant_live(all.q)) {
        return emit_func(fl, x.f(DUMMY), all.B(DUMMY), args, dst);
      }
      const a0 = args[0];
      const name = typeof a0 === "string" ? emit_alias(fl, a0, x.k) : "";
      const rec = typeof a0 === "string" ? undefined : a0;
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
      const s = emit_alias(fl, arg_term(fl, args[0]), "s");
      return emit_match(fl, x, ty, s,
        args.slice(1).map((a) => arg_term(fl, a)), dst);
    }
    default: return emit_leaf(fl, x, ty, dst);
  }
}

function emit_leaf(fl: File, tm: HTerm, ty0: HTerm | null,
  dst: Dst): void {
  const [x, ty] = ty_peel(tm, ty0);
  if (x.$ === "Let") {
    const { ls, rest } = fork_chain(x, Infinity, fl);
    if (ls.length >= 2) {
      return emit_fork(fl, ls, rest);
    }
    const vc = call_kind(fl, x.v);
    if (vc !== null) {
      const km = call_kind(fl, rest) as Call;
      if (!fuse_cut(fl, vc, km, dst)) {
        emit_call(fl, vc, km);
      }
      return;
    }
    return emit_leaf(fl, emit_open(fl, x), null, dst);
  }
  const ck = call_kind(fl, x);
  if (ck !== null) {
    if (fuse_call(fl, ck, dst)) {
      return;
    }
    return emit_call(fl, ck, null);
  }
  const m = term_spine(fl, x);
  if (mat_head(m.t)) {
    return emit_matapp(fl, m, dst);
  }
  if (dst !== null && dst.length > 1) {
    if (x.$ !== "Ctr") {
      const v = emit_alias(fl, emit_expr(fl, x, ty), "v");
      const bl = emit_peek(fl, v);
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
  emit_func(fl, m.h, null, [arg_fuse(fl, m.args[0]),
    ...emit_exprs(fl, m.args.slice(1))], dst);
}

function emit_stuck(fl: File): void {
  file_push(fl, "err_post(e.mem, ERR_TAGS);");
  file_push(fl, "return 0;");
}

function emit_match(fl: File, x: HTerm, T: HTerm | null, s: string,
  rest: string[], dst: Dst): void {
  if (x.$ === "Efq") {
    return emit_stuck(fl);
  }
  const all = term_uncop(fl.book, T as HTerm) as HAll;
  const adt = term_uncop(fl.book, all.A) as HAdt;
  const { arms, end } = mat_arms(x);
  const total = mat_total(fl.book, adt);
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
      let sel = `${mT.m}u`;
      if (mT.m !== mF.m) {
        sel = `(${s} != 0 ? ${mT.m}u : ${mF.m}u)`;
      }
      return emit_put(fl, dst,
        `u32_is_eq(u32_or(${bind_pop(fl, eT!.p)}, ${sel}), ${mT.K}u)`);
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
    s = emit_alias(fl, `blk_cow(e, ${s})`, "s");
  }
  const armsets = arms.map(([, h]) => term_uses(fl.cb, h));
  const emits = arms.map(([k, h], i) =>
    () => arm_emit(h, k, armsets[i]));
  if (end !== null || arms.length < total) {
    const last: HTerm = end ?? Efq();
    armsets.push(term_uses(fl.cb, last));
    emits.push(() => fin(last, armsets[arms.length], [s, ...rest]));
  }
  const mx_of = (p: Probe) =>
    armsets.reduce((m, u) => Math.max(m, term_use(u, p)), 0);
  function fin(h2: HTerm, mine: UMap, args: string[]) {
    for (const [p, b] of [...fl.uses]) {
      const use = term_use(mine, p);
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
        const bl = emit_peek(fl, s);
        fexprs = Array.from({ length: live }, (_, j) => `e.mem[${bl} + ${j}]`);
      } else {
        const sp2 = name_local(fl, "sp");
        const fb = name_local(fl, "fb");
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
    const fields = emit_hold(fl, fexprs, "f");
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

// Gen
// ---

function gen_case(seg: Seg): string {
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
}

function gen_dyn(fl: File): boolean {
  return fl.segs.some((s) => s.refs.has("FID_CLO_APPLY"));
}

function gen_defs(fl: File): string {
  const clo = gen_dyn(fl);
  const entries = [...fl.segs,
    { fid: "FID_IO_EMIT", params: [""], frame: null, dead: !clo } as Seg,
    ...clo ? [{ fid: "FID_CLO_APPLY", params: ["", ""],
      frame: null } as Seg] : []];
  const out: string[] = [];
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
      out.push(`#define ${m.padEnd(w)} ${i}`);
    });
    out.push("");
  }
  const table = (nm: string, vals: number[]) => {
    if (vals.some((v) => v > 255)) {
      die("an arity over 255");
    }
    out.push(`CONSTV u8 ${nm}[] = { ${vals.join(", ")} };`, "");
  };

  const cb = fl.cb;
  table("FID_ARITY_T", entries.map((s) => s.params.length));
  table("FID_BANGS_T", entries.map((s) => Number(cb.bangs.has(s.def))));
  const deps = new Map<Name, Set<Name>>();
  const nofk = new Set<Name>();
  for (const [k, tld] of done_defs(cb)) {
    const body = tld.e as HTerm;
    deps.set(k, carb_refs(cb, body));
    if (!term_any(cb, body, (s) =>
      (s.$ === "Let" && fork_chain(s, Infinity, cb).ls.length >= 2)
        || call_kind(cb, s)?.k === CLO_APPLY)) {
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
  const ns = [...Array(bank).keys()];
  const rs = ns.map((i) => "r" + i).join(", ");
  const load = [...ns].reverse().map((r) =>
    `    case ${r + 1}: r${r} = e.mem[a + ${r}]; \\\n`).join("");
  out.push(`#define IO_HOTS ${"SCon Tuple Done Fail".split(" ")
    .reduce((m, k, i) => m | (fl.shr.has(k) ? 1 << i : 0), 0)}`, "");
  const pass = ns.map((i) =>
    `    case ${i}: r${i} = res; \\\n      break; \\\n`).join("");
  out.push(`#define WL_LAST \\\n  switch (war) { \\\n${pass}  }`);
  if (cb.clo) {
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
    const mac = line.startsWith("#") || line.endsWith("\\");
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

// Compile
// =======

function compile_open(): Scratch {
  return {
    fresh: new Map(),
    spares: [],
    uses: new Map(),
    local: new Set(),
    brwl: new Set(),
    fusing: new Set(),
  };
}

function compile_emit(cb: Carb, shr: Set<string>): File {
  const fl: File = {
    book: cb.book,
    segs: [],
    seg: { fid: "", def: "", lines: [], params: [], frame: null,
      refs: new Set() },
    tab: 2,
    cb,
    cids: new Map(),
    shr,
    tabs: new Map(),
    spins: [],
    reqs: "",
    ...compile_open(),
  };
  for (const k of "Tuple SNil SCon Chr Unit Emit Halt Fail Done File Socket \
Listener".split(" ")) {
    cid_reg(fl, k);
  }
  for (const [k, tld] of done_defs(cb)) {
    Object.assign(fl, compile_open());
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
    emit_func(fl, tld.e as HTerm, tld.T, params, null);
  }
  const seen = new Set<string>();
  fl.reqs += eff_src(new URL("./effs/sys.c", import.meta.url).pathname, seen);
  fl.spares = [];
  for (const k of cb.done) {
    const tld = cb.book.tlds[k];
    if (!def_foreign(tld)) {
      continue;
    }
    const imp = tld.i!.find((x) => x.endsWith(".c"))
      ?? die(`a foreign def without a .c import: ${k}`);
    fl.reqs += eff_src(imp, seen);
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
  for (const s of fl.segs) {
    s.dead = !live.has(s.fid)
      || (!gen_dyn(fl) && def_foreign(cb.book.tlds[s.def]));
  }
  fl.spins = fl.spins.filter((_, i) => live.has(`spin_${i}`));
  return fl;
}

export function compile_book(book: Book): string {
  if (io_type(book) === null) {
    die("main must answer IO<T>: the event loop runs IO mains only");
  }
  const cb = carb_book(book, ["main"]);
  brw_build(cb);
  const fl = compile_emit(cb, shr_build(cb));
  const segs = fl.segs.filter((s) => !s.dead).map(gen_case).join("\n\n");
  const spins = fl.spins.length === 0 ? "" :
    "#ifdef __METAL_VERSION__\nstruct Spin {\n"
    + fl.spins.join("\n\n") + "\n};\n#endif\n\n";
  return width_fold(TEMPLATE
    .replace(/^\/\/ Book\n\/\/ ====$/m, (m) => m + "\n\n" + gen_defs(fl))
    .replace(/^\/\/ Segments\n\/\/ ========$/m, (m) =>
      m + "\n\n" + spins + segs)
    .replace(/^\/\/ Requests\n\/\/ ========$/m, (m) => m + "\n\n" + fl.reqs));
}

// Js
// ==

function js_push(fl: Js, tab: number, line: string): void {
  fl.lines.push("  ".repeat(tab) + line);
}

function js_fresh(fl: Js, k: Name): string {
  const n = fl.fresh.get(k) ?? 0;
  fl.fresh.set(k, n + 1);
  return k.replace(/\./g, "$") + "$" + n;
}

function js_die(m: string): never {
  throw new Error("tojs: " + m);
}

function js_sat(k: Name): string {
  return "$" + k.replace(/\./g, "$") + "$";
}

function js_intr(book: Book, k: Name): string | null {
  const low = eff_name(k);
  return def_own(book.tlds[k]) && JS_INTRINSICS[low] !== undefined ? low : null;
}

function js_render(fl: Js, low: string, exprs: string[],
  tab: number): string {
  const xs = exprs.map((e) => {
    if (ATOM.test(e) || STRLIT.test(e)) {
      return e;
    }
    const t = js_fresh(fl, "x");
    js_push(fl, tab, "const " + t + " = " + e + ";");
    return t;
  });
  const r = JS_INTRINSICS[low];
  return typeof r === "string" ? tpl(r)(xs) : r(xs);
}

function js_alias(fl: Js, e: string, k: Name,
  tab: number): string {
  if (IDENT.test(e)) {
    return e;
  }
  const t = js_fresh(fl, k);
  js_push(fl, tab, "const " + t + " = " + e + ";");
  return t;
}

function js_put(fl: Js, tab: number, tgt: string, e: string): void {
  if (tgt === "return") {
    js_push(fl, tab, "return " + e + ";");
  } else {
    js_push(fl, tab, tgt + " = " + e + ";");
  }
}

function js_args(fl: Js, xs: HTerm[], tab: number): string[] {
  return xs.map((x) => js_expr(fl, x, null, tab));
}

function js_call(fl: Js, ck: Call, tab: number,
  tail: boolean): string {
  const exprs = js_args(fl, ck.args, tab);
  if (ck.k === CLO_APPLY) {
    const [f, x] = exprs;
    return tail ? "run_jump(" + f + ", [" + x + "])" : f + "(" + x + ")";
  }
  const intr = js_intr(fl.book, ck.k);
  if (intr !== null) {
    return js_render(fl, intr, exprs, tab);
  }
  const all = exprs.join(", ");
  if (def_foreign(fl.book.tlds[ck.k])) {
    return js_sat(ck.k) + "(" + all + ")";
  }
  if (tail) {
    return "run_jump(" + js_sat(ck.k) + ", [" + all + "])";
  }
  return "run_loop(" + js_sat(ck.k) + "(" + all + "))";
}

function js_spine(fl: Js, k: Name, exprs: string[],
  tab: number): string {
  const tld = fl.book.tlds[k];
  if (tld === undefined) {
    js_die("unknown name: " + k);
  }
  if (tld.$ === "ADT") {
    return "null";
  }
  const intr = js_intr(fl.book, k);
  const live = def_live(fl, tld);
  if (intr !== null && exprs.length === live) {
    return js_render(fl, intr, exprs, tab);
  }
  if (intr === null && tld.v === null && tld.i === undefined) {
    js_die("a live call into the assert " + k);
  }
  if (exprs.length !== live - 1) {
    js_die("an under-applied def value: " + k);
  }
  const v = js_fresh(fl, "x");
  if (intr !== null) {
    return "(" + v + ") => " + js_render(fl, intr, [...exprs, v], tab);
  }
  const call = js_sat(k) + "(" + [...exprs, v].join(", ") + ")";
  if (def_foreign(tld)) {
    return "(" + v + ") => " + call;
  }
  return "(" + v + ") => run_loop(" + call + ")";
}

function js_expr(fl: Js, tm: HTerm,
  ty: HTerm | null, tab: number): string {
  const x = term_force(tm);
  switch (x.$) {
    case "Ann": {
      return js_expr(fl, x.x, x.T, tab);
    }
    case "Var": {
      return x.k;
    }
    case "Ref":
    case "App": {
      const m = term_spine(fl.cb, x);
      if (mat_head(m.t)) {
        const t = js_fresh(fl, "$t");
        js_push(fl, tab, "let " + t + ";");
        js_func(fl, m.h, null, js_args(fl, m.args, tab), tab, t);
        return t;
      }
      if (m.t.$ === "Var" && m.args.length === 0) {
        return m.t.k;
      }
      if (m.t.$ !== "Ref") {
        js_die("a " + m.t.$ + "-headed spine in an expression");
      }
      return js_spine(fl, m.t.k, js_args(fl, m.args, tab), tab);
    }
    case "Ctr": {
      const adt = ty === null ? null : term_uncop(fl.book, ty);
      if (adt === null || adt.$ !== "ADT") {
        js_die("a Ctr without a datatype-typed Ann: " + x.k);
      }
      if (adt.k === "U32") {
        const u = u32_from_term(x);
        if (u !== null) {
          return String(u);
        }
      }
      if (fl.book.ctrs[x.k] === undefined) {
        js_die("unknown constructor: " + x.k);
      }
      const exprs = ctr_flds(fl.book, x.k, x.x)
        .map((f) => js_expr(fl, f, null, tab));
      const native = JS_NATIVES[adt.k];
      if (native !== undefined) {
        const it = native.intr[x.k];
        const el = native.elim[x.k];
        if (it === undefined || el === undefined
          || el("s").length !== exprs.length) {
          js_die(x.k + NATIVE_DIE);
        }
        return it(exprs);
      }
      let e = "{$: \"" + x.k + "\"";
      for (let j = 0; j < exprs.length; j++) {
        e += ", $" + String(j) + ": " + exprs[j];
      }
      return e + "}";
    }
    case "Let": {
      if (!quant_live(x.q)) {
        return js_expr(fl, x.f(x.v), ty, tab);
      }
      const v = js_expr(fl, x.v, null, tab);
      const name = js_fresh(fl, x.k);
      js_push(fl, tab, "const " + name + " = " + v + ";");
      return js_expr(fl, x.f(Var(name, 0)), ty, tab);
    }
    case "Rwt": {
      return js_expr(fl, x.f, ty, tab);
    }
    case "Rfl":
    case "Typ":
    case "All":
    case "ADT":
    case "Eql": {
      return "null";
    }
    default: {
      js_die("cannot compile a " + x.$ + " node");
    }
  }
}

function js_func(fl: Js, tm: HTerm, ty: HTerm | null,
  args: string[], tab: number, tgt: string): void {
  const x = term_force(tm);
  if (x.$ === "Ann") {
    return js_func(fl, x.x, x.T, args, tab, tgt);
  }
  if (x.$ === "Lam") {
    const all = ty_all(fl.book, ty);
    if (all === null) {
      js_die("a Lam without a function-typed Ann");
    }
    if (!quant_live(all.q)) {
      const nul: HTerm = Var("null", 0);
      return js_func(fl, x.f(nul), all.B(nul), args, tab, tgt);
    }
    if (args.length === 0) {
      js_die("a function layer past its arity");
    }
    const name = js_alias(fl, args[0], x.k, tab);
    const v: HTerm = Var(name, 0);
    return js_func(fl, x.f(v), all.B(v), args.slice(1), tab, tgt);
  }
  if (mat_head(x)) {
    return js_match(fl, x, ty, args, tab, tgt);
  }
  return js_leaf(fl, x, ty, tab, tgt);
}

function js_leaf(fl: Js, tm: HTerm, ty: HTerm | null,
  tab: number, tgt: string): void {
  const x = term_force(tm);
  if (x.$ === "Ann") {
    return js_leaf(fl, x.x, x.T, tab, tgt);
  }
  if (x.$ === "Let") {
    if (!quant_live(x.q)) {
      return js_leaf(fl, x.f(x.v), ty, tab, tgt);
    }
    const ck = call_kind(fl.cb, x.v);
    const v = ck === null
      ? js_expr(fl, x.v, null, tab)
      : js_call(fl, ck, tab, false);
    const name = js_fresh(fl, x.k);
    js_push(fl, tab, "const " + name + " = " + v + ";");
    return js_leaf(fl, x.f(Var(name, 0)), ty, tab, tgt);
  }
  const ck = call_kind(fl.cb, x);
  if (ck !== null) {
    return js_put(fl, tab, tgt,
      js_call(fl, ck, tab, tgt === "return"));
  }
  const m = term_spine(fl.cb, x);
  if (mat_head(m.t)) {
    return js_func(fl, m.h, null,
      js_args(fl, m.args, tab), tab, tgt);
  }
  return js_put(fl, tab, tgt, js_expr(fl, x, ty, tab));
}

function js_match(fl: Js, x: HTerm, ty: HTerm | null,
  args: string[], tab: number, tgt: string): void {
  if (x.$ === "Efq") {
    js_push(fl, tab, "throw new Error(\"unreachable\");");
    return;
  }
  const s = js_alias(fl, args[0], "$t", tab);
  const rest = args.slice(1);
  const all = ty_all(fl.book, ty);
  if (all === null) {
    js_die("a match without a function-typed Ann");
  }
  const adt = term_uncop(fl.book, all.A);
  if (adt.$ !== "ADT") {
    js_die("a non-datatype match scrutinee");
  }
  let { arms, end } = mat_arms(x);
  const total = mat_total(fl.book, adt);
  if (adt.k === "IO.OP") {
    js_push(fl, tab, "if (" + s + ".$ === \"$FFI\") {");
    js_push(fl, tab + 1, "throw " + s + ";");
    js_push(fl, tab, "}");
  }
  if (arms.length === total) {
    end = null;
  } else if (end === null) {
    end = Efq();
  }
  const native = JS_NATIVES[adt.k];
  const arm = (h: HTerm, k: Name, tab2: number): void => {
    const ctr = fl.book.ctrs[k];
    if (ctr === undefined) {
      js_die("unknown constructor: " + k);
    }
    const live = ctr_doms(fl.book, ctr).length;
    let fields: string[];
    if (native !== undefined) {
      const el = native.elim[k];
      if (el === undefined || el(s).length !== live) {
        js_die(k + NATIVE_DIE);
      }
      fields = el(s);
    } else {
      fields = [];
      for (let j = 0; j < live; j++) {
        fields.push(s + ".$" + String(j));
      }
    }
    js_func(fl, h, null, [...fields, ...rest], tab2, tgt);
  };
  if (arms.length === 1 && end === null && total === 1) {
    return arm(arms[0][1], arms[0][0], tab);
  }
  for (let i = 0; i < arms.length; i++) {
    let cond: string;
    if (native !== undefined) {
      const cn = native.cond[arms[i][0]];
      if (cn === undefined) {
        js_die(arms[i][0] + NATIVE_DIE);
      }
      cond = cn(s);
    } else {
      cond = s + ".$ === \"" + arms[i][0] + "\"";
    }
    let open = "} else if (" + cond + ") {";
    if (i === 0) {
      open = "if (" + cond + ") {";
    } else if (end === null && i === arms.length - 1) {
      open = "} else {";
    }
    js_push(fl, tab, open);
    arm(arms[i][1], arms[i][0], tab + 1);
  }
  if (end !== null) {
    js_push(fl, tab, "} else {");
    js_func(fl, end, null, [s, ...rest], tab + 1, tgt);
  }
  js_push(fl, tab, "}");
}

function js_def(fl: Js, k: Name, def: Def): void {
  fl.fresh = new Map();
  if (js_intr(fl.book, k.split("$")[0]) !== null) {
    return;
  }
  const params = live_doms(fl, def).map(([, n]) => js_fresh(fl, n));
  if (def.i !== undefined) {
    if (def.i.find((p) => p.endsWith(".js")) === undefined) {
      js_die("a foreign def without a .js import: " + k);
    }
    const kont = js_fresh(fl, "k");
    js_push(fl, 0, "function " + js_sat(k) + "("
      + [...params, kont].join(", ") + ") {");
    js_push(fl, 1, "return { $: \"$FFI\", run: () => $0eff."
      + eff_name(k) + "(" + params.join(", ") + "), kont: " + kont + " };");
    js_push(fl, 0, "}");
  } else {
    if (def.e === undefined) {
      js_die("unelaborated def " + k + ": run book_valid first");
    }
    js_push(fl, 0, "function " + js_sat(k) + "("
      + params.join(", ") + ") {");
    js_func(fl, def.e, def.T, params, 1, "return");
    js_push(fl, 0, "}");
  }
  js_push(fl, 0, "");
}

function js_seam(line: string): number {
  let seam = 0;
  let text = false;
  for (let i = 0; i < 80 && i < line.length; i += 1) {
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
    }
  }
  return seam;
}

function js_fold(text: string): string {
  const out: string[] = [];
  for (let line of text.split("\n")) {
    const bent = line.match(/^ */)![0] + "  ";
    while (line.length > 80) {
      const seam = js_seam(line);
      if (seam <= bent.length) {
        break;
      }
      out.push(line.slice(0, seam));
      line = bent + line.slice(seam).trimStart();
    }
    out.push(line);
  }
  return out.join("\n");
}

function js_text(book: Book): string {
  const roots: Name[] = [];
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
  const fl: Js = { book: cb.book, cb, lines: [], fresh: new Map() };
  for (const [k, def] of done_defs(cb)) {
    js_def(fl, k, def);
  }
  for (const k of cb.done) {
    const tld = cb.book.tlds[k];
    if (def_foreign(tld)) {
      js_def(fl, k, tld);
    }
  }
  const [srcs, names] = eff_srcs(book);
  let effs = "";
  if (srcs.length > 0) {
    const rows = names.map((n) => "  " + n + ": typeof " + n
      + " === \"function\" ? " + n + " : undefined,");
    effs = "const $0eff = (() => {\n" + srcs.join("\n") + "\n"
      + "return {\n" + js_fold(rows.join("\n")) + "\n};\n"
      + "})();\n\n";
  }
  const out = RUNTIME + effs + "// Program\n// =======\n\n"
    + js_fold(fl.lines.join("\n"));
  const main = book.tlds["main"];
  if (main !== undefined) {
    if (main.$ !== "Def" || main.v === null
      || def_get_params(book, main).some(([q]) => quant_live(q))) {
      js_die("main must be a filled def with no live "
        + "parameters (the runner calls it with none)");
    }
    if (io_type(book) === null) {
      js_die("main must answer IO<T>: "
        + "the event loop runs IO mains only");
    }
  }
  return out;
}

export function js_book(book: Book): string {
  let out = js_text(book);
  if (book.tlds["main"] !== undefined) {
    out += "\ncli(process.argv.slice(2));";
    out += "\nio_exit(" + js_sat("main") + ");";
  }
  return out;
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
#else
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
#endif
#endif

// Dialect
// =======

#ifdef __METAL_VERSION__
#define DEV     device
#define GRP     threadgroup
#define THR     thread
#define INLINE  inline
#define HOT     inline
#define OUTLINE static
#define CONSTV  constant
#define DEVICE  1
#define A32(p)  ((DEV atomic_uint*)(p))
#define RLX     memory_order_relaxed
#define FENCE() atomic_thread_fence(mem_flags::mem_device, memory_order_seq_cst)
#else
#define DEV
#define THR
#define INLINE  static inline
#define HOT     static inline __attribute__((always_inline))
#define OUTLINE static __attribute__((noinline))
#define CONSTV  static const
#define DEVICE  0
#define FENCE() __atomic_thread_fence(__ATOMIC_SEQ_CST)
#endif

#ifdef __METAL_VERSION__
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

#ifdef __METAL_VERSION__
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
#else
typedef uint64_t u64;
typedef uint32_t u32;
typedef uint8_t  u8;
typedef float    f32;
#endif

typedef u64 Loc;
#define LOC_MASK ((1ull << 40) - 1)

#define f32_unbox(x)  __builtin_bit_cast(f32, (u32)(x))
#define u32_unbox(x)  ((u32)(x))
#define f32_rewrap(x) ((u64)__builtin_bit_cast(u32, (f32)(x)))
#define u32_rewrap(x) ((u64)(x))

#define u32_inc(a)       U32_BIN(a, +, 1)
#define u32_not(a)       u32_rewrap(~u32_unbox(a))
#define u32_shl(a)       U32_BIN(a, <<, 1)
#define u32_shr(a)       U32_BIN(a, >>, 1)
#define u32_is_zero(a)   U32_BIN(a, ==, 0)
#define u32_to_f32(a)    f32_rewrap((f32)u32_unbox(a))
#define u32_to_nat(a)    u32_rewrap(u32_unbox(a))
#define u32_from_nat     u32_to_nat
#define U32_BIN(a, o, b) u32_rewrap(u32_unbox(a) o u32_unbox(b))
#define F32_BIN(a, o, b) f32_rewrap(f32_unbox(a) o f32_unbox(b))
#define F32_CMP(a, o, b) u32_rewrap(f32_unbox(a) o f32_unbox(b))

#define u32_and(a, b)   U32_BIN(a, &, b)
#define u32_or(a, b)    U32_BIN(a, |, b)
#define u32_xor(a, b)   U32_BIN(a, ^, b)
#define u32_is_eq(a, b) U32_BIN(a, ==, b)
#define u32_is_ne(a, b) U32_BIN(a, !=, b)
#define u32_is_lt(a, b) U32_BIN(a, <, b)
#define u32_is_le(a, b) U32_BIN(a, <=, b)
#define u32_is_gt(a, b) U32_BIN(a, >, b)
#define u32_is_ge(a, b) U32_BIN(a, >=, b)
#define u32_cmp(a, b)   (u32_is_gt(a, b) + u32_is_ge(a, b))
#define u32_add(a, b)   U32_BIN(a, +, b)
#define u32_sub(a, b)   U32_BIN(a, -, b)
#define u32_mul(a, b)   U32_BIN(a, *, b)
#define bool_or(a, b)   ((a) | (b))
#define bool_xor(a, b)  ((a) ^ (b))
#define f32_add(a, b)   F32_BIN(a, +, b)
#define f32_sub(a, b)   F32_BIN(a, -, b)
#define f32_mul(a, b)   F32_BIN(a, *, b)
#define f32_div(a, b)   F32_BIN(a, /, b)
#define f32_sqrt(a)     f32_rewrap(sqrtf(f32_unbox(a)))

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
#define H_TOME_WIRED 65ull

#define HEAP_OFF  (STAK_OFF + CUBE * STAK_LEN)

typedef DEV u64* Corpus;

typedef struct {
  Corpus   mem;
  Monk     mnk;
#ifdef __METAL_VERSION__
  GRP u64* alc;
#endif
} Env;

typedef DEV Term* Stk;

typedef Term Nat;
#define NAT_IMM ((1ull << 48) - 1)

typedef Term U32;

#ifdef __METAL_VERSION__
typedef u32 u32a;
#else
typedef u32 __attribute__((may_alias)) u32a;
#endif

#ifdef __METAL_VERSION__
typedef threadgroup atomic_uint* Cursor;
#define CUR_STEP(c) atomic_fetch_add_explicit(c, 1, RLX)
#else
typedef u32* Cursor;
#define CUR_STEP(c) ((*(c))++)
#endif

// Constants
// =========

#define PAGE_BITS    7
#define QUANTUM_BITS (DEVICE ? PAGE_BITS : 12)
#define DOOM_WORDS   (1ull << NCLS)
#define CUBE_SIDE    128
#define CUBE         (1ull << 14)
#define RING_LEN     (1ull << 10)
#define STAK_LEN     (1ull << 11)
#define MONK_WORDS   32ull
#define NCLS         9
#define HUGE_CLS     (32 - NCLS)
#define ALC_WORDS    (2 * NCLS)
#define TOME_PAGES   (1u << 18)

// Globals
// =======

#ifndef __METAL_VERSION__

typedef _Atomic u32     au32;
typedef _Atomic u64     au64;
typedef pthread_mutex_t lock;
typedef pthread_cond_t  cond;

static Corpus CORPUS;

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
static u64                         gpu_wired;
static u64                         gpu_cap;
#endif

static u64 ALC[CUBE_SIDE][ALC_WORDS];

static bool io_metal;
static Stk  io_stk;

static const char* CLI_HELP =
  "usage: %s [options]\n"
  "  --threads N        worker threads, up to 128 (default: the CPU count)\n"
  "  --parallel on|off  off means one thread and no GPU (default: on)\n"
  "  --gpu on|off       send ! calls to the GPU (default: on if present)\n"
  "  --help             show this text\n";

#endif

// Book
// ====

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

INLINE u32 cid_arity(Cid cid) {
  return (u32)CID_ARITY_T[cid];
}

// A32
// ===

#ifdef __METAL_VERSION__

#define a32_load(p)         atomic_load_explicit(A32(p), RLX)
#define a32_store(p, v)     atomic_store_explicit(A32(p), v, RLX)
#define a32_add(p, v)       atomic_fetch_add_explicit(A32(p), v, RLX)

INLINE u32 a32_sub_rel(DEV u32* p, u32 v) {
  FENCE();
  return atomic_fetch_sub_explicit(A32(p), v, RLX);
}

INLINE void a32_store_rel(DEV u32* p, u32 v) {
  FENCE();
  atomic_store_explicit(A32(p), v, RLX);
}

INLINE u32 a32_load_acq(DEV u32* p) {
  u32 v = a32_load(p);
  FENCE();
  return v;
}

#define a32_acq(p) FENCE()

INLINE bool a32_cas(DEV u32* p, thread u32* e, u32 v) {
  FENCE();
  bool ok = atomic_compare_exchange_weak_explicit(A32(p), e, v, RLX, RLX);
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

#ifdef __METAL_VERSION__

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
  err_fail(code, "runtime fail-stop");
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
  Page p = DEVICE && err_seen(H) ? 0
    : a32_add(a32_at(H, H_PAGE_BUMP), span);
  if ((u64)p + span > a32_load(a32_at(H, DEVICE ? H_TOME_WIRED : H_PAGE_CAP))) {
    err_post(H, ERR_HEAP);
    p = 0;
  }
  return p;
}

#define loc_doomed(loc) (DEVICE && (loc) == page_loc(0))

#if DEVICE

INLINE bool page_tight(Corpus H, u32 tomes) {
  u32 wired = a32_load(a32_at(H, H_TOME_WIRED));
  u32 bump  = a32_load(a32_at(H, H_PAGE_BUMP));
  return bump + tomes * TOME_PAGES >= wired
    && bump >= (tomes - 1) * TOME_PAGES
    && wired < a32_load(a32_at(H, H_PAGE_CAP));
}

INLINE bool page_park(Env e) {
  if (page_tight(e.mem, 1)) {
    a32_add(a32_at(e.mem, H_CURSOR), 1);
    return true;
  }
  return false;
}

#else

#define page_tight(H, tomes) false
#define page_park(e)         false

#endif

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

// Heap
// ====

#ifdef __METAL_VERSION__
INLINE void alc_open(Env e) {
  for (u32 i = 0; i < ALC_WORDS; i += 1) {
    e.alc[i * CUBE_SIDE] = *monk_word(e.mem, e.mnk, M_HEAD + i);
  }
}
INLINE void alc_close(Env e) {
  for (u32 i = 0; i < ALC_WORDS; i += 1) {
    *monk_word(e.mem, e.mnk, M_HEAD + i) = e.alc[i * CUBE_SIDE];
  }
}

INLINE u64 alc_load(Env e, u32 ride, Cls c) {
  return e.alc[(ride * NCLS + c) * CUBE_SIDE];
}
INLINE void alc_store(Env e, u32 ride, Cls c, u64 v) {
  e.alc[(ride * NCLS + c) * CUBE_SIDE] = v;
}
#else
INLINE u64 alc_load(Env e, u32 ride, Cls c) {
  return ALC[e.mnk][ride * NCLS + c];
}
INLINE void alc_store(Env e, u32 ride, Cls c, u64 v) {
  ALC[e.mnk][ride * NCLS + c] = v;
}
#endif

#define cls_quantum(cls) (1u << ((cls) > QUANTUM_BITS ? (cls) : QUANTUM_BITS))

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
  if (p == 0) {
    return page_loc(0);
  }
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
  if (cls < NCLS) {
    H[loc] = alc_load(e, 0, cls);
    alc_store(e, 0, cls, loc);
  } else {
    heap_free_huge(e, cls, loc);
  }
}

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
  if (term_triv(t) || term_rfc(t)) {
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

OUTLINE Term rfc_open(Env e, Term t) {
  Corpus H = e.mem;
  u32 cls  = blk_span(e, t);
  u64 span = 1ull << cls;
  Loc r    = term_loc(t);
  u64 cell = rfc_view(e, r);
  if ((cell & RFC_CNT) == 1) {
    return rfc_sole(e, t);
  }
  Loc src = cell >> 24;
  Loc dst = heap_alloc(e, cls);
  if (loc_doomed(dst)) {
    return term_buf(0, dst);
  }
  for (u64 j = 0; j < span; j += 1) {
    H[dst + j] = H[src + j];
  }
  span_fade(e, t, src, term_tag(t) == TAG_ARR ? (u32)span : 0);
  return (t & ~(RFC_BIT | LOC_MASK)) | dst;
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

// Natives
// =======

OUTLINE Term u32_show(Env e, u32 v) {
  Term s = term_pak(CID_SNIL, 0);
  do {
    Loc l = heap_alloc(e, 1);
    e.mem[l] = term_pak(CID_CHR, '0' + v % 10);
    e.mem[l + 1] = IO_HOTS & 1 ? rfc_seal(e, s) : s;
    s = term_ctr(CID_SCON, l);
    v /= 10;
  } while (v);
  return s;
}

INLINE U32 u32_div(U32 a, U32 b) {
  if ((u32)b == 0) {
    return 0;
  }
  return (u32)a / (u32)b;
}

INLINE U32 u32_mod(U32 a, U32 b) {
  if ((u32)b == 0) {
    return (u32)a;
  }
  return (u32)a % (u32)b;
}

INLINE U32 u32_shln(U32 n, U32 a) {
  if (n >= 32) {
    return 0;
  }
  return (u32)a << n;
}

INLINE U32 u32_shrn(U32 n, U32 a) {
  if (n >= 32) {
    return 0;
  }
  return (u32)a >> n;
}

#ifdef __METAL_VERSION__
#define sqrtf precise::sqrt
#endif

INLINE u32 f32_to_u32(u32 b) {
  if ((b >> 31) != 0) {
    return 0;
  }
  u32 e = (b >> 23) & 0xff;
  if (e < 127 || e >= 159) {
    return 0;
  }
  u32 m = (b & 0x7fffff) | 0x800000;
  if (e >= 150) {
    return m << (e - 150);
  }
  return m >> (150 - e);
}

INLINE Nat nat_succ(Env e, Nat n) {
  if (n + 1 > NAT_IMM) {
    err_post(e.mem, ERR_NATS);
    return NAT_IMM;
  }
  return n + 1;
}

INLINE DEV u32a* buf_ptr(Corpus H, Loc loc, u32 i) {
  return (DEV u32a*)(H + loc) + i;
}

INLINE Term blk_read(Corpus H, bool arr, Loc loc, u32 i) {
  if (arr) {
    return H[loc + i];
  }
  return (u64)*buf_ptr(H, loc, i);
}

INLINE void blk_write(Corpus H, bool arr, Loc loc, u32 i, Term v) {
  if (arr) {
    H[loc + i] = v;
  } else {
    *buf_ptr(H, loc, i) = (u32)v;
  }
}

INLINE Term buf_new(Env e, Nat d, Term v) {
  if (d > 31) {
    err_post(e.mem, ERR_NATS);
    d = 0;
  }
  Cls c = (u32)d;
  Loc n = heap_alloc(e, buf_wcls(c));
  if (loc_doomed(n)) {
    return term_buf(0, n);
  }
  for (u64 i = 0; i < (1ull << buf_wcls(c)); i += 1) {
    e.mem[n + i] = (u64)(u32)v * 0x100000001ull;
  }
  return term_buf(c, n);
}

INLINE u32 blk_at(Env e, Term a, U32 i) {
  return (u32)i & (u32)((1ull << blk_cls(e, a)) - 1);
}

INLINE Term buf_read(Env e, Term a, U32 i) {
  return blk_read(e.mem, 0, term_loc(a), blk_at(e, a, i));
}

INLINE Term blk_cow(Env e, Term a) {
  return term_rfc(a) ? rfc_open(e, a) : a;
}

INLINE Term blk_leaf(Env e, Term v) {
  Loc loc = heap_alloc(e, 0);
  e.mem[loc] = rfc_seal(e, v);
  return term_blk(1, 0, loc);
}

INLINE Term blk_node(Env e, Term l, Term r) {
  Corpus H = e.mem;
  l = blk_cow(e, l);
  r = blk_cow(e, r);
  bool arr = term_tag(l) == TAG_ARR;
  Cls c = blk_cls(e, l);
  if (c != blk_cls(e, r) || c > 30) {
    err_post(H, ERR_TAGS);
    return l;
  }
  Loc n = heap_alloc(e, c + arr);
  if (loc_doomed(n)) {
    return term_buf(0, n);
  }
  for (u32 w = 0; w < (1u << c); w += 1) {
    blk_write(H, arr, n, 2 * w, blk_read(H, arr, term_loc(l), w));
    blk_write(H, arr, n, 2 * w + 1, blk_read(H, arr, term_loc(r), w));
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
  Loc n  = heap_alloc(e, arr ? c : buf_wcls(c));
  if (loc_doomed(n)) {
    return term_buf(0, n);
  }
  for (u32 i = 0; i < (1u << c); i += 1) {
    blk_write(H, arr, n, i, blk_read(H, arr, pa, 2 * i + hi));
  }
  return term_blk(arr, c, n);
}

INLINE Term blk_rest(Env e, Term a) {
  Term r = blk_half(e, a, 1);
  blk_free(e, a);
  return r;
}

INLINE Term blk_take(Env e, Term a) {
  Term v = blk_read(e.mem, term_tag(a) == TAG_ARR, term_loc(a), 0);
  heap_free(e, 0, term_loc(a));
  return v;
}

INLINE Term blk_give(Env e, bool arr, Term a, U32 i, Term v) {
  u32 at = blk_at(e, a, i);
  if (arr) {
    v = rfc_seal(e, v);
  }
  Term old = blk_read(e.mem, arr, term_loc(a), at);
  blk_write(e.mem, arr, term_loc(a), at, v);
  return old;
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

INLINE bool reply_runs(Corpus H, Reply r) {
  return (u32)H[task_tail(r) + 1] == 0;
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

INLINE bool root_done(Corpus H) {
  return a32_load_acq(a32_at(H, H_ROOT_DONE)) != 0;
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

// Stack
// =====

#ifdef __METAL_VERSION__
#define WL_ROOM(N) \
  if (sp + (N) * CUBE > e.mem + STAK_OFF + e.mnk + CUBE * STAK_LEN) { \
    err_post(e.mem, ERR_DEEP); \
    return 0; \
  }
#else
#define WL_ROOM(N)
#endif

// Code
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
#ifdef __METAL_VERSION__
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
    if (cont != TERM_HOLE && fid_seqk((u32)term_aux(cont)) && !page_park(e)) {
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

#ifdef __METAL_VERSION__
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

INLINE bool monk_run(Env e, Stk stk, Term t, bool seq, u32 base, u32 stride,
  Cursor cur) {
  u32 spin = 0;
  for (;;) {
    Reply r = work_loop(e, stk, t, seq);
    if (r == 0) {
      return false;
    }
    if (reply_runs(e.mem, r)) {
      if (err_spun(e.mem, &spin, ERR_TICK)) {
        return false;
      }
      if ((DEVICE && stride != 0) || page_park(e)) {
        ring_push(e.mem, ring_pick(base, stride, cur), r);
        return false;
      }
      t   = r;
      seq = false;
      continue;
    }
    task_deal(e.mem, r, base, stride, cur);
    return true;
  }
}

INLINE bool monk_grow(Env e, Stk stk, Ring rg, u32 put0, u32 base, u32 stride,
  Cursor cur) {
  Corpus H = e.mem;
  if (*ring_get(H, rg) == put0) {
    return false;
  }
  Term t = ring_head(H, rg);
  if (t == 0 || fid_nofk((u32)term_aux(t)) || page_park(e)) {
    return false;
  }
  ring_skip(H, rg);
  return monk_run(e, stk, t, false, base, stride, cur);
}

static void monk_work(Env e, Stk stk, Monk m) {
  Corpus H = e.mem;
#ifdef __METAL_VERSION__
  u32 put0 = a32_load(ring_put(H, m));
#else
  u32 put0 = (u32)*monk_word(H, m, M_SNAP);
#endif
  while (*ring_get(H, m) != put0) {
    if (err_seen(H) || page_park(e)) {
      return;
    }
    Term t = ring_head(H, m);
    if (t == 0) {
      continue;
    }
    ring_skip(H, m);
    monk_run(e, stk, t, !page_tight(H, 2), m, 0, (Cursor)0);
  }
}

#ifdef __METAL_VERSION__

kernel void grow_dev(Corpus H [[buffer(0)]],
  u32 grids [[threadgroups_per_grid]],
  u32 row [[threadgroup_position_in_grid]],
  u32 lane [[thread_position_in_threadgroup]]) {
  u32  stride = grids == 1 ? CUBE_SIDE : 1;
  Ring rg  = (row << 7) + stride * lane;
  threadgroup u64 tg_alc[CUBE_SIDE * ALC_WORDS];
  Env  e   = { H, rg, tg_alc + lane };
  alc_open(e);
  threadgroup atomic_uint tg_cur;
  threadgroup atomic_uint tg_grew;
  threadgroup atomic_uint tg_has;
  atomic_store_explicit(&tg_cur, 0, RLX);
  atomic_store_explicit(&tg_grew, 0, RLX);
  atomic_store_explicit(&tg_has, 0, RLX);
  threadgroup_barrier(mem_flags::mem_threadgroup);
  u32 seen_has  = 0;
  u32 seen_grew = 0;
  for (;;) {
    u32 put0 = a32_load(ring_put(H, rg));
    u32 vote = put0 != a32_load(ring_get(H, rg));
    if (lane == 0 && (err_seen(H) || root_done(H))) {
      vote = CUBE_SIDE;
    }
    atomic_fetch_add_explicit(&tg_has, vote, RLX);
    threadgroup_barrier(mem_flags::mem_threadgroup);
    u32 has = atomic_load_explicit(&tg_has, RLX);
    if (has - seen_has >= CUBE_SIDE) {
      break;
    }
    seen_has = has;
    if (monk_grow(e, H + STAK_OFF + rg, rg, put0, row << 7, stride, &tg_cur)) {
      atomic_fetch_add_explicit(&tg_grew, 1, RLX);
    }
    threadgroup_barrier(mem_flags::mem_device | mem_flags::mem_threadgroup);
    u32 grew = atomic_load_explicit(&tg_grew, RLX);
    if (grew == seen_grew) {
      break;
    }
    seen_grew = grew;
  }
  alc_close(e);
}

kernel void work_dev(Corpus H [[buffer(0)]],
  u32 tid [[thread_position_in_grid]],
  u32 lane [[thread_position_in_threadgroup]]) {
  threadgroup u64 tg_alc[CUBE_SIDE * ALC_WORDS];
  Env e = { H, tid, tg_alc + lane };
  alc_open(e);
  monk_work(e, H + STAK_OFF + tid, ring_flip(tid));
  alc_close(e);
}

#endif

#ifndef __METAL_VERSION__

// Cube
// ====

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
    for (u32 i = 0; i < CUBE_SIDE; i += 1) {
      Ring rg = base + stride * i;
      grew += monk_grow(e, stk, rg, put0[i], base, stride, &cur);
    }
    if (grew == 0) {
      return;
    }
  }
}

// Pool
// ====

static Term* stack_new(void) {
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
  Term* stk  = stack_new();
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

static bool feed(Corpus H) {
  u64 need = gpu_wired == 0 ? 2 * TOME_PAGES
    : ((u64)a32_load(a32_at(H, H_PAGE_BUMP)) / TOME_PAGES + 3) * TOME_PAGES;
  if (!err_seen(H) && need <= gpu_wired) {
    return false;
  }
  u64 want = 2 * gpu_wired > need ? 2 * gpu_wired : need;
  want = want > gpu_cap ? gpu_cap : want;
  if (want <= gpu_wired) {
    return false;
  }
  gpu_buf = [gpu_dev
    newBufferWithBytesNoCopy:CORPUS
    length:(page_loc(want) * 8 + 16383) & ~16383ull
    options:MTLResourceStorageModeShared
      | MTLResourceHazardTrackingModeUntracked deallocator:nil];
  if (!gpu_buf) {
    err_fail(ERR_HEAP, "wiring failed");
  }
  gpu_wired = want;
  a32_store(a32_at(H, H_PAGE_CAP), (u32)gpu_cap);
  a32_store(a32_at(H, H_TOME_WIRED), (u32)want);
  return true;
}

static u64 gpu_reserve(void) {
  u64 span = [gpu_dev recommendedMaxWorkingSetSize];
  u64 most = [gpu_dev maxBufferLength];
  span = span < most ? span : most;
  if (span < page_loc(2 * TOME_PAGES) * 8) {
    err_fail(ERR_HEAP, "device too small");
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
  return span / 8;
}

static void gpu_kernel(id<MTLComputeCommandEncoder> enc,
  id<MTLComputePipelineState> pso, u32 groups) {
  [enc setComputePipelineState:pso];
  [enc setBuffer:gpu_buf offset:0 atIndex:0];
  [enc dispatchThreadgroups:MTLSizeMake(groups, 1, 1)
    threadsPerThreadgroup:MTLSizeMake(CUBE_SIDE, 1, 1)];
  [enc memoryBarrierWithScope:MTLBarrierScopeBuffers];
}

static bool gpu_round(Corpus H, u32 f) {
  feed(H);
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
  u32 ec = a32_load(a32_at(H, H_ERROR_CODE));
  if (ec && ec != ERR_HEAP) {
    err_fail(ec, ec == ERR_DEEP ? "device stack exceeded" : "device error");
  }
  return ec;
}

#else

#define gpu_probe()   false
#define gpu_reserve() 0

#endif

// Driver
// ======

static void cube_run(Corpus H, bool metal) {
  for (;;) {
    u32 f = a32_load(a32_at(H, H_CURSOR));
    a32_store(a32_at(H, H_CURSOR), 0);
    if (root_done(H)) {
      return;
    }
    if (f == 0) {
      err_fail(ERR_LEAK, "frontier drained without a result");
    }
    if (metal) {
      #if BEND_METAL
      if (gpu_round(H, f)) {
        return;
      }
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

static void corpus_seed(Corpus H) {
  u64 doom = term_ctr(0, HEAP_OFF);
  u64 lone = PAGE_NIL;
  memset_pattern8(H + HEAP_OFF, &doom, DOOM_WORDS * 8);
  memset_pattern8(H + H_HUGE_FREE, &lone, HUGE_CLS * 8);
  H[H_PAGE_BUMP] = DOOM_WORDS >> PAGE_BITS;
}

static Corpus corpus_setup(bool metal, long threads) {
  u64 span = metal ? gpu_reserve() : 1ull << 40;
  CORPUS = mmap(NULL, span * 8, PROT_READ | PROT_WRITE,
    MAP_PRIVATE | MAP_ANON | MAP_NORESERVE, -1, 0);
  if (CORPUS == MAP_FAILED) {
    err_fail(ERR_HEAP, "corpus reservation failed");
  }
  Corpus H = CORPUS;
  corpus_seed(H);
  u64 cap = (span - HEAP_OFF) >> PAGE_BITS;
  if (cap > PAGE_NIL) {
    cap = PAGE_NIL;
  }
  a32_store(a32_at(H, H_PAGE_CAP), (u32)cap);
#if BEND_METAL
  gpu_cap = cap;
#endif
  pool_size = (u32)(threads < CUBE_SIDE ? threads : CUBE_SIDE);
  return H;
}

#if BEND_METAL

static Term corpus_wake(Env e) {
  Corpus H = e.mem;
  if (!feed(H)) {
    err_fail(ERR_HEAP, "device out of memory");
  }
  memset(ALC, 0, sizeof(ALC));
  memset(H + MONK_OFF, 0, (STAK_OFF - MONK_OFF) * 8);
  memset(H + H_ROOT_WORD, 0, 72);
  corpus_seed(H);
  return term_tsk(FID_MAIN, task_node(e, FID_MAIN, TERM_HOLE, 0, 0));
}

#endif

static Term root_take(Corpus H) {
  Term v = H[H_ROOT_WORD];
  a32_store(a32_at(H, H_ROOT_DONE), 0);
  return v;
}

OUTLINE Term corpus_eval(Corpus H, bool fresh, Term t) {
  Env e = { H, 0 };
  for (;;) {
    Reply r = work_loop(e, io_stk, t, false);
    if (r == 0) {
      if (root_done(H)) {
        break;
      }
      err_fail(ERR_LEAK, "solo delivery lost");
    }
    if (reply_runs(H, r)) {
      t = r;
      if (io_metal && fid_bangs((u32)term_aux(t))) {
        Loc  tl   = task_tail(t);
        Term cont = H[tl];
        u32  idx  = (u32)(H[tl + 1] >> 32);
        H[tl]     = TERM_HOLE;
        H[tl + 1] = 0;
        a32_store(a32_at(H, H_CURSOR), 1);
        ring_push(H, 0, t);
        cube_run(H, true);
        #if BEND_METAL
        if (err_seen(H)) {
          if (!fresh) {
            err_fail(ERR_HEAP, "device out of memory");
          }
          t = corpus_wake(e);
          continue;
        }
        #endif
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

// Main
// ====

OUTLINE int io_loop(Corpus H, bool metal, Fid fid) {
  Env e = { H, 0 };
  io_metal = metal;
  io_stk = stack_new();
  Term op = corpus_eval(H, true,
    term_tsk(fid, task_node(e, fid, TERM_HOLE, 0, 0)));
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
      op = corpus_eval(H, false, term_tsk(c, a));
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

int main(int argc, char** argv) {
  long thr = 0;
  int  par = -1;
  int  gpu = -1;
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
  bool metal = gpu != 0 && gpu_probe();
  if (gpu == 1 && !metal) {
    cli_fail("--gpu on, but this binary found no Metal device", NULL);
  }
  long ncpu = sysconf(_SC_NPROCESSORS_ONLN);
  long dflt = ncpu > 0 ? ncpu : 1;
  Corpus H  = corpus_setup(metal, thr > 0 ? thr : dflt);
  int code  = io_loop(H, metal, FID_MAIN);
  io_sync();
  return code;
}

#endif
`.slice(1);

// RuntimeJs
// =========

const RUNTIME: string = String.raw`
// Word
// ====

function word_to_u32(w) {
  let x = 0;
  for (let i = 0; w.$ === "WCon"; i++) {
    x |= (w.$0 ? 1 : 0) << i;
    w = w.$1;
  }
  return x >>> 0;
}

// Cmp
// ===

function cmp_new(a, b) {
  if (a < b) {
    return {$: "LT"};
  }
  if (a === b) {
    return {$: "EQ"};
  }
  return {$: "GT"};
}

// U32
// ===

function u32_to_word(x) {
  let w = {$: "WNil"};
  for (let i = 31; i >= 0; i--) {
    w = {$: "WCon", $0: ((x >>> i) & 1) === 1, $1: w};
  }
  return w;
}

// Char
// ====

function char_new(code) {
  if (code > 0x10FFFF || (code >= 0xD800 && code <= 0xDFFF)) {
    throw new Error("char_new: " + code + " is not a Unicode scalar value");
  }
  return String.fromCodePoint(code);
}

// Array
// =====

function array_get(a, i) {
  let x = a;
  while (x.$ === "ANode") {
    x = (i & 1) === 0 ? x.$0 : x.$1;
    i = i >>> 1;
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

function array_swap(a, i, v) {
  if (a.$ === "ALeaf") {
    return {$: "Tuple", $0: {$: "ALeaf", $0: v}, $1: a.$0};
  }
  if ((i & 1) === 0) {
    const r = array_swap(a.$0, i >>> 1, v);
    return {$: "Tuple", $0: {$: "ANode", $0: r.$0, $1: a.$1}, $1: r.$1};
  }
  const r = array_swap(a.$1, i >>> 1, v);
  return {$: "Tuple", $0: {$: "ANode", $0: a.$0, $1: r.$0}, $1: r.$1};
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

function cli_help() {
  const text = [
    "usage: " + process.argv[1] + " [options]",
    "  --threads N        worker threads: a JS program runs one",
    "  --parallel on|off  off means one thread and no GPU (default: on)",
    "  --gpu on|off       send ! calls to the GPU (default: on if present)",
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
    } else {
      cli_fail("unknown option " + a);
    }
  }
  if (par === 0 && (gpu === 1 || thr > 1)) {
    cli_fail("--parallel off means --threads 1 with --gpu off");
  }
  if (gpu === 1) {
    cli_fail("--gpu on, but this binary found no Metal device");
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

// Main
// ====

// Constants
// =========

const USAGE = "usage: bend <file.bend> [--to <out.c|out.js>]";

// CLI
// ===

function cli(): void {
  const [path, flag, to] = process.argv.slice(2);
  if (path === undefined || path === "--help") {
    console.log(USAGE);
    process.exit(path === undefined ? 1 : 0);
  }
  if (path.startsWith("--")) {
    cli_fail("unknown option " + path);
  }
  if (flag !== undefined && flag !== "--to") {
    cli_fail("unknown option " + flag);
  }
  if (flag === "--to" && to === undefined) {
    cli_fail("--to needs an output file");
  }
  if (to !== undefined && !to.endsWith(".c") && !to.endsWith(".js")) {
    cli_fail("--to expects a .c or a .js file, not " + to);
  }
  if (process.argv.length > 5) {
    cli_fail("too many arguments");
  }

  const book = book_nil();
  try {
    book_load(book, path, "", new Map());
    book_valid(book);
    if (to !== undefined) {
      const emit = to.endsWith(".c") ? compile_book : js_book;
      fs.writeFileSync(to, emit(book));
    } else if (book.tlds["main"] !== undefined) {
      if (io_type(book) !== null) {
        process.exit(io_run(book));
      } else {
        const snf = term_snf(book, Ref("main"));
        console.log(term_show(term_lower(snf)));
      }
    }
  } catch (e) {
    if (e !== null && typeof e === "object" && (e as Err).$ === "Err") {
      console.log(err_show(e as Err));
    } else {
      console.log(String(e));
    }
    process.exit(1);
  }
}

function cli_fail(msg: string): never {
  console.error("bend: " + msg + "\n" + USAGE);
  process.exit(1);
}

if (import.meta.main) {
  cli();
}
