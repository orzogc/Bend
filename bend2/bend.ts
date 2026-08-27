// Bend// ====
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
//   | Ann ::= "{" Term ":" Term "}"
//   | Typ ::= "Type"
//   | All ::= "@" Bind "->" Term
//   | Lam ::= Name "=>" Body
//   | App ::= Term "(" [Term ","?] ")"
//   | ADT ::= Name "<" [Term ","?] ">"
//   | Ctr ::= Name "{" [Term ","?] "}"
//   | Mat ::= "\" "{" Name ":" Term ";"? Term "}"
//   | Efq ::= "\" "{" "}"
//   | Eql ::= "{" Term "==" Term ":" Term "}"
//   | Rfl ::= "{" "==" "}"
//   | Rwt ::= "%" (Name "@")? Term ":" Term ";"? Body
//   | Cop ::= "+" Term ("~" Term)?
//   | Grp ::= "(" Body ")"
//
// Case   ::= "case" [Term] ":" Body
// Match  ::= "match" [Term] ":" [Case]
// Local  ::= (Quant Name | Term)+ "=" Term+ ";"? Body
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
// juxtaposition laws: a call or index suffix may be spaced but a
// newline ends the spine. after a term, "<" takes one argument above
// comparison level, then one token decides: ">" or "," commits to
// type args (x<y>, X<A, B>), anything else is less-than -- so a
// compound FIRST type argument needs parens (X<(A & B), C>; later
// arguments are full terms). a glued
// ">"-headed operator never fires -- space your comparisons and
// shifts -- so nested closers stack (List<List<A>>). "-" or "+" glued
// to a name heads a binder or literal, never an operator. statements
// live in bodies: a def body, a case body, a lambda body, an if
// branch, a fork or rewrite tail; parens hold one body, or a tuple.
// a parallel let "x y z = a b c" is one Let binding n names to n
// values, each checked in the outer scope; the compiler forks its
// calls. the parser never rewinds: one token after a parsed term
// decides.
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
// do M<ls.., R>: desugars onto M.bind(ls.., A, R, v, x => ..) and
// M.pure(ls.., R, e); an empty list (do M<>:) drops R from both.
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
// needs a Cop type + T ~ C, well-formed iff C : Copiable(T); Sigma,
// Copy and Copiable are locked in book_valid.
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

import { readFileSync, realpathSync } from "node:fs";
import { fileURLToPath } from "node:url";

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
export type LetsOf<B> = BodyOf<B> extends Function ? (xs: TermOf<B>[]) => TermOf<B> : BodyOf<B>;
export type TermOf<B> = (
  | { $: "Var"; k: Name; i: number; v?: TermOf<B> }                                // x
  | { $: "Ref"; k: Name; b?: Bool }                                                // x
  | { $: "Sub"; i: number; v: TermOf<B>; f: TermOf<B> }                            // x <- v; f
  | { $: "Let"; k: Name[]; i: number[]; q: Quant[]; v: TermOf<B>[]; f: LetsOf<B> } // x y = v w; f
  | { $: "Typ" }                                                                   // Type
  | { $: "All"; q: Quant; k: Name; i: number; A: TermOf<B>; B: BodyOf<B> }         // @x:A -> B
  | { $: "Lam"; k: Name; i: number; f: BodyOf<B> }                                 // x => f
  | { $: "App"; f: TermOf<B>; x: TermOf<B> }                                       // f(x)
  | { $: "ADT"; k: Name; x: TermOf<B>[]; r: Name[] }                               // A<x0,x1,...>
  | { $: "Ctr"; k: Name; x: TermOf<B>[] }                                          // A{x0,x1,...}
  | { $: "Mat"; k: Name; h: TermOf<B>; m: TermOf<B> }                              // \{A: h; m}
  | { $: "Efq" }                                                                   // \{}
  | { $: "Eql"; a: TermOf<B>; b: TermOf<B>; T: TermOf<B> }                         // {a == b : T}
  | { $: "Rfl" }                                                                   // {==}
  | { $: "Rwt"; e: TermOf<B>; p: TermOf<B>; f: TermOf<B> }                         // %e@E : P; f (p = _ => e => P)
  | { $: "Cop"; T: TermOf<B>; c: TermOf<B> }                                       // + T ~ c
  | { $: "Ann"; x: TermOf<B>; T: TermOf<B> }                                       // {x : T}
  | { $: "Laz"; f: () => TermOf<B>; x?: TermOf<B>; v?: TermOf<B> }                 // x
) & { s?: Span };

export type LTerm = TermOf<[LTerm]>;
export type HBody = (x: HTerm) => HTerm;
export type HTerm = TermOf<HBody>;

// Env
export type Env = PMap<HTerm>;

// Fill
export type Vars = { x: HTerm; up: Vars } | null;
export type Fill = HTerm | ((vs: Vars) => HTerm);

// Definitions & Book
export type Ctr  = { k: Name; n: number; T: HTerm }
export type Ctrs = Array<Ctr>;
export type ADT  = { $: "ADT"; n: number; T: HTerm; c: Ctrs; };
export type Def  = { $: "Def"; n: number; T: HTerm; v: HTerm | null; e?: HTerm; b?: Bool; i?: string[]; };
export type TLD  = ADT | Def;
export type Book = { tlds: Record<Name, TLD>; ctrs: Record<Name, Ctr>; order: Name[]; };

// Context
export type Ann = { q: Quant; k: Name; T: HTerm };
export type Ctx = PMap<Ann>;

// Body
export type PVar  = { $: "PVar"; k: Name; i: number; s?: Span };
export type PCtr  = { $: "PCtr"; k: Name; x: Patt[]; s?: Span };
export type Patt  = PVar | PCtr;
export type Case  = { p: Patt[]; f: Body };
export type Rows  = Array<Case>;
export type Match = { $: "Match"; e: LTerm[]; r: Rows; s?: Span };
export type Local = { $: "Local"; k: Patt[]; q: Quant; v: LTerm[]; f: Body };
export type Reply = { $: "Reply"; x: LTerm; s?: Span };
export type Body  = Match | Local | Reply

// Parser
export type Loc   = number;
export type Scope = { stk: Array<[Name, number]>; frs: number; };
export type Parse = { book: Book; dir: string; str: string; pos: Loc; sc: Scope; ns: string; };
export type Span  = { src: string; beg: Loc; end: Loc; };

// Machine
export type LHS   = { t: HTerm; n: number; def: Name; qs: Quant[] };
export type Frame =
  | { $: "APP"; x: HTerm } // _(x)
  | { $: "MAT"; t: Extract<HTerm, { $: "Mat" }>; e: HTerm; lhs: { t: HTerm; n: number } | null } // \{c:h;m}(_)
  | { $: "LAZ"; l: Extract<HTerm, { $: "Laz" }> } // a thunk being filled

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

export function Let(k: Name[], i: number[], v: LTerm[], f: LTerm, s?: Span, q?: Quant[]): LTerm;
export function Let(k: Name[], i: number[], v: HTerm[], f: (xs: HTerm[]) => HTerm, s?: Span, q?: Quant[]): HTerm;
export function Let(k: Name[], i: number[], v: LTerm[] | HTerm[], f: LTerm | ((xs: HTerm[]) => HTerm), s?: Span, q?: Quant[]): LTerm | HTerm {
  return { $: "Let", k, i, q: q ?? k.map(() => Lone()), v, f, s } as LTerm;
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
  const n = c.charCodeAt(0);
  return (n >= 65 && n <= 90) || (n >= 97 && n <= 122) || n === 95;
}

export function char_is_name(c: string): boolean {
  const n = c.charCodeAt(0);
  return (n >= 65 && n <= 90) || (n >= 97 && n <= 122)
    || (n >= 48 && n <= 57) || n === 95 || n === 46;
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
  return q.$ !== "Many" || term_wnf(book, A).$ === "Cop";
}

export function quant_used(book: Book, ctx: Ctx, k: Name, q: Quant, u: Quant, s: Span | undefined, def?: Name): void {
  if (quant_join(u, q).$ !== q.$) {
    const obs = u.$ === "Many" ? k + " (consumed more than once)" : quant_show(u) + k;
    throw Err(book, ctx, quant_show(q) + k, obs, s, def);
  }
}

// Uses
// ====

export function uses_nil(): Uses {
  return Emp<Quant>();
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
      return lhs_ext(lhs, k, n - 1, [...xs, x]);
    });
  }
}

// Loop
// ====

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
  if (t.$ !== "Laz") {
    return t;
  }
  if (t.v === undefined) {
    t.v = term_force(t.f());
    t.x = undefined;
  }
  return t.v;
}

export function term_strip<X>(tm: TermOf<X>): TermOf<X> {
  let t = term_force(tm);
  while (t.$ === "Ann") {
    t = term_force(t.x);
  }
  return t;
}

export function term_higher(tm: LTerm, env: Env): HTerm {
  const sc: number[] = [];
  function at(m: Fill, vs: Vars): HTerm {
    if (typeof m === "function") {
      return m(vs);
    } else {
      return m;
    }
  }
  function under(is: number[], f: LTerm): Fill {
    for (const i of is) {
      sc.push(i);
    }
    const m = go(f);
    sc.length -= is.length;
    return m;
  }
  function mk(xs: Fill[], f: (ys: HTerm[]) => HTerm): Fill {
    if (xs.every((m) => typeof m !== "function")) {
      return f(xs as HTerm[]);
    }
    return (vs: Vars) => {
      const ys = new Array<HTerm>(xs.length);
      for (let j = 0; j < xs.length; j++) {
        ys[j] = at(xs[j], vs);
      }
      return f(ys);
    };
  }
  function go(t: LTerm): Fill {
    switch (t.$) {
      case "Var": {
        const idx = sc.lastIndexOf(t.i);
        if (idx < 0) {
          const v = pmap_get(env, t.i);
          if (v === null) {
            return Ref(t.k, t.s);
          } else {
            return v;
          }
        }
        const d = sc.length - 1 - idx;
        return (vs: Vars) => {
          let p = vs as { x: HTerm; up: Vars };
          for (let j = 0; j < d; j++) {
            p = p.up as { x: HTerm; up: Vars };
          }
          return p.x;
        };
      }
      case "Ref": {
        return Ref(t.k, t.s, t.b);
      }
      case "Sub": {
        const v = go(t.v);
        const m = under([t.i], t.f);
        return (vs: Vars) => at(m, { x: at(v, vs), up: vs });
      }
      case "Let": {
        const ws = t.v.map(go);
        const m = under(t.i, t.f);
        return (vs: Vars) => Let(t.k, t.i, ws.map((w) => at(w, vs)), (xs: HTerm[]) => {
          let up = vs;
          for (const x of xs) {
            up = { x, up };
          }
          return at(m, up);
        }, t.s, t.q);
      }
      case "Typ": {
        return Typ(t.s);
      }
      case "All": {
        const A = go(t.A);
        const m = under([t.i], t.B);
        return (vs: Vars) => All(t.q, t.k, t.i, at(A, vs), (x: HTerm) => at(m, { x, up: vs }), t.s);
      }
      case "Lam": {
        const m = under([t.i], t.f);
        return (vs: Vars) => Lam(t.k, t.i, (x: HTerm) => at(m, { x, up: vs }), t.s);
      }
      case "App": {
        const f = go(t.f);
        const x = go(t.x);
        if (typeof f !== "function" && typeof x !== "function") {
          return App(f, x, t.s);
        }
        return (vs: Vars) => App(at(f, vs), at(x, vs), t.s);
      }
      case "ADT": {
        const out = mk(t.x.map(go), (ys) => ADT(t.k, ys, t.s, t.r));
        return out;
      }
      case "Ctr": {
        const out = mk(t.x.map(go), (ys) => Ctr(t.k, ys, t.s));
        return out;
      }
      case "Mat": {
        const out = mk([go(t.h), go(t.m)], (ys) => Mat(t.k, ys[0], ys[1], t.s));
        return out;
      }
      case "Efq": {
        return Efq(t.s);
      }
      case "Eql": {
        const out = mk([go(t.a), go(t.b), go(t.T)], (ys) => Eql(ys[0], ys[1], ys[2], t.s));
        return out;
      }
      case "Rfl": {
        return Rfl(t.s);
      }
      case "Rwt": {
        const out = mk([go(t.e), go(t.p), go(t.f)], (ys) => Rwt(ys[0], ys[1], ys[2], t.s));
        return out;
      }
      case "Cop": {
        const out = mk([go(t.T), go(t.c)], (ys) => Cop(ys[0], ys[1], t.s));
        return out;
      }
      case "Ann": {
        const out = mk([go(t.x), go(t.T)], (ys) => Ann(ys[0], ys[1], t.s));
        return out;
      }
      case "Laz": {
        const out = go(term_force(t));
        return out;
      }
    }
  }
  const m = go(tm);
  return at(m, null);
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
        const b  = tm;
        const xs = b.k.map((k, j): HTerm => Var(k, d + j, undefined, b.v[j]));
        const vs: LTerm[] = [];
        for (const v of b.v) {
          vs.push(yield [v, d]);
        }
        return Let(b.k, xs.map((_, j) => d + j), vs, yield [b.f(xs), d + b.k.length], b.s, b.q);
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
  return { tlds: Object.create(null), ctrs: Object.create(null), order: [] };
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

const BASE_BEND = realpathSync(fileURLToPath(new URL("./base.bend", import.meta.url)));

export function book_load(book: Book, file: string, ns: string, seen: Map<string, string | null>): void {
  const real = realpathSync(file);
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
  const lines = readFileSync(file, "utf8").split("\n");
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i].trim();
    const m = line.match(/^import(\s.*|)$/);
    if (m !== null) {
      const h = m[1].match(/^\s+(\S+)(?:\s+as\s+([A-Za-z_][A-Za-z0-9_]*))?\s*(?:#.*)?$/);
      if (h === null || (h[2] === undefined && h[1] !== "Base")) {
        throw Err(book, ctx_nil(), "an import ('import Base', or 'import <path> as <Name>')");
      }
      if (h[2] === undefined) {
        book_load(book, BASE_BEND, "", seen);
      } else {
        book_load(book, h[1].startsWith("/") ? h[1] : dir + h[1], h[2], seen);
      }
      lines[i] = "";
      continue;
    }
    if (line !== "" && !line.startsWith("#")) {
      break;
    }
  }
  const n0 = book.order.length;
  parse_book(book, dir, lines.join("\n"), ns);
  if (real === BASE_BEND) {
    for (const k of book.order.slice(n0)) {
      const tld = book.tlds[k];
      if (tld.$ === "Def") {
        tld.b = true;
      }
    }
  }
  seen.set(real, ns);
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
  const t = term_strip(tm);
  if (t.$ !== "Ctr" || t.k !== "U32" || t.x.length !== 1) {
    return null;
  }
  let n = 0;
  let i = 0;
  let w = term_strip(t.x[0]);
  while (w.$ === "Ctr" && w.k === "WCon" && w.x.length === 2) {
    const b = term_strip(w.x[0]);
    if (b.$ !== "Ctr" || b.x.length !== 0 || (b.k !== "True" && b.k !== "False")) {
      return null;
    }
    if (b.k === "True") {
      n += 2 ** i;
    }
    i += 1;
    w = term_strip(w.x[1]);
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
        const vs: string[] = [];
        for (const v of tm.v) {
          vs.push(yield [v, 1]);
        }
        for (const k of tm.k) {
          bnd.push(k);
        }
        const f = yield [tm.f, 0];
        bnd.length -= tm.k.length;
        const ks = tm.k.map((k, j) => quant_show(tm.q[j]) + k);
        const s  = ks.join(" ") + " = " + vs.join(" ") + "; " + f;
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
  const at  = s.src.slice(0, s.beg).split("\n").length;
  const beg = Math.max(1, at - 1);
  const end = Math.min(lns.length, at + 1);
  const out: string[] = [];
  for (let lin = beg; lin <= end; lin++) {
    const bar = lin === at ? ">| " : " | ";
    out.push(String(lin).padStart(String(end).length) + bar + (lns[lin - 1] ?? ""));
  }
  return out.join("\n");
}

export function err_show(err: Err): string {
  const bnd = ctx_scope(err.ctx);
  const msg = err.obs === undefined
    ? "\n- message  : " + expr_show(err.bok, err.exp, bnd)
    : "\n- expected : " + expr_show(err.bok, err.exp, bnd)
    + "\n- observed : " + expr_show(err.bok, err.obs, bnd);
  const def = err.def === undefined ? "" : " " + err.def;
  const spn = err.spn === undefined ? "" : "\n" + span_show(err.spn);
  const loc = def === "" && spn === "" ? "" : "\nLocation:" + def + spn;
  return "Error:" + msg + ctx_show(err.bok, err.ctx) + loc;
}

// Parse
// =====

const KEYWORDS = new Set([
  "def", "type", "match", "case", "do",
  "return", "Type",
]);

export function parse_new(book: Book, dir: string, str: string, ns: string = ""): Parse {
  return { book, dir, str, pos: 0, sc: { stk: [], frs: 0 }, ns };
}

export function parse_col(src: string, pos: Loc): number {
  return pos - src.lastIndexOf("\n", pos - 1);
}

export function parse_span(p: Parse, beg: Loc): Span {
  return { src: p.str, beg, end: p.pos };
}

export function parse_fail(p: Parse, exp: string): never {
  const obs = p.pos < p.str.length ? "'" + p.str[p.pos] + "'" : "end of input";
  throw Err(p.book, ctx_nil(), exp, obs, { src: p.str, beg: p.pos, end: p.pos });
}

export function parse_peek(p: Parse): string {
  return p.pos < p.str.length ? p.str[p.pos] : "";
}

export function parse_bump(p: Parse): string {
  const c = parse_peek(p);
  p.pos += 1;
  return c;
}

export function parse_at(p: Parse, s: string): boolean {
  if (p.str.charCodeAt(p.pos) !== s.charCodeAt(0)) {
    return false;
  }
  return s.length === 1 || p.str.startsWith(s, p.pos);
}

export function parse_take(p: Parse, s: string): boolean {
  if (!parse_at(p, s)) {
    return false;
  }
  p.pos += s.length;
  return true;
}

export function parse_skip(p: Parse): void {
  const s = p.str;
  while (p.pos < s.length) {
    const n = s.charCodeAt(p.pos);
    if (n === 32 || n === 10 || n === 13 || n === 9) {
      p.pos += 1;
      continue;
    }
    if (n === 35) {
      while (p.pos < s.length && s.charCodeAt(p.pos) !== 10) {
        p.pos += 1;
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
  return !char_is_name(p.str[p.pos + w.length] ?? "");
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
  const beg = p.pos;
  while (p.pos < p.str.length && char_is_name(p.str[p.pos])) {
    p.pos += 1;
  }
  const k = p.str.slice(beg, p.pos);
  if (k.endsWith(".")) {
    parse_fail(p, "a name (a name cannot end in '.')");
  }
  return k;
}

export function parse_name(p: Parse): Name {
  const k = parse_lexeme(p);
  if (KEYWORDS.has(k)) {
    parse_fail(p, "a name (got the keyword '" + k + "')");
  }
  return k;
}

const ESCAPES: Record<string, U32> = {
  "n": 10, "t": 9, "r": 13, "0": 0, "\\": 92, "'": 39, '"': 34,
};

export function parse_char(p: Parse): U32 {
  if (parse_take(p, "\\")) {
    const c = ESCAPES[parse_bump(p)];
    if (c === undefined) {
      parse_fail(p, "an escape (\\n \\t \\r \\0 \\\\ \\' \\\")");
    }
    return c;
  }
  const n = p.str.codePointAt(p.pos);
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
  const i = p.sc.frs++;
  if (k !== "_") {
    p.sc.stk.push([k, i]);
  }
  return i;
}

export function parse_close(p: Parse, n: number): void {
  p.sc.stk.length = n;
}

export function parse_lookup(p: Parse, k: Name): number | null {
  const stk = p.sc.stk;
  for (let j = stk.length - 1; j >= 0; j--) {
    if (stk[j][0] === k) {
      return stk[j][1];
    }
  }
  return null;
}

export function parse_var(p: Parse, k: Name, s?: Span): LTerm {
  const i = parse_lookup(p, k);
  if (i !== null) {
    return Var(k, i, s);
  }
  const q = parse_reso(p, k);
  if (q !== k || k.includes(".")) {
    return Ref(q, s);
  }
  return Var(k, p.sc.frs++, s);
}

export function parse_qual(p: Parse, k: Name): Name {
  return p.ns === "" ? k : p.ns + "." + k;
}

export function parse_reso(p: Parse, k: Name): Name {
  const q = parse_qual(p, k);
  if (q in p.book.tlds || q in p.book.ctrs) {
    return q;
  }
  return k;
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

export function parse_patt(p: Parse, t: LTerm): Patt {
  const book = p.book;
  switch (t.$) {
    case "Var": {
      if (book_ctr(book, parse_reso(p, t.k)) !== null) {
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
        xs.push(parse_patt(p, x));
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
  const out = parse_term_sub(p, 0);
  parse_skip(p);
  if (parse_take(p, "=>")) {
    if (out.$ !== "Var") {
      parse_fail(p, "a lambda binder (one name: k => body)");
    }
    const n0 = p.sc.stk.length;
    const i  = parse_open(p, out.k);
    const f  = parse_block(p);
    parse_close(p, n0);
    return Lam(out.k, i, f, out.s);
  }
  if (parse_take(p, "->")) {
    const B = parse_term(p);
    const s = parse_grow(p, out);
    return All(Lone(), "_", parse_open(p, "_"), out, B, s);
  }
  return out;
}

export function parse_term_sub(p: Parse, lvl: number): LTerm {
  parse_skip(p);
  const beg  = p.pos;
  const base = parse_term_base(p);
  if (base.s === undefined) {
    base.s = parse_span(p, beg);
  }
  return parse_term_ops(p, base, lvl);
}

export function parse_term_base(p: Parse): LTerm {
  parse_skip(p);
  const beg = p.pos;
  const c   = parse_peek(p);
  if (char_is_head(c)) {
    return parse_term_base_word(p, parse_lexeme(p), beg);
  }
  if (/[0-9]/.test(c)) {
    return parse_term_num(p);
  }
  switch (c) {
    case "@": {
      return parse_term_all(p);
    }
    case "&": {
      return parse_term_exi(p);
    }
    case "\\": {
      parse_bump(p);
      parse_eat(p, "{");
      return parse_term_mat(p);
    }
    case "%": {
      return parse_term_rwt(p, beg);
    }
    case "{": {
      return parse_term_brc(p);
    }
    case "(": {
      parse_bump(p);
      return parse_term_tup(p, beg);
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
      return parse_term_chr(p);
    }
    case '"': {
      return parse_term_str(p);
    }
    case "+": {
      parse_bump(p);
      return parse_term_cop(p, parse_term_sub(p, 2), beg);
    }
    default: {
      parse_fail(p, "a term");
    }
  }
}

const HEADLESS: Record<Name, string> = {
  "match" : "a term (a match heads a def body, not a term)",
  "case"  : "a match heading this case (this case is orphaned)",
  "return": "a do-block heading this return",
};

export function parse_term_base_word(p: Parse, k: Name, beg: Loc): LTerm {
  if (k === "Type") {
    return Typ(parse_span(p, beg));
  }
  if (k === "do") {
    return parse_term_do(p);
  }
  if (HEADLESS[k] !== undefined) {
    parse_fail(p, HEADLESS[k]);
  }
  if (KEYWORDS.has(k)) {
    parse_fail(p, "a term (the keyword '" + k + "' cannot head one)");
  }
  if (parse_at(p, "{")) {
    parse_bump(p);
    const xs = parse_term_args(p, "}");
    return Ctr(parse_reso(p, k), xs, parse_span(p, beg));
  }
  return parse_var(p, k, parse_span(p, beg));
}

const INFIX_OPS: Array<[string, number, Bool, Name]> = [
  ["==.",  4, false, "F32.is_eq"],
  ["!=.",  4, false, "F32.is_ne"],
  ["<=.",  4, false, "F32.is_le"],
  [">=.",  4, false, "F32.is_ge"],
  ["<.",   4, false, "F32.is_lt"],
  [">.",   4, false, "F32.is_gt"],
  [".|.",  6, false, "U32.or"],
  [".^.",  7, false, "U32.xor"],
  [".&.",  8, false, "U32.and"],
  ["+.",  10, false, "F32.add"],
  ["-.",  10, false, "F32.sub"],
  ["*.",  11, false, "F32.mul"],
  ["/.",  11, false, "F32.div"],
  ["||",   2, false, "Bool.or"],
  ["&&",   3, false, "Bool.and"],
  ["<=",   4, false, "U32.is_le"],
  [">=",   4, false, "U32.is_ge"],
  ["<>",   5, true,  ""],
  ["++",   5, true,  "String.append"],
  ["<<",   9, false, "U32.shln"],
  [">>",   9, false, "U32.shrn"],
  ["&",    1, true,  ""],
  ["|",    1, true,  ""],
  [">",    4, false, "U32.is_gt"],
  ["+n",  10, false, "Nat.add"],
  ["+",   10, false, "U32.add"],
  ["-",   10, false, "U32.sub"],
  ["*",   11, false, "U32.mul"],
  ["/",   11, false, "U32.div"],
];

export function parse_infx_find(p: Parse): [string, number, Bool, Name] | null {
  for (const op of INFIX_OPS) {
    if (!parse_at(p, op[0])) {
      continue;
    }
    const nx = p.str[p.pos + op[0].length] ?? "";
    if ((op[0] === "-" || op[0] === "+") && (nx === ">" || char_is_head(nx))) {
      continue;
    }
    if (op[0] === "+n" && char_is_name(nx)) {
      continue;
    }
    if (op[0][0] === ">" && !/\s/.test(p.str[p.pos - 1] ?? " ")) {
      continue;
    }
    return op;
  }
  return null;
}

export function parse_grow(p: Parse, t: LTerm): Span | undefined {
  if (t.s === undefined) {
    return undefined;
  }
  return parse_span(p, t.s.beg);
}

export function parse_nl(p: Parse): boolean {
  for (let j = p.pos - 1; j >= 0; j--) {
    const c = p.str[j];
    if (c === "\n") {
      return true;
    }
    if (c !== " " && c !== "\r" && c !== "\t") {
      return false;
    }
  }
  return true;
}

export function parse_term_ops(p: Parse, tm: LTerm, lvl: number): LTerm {
  let out = tm;
  while (true) {
    parse_skip(p);
    if (parse_nl(p) && (parse_at(p, "(") || parse_at(p, "["))) {
      return out;
    }
    if (parse_at(p, "!(")) {
      if (out.$ === "Var" && parse_lookup(p, out.k) === null) {
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
      const s  = parse_grow(p, out);
      for (const x of xs) {
        out = App(out, x, s);
      }
      continue;
    }
    if (parse_at(p, "[")) {
      parse_bump(p);
      const ix = parse_term(p);
      parse_eat(p, "]");
      const s = parse_grow(p, out);
      parse_skip(p);
      if (!parse_nl(p) && parse_take(p, "<-")) {
        const v = parse_term_sub(p, 2);
        out = App(App(App(Ref("Array.set", s), out, s), ix, s), v, s);
      } else {
        out = App(App(Ref("Array.get", s), out, s), ix, s);
      }
      continue;
    }
    if (parse_at(p, "<") && !"-=<.>".includes(p.str[p.pos + 1] ?? "")
      && (lvl <= 4 || /\S/.test(p.str[p.pos - 1] ?? ""))) {
      parse_bump(p);
      const a = parse_term_sub(p, 5);
      parse_skip(p);
      const s = parse_grow(p, out);
      if (parse_at(p, ">") || parse_at(p, ",")) {
        if (out.$ !== "Var" && out.$ !== "Ref") {
          parse_fail(p, "a family name before <..> (a comparison here needs parens)");
        }
        const xs = [a];
        if (!parse_take(p, ">")) {
          parse_take(p, ",");
          xs.push(...parse_term_args(p, ">"));
        }
        out = ADT(parse_reso(p, out.k), xs, s);
      } else {
        out = App(App(Ref("U32.is_lt", s), out, s), a, s);
      }
      continue;
    }
    const op = parse_infx_find(p);
    if (op === null || op[1] < lvl) {
      return out;
    }
    parse_take(p, op[0]);
    const b = parse_term_sub(p, op[2] ? op[1] : op[1] + 1);
    const s = parse_grow(p, out);
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

export function parse_term_cop(p: Parse, T: LTerm, beg: Loc): LTerm {
  parse_skip(p);
  const c = parse_take(p, "~") ? parse_term_sub(p, 2) : parse_term_cop_wit(p, T);
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
  while (true) {
    parse_skip(p);
    if (parse_take(p, close)) {
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
  const A = parse_term_sub(p, 0);
  parse_eat(p, "->");
  const n0 = p.sc.stk.length;
  const i  = parse_open(p, k);
  const B  = parse_term(p);
  parse_close(p, n0);
  return All(q, k, i, A, B);
}

export function parse_term_exi(p: Parse): LTerm {
  parse_bump(p);
  const k = parse_name(p);
  parse_eat(p, ":");
  const A = parse_term_sub(p, 0);
  parse_skip(p);
  parse_eat(p, "->");
  const n0 = p.sc.stk.length;
  const i  = parse_open(p, k);
  const B  = parse_term(p);
  parse_close(p, n0);
  return ADT("Sigma", [A, Lam(k, i, B)]);
}

export function parse_term_tup(p: Parse, beg: Loc): LTerm {
  parse_skip(p);
  const b = parse_body(p, parse_col(p.str, p.pos) - 1);
  parse_skip(p);
  if (b.$ === "Reply" && parse_take(p, ",")) {
    const rest = parse_term_tup(p, beg);
    return Ctr("Tuple", [b.x, rest], parse_span(p, beg));
  }
  const out = body_flatten(b, [], () => p.sc.frs++);
  parse_eat(p, ")");
  return out;
}

export function parse_term_mat(p: Parse): LTerm {
  const arms: Array<[Name, LTerm]> = [];
  let tail: LTerm = Efq();
  while (true) {
    parse_skip(p);
    if (parse_take(p, "}")) {
      break;
    }
    const t = parse_term(p);
    parse_skip(p);
    if ((t.$ === "Var" || t.$ === "Ref") && parse_take(p, ":")) {
      const h = parse_term(p);
      arms.push([parse_reso(p, t.k), h]);
      parse_skip(p);
      parse_take(p, ";");
      continue;
    }
    tail = t;
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
  const e0 = parse_term(p);
  parse_skip(p);
  let k = "";
  let e = e0;
  if (parse_take(p, "@")) {
    if (e0.$ !== "Var") {
      parse_fail(p, "a name before @ (a rewrite binder is one name: %e@E : P)");
    }
    k = e0.k;
    e = parse_term(p);
  }
  parse_eat(p, ":");
  const n0 = p.sc.stk.length;
  const xi = p.sc.frs++;
  p.sc.stk.push(["_", xi]);
  const ei = k === "" ? p.sc.frs++ : parse_open(p, k);
  const P  = parse_term(p);
  parse_close(p, n0);
  parse_skip(p);
  parse_take(p, ";");
  const f = parse_block(p);
  const s = parse_span(p, beg);
  return Rwt(e, Lam("_", xi, Lam(k, ei, P), s), f, s);
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
  const beg = p.pos;
  let s = "";
  while (/[0-9]/.test(parse_peek(p))) {
    s += parse_bump(p);
  }
  if (!parse_take(p, "n")) {
    if (parse_at(p, ".") && /[0-9]/.test(p.str[p.pos + 1] ?? "")) {
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
  const beg = p.pos;
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
  const beg = p.pos;
  parse_bump(p);
  const cs: U32[] = [];
  while (parse_peek(p) !== '"') {
    if (p.pos >= p.str.length) {
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
  return parse_term_do_stmt(p, m, ts.slice(0, -1), ts.length === 0 ? null : ts[ts.length - 1]);
}

export function parse_term_do_stmt(p: Parse, m: Name, ls: LTerm[], R: LTerm | null): LTerm {
  function parse_term_do_call(op: Name, xs: LTerm[], s: Span): LTerm {
    let fn: LTerm = Ref(parse_reso(p, m + "." + op), s);
    for (const l of ls) {
      fn = App(fn, l, s);
    }
    for (const x of xs) {
      fn = App(fn, x, s);
    }
    return fn;
  }
  parse_skip(p);
  const beg = p.pos;
  if (parse_word(p, "return")) {
    const e = parse_term(p);
    return parse_term_do_call("pure", R === null ? [e] : [R, e], parse_span(p, beg));
  }
  const t = parse_term(p);
  parse_skip(p);
  if (t.$ === "Var" && parse_take(p, ":")) {
    const A   = parse_term_sub(p, 0);
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
    const n0 = p.sc.stk.length;
    const i  = parse_open(p, t.k);
    const f  = parse_term_do_stmt(p, m, ls, R);
    parse_close(p, n0);
    return asg ? Let([t.k], [i], [Ann(v, A, s)], f, s) : parse_term_do_call("bind", R === null ? [A, v, Lam(t.k, i, f, s)] : [A, R, v, Lam(t.k, i, f, s)], s);
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
  return t;
}

// Body
// ----

export function parse_body(p: Parse, col: number = 0): Body {
  parse_skip(p);
  const beg = p.pos;
  if (parse_at_word(p, "match")) {
    return parse_match(p, col);
  }
  let q  = Lone();
  let ts: LTerm[];
  if (parse_take(p, "-")) {
    q  = None();
    ts = [Var(parse_name(p), 0, parse_span(p, beg))];
    parse_eat(p, "=");
  } else if (parse_at(p, "+")) {
    parse_bump(p);
    const t = parse_term_sub(p, 2);
    parse_skip(p);
    if (t.$ !== "Var" || !parse_at(p, "=") || parse_at(p, "==")) {
      const x = parse_term_ops(p, parse_term_cop(p, t, beg), 0);
      return { $: "Reply", x, s: parse_span(p, beg) };
    }
    parse_bump(p);
    q  = Many();
    ts = [t];
  } else {
    ts = [parse_term(p)];
    parse_skip(p);
    while (!parse_nl(p) && char_is_head(parse_peek(p)) && !parse_at_key(p)) {
      ts.push(parse_term(p));
      parse_skip(p);
    }
    if (ts.length === 1 && !(parse_at(p, "=") && !parse_at(p, "=="))) {
      return { $: "Reply", x: ts[0], s: parse_span(p, beg) };
    }
    parse_eat(p, "=");
  }
  const vs: LTerm[] = [];
  for (const _ of ts) {
    vs.push(parse_term(p));
  }
  parse_skip(p);
  parse_take(p, ";");
  const n0 = p.sc.stk.length;
  const ks = ts.map((x): Patt => {
    if (ts.length > 1 && x.$ !== "Var") {
      throw Err(p.book, ctx_nil(), "a name (a parallel let binds names; destructure in its body)", undefined, x.s);
    }
    return parse_patt(p, x);
  });
  const f = parse_body(p, col);
  parse_close(p, n0);
  return { $: "Local", k: ks, q, v: vs, f };
}

export function parse_at_key(p: Parse): boolean {
  let k = "";
  for (let j = p.pos; j < p.str.length && char_is_name(p.str[j]); j++) {
    k += p.str[j];
  }
  return KEYWORDS.has(k);
}

export function parse_block(p: Parse): LTerm {
  parse_skip(p);
  const b = parse_body(p, parse_col(p.str, p.pos) - 1);
  return body_flatten(b, [], () => p.sc.frs++);
}

export function parse_match(p: Parse, col: number): Match {
  parse_skip(p);
  const beg = p.pos;
  parse_word(p, "match");
  const es: LTerm[] = [];
  while (true) {
    const e = parse_term(p);
    es.push(e);
    parse_skip(p);
    if (parse_take(p, ":")) {
      break;
    }
    parse_take(p, ",");
  }
  parse_skip(p);
  const ccol = parse_col(p.str, p.pos);
  const rows: Rows = [];
  while (ccol > col && parse_at_word(p, "case") && parse_col(p.str, p.pos) >= ccol) {
    const rcol = parse_col(p.str, p.pos);
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
    const n0 = p.sc.stk.length;
    const pp: Patt[] = [];
    for (const q of qs) {
      pp.push(parse_patt(p, q));
    }
    const f = parse_body(p, rcol);
    parse_close(p, n0);
    rows.push({ p: pp, f });
  }
  return { $: "Match", e: es, r: rows, s: parse_span(p, beg) };
}

// Tele
// ----

export function parse_tele(p: Parse, close: string): Array<[Quant, Name, number, LTerm]> {
  const tele: Array<[Quant, Name, number, LTerm]> = [];
  while (true) {
    parse_skip(p);
    if (parse_take(p, close)) {
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
  p.sc = { stk: [], frs: 0 };
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
  const n0 = p.sc.stk.length;
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
  const b = parse_body(p);
  parse_close(p, n0);
  const v  = body_flatten(b, vars, () => p.sc.frs++);
  const hv = term_higher(v, Emp<HTerm>());
  def.n = vars.length;
  def.v = hv;
  book.order.push(k);
}

export function parse_assert(p: Parse, book: Book): void {
  parse_skip(p);
  p.sc = { stk: [], frs: 0 };
  parse_word(p, "assert");
  const k = parse_qual(p, parse_name(p));
  if (book.tlds[k] !== undefined) {
    parse_fail(p, "a fresh name (duplicate declaration: " + k + ")");
  }
  parse_eat(p, ":");
  const n0  = p.sc.stk.length;
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
      const n1 = p.sc.stk.length;
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
  book.tlds[k] = { $: "Def", n, T: hT, v: null };
  book.order.push(k);
}

export function parse_adt(p: Parse, book: Book): void {
  parse_skip(p);
  p.sc = { stk: [], frs: 0 };
  parse_word(p, "type");
  const k = parse_qual(p, parse_name(p));
  if (book.tlds[k] !== undefined) {
    parse_fail(p, "a fresh name (duplicate declaration: " + k + ")");
  }
  const n0 = p.sc.stk.length;
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
    if (p.pos >= p.str.length || !char_is_head(parse_peek(p))) {
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
    const n1 = p.sc.stk.length;
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

export function parse_book(book: Book, dir: string, src: string, ns: string = ""): Book {
  const p = parse_new(book, dir, src, ns);
  while (true) {
    parse_skip(p);
    if (p.pos >= p.str.length) {
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

// Flatten
// =======
// https://gist.github.com/VictorTaelin/82264b517a1ab7d2ffe17f13deba9c68
// match_flatten compiles nested ctr/var patterns into a tree of lambda-
// matches and binders: first row wins, uncovered cases become \{}; guards,
// literals, or/as and column heuristics are out by design. binders are
// identities and ctrs structural, so substitution cannot capture; a ctr
// row makes its column strict even under an earlier catch-all. scus (the
// vars, duplicate-free, in order, one pattern each) is the precondition.
// a match scrutinizes a parameter or a bound field, nothing else: a
// lambda-match applied to a value is a banned form, so a computed or
// let-bound scrutinee is an error here - give it its own def, where it
// is a parameter. a parallel let becomes one Let node binding its
// names to its values.

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
      const es = b.e.map(scrut);
      const rs = b.r.map((row): Case => ({ p: row.p, f: body_sub(row.f, i, v) }));
      return { $: "Match", e: es, r: rs, s: b.s };
    }
    case "Local": {
      const w = b.v.map(scrut);
      const f = body_sub(b.f, i, v);
      return { $: "Local", k: b.k, q: b.q, v: w, f };
    }
    case "Reply": {
      const x = Sub(i, v, b.x);
      return { $: "Reply", x, s: b.s };
    }
  }
}

export function match_flatten(m: Match, vars: PVar[], fr: () => number): LTerm {
  if (m.e.length === 0 && m.r.length > 0) {
    return body_flatten(m.r[0].f, vars, fr);
  } else if (m.e.length === 0) {
    throw Err(book_nil(), ctx_nil(), "a case (this match has no row to return)", undefined, m.s);
  } else if (vars.length === 0) {
    let e = m.e[0];
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
        throw Err(book_nil(), ctx_nil(), "a parameter or field scrutinee (a match cannot scrutinize a computed value: give it its own def)", undefined, e.s ?? m.s);
      }
    }
  } else {
    const x   = vars[0];
    const scu = m.e[0];
    if (scu.$ === "Var" && scu.i === x.i) {
      if (m.r.length === 0) {
        return Efq(m.s);
      } else {
        const c = rows_find_ctr(m.r);
        if (c === null) {
          const rs = rows_bind_var(m.r, x);
          return match_flatten({ $: "Match", e: m.e.slice(1), r: rs, s: m.s }, vars, fr);
        } else {
          const xs = patt_binds(c.x, fr);
          const ps = rows_pick_ctr(m.r, x, c.k, xs);
          const pe = xs.map((q) => patt_term(q)).concat(m.e.slice(1));
          const pv = xs.concat(vars.slice(1));
          const pt = match_flatten({ $: "Match", e: pe, r: ps, s: m.s }, pv, fr);
          const ds = rows_drop_ctr(m.r, c.k);
          const dt = match_flatten({ $: "Match", e: m.e, r: ds, s: m.s }, vars, fr);
          return Mat(c.k, pt, dt, c.s);
        }
      }
    } else {
      const t = match_flatten(m, vars.slice(1), fr);
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
          return [{ p: p0.x.concat(row.p.slice(1)), f }];
        }
      }
      case "PVar": {
        const g = body_sub(row.f, p0.i, patt_term(x));
        const f = body_sub(g, x.i, patt_term({ $: "PCtr", k, x: xs }));
        return [{ p: xs.concat(row.p.slice(1)), f }];
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
      return { p: row.p.slice(1), f };
    } else {
      throw Err(book_nil(), ctx_nil(), "a variable pattern (this column has no constructor row)", undefined, p0.s);
    }
  });
}

export function rows_find_ctr(rows: Rows): PCtr | null {
  for (const row of rows) {
    const p0 = row.p[0];
    if (p0.$ === "PCtr") {
      return p0;
    }
  }
  return null;
}

export function patt_binds(qs: Patt[], fr: () => number): PVar[] {
  return qs.map((q): PVar => {
    if (q.$ === "PVar") {
      return q;
    }
    const i = fr();
    return { $: "PVar", k: "_" + String(i), i, s: q.s };
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

export function body_flatten(b: Body, vars: PVar[], fr: () => number): LTerm {
  switch (b.$) {
    case "Reply": {
      if (vars.length === 0) {
        return b.x;
      } else {
        const v = vars[0];
        const f = body_flatten(b, vars.slice(1), fr);
        return Lam(v.k, v.i, f, v.s);
      }
    }
    case "Local": {
      if (b.k.length === 1 && b.k[0].$ === "PCtr") {
        const r: Case = { p: [b.k[0]], f: b.f };
        return match_flatten({ $: "Match", e: [b.v[0]], r: [r], s: b.v[0].s }, vars, fr);
      }
      const ws = b.k as PVar[];
      let g = body_flatten(b.f, ws, fr);
      for (let j = 0; j < ws.length; j++) {
        const w = ws[j];
        if (g.$ !== "Lam") {
          throw Err(book_nil(), ctx_nil(), "a parameter or field scrutinee (a match cannot scrutinize a local binder: give it its own def)", undefined, w.s);
        }
        g = g.f;
      }
      const x = Let(ws.map((w) => w.k), ws.map((w) => w.i), b.v, g, ws[0].s, ws.map(() => b.q));
      return body_flatten({ $: "Reply", x }, vars, fr);
    }
    case "Match": {
      return match_flatten(b, vars, fr);
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

export function wnf_laz(book: Book, x: HTerm): HTerm {
  return x.$ === "Laz" ? x : Laz(() => {
    const r = term_wnf(book, x);
    return x.$ === "Ann" ? Ann(r, x.T, x.s) : r;
  }, undefined, x);
}

export function term_wnf(book: Book, term: HTerm): HTerm {
  const frs: Frame[] = [];
  let tm: HTerm = term;
  let lhs_t: HTerm | null = null;
  let lhs_n = 0;
  main: while (true) {
    focus: switch (tm.$) {
      case "Var": {
        if (tm.v === undefined) {
          break focus;
        } else {
          lhs_t = null;
          tm = tm.v;
          continue main;
        }
      }
      case "Laz": {
        lhs_t = null;
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
        tm = tm.f(tm.v.map((v) => wnf_laz(book, v)));
        continue main;
      }
      case "App": {
        const x = tm.x;
        frs.push({ $: "APP", x: wnf_laz(book, x) });
        lhs_t = null;
        tm = tm.f;
        continue main;
      }
      case "Lam": {
        if (frs.length === 0 || frs[frs.length - 1].$ !== "APP") {
          break focus;
        } else {
          const fr = frs.pop() as Extract<Frame, { $: "APP" }>;
          if (lhs_t !== null) {
            if (lhs_n === 0) {
              lhs_t = null;
            } else {
              const pt: HTerm = lhs_t;
              lhs_t = Laz(() => term_apply(pt, fr.x));
              lhs_n = lhs_n - 1;
            }
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
          frs.push({ $: "MAT", t: tm, e: fr.x, lhs: lhs_t !== null ? { t: lhs_t, n: lhs_n } : null });
          tm = fr.x;
          lhs_t = null;
          continue main;
        }
      }
      case "Efq": {
        if (lhs_t !== null && lhs_n > 0 && frs.length > 0 && frs[frs.length - 1].$ === "APP") {
          tm = term_force(lhs_t);
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
        lhs_t = tm;
        lhs_n = tld.n;
        tm = tld.v;
        continue main;
      }
      default: {
        break focus;
      }
    }
    lhs_t = null;
    back: while (true) {
      const fr = frs.pop();
      if (fr === undefined) {
        return tm;
      } else {
        switch (fr.$) {
          case "LAZ": {
            const x = fr.l.x;
            fr.l.v = x?.$ === "Ann" ? Ann(tm, x.T, x.s) : tm;
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
                        lhs_t = null;
                      } else {
                        const ft = fr.lhs.t;
                        lhs_t = Laz(() => lhs_ext(term_force(ft), ctr.k, ctr.x.length));
                        lhs_n = fr.lhs.n - 1 + ctr.x.length;
                      }
                      for (let j = ctr.x.length - 1; j >= 0; j--) {
                        const x = ctr.x[j];
                        if (x.$ !== "Laz") {
                          ctr.x[j] = wnf_laz(book, x);
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
                    tm = term_apply(fr.lhs === null ? fr.t : term_force(fr.lhs.t), fr.e);
                    continue back;
                  }
                  default: {
                    if (fr.lhs === null) {
                      lhs_t = null;
                    } else {
                      lhs_t = fr.lhs.t;
                      lhs_n = fr.lhs.n;
                    }
                    frs.push({ $: "APP", x: ctr });
                    tm = t;
                    continue main;
                  }
                }
              }
            } else {
              tm = term_apply(fr.lhs === null ? fr.t : term_force(fr.lhs.t), fr.e);
              continue back;
            }
          }
        }
      }
    }
  }
}

// Uncop
// =====

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
    const tm = term_wnf(book, t0) as
      Exclude<HTerm, { $: "Laz" | "Let" | "Ann" }>;
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
        return App(tm.f.$ === "Ref" ? tm.f : yield tm.f, yield tm.x, tm.s);
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
    case "ADT":
    case "Ctr": {
      if ((b.$ === "ADT" || b.$ === "Ctr") && b.$ === a.$
        && a.k === b.k && a.x.length === b.x.length) {
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

export function term_check_goal(book: Book, A: HTerm, d: number): boolean {
  const a = term_uncop(book, A);
  if (a.$ === "All") {
    return term_equal(book, A, App(Ref("Copiable"), a.A), d);
  }
  const [h] = term_unapply(a);
  return h.$ === "Ref" && h.k === "Copiable";
}

export function term_check_wit(book: Book, lhs: LHS | null, tm: HTerm, ty: HTerm, ctx: Ctx, d: number): Infer {
  const def = lhs === null ? undefined : lhs.def;
  const chk = term_check(book, lhs, tm, Lone(), ty, ctx, d);
  for (const [i, q] of pmap_to_array(chk.us)) {
    if (q.$ === "None") {
      continue;
    }
    const ann = pmap_get(ctx, i) as Ann;
    if (ann.q.$ === "None" && !term_check_goal(book, ann.T, d)) {
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
        var us = pmap_set(uses_nil(), tm.i, qt);
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
      if (qt.$ !== "None" && tm.k === def) {
        throw Err(book, ctx, "a whole, decreasing self-call (a live self-reference cannot escape as a value)", tm, tm.s, def);
      }
      if (qt.$ !== "None" && tld.$ === "Def" && tld.v === null && tld.b !== true && !tld.i) {
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
    // where a + binder's A is a Cop
    // ----------------------------------------------- infer-all
    // Γ ⊢ @q x:A -> B : Type
    case "All": {
      const b = tm;
      const B_ctx = ctx_bind(ctx, d, tm.q, tm.k, tm.A);
      const A_chk = term_check(book, lhs, tm.A, None(), Typ(tm.s), ctx, d);
      if (!quant_valid(book, tm.q, tm.A)) {
        throw Err(book, ctx, "a copiable type (a + binder needs a + T ~ C type)", tm, tm.s, def);
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
    //       the head is never a Lam: a beta-redex is unnameable in a
    //       compiled expression, so it is rejected here
    //       the head is never a Mat or Efq, even Ann-wrapped,
    //       let-bound, or behind a let or rewrite expression: a
    //       lambda-match application is a banned form
    // --------------------------------------------------------------- infer-app
    // Γ ⊢ f(a) : B(a) ~ fu + au
    case "App": {
      const [fun, arg] = term_unapply(tm);
      let fh = term_strip(fun);
      if (fh.$ === "Lam") {
        throw Err(book, ctx, "a named function (a lambda application is a beta-redex: bind the argument with a let or give the function its own def)", fun, tm.s, def);
      }
      while ((fh.$ === "Var" && fh.v !== undefined) || fh.$ === "Let" || fh.$ === "Rwt") {
        fh = term_strip(fh.$ === "Var" ? fh.v! : fh.$ === "Let" ? fh.f(fh.v) : fh.f);
      }
      if (fh.$ === "Mat" || fh.$ === "Efq") {
        throw Err(book, ctx, "a named eliminator (a lambda-match application is a banned form: give the match its own def)", tm, tm.s, def);
      }
      let f_inf: Infer;
      if (lhs !== null && qt.$ !== "None" && fun.$ === "Ref" && fun.k === def) {
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

export function term_check(book: Book, lhs: LHS | null, tm: HTerm, qt: Quant, ty: HTerm, ctx: Ctx, d: number): Infer {
  const def = lhs === null ? undefined : lhs.def;
  if (qt.$ === "None" && term_check_goal(book, ty, d)) {
    return term_check_wit(book, lhs, tm, ty, ctx, d);
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
      quant_used(book, ctx, tm.k, t_wnf.q, uses_get(f_chk.us, d), tm.s, def);
      var tm = Lam(b.k, b.i, (y: HTerm) => y.$ === "Var" && y.i === d ? f_chk.tm : Laz(() => term_check(book, f_lhs(y), b.f(y), qt, t_wnf.B(y), f_ctx, d+1).tm), b.s);
      var tm = Ann(tm, ty);
      var us = uses_del(f_chk.us, d);
      return { tm, us };
    }
    // Γ ⊢ vj : Aj ~ vuj  (each value in Γ: the binders are parallel)
    // Γ , x1 : q1A1 , .. , xn : qnAn ⊢ f(x1, .., xn) : T ~ fu
    // where a + binder's Aj is a Cop
    //       vj is dead if qj is -
    //       fu[xj] <= qj
    //       the elaborated let re-checks its body lazily; a bare
    //       opened variable takes its value back, so a forcer's
    //       probe cannot flip a verdict validation already passed
    // ------------------------------------------------------------ check-let
    // Γ ⊢ q1 x1 .. qn xn = v1 .. vn; f : T ~ vu1 + .. + vun + fu - x⃗
    case "Let": {
      const b = tm;
      const n = b.k.length;
      const vx: HTerm[] = [];
      var us = uses_nil();
      let f_ctx = ctx;
      for (let j = 0; j < n; j++) {
        const v_dem = quant_dem(b.q[j], qt);
        const v_inf = term_infer(book, lhs, b.v[j], v_dem, ctx, d);
        const v_ann = v_inf.tm as HAnn;
        if (v_dem.$ === "None" && term_check_goal(book, v_ann.T, d)) {
          term_check_wit(book, lhs, b.v[j], v_ann.T, ctx, d);
        }
        if (!quant_valid(book, b.q[j], v_ann.T)) {
          throw Err(book, ctx, "a copiable type (a + binder needs a + T ~ C type)", tm, tm.s, def);
        }
        vx.push(v_inf.tm);
        us = uses_add(us, v_inf.us);
        f_ctx = ctx_bind(f_ctx, d + j, b.q[j], b.k[j], v_ann.T);
      }
      const xs = b.k.map((k, j): HTerm => Var(k, d + j, b.s, b.v[j]));
      const f_chk = term_check(book, lhs, b.f(xs), qt, ty, f_ctx, d + n);
      let fu = f_chk.us;
      for (let j = 0; j < n; j++) {
        quant_used(book, ctx, b.k[j], b.q[j], uses_get(fu, d + j), tm.s, def);
        fu = uses_del(fu, d + j);
      }
      const f_val = (ys: HTerm[]): HTerm[] => ys.map((y, j) => y.$ === "Var" && y.v === undefined ? Var(y.k, y.i, y.s, b.v[j]) : y);
      const f_hit = (ys: HTerm[]): boolean => ys.every((y, j) => y.$ === "Var" && y.i === d + j);
      var tm = Let(b.k, b.i, vx, (ys: HTerm[]) => f_hit(ys) ? f_chk.tm : Laz(() => term_check(book, lhs, b.f(f_val(ys)), qt, ty, f_ctx, d + n).tm), b.s, b.q);
      var tm = Ann(tm, (f_chk.tm as HAnn).T);
      var us = uses_add(us, fu);
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
      term_check(book, null, t_all.A, None(), Typ(), ctx, d);
      if (!quant_valid(book, t_all.q, t_all.A)) {
        throw Err(book, ctx, "a copiable type (a + binder needs a + T ~ C type)", undefined, undefined, ctr.k);
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
    lock_book = parse_book(book_nil(), "", LOCK_SRC);
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
    switch (tld.$) {
      case "ADT": {
        seen.tlds[k] = tld;
        for (const c of tld.c) {
          seen.ctrs[c.k] = c;
        }
        adt_valid(seen, k, tld);
        lock_valid(seen, k, tld);
        break;
      }
      case "Def": {
        const dec: Def = { $: "Def", n: tld.n, T: tld.T, v: null, b: tld.b };
        const fin = last.get(k) === i;
        if (fin && tld.v === null && tld.b !== true && !tld.i) {
          throw Err(book, ctx_nil(), "a filled definition for '" + k + "' (an unfilled assert is an error outside base)");
        }
        seen.tlds[k] = dec;
        def_valid(seen, k, fin ? tld : dec);
        lock_valid(seen, k, fin ? tld : dec);
        seen.tlds[k] = fin ? tld : dec;
        break;
      }
    }
  }
}
