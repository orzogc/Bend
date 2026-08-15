// Bend Core
// =========
// 
// SYNTAX
// ------
//
// Quant ::=
//   | "-"
//   | ""
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
//   | Grp ::= "(" Term ")"
//
// Case   ::= "case" [Term] ":" Body
// Cell   ::= Term | Name ":" Term "=" Term
// Match  ::= "match" [Cell] ":" [Case] ("return" Term)?
// Local  ::= Term "=" Term ";"? Body
// Reply  ::= Term
// Body   ::= Match | Local | Reply
// Def    ::= "def" Name "(" [Bind ","?] ")" "->" Term ":" Body
// Ctr    ::= Name "{" [Bind ","?] "}"
// ADT    ::= "type" Name ("<" [Bind ","?] ">")? ":" [Ctr]
// Clause ::= ("forall" Quant | "exists") Name ":" Term ("where" Term)?
// Assert ::= "assert" Name ":" [Clause] Term
// Fill   ::= "def" Name "(" [Name ","?] ")" ":" Body
// TLD    ::= Def | ADT | Assert | Fill
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
// LitChr  | "'" CHAR "'"          | Chr{U32{bits}}
// LitStr  | "\"" [CHAR] "\""      | SCon{x, SCon{y,...SNil{}}}
//
// a literal expands to one node per unit, unbounded by design. Arrow is
// right-associative; the domain of a written @ or & binder stops at the
// first bare "->", so an arrow (or a nested binder) there needs parens.
// infix "&" and "|" are right-associative, share one precedence, and
// bind tighter than "->". a rewrite "%e@E : P; f" binds e and "_" inside
// its motive P; "%E : P; f" is the nameless form: the equation binder is
// spelled "" and cannot be referenced.
//
// Assert
// ------
//
// Assert declares a bodiless def: an axiom, visible and stuck, dead-only
// (a live reference to an unfilled assert is an error: an axiom is a
// dead claim), until a later Fill (a def with bare binders and no return
// type) gives it a body, checked at the fill's own position against the
// asserted type: the name is stuck before its fill and unfolds after it.
// A forall clause folds to an All (- erases), an exists clause to a
// Sigma, and "where w" turns the clause type A into &x:A -> w, reusing
// the clause name for the witness.
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
// LAYOUT
// ------
//
// `;` and `,` are always optional. Whitespace is irrelevant, with two
// exceptions: App's `(` (like Ctr's `{` and ADT's `<`) must be GLUED to
// its head, and a match owns a case only if it sits right of the
// enclosing case's column; a `case` column left of a match's first case
// closes that match. `=>` and `=` are ordinary suffixes: a lambda or a
// let parses wherever a term does, and stops at the position's delimiter.
//
// THEORY
// ------
//
// Bend is a dependent affine calculus: two checking modes (dead and live)
// and a well-founded descent judgment on live recursion. a live variable
// is consumed at most once (core v1 has no duplication of any kind); no
// live computation duplicates a closure, every live self-call descends,
// and no dead inhabitant is promoted to live evidence. this wall permits
// Type : Type, impredicativity and negative recursive types with no
// universe hierarchy and no positivity check.
//
// QUANTITIES. None | Lone, spelled -x, x on a binder.
//   add  (sequential): None + q = q; a second live use saturates to an
//                      internal overflow (Many) that no binder satisfies
//   join (branches):   pointwise max
// Lone is affine: zero or one live use; dead occurrences cost nothing.
// Many is unspellable: + is a parse error, a Many binder is a formation
// error, and inside the usage measure Many is always a violation. a
// binder is a cost contract: no hidden clone or retain, absolute in v1.
//
// MODES. a type position, an erased (-) argument, an equality endpoint or
// a motive checks dead: it may mention anything any number of times,
// self-apply, diverge, and inhabit Empty. dead code is specification, not
// proof; acceptance is sound-on-success. the boundary is sealed: no rule
// coerces dead to live, and a dead field is untrusted ghost data.
//
// DATATYPES. type declares an ordinary family: one telescope of
// parameters tipped at Type, each constructor a telescope of parameters
// then fields tipped at the family instance. fields never carry a
// license; a -field is absent from storage and dead. a pattern binder
// takes its quantity from the elimination site.
//
// EQUALITY. intensional and computationally quiet: carrier and endpoints
// are dead, so propositions mention consumed variables freely; Rfl checks
// when the endpoints convert. elimination is the J axiom, spelled
// %e@E : P; f. for E : {a == b : A} the motive P binds "_" (the second
// endpoint, at A) and e (the equation, at {a == _ : A}); the ambient
// goal must be P(b, E) and the body f checks at P(a, {==}). P is dead;
// E checks at the ambient demand, so a live rewrite needs live evidence,
// and a closed live proof normalizes to Rfl, whose endpoints convert. a
// stuck rewrite is a value: it fires exactly when its evidence reaches
// {==}, and then steps to f, so a forged dead equation never rewrites a
// live goal. conversion is up to eta for functions: a lambda and a
// non-lambda compare pointwise under a fresh variable, so a saturating
// argument can unfold what an underapplied def kept closed.
//
// DESCENT. every live self-call is a whole call in the def's own case
// tree whose live columns compare EQ left to right until one is a strict
// subterm; an erased (-) column is skipped, since erased data cannot be
// matched live and never carries the decrease, only spurious mismatch. a
// live self-reference cannot escape as a value, a forward reference
// fails as undefined, and an unfilled assert is dead-only, so mutual
// recursion cannot bypass the wall.
//
// CONSISTENCY. omega, Curry through negative types and Hurkens through
// impredicativity all bottom out in live contraction of a function-valued
// binding: in core v1 no live binding contracts at all. descent excludes
// infinite live chains, and dead isolation keeps divergence and Empty
// inside types. trusted claims: subject reduction, progress, weak
// normalization of closed live terms, no closed live inhabitant of
// Empty. deliberate boundaries: strong reduction under binders and
// type-level computation need not terminate. live values never clone;
// top-level defs are freely reusable.
//
// DUPLICATION (FUTURE). out of core v1 on purpose, not solved and
// hidden: + is a parse error, a Many binder is a formation error, and no
// rule gives a second live use a meaning. over {None, Lone} every
// candidate semantics collapses to the same accounting (None absorbs,
// Lone is identity), so any of them can be layered on later without
// changing the meaning of a single v1 program.
//
// OWNERSHIP. full Bend layers representation over this core: an owned
// value is a unique tree; arrays and resource handles are unique values,
// so double free is unrepresentable. the checker is authoritative about
// cost: a compiler may drop a cost the source spelled, never add a clone
// or retain the source did not.
//
// PIPELINE
// --------
//
// parse -> flatten -> higher. a binder takes a fresh int id at parse: the
// id is the identity, the name a display label, so scope is structural
// and capture is impossible; a name still unbound after flattening
// resolves to a Ref. a def's body flattens at parse into a point-free
// case tree (Def.v). one Term type, two views: LTerm binds LTerm bodies,
// HTerm binds (x: HTerm) => HTerm. LTerm dies after parsing; the book
// stores HTerm; wnf and the checker act on HTerm; show lowers, then
// prints. Sub is the one flatten-time substitution node; every other
// substitution is HOAS application.
//
// NOT-A-BUG
// ---------
//
// - validation or an error report may hang: dead terms may diverge, and
//   the checker and the printer both normalize them. a hang accepts
//   nothing, so no wrong program gets in.
//
// - a big nat literal overflows the host stack: literals are unbounded by
//   design, and a crash on absurd input accepts nothing.
//
// - a constructor and a def may share a name: separate namespaces; every
//   use resolves by shape and is checked against its own declaration.
//
// - conversion ignores a match's peeled constructors (ADT.r), so a
//   duplicate, unreachable match arm may validate; r is unspellable in
//   source.
//
// - a non-well-founded type and its eliminator both validate: such a
//   type has no closed inhabitant, since a generator needs a
//   non-decreasing self-call.
//
// - &c:A -> B is notation for Sigma<A, c => B>, nothing more.
//
// - a stuck rewrite is inert: only evidence that normalizes to {==}
//   fires it, so no forged equation moves a value.
//
// - validation stores each def's elaborated body on def.e: the checked
//   term with an Ann wrapped on every layer. Compilation consumes it.

import * as fs from "fs";

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
  | { $: "Ref"; k: Name }                                                  // x
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
  | { $: "Ann"; x: TermOf<B>; T: TermOf<B> }                               // {x : T}
  | { $: "Laz"; f: () => TermOf<B> }                                       // x
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
export type Def  = { $: "Def"; n: number; T: HTerm; v: HTerm | null; e?: HTerm; };
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
export type Parse = { str: string; loc: Loc; env: Name[]; ids: Record<Name, number[]>; frs: number; book: Book; ns: string; };
export type Span  = { src: string; beg: Loc; end: Loc; };

// Machine
export type LHS   = { t: HTerm; n: number; def: Name; qs: Quant[] };
export type Frame =
  | { $: "APP"; x: HTerm }                                                   // _(x)
  | { $: "MAT"; t: Extract<HTerm, { $: "Mat" }>; e: HTerm; lhs: LHS | null } // \{c:h;m}(_)

// Error
export type Expr = HTerm | string;
export type Err  = { $: "Err"; exp: Expr; obs?: Expr; ctx: Ctx; def?: Name; spn?: Span; };

// Constructors
// ============

// Term
// ----

export function Var<X>(k: Name, i: number, s?: Span, v?: TermOf<X>): TermOf<X> {
  return { $: "Var", k, i, s, v };
}

export function Ref<X>(k: Name, s?: Span): TermOf<X> {
  return { $: "Ref", k, s };
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

export function Ann<X>(x: TermOf<X>, T: TermOf<X>, s?: Span): TermOf<X> {
  return { $: "Ann", x, T, s };
}

export function Laz<X>(f: () => TermOf<X>, s?: Span): TermOf<X> {
  return { $: "Laz", f, s };
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

export function Err(ctx: Ctx, exp: Expr, obs?: Expr, spn?: Span, def?: Name): Err {
  return { $: "Err", ctx, exp, obs, spn, def };
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

export function term_strip(tm: HTerm): HTerm {
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
      return Ref(tm.k, tm.s);
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

export function term_lower(tm: HTerm, d: number = 0): LTerm {
  switch (tm.$) {
    case "Var": {
      return Var(tm.k, tm.i, tm.s);
    }
    case "Ref": {
      return Ref(tm.k, tm.s);
    }
    case "Sub": {
      const v = term_lower(tm.v, d);
      const f = term_lower(tm.f, d);
      return Sub(tm.i, v, f, tm.s);
    }
    case "Let": {
      const x: HTerm = Var(tm.k, d, undefined, tm.v);
      const v = term_lower(tm.v, d);
      const f = term_lower(tm.f(x), d + 1);
      return Let(tm.k, d, v, f, tm.s, tm.q);
    }
    case "Typ": {
      return Typ(tm.s);
    }
    case "All": {
      const x: HTerm = Var(tm.k, d);
      const A = term_lower(tm.A, d);
      const B = term_lower(tm.B(x), d + 1);
      return All(tm.q, tm.k, d, A, B, tm.s);
    }
    case "Lam": {
      const x: HTerm = Var(tm.k, d);
      const f = term_lower(tm.f(x), d + 1);
      return Lam(tm.k, d, f, tm.s);
    }
    case "App": {
      const f = term_lower(tm.f, d);
      const x = term_lower(tm.x, d);
      return App(f, x, tm.s);
    }
    case "ADT": {
      const xs = tm.x.map((x) => term_lower(x, d));
      return ADT(tm.k, xs, tm.s, tm.r);
    }
    case "Ctr": {
      const xs = tm.x.map((x) => term_lower(x, d));
      return Ctr(tm.k, xs, tm.s);
    }
    case "Mat": {
      const h = term_lower(tm.h, d);
      const m = term_lower(tm.m, d);
      return Mat(tm.k, h, m, tm.s);
    }
    case "Efq": {
      return Efq(tm.s);
    }
    case "Eql": {
      const a = term_lower(tm.a, d);
      const b = term_lower(tm.b, d);
      const T = term_lower(tm.T, d);
      return Eql(a, b, T, tm.s);
    }
    case "Rfl": {
      return Rfl(tm.s);
    }
    case "Rwt": {
      const e = term_lower(tm.e, d);
      const p = term_lower(tm.p, d);
      const f = term_lower(tm.f, d);
      return Rwt(e, p, f, tm.s);
    }
    case "Ann": {
      const x = term_lower(tm.x, d);
      const T = term_lower(tm.T, d);
      return Ann(x, T, tm.s);
    }
    case "Laz": {
      const t = term_lower(term_force(tm), d);
      return t;
    }
  }
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
    throw Err(ctx, "a declared datatype (unknown: " + tm.k + ")", undefined, tm.s, def);
  }
  if (tm.r.length === 0) {
    return tld;
  }
  return { $: "ADT", n: tld.n, T: tld.T, c: tld.c.filter((c) => !tm.r.includes(c.k)) };
}

// Tele
// ====

export function tele_to_term(tele: Array<[Quant, Name, number, LTerm]>, end: LTerm): LTerm {
  let out = end;
  for (let j = tele.length - 1; j >= 0; j--) {
    const [q, k, i, T] = tele[j];
    out = All(q, k, i, T, out);
  }
  return out;
}

export function tele_next(book: Book, tel: HTerm, ctx: Ctx, def?: Name, s?: Span): Extract<HTerm, { $: "All" }> {
  const t = term_wnf(book, tel);
  if (t.$ !== "All") {
    throw Err(ctx, "unreachable (a telescope binds its parameters and fields)", undefined, s, def);
  }
  return t;
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

export function term_show(tm: LTerm, prc: number = 0, bnd: Name[] = []): string {
  function term_show_sugar_exi(tm: LTerm, prc: number): string | null {
    const t = term_force(tm);
    if (t.$ !== "ADT" || t.k !== "Sigma" || t.x.length !== 2) {
      return null;
    }
    const b = term_force(t.x[1]);
    if (b.$ !== "Lam") {
      return null;
    }
    const A = term_show(t.x[0], 1, bnd);
    bnd.push(b.k);
    const f = term_show(b.f, 1, bnd);
    bnd.pop();
    const s = "&" + b.k + ":" + A + " -> " + f;
    return prc > 1 ? "(" + s + ")" : s;
  }
  function term_show_sugar_nat(tm: LTerm, prc: number): string | null {
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
    const k = term_show(t, 1, bnd);
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
  switch (tm.$) {
    case "Var": {
      return bnd.lastIndexOf(tm.k) === tm.i ? tm.k : tm.k + "^" + String(tm.i);
    }
    case "Ref": {
      return bnd.includes(tm.k) ? tm.k + "^" : tm.k;
    }
    case "Sub": {
      const f = term_show(tm.f, prc, bnd);
      return f;
    }
    case "Let": {
      const v = term_show(tm.v, 1, bnd);
      bnd.push(tm.k);
      const f = term_show(tm.f, 0, bnd);
      bnd.pop();
      const s = quant_show(tm.q) + tm.k + " = " + v + "; " + f;
      return prc > 0 ? "(" + s + ")" : s;
    }
    case "Typ": {
      return "Type";
    }
    case "All": {
      const A = term_show(tm.A, 1, bnd);
      bnd.push(tm.k);
      const B = term_show(tm.B, 1, bnd);
      bnd.pop();
      const s = "@" + quant_show(tm.q) + tm.k + ":" + A + " -> " + B;
      return prc > 1 ? "(" + s + ")" : s;
    }
    case "Lam": {
      bnd.push(tm.k);
      const f = term_show(tm.f, 0, bnd);
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
      const hs = term_show(h, 2, bnd);
      const as = xs.map((x) => term_show(x, 0, bnd)).join(", ");
      return hs + "(" + as + ")";
    }
    case "ADT": {
      const sug = term_show_sugar_exi(tm, prc);
      if (sug !== null) {
        return sug;
      }
      const as = tm.x.map((x) => term_show(x, 0, bnd)).join(", ");
      const rs = tm.r.map((c) => " - " + c + "{}").join("");
      const s  = tm.k + "<" + as + ">" + rs;
      return rs !== "" && prc > 1 ? "(" + s + ")" : s;
    }
    case "Ctr": {
      const chr = term_show_sugar_chr(tm, "'");
      const sug = term_show_sugar_nat(tm, prc)
               ?? (chr !== null ? "'" + chr + "'" : null)
               ?? term_show_sugar_str(tm);
      if (sug !== null) {
        return sug;
      }
      const as = tm.x.map((x) => term_show(x, 0, bnd)).join(", ");
      return tm.k + "{" + as + "}";
    }
    case "Mat": {
      const arms: string[] = [];
      let m: LTerm = tm;
      while (m.$ === "Mat") {
        arms.push(m.k + ": " + term_show(m.h, 1, bnd));
        m = term_force(m.m);
      }
      if (m.$ !== "Efq") {
        arms.push(term_show(m, 1, bnd));
      }
      return "\\{" + arms.join("; ") + "}";
    }
    case "Efq": {
      return "\\{}";
    }
    case "Eql": {
      const a = term_show(tm.a, 1, bnd);
      const b = term_show(tm.b, 1, bnd);
      const T = term_show(tm.T, 1, bnd);
      return "{" + a + " == " + b + " : " + T + "}";
    }
    case "Rfl": {
      return "{==}";
    }
    case "Rwt": {
      const e = term_show(tm.e, 1, bnd);
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
          const P = term_show(mb.f, 1, bnd);
          bnd.pop();
          bnd.pop();
          const f = term_show(tm.f, 0, bnd);
          const n = mb.k === "" ? "" : mb.k + "@";
          const s = "%" + n + e + " : " + P + "; " + f;
          return prc > 0 ? "(" + s + ")" : s;
        }
      }
      const P = term_show(tm.p, 1, bnd);
      const f = term_show(tm.f, 0, bnd);
      const s = "%" + e + " : " + P + "; " + f;
      return prc > 0 ? "(" + s + ")" : s;
    }
    case "Ann": {
      const x = term_show(tm.x, 1, bnd);
      const T = term_show(tm.T, 1, bnd);
      return "{" + x + " : " + T + "}";
    }
    case "Laz": {
      const s = term_show(term_force(tm), prc, bnd);
      return s;
    }
  }
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

export function err_show(book: Book, err: Err): string {
  const bnd = ctx_scope(err.ctx);
  const msg = err.obs === undefined
    ? "\n- message  : " + expr_show(book, err.exp, bnd)
    : "\n- expected : " + expr_show(book, err.exp, bnd) + "\n- observed : " + expr_show(book, err.obs, bnd);
  const def = err.def === undefined ? "" : " " + err.def;
  const spn = err.spn === undefined ? "" : "\n" + span_show(err.spn);
  const loc = def === "" && spn === "" ? "" : "\nLocation:" + def + spn;
  return "Error:" + msg + ctx_show(book, err.ctx) + loc;
}

// Parse
// =====

const IS_KEYWORD: Record<Name, Bool> = {
  "def"   : true, "type": true, "match": true,
  "case"  : true, "do"  : true, "return": true,
  "Type"  : true,
};

export function parse_new(str: string, book: Book, ns: string): Parse {
  return { str, loc: { pos: 0, lin: 1, col: 1 }, env: [], ids: Object.create(null), frs: 0, book, ns };
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
  throw Err(ctx_nil(), exp, obs, { src: p.str, beg: here, end: here });
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

export function parse_bind(p: Parse): Name {
  const k = parse_name(p);
  if (k.includes(".")) {
    parse_fail(p, "an unqualified binder");
  }
  return k;
}

export function parse_char(p: Parse): U32 {
  if (parse_take(p, "\\")) {
    const c = parse_bump(p);
    switch (c) {
      case "n":  return 10;
      case "\\": return 92;
      case "'":  return 39;
      case '"':  return 34;
      default: {
        parse_fail(p, "an escape (\\n \\\\ \\' \\\")");
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
  if (parse_at(p, "+")) {
    parse_fail(p, "an affine quantity (- or plain; + is not supported)");
  }
  return Lone();
}

// Patt
// ----

export function parse_patt(p: Parse, book: Book, t: LTerm): Patt {
  switch (t.$) {
    case "Var": {
      if (book_ctr(book, t.k) !== null || book_ctr(book, parse_qual(p, t.k)) !== null) {
        throw Err(ctx_nil(), "a braced constructor pattern (" + t.k + " is a constructor: write " + t.k + "{}, or rename the binder)", undefined, t.s);
      }
      const i = parse_open(p, t.k);
      return { $: "PVar", k: t.k, i, s: t.s };
    }
    case "Ctr": {
      const ctr = book_ctr(book, t.k);
      if (ctr === null) {
        throw Err(ctx_nil(), "a declared constructor (unknown: " + t.k + ")", undefined, t.s);
      }
      if (ctr.n !== t.x.length) {
        throw Err(ctx_nil(), "a " + t.k + " pattern with " + String(ctr.n) + (ctr.n === 1 ? " field" : " fields"), undefined, t.s);
      }
      const xs: Patt[] = [];
      for (const x of t.x) {
        const px = parse_patt(p, book, x);
        xs.push(px);
      }
      return { $: "PCtr", k: t.k, x: xs, s: t.s };
    }
    default: {
      parse_fail(p, "a pattern (a binder or a constructor)");
    }
  }
}

// Term
// ----

export function parse_term(p: Parse, arr: boolean = true, asg: boolean = true): LTerm {
  parse_skip(p);
  const beg  = parse_loc(p);
  const base = parse_term_base(p);
  if (base.s === undefined) {
    base.s = parse_span(p, beg);
  }
  const out = parse_term_suff(p, base, arr, asg);
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
    const t = parse_term_nat(p);
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
      const t = parse_term_mat(p);
      return t;
    }
    case "%": {
      const t = parse_term_rwt(p, beg);
      return t;
    }
    case "{": {
      const t = parse_term_brc(p);
      return t;
    }
    case "(": {
      parse_bump(p);
      const t = parse_term_tup(p, beg);
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
    case "-":
    case "+": {
      const q = parse_quant(p);
      const k = parse_bind(p);
      parse_eat(p, "=");
      const t = parse_term_let(p, k, q, parse_span(p, beg));
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
      if (parse_at(p, "<") && !parse_at(p, "<-")) {
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

export function parse_term_suff(p: Parse, tm: LTerm, arr: boolean = true, asg: boolean = true): LTerm {
  let out = tm;
  while (true) {
    if (parse_at(p, "(")) {
      parse_bump(p);
      const xs = parse_term_args(p, ")");
      const s  = out.s === undefined ? undefined : parse_span(p, out.s.beg);
      for (const x of xs) {
        out = App(out, x, s);
      }
      continue;
    }
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
    if (arr && parse_take(p, "->")) {
      const B = parse_term(p, true, asg);
      return All(Lone(), "_", parse_open(p, "_"), out, B);
    }
    if (parse_at(p, "&") || parse_at(p, "|")) {
      const ei = parse_peek(p) === "|";
      parse_bump(p);
      const b = parse_term(p, false, asg);
      const s = out.s === undefined ? undefined : parse_span(p, out.s.beg);
      out = ei ? ADT("Either", [out, b], s) : App(App(Ref("Pair", s), out, s), b, s);
      continue;
    }
    if (asg && parse_at(p, "=") && !parse_at(p, "==")) {
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
  const k = parse_bind(p);
  parse_eat(p, ":");
  const A = parse_term(p, false);
  parse_eat(p, "->");
  const n0 = p.env.length;
  const i  = parse_open(p, k);
  const B  = parse_term(p);
  parse_close(p, n0);
  return All(q, k, i, A, B);
}

export function parse_term_exi(p: Parse): LTerm {
  parse_bump(p);
  const k = parse_bind(p);
  parse_eat(p, ":");
  const A = parse_term(p, false);
  parse_eat(p, "->");
  const n0 = p.env.length;
  const i  = parse_open(p, k);
  const B  = parse_term(p);
  parse_close(p, n0);
  return ADT("Sigma", [A, Lam(k, i, B)]);
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
        arms.push([k, h]);
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
      if (nm.includes(".")) {
        parse_fail(p, "an unqualified binder");
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
  parse_eat(p, ":");
  const T = parse_term(p);
  parse_eat(p, "}");
  return Ann(a, T);
}

export function parse_term_nat(p: Parse): LTerm {
  const beg = parse_loc(p);
  let s = "";
  while (/[0-9]/.test(parse_peek(p))) {
    s += parse_bump(p);
  }
  if (!parse_take(p, "n")) {
    parse_fail(p, "a nat literal (NUMBER n)");
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
  function parse_term_do_call(op: Name, xs: LTerm[]): LTerm {
    const q = parse_qual(p, m + "." + op);
    let fn: LTerm = Ref(p.book.tlds[q] !== undefined ? q : m + "." + op);
    for (const l of ls) {
      fn = App(fn, l);
    }
    for (const x of xs) {
      fn = App(fn, x);
    }
    return fn;
  }
  parse_skip(p);
  if (parse_word(p, "return")) {
    const e = parse_term(p);
    return parse_term_do_call("pure", R === null ? [e] : [R, e]);
  }
  const t = parse_term(p);
  const bak = parse_loc(p);
  parse_skip(p);
  if (t.$ === "Var" && parse_take(p, ":")) {
    const A   = parse_term(p);
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
    const n0 = p.env.length;
    const i  = parse_open(p, t.k);
    const f  = parse_term_do_stmt(p, m, ls, R);
    parse_close(p, n0);
    return asg ? Let(t.k, i, Ann(v, A), f) : parse_term_do_call("bind", R === null ? [A, v, Lam(t.k, i, f)] : [A, R, v, Lam(t.k, i, f)]);
  }
  if (parse_take(p, "<-")) {
    const v = parse_term(p);
    parse_skip(p);
    parse_take(p, ";");
    const i = parse_open(p, "_");
    const f = parse_term_do_stmt(p, m, ls, R);
    return parse_term_do_call("bind", R === null ? [t, v, Lam("_", i, f)] : [t, R, v, Lam("_", i, f)]);
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
    return { $: "Local", k, q: Lone(), v, f };
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
    const A = parse_term(p, true, false);
    parse_eat(p, "=");
    const v = parse_term(p);
    es.push({ $: "Cell", k: e.k, i: 0, A, v, s: e.s });
    fr = true;
    parse_skip(p);
    if (parse_take(p, ":")) {
      break;
    }
  }
  if (fr) {
    for (const c of es) {
      if (c.A === null) {
        parse_fail(p, "a uniform match (frame every scrutinee, or none)");
      }
      c.i = parse_open(p, c.k);
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
  while (true) {
    parse_skip(p);
    if (parse_take(p, close)) {
      return tele;
    }
    const q = parse_quant(p);
    const k = parse_bind(p);
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
  const n0 = p.env.length;
  parse_eat(p, "(");
  const tele = parse_tele(p, ")");
  parse_eat(p, "->");
  const ret = parse_term(p);
  const T   = tele_to_term(tele, ret);
  const hT  = term_higher(T, Emp<HTerm>());
  const def: Def = { $: "Def", n: tele.length, T: hT, v: null };
  book.tlds[k] = def;
  parse_eat(p, ":");
  const b = parse_body(p, book);
  parse_close(p, n0);
  const vars = tele.map((cell): PVar => ({ $: "PVar", k: cell[1], i: cell[2] }));
  const v    = body_flatten(b, vars, p.frs);
  def.v = term_higher(v, Emp<HTerm>());
  book.order.push(k);
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
    const c = parse_bind(p);
    vars.push({ $: "PVar", k: c, i: parse_open(p, c) });
    parse_skip(p);
    parse_take(p, ",");
  }
  parse_eat(p, ":");
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
    const c = parse_bind(p);
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
  book.tlds[k] = { $: "Def", n, T: hT, v: null };
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
  const sig = tele_to_term(params, Typ());
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
    const T  = tele_to_term(params.concat(fs), target);
    const hT = term_higher(T, Emp<HTerm>());
    parse_close(p, n1);
    const ctr = { k: c, n: fs.length, T: hT };
    cs.push(ctr);
    book.ctrs[c] = ctr;
  }
  parse_close(p, n0);
  book.order.push(k);
}

export function parse_book(src: string, book: Book = book_nil(), ns: string = ""): Book {
  const p = parse_new(src, book, ns);
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

export function book_load(book: Book, file: string, ns: string, seen: Map<string, string | null>): void {
  const real = fs.realpathSync(file);
  const done = seen.get(real);
  if (done === null) {
    throw Err(ctx_nil(), "an acyclic import graph (a cycle reaches " + file + ")");
  }
  if (done !== undefined) {
    if (done !== ns) {
      throw Err(ctx_nil(), "one namespace per file (" + file + " is both '" + done + "' and '" + ns + "')");
    }
    return;
  }
  seen.set(real, null);
  const lines = fs.readFileSync(file, "utf8").split("\n");
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i].trim();
    if (line === "import Base") {
      book_load(book, new URL("./base.bend", import.meta.url).pathname, "", seen);
      lines[i] = "";
      continue;
    }
    const m = line.match(/^import\s+(\S+)\s+as\s+(\S+)$/);
    if (m !== null) {
      const dir = file.slice(0, file.lastIndexOf("/") + 1);
      book_load(book, m[1].startsWith("/") ? m[1] : dir + m[1], m[2], seen);
      lines[i] = "";
      continue;
    }
    if (line !== "" && !line.startsWith("#")) {
      break;
    }
  }
  parse_book(lines.join("\n"), book, ns);
  seen.set(real, ns);
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
// a framed match meets it by construction: its cells' fresh binders are
// the scus, and its leaf returns the tree annotated with the written
// telescope and applied to the cell values. a computed scrutinee takes
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
    const T  = tele_to_term(m.e.map((c): [Quant, Name, number, LTerm] => [Lone(), c.k, c.i, c.A as LTerm]), m.P as LTerm);
    let x: LTerm = Ann(t, T, m.s);
    for (const c of m.e) {
      x = App(x, c.v, m.s);
    }
    const f = body_flatten({ $: "Reply", x, s: m.s }, vars, d);
    return f;
  }
  if (m.e.length === 0 && m.r.length > 0) {
    const t = body_flatten(m.r[0].f, vars, d);
    return t;
  } else if (m.e.length === 0) {
    throw Err(ctx_nil(), "a case (this match has no row to return)", undefined, m.s);
  } else if (vars.length === 0) {
    let e = m.e[0].v;
    while (e.$ === "Sub") {
      e = e.f;
    }
    switch (e.$) {
      case "Var": {
        throw Err(ctx_nil(), "match scrutinees in binder order (this variable is unbound, consumed, or out of order: reorder the match)", undefined, e.s);
      }
      case "Ctr": {
        throw Err(ctx_nil(), "an undestructed scrutinee (this var was destructed by the outer match: fold the pattern into the outer case)", undefined, m.s);
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
          throw Err(ctx_nil(), "a " + k + " pattern with " + String(xs.length) + " fields", undefined, p0.s);
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
      throw Err(ctx_nil(), "a variable pattern (this column has no constructor row)", undefined, p0.s);
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
          const f = body_flatten(b.f, [], d);
          const t = body_flatten({ $: "Reply", x: Let(w.k, w.i, b.v, f, w.s, b.q) }, vars, d);
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
          tm = tm.v;
          continue main;
        }
      }
      case "Laz": {
        tm = term_force(tm);
        continue main;
      }
      case "Ann": {
        tm = tm.x;
        continue main;
      }
      case "Let": {
        const v = tm.v;
        tm = tm.f(Laz(() => term_wnf(book, v)));
        continue main;
      }
      case "App": {
        const x = tm.x;
        frs.push({ $: "APP", x: x.$ === "Laz" ? x : Laz(() => term_wnf(book, x)) });
        tm = tm.f;
        continue main;
      }
      case "Lam": {
        if (frs.length === 0 || frs[frs.length - 1].$ !== "APP") {
          break focus;
        } else {
          const fr = frs.pop() as Extract<Frame, { $: "APP" }>;
          if (lhs !== null) {
            lhs = lhs.n === 1 ? null : { t: term_apply(lhs.t, fr.x), n: lhs.n - 1, def: lhs.def, qs: lhs.qs };
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
        if (lhs !== null) {
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
        lhs = tld.n === 0 ? null : { t: tm, n: tld.n, def: tm.k, qs: [] };
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
                      if (fr.lhs === null || fr.lhs.n - 1 + ctr.x.length === 0) {
                        lhs = null;
                      } else {
                        lhs = { t: lhs_ext(fr.lhs.t, ctr.k, ctr.x.length), n: fr.lhs.n - 1 + ctr.x.length, def: fr.lhs.def, qs: fr.lhs.qs };
                      }
                      for (let j = ctr.x.length - 1; j >= 0; j--) {
                        const x = ctr.x[j];
                        if (x.$ !== "Laz") {
                          ctr.x[j] = Laz(() => term_wnf(book, x));
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

// SNF
// ===

export function term_snf(book: Book, term: HTerm): HTerm {
  const tm = term_wnf(book, term);
  switch (tm.$) {
    case "Var": {
      return Var(tm.k, tm.i, tm.s);
    }
    case "Ref": {
      return Ref(tm.k, tm.s);
    }
    case "Sub": {
      const v = term_snf(book, tm.v);
      const f = term_snf(book, tm.f);
      return Sub(tm.i, v, f, tm.s);
    }
    case "Let": {
      const b = tm;
      const v = term_snf(book, b.v);
      return Let(b.k, b.i, v, (x: HTerm) => {
        return term_snf(book, b.f(x));
      }, b.s, b.q);
    }
    case "Typ": {
      return Typ(tm.s);
    }
    case "All": {
      const b = tm;
      const A = term_snf(book, b.A);
      return All(b.q, b.k, b.i, A, (x: HTerm) => {
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
      const f = term_snf(book, tm.f);
      const x = term_snf(book, tm.x);
      return App(f, x, tm.s);
    }
    case "ADT": {
      const xs = tm.x.map((x) => term_snf(book, x));
      return ADT(tm.k, xs, tm.s, tm.r);
    }
    case "Ctr": {
      const xs = tm.x.map((x) => term_snf(book, x));
      return Ctr(tm.k, xs, tm.s);
    }
    case "Mat": {
      const h = term_snf(book, tm.h);
      const m = term_snf(book, tm.m);
      return Mat(tm.k, h, m, tm.s);
    }
    case "Efq": {
      return Efq(tm.s);
    }
    case "Eql": {
      const a = term_snf(book, tm.a);
      const b = term_snf(book, tm.b);
      const T = term_snf(book, tm.T);
      return Eql(a, b, T, tm.s);
    }
    case "Rfl": {
      return Rfl(tm.s);
    }
    case "Rwt": {
      const e = term_snf(book, tm.e);
      const p = term_snf(book, tm.p);
      const f = term_snf(book, tm.f);
      return Rwt(e, p, f, tm.s);
    }
    case "Ann": {
      const x = term_snf(book, tm.x);
      const T = term_snf(book, tm.T);
      return Ann(x, T, tm.s);
    }
    case "Laz": {
      const t = term_snf(book, term_force(tm));
      return t;
    }
  }
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

export function term_infer(book: Book, lhs: LHS | null, tm: HTerm, qt: Quant, ctx: Ctx, d: number): Infer {
  const def = lhs === null ? undefined : lhs.def;
  switch (tm.$) {
    // Γ[x] = q A
    // ----------------- infer-var
    // Γ ⊢ x : A ~ {x:q}
    case "Var": {
      const ann = pmap_get(ctx, tm.i);
      if (ann === null) {
        throw Err(ctx, "a bound variable", tm, tm.s, def);
      } else {
        var us = uses_one(tm.i, qt);
        var tm = Ann(tm, ann.T);
        return { tm, us };
      }
    }
    // Book(k) : T
    // where k is not the lhs head in a live region
    //       (a live self-call enters whole, through infer-app)
    //       k has a body in a live region
    //       (an unfilled assert is a dead claim)
    //       k is not a parameterized family: D<..> is the one
    //       spelling, a bare family head is an error
    // -------------------------------------------------------- infer-ref
    // Γ ⊢ k : T ~ {}
    case "Ref": {
      const tld = book.tlds[tm.k];
      if (tld === undefined) {
        throw Err(ctx, "a defined name", tm, tm.s, def);
      }
      if (qt.$ !== "None" && tm.k === def && !book.halts) {
        throw Err(ctx, "a whole, decreasing self-call (a live self-reference cannot escape as a value)", tm, tm.s, def);
      }
      if (qt.$ !== "None" && tld.$ === "Def" && tld.v === null && !book.halts) {
        throw Err(ctx, "a filled definition (an unfilled assert is a dead claim: live code cannot use it)", tm, tm.s, def);
      }
      if (tld.$ === "ADT" && tld.n > 0) {
        throw Err(ctx, "a family instance (write " + tm.k + "<..>)", tm, tm.s, def);
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
    // where q is - or plain; + is a formation error
    // ----------------------------------------------- infer-all
    // Γ ⊢ @q x:A -> B : Type
    case "All": {
      if (tm.q.$ === "Many") {
        throw Err(ctx, "an affine binder (- or plain; + is not supported)", tm, tm.s, def);
      }
      const b = tm;
      const B_ctx = ctx_bind(ctx, d, tm.q, tm.k, tm.A);
      const A_chk = term_check(book, lhs, tm.A, None(), Typ(tm.s), ctx, d);
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
          throw Err(ctx, "a defined name", fun, tm.s, def);
        }
        const cols = term_unapply(lhs.t)[1];
        if (lhs.n !== 0 || arg.length < cols.length) {
          throw Err(ctx, "a whole self-call (one argument per parameter, inside the case tree)", tm, tm.s, def);
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
          throw Err(ctx, "a decreasing self-call (some live argument must shrink)", tm, tm.s, def);
        }
        f_inf = { tm: Ann(fun, tld.T), us: uses_nil() };
      } else {
        f_inf = term_infer(book, lhs, fun, qt, ctx, d);
      }
      for (const x of arg) {
        const f_ann = f_inf.tm as HAnn;
        const f_wnf = term_wnf(book, f_ann.T);
        if (f_wnf.$ !== "All") {
          throw Err(ctx, "a function type", f_ann.T, tm.s, def);
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
        throw Err(ctx, tm.k + " with " + String(adt.n) + (adt.n === 1 ? " parameter" : " parameters"), tm, tm.s, def);
      }
      const xs: HTerm[] = [];
      let tel: HTerm = adt.T;
      var us = uses_nil();
      for (const x of tm.x) {
        const t_all = tele_next(book, tel, ctx, def, tm.s);
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
      throw Err(ctx, "an annotated term (cannot infer)", tm, tm.s, def);
    }
  }
}

export function term_check(book: Book, lhs: LHS | null, tm: HTerm, qt: Quant, ty: HTerm, ctx: Ctx, d: number): Check {
  const def = lhs === null ? undefined : lhs.def;
  switch (tm.$) {
    // T == @q x:A -> B
    // Γ , x : qA ⊢ f(x) : B(x) ~ u
    // where u[x] <= q
    //       lhs steps by x while a parameter remains
    // ---------------------------------------------- check-lam
    // Γ ⊢ x => f : T ~ u - x
    case "Lam": {
      const b     = tm;
      const t_wnf = term_wnf(book, ty);
      if (t_wnf.$ !== "All") {
        throw Err(ctx, ty, tm, tm.s, def);
      }
      if (t_wnf.q.$ === "Many") {
        throw Err(ctx, "an affine binder (- or plain; + is not supported)", t_wnf, tm.s, def);
      }
      const x: HTerm = Var(tm.k, d);
      const f_lhs = (a: HTerm) => lhs !== null && lhs.n > 0 ? { t: term_apply(lhs.t, a), n: lhs.n - 1, def: lhs.def, qs: lhs.qs } : lhs;
      const f_ctx = ctx_bind(ctx, d, t_wnf.q, tm.k, t_wnf.A);
      const f_chk = term_check(book, f_lhs(x), tm.f(x), qt, t_wnf.B(x), f_ctx, d+1);
      const f_use = uses_get(f_chk.us, d);
      if (quant_join(f_use, t_wnf.q).$ !== t_wnf.q.$) {
        const obs = f_use.$ === "Many" ? tm.k + " (consumed more than once)" : quant_show(f_use) + tm.k;
        throw Err(ctx, quant_show(t_wnf.q) + tm.k, obs, tm.s, def);
      }
      var tm = Lam(b.k, b.i, (y: HTerm) => Laz(() => term_check(book, f_lhs(y), b.f(y), qt, t_wnf.B(y), f_ctx, d+1).tm), b.s);
      var tm = Ann(tm, ty);
      var us = uses_del(f_chk.us, d);
      return { tm, us };
    }
    // Γ ⊢ v : A ~ vu
    // Γ , x : qA ⊢ f(x) : T ~ fu
    // where q is - or plain; + is a formation error
    //       v is dead if q is -
    //       fu[x] <= q
    // ----------------------------------------------- check-let
    // Γ ⊢ q x = v; f : T ~ vu + fu - x
    case "Let": {
      if (tm.q.$ === "Many") {
        throw Err(ctx, "an affine binder (- or plain; + is not supported)", tm, tm.s, def);
      }
      const b = tm;
      const v_dem = quant_dem(tm.q, qt);
      const v_inf = term_infer(book, lhs, tm.v, v_dem, ctx, d);
      const v_ann = v_inf.tm as HAnn;
      const x: HTerm = Var(tm.k, d, tm.s, tm.v);
      const f_ctx = ctx_bind(ctx, d, tm.q, tm.k, v_ann.T);
      const f_chk = term_check(book, lhs, tm.f(x), qt, ty, f_ctx, d+1);
      const f_use = uses_get(f_chk.us, d);
      if (quant_join(f_use, tm.q).$ !== tm.q.$) {
        const obs = f_use.$ === "Many" ? tm.k + " (consumed more than once)" : quant_show(f_use) + tm.k;
        throw Err(ctx, quant_show(tm.q) + tm.k, obs, tm.s, def);
      }
      var tm = Let(b.k, b.i, v_inf.tm, (y: HTerm) => Laz(() => term_check(book, lhs, b.f(y), qt, ty, f_ctx, d+1).tm), b.s, b.q);
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
      const t_wnf = term_wnf(book, ty);
      if (t_wnf.$ !== "ADT") {
        throw Err(ctx, ty, tm, tm.s, def);
      }
      const ctr = ctrs_find(book_adt(book, t_wnf, ctx, def).c, tm.k);
      if (ctr === null) {
        throw Err(ctx, ty, tm, tm.s, def);
      }
      if (tm.x.length !== ctr.n) {
        throw Err(ctx, tm.k + " with " + String(ctr.n) + (ctr.n === 1 ? " field" : " fields"), tm, tm.s, def);
      }
      let tel: HTerm = ctr.T;
      for (const p of t_wnf.x) {
        const p_all = tele_next(book, tel, ctx, def, tm.s);
        tel = p_all.B(p);
      }
      const xs: HTerm[] = [];
      var us = uses_nil();
      for (const x of tm.x) {
        const f_all = tele_next(book, tel, ctx, def, tm.s);
        if (f_all.q.$ === "Many") {
          throw Err(ctx, "an affine field (- or plain; + is not supported)", f_all, tm.s, def);
        }
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
      const t_wnf = term_wnf(book, ty);
      if (t_wnf.$ !== "All") {
        throw Err(ctx, ty, tm, tm.s, def);
      }
      const t_all = t_wnf;
      if (t_all.q.$ === "Many") {
        throw Err(ctx, "an affine binder (- or plain; + is not supported)", t_all, tm.s, def);
      }
      if (qt.$ !== "None" && t_all.q.$ === "None") {
        throw Err(ctx, "a live scrutinee (a - scrutinee matches only in a dead region)", undefined, tm.s, def);
      }
      const a_wnf = term_wnf(book, t_all.A);
      if (a_wnf.$ !== "ADT") {
        throw Err(ctx, "a datatype", t_all.A, tm.s, def);
      }
      const rem = book_adt(book, a_wnf, ctx, def).c;
      const ctr = ctrs_find(rem, tm.k);
      if (ctr === null) {
        throw Err(ctx, "a constructor of " + a_wnf.k + " (missing, or already matched)", tm, tm.s, def);
      }
      let tel: HTerm = ctr.T;
      for (const p of a_wnf.x) {
        const p_all = tele_next(book, tel, ctx, def, tm.s);
        tel = p_all.B(p);
      }
      function term_check_mat_goal(cur: HTerm, n: number, xs: HTerm[]): HTerm {
        if (n === 0) {
          return t_all.B(Ctr(b.k, xs, b.s));
        } else {
          const c_all = tele_next(book, cur, ctx, def, b.s);
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
    // T == @q s:D<p..> -> P    D.c = []
    // where q is not - in a live region
    // ---------------------------------- check-efq
    // Γ ⊢ \ {} : T ~ {}
    case "Efq": {
      const t_wnf = term_wnf(book, ty);
      if (t_wnf.$ !== "All") {
        throw Err(ctx, ty, tm, tm.s, def);
      }
      if (t_wnf.q.$ === "Many") {
        throw Err(ctx, "an affine binder (- or plain; + is not supported)", t_wnf, tm.s, def);
      }
      if (qt.$ !== "None" && t_wnf.q.$ === "None") {
        throw Err(ctx, "a live scrutinee (a - scrutinee matches only in a dead region)", undefined, tm.s, def);
      }
      const a_wnf = term_wnf(book, t_wnf.A);
      if (a_wnf.$ !== "ADT") {
        throw Err(ctx, "a datatype", t_wnf.A, tm.s, def);
      }
      const rem = book_adt(book, a_wnf, ctx, def).c;
      if (rem.length !== 0) {
        throw Err(ctx, "cases for " + rem.map((c) => c.k).join(", "), tm, tm.s, def);
      }
      var tm = Ann(tm, ty);
      var us = uses_nil();
      return { tm, us };
    }
    // T == {a == b : A}    a == b
    // ---------------------------- check-rfl
    // Γ ⊢ {==} : T ~ {}
    case "Rfl": {
      const t_wnf = term_wnf(book, ty);
      if (t_wnf.$ !== "Eql") {
        throw Err(ctx, ty, tm, tm.s, def);
      }
      if (!term_equal(book, t_wnf.a, t_wnf.b, d)) {
        throw Err(ctx, t_wnf.a, t_wnf.b, tm.s, def);
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
      const e_wnf = term_wnf(book, e_ann.T);
      if (e_wnf.$ !== "Eql") {
        throw Err(ctx, "an equation {a == b : T}", e_ann.T, tm.s, def);
      }
      const p_typ = All<HBody>(Lone(), "_", 0, e_wnf.T, (x: HTerm) => All<HBody>(Lone(), "e", 0, Eql(e_wnf.a, x, e_wnf.T), () => Typ(), tm.s), tm.s);
      const p_chk = term_check(book, lhs, tm.p, None(), p_typ, ctx, d);
      const b_gol = term_apply(term_apply(tm.p, e_wnf.b), tm.e);
      if (!term_equal(book, b_gol, ty, d)) {
        throw Err(ctx, ty, b_gol, tm.s, def);
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
      let gol: HTerm = ty;
      for (let j = xs.length - 1; j >= 0; j--) {
        const A = (xs[j].tm as HAnn).T;
        const B = gol;
        gol = All<HBody>(Lone(), "_", 0, A, () => B, tm.s);
      }
      const f_chk = term_check(book, lhs, fun, qt, gol, ctx, d);
      var us = f_chk.us;
      let ap: HTerm = f_chk.tm;
      for (const x of xs) {
        ap = App(ap, x.tm, tm.s);
        us = uses_add(us, x.us);
      }
      var tm = Ann(ap, ty);
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
  throw Err(ctx, ty, x_ann.T, tm.s, def);
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
      const t_all = tele_next(book, tel, ctx, ctr.k);
      if (t_all.q.$ === "Many") {
        throw Err(ctx, "an affine binder (- or plain; + is not supported)", undefined, undefined, ctr.k);
      }
      const A_chk = term_check(book, null, t_all.A, None(), Typ(), ctx, d);
      const A_srt = term_wnf(book, (A_chk.tm as HAnn).T);
      if (A_srt.$ !== "Typ") {
        throw Err(ctx, Typ<HBody>(), t_all.A, undefined, ctr.k);
      }
      ctx = ctx_bind(ctx, d, t_all.q, t_all.k, t_all.A);
      tel = t_all.B(Var(t_all.k, d));
    }
    const exp = "a telescope tipped at " + k + " applied to its own parameters";
    const tip = term_wnf(book, tel);
    if (tip.$ !== "ADT" || tip.k !== k || tip.x.length !== adt.n || tip.r.length !== 0) {
      throw Err(ctx, exp, tip, undefined, ctr.k);
    }
    for (let d = 0; d < adt.n; d++) {
      const x = term_wnf(book, tip.x[d]);
      if (x.$ !== "Var" || x.i !== d) {
        throw Err(ctx, exp, tip, undefined, ctr.k);
      }
    }
  }
}

export function def_valid(book: Book, k: Name, def: Def): void {
  term_check(book, null, def.T, None(), Typ(), ctx_nil(), 0);
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

export function book_valid(book: Book): void {
  const seen = book_nil();
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
        break;
      }
      case "Def": {
        const dec: Def = { $: "Def", n: tld.n, T: tld.T, v: null };
        const fin = book.order.lastIndexOf(k) === i;
        seen.tlds[k] = dec;
        def_valid(scope, k, fin ? tld : dec);
        seen.tlds[k] = fin ? tld : dec;
        break;
      }
    }
  }
}
