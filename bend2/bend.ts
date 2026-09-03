// HUMAN NOTE: this file is 100% human-designed, and near fully audited by me.
// It is safest and most important file in this repository, as it contains the
// entire trusted kernel: evaluator, syntax, type and termination checker. All
// of that was designed by humans, and obsessivelly audited by us. That doesn't
// mean there aren't bugs, specially since it ships with additional features to
// make it much faster. It also drifts from the Lean spec in some important
// parts that will be aligned soon. The file is surprisingly small and will not
// grow significantly past this point, so, the trust in it will only increase
// over time, as we'll be auditing further and placing community bounties (with
// ProofMarket itself being the largest bounty on Bend's consistency, since any
// proof of falsehood would allow one to immediatelly claim every open bounty!)
// 
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
//   | Name
//
// Term ::=
//   | Var ::= Name
//   | Ref ::= Name
//   | Ann ::= "{" Term ":" Term "}"
//   | Typ ::= "Type" | "Data" | "Kind" "(" Term ")"
//   | Qnt ::= "Quant"
//   | Qua ::= "&0" | "&1" | "&2"
//   | Min ::= Term "<&>" Term
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
//   | Hol ::= "?" Name
//   | Grp ::= "(" Body ")"
//
// Case   ::= "case" [Term] ":" Body
// Match  ::= "match" [Term] ":" [Case]
// Local  ::= (Quant Name | Term)+ "=" Term+ ";"? Body
// Reply  ::= Term
// Body   ::= Match | Local | Reply
// Ctr    ::= Name "{" [Bind ","?] "}"
// ADT    ::= "type" Name ("<" [Bind ","?] ">")? "is" Term ":" [Ctr]
// Clause ::= ("forall" Quant | "exists") Name ":" Term ("where" Term)?
// Assert ::= "assert" Name ":" [Clause] Body
// Def    ::= ("@unsafe")? "def" Name "(" [Bind ","?] ")" ("->" Term)? ":" (Body | ["import" STRING]+)
// TLD    ::= ADT | Assert | Def
// Import ::= "import" "Base" | "import" Path "as" Name   (Path ends in .bend)
// Book   ::= [Import] [TLD]
//
// SUGARS
// ------
//
// Name   | Grammar                    | Term
// ------ | -------------------------- | ----
// Arrow  | A "->" B                   | @_:A -> B
// Exists | "&" Name ":" A "->" B      | Exists(A, x => B)
// Pair   | A "&" B                    | Pair(A, B)
// Or     | A "|" B                    | Or(A, B)
// Not    | "{" a "!=" b ":" T "}"     | {a == b : T} -> Empty
// Tuple  | "(" A ("," B)+ ")"         | Tuple{A, Tuple{B, ..}}
// List   | "[" [A ","?] "]", A "<>" B | Con{A, ..Nil{}}, Con{A, B}
// Nat    | NUMBER "n" ("+" T)?        | Succ{..Zero{}}, Succ{..T}
// U32    | NUMBER                     | U32{WCon{b, ..WNil{}}}
// F32    | NUMBER "." NUMBER [EXP]    | F32{WCon{b, ..WNil{}}}
// Chr    | "'" CHAR "'"               | Chr{U32}
// Str    | "\"" [CHAR] "\""           | SCon{Chr, ..SNil{}}
// Index  | x "[" i "]" ("<-" v)?      | Array.get(U32, x, i), ..set(..)
// Fill   | D "<" [A ","?] ">"         | D<&1.., A..>
// Plus   | "+" D ("<" [A ","?] ">")?  | D<&2.., A..>
//
// every word the parser dispatches on is reserved and names nothing:
// def, type, assert, match, case, do, return, forall, exists, where,
// is, import, Type, Data, Kind, Quant ("as" reads only on an import
// line, so it stays free).
// a file's namespace is its path without ".bend": an import's path
// joins onto the importer's namespace dir; a "0x<hash>/" path is its
// own namespace, read from BEND_STORE and fetched from BEND_HUB on a
// miss. "as Name" binds a per-file alias: Name.x resolves to the
// file's canonical name, so two aliases of one file agree, and a def
// of an aliased name fills it. "import Base" is the empty namespace.
// a def with no prior assert types itself: a Bind telescope and a
// "->" return type. a def after its assert takes bare names, no "->".
// a bare Bind name is -Name: Quant. Fill and Plus omit a datatype's
// leading Quant parameters as a block; Plus alone fills a quant-only D.
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
// variable is consumed at most once; a + binder licenses many uses and
// forms only when its type is Data. every live self-call descends, and
// no dead inhabitant is promoted to live evidence. this wall permits
// Type : Type, impredicativity and negative recursive types with no
// universe hierarchy and no positivity check: omega, Curry and Hurkens
// each contract a live function-valued binding, and no function type
// is Data. the gate is the wall.
// quantities None | Lone | Many (-x, x, +x) add sequentially (two live
// uses saturate to Many) and join pointwise-max across branches. the
// demand qt is None (dead) or Lone (live), never Many: a term checked
// at demand Many lets a binder inside it contract (McBride's system;
// Atkey 2018, 2.3, shows it also breaks substitution). an argument to
// a q binder checks at demand dem(q, qt), dead if q is -, else the
// ambient demand, and its measure adds once, unscaled: certify-once.
// so a Lone Data value may enter a + binder, let or field, and the
// callee copies the value. QTT forbids this: a 1 never becomes an ω
// (Atkey scales the argument's measure by the binder's ω), and a
// linear value is copied only by walking it. QTT affords that because
// its default is ω; Bend's default is Lone, so without promotion only
// closed data would ever be reusable, and input only by an O(n) walk.
// the price is a narrower theorem: term-substitution reduction does
// not preserve the measure (unfold f(+x) at f(y): y counts twice under
// its plain binder), so subject reduction for usage is claimed for
// weak by-value reduction of closed terms, the only reduction the
// machine performs: y is a value when f unfolds, its resources were
// consumed once, and the copy is Data, which owns nothing by the gate.
// three invariants outside the checker carry this: no pass duplicates
// a term (wnf shares every argument, let value and field in a cell;
// the compiler is strict); a type with runtime ownership (File,
// Socket, Array) is Type, never Data; a compiler may drop a copy the
// source spelled, never add one.
// every type has a kind Kind(q) over a quantity q : Quant, &0 (None),
// &1 (Lone) or &2 (Many); Type is Kind(&1), Data is Kind(&2), and a
// - binder's domain checks at Kind(&0). term_compare (LE) orders
// kinds by the quantity order: Kind(g) fits Kind(h) when h <= g, so
// Data fits every kind and every kind fits Type, and a meet fits every
// kind under one of its sides, never else. a binder q x: A needs A to
// fit Kind(q): its type's quantity is at least q. a function type
// is Type (a closure captures), an equation is Data (evidence is
// erased), a datatype declares its kind, Kind(G) over its parameters,
// and the meet a <&> b is the minimum, reduced only when forced: &2 is
// the identity, &0 absorbs, two literals meet, a stuck side stays
// stuck, so no definition order can decide it early. both its operands
// check at the ambient demand and their measures add, so a meet never
// launders a live occurrence past the tally. adt_valid earns
// G: every live field's kind must fit Kind(G) in the real constructor
// context, so a constructor-local quantity never reaches G and a
// function field never sits in Data.
// a type position, an erased (-) argument, an equality endpoint or a
// motive checks dead: it may diverge and inhabit Empty; no rule coerces
// dead to live. a +field is QTT's ω-tensor read the Bend way: it forms
// only at Data, building it certifies its argument once, and matching
// a Lone node still yields it Many; a -field is absent from storage
// and dead; a pattern binder's quantity is its field's times its
// scrutinee's.
// equality is intensional; elimination is the J axiom, %e@E : P; f,
// and a stuck rewrite fires only when its evidence reaches {==}.
// conversion is term_compare LE -- a fits b, a preorder, up to eta:
// directional only at kinds and ADT residuals (removing more
// constructors fits removing fewer), a function type compares its
// domains swapped, and every part that flows both ways (an argument,
// a parameter, a field, an equation endpoint) compares EQ.
// every live self-call descends on a strict
// subterm in its own case tree, live columns compared EQ left to right,
// erased columns skipped. trusted claims: subject reduction (for
// by-value reduction), progress, weak normalization of closed live
// terms, no closed live inhabitant of Empty.
// an @unsafe def opts out of the wall: its self-calls skip descent
// and its binder domains form + at any kind, so the claims above do
// not cover a book that uses one. a hole ?name fails every check,
// shown against the goal; ?TODO alone checks at any goal and marks
// the book incomplete.

import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import * as url from "node:url";

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
  | { $: "Var"; k: Name; i: number; v?: HTerm }                                    // x
  | { $: "Ref"; k: Name; b?: Bool }                                                // x
  | { $: "Sub"; i: number; v: TermOf<B>; f: TermOf<B> }                            // x <- v; f
  | { $: "Let"; k: Name[]; i: number[]; q: Quant[]; v: TermOf<B>[]; f: LetsOf<B> } // x y = v w; f
  | { $: "Typ"; g: TermOf<B> }                                                     // Kind(g)
  | { $: "Qnt" }                                                                   // Quant
  | { $: "Qua"; q: Quant }                                                         // &1, &2
  | { $: "Min"; a: TermOf<B>; b: TermOf<B> }                                       // a <&> b
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
  | { $: "Hol"; k: Name }                                                          // ?name
  | { $: "Ann"; x: TermOf<B>; T: TermOf<B> }                                       // {x : T}
) & { s?: Span };

export type LTerm = TermOf<[LTerm]>;
export type HBody = (x: HTerm) => HTerm;
export type HTerm = TermOf<HBody>;

// Env
export type Env = PMap<HTerm>;

// Definitions & Book
export type Ctr  = { k: Name; n: number; T: HTerm }
export type Ctrs = Array<Ctr>;
export type ADT  = { $: "ADT"; n: number; g: number; T: HTerm; c: Ctrs; };
export type Def  = { $: "Def"; n: number; T: HTerm; v: HTerm | null; e?: LTerm; b?: Bool; u?: Bool; i?: string[]; };
export type TLD  = ADT | Def;
export type Book = { tlds: Record<Name, TLD>; ctrs: Record<Name, Ctr>; order: Name[]; hols: number; };

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
export type Parse = { book: Book; dir: string; str: string; pos: Loc; sc: Scope; ns: string; al: Record<Name, Name>; };
export type Span  = { src: string; beg: Loc; end: Loc; };

// Machine
export type LHS   = { t: HTerm; n: number; def: Name; qs: Quant[]; u?: Bool };
export type Frame =
  | { $: "APP"; x: HTerm } // _(x)
  | { $: "MAT"; t: Extract<HTerm, { $: "Mat" }>; e: HTerm; lhs: { t: () => HTerm; n: number } | null } // \{c:h;m}(_)
  | { $: "VAR"; l: Extract<HTerm, { $: "Var" }>; a?: Extract<HTerm, { $: "Ann" }> } // a share cell being filled
  | { $: "MNA"; b: HTerm; s?: Span } // _ <&> b
  | { $: "MNB"; a: HTerm; s?: Span } // a <&> _

// Infer
export type Infer = { tm: LTerm; ty: HTerm; us: Uses };
export type Check = { tm: LTerm; us: Uses };

// Error
export type Expr = HTerm | string;
export type Err  = { $: "Err"; bok: Book; exp: Expr; obs?: Expr; ctx: Ctx; def?: Name; spn?: Span; };

// Constructors
// ============

// Term
// ----

export function Var<X>(k: Name, i: number, s?: Span, v?: HTerm): TermOf<X> {
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

export function Typ<X>(g: TermOf<X>, s?: Span): TermOf<X> {
  return { $: "Typ", g, s };
}

export function Qnt<X>(s?: Span): TermOf<X> {
  return { $: "Qnt", s };
}

export function Qua<X>(q: Quant, s?: Span): TermOf<X> {
  return { $: "Qua", q, s };
}

export function Min<X>(a: TermOf<X>, b: TermOf<X>, s?: Span): TermOf<X> {
  return { $: "Min", a, b, s };
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

export function Hol<X>(k: Name, s?: Span): TermOf<X> {
  return { $: "Hol", k, s };
}

export function Ann<X>(x: TermOf<X>, T: TermOf<X>, s?: Span): TermOf<X> {
  return { $: "Ann", x, T, s };
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

// Infer
// -----

export function Infer(tm: LTerm, ty: HTerm, us: Uses): Infer {
  return { tm: Ann(tm, Var("_", -1, undefined, ty)), ty, us };
}

export function Check(tm: LTerm, ty: HTerm, us: Uses): Check {
  return { tm: Ann(tm, Var("_", -1, undefined, ty)), us };
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
      return pmap_set(Bin<T>(null, map, map), key, val);
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

export function quant_mul(q: Quant, x: Quant): Quant {
  switch (q.$) {
    case "None": {
      return None();
    }
    case "Lone": {
      return x;
    }
    case "Many": {
      return quant_add(x, x);
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

export function quant_used(book: Book, ctx: Ctx, k: Name, q: Quant, u: Quant, s: Span | undefined, def?: Name): void {
  if (quant_join(u, q).$ !== q.$) {
    let obs = quant_show(u) + k;
    if (u.$ === "Many") {
      obs = k + " (consumed more than once)";
    }
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

export function lhs_kind(lhs: LHS, q: Quant): Quant {
  return lhs.u === true && q.$ === "Many" ? Lone() : q;
}

export function lhs_descend(lhs: LHS, sp: HTerm[]): Cmp {
  const cols = term_unapply(lhs.t)[1];
  let ord: Cmp = "EQ";
  for (let j = 0; j < cols.length && j < sp.length && ord === "EQ"; j++) {
    ord = term_descend(lhs.qs[j], sp[j], cols[j]);
  }
  return ord;
}

// Term
// ====

export function term_apply(fn: HTerm, tm: HTerm): HTerm {
  const f = term_strip(fn);
  if (f.$ === "Lam") {
    return f.f(tm);
  }
  return App(f, tm);
}

export function term_unapply<X>(tm: TermOf<X>): [TermOf<X>, TermOf<X>[]] {
  const xs: TermOf<X>[] = [];
  let cur = tm;
  while (true) {
    switch (cur.$) {
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

export function term_cell(t: HTerm, k: Name = "_"): HTerm {
  if (t.$ === "Var" && t.i < 0) {
    return t;
  }
  return Var(k, -1, t.s, t);
}

export function term_force<X>(t: TermOf<X>): TermOf<X> {
  while (t.$ === "Var" && t.v !== undefined) {
    t = t.v as TermOf<X>;
  }
  return t;
}

export function term_strip<X>(tm: TermOf<X>): TermOf<X> {
  let t = term_force(tm);
  while (t.$ === "Ann") {
    t = term_force(t.x);
  }
  return t;
}

export function term_higher(tm: LTerm, env: Env = Emp<HTerm>()): HTerm {
  switch (tm.$) {
    case "Var": {
      if (tm.i < 0) {
        return tm;
      }
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
      return term_higher(tm.f, pmap_set(env, tm.i, v));
    }
    case "Let": {
      const b = tm;
      const v = b.v.map((x) => term_higher(x, env));
      return Let(b.k, b.i, v, (xs: HTerm[]) => {
        let e = env;
        for (let j = 0; j < xs.length; j++) {
          e = pmap_set(e, b.i[j], xs[j]);
        }
        return term_higher(b.f, e);
      }, b.s, b.q);
    }
    case "Typ": {
      return Typ(term_higher(tm.g, env), tm.s);
    }
    case "Qnt":
    case "Qua": {
      return tm;
    }
    case "Min": {
      return Min(term_higher(tm.a, env), term_higher(tm.b, env), tm.s);
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
      return App(term_higher(tm.f, env), term_higher(tm.x, env), tm.s);
    }
    case "ADT": {
      return ADT(tm.k, tm.x.map((x) => term_higher(x, env)), tm.s, tm.r);
    }
    case "Ctr": {
      return Ctr(tm.k, tm.x.map((x) => term_higher(x, env)), tm.s);
    }
    case "Mat": {
      return Mat(tm.k, term_higher(tm.h, env), term_higher(tm.m, env), tm.s);
    }
    case "Efq": {
      return Efq(tm.s);
    }
    case "Eql": {
      return Eql(term_higher(tm.a, env), term_higher(tm.b, env), term_higher(tm.T, env), tm.s);
    }
    case "Rfl": {
      return Rfl(tm.s);
    }
    case "Rwt": {
      return Rwt(term_higher(tm.e, env), term_higher(tm.p, env), term_higher(tm.f, env), tm.s);
    }
    case "Hol": {
      return Hol(tm.k, tm.s);
    }
    case "Ann": {
      return Ann(term_higher(tm.x, env), term_higher(tm.T, env), tm.s);
    }
  }
}

export function term_lower(term: HTerm, d: number = 0): LTerm {
  const tm = term_force(term);
  switch (tm.$) {
    case "Var": {
      return Var(tm.k, tm.i, tm.s);
    }
    case "Ref": {
      return Ref(tm.k, tm.s, tm.b);
    }
    case "Sub": {
      return Sub(tm.i, term_lower(tm.v, d), term_lower(tm.f, d), tm.s);
    }
    case "Let": {
      const xs = tm.k.map((k, j): HTerm => Var(k, d + j));
      const vs = tm.v.map((v) => term_lower(v, d));
      return Let(tm.k, xs.map((_, j) => d + j), vs, term_lower(tm.f(xs), d + tm.k.length), tm.s, tm.q);
    }
    case "Typ": {
      return Typ(term_lower(tm.g, d), tm.s);
    }
    case "Qnt":
    case "Qua": {
      return tm;
    }
    case "Min": {
      return Min(term_lower(tm.a, d), term_lower(tm.b, d), tm.s);
    }
    case "All": {
      const x: HTerm = Var(tm.k, d);
      return All(tm.q, tm.k, d, term_lower(tm.A, d), term_lower(tm.B(x), d + 1), tm.s);
    }
    case "Lam": {
      const x: HTerm = Var(tm.k, d);
      return Lam(tm.k, d, term_lower(tm.f(x), d + 1), tm.s);
    }
    case "App": {
      return App(term_lower(tm.f, d), term_lower(tm.x, d), tm.s);
    }
    case "ADT": {
      return ADT(tm.k, tm.x.map((x) => term_lower(x, d)), tm.s, tm.r);
    }
    case "Ctr": {
      return Ctr(tm.k, tm.x.map((x) => term_lower(x, d)), tm.s);
    }
    case "Mat": {
      return Mat(tm.k, term_lower(tm.h, d), term_lower(tm.m, d), tm.s);
    }
    case "Efq": {
      return Efq(tm.s);
    }
    case "Eql": {
      return Eql(term_lower(tm.a, d), term_lower(tm.b, d), term_lower(tm.T, d), tm.s);
    }
    case "Rfl": {
      return Rfl(tm.s);
    }
    case "Rwt": {
      return Rwt(term_lower(tm.e, d), term_lower(tm.p, d), term_lower(tm.f, d), tm.s);
    }
    case "Hol": {
      return Hol(tm.k, tm.s);
    }
    case "Ann": {
      return Ann(term_lower(tm.x, d), term_lower(tm.T, d), tm.s);
    }
  }
}

export function term_descend(q: Quant, arg: HTerm, col: HTerm): Cmp {
  switch (q.$) {
    case "None": {
      return "EQ";
    }
    default: {
      break;
    }
  }
  const a = term_strip(arg);
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
          const fld = term_descend(Lone(), a.x[j], p.x[j]);
          ord = fld === "EQ" ? ord : fld;
        }
        if (ord !== "GT") {
          return ord;
        }
      }
      for (const q of p.x) {
        const sub = term_descend(Lone(), a, q);
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
  return { tlds: Object.create(null), ctrs: Object.create(null), order: [], hols: 0 };
}

export function book_ctr(book: Book, k: Name): Ctr | null {
  return book.ctrs[k] ?? null;
}

export function book_fam(book: Book, k: Name): Name {
  let t = term_strip((book_ctr(book, k) as Ctr).T);
  for (let d = 0; t.$ === "All"; d++) {
    t = term_strip(t.B(Var(t.k, d)));
  }
  return t.$ === "ADT" ? t.k : k;
}

export function book_adt(book: Book, tm: Extract<HTerm, { $: "ADT" }>, ctx: Ctx, def?: Name): ADT {
  const tld = book.tlds[tm.k];
  if (tld === undefined || tld.$ !== "ADT") {
    throw Err(book, ctx, "a declared datatype (unknown: " + tm.k + ")", undefined, tm.s, def);
  }
  if (tm.r.length === 0) {
    return tld;
  }
  return { $: "ADT", n: tld.n, g: tld.g, T: tld.T, c: tld.c.filter((c) => !tm.r.includes(c.k)) };
}

const BASE_BEND  = fs.realpathSync(url.fileURLToPath(new URL("./base.bend", import.meta.url)));
const BEND_STORE = path.resolve(process.env.BEND_STORE ?? path.join(os.homedir(), ".bend", "store"));
const BEND_HUB   = process.env.BEND_HUB ?? "https://proofmarket.com";

export async function book_load(book: Book, file: string, ns: string, seen: Map<string, string | null>): Promise<number> {
  if (file.startsWith(BEND_STORE + "/") && !fs.existsSync(file)) {
    const sub = file.slice(BEND_STORE.length + 1);
    const res = await fetch(BEND_HUB + "/api/v1/files/" + sub);
    if (!res.ok) {
      throw Err(book, ctx_nil(), "a published package (" + BEND_HUB + " has no " + sub + ")");
    }
    fs.mkdirSync(path.dirname(file), { recursive: true });
    fs.writeFileSync(file, await res.text());
  }
  const real = fs.realpathSync(file);
  const done = seen.get(real);
  if (done === null) {
    throw Err(book, ctx_nil(), "an acyclic import graph (a cycle reaches " + file + ")");
  }
  if (done !== undefined) {
    if (done !== ns) {
      throw Err(book, ctx_nil(), "one namespace per file (" + file + " is both '" + done + "' and '" + ns + "')");
    }
    return book.order.length;
  }
  seen.set(real, null);
  const dir   = file.slice(0, file.lastIndexOf("/") + 1);
  const al    : Record<Name, Name> = Object.create(null);
  const text  = fs.readFileSync(file, "utf8");
  const lines = text.split("\n");
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i].trim();
    const m = line.match(/^import(\s.*|)$/);
    if (m !== null) {
      const h = m[1].match(/^\s+(\S+)(?:\s+as\s+([A-Za-z_][A-Za-z0-9_]*))?\s*(?:#.*)?$/);
      if (h === null || (h[2] === undefined && h[1] !== "Base")) {
        throw Err(book, ctx_nil(), "an import ('import Base', or 'import <path> as <Name>')");
      }
      if (h[2] === undefined) {
        await book_load(book, BASE_BEND, "", seen);
      } else {
        const rel = path.posix.normalize(h[1]);
        if (!rel.endsWith(".bend")) {
          const beg = text.split("\n", i).join("\n").length + (i && 1) + lines[i].indexOf(h[1]);
          throw Err(book, ctx_nil(), "an import of a .bend file", "'" + h[1] + "'", { src: text, beg, end: beg });
        }
        let at  = dir + rel;
        let sub = path.posix.join(path.posix.dirname(ns), rel);
        if (rel.startsWith("/")) {
          at  = rel;
          sub = rel;
        }
        if (/^0x[0-9a-f]+\//.test(rel)) {
          at  = BEND_STORE + "/" + rel;
          sub = rel;
        }
        al[h[2]] = sub.replace(/\.bend$/, "");
        await book_load(book, at, al[h[2]], seen);
      }
      lines[i] = "";
      continue;
    }
    if (line !== "" && !line.startsWith("#")) {
      break;
    }
  }
  const n0 = book.order.length;
  parse_book(book, dir, lines.join("\n"), ns, al);
  if (real === BASE_BEND) {
    for (const k of book.order.slice(n0)) {
      const tld = book.tlds[k];
      if (tld.$ === "Def") {
        tld.b = true;
      }
    }
  }
  seen.set(real, ns);
  return n0;
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

export function tele_fill(book: Book, tel: HTerm, xs: HTerm[], ctx: Ctx, def?: Name, s?: Span): HTerm {
  let out = tel;
  for (const x of xs) {
    out = tele_head(book, out, ctx, def, s).B(x);
  }
  return out;
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

// Word
// ====

export function word_to_term(n: U32, s?: Span): LTerm {
  let out: LTerm = Ctr("WNil", [], s);
  for (let i = 31; i >= 0; i--) {
    const bit = (n >>> i) & 1;
    out = Ctr("WCon", [Ctr(bit === 1 ? "True" : "False", [], s), out], s);
  }
  return out;
}

// U32
// ===

export function u32_to_term(n: U32, s?: Span): LTerm {
  return Ctr("U32", [word_to_term(n, s)], s);
}

export function u32_from_term<X>(tm: TermOf<X>, k: Name = "U32"): number | null {
  const w0 = term_strip(tm);
  if (w0.$ !== "Ctr" || w0.k !== k || w0.x.length !== 1) {
    return null;
  }
  let n = 0;
  let i = 0;
  let w = term_strip(w0.x[0]);
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

// F32
// ===

const F32_VIEW = new DataView(new ArrayBuffer(4));

export function f32_to_bits(v: number): U32 {
  F32_VIEW.setFloat32(0, v);
  return F32_VIEW.getUint32(0);
}

export function f32_from_bits(n: U32): number {
  F32_VIEW.setUint32(0, n);
  return F32_VIEW.getFloat32(0);
}

export function f32_to_term(v: number, s?: Span): LTerm {
  return Ctr("F32", [word_to_term(f32_to_bits(v), s)], s);
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

const ESCAPES: Record<string, U32> = {
  "n": 10, "t": 9, "r": 13, "0": 0, "\\": 92, "'": 39, '"': 34,
};

export function char_show(n: U32, quote: string): string | null {
  for (const [k, c] of Object.entries(ESCAPES)) {
    if (c === n && ((k !== "'" && k !== '"') || k === quote)) {
      return "\\" + k;
    }
  }
  if (n < 32 || n === 127 || (n >= 0xd800 && n <= 0xdfff) || n > 0x10ffff) {
    return null;
  }
  return String.fromCodePoint(n);
}

export function term_show(term: LTerm, top: number = 0, bnd: Name[] = []): string {
  function term_show_sugar_exi(tm: LTerm, prc: number): string | null {
    if (tm.$ !== "App") {
      return null;
    }
    const h = tm.f;
    const b = tm.x;
    if (h.$ !== "App" || b.$ !== "Lam") {
      return null;
    }
    const r = h.f;
    if (r.$ !== "Ref" || r.k !== "Exists") {
      return null;
    }
    const A = go(h.x, 2);
    bnd.push(b.k);
    const f = go(b.f, 1);
    bnd.pop();
    const s = "&" + b.k + ":" + A + " -> " + f;
    return prc > 1 ? "(" + s + ")" : s;
  }
  function term_show_sugar_nat(tm: LTerm, prc: number): string | null {
    let n = 0;
    let t = tm;
    while (t.$ === "Ctr" && t.k === "Succ" && t.x.length === 1) {
      n += 1;
      t = t.x[0];
    }
    if (t.$ === "Ctr" && t.k === "Zero" && t.x.length === 0) {
      return String(n) + "n";
    }
    if (n === 0) {
      return null;
    }
    const s = String(n) + "n+" + go(t, 1);
    return prc > 1 ? "(" + s + ")" : s;
  }
  function term_show_sugar_chr(tm: LTerm, quote: string): string | null {
    if (tm.$ !== "Ctr" || tm.k !== "Chr" || tm.x.length !== 1) {
      return null;
    }
    const n = u32_from_term(tm.x[0]);
    if (n === null || n > 0x10ffff) {
      return null;
    }
    return char_show(n, quote);
  }
  function term_show_sugar_str(tm: LTerm): string | null {
    let out = "";
    let t = tm;
    while (t.$ === "Ctr" && t.k === "SCon" && t.x.length === 2) {
      const c = term_show_sugar_chr(t.x[0], "\"");
      if (c === null) {
        return null;
      }
      out += c;
      t = t.x[1];
    }
    if (out === "" || t.$ !== "Ctr" || t.k !== "SNil" || t.x.length !== 0) {
      return null;
    }
    return "\"" + out + "\"";
  }
  function go(tm: LTerm, prc: number): string {
    switch (tm.$) {
      case "Var": {
        return bnd.lastIndexOf(tm.k) === tm.i ? tm.k : tm.k + "^" + String(tm.i);
      }
      case "Ref": {
        return bnd.includes(tm.k) ? tm.k + "^" : tm.k;
      }
      case "Sub": {
        return go(tm.f, prc);
      }
      case "Let": {
        const vs = tm.v.map((v) => go(v, 1));
        for (const k of tm.k) {
          bnd.push(k);
        }
        const f = go(tm.f, 0);
        bnd.length -= tm.k.length;
        const ks = tm.k.map((k, j) => quant_show(tm.q[j]) + k);
        const s  = ks.join(" ") + " = " + vs.join(" ") + "; " + f;
        return prc > 0 ? "(" + s + ")" : s;
      }
      case "Typ": {
        const g = tm.g;
        if (g.$ === "Qua" && g.q.$ === "Lone") {
          return "Type";
        }
        if (g.$ === "Qua" && g.q.$ === "Many") {
          return "Data";
        }
        return "Kind(" + go(tm.g, 0) + ")";
      }
      case "Qnt": {
        return "Quant";
      }
      case "Qua": {
        return { None: "&0", Lone: "&1", Many: "&2" }[tm.q.$];
      }
      case "Min": {
        const s = go(tm.a, 2) + " <&> " + go(tm.b, 2);
        return prc > 1 ? "(" + s + ")" : s;
      }
      case "All": {
        const A = go(tm.A, 2);
        bnd.push(tm.k);
        const B = go(tm.B, 1);
        bnd.pop();
        const s = "@" + quant_show(tm.q) + tm.k + ":" + A + " -> " + B;
        return prc > 1 ? "(" + s + ")" : s;
      }
      case "Lam": {
        bnd.push(tm.k);
        const f = go(tm.f, 0);
        bnd.pop();
        const s = tm.k + " => " + f;
        return prc > 0 ? "(" + s + ")" : s;
      }
      case "App": {
        const sug = term_show_sugar_exi(tm, prc);
        if (sug !== null) {
          return sug;
        }
        const [h, xs] = term_unapply(tm);
        const hs = go(h, 2);
        const as = xs.map((x) => go(x, 0));
        return hs + "(" + as.join(", ") + ")";
      }
      case "ADT": {
        const as = tm.x.map((x) => go(x, 0));
        const rs = tm.r.map((c) => " - " + c + "{}").join("");
        const s  = tm.k + (as.length === 0 && rs === "" ? "" : "<" + as.join(", ") + ">") + rs;
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
        const as = tm.x.map((x) => go(x, 0));
        return tm.k + "{" + as.join(", ") + "}";
      }
      case "Mat": {
        const arms: string[] = [];
        let m: LTerm = tm;
        while (m.$ === "Mat") {
          arms.push(m.k + ": " + go(m.h, 1));
          m = m.m;
        }
        if (m.$ !== "Efq") {
          arms.push(go(m, 1));
        }
        return "\\{" + arms.join("; ") + "}";
      }
      case "Efq": {
        return "\\{}";
      }
      case "Eql": {
        return "{" + go(tm.a, 1) + " == " + go(tm.b, 1) + " : " + go(tm.T, 1) + "}";
      }
      case "Rfl": {
        return "{==}";
      }
      case "Hol": {
        return "?" + tm.k;
      }
      case "Rwt": {
        const e  = go(tm.e, 1);
        const mp = term_strip(tm.p);
        const mb = mp.$ === "Lam" ? term_strip(mp.f) : mp;
        let n = "";
        let P;
        if (mp.$ === "Lam" && mb.$ === "Lam") {
          bnd.push(mp.k, mb.k);
          P = go(mb.f, 1);
          bnd.length -= 2;
          n = mb.k === "" ? "" : mb.k + "@";
        } else {
          P = go(tm.p, 1);
        }
        const f = go(tm.f, 0);
        const s = "%" + n + e + " : " + P + "; " + f;
        return prc > 0 ? "(" + s + ")" : s;
      }
      case "Ann": {
        return "{" + go(tm.x, 1) + " : " + go(tm.T, 1) + "}";
      }
    }
  }
  return go(term, top);
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

export function typeless_show(book: Book, ctx: Ctx, tm: HTerm): string {
  return "non-inferrable term '" + expr_show(book, tm, ctx_scope(ctx)) + "'";
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
  "def", "type", "assert", "match", "case", "do", "return",
  "forall", "exists", "where", "is", "import",
  "Type", "Data", "Kind", "Quant",
]);

const QUAS: Record<string, Quant> = { "0": None(), "1": Lone(), "2": Many() };

export function parse_new(book: Book, dir: string, str: string, ns: string = "", al: Record<Name, Name> = Object.create(null)): Parse {
  return { book, dir, str, pos: 0, sc: { stk: [], frs: 0 }, ns, al };
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
  const dot = k.indexOf(".");
  let q = parse_qual(p, k);
  if (dot !== -1 && k.slice(0, dot) in p.al) {
    q = p.al[k.slice(0, dot)] + k.slice(dot);
  }
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
      throw Err(book, ctx_nil(), "a pattern (a binder or a constructor)", term_show(term_lower(term_higher(t), 0)), t.s);
    }
  }
}

// Term
// ----

export function parse_term(p: Parse, lvl: number = 0): LTerm {
  parse_skip(p);
  const beg  = p.pos;
  const base = parse_term_base(p, beg);
  base.s ??= parse_span(p, beg);
  return parse_term_ops(p, base, lvl);
}

export function parse_term_base(p: Parse, beg: Loc): LTerm {
  const c = parse_peek(p);
  if (char_is_head(c)) {
    return parse_term_base_word(p, parse_lexeme(p), beg);
  }
  if (/[0-9]/.test(c)) {
    return parse_term_num(p);
  }
  switch (c) {
    case "@": {
      return parse_term_all(p, false);
    }
    case "&": {
      const q = QUAS[p.str[p.pos + 1] ?? ""];
      if (q !== undefined) {
        parse_bump(p);
        parse_bump(p);
        return Qua(q, parse_span(p, beg));
      }
      return parse_term_all(p, true);
    }
    case "+": {
      parse_bump(p);
      const t = parse_term(p, 5);
      const s = parse_span(p, beg);
      let k = "";
      if (t.$ === "ADT") {
        k = t.k;
      } else if (t.$ === "Var" || t.$ === "Ref") {
        k = parse_reso(p, t.k);
      }
      const tld = p.book.tlds[k];
      if (tld === undefined || tld.$ !== "ADT" || tld.g === 0 || tld.g < tld.n && t.$ !== "ADT") {
        parse_fail(p, "a quantified datatype after + (+D<..> sets D's leading quantities to &2)");
      }
      const xs = t.$ === "ADT" ? t.x : Array.from({ length: tld.n }, (): LTerm => Qua(Lone(), s));
      return ADT(k, xs.map((x, i) => i < tld.g ? Qua(Many(), s) : x), s);
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
    case "?": {
      parse_bump(p);
      const k = parse_name(p);
      if (k === "TODO") {
        p.book.hols += 1;
      }
      return Hol(k, parse_span(p, beg));
    }
    default: {
      parse_fail(p, "a term");
    }
  }
}

export function parse_term_base_word(p: Parse, k: Name, beg: Loc): LTerm {
  if (k === "Type") {
    return Typ(Qua(Lone()), parse_span(p, beg));
  }
  if (k === "Data") {
    return Typ(Qua(Many()), parse_span(p, beg));
  }
  if (k === "Quant") {
    return Qnt(parse_span(p, beg));
  }
  if (k === "Kind") {
    parse_eat(p, "(");
    const g = parse_term(p);
    parse_eat(p, ")");
    return Typ(g, parse_span(p, beg));
  }
  if (k === "do") {
    return parse_term_do(p);
  }
  if (k === "match") {
    parse_fail(p, "a term (a match heads a def body, not a term)");
  }
  if (k === "case") {
    parse_fail(p, "a match heading this case (this case is orphaned)");
  }
  if (k === "return") {
    parse_fail(p, "a do-block heading this return");
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
  ["%.",  11, false, "F32.mod"],
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
  ["%",   11, false, "U32.mod"],
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
    if (op[0] === "%" && !/\s/.test(nx)) {
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
        const v = parse_term(p, 2);
        out = App(App(App(App(Ref("Array.set", s), Ref("U32", s), s),
          out, s), ix, s), v, s);
      } else {
        out = App(App(App(Ref("Array.get", s), Ref("U32", s), s),
          out, s), ix, s);
      }
      continue;
    }
    if (parse_at(p, "<") && !"-=<.>".includes(p.str[p.pos + 1] ?? "") && !parse_at(p, "<&>")
      && (lvl <= 4 || /\S/.test(p.str[p.pos - 1] ?? ""))) {
      parse_bump(p);
      const a = parse_term(p, 5);
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
        const k   = parse_reso(p, out.k);
        const tld = p.book.tlds[k];
        if (tld !== undefined && tld.$ === "ADT" && xs.length + tld.g === tld.n) {
          xs.unshift(...Array.from({ length: tld.g }, (): LTerm => Qua(Lone(), s)));
        }
        out = ADT(k, xs, s);
      } else {
        out = App(App(Ref("U32.is_lt", s), out, s), a, s);
      }
      continue;
    }
    if (lvl === 0 && parse_take(p, "=>")) {
      if (out.$ !== "Var") {
        parse_fail(p, "a lambda binder (one name: k => body)");
      }
      const n0 = p.sc.stk.length;
      const i  = parse_open(p, out.k);
      const f  = parse_block(p);
      parse_close(p, n0);
      out = Lam(out.k, i, f, out.s);
      continue;
    }
    if (lvl === 0 && parse_take(p, "->")) {
      const B = parse_term(p);
      const s = parse_grow(p, out);
      out = All(Lone(), "_", parse_open(p, "_"), out, B, s);
      continue;
    }
    if (lvl <= 5 && parse_take(p, "<&>")) {
      const b = parse_term(p, 5);
      out = Min(out, b, parse_grow(p, out));
      continue;
    }
    const op = parse_infx_find(p);
    if (op === null || op[1] < lvl || parse_at(p, "<-")) {
      return out;
    }
    parse_take(p, op[0]);
    const b = parse_term(p, op[2] ? op[1] : op[1] + 1);
    const s = parse_grow(p, out);
    if (op[0] === "<>") {
      out = Ctr("Con", [out, b], s);
    } else if (op[0] === "&") {
      out = App(App(Ref("Pair", s), out, s), b, s);
    } else if (op[0] === "|") {
      out = App(App(Ref("Or", s), out, s), b, s);
    } else {
      out = App(App(Ref(op[3], s), out, s), b, s);
    }
  }
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

export function parse_term_all(p: Parse, exi: boolean): LTerm {
  parse_bump(p);
  const q = exi ? Lone() : parse_quant(p);
  const k = parse_name(p);
  parse_eat(p, ":");
  const A = parse_term(p, 1);
  parse_eat(p, "->");
  const n0 = p.sc.stk.length;
  const i  = parse_open(p, k);
  const B  = parse_term(p);
  parse_close(p, n0);
  if (exi) {
    return App(App(Ref("Exists"), A), Lam(k, i, B));
  }
  return All(q, k, i, A, B);
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
    return All(Lone(), "_", parse_open(p, "_"), Eql(a, b, T), Ref("Empty"));
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
      let txt = s + parse_bump(p);
      while (/[0-9]/.test(parse_peek(p))) {
        txt += parse_bump(p);
      }
      if (/[eE]/.test(parse_peek(p)) && /[0-9+-]/.test(p.str[p.pos + 1] ?? "")) {
        txt += parse_bump(p) + (/[+-]/.test(parse_peek(p)) ? parse_bump(p) : "");
        while (/[0-9]/.test(parse_peek(p))) {
          txt += parse_bump(p);
        }
      }
      const v = Math.fround(Number(txt));
      if (!isFinite(v)) {
        parse_fail(p, "a float literal with a finite f32 value (got " + txt + ")");
      }
      return f32_to_term(v, parse_span(p, beg));
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
  function parse_term_do_call(op: Name, xs: LTerm[], ys: LTerm[], s: Span): LTerm {
    let fn: LTerm = Ref(parse_reso(p, m + "." + op), s);
    for (const x of ls.concat(xs, R === null ? [] : [R], ys)) {
      fn = App(fn, x, s);
    }
    return fn;
  }
  parse_skip(p);
  const beg = p.pos;
  if (parse_word(p, "return")) {
    const e = parse_term(p);
    return parse_term_do_call("pure", [], [e], parse_span(p, beg));
  }
  const t = parse_term(p);
  parse_skip(p);
  const typed = t.$ === "Var" && parse_take(p, ":");
  const A     = typed ? parse_term(p, 1) : t;
  parse_skip(p);
  const asg = typed && parse_at(p, "=") && !parse_at(p, "==");
  if (asg) {
    parse_bump(p);
  } else if (typed) {
    parse_eat(p, "<-");
  } else if (!parse_take(p, "<-")) {
    return t;
  }
  const v = parse_term(p);
  parse_skip(p);
  parse_take(p, ";");
  const s  = parse_span(p, beg);
  const k  = typed && t.$ === "Var" ? t.k : "_";
  const n0 = p.sc.stk.length;
  const i  = parse_open(p, k);
  const f  = parse_term_do_stmt(p, m, ls, R);
  parse_close(p, n0);
  if (asg) {
    return Let([k], [i], [Ann(v, A, s)], f, s);
  }
  return parse_term_do_call("bind", [A], [v, Lam(k, i, f, s)], s);
}

// Body
// ----

export function parse_body(p: Parse, col: number = 0): Body {
  parse_skip(p);
  const beg = p.pos;
  if (parse_at_word(p, "match")) {
    return parse_match(p, col);
  }
  let q = parse_quant(p);
  let ts: LTerm[] = [];
  if (q.$ !== "Lone") {
    // a graded name before "=" opens a let; a graded type (a claim's
    // result) is a reply, so the sigil is given back
    const k = char_is_head(parse_peek(p)) ? parse_name(p) : "";
    parse_skip(p);
    if (k !== "" && parse_at(p, "=") && !parse_at(p, "==")) {
      ts = [Var(k, 0, parse_span(p, beg))];
      parse_eat(p, "=");
    } else {
      p.pos = beg;
      q = Lone();
    }
  }
  if (q.$ === "Lone") {
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

export function parse_terms(p: Parse): LTerm[] {
  const xs: LTerm[] = [];
  while (true) {
    xs.push(parse_term(p));
    parse_skip(p);
    if (parse_take(p, ":")) {
      return xs;
    }
    parse_take(p, ",");
  }
}

export function parse_match(p: Parse, col: number): Match {
  parse_skip(p);
  const beg = p.pos;
  parse_word(p, "match");
  const es = parse_terms(p);
  parse_skip(p);
  const ccol = parse_col(p.str, p.pos);
  const rows: Rows = [];
  while (ccol > col && parse_at_word(p, "case") && parse_col(p.str, p.pos) >= ccol) {
    const rcol = parse_col(p.str, p.pos);
    parse_word(p, "case");
    const qs = parse_terms(p);
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
    parse_skip(p);
    if (q.$ === "Lone" && !parse_at(p, ":")) {
      tele.push([None(), k, parse_open(p, k), Qnt()]);
    } else {
      parse_eat(p, ":");
      const T = parse_term(p);
      tele.push([q, k, parse_open(p, k), T]);
    }
    parse_skip(p);
    parse_take(p, ",");
  }
}

// Book
// ----

export function parse_fresh(p: Parse, k: Name): void {
  if (p.book.tlds[k] !== undefined) {
    parse_fail(p, "a fresh name (duplicate declaration: " + k + ")");
  }
}

export function parse_def(p: Parse, book: Book, u: Bool = false): void {
  parse_word(p, "def");
  const nm  = parse_name(p);
  const q   = parse_reso(p, nm);
  const tld = book.tlds[q];
  if (tld !== undefined && tld.$ === "Def" && tld.v === null && tld.b !== true) {
    if (u) {
      tld.u = true;
    }
    parse_def_fill(p, book, q, tld);
    return;
  }
  const k = parse_qual(p, nm);
  parse_fresh(p, k);
  const n0   = p.sc.stk.length;
  parse_eat(p, "(");
  const tele = parse_tele(p, ")");
  parse_eat(p, "->");
  const ret  = parse_term(p);
  const def: Def = { $: "Def", n: tele.length, T: term_higher(tele_bind(tele, ret)), v: null };
  if (u) {
    def.u = true;
  }
  book.tlds[k] = def;
  const vars = tele.map((cell): PVar => ({ $: "PVar", k: cell[1], i: cell[2] }));
  parse_def_body(p, book, k, def, vars, n0);
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
  def.n = vars.length;
  parse_def_body(p, book, k, def, vars, n0);
}

export function parse_def_body(p: Parse, book: Book, k: Name, def: Def, vars: PVar[], n0: number): void {
  parse_eat(p, ":");
  if (parse_at_word(p, "import")) {
    def.i = [];
    while (parse_word(p, "import")) {
      parse_eat(p, "\"");
      let eff = "";
      while (parse_peek(p) !== "\"" && parse_peek(p) !== "") {
        eff += parse_bump(p);
      }
      parse_eat(p, "\"");
      if (!/\.(c|js)$/.test(eff)) {
        parse_fail(p, "a .c or .js path");
      }
      def.i.push(p.dir + eff);
    }
    parse_close(p, n0);
    book.order.push(k);
    return;
  }
  const b = parse_body(p);
  parse_close(p, n0);
  def.v = term_higher(body_flatten(b, vars, () => p.sc.frs++));
  book.order.push(k);
}

export function parse_assert(p: Parse, book: Book): void {
  parse_word(p, "assert");
  const k = parse_qual(p, parse_name(p));
  parse_fresh(p, k);
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
      A = App(App(Ref("Exists"), A), Lam(c, i, w));
    }
    cls.push([all, q, c, parse_open(p, c), A]);
  }
  let T = parse_block(p);
  for (let j = cls.length - 1; j >= 0; j--) {
    const [all, q, c, i, A] = cls[j];
    T = all ? All(q, c, i, A, T) : App(App(Ref("Exists"), A), Lam(c, i, T));
  }
  parse_close(p, n0);
  let n = 0;
  while (n < cls.length && cls[n][0]) {
    n += 1;
  }
  book.tlds[k] = { $: "Def", n, T: term_higher(T), v: null };
  book.order.push(k);
}

export function parse_adt(p: Parse, book: Book): void {
  parse_word(p, "type");
  const k = parse_qual(p, parse_name(p));
  parse_fresh(p, k);
  const n0 = p.sc.stk.length;
  parse_skip(p);
  const params = parse_take(p, "<") ? parse_tele(p, ">") : [];
  if (!parse_word(p, "is")) {
    parse_fail(p, "'is'");
  }
  const K = parse_term(p);
  parse_eat(p, ":");
  const cs: Ctrs = [];
  const g  = params.findIndex((cell) => cell[3].$ !== "Qnt");
  book.tlds[k] = { $: "ADT", n: params.length, g: g < 0 ? params.length : g, T: term_higher(tele_bind(params, K)), c: cs };
  while (true) {
    parse_skip(p);
    if (p.pos >= p.str.length || !char_is_head(parse_peek(p))) {
      break;
    }
    if (["def", "type", "assert"].some((w) => parse_at_word(p, w))) {
      break;
    }
    const c = parse_qual(p, parse_name(p));
    if (book_ctr(book, c) !== null) {
      parse_fail(p, "a fresh constructor name (duplicate declaration: " + c + ")");
    }
    parse_eat(p, "{");
    const n1 = p.sc.stk.length;
    const fs = parse_tele(p, "}");
    const tip: LTerm = ADT(k, params.map((cell) => Var(cell[1], cell[2])));
    const ctr = { k: c, n: fs.length, T: term_higher(tele_bind(params.concat(fs), tip)) };
    parse_close(p, n1);
    cs.push(ctr);
    book.ctrs[c] = ctr;
  }
  parse_close(p, n0);
  book.order.push(k);
}

export function parse_book(book: Book, dir: string, src: string, ns: string = "", al: Record<Name, Name> = Object.create(null)): Book {
  const p = parse_new(book, dir, src, ns, al);
  while (true) {
    parse_skip(p);
    if (p.pos >= p.str.length) {
      return book;
    }
    p.sc = { stk: [], frs: 0 };
    if (parse_take(p, "@")) {
      if (!parse_word(p, "unsafe")) {
        parse_fail(p, "'unsafe' (the one decorator)");
      }
      parse_skip(p);
      if (!parse_at_word(p, "def")) {
        parse_fail(p, "'def' (@unsafe marks the def below it)");
      }
      parse_def(p, book, true);
      continue;
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
    return p0.$ !== "PCtr" || p0.k !== k;
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
      for (const w of ws) {
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
// a term entering a spine (an argument, a let value, a demanded match
// field) becomes a share Var: index -1, its value the raw term; the
// machine overwrites the value with its whnf, restores the term's Ann,
// and marks the var -2, so shared work runs once and a type survives
// the fill; a forcer outside the machine calls term_wnf on the var; a
// var steps into its value; tree nodes inside a leaf are plain values.
// a cell lives in the machine's frames and output, NEVER in an input
// node: the machine does not write into the term it was given, so the
// checker walks and counts unevaluated source syntax, and a cell it
// meets (in a goal computed by evaluation) opens by term_force alone.
// a rewrite demands its evidence and steps to its body on {==}, else
// sticks as a value.

export function term_wnf(book: Book, term: HTerm): HTerm {
  const frs: Frame[] = [];
  let tm: HTerm = term;
  let lhs: { t: () => HTerm; n: number } | null = null;
  main: while (true) {
    focus: switch (tm.$) {
      case "Var": {
        if (tm.v === undefined) {
          break focus;
        } else {
          if (tm.i === -1) {
            frs.push({ $: "VAR", l: tm, a: tm.v.$ === "Ann" ? tm.v : undefined });
          }
          lhs = null;
          tm = tm.v;
          continue main;
        }
      }
      case "Ann": {
        tm = tm.x;
        continue main;
      }
      case "Min": {
        frs.push({ $: "MNA", b: tm.b, s: tm.s });
        tm = tm.a;
        continue main;
      }
      case "Let": {
        const l = tm;
        tm = l.f(l.v.map((v, j) => term_cell(v, l.k[j])));
        continue main;
      }
      case "App": {
        frs.push({ $: "APP", x: term_cell(tm.x) });
        lhs = null;
        tm = tm.f;
        continue main;
      }
      case "Lam": {
        if (frs.length === 0 || frs[frs.length - 1].$ !== "APP") {
          break focus;
        } else {
          const fr = frs.pop() as Extract<Frame, { $: "APP" }>;
          if (lhs !== null && lhs.n === 0) {
            lhs = null;
          } else if (lhs !== null) {
            const pt: () => HTerm = lhs.t;
            const pn: number = lhs.n;
            lhs = { t: () => term_apply(pt(), fr.x), n: pn - 1 };
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
        if (lhs !== null && lhs.n > 0 && frs.length > 0 && frs[frs.length - 1].$ === "APP") {
          tm = lhs.t();
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
        const rf: HTerm = tm;
        lhs = { t: () => rf, n: tld.n };
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
          case "VAR": {
            fr.l.v = fr.a === undefined ? tm : Ann(tm, fr.a.T, fr.a.s);
            fr.l.i = -2;
            continue main;
          }
          case "APP": {
            tm = term_apply(tm, fr.x);
            continue back;
          }
          case "MNA": {
            if (tm.$ === "Qua" && tm.q.$ === "Many") {
              tm = fr.b;
              continue main;
            }
            if (tm.$ === "Qua" && tm.q.$ === "None") {
              continue back;
            }
            frs.push({ $: "MNB", a: tm, s: fr.s });
            tm = fr.b;
            continue main;
          }
          case "MNB": {
            if (tm.$ === "Qua" && tm.q.$ === "Many") {
              tm = fr.a;
            } else if (tm.$ !== "Qua" || (tm.q.$ === "Lone" && fr.a.$ !== "Qua")) {
              tm = Min(fr.a, tm, fr.s);
            }
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
                  case "Mat": {
                    if (t.k === ctr.k) {
                      const fl = fr.lhs;
                      if (fl === null) {
                        lhs = null;
                      } else {
                        lhs = { t: () => lhs_ext(fl.t(), ctr.k, ctr.x.length), n: fl.n - 1 + ctr.x.length };
                      }
                      for (let j = ctr.x.length - 1; j >= 0; j--) {
                        frs.push({ $: "APP", x: term_cell(ctr.x[j]) });
                      }
                      tm = t.h;
                      continue main;
                    } else {
                      t = t.m;
                      continue walk;
                    }
                  }
                  case "Efq": {
                    tm = term_apply(fr.lhs === null ? fr.t : fr.lhs.t(), fr.e);
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
              tm = term_apply(fr.lhs === null ? fr.t : fr.lhs.t(), fr.e);
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
  const tm = term_wnf(book, term) as Exclude<HTerm, { $: "Let" | "Ann" }>;
  switch (tm.$) {
    case "Var": {
      return Var(tm.k, tm.i, tm.s);
    }
    case "Ref": {
      return Ref(tm.k, tm.s, tm.b);
    }
    case "Sub": {
      return Sub(tm.i, term_snf(book, tm.v), term_snf(book, tm.f), tm.s);
    }
    case "Typ": {
      return Typ(term_snf(book, tm.g), tm.s);
    }
    case "Qnt":
    case "Qua": {
      return tm;
    }
    case "Min": {
      return Min(term_snf(book, tm.a), term_snf(book, tm.b), tm.s);
    }
    case "All": {
      return All(tm.q, tm.k, tm.i, term_snf(book, tm.A), (x: HTerm) => {
        return term_snf(book, tm.B(x));
      }, tm.s);
    }
    case "Lam": {
      return Lam(tm.k, tm.i, (x: HTerm) => {
        return term_snf(book, tm.f(x));
      }, tm.s);
    }
    case "App": {
      return App(tm.f.$ === "Ref" ? tm.f : term_snf(book, tm.f), term_snf(book, tm.x), tm.s);
    }
    case "ADT": {
      return ADT(tm.k, tm.x.map((x) => term_snf(book, x)), tm.s, tm.r);
    }
    case "Ctr": {
      return Ctr(tm.k, tm.x.map((x) => term_snf(book, x)), tm.s);
    }
    case "Mat": {
      return Mat(tm.k, term_snf(book, tm.h), term_snf(book, tm.m), tm.s);
    }
    case "Efq": {
      return Efq(tm.s);
    }
    case "Eql": {
      return Eql(term_snf(book, tm.a), term_snf(book, tm.b), term_snf(book, tm.T), tm.s);
    }
    case "Rfl": {
      return Rfl(tm.s);
    }
    case "Rwt": {
      return Rwt(term_snf(book, tm.e), term_snf(book, tm.p), term_snf(book, tm.f), tm.s);
    }
    case "Hol": {
      return Hol(tm.k, tm.s);
    }
  }
}

// Compare
// =======
// term_compare(mode, a, b): a fits b. the relation is a preorder, not an
// equality: mode LE is conversion (check-any's goal meet), directional
// only at kinds (the quantity order) and ADT residuals (removing more
// constructors fits removing fewer); a function type compares its
// domains SWAPPED (the slot's owner picks the argument, so the wanted
// domain must fit the given one) and its codomain along; every part
// that flows both ways -- an argument, a parameter, a field, an
// equation endpoint -- compares EQ, and EQ stays EQ all the way down,
// so no position is ever visited twice. mode EQ is the symmetric core:
// same walk, kinds exact, no swap (a swap under EQ is harmless, so
// the All case swaps unconditionally).

export function term_compare(mode: "EQ" | "LE", book: Book, lhs: HTerm, rhs: HTerm, dep: number = 0): boolean {
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
    return term_compare(mode, book, term_apply(a, x), term_apply(b, x), dep + 1);
  }
  switch (a.$) {
    case "Var": {
      return b.$ === "Var" && a.i === b.i;
    }
    case "Ref": {
      return b.$ === "Ref" && a.k === b.k;
    }
    case "Typ": {
      if (b.$ !== "Typ") {
        return false;
      }
      if (mode === "EQ") {
        return term_compare("EQ", book, a.g, b.g, dep);
      }
      const g = term_wnf(book, a.g);
      const h = term_wnf(book, b.g);
      if ((g.$ === "Qua" && g.q.$ === "Many") || (h.$ === "Qua" && h.q.$ !== "Many")) {
        return true;
      }
      if (g.$ === "Min") {
        const fa = term_compare("LE", book, Typ(g.a), b, dep);
        const fb = term_compare("LE", book, Typ(g.b), b, dep);
        return fa && fb;
      }
      if (h.$ === "Min") {
        const fa = term_compare("LE", book, a, Typ(h.a), dep);
        const fb = term_compare("LE", book, a, Typ(h.b), dep);
        return fa || fb;
      }
      return term_compare("LE", book, g, h, dep);
    }
    case "Qnt": {
      return b.$ === "Qnt";
    }
    case "Qua": {
      return b.$ === "Qua" && a.q.$ === b.q.$;
    }
    case "Min": {
      return b.$ === "Min"
          && term_compare("EQ", book, a.a, b.a, dep)
          && term_compare("EQ", book, a.b, b.b, dep);
    }
    case "All": {
      const x: HTerm = Var(a.k, dep);
      return b.$ === "All" && a.q.$ === b.q.$
          && term_compare(mode, book, b.A, a.A, dep)
          && term_compare(mode, book, a.B(x), b.B(x), dep + 1);
    }
    case "App": {
      return b.$ === "App"
          && term_compare("EQ", book, a.f, b.f, dep)
          && term_compare("EQ", book, a.x, b.x, dep);
    }
    case "ADT": {
      if (b.$ !== "ADT" || a.k !== b.k || a.x.length !== b.x.length) {
        return false;
      }
      if (mode === "EQ" && a.r.length !== b.r.length) {
        return false;
      }
      return b.r.every((c) => a.r.includes(c))
          && a.x.every((x, j) => term_compare("EQ", book, x, b.x[j], dep));
    }
    case "Ctr": {
      return b.$ === "Ctr" && a.k === b.k && a.x.length === b.x.length
          && a.x.every((x, j) => term_compare("EQ", book, x, b.x[j], dep));
    }
    case "Mat": {
      return b.$ === "Mat" && a.k === b.k
          && term_compare("EQ", book, a.h, b.h, dep)
          && term_compare("EQ", book, a.m, b.m, dep);
    }
    case "Efq": {
      return b.$ === "Efq";
    }
    case "Eql": {
      return b.$ === "Eql"
          && term_compare("EQ", book, a.a, b.a, dep)
          && term_compare("EQ", book, a.b, b.b, dep)
          && term_compare("EQ", book, a.T, b.T, dep);
    }
    case "Rfl": {
      return b.$ === "Rfl";
    }
    case "Hol": {
      return b.$ === "Hol" && a.k === b.k;
    }
    case "Rwt": {
      return b.$ === "Rwt"
          && term_compare("EQ", book, a.e, b.e, dep)
          && term_compare("EQ", book, a.p, b.p, dep)
          && term_compare("EQ", book, a.f, b.f, dep);
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
// premise it itself checks dead; only demanded premises add, once,
// unscaled (certify-once: a + position copies the value it receives).
// ordinary typing never consults the usage measure: resource accounting
// rides alongside the type judgment, it does not steer it. a checked term
// returns first-order: an LTerm built bottom-up, every node Ann-wrapped
// with its type in a share cell (Infer, Check), so no type is lowered
// and no closure survives; a consumer that needs HOAS calls
// term_higher, which passes a cell through; goals always compute on
// source terms. lhs is the def's
// own equation, rebuilt as the tree walks; lhs.qs holds the def's
// parameter quantities, read off its type once, so descent can skip
// erased columns. quantities: a binder q x: A checks A against Kind(q),
// so its type's quantity is at least q under term_compare's order.

export function term_infer(book: Book, lhs: LHS, tm: HTerm, qt: Quant, ctx: Ctx, d: number, sp: HTerm[] = []): Infer {
  switch (tm.$) {
    // Γ[x] = q A
    // ----------------- infer-var
    // Γ ⊢ x : A ~ {x:q}
    case "Var": {
      if (tm.i < 0 && tm.v !== undefined) {
        return term_infer(book, lhs, term_force(tm), qt, ctx, d, sp);
      }
      const ann = pmap_get(ctx, tm.i);
      if (ann === null) {
        throw Err(book, ctx, "a bound variable", tm, tm.s, lhs.def);
      } else {
        return Infer(Var(tm.k, tm.i, tm.s), ann.T, pmap_set(uses_nil(), tm.i, qt));
      }
    }
    // Book(k) : T
    // where a live k that is the lhs head descends: its pending
    //       arguments sp (the spine above it) compare EQ against the
    //       lhs columns left to right until one is LT; an erased (-)
    //       column is skipped; a bare or non-shrinking self-reference
    //       is an error, so a self-reference never escapes as a value
    //       k has a body in a live region, unless base declared it
    //       (an unfilled assert is a dead claim; base's are native)
    //       k is not a parameterized family: D<..> is the one
    //       spelling, a bare family head is an error
    // -------------------------------------------------------- infer-ref
    // Γ ⊢ k : T ~ {}
    case "Ref": {
      const tld = book.tlds[tm.k];
      if (tld === undefined) {
        throw Err(book, ctx, "a defined name", tm, tm.s, lhs.def);
      }
      switch (qt.$) {
        case "None": {
          break;
        }
        default: {
          if (tm.k === lhs.def && lhs.u !== true && lhs_descend(lhs, sp) !== "LT") {
            throw Err(book, ctx, "a decreasing self-call (some live argument must shrink)", tm, tm.s, lhs.def);
          }
          if (tm.k === lhs.def) {
            return Infer(Ref(tm.k, tm.s, tm.b), tld.T, uses_nil());
          }
          if (tld.$ === "Def" && tld.v === null && tld.b !== true && !tld.i) {
            throw Err(book, ctx, "a filled definition (an unfilled assert is a dead claim: live code cannot use it)", tm, tm.s, lhs.def);
          }
          break;
        }
      }
      if (tld.$ === "ADT" && tld.n > 0) {
        throw Err(book, ctx, "a family instance (write " + tm.k + "<..>)", tm, tm.s, lhs.def);
      }
      return Infer(Ref(tm.k, tm.s, tm.b), tld.T, uses_nil());
    }
    // Γ ⊢ q : Quant
    // where q is dead
    // ------------------- infer-typ
    // Γ ⊢ Kind(q) : Type
    case "Typ": {
      const g_chk = term_check(book, lhs, tm.g, None(), Qnt(tm.s), ctx, d);
      return Infer(Typ(g_chk.tm, tm.s), Typ(Qua(Lone()), tm.s), uses_nil());
    }
    // ∅
    // ------------------------------------ infer-qnt
    // Γ ⊢ Quant : Type    Γ ⊢ &1, &2 : Quant
    case "Qnt": {
      return Infer(Qnt(tm.s), Typ(Qua(Lone()), tm.s), uses_nil());
    }
    case "Qua": {
      return Infer(Qua(tm.q, tm.s), Qnt(tm.s), uses_nil());
    }
    // Γ ⊢ a : Quant ~ au    Γ ⊢ b : Quant ~ bu
    // ------------------------------------- infer-min
    // Γ ⊢ a <&> b : Quant ~ au + bu
    case "Min": {
      const a_chk = term_check(book, lhs, tm.a, qt, Qnt(tm.s), ctx, d);
      const b_chk = term_check(book, lhs, tm.b, qt, Qnt(tm.s), ctx, d);
      return Infer(Min(a_chk.tm, b_chk.tm, tm.s), Qnt(tm.s), uses_add(a_chk.us, b_chk.us));
    }
    // Γ ⊢ A : Kind(q)
    // Γ , x : qA ⊢ B(x) : Type
    // ----------------------------------------------- infer-all
    // Γ ⊢ @q x:A -> B : Type
    case "All": {
      const B_ctx = ctx_bind(ctx, d, tm.q, tm.k, tm.A);
      const A_chk = term_check(book, lhs, tm.A, None(), Typ(Qua(lhs_kind(lhs, tm.q)), tm.s), ctx, d);
      const B_chk = term_check(book, lhs, tm.B(Var(tm.k, d)), None(), Typ(Qua(Lone()), tm.s), B_ctx, d+1);
      return Infer(All(tm.q, tm.k, d, A_chk.tm, B_chk.tm, tm.s), Typ(Qua(Lone()), tm.s), uses_nil());
    }
    // Γ ⊢ f : @q x:A -> B ~ fu
    // Γ ⊢ a : A ~ au
    // where a is dead if q is -, and consumed once otherwise: its
    //       measure adds unscaled (certify-once), a + callee copies it
    //       f infers with a on its pending spine, for infer-ref's descent
    //       a family head is not a function: infer-ref rejects it,
    //       so D(x) is an error and D<x> the one spelling
    //       (x => f)(a) is one beta step: f(a) infers (a substituted
    //       lambda, a Sigma field type B(fst) say, makes one)
    // --------------------------------------------------------------- infer-app
    // Γ ⊢ f(a) : B(a) ~ fu + au
    case "App": {
      if (tm.f.$ === "Lam") {
        return term_infer(book, lhs, tm.f.f(tm.x), qt, ctx, d, sp);
      }
      const f_inf = term_infer(book, lhs, tm.f, qt, ctx, d, [tm.x, ...sp]);
      const f_wnf = term_wnf(book, f_inf.ty);
      if (f_wnf.$ !== "All") {
        throw Err(book, ctx, "a function type", f_inf.ty, tm.s, lhs.def);
      }
      const x_chk = term_check(book, lhs, tm.x, quant_dem(f_wnf.q, qt), f_wnf.A, ctx, d);
      return Infer(App(f_inf.tm, x_chk.tm, tm.s), f_wnf.B(tm.x), uses_add(f_inf.us, x_chk.us));
    }
    // book[k].T = @q1 p1:K1 -> .. -> Kind(G)
    // Γ ⊢ xi : Ki ~ ui
    // where xi is dead if qi is -
    // ------------------------------------------------- infer-adt
    // Γ ⊢ k<x1, .., xn> : Kind(G[x..]) ~ u1 + .. + un
    case "ADT": {
      const adt = book_adt(book, tm, ctx, lhs.def);
      if (tm.x.length !== adt.n) {
        throw Err(book, ctx, tm.k + " with " + String(adt.n) + (adt.n === 1 ? " parameter" : " parameters"), tm, tm.s, lhs.def);
      }
      const xs: LTerm[] = [];
      let tel: HTerm = adt.T;
      let us = uses_nil();
      for (const x of tm.x) {
        const t_all = tele_head(book, tel, ctx, lhs.def, tm.s);
        const t_dem = quant_dem(t_all.q, qt);
        const x_chk = term_check(book, lhs, x, t_dem, t_all.A, ctx, d);
        xs.push(x_chk.tm);
        us = uses_add(us, x_chk.us);
        tel = t_all.B(x);
      }
      return Infer(ADT(tm.k, xs, tm.s, tm.r), tel, us);
    }
    // Γ ⊢ A : Type    Γ ⊢ a : A    Γ ⊢ b : A
    // where A, a and b are dead; evidence is erased, so Data
    // ------------------------------------------------------ infer-eql
    // Γ ⊢ {a == b : A} : Data ~ {}
    case "Eql": {
      const T_chk = term_check(book, lhs, tm.T, None(), Typ(Qua(Lone()), tm.s), ctx, d);
      const a_chk = term_check(book, lhs, tm.a, None(), tm.T, ctx, d);
      const b_chk = term_check(book, lhs, tm.b, None(), tm.T, ctx, d);
      return Infer(Eql(a_chk.tm, b_chk.tm, T_chk.tm, tm.s), Typ(Qua(Many()), tm.s), uses_nil());
    }
    // Γ ⊢ T : Type
    // Γ ⊢ x : T ~ u
    // where T is dead
    // ------------------- infer-ann
    // Γ ⊢ {x : T} : T ~ u
    case "Ann": {
      term_check(book, lhs, tm.T, None(), Typ(Qua(Lone()), tm.s), ctx, d);
      const x_chk = term_check(book, lhs, tm.x, qt, tm.T, ctx, d);
      return { tm: x_chk.tm, ty: tm.T, us: x_chk.us };
    }
    // x is a Lam, Let, Ctr, Mat, Efq, Rfl, Rwt or Hol
    // ------------------------------------------- infer-err
    // Γ ⊢ x : ⊥ (a goal is needed)
    default: {
      if (tm.$ === "Ctr" && book_ctr(book, tm.k) === null) {
        throw Err(book, ctx, "a declared constructor", tm, tm.s, lhs.def);
      }
      throw Err(book, ctx, "an annotated term (cannot infer)", tm, tm.s, lhs.def);
    }
  }
}

export function term_check(book: Book, lhs: LHS, tm: HTerm, qt: Quant, ty: HTerm, ctx: Ctx, d: number): Check {
  switch (tm.$) {
    // a share cell in a goal-checked position: open it, no evaluation
    case "Var": {
      if (tm.i < 0 && tm.v !== undefined) {
        return term_check(book, lhs, term_force(tm), qt, ty, ctx, d);
      }
      break;
    }
    // T == @q x:A -> B
    // Γ , x : qA ⊢ f(x) : B(x) ~ u
    // where u[x] <= q
    //       lhs steps by x while a parameter remains
    // ---------------------------------------------- check-lam
    // Γ ⊢ x => f : T ~ u - x
    case "Lam": {
      const t_wnf = term_wnf(book, ty);
      if (t_wnf.$ !== "All") {
        throw Err(book, ctx, ty, typeless_show(book, ctx, tm), tm.s, lhs.def);
      }
      const x: HTerm = Var(tm.k, d);
      let f_lhs = lhs;
      if (lhs.n > 0) {
        f_lhs = { ...lhs, t: term_apply(lhs.t, x), n: lhs.n - 1 };
      }
      const f_ctx = ctx_bind(ctx, d, t_wnf.q, tm.k, t_wnf.A);
      const f_chk = term_check(book, f_lhs, tm.f(x), qt, t_wnf.B(x), f_ctx, d+1);
      quant_used(book, ctx, tm.k, t_wnf.q, uses_get(f_chk.us, d), tm.s, lhs.def);
      return Check(Lam(tm.k, d, f_chk.tm, tm.s), ty, uses_del(f_chk.us, d));
    }
    // Γ ⊢ vj : Aj ~ vuj  (each value in Γ: the binders are parallel)
    // Γ ⊢ Aj : Kind(qj)
    // Γ , x1 : q1A1 , .. , xn : qnAn ⊢ f(x1, .., xn) : T ~ fu
    // where vj is dead if qj is -
    //       fu[xj] <= qj
    // ------------------------------------------------------------ check-let
    // Γ ⊢ q1 x1 .. qn xn = v1 .. vn; f : T ~ vu1 + .. + vun + fu - x⃗
    case "Let": {
      const n = tm.k.length;
      const vx: LTerm[] = [];
      let us = uses_nil();
      let f_ctx = ctx;
      for (let j = 0; j < n; j++) {
        const v_dem = quant_dem(tm.q[j], qt);
        const v_inf = term_infer(book, lhs, tm.v[j], v_dem, ctx, d);
        term_check(book, lhs, v_inf.ty, None(), Typ(Qua(lhs_kind(lhs, tm.q[j])), tm.s), ctx, d);
        vx.push(v_inf.tm);
        us = uses_add(us, v_inf.us);
        f_ctx = ctx_bind(f_ctx, d + j, tm.q[j], tm.k[j], v_inf.ty);
      }
      const xs = tm.k.map((k, j): HTerm => Var(k, d + j, tm.s, tm.v[j]));
      const f_chk = term_check(book, lhs, tm.f(xs), qt, ty, f_ctx, d + n);
      let fu = f_chk.us;
      for (let j = 0; j < n; j++) {
        quant_used(book, ctx, tm.k[j], tm.q[j], uses_get(fu, d + j), tm.s, lhs.def);
        fu = uses_del(fu, d + j);
      }
      return Check(Let(tm.k, xs.map((_, j) => d + j), vx, f_chk.tm, tm.s, tm.q), ty, uses_add(us, fu));
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
        const fam = book_ctr(book, tm.k) === null ? null : book_fam(book, tm.k);
        throw Err(book, ctx, ty, fam === null ? typeless_show(book, ctx, tm) : Ref(fam, tm.s), tm.s, lhs.def);
      }
      const adt = book_adt(book, t_wnf, ctx, lhs.def);
      const ctr = ctrs_find(adt.c, tm.k);
      if (ctr === null) {
        if (book_ctr(book, tm.k) === null) {
          throw Err(book, ctx, "a declared constructor (" + t_wnf.k + " declares " + adt.c.map((c) => c.k).join(", ") + ")", tm, tm.s, lhs.def);
        }
        throw Err(book, ctx, ty, Ref(book_fam(book, tm.k), tm.s), tm.s, lhs.def);
      }
      if (tm.x.length !== ctr.n) {
        throw Err(book, ctx, tm.k + " with " + String(ctr.n) + (ctr.n === 1 ? " field" : " fields"), tm, tm.s, lhs.def);
      }
      let tel = tele_fill(book, ctr.T, t_wnf.x, ctx, lhs.def, tm.s);
      const xs: LTerm[] = [];
      let us = uses_nil();
      for (const x of tm.x) {
        const f_all = tele_head(book, tel, ctx, lhs.def, tm.s);
        const f_dem = quant_dem(f_all.q, qt);
        const x_chk = term_check(book, lhs, x, f_dem, f_all.A, ctx, d);
        xs.push(x_chk.tm);
        us  = uses_add(us, x_chk.us);
        tel = f_all.B(x);
      }
      return Check(Ctr(tm.k, xs, tm.s), ty, us);
    }
    // T == @q s:D<p..> -> P
    // D.c[k] = @r1 x1:F1 -> .. -> D<p..>
    // Γ ⊢ h : @s1 x1:F1 -> .. -> P(k{x1, .., xn}) ~ hu
    // Γ ⊢ m : @q s:(D - k)<p..> -> P ~ mu
    // where q is not - in a live region
    //       si = ri · q (a field's quantity times its scrutinee's)
    //       h's lhs steps by k{x1, .., xn} while a parameter remains
    // -------------------------------------------------------------- check-mat
    // Γ ⊢ \ {k: h; m} : T ~ hu | mu
    //
    // T == @q s:D<p..> -> P    D.c = [] or live x:E ∈ Γ with E.c = []
    // where q is not - in a live region; a LIVE binder at an emptied
    //       ADT makes the region unreachable (a flattened match's
    //       default chain past its last constructor) - an erased one
    //       proves nothing, dead code inhabits it - so residue is dead
    // ------------------------------------------------------------- check-efq
    // Γ ⊢ \ {} : T ~ {}
    case "Mat":
    case "Efq": {
      const t_wnf = term_wnf(book, ty);
      if (t_wnf.$ !== "All") {
        throw Err(book, ctx, ty, typeless_show(book, ctx, tm), tm.s, lhs.def);
      }
      if (qt.$ !== "None" && t_wnf.q.$ === "None") {
        throw Err(book, ctx, "a live scrutinee (a - scrutinee matches only in a dead region)", undefined, tm.s, lhs.def);
      }
      const a_wnf = term_wnf(book, t_wnf.A);
      if (a_wnf.$ !== "ADT") {
        throw Err(book, ctx, "a datatype", t_wnf.A, tm.s, lhs.def);
      }
      const rem = book_adt(book, a_wnf, ctx, lhs.def).c;
      switch (tm.$) {
        case "Efq": {
          if (rem.length !== 0 && !ctx_dead(book, ctx)) {
            throw Err(book, ctx, "cases for " + rem.map((c) => c.k).join(", "), tm, tm.s, lhs.def);
          }
          return Check(Efq(tm.s), ty, uses_nil());
        }
        case "Mat": {
          const b     = tm;
          const t_all = t_wnf;
          const ctr   = ctrs_find(rem, tm.k);
          if (ctr === null) {
            throw Err(book, ctx, "a constructor of " + a_wnf.k + " (missing, or already matched)", tm, tm.s, lhs.def);
          }
          const tel = tele_fill(book, ctr.T, a_wnf.x, ctx, lhs.def, tm.s);
          function term_check_mat_goal(cur: HTerm, n: number, xs: HTerm[]): HTerm {
            if (n === 0) {
              return t_all.B(Ctr(b.k, xs, b.s));
            } else {
              const c_all = tele_head(book, cur, ctx, lhs.def, b.s);
              const c_dem = quant_mul(c_all.q, t_all.q);
              return All(c_dem, c_all.k, c_all.i, c_all.A, (x: HTerm) => {
                return term_check_mat_goal(c_all.B(x), n - 1, xs.concat([x]));
              }, b.s);
            }
          }
          let h_lhs = lhs;
          if (lhs.n > 0) {
            h_lhs = { ...lhs, t: lhs_ext(lhs.t, tm.k, ctr.n), n: lhs.n - 1 + ctr.n };
          }
          const h_chk = term_check(book, h_lhs, tm.h, qt, term_check_mat_goal(tel, ctr.n, []), ctx, d);
          const m_gol = All(t_wnf.q, t_wnf.k, t_wnf.i, ADT(a_wnf.k, a_wnf.x, tm.s, a_wnf.r.concat([ctr.k])), t_wnf.B, tm.s);
          const m_chk = term_check(book, lhs, tm.m, qt, m_gol, ctx, d);
          return Check(Mat(tm.k, h_chk.tm, m_chk.tm, tm.s), ty, uses_join(h_chk.us, m_chk.us));
        }
      }
    }
    // T == {a == b : A}    a == b
    // ---------------------------- check-rfl
    // Γ ⊢ {==} : T ~ {}
    case "Rfl": {
      const t_wnf = term_wnf(book, ty);
      if (t_wnf.$ !== "Eql") {
        throw Err(book, ctx, ty, typeless_show(book, ctx, tm), tm.s, lhs.def);
      }
      if (!term_compare("EQ", book, t_wnf.a, t_wnf.b, d)) {
        throw Err(book, ctx, t_wnf.a, t_wnf.b, tm.s, lhs.def);
      }
      return Check(Rfl(tm.s), ty, uses_nil());
    }
    // T
    // ------------------- check-hol
    // Γ ⊢ ?TODO : T ~ {}
    case "Hol": {
      if (tm.k === "TODO") {
        return Check(Hol(tm.k, tm.s), ty, uses_nil());
      }
      throw Err(book, ctx, ty, tm, tm.s, lhs.def);
    }
    // Γ ⊢ E : {a == b : A} ~ eu
    // Γ ⊢ P : @x:A -> @e:{a == x : A} -> Type    P(b, E) <= T
    // Γ ⊢ f : P(a, {==}) ~ fu
    // where P is dead; this is the J axiom: elimination
    //       specializes both the equation and its second endpoint
    // ------------------------------------------------------------ check-rwt
    // Γ ⊢ %e@E : P; f : T ~ eu + fu
    case "Rwt": {
      const e_inf = term_infer(book, lhs, tm.e, qt, ctx, d);
      const e_wnf = term_wnf(book, e_inf.ty);
      if (e_wnf.$ !== "Eql") {
        throw Err(book, ctx, "an equation {a == b : T}", e_inf.ty, tm.s, lhs.def);
      }
      const p_typ = All<HBody>(Lone(), "_", 0, e_wnf.T, (x: HTerm) => All<HBody>(Lone(), "e", 0, Eql(e_wnf.a, x, e_wnf.T), () => Typ(Qua(Lone())), tm.s), tm.s);
      const p_chk = term_check(book, lhs, tm.p, None(), p_typ, ctx, d);
      const b_gol = term_apply(term_apply(tm.p, e_wnf.b), tm.e);
      if (!term_compare("LE", book, b_gol, ty, d)) {
        throw Err(book, ctx, ty, b_gol, tm.s, lhs.def);
      }
      const a_gol = term_apply(term_apply(tm.p, e_wnf.a), Rfl<HBody>(tm.s));
      const f_chk = term_check(book, lhs, tm.f, qt, a_gol, ctx, d);
      return Check(Rwt(e_inf.tm, p_chk.tm, f_chk.tm, tm.s), ty, uses_add(e_inf.us, f_chk.us));
    }
    // Γ ⊢ x : A ~ u    A <= T
    // ---------------------- check-any
    // Γ ⊢ x : T ~ u
    default: {
      break;
    }
  }
  const x_inf = term_infer(book, lhs, tm, qt, ctx, d);
  if (term_compare("LE", book, x_inf.ty, ty, d)) {
    return { tm: x_inf.tm, us: x_inf.us };
  }
  throw Err(book, ctx, ty, x_inf.ty, tm.s, lhs.def);
}

// Valid
// =====
// book_valid throws the first Err (its first done entries are taken
// as validated: a harness resumes past a seeded base); an order entry
// is an event: an
// asserted name declares (bodiless, type checked) at its assert and
// defines at its fill, so it is visible and stuck between the two and
// unfolds after; a plain def or ADT does both at once. each event checks
// against the book so far, so a forward reference fails as undefined,
// and a live reference to a bodiless def errs (infer-ref), so mutual
// recursion cannot bypass the wall. a def is declared, body null, until
// its check passes: an unchecked body never unfolds, a declared ref is
// stuck. a def checks its type against Type, then its tree against it,
// entering with { t: Ref k, n: Def.n, qs: the parameter quantities read
// off T }; an ADT checks its signature against Type and reads its
// declared kind Kind(G) off the tip, then checks every constructor
// telescope domain (parameters, then fields) in the real context
// against one goal: Kind(G) for a live field, Kind(q) for a binder of
// quantity q otherwise (term_compare's order does the fitting); the tip must
// be the family applied to its own parameters, in order. one telescope
// per declaration: there is no second face, no substitution and no
// speculative pass.

export function adt_valid(book: Book, k: Name, adt: ADT): void {
  term_check(book, { t: Ref(k), n: 0, def: k, qs: [] }, adt.T, None(), Typ(Qua(Lone())), ctx_nil(), 0);
  const { doms, ret: kind } = tele_unbind(book, adt.T);
  if (kind.$ !== "Typ" || doms.length !== adt.n) {
    throw Err(book, ctx_nil(), "a kind (type " + k + "<..> is Kind(g))", kind, undefined, k);
  }
  for (const ctr of adt.c) {
    let tel: HTerm = ctr.T;
    let ctx = ctx_nil();
    for (let d = 0; d < adt.n + ctr.n; d++) {
      const t_all = tele_head(book, tel, ctx, ctr.k);
      let goal: HTerm = Typ(Qua(t_all.q));
      if (d >= adt.n && t_all.q.$ === "Lone") {
        goal = kind;
      }
      term_check(book, { t: Ref(ctr.k), n: 0, def: ctr.k, qs: [] }, t_all.A, None(), goal, ctx, d);
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
  term_check(book, { t: Ref(k), n: 0, def: k, qs: [], u: def.u }, def.T, None(), Typ(Qua(Lone())), ctx_nil(), 0);
  if (def.i) {
    let tel = term_strip(def.T);
    for (let d = 0; tel.$ === "All"; d++) {
      tel = term_strip(tel.B(Var(tel.k, d)));
    }
    const [h] = term_unapply(tel);
    const io  = book.tlds["IO"];
    if (h.$ !== "Ref" || h.k !== "IO" || io === undefined || io.$ !== "Def" || io.b !== true) {
      throw Err(book, ctx_nil(), "a foreign definition answering base's IO", k);
    }
  }
  if (def.v !== null) {
    const qs = tele_unbind(book, def.T).doms.map((dom) => dom[0]).slice(0, def.n);
    while (qs.length < def.n) {
      qs.push(Lone());
    }
    def.e = term_check(book, { t: Ref(k), n: def.n, def: k, qs, u: def.u }, def.v, Lone(), def.T, ctx_nil(), 0).tm;
  }
}

export function book_valid(book: Book, done: number = 0): void {
  const seen = book_nil();
  const last = new Map<Name, number>();
  for (let i = 0; i < book.order.length; i++) {
    last.set(book.order[i], i);
  }
  for (let i = 0; i < book.order.length; i++) {
    const k   = book.order[i];
    const tld = book.tlds[k];
    const fin = last.get(k) === i;
    if (tld.$ === "ADT") {
      seen.tlds[k] = tld;
      for (const c of tld.c) {
        seen.ctrs[c.k] = c;
      }
      if (i >= done) {
        adt_valid(seen, k, tld);
      }
      continue;
    }
    const dec: Def = { $: "Def", n: tld.n, T: tld.T, v: null, b: tld.b, u: tld.u };
    if (i < done) {
      seen.tlds[k] = fin ? tld : dec;
      continue;
    }
    if (fin && tld.v === null && tld.b !== true && !tld.i) {
      book.hols += 1;
    }
    seen.tlds[k] = dec;
    def_valid(seen, k, fin ? tld : dec);
    seen.tlds[k] = fin ? tld : dec;
  }
}
