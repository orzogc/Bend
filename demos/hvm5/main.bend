# HVM5 in Bend
# ============
#
# A port of hvm5.c: an Interaction Calculus evaluator with the same
# syntax, semantics and interaction counting as the C reference.
#
#   Term ::= x | &{} | &L{a,b} | ! &L{a,b} = v; k | λx.f | λ- f | (f x)
#          | () | λ() f | #0{x} | #1{x} | λ{#0:f; #1:g} | #(a,b) | λ! f
#          | @ref | @ref(a,b,..)
#
# Terms are Bend constructors, so term memory is Bend's own: erasing a
# term is dropping it. The env is an Array of cells indexed by binder
# id: a lambda's cell holds its argument (Sub) once applied; a dup's
# cell holds the value until a side asks (Sha), then the twin's copy.
# The book is a Map from a definition's name to its body, a template
# whose binder ids count from 0: a reference copies the template with
# every id moved past the next free cell (term_shift), so one array
# write per binder is the whole instantiation.
#
# The evaluator is one loop over a Step: a mode (a term to evaluate, or
# a whnf to deliver) and a continuation chain that is hvm5.c's stack.
# Strong normalization runs in the same loop: an NfK frame normalizes
# the children of the whnf it receives, Rb1/Rb2 frames rebuild the
# node. Every helper takes the machine's registers and answers the
# next Step; the loop matches the mode and the top frame.
#
# hvm5.c dies on a stuck redex (a lambda-bound variable in head
# position); here a stuck term is its own whnf. Freed cells are not
# reused; a dead dup side keeps its copy. Both leave the printed normal
# form and the interaction count unchanged.
#
# The program to run is the src constant, since a Bend binary takes no
# arguments; the output is hvm5 -s's. A literal holds λ as one code
# point (955); the output writes it as its two UTF-8 bytes.

import Base

# Types
# =====

# Term: the syntax. Dup lives in templates and freshly copied bodies
# only (a step turns it into a cell); Nam only in normal forms, the
# display name of a lambda. A run of #0/#1 is one Pak node holding
# its bits outermost first, so a dup copies the run in one step that
# counts one interaction per bit, as hvm5.c's packed constructors.
type Term is Data:
  Var{i: U32}
  Cov{+l: String, i: U32, +s: Bool}
  Nam{n: U32}
  Era{}
  Sup{+l: String, a: Term, b: Term}
  Dup{+l: String, i: U32, v: Term, k: Term}
  Lam{i: U32, f: Term}
  Drp{f: Term}
  App{f: Term, x: Term}
  One{}
  Use{f: Term}
  Pak{+bs: List<&2, Bool>, t: Term}
  Tup{a: Term, b: Term}
  Get{f: Term}
  Mat{f: Term, g: Term}
  Ref{n: String}

# Cell: an env slot: a substitution, a dup value not yet copied, nothing.
type Cell is Data:
  Sub{t: Term}
  Sha{v: Term}
  Nul{}

# Def: a book entry: the binder ids its body uses, and the body.
type Def is Data:
  Def{n: U32, t: Term}

# Kont: the stack. Arg: a pending argument. Elk: an eliminator waiting
# for its scrutinee. Dpk: dup cell i (label l) waiting for its value,
# side s asking. NfK: the whnf arriving gets normalized deeper. Rb1,
# Rb2: a node rebuilt from its normalized children.
type Kont is Type:
  Arg{x: Term, k: Kont}
  Elk{e: Term, k: Kont}
  Dpk{+l: String, i: U32, +s: Bool, k: Kont}
  NfK{k: Kont}
  Rb1{f: Term -> Term, k: Kont}
  Rb2{f: Term -> Term -> Term, b: Term, k: Kont}
  End{}

# Mode: a term to evaluate, or a whnf to deliver to the top frame.
type Mode is Data:
  Go{t: Term}
  Kn{w: Term}

# Step: the machine: env, book, mode, stack, interactions, next free
# cell, last display name.
type Step is Type:
  Step{
    env: Array<Cell>, +book: Map<&2, Def>, m: Mode, k: Kont,
    +c: U32, +nx: U32, +nm: U32
  }

# Hc: the syntax form the first two characters of the source open.
type Hc is Data:
  HEra{}
  HSup{}
  HDup{}
  HTup{}
  HCt0{}
  HCt1{}
  HRef{}
  HOne{}
  HApp{}
  HMat{}
  HDrp{}
  HGet{}
  HUse{}
  HLam{}
  HOth{}

# Ws: the source head as whitespace: a blank, a comment, or neither.
type Ws is Data:
  Sp{}
  Cm{}
  No{}

# Bind: a scoped binder: its name, its occurrence term, its use count.
type Bind is Data:
  Bind{+nm: String, +t: Term, +u: U32}

# St: the parser state: the head class, the source (blanks skipped),
# the scope, the next binder id.
type St is Type:
  St{h: Hc, src: String, sc: List<&2, Bind>, +vc: U32}

# Ph: the parser phase: a term, or a form resumed after a lookahead.
type Ph is Data:
  Trm{}
  PCtr{br: Bool, b: Bool, x: Term}
  PArg{op: Bool, f: Term}
  PCls{cl: Bool, f: Term}
  PSep{m: Bool, f: Term}
  PDup{dead: Bool, l: String, a: String, b: String, v: Term}

# Constants
# =========

# the display-name alphabet, hvm5.c's
def alphabet() -> String:
  "_abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789$"

# "λ" as the two bytes the output writes
def lam() -> String:
  SCon{Chr{206}, SCon{Chr{187}, ""}}

# the program: hvm5 -s of this file prints the same
def src() -> String:
  "// Booleans are bit runs over (); @not flips one.\n" ++
  "@not = λ{#0: λ- #1{()}; #1: λ- #0{()}};\n" ++
  "// Church numeral 2: the function is shared by a dup.\n" ++
  "@two = λf. ! &F{f0, f1} = f; λx. (f0 (f1 x));\n" ++
  "// 2^2 flips of a bit, applied to both bits at once.\n" ++
  "@main = ! &A{f, g} = @two(@two(@not)); &S{(f #0{()}), (g #1{()})};\n"

# Pick
# ====

def pick(-A: Type, z: Bool, a: A, b: A) -> A:
  match z:
    case True{}:
      a
    case False{}:
      b

# Str
# ===

# the code at position n (0 past the end)
def str_at(s: String, n: Nat) -> U32:
  match s n:
    case SCon{Chr{c}, t} 0n:
      c
    case SCon{h, t} 1n+p:
      str_at(t, p)
    case SNil{} _:
      0

# a name character: [a-zA-Z0-9_$-]; "-" so a dead dup side reads as a name
def chr_name(+c: U32) -> Bool:
  (U32.is_le(97, c) && U32.is_le(c, 122)) || (U32.is_le(65, c) && U32.is_le(c, 90))
    || (U32.is_le(48, c) && U32.is_le(c, 57)) || U32.is_eq(c, 95)
    || U32.is_eq(c, 36) || U32.is_eq(c, 45)

def ws_new(sp: Bool, cm: Bool) -> Ws:
  match sp cm:
    case True{} _:
      Sp{}
    case _ True{}:
      Cm{}
    case _ _:
      No{}

# the source head as whitespace: a blank or "~", or "//"
def str_ws(s: String) -> Ws:
  match s:
    case SCon{Chr{c}, t}:
      +d = c
      ws_new(U32.is_le(d, 32) || U32.is_eq(d, 126),
        U32.is_eq(d, 47) && U32.is_eq(str_at(t, 0n), 47))
    case SNil{}:
      No{}

# the source head inside a comment: a newline ends it
def str_cm(s: String) -> Ws:
  match s:
    case SCon{Chr{c}, t}:
      +nl = U32.is_eq(c, 10)
      ws_new(nl, Bool.not(nl))
    case SNil{}:
      No{}

# blanks and comments dropped from the head; z classifies the head
def str_skip(s: String, z: Ws) -> String:
  match s z:
    case SCon{c, t} Sp{}:
      +r = t
      str_skip(r, str_ws(r))
    case SCon{c, t} Cm{}:
      +r = t
      str_skip(r, str_cm(r))
    case u _:
      u

# the word at the head and the rest; z: is the head a name character
def str_word(s: String, z: Bool, k: String -> String -> IO(Unit)) -> IO(Unit):
  match s z:
    case SCon{c, t} True{}:
      +r = t
      str_word(r, chr_name(str_at(r, 0n)), w => u => k(SCon{c, w}, u))
    case u _:
      k("", u)

# Hc
# ==

def hc_new.hash(tup: Bool, one: Bool) -> Hc:
  match tup one:
    case True{} _:
      HTup{}
    case _ True{}:
      HCt1{}
    case _ _:
      HCt0{}

def hc_new.lam(mat: Bool, drp: Bool, get: Bool, use: Bool) -> Hc:
  match mat drp get use:
    case True{} _ _ _:
      HMat{}
    case _ True{} _ _:
      HDrp{}
    case _ _ True{} _:
      HGet{}
    case _ _ _ True{}:
      HUse{}
    case _ _ _ _:
      HLam{}

def hc_new.go(
  amp: Bool, bang: Bool, hash: Bool, at: Bool, par: Bool, lam: Bool, +d: U32
) -> Hc:
  match amp bang hash at par lam:
    case True{} _ _ _ _ _:
      pick(Hc, U32.is_eq(d, 123), HEra{}, HSup{})
    case _ True{} _ _ _ _:
      HDup{}
    case _ _ True{} _ _ _:
      hc_new.hash(U32.is_eq(d, 40), U32.is_eq(d, 49))
    case _ _ _ True{} _ _:
      HRef{}
    case _ _ _ _ True{} _:
      pick(Hc, U32.is_eq(d, 41), HOne{}, HApp{})
    case _ _ _ _ _ True{}:
      hc_new.lam(
        U32.is_eq(d, 123), U32.is_eq(d, 45), U32.is_eq(d, 33), U32.is_eq(d, 40))
    case _ _ _ _ _ _:
      HOth{}

# the form opened by the two characters c, d
def hc_new(+c: U32, d: U32) -> Hc:
  hc_new.go(
    U32.is_eq(c, 38), U32.is_eq(c, 33), U32.is_eq(c, 35), U32.is_eq(c, 64),
    U32.is_eq(c, 40), U32.is_eq(c, 955), d)

# St
# ==

# a state over a source: blanks skipped, the head classified
def st_new(src: String, sc: List<&2, Bind>, vc: U32) -> St:
  +r = src
  +s = str_skip(r, str_ws(r))
  St{hc_new(str_at(s, 0n), str_at(s, 1n)), s, sc, vc}

# Parser
# ======
#
# Continuation-passing: a parser of an A takes k: A -> St -> IO(Unit)
# and the state, and the last continuation runs the program. An error
# prints and stops: nothing after it runs. A phase (Ph) resumes a form
# after a lookahead, since a decision that leads back to a term must
# be made inside st_parse itself.

# the next name
def st_name(k: String -> St -> IO(Unit), s: St) -> IO(Unit):
  St{h, src, sc, vc} = s
  +r = src
  str_word(r, chr_name(str_at(r, 0n)), w => u => k(w, st_new(u, sc, vc)))

def st_opt.go(hit: Bool, k: Bool -> St -> IO(Unit), s: St, t: String) -> IO(Unit):
  match hit:
    case True{}:
      St{h, src, sc, vc} = s
      k(True{}, st_new(t, sc, vc))
    case False{}:
      k(False{}, s)

# an optional character: consumed when present; k learns which
def st_opt(c: U32, k: Bool -> St -> IO(Unit), s: St) -> IO(Unit):
  St{h, src, sc, vc} = s
  match src:
    case SCon{Chr{d}, t}:
      +e = d
      +u = t
      st_opt.go(U32.is_eq(c, e), k, St{h, SCon{Chr{e}, u}, sc, vc}, u)
    case SNil{}:
      k(False{}, St{h, SNil{}, sc, vc})

def st_sym.go(hit: Bool, c: U32, k: St -> IO(Unit), s: St) -> IO(Unit):
  match hit:
    case True{}:
      k(s)
    case False{}:
      IO.print("parse error: expected '" ++ SCon{Chr{c}, "'"})

# a required character
def st_sym(+c: U32, k: St -> IO(Unit), s: St) -> IO(Unit):
  st_opt(c, hit => st_sym.go(hit, c, k), s)

# a binder pushed onto the scope, with its occurrence term
def st_bind(nm: String, t: Term, k: St -> IO(Unit), s: St) -> IO(Unit):
  St{h, src, sc, vc} = s
  k(St{h, src, Bind{nm, t, 0} <> sc, vc})

def st_pop.go(ok: Bool, nm: String, u: U32, k: St -> IO(Unit), s: St) -> IO(Unit):
  match ok:
    case True{}:
      k(s)
    case False{}:
      IO.print("non-linear variable: " ++ nm ++ " used " ++ U32.show(u) ++ " times")

# the innermost binder popped: used once, unless it is the dead side "-"
def st_pop(k: St -> IO(Unit), s: St) -> IO(Unit):
  St{h, src, sc, vc} = s
  match sc:
    case Con{Bind{nm, t, u}, r}:
      st_pop.go(U32.is_eq(u, 1) || String.eq(nm, "-"), nm, u, k, St{h, src, r, vc})
    case Nil{}:
      k(St{h, src, Nil{}, vc})

# the binder count, reset for the next definition
def st_count(k: U32 -> St -> IO(Unit), s: St) -> IO(Unit):
  St{h, src, sc, vc} = s
  k(vc, St{h, src, sc, 0})

# is the innermost binder named nm
def sc_head(+sc: List<&2, Bind>, +nm: String) -> Bool:
  match sc:
    case Con{Bind{n, t, u}, r}:
      String.eq(n, nm)
    case Nil{}:
      False{}

# the nearest binder named nm, its use counted; eq: is it the innermost
def sc_find(
  +sc: List<&2, Bind>, eq: Bool, +nm: String,
  k: List<&2, Bind> -> Maybe<&2, Term> -> IO(Unit)
) -> IO(Unit):
  match sc eq:
    case Con{Bind{n, t, u}, r} True{}:
      k(Bind{n, t, (u + 1 : U32)} <> r, Some{t})
    case Con{b, r} False{}:
      sc_find(r, sc_head(r, nm), nm, r2 => m => k(b <> r2, m))
    case Nil{} _:
      k(Nil{}, None{})

def st_look.go(
  m: Maybe<&2, Term>, nm: String, k: Term -> St -> IO(Unit), s: St
) -> IO(Unit):
  match m:
    case Some{t}:
      k(t, s)
    case None{}:
      IO.print("unbound variable: " ++ nm)

# a variable occurrence
def st_look(nm: String, k: Term -> St -> IO(Unit), s: St) -> IO(Unit):
  St{h, src, sc, vc} = s
  +n = nm
  +c = sc
  sc_find(c, sc_head(c, n), n, r => m => st_look.go(m, n, k, St{h, src, r, vc}))

# #b{x}: the run of x grows when it has room, else a new run starts
# (hvm5.c packs 24 bits per node)
def term_pak.go(room: Bool, b: Bool, bs: List<&2, Bool>, t: Term) -> Term:
  match room:
    case True{}:
      Pak{b <> bs, t}
    case False{}:
      Pak{[b], Pak{bs, t}}

def bits_len(bs: List<&2, Bool>) -> U32:
  match bs:
    case Nil{}:
      0
    case Con{b, r}:
      (1 + bits_len(r) : U32)

def term_pak(b: Bool, x: Term) -> Term:
  match x:
    case Pak{bs, t}:
      term_pak.go(U32.is_lt(bits_len(bs), 24), b, bs, t)
    case y:
      Pak{[b], y}

# a term
@unsafe
def st_parse(ph: Ph, k: Term -> St -> IO(Unit), s: St) -> IO(Unit):
  match ph:
    case Trm{}:
      St{h, src, sc, vc} = s
      match h src:
        case HEra{} SCon{c, SCon{d, t}}:
          st_sym(125, k(Era{}), st_new(t, sc, vc))
        case HSup{} SCon{c, t}:
          st_name(l =>
            st_sym(123, st_parse(Trm{}, a =>
            st_sym(44, st_parse(Trm{}, b =>
            st_sym(125, k(Sup{l, a, b})))))), st_new(t, sc, vc))
        case HDup{} SCon{c, t}:
          st_sym(38, st_name(l =>
            st_sym(123, st_name(a =>
            st_sym(44, st_name(b =>
              +a2 = a
              +b2 = b
              st_sym(125, st_sym(61, st_parse(Trm{}, v =>
              st_sym(59, st_parse(
                PDup{String.eq(a2, "-") && String.eq(b2, "-"), l, a2, b2, v},
                k)))))))))), st_new(t, sc, vc))
        case HTup{} SCon{c, SCon{d, t}}:
          st_parse(Trm{}, a =>
            st_sym(44, st_parse(Trm{}, b =>
            st_sym(41, k(Tup{a, b})))), st_new(t, sc, vc))
        case HCt0{} SCon{c, SCon{d, t}}:
          st_opt(123, br =>
            st_parse(Trm{}, x =>
            st_parse(PCtr{br, False{}, x}, k)), st_new(t, sc, vc))
        case HCt1{} SCon{c, SCon{d, t}}:
          st_opt(123, br =>
            st_parse(Trm{}, x =>
            st_parse(PCtr{br, True{}, x}, k)), st_new(t, sc, vc))
        case HRef{} SCon{c, t}:
          st_name(n =>
            st_opt(40, op =>
            st_parse(PArg{op, Ref{n}}, k)), st_new(t, sc, vc))
        case HOne{} SCon{c, SCon{d, t}}:
          k(One{}, st_new(t, sc, vc))
        case HApp{} SCon{c, t}:
          st_parse(Trm{}, f =>
            st_parse(Trm{}, x =>
            st_sym(41, k(App{f, x}))), st_new(t, sc, vc))
        case HMat{} SCon{c, SCon{d, t}}:
          st_sym(35, st_sym(48, st_sym(58, st_parse(Trm{}, f =>
            st_opt(59, _ =>
            st_sym(35, st_sym(49, st_sym(58, st_parse(Trm{}, g =>
            st_opt(59, _ =>
            st_sym(125, k(Mat{f, g}))))))))))), st_new(t, sc, vc))
        case HDrp{} SCon{c, SCon{d, t}}:
          st_parse(Trm{}, f => k(Drp{f}), st_new(t, sc, vc))
        case HGet{} SCon{c, SCon{d, t}}:
          st_parse(Trm{}, f => k(Get{f}), st_new(t, sc, vc))
        case HUse{} SCon{c, SCon{d, t}}:
          st_sym(41, st_parse(Trm{}, f => k(Use{f})), st_new(t, sc, vc))
        case HLam{} SCon{c, t}:
          st_name(x =>
            st_sym(46, st_bind(x, Var{vc}, st_parse(Trm{}, f =>
            st_pop(k(Lam{vc, f}))))), st_new(t, sc, (vc + 1 : U32)))
        case HOth{} u:
          st_name(n => st_look(n, k), St{h, u, sc, vc})
        case _ _:
          IO.print("parse error")
    case PCtr{br, b, x}:
      match br:
        case True{}:
          st_sym(125, k(term_pak(b, x)), s)
        case False{}:
          k(term_pak(b, x), s)
    case PArg{op, f}:
      match op:
        case True{}:
          st_opt(41, cl => st_parse(PCls{cl, f}, k), s)
        case False{}:
          k(f, s)
    case PCls{cl, f}:
      match cl:
        case True{}:
          k(f, s)
        case False{}:
          st_parse(Trm{}, a => st_opt(44, m => st_parse(PSep{m, App{f, a}}, k)), s)
    case PSep{m, f}:
      match m:
        case True{}:
          st_parse(Trm{}, a => st_opt(44, m2 => st_parse(PSep{m2, App{f, a}}, k)), s)
        case False{}:
          st_sym(41, k(f), s)
    case PDup{dead, l, a, b, v}:
      match dead:
        case True{}:
          st_parse(Trm{}, q => k(App{Drp{q}, v}), s)
        case False{}:
          St{h, src, sc, vc} = s
          +l2 = l
          st_bind(a, Cov{l2, vc, False{}}, st_bind(b, Cov{l2, vc, True{}},
            st_parse(Trm{}, q =>
            st_pop(st_pop(k(Dup{l2, vc, v, q}))))), St{h, src, sc, (vc + 1 : U32)})

# the definitions to the end of the source; k gets the book
@unsafe
def st_book(b: Map<&2, Def>, k: Map<&2, Def> -> St -> IO(Unit), s: St) -> IO(Unit):
  St{h, src, sc, vc} = s
  match src:
    case SNil{}:
      k(b, St{h, SNil{}, sc, vc})
    case u:
      st_sym(64, st_name(n =>
        st_sym(61, st_parse(Trm{}, t =>
        st_sym(59, st_count(v =>
        st_book(Map.set(&2, Def, b, n, Def{v, t}), k)))))), St{h, u, sc, vc})

# Evaluator
# =========
#
# Each helper takes the registers and answers the next Step. Env
# reads are Array.swap results opened by the helper; cells are never
# reused, so a fresh cell is always Nul and needs no write.

# a template copied into fresh cells: every binder id moves up by b
def term_shift(+b: U32, t: Term) -> Term:
  match t:
    case Var{i}:
      Var{(b + i : U32)}
    case Cov{l, i, s}:
      Cov{l, (b + i : U32), s}
    case Sup{l, x, y}:
      Sup{l, term_shift(b, x), term_shift(b, y)}
    case Dup{l, i, v, k}:
      Dup{l, (b + i : U32), term_shift(b, v), term_shift(b, k)}
    case Lam{i, f}:
      Lam{(b + i : U32), term_shift(b, f)}
    case Drp{f}:
      Drp{term_shift(b, f)}
    case App{f, x}:
      App{term_shift(b, f), term_shift(b, x)}
    case Use{f}:
      Use{term_shift(b, f)}
    case Pak{bs, x}:
      Pak{bs, term_shift(b, x)}
    case Tup{x, y}:
      Tup{term_shift(b, x), term_shift(b, y)}
    case Get{f}:
      Get{term_shift(b, f)}
    case Mat{f, g}:
      Mat{term_shift(b, f), term_shift(b, g)}
    case u:
      u

# a variable read its cell: a substitution continues, else it is free
def cell_var(
  +book: Map<&2, Def>, k: Kont, +c: U32, +nx: U32, +nm: U32, +i: U32,
  r: Array<Cell> & Cell
) -> Step:
  (env, cell) = r
  match cell:
    case Sub{t}:
      Step{env, book, Go{t}, k, c, nx, nm}
    case _:
      Step{env, book, Kn{Var{i}}, k, c, nx, nm}

# a dup variable read its cell: the twin's copy, or the value still
# to copy (evaluated under a Dpk frame), or nothing
def cell_cov(
  +book: Map<&2, Def>, +l: String, +s: Bool, k: Kont, +c: U32, +nx: U32,
  +nm: U32, +i: U32, r: Array<Cell> & Cell
) -> Step:
  (env, cell) = r
  match cell:
    case Sub{t}:
      Step{env, book, Go{t}, k, c, nx, nm}
    case Sha{v}:
      Step{env, book, Go{v}, Dpk{l, i, s, k}, c, nx, nm}
    case Nul{}:
      Step{env, book, Kn{Cov{l, i, s}}, k, c, nx, nm}

# a reference: the template moves into fresh cells (one interaction)
def def_ref(
  env: Array<Cell>, +book: Map<&2, Def>, k: Kont, +c: U32, +nx: U32, +nm: U32,
  r: Map<&2, Def> & Def
) -> Step:
  (b2, d) = r
  Def{n, t} = d
  Step{env, book, Go{term_shift(nx, t)}, k, (c + 1 : U32), (nx + n : U32), nm}

# a whnf applied to x
def term_app(
  env: Array<Cell>, +book: Map<&2, Def>, w: Term, x: Term, k: Kont, +c: U32,
  +nx: U32, +nm: U32
) -> Step:
  match w:
    case Lam{i, f}:
      Step{Array.set(Cell, env, i, Sub{x}), book, Go{f}, k, (c + 1 : U32), nx, nm}
    case Drp{f}:
      Step{env, book, Go{f}, k, (c + 1 : U32), nx, nm}
    case Era{}:
      Step{env, book, Kn{Era{}}, k, (c + 1 : U32), nx, nm}
    case Sup{l, a, b}:
      Step{Array.set(Cell, env, nx, Sha{x}), book,
        Kn{Sup{l, App{a, Cov{l, nx, False{}}}, App{b, Cov{l, nx, True{}}}}},
        k, (c + 1 : U32), (nx + 1 : U32), nm}
    case Use{f}:
      Step{env, book, Go{x}, Elk{Use{f}, k}, c, nx, nm}
    case Mat{f, g}:
      Step{env, book, Go{x}, Elk{Mat{f, g}, k}, c, nx, nm}
    case Get{f}:
      Step{env, book, Go{x}, Elk{Get{f}, k}, c, nx, nm}
    case u:
      Step{env, book, Kn{App{u, x}}, k, c, nx, nm}

# a run over t, or t itself when the run is empty
def bits_pak(bs: List<&2, Bool>, t: Term) -> Term:
  match bs:
    case Nil{}:
      t
    case r:
      Pak{r, t}

# an eliminator meets its scrutinee's whnf
def term_elim(
  env: Array<Cell>, +book: Map<&2, Def>, e: Term, w: Term, k: Kont, +c: U32,
  +nx: U32, +nm: U32
) -> Step:
  match e w:
    case Use{f} One{}:
      Step{env, book, Go{f}, k, (c + 1 : U32), nx, nm}
    case Get{f} Tup{a, b}:
      Step{env, book, Go{f}, Arg{a, Arg{b, k}}, (c + 1 : U32), nx, nm}
    case Mat{f, g} Pak{Con{b, bs}, t}:
      Step{env, book, Go{pick(Term, b, g, f)}, Arg{bits_pak(bs, t), k},
        (c + 1 : U32), nx, nm}
    case _ Era{}:
      Step{env, book, Kn{Era{}}, k, (c + 1 : U32), nx, nm}
    case Use{f} Sup{m, x, y}:
      Step{Array.set(Cell, env, nx, Sha{f}), book,
        Kn{Sup{m, App{Use{Cov{m, nx, False{}}}, x}, App{Use{Cov{m, nx, True{}}}, y}}},
        k, (c + 1 : U32), (nx + 1 : U32), nm}
    case Get{f} Sup{m, x, y}:
      Step{Array.set(Cell, env, nx, Sha{f}), book,
        Kn{Sup{m, App{Get{Cov{m, nx, False{}}}, x}, App{Get{Cov{m, nx, True{}}}, y}}},
        k, (c + 1 : U32), (nx + 1 : U32), nm}
    case Mat{f, g} Sup{m, x, y}:
      Step{Array.set(Cell, Array.set(Cell, env, nx, Sha{f}), (nx + 1 : U32), Sha{g}),
        book, Kn{Sup{m,
          App{Mat{Cov{m, nx, False{}}, Cov{m, (nx + 1 : U32), False{}}}, x},
          App{Mat{Cov{m, nx, True{}}, Cov{m, (nx + 1 : U32), True{}}}, y}}},
        k, (c + 1 : U32), (nx + 2 : U32), nm}
    case u v:
      Step{env, book, Kn{App{u, v}}, k, c, nx, nm}

# a dup settles: the asking side's copy continues, the twin's parks in
# the cell (one interaction)
def term_dup.fin(
  env: Array<Cell>, +book: Map<&2, Def>, i: U32, s: Bool, k: Kont, +c: U32,
  +nx: U32, +nm: U32, a: Term, b: Term
) -> Step:
  match s:
    case False{}:
      Step{Array.set(Cell, env, i, Sub{b}), book, Go{a}, k, (c + 1 : U32), nx, nm}
    case True{}:
      Step{Array.set(Cell, env, i, Sub{a}), book, Go{b}, k, (c + 1 : U32), nx, nm}

# a dup meets a sup: same label, the sides are the copies; else the
# sup's children share fresh cells
def term_dup.sup(
  env: Array<Cell>, +book: Map<&2, Def>, +l: String, +i: U32, +s: Bool, k: Kont,
  +c: U32, +nx: U32, +nm: U32, +m: String, a: Term, b: Term, same: Bool
) -> Step:
  match same:
    case True{}:
      term_dup.fin(env, book, i, s, k, c, nx, nm, a, b)
    case False{}:
      term_dup.fin(
        Array.set(Cell, Array.set(Cell, env, nx, Sha{a}), (nx + 1 : U32), Sha{b}),
        book, i, s, k, c, (nx + 2 : U32), nm,
        Sup{m, Cov{l, nx, False{}}, Cov{l, (nx + 1 : U32), False{}}},
        Sup{m, Cov{l, nx, True{}}, Cov{l, (nx + 1 : U32), True{}}})

# a dup cell meets its value's whnf: one layer copied, the children
# shared through fresh cells; a stuck value parks back
def term_dup(
  env: Array<Cell>, +book: Map<&2, Def>, w: Term, +l: String, +i: U32, +s: Bool,
  k: Kont, +c: U32, +nx: U32, +nm: U32
) -> Step:
  match w:
    case Era{}:
      term_dup.fin(env, book, i, s, k, c, nx, nm, Era{}, Era{})
    case One{}:
      term_dup.fin(env, book, i, s, k, c, nx, nm, One{}, One{})
    case Lam{j, f}:
      term_dup.fin(
        Array.set(Cell, Array.set(Cell, env, nx, Sha{f}), j,
          Sub{Sup{l, Var{(nx + 1 : U32)}, Var{(nx + 2 : U32)}}}),
        book, i, s, k, c, (nx + 3 : U32), nm,
        Lam{(nx + 1 : U32), Cov{l, nx, False{}}},
        Lam{(nx + 2 : U32), Cov{l, nx, True{}}})
    case Drp{f}:
      term_dup.fin(Array.set(Cell, env, nx, Sha{f}), book, i, s, k, c, (nx + 1 : U32), nm,
        Drp{Cov{l, nx, False{}}}, Drp{Cov{l, nx, True{}}})
    case Use{f}:
      term_dup.fin(Array.set(Cell, env, nx, Sha{f}), book, i, s, k, c, (nx + 1 : U32), nm,
        Use{Cov{l, nx, False{}}}, Use{Cov{l, nx, True{}}})
    case Get{f}:
      term_dup.fin(Array.set(Cell, env, nx, Sha{f}), book, i, s, k, c, (nx + 1 : U32), nm,
        Get{Cov{l, nx, False{}}}, Get{Cov{l, nx, True{}}})
    case Tup{a, b}:
      term_dup.fin(
        Array.set(Cell, Array.set(Cell, env, nx, Sha{a}), (nx + 1 : U32), Sha{b}),
        book, i, s, k, c, (nx + 2 : U32), nm,
        Tup{Cov{l, nx, False{}}, Cov{l, (nx + 1 : U32), False{}}},
        Tup{Cov{l, nx, True{}}, Cov{l, (nx + 1 : U32), True{}}})
    case Mat{f, g}:
      term_dup.fin(
        Array.set(Cell, Array.set(Cell, env, nx, Sha{f}), (nx + 1 : U32), Sha{g}),
        book, i, s, k, c, (nx + 2 : U32), nm,
        Mat{Cov{l, nx, False{}}, Cov{l, (nx + 1 : U32), False{}}},
        Mat{Cov{l, nx, True{}}, Cov{l, (nx + 1 : U32), True{}}})
    case Sup{m, a, b}:
      term_dup.sup(env, book, l, i, s, k, c, nx, nm, m, a, b, String.eq(l, m))
    case Pak{bs, One{}}:
      term_dup.fin(env, book, i, s, k, (c + bits_len(bs) : U32), nx, nm,
        Pak{bs, One{}}, Pak{bs, One{}})
    case Pak{bs, t}:
      term_dup.fin(Array.set(Cell, env, nx, Sha{t}), book, i, s, k,
        ((c + bits_len(bs) : U32) - 1 : U32), (nx + 1 : U32), nm,
        Pak{bs, Cov{l, nx, False{}}}, Pak{bs, Cov{l, nx, True{}}})
    case u:
      Step{Array.set(Cell, env, i, Sha{u}), book, Kn{Cov{l, i, s}}, k, c, nx, nm}

# a whnf to normalize: its children normalize left to right and the
# node is rebuilt; a live lambda gets the next display name
def term_nf(
  env: Array<Cell>, +book: Map<&2, Def>, w: Term, k: Kont, +c: U32, +nx: U32,
  +nm: U32
) -> Step:
  match w:
    case Sup{l, a, b}:
      Step{env, book, Go{a}, NfK{Rb2{x => y => Sup{l, x, y}, b, k}}, c, nx, nm}
    case Tup{a, b}:
      Step{env, book, Go{a}, NfK{Rb2{x => y => Tup{x, y}, b, k}}, c, nx, nm}
    case Mat{f, g}:
      Step{env, book, Go{f}, NfK{Rb2{x => y => Mat{x, y}, g, k}}, c, nx, nm}
    case Pak{bs, t}:
      Step{env, book, Go{t}, NfK{Rb1{x => Pak{bs, x}, k}}, c, nx, nm}
    case Use{f}:
      Step{env, book, Go{f}, NfK{Rb1{x => Use{x}, k}}, c, nx, nm}
    case Get{f}:
      Step{env, book, Go{f}, NfK{Rb1{x => Get{x}, k}}, c, nx, nm}
    case Drp{f}:
      Step{env, book, Go{f}, NfK{Rb1{x => Drp{x}, k}}, c, nx, nm}
    case Lam{i, f}:
      Step{Array.set(Cell, env, i, Sub{Nam{(nm + 1 : U32)}}), book, Go{f},
        NfK{Rb1{x => Lam{(nm + 1 : U32), x}, k}}, c, nx, (nm + 1 : U32)}
    case u:
      Step{env, book, Kn{u}, k, c, nx, nm}

# the loop: a term steps, a whnf goes to the top frame; End answers
# the normal form and the interaction count
@unsafe
def step_run(s: Step) -> Term & U32:
  Step{env, book, m, k, c, nx, nm} = s
  match m:
    case Go{t}:
      match t:
        case App{f, x}:
          step_run(Step{env, book, Go{f}, Arg{x, k}, c, nx, nm})
        case Var{i}:
          +j = i
          step_run(cell_var(book, k, c, nx, nm, j, Array.swap(Cell, env, j, Nul{})))
        case Cov{l, i, sd}:
          +j = i
          step_run(
            cell_cov(book, l, sd, k, c, nx, nm, j, Array.swap(Cell, env, j, Nul{})))
        case Dup{l, i, v, q}:
          step_run(Step{Array.set(Cell, env, i, Sha{v}), book, Go{q}, k, c, nx, nm})
        case Ref{n}:
          step_run(
            def_ref(env, book, k, c, nx, nm, Map.get(Def, Def{0, Era{}}, book, n)))
        case u:
          step_run(Step{env, book, Kn{u}, k, c, nx, nm})
    case Kn{w}:
      match k:
        case End{}:
          (w, c)
        case Arg{x, r}:
          step_run(term_app(env, book, w, x, r, c, nx, nm))
        case Elk{e, r}:
          step_run(term_elim(env, book, e, w, r, c, nx, nm))
        case Dpk{l, i, sd, r}:
          step_run(term_dup(env, book, w, l, i, sd, r, c, nx, nm))
        case NfK{r}:
          step_run(term_nf(env, book, w, r, c, nx, nm))
        case Rb1{f, r}:
          step_run(Step{env, book, Kn{f(w)}, r, c, nx, nm})
        case Rb2{f, b, r}:
          step_run(Step{env, book, Go{b}, NfK{Rb1{f(w), r}}, c, nx, nm})

# Show
# ====

# one display-name digit
def nam_digit(d: U32) -> String:
  SCon{Chr{str_at(alphabet(), U32.to_nat(d))}, ""}

# a display name: base-64 digits, most significant first (print_name);
# one: n is a single digit; d bounds the digits
def nam_show(d: Nat, one: Bool, +n: U32) -> String:
  match d one:
    case 0n _:
      ""
    case 1n+p True{}:
      nam_digit(n)
    case 1n+p False{}:
      +h = (n >> 6n : U32)
      nam_show(p, U32.is_lt(h, 64), h) ++ nam_digit(U32.and(n, 63))

def bits_open(bs: List<&2, Bool>) -> String:
  match bs:
    case Nil{}:
      ""
    case Con{False{}, r}:
      "#0{" ++ bits_open(r)
    case Con{True{}, r}:
      "#1{" ++ bits_open(r)

def bits_close(bs: List<&2, Bool>) -> String:
  match bs:
    case Nil{}:
      ""
    case Con{b, r}:
      "}" ++ bits_close(r)

def term_show(t: Term) -> String:
  match t:
    case Nam{n}:
      +m = n
      nam_show(4n, U32.is_lt(m, 64), m)
    case Lam{n, f}:
      +m = n
      lam() ++ nam_show(4n, U32.is_lt(m, 64), m) ++ "." ++ term_show(f)
    case Drp{f}:
      lam() ++ "- " ++ term_show(f)
    case Use{f}:
      lam() ++ "() " ++ term_show(f)
    case Get{f}:
      lam() ++ "! " ++ term_show(f)
    case Mat{f, g}:
      lam() ++ "{#0:" ++ term_show(f) ++ "; #1:" ++ term_show(g) ++ "}"
    case Era{}:
      "&{}"
    case One{}:
      "()"
    case Sup{l, a, b}:
      "&" ++ l ++ "{" ++ term_show(a) ++ "," ++ term_show(b) ++ "}"
    case Tup{a, b}:
      "#(" ++ term_show(a) ++ "," ++ term_show(b) ++ ")"
    case Pak{bs, x}:
      bits_open(bs) ++ term_show(x) ++ bits_close(bs)
    case App{f, x}:
      "(" ++ term_show(f) ++ " " ++ term_show(x) ++ ")"
    case Ref{n}:
      "@" ++ n
    case u:
      "<var>"

# Main
# ====

def out(r: Term & U32) -> IO(Unit):
  (w, c) = r
  IO.print(term_show(w) ++ "\n- Itrs: " ++ U32.show(c) ++ " interactions")

# @main normalized and printed; a book without it is an error
def book_run.go(+b: Map<&2, Def>, r: Map<&2, Def> & Bool) -> IO(Unit):
  (b2, ok) = r
  match ok:
    case True{}:
      out(step_run(
        Step{Array.new(Cell, 24n, Nul{}), b, Go{Ref{"main"}}, NfK{End{}}, 0, 0, 0}))
    case False{}:
      IO.print("undefined function @main")

def book_run(b: Map<&2, Def>, s: St) -> IO(Unit):
  +m = b
  book_run.go(m, Map.has(&2, Def, m, "main"))

def main() -> IO(Unit):
  st_book(Map.new(&2, Def), book_run, st_new(src(), Nil{}, 0))
