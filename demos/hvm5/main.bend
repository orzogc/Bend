# HVM5 in Bend
# ============
#
# A port of hvm5.c: an Interaction Calculus evaluator with the same
# syntax, semantics and interaction counting as the C reference.
#
#   Term ::=
#     | x                  variable
#     | &{}                eraser
#     | &L{a,b}            superposition
#     | ! &L{a,b} = v; k   duplication
#     | λx.f               lambda
#     | λ- f               drop lambda
#     | (f x)              application
#     | ()                 unit
#     | λ() f              unit eliminator
#     | #0{x}              left constructor
#     | #1{x}              right constructor
#     | λ{#0:f; #1:g}      constructor eliminator
#     | #(a,b)             pair
#     | λ! f               pair eliminator
#     | @ref               reference
#     | @ref(a,b,..)       reference applied to arguments
#
# Terms are Bend constructors, so term memory is Bend's own: erasing a
# term is dropping it. A run of #0/#1 is one word: 24 bits and their
# count, outermost bit lowest, as hvm5.c packs them; a run over () is
# the word alone (Won), so a bit chain costs no heap at all.
#
# The env is an Array of cells indexed by binder id. A lambda's cell
# holds its argument (Sub) once applied; a dup's cell holds the value
# until a side asks (Sha, or Haf when the other side is dead), then
# the twin's copy. A cell read by its variable goes to the free list:
# the cell stores the old head (Num), and the words fh and nx (the
# head, the next fresh id) ride the loop. The book is an Array of
# templates by definition index, the parser numbering names and
# binders as it meets them. A reference moves its template out of the
# book and copies it (inst_run): a binder's cell hands its occurrence
# to the copy, a fresh cell takes the binder, and the template is
# rebuilt beside the copy and written back. Leading lambdas fuse with
# pending arguments as hvm5.c's L_RF0 loop, and a body that is a
# constructor eliminator waits for its scrutinee (K_DISP), so only the
# selected branch gets copied.
#
# The evaluator is one loop over the env, the book, a mode, a stack
# and the registers. The mode is a term to evaluate (Go), a whnf to
# deliver to the top frame (Kn), a stuck term unwinding the stack (St:
# hvm5.c dies here) or a template being fused (Rf). The stack is
# hvm5.c's: a pending argument, an eliminator waiting for its
# scrutinee, a dup cell waiting for its value, a deferred @ref. Strong
# normalization runs in the same loop: an NfK frame normalizes the
# children of the whnf it receives, and a frame holding the node's
# shape rebuilds it. Every helper answers the next state; the loop
# matches the mode and the top frame.
#
# The parser is a continuation monad over the parser state, in
# do-notation: a primitive is a def over the continuation and the
# state. An error prints and stops: nothing after it runs. A form that
# looks ahead before it reads more terms resumes as a phase (Ph) of
# term, the one recursive parser.
#
# Names and labels are codes, as in hvm5.c: six bits per character of
# the display alphabet, first character highest. The program to run
# is the src constant, since a Bend binary takes no arguments; the
# output is hvm5 -s's. A literal holds λ as one code point (955); the
# output writes it as its two UTF-8 bytes.

import Base

# Types
# =====

# Term: the syntax. Dup/Dux (both sides live, one side live) appear in
# templates only: a copy turns them into a cell. Abs and Nam appear in
# normal forms only: a lambda shown with its display name.
type Term is Data:
  Var{i: U32}
  Co0{+l: U32, i: U32}
  Co1{+l: U32, i: U32}
  Era{}
  Sup{+l: U32, a: Term, b: Term}
  Dup{+a: U32, +b: U32, v: Term, k: Term}
  Dux{+a: U32, v: Term, k: Term}
  Lam{+i: U32, f: Term}
  Drp{f: Term}
  App{f: Term, x: Term}
  One{}
  Use{f: Term}
  Pak{+p: U32, t: Term}
  Won{+p: U32}
  Tup{a: Term, b: Term}
  Get{f: Term}
  Mat{f: Term, g: Term}
  Ref{+n: U32}
  Abs{+n: U32, f: Term}
  Nam{+n: U32}

# Cell: an env slot: a substitution, a dup value not yet copied (both
# sides live, or the twin dead), a free-list link, nothing.
type Cell is Data:
  Sub{t: Term}
  Sha{v: Term}
  Haf{v: Term}
  Num{+n: U32}
  Nul{}

# Sh1, Sh2: the shape of a node with one child, with two: what
# rebuilds it once the children are copied or normalized.
type Sh1 is Data:
  SPak{+p: U32}
  SUse{}
  SGet{}
  SDrp{}
  SAbs{+n: U32}

type Sh2 is Data:
  SSup{+l: U32}
  SApp{}
  STup{}
  SMat{}

# Kont: the stack. Arg: a pending argument. Usk, Mtk, Gtk: an
# eliminator waiting for its scrutinee. Dpk: dup cell i (label l)
# waiting for its value, side sd asking, fl: is the twin alive. Rfk:
# a deferred eliminator @ref. NfK: the whnf arriving gets normalized
# deeper. N2A, N2B, N1: a node rebuilt from its normalized children
# (the first done and the second pending, both done, the one done).
type Kont is Data:
  Arg{x: Term, k: Kont}
  Usk{f: Term, k: Kont}
  Mtk{f: Term, g: Term, k: Kont}
  Gtk{f: Term, k: Kont}
  Dpk{+l: U32, +i: U32, +sd: U32, +fl: U32, k: Kont}
  Rfk{+r: U32, k: Kont}
  NfK{k: Kont}
  N2A{sh: Sh2, b: Term, k: Kont}
  N2B{sh: Sh2, a: Term, k: Kont}
  N1{sh: Sh1, k: Kont}
  End{}

# Path: the consumed prefix of a template, root at the bottom (the
# definition index); path_put folds the rebuilt remainder back.
type Path is Data:
  Plm{+i: U32, p: Path}
  Pdr{p: Path}
  Pm0{g: Term, p: Path}
  Pm1{f: Term, p: Path}
  Prt{+r: U32}

# Mode: a term to evaluate, a whnf to deliver, a stuck term unwinding
# the stack, a template being fused with pending arguments.
type Mode is Data:
  Go{t: Term}
  Kn{w: Term}
  Sk{w: Term}
  Rf{t: Term, p: Path}

# S: the machine: the env, the book, the mode, the stack, the
# interaction count, the free-list head, the next fresh id.
type S is Type:
  S{env: Array<Cell>, book: Array<Term>, m: Mode, k: Kont, +c: U32, +fh: U32, +nx: U32}

# Out: the normal form and the interaction count.
type Out is Type:
  Out{env: Array<Cell>, book: Array<Term>, t: Term, +c: U32}

# IK: the frames of a template copy: a node whose children are still
# to copy or already copied (instance, rebuilt); a dup's value and
# body; a lambda's binder (the template's id and the fresh one).
type IK is Data:
  IEnd{}
  IKA{sh: Sh2, b: Term, k: IK}
  IKB{+sh: Sh2, a1: Term, a2: Term, k: IK}
  IK1{+sh: Sh1, k: IK}
  IDupV{+a: U32, +b: U32, q: Term, k: IK}
  IDupQ{+a: U32, +b: U32, v2: Term, k: IK}
  IDuxV{+a: U32, q: Term, k: IK}
  IDuxQ{+a: U32, v2: Term, k: IK}
  ILam{+i: U32, +n: U32, k: IK}

# IM: a template node to copy, or a copied pair (instance, rebuilt)
# for the top frame.
type IM is Data:
  IGo{t: Term}
  IKn{t1: Term, t2: Term}

# IS: the copier's state; Ins: its answer.
type IS is Type:
  IS{env: Array<Cell>, m: IM, k: IK, +fh: U32, +nx: U32}

type Ins is Type:
  Ins{env: Array<Cell>, t: Term, p: Term, +fh: U32, +nx: U32}

# Al: fresh cells taken: the env, their ids, the allocator words.
type Al is Type:
  Al{env: Array<Cell>, +n: U32, +fh: U32, +nx: U32}

type Al2 is Type:
  Al2{env: Array<Cell>, +n: U32, +p: U32, +fh: U32, +nx: U32}

type Al3 is Type:
  Al3{env: Array<Cell>, +n: U32, +p: U32, +r: U32, +fh: U32, +nx: U32}

# Hc: the syntax form the first two characters of the source open;
# HCtr{b} is #0 (b false) or #1.
type Hc is Data:
  HEra{}
  HSup{}
  HDup{}
  HTup{}
  HCtr{b: Bool}
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

# Occ: how a binder occurs: a variable, a dup side (label, cell).
type Occ is Data:
  OVar{+i: U32}
  OCo0{+l: U32, +i: U32}
  OCo1{+l: U32, +i: U32}

# Bind: a scoped binder: its name, its occurrence, its use count.
type Bind is Data:
  Bind{+nm: String, +oc: Occ, +u: U32}

# Names: the definition names met so far, each with its index; the
# next index.
type Names is Data:
  Names{m: Map<&2, U32>, +n: U32}

# Ent: a parsed definition: its index and its template.
type Ent is Data:
  Ent{ix: U32, t: Term}

# St: the parser state: the head form, the source (blanks skipped),
# the scope, the next binder id, the names.
type St is Data:
  St{+h: Hc, src: String, sc: List<&2, Bind>, +vc: U32, ns: Names}

# Dp: a dup's sides: both dead, one live (its cell), both live.
type Dp is Data:
  Dead{}
  Half{+j: U32}
  Both{+i: U32, +j: U32}

# Ph: the parser phase: a term; a term whose head form is known; a
# reference with or without arguments; a call after "(", closed or
# not; a call after an argument, with a comma or not; a dup's body.
type Ph is Data:
  Trm{}
  PAt{h: Hc}
  PArg{op: Bool, f: Term}
  PCls{cl: Bool, f: Term}
  PSep{m: Bool, f: Term}
  PDup{d: Dp, v: Term}

# Constants
# =========

# the display-name alphabet, hvm5.c's: a name code is base 64 over it
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

# Chr
# ===

def chr_code(ch: Char) -> U32:
  Chr{x} = ch
  x

# is code c the character ch
def chr_is(c: U32, ch: Char) -> Bool:
  U32.is_eq(c, chr_code(ch))

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

# the string past n characters
def str_drop(s: String, n: Nat) -> String:
  match s n:
    case SCon{h, t} 1n+p:
      str_drop(t, p)
    case u _:
      u

# the position of code c in s, or the length of s; z: is the head c
def str_find(s: String, z: Bool, +c: U32, +i: U32) -> U32:
  match s z:
    case _ True{}:
      i
    case SCon{h, t} False{}:
      +u = t
      str_find(u, U32.is_eq(str_at(u, 0n), c), c, (i + 1 : U32))
    case SNil{} False{}:
      i

# the digit of code c in the alphabet; 64 when it is not a digit
def alpha(+c: U32) -> U32:
  +a = alphabet()
  str_find(a, U32.is_eq(str_at(a, 0n), c), c, 0)

# a name character: a digit, or "-" so a dead dup side reads as a name
def chr_name(+c: U32) -> Bool:
  U32.is_lt(alpha(c), 64) || chr_is(c, '-')

# a name's code: six bits per character, first character highest
def name_code(s: String, +acc: U32) -> U32:
  match s:
    case SCon{Chr{c}, t}:
      name_code(t, ((acc << 6n : U32) + alpha(c) : U32))
    case SNil{}:
      acc

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
      ws_new(U32.is_le(d, chr_code(' ')) || chr_is(d, '~'),
        chr_is(d, '/') && chr_is(str_at(t, 0n), '/'))
    case SNil{}:
      No{}

# the source head inside a comment: a newline ends it
def str_cm(s: String) -> Ws:
  match s:
    case SCon{Chr{c}, t}:
      +nl = chr_is(c, '\n')
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

def str_word.go(c: Char, p: String & String) -> String & String:
  (w, u) = p
  (SCon{c, w}, u)

# the word at the head, and the rest; z: is the head a name character
def str_word(s: String, z: Bool) -> String & String:
  match s z:
    case SCon{c, t} True{}:
      +r = t
      str_word.go(c, str_word(r, chr_name(str_at(r, 0n))))
    case u _:
      ("", u)

# Hc
# ==

def hc_hash(+d: U32) -> Hc:
  pick(Hc, chr_is(d, '('), HTup{}, HCtr{chr_is(d, '1')})

def hc_lam(+d: U32) -> Hc:
  pick(Hc, chr_is(d, '{'), HMat{},
  pick(Hc, chr_is(d, '-'), HDrp{},
  pick(Hc, chr_is(d, '!'), HGet{},
  pick(Hc, chr_is(d, '('), HUse{}, HLam{}))))

# the form opened by the two characters c, d
def hc_new(+c: U32, +d: U32) -> Hc:
  pick(Hc, chr_is(c, '&'), pick(Hc, chr_is(d, '{'), HEra{}, HSup{}),
  pick(Hc, chr_is(c, '!'), HDup{},
  pick(Hc, chr_is(c, '#'), hc_hash(d),
  pick(Hc, chr_is(c, '@'), HRef{},
  pick(Hc, chr_is(c, '('), pick(Hc, chr_is(d, ')'), HOne{}, HApp{}),
  pick(Hc, chr_is(c, 'λ'), hc_lam(d), HOth{}))))))

# St
# ==

# a state over a source: blanks skipped, the head classified
def st_new(src: String, sc: List<&2, Bind>, vc: U32, ns: Names) -> St:
  +r = src
  +s = str_skip(r, str_ws(r))
  St{hc_new(str_at(s, 0n), str_at(s, 1n)), s, sc, vc, ns}

# Parser monad
# ============

# a parser of an A: it takes the continuation and the state; the last
# continuation runs the program
def P(-A: Type) -> Type:
  (A -> St -> IO(Unit)) -> St -> IO(Unit)

def P.pure(-A: Type, x: A) -> P(A):
  k => s => k(x, s)

def P.bind(-A: Type, -B: Type, m: P(A), f: A -> P(B)) -> P(B):
  k => s => m(a => f(a)(k), s)

# an error: it prints, and nothing after it runs
def fail(-A: Type, msg: String) -> P(A):
  k => s => IO.print(msg)

# the form at the head
def peek(k: Hc -> St -> IO(Unit), s: St) -> IO(Unit):
  St{h, src, sc, vc, ns} = s
  k(h, St{h, src, sc, vc, ns})

# n characters consumed
def drop(n: Nat, k: Unit -> St -> IO(Unit), s: St) -> IO(Unit):
  St{h, src, sc, vc, ns} = s
  k(Unit{}, st_new(str_drop(src, n), sc, vc, ns))

def name.go(
  sc: List<&2, Bind>,
  vc: U32,
  ns: Names,
  k: String -> St -> IO(Unit),
  p: String & String
) -> IO(Unit):
  (w, u) = p
  k(w, st_new(u, sc, vc, ns))

# the name at the head
def name(k: String -> St -> IO(Unit), s: St) -> IO(Unit):
  St{h, src, sc, vc, ns} = s
  +r = src
  name.go(sc, vc, ns, k, str_word(r, chr_name(str_at(r, 0n))))

# the name at the head, as a code
def label() -> P(U32):
  do P<U32>:
    w : String <- name
    return name_code(w, 0)

def opt.go(hit: Bool, k: Bool -> St -> IO(Unit), s: St, t: String) -> IO(Unit):
  match hit:
    case True{}:
      St{h, src, sc, vc, ns} = s
      k(True{}, st_new(t, sc, vc, ns))
    case False{}:
      k(False{}, s)

# an optional character: consumed when present; the answer says which
def opt(ch: Char, k: Bool -> St -> IO(Unit), s: St) -> IO(Unit):
  St{h, src, sc, vc, ns} = s
  +r = src
  opt.go(chr_is(str_at(r, 0n), ch), k, St{h, r, sc, vc, ns}, str_drop(r, 1n))

# an optional character, consumed when present
def skip(ch: Char) -> P(Unit):
  do P<Unit>:
    hit : Bool <- opt(ch)
    return Unit{}

def sym.go(hit: Bool, ch: Char) -> P(Unit):
  match hit:
    case True{}:
      P.pure(Unit, Unit{})
    case False{}:
      fail(Unit, "parse error: expected '" ++ SCon{ch, "'"})

# a required character
def sym(+ch: Char) -> P(Unit):
  do P<Unit>:
    hit : Bool <- opt(ch)
    sym.go(hit, ch)

# the closing brace of a form that opened one
def close(br: Bool) -> P(Unit):
  match br:
    case True{}:
      sym('}')
    case False{}:
      P.pure(Unit, Unit{})

# a variable binder pushed onto the scope: its id
def bindv(x: String, k: U32 -> St -> IO(Unit), s: St) -> IO(Unit):
  St{h, src, sc, vc, ns} = s
  k(vc, St{h, src, Bind{x, OVar{vc}, 0} <> sc, (vc + 1 : U32), ns})

def bindc.go(
  da: Bool,
  db: Bool,
  +l: U32,
  a: String,
  b: String,
  k: Dp -> St -> IO(Unit),
  s: St
) -> IO(Unit):
  match da db:
    case True{} True{}:
      k(Dead{}, s)
    case True{} False{}:
      St{h, src, sc, vc, ns} = s
      k(Half{vc}, St{h, src, Bind{b, OCo1{l, vc}, 0} <> sc, (vc + 1 : U32), ns})
    case False{} True{}:
      St{h, src, sc, vc, ns} = s
      k(Half{vc}, St{h, src, Bind{a, OCo0{l, vc}, 0} <> sc, (vc + 1 : U32), ns})
    case False{} False{}:
      St{h, src, sc, vc, ns} = s
      k(Both{vc, (vc + 1 : U32)}, St{h, src,
        Bind{b, OCo1{l, (vc + 1 : U32)}, 0} <> (Bind{a, OCo0{l, vc}, 0} <> sc),
        (vc + 2 : U32), ns})

# a dup's live sides pushed onto the scope ("-" is a dead side)
def bindc(l: U32, a: String, b: String, k: Dp -> St -> IO(Unit), s: St) -> IO(Unit):
  +a2 = a
  +b2 = b
  bindc.go(String.eq(a2, "-"), String.eq(b2, "-"), l, a2, b2, k, s)

def pop.go(ok: Bool, nm: String, u: U32) -> P(Unit):
  match ok:
    case True{}:
      P.pure(Unit, Unit{})
    case False{}:
      fail(Unit, "non-linear variable: " ++ nm ++ " used " ++ U32.show(u) ++ " times")

# the innermost binder popped: it was used once
def pop(k: Unit -> St -> IO(Unit), s: St) -> IO(Unit):
  St{h, src, sc, vc, ns} = s
  match sc:
    case Con{Bind{nm, oc, u}, r}:
      pop.go(U32.is_eq(u, 1), nm, u)(k, St{h, src, r, vc, ns})
    case Nil{}:
      k(Unit{}, St{h, src, Nil{}, vc, ns})

# is the innermost binder named nm
def sc_head(+sc: List<&2, Bind>, +nm: String) -> Bool:
  match sc:
    case Con{Bind{n, oc, u}, r}:
      String.eq(n, nm)
    case Nil{}:
      False{}

def sc_find.go(
  b: Bind,
  p: List<&2, Bind> & Maybe<&2, Occ>
) -> List<&2, Bind> & Maybe<&2, Occ>:
  (r, m) = p
  (b <> r, m)

# the nearest binder named nm, its use counted; eq: is it the innermost
def sc_find(sc: List<&2, Bind>, eq: Bool, +nm: String) -> List<&2, Bind> & Maybe<&2, Occ>:
  match sc eq:
    case Con{Bind{n, oc, u}, r} True{}:
      (Bind{n, oc, (u + 1 : U32)} <> r, Some{oc})
    case Con{b, r} False{}:
      +r2 = r
      sc_find.go(b, sc_find(r2, sc_head(r2, nm), nm))
    case Nil{} _:
      (Nil{}, None{})

# the occurrence term of a binder
def occ_term(oc: Occ) -> Term:
  match oc:
    case OVar{i}:
      Var{i}
    case OCo0{l, i}:
      Co0{l, i}
    case OCo1{l, i}:
      Co1{l, i}

def look.go(
  nm: String,
  k: Term -> St -> IO(Unit),
  h: Hc,
  src: String,
  vc: U32,
  ns: Names,
  p: List<&2, Bind> & Maybe<&2, Occ>
) -> IO(Unit):
  (r, m) = p
  match m:
    case Some{oc}:
      k(occ_term(oc), St{h, src, r, vc, ns})
    case None{}:
      IO.print("unbound variable: " ++ nm)

# a variable occurrence
def look(nm: String, k: Term -> St -> IO(Unit), s: St) -> IO(Unit):
  St{h, src, sc, vc, ns} = s
  +n = nm
  +c = sc
  look.go(n, k, h, src, vc, ns, sc_find(c, sc_head(c, n), n))

# is the source over
def eof(k: Bool -> St -> IO(Unit), s: St) -> IO(Unit):
  St{h, src, sc, vc, ns} = s
  match src:
    case SNil{}:
      k(True{}, St{h, SNil{}, sc, vc, ns})
    case SCon{c, t}:
      k(False{}, St{h, SCon{c, t}, sc, vc, ns})

def names_find.old(n: U32, p: Map<&2, U32> & U32) -> Names & U32:
  (m, ix) = p
  (Names{m, n}, ix)

def names_find.go(+nm: String, +n: U32, p: Map<&2, U32> & Bool) -> Names & U32:
  (m, has) = p
  match has:
    case True{}:
      names_find.old(n, Map.get(U32, 0, m, nm))
    case False{}:
      (Names{Map.set(&2, U32, m, nm, n), (n + 1 : U32)}, n)

# the index of a name: the next one when the name is new
def names_find(ns: Names, nm: String) -> Names & U32:
  Names{m, n} = ns
  +w = nm
  names_find.go(w, n, Map.has(&2, U32, m, w))

def index.go(
  k: U32 -> St -> IO(Unit),
  h: Hc,
  src: String,
  sc: List<&2, Bind>,
  vc: U32,
  p: Names & U32
) -> IO(Unit):
  (ns, ix) = p
  k(ix, St{h, src, sc, vc, ns})

# the definition index of a name
def index(w: String, k: U32 -> St -> IO(Unit), s: St) -> IO(Unit):
  St{h, src, sc, vc, ns} = s
  index.go(k, h, src, sc, vc, names_find(ns, w))

# the name at the head, as a definition index
def ref() -> P(U32):
  do P<U32>:
    w : String <- name
    index(w)

# Parser
# ======

# a run word: n bits, w their values (outermost lowest)
def run_word(+n: U32, +w: U32) -> U32:
  ((n << 24n) .|. w : U32)

# bit b pushed outermost onto the run word p
def run_push(+p: U32, +b: U32) -> U32:
  run_word(((p >> 24n) + 1 : U32), (((p .&. 16777215) << 1n) .|. b : U32))

# is the run word full (24 bits)
def run_full(+p: U32) -> Bool:
  U32.is_eq((p >> 24n : U32), 24)

def term_pak.pak(full: Bool, +b: U32, +p: U32, t: Term) -> Term:
  match full:
    case True{}:
      Pak{run_word(1, b), Pak{p, t}}
    case False{}:
      Pak{run_push(p, b), t}

def term_pak.won(full: Bool, +b: U32, +p: U32) -> Term:
  match full:
    case True{}:
      Pak{run_word(1, b), Won{p}}
    case False{}:
      Won{run_push(p, b)}

# #b{x}: the run of x grows when it has room, else a new run starts
def term_pak(b: Bool, x: Term) -> Term:
  match x:
    case Pak{p, t}:
      term_pak.pak(run_full(p), pick(U32, b, 1, 0), p, t)
    case Won{p}:
      term_pak.won(run_full(p), pick(U32, b, 1, 0), p)
    case One{}:
      Won{run_word(1, pick(U32, b, 1, 0))}
    case y:
      Pak{run_word(1, pick(U32, b, 1, 0)), y}

# a term
@unsafe
def term(ph: Ph) -> P(Term):
  match ph:
    case Trm{}:
      do P<Term>:
        h : Hc <- peek
        term(PAt{h})
    case PAt{HEra{}}:
      do P<Term>:
        Unit <- drop(2n)
        Unit <- sym('}')
        return Era{}
    case PAt{HSup{}}:
      do P<Term>:
        Unit <- drop(1n)
        l : U32 <- label()
        Unit <- sym('{')
        a : Term <- term(Trm{})
        Unit <- sym(',')
        b : Term <- term(Trm{})
        Unit <- sym('}')
        return Sup{l, a, b}
    case PAt{HDup{}}:
      do P<Term>:
        Unit <- drop(1n)
        Unit <- sym('&')
        l : U32 <- label()
        Unit <- sym('{')
        a : String <- name
        Unit <- sym(',')
        b : String <- name
        Unit <- sym('}')
        Unit <- sym('=')
        v : Term <- term(Trm{})
        Unit <- sym(';')
        d : Dp <- bindc(l, a, b)
        term(PDup{d, v})
    case PAt{HTup{}}:
      do P<Term>:
        Unit <- drop(2n)
        a : Term <- term(Trm{})
        Unit <- sym(',')
        b : Term <- term(Trm{})
        Unit <- sym(')')
        return Tup{a, b}
    case PAt{HCtr{b}}:
      do P<Term>:
        Unit <- drop(2n)
        br : Bool <- opt('{')
        x : Term <- term(Trm{})
        Unit <- close(br)
        return term_pak(b, x)
    case PAt{HRef{}}:
      do P<Term>:
        Unit <- drop(1n)
        ix : U32 <- ref()
        op : Bool <- opt('(')
        term(PArg{op, Ref{ix}})
    case PAt{HOne{}}:
      do P<Term>:
        Unit <- drop(2n)
        return One{}
    case PAt{HApp{}}:
      do P<Term>:
        Unit <- drop(1n)
        f : Term <- term(Trm{})
        x : Term <- term(Trm{})
        Unit <- sym(')')
        return App{f, x}
    case PAt{HMat{}}:
      do P<Term>:
        Unit <- drop(2n)
        Unit <- sym('#')
        Unit <- sym('0')
        Unit <- sym(':')
        f : Term <- term(Trm{})
        Unit <- skip(';')
        Unit <- sym('#')
        Unit <- sym('1')
        Unit <- sym(':')
        g : Term <- term(Trm{})
        Unit <- skip(';')
        Unit <- sym('}')
        return Mat{f, g}
    case PAt{HDrp{}}:
      do P<Term>:
        Unit <- drop(2n)
        f : Term <- term(Trm{})
        return Drp{f}
    case PAt{HGet{}}:
      do P<Term>:
        Unit <- drop(2n)
        f : Term <- term(Trm{})
        return Get{f}
    case PAt{HUse{}}:
      do P<Term>:
        Unit <- drop(2n)
        Unit <- sym(')')
        f : Term <- term(Trm{})
        return Use{f}
    case PAt{HLam{}}:
      do P<Term>:
        Unit <- drop(1n)
        x : String <- name
        Unit <- sym('.')
        i : U32 <- bindv(x)
        f : Term <- term(Trm{})
        Unit <- pop
        return Lam{i, f}
    case PAt{HOth{}}:
      do P<Term>:
        n : String <- name
        look(n)
    case PArg{False{}, f}:
      P.pure(Term, f)
    case PArg{True{}, f}:
      do P<Term>:
        cl : Bool <- opt(')')
        term(PCls{cl, f})
    case PCls{True{}, f}:
      P.pure(Term, f)
    case PCls{False{}, f}:
      term(PSep{True{}, f})
    case PSep{True{}, f}:
      do P<Term>:
        a : Term <- term(Trm{})
        m : Bool <- opt(',')
        term(PSep{m, App{f, a}})
    case PSep{False{}, f}:
      do P<Term>:
        Unit <- sym(')')
        return f
    case PDup{Dead{}, v}:
      do P<Term>:
        q : Term <- term(Trm{})
        return App{Drp{q}, v}
    case PDup{Half{j}, v}:
      do P<Term>:
        q : Term <- term(Trm{})
        Unit <- pop
        return Dux{j, v, q}
    case PDup{Both{i, j}, v}:
      do P<Term>:
        q : Term <- term(Trm{})
        Unit <- pop
        Unit <- pop
        return Dup{i, j, v, q}

# the definitions to the end of the source; done: is the source over
@unsafe
def book(done: Bool, es: List<&2, Ent>) -> P(List<&2, Ent>):
  match done:
    case True{}:
      P.pure(List<&2, Ent>, es)
    case False{}:
      do P<List<&2, Ent>>:
        Unit <- sym('@')
        ix : U32 <- ref()
        Unit <- sym('=')
        t : Term <- term(Trm{})
        Unit <- sym(';')
        e : Bool <- eof
        book(e, Ent{ix, t} <> es)

# the definitions of the source
def prog() -> P(List<&2, Ent>):
  do P<List<&2, Ent>>:
    e : Bool <- eof
    book(e, Nil{})

# Pak
# ===

def pak_pop.go(one: Bool, +p: U32, t: Term) -> Term:
  match one:
    case True{}:
      t
    case False{}:
      Pak{((((p >> 24n) - 1) << 24n) .|. ((p .&. 16777215) >> 1n) : U32), t}

def pak_pop(+p: U32, t: Term) -> Term:
  pak_pop.go(U32.is_eq((p >> 24n : U32), 1), p, t)

def won_pop.go(one: Bool, +p: U32) -> Term:
  match one:
    case True{}:
      One{}
    case False{}:
      Won{((((p >> 24n) - 1) << 24n) .|. ((p .&. 16777215) >> 1n) : U32)}

def won_pop(+p: U32) -> Term:
  won_pop.go(U32.is_eq((p >> 24n : U32), 1), p)

def bit0(+p: U32) -> Bool:
  U32.is_eq((p .&. 1 : U32), 0)

# The env
# =======

def num(s: Cell) -> U32:
  match s:
    case Num{n}:
      n
    case _:
      0

def cel(s: Cell) -> Term:
  match s:
    case Sub{t}:
      t
    case _:
      Era{}

def subst(env: Array<Cell>, i: U32, v: Cell) -> Array<Cell>:
  Array.set(Cell, env, i, v)

def spot.go(z: Bool, +fh: U32, +nx: U32) -> U32:
  match z:
    case True{}:
      nx
    case False{}:
      fh

def spot(+fh: U32, +nx: U32) -> U32:
  spot.go(U32.is_eq(fh, 0), fh, nx)

def bump.go(z: Bool, +nx: U32) -> U32:
  match z:
    case True{}:
      (nx + 1 : U32)
    case False{}:
      nx

def bump(+fh: U32, +nx: U32) -> U32:
  bump.go(U32.is_eq(fh, 0), nx)

def cov.go(z: Bool, +l: U32, +i: U32) -> Term:
  match z:
    case True{}:
      Co0{l, i}
    case False{}:
      Co1{l, i}

# the occurrence term of dup side sd (0 = Co0, 1 = Co1)
def cov(+sd: U32, +l: U32, +i: U32) -> Term:
  cov.go(U32.is_eq(sd, 0), l, i)

def park.go(z: Bool, w: Term) -> Cell:
  match z:
    case True{}:
      Haf{w}
    case False{}:
      Sha{w}

# a dup value parked back: Haf when the twin is dead (fl = 0)
def park(+fl: U32, w: Term) -> Cell:
  park.go(U32.is_eq(fl, 0), w)

# a fresh cell holding v: spot picks the free-list head or the bump
def alloc.go(+n: U32, +fh: U32, +nx: U32, p: Array<Cell> & Cell) -> Al:
  (env, s) = p
  Al{env, n, num(s), bump(fh, nx)}

def alloc(env: Array<Cell>, +fh: U32, +nx: U32, v: Cell) -> Al:
  +n = spot(fh, nx)
  alloc.go(n, fh, nx, Array.swap(Cell, env, n, v))

def alloc2.fin(+n: U32, al: Al) -> Al2:
  Al{env, p, fh, nx} = al
  Al2{env, n, p, fh, nx}

def alloc2.go(v2: Cell, al: Al) -> Al2:
  Al{env, n, fh, nx} = al
  alloc2.fin(n, alloc(env, fh, nx, v2))

def alloc2(env: Array<Cell>, +fh: U32, +nx: U32, v1: Cell, v2: Cell) -> Al2:
  alloc2.go(v2, alloc(env, fh, nx, v1))

def alloc3.fin(+n: U32, +p: U32, al: Al) -> Al3:
  Al{env, r, fh, nx} = al
  Al3{env, n, p, r, fh, nx}

def alloc3.go(v3: Cell, al: Al2) -> Al3:
  Al2{env, n, p, fh, nx} = al
  alloc3.fin(n, p, alloc(env, fh, nx, v3))

def alloc3(env: Array<Cell>, +fh: U32, +nx: U32, v1: Cell, v2: Cell, v3: Cell) -> Al3:
  alloc3.go(v3, alloc2(env, fh, nx, v1, v2))

# Book
# ====

def book_put(book: Array<Term>, r: U32, t: Term) -> Array<Term>:
  Array.set(Term, book, r, t)

def path_put(p: Path, book: Array<Term>, t: Term) -> Array<Term>:
  match p:
    case Plm{i, q}:
      path_put(q, book, Lam{i, t})
    case Pdr{q}:
      path_put(q, book, Drp{t})
    case Pm0{g, q}:
      path_put(q, book, Mat{t, g})
    case Pm1{f, q}:
      path_put(q, book, Mat{f, t})
    case Prt{r}:
      book_put(book, r, t)

# Nodes
# =====

def node1(sh: Sh1, x: Term) -> Term:
  match sh:
    case SPak{p}:
      Pak{p, x}
    case SUse{}:
      Use{x}
    case SGet{}:
      Get{x}
    case SDrp{}:
      Drp{x}
    case SAbs{n}:
      Abs{n, x}

def node2(sh: Sh2, a: Term, b: Term) -> Term:
  match sh:
    case SSup{l}:
      Sup{l, a, b}
    case SApp{}:
      App{a, b}
    case STup{}:
      Tup{a, b}
    case SMat{}:
      Mat{a, b}

# Instantiation
# =============
#
# inst_run copies a template, riding fh/nx, moving each binder's
# occurrence out of its cell and rebuilding the template beside the
# instance. A frame stack (IK) replaces the recursion.

def inst.var(k: IK, +fh: U32, +nx: U32, +i: U32, p: Array<Cell> & Cell) -> IS:
  (env, s) = p
  IS{env, IKn{cel(s), Var{i}}, k, fh, nx}

def inst.co0(k: IK, +fh: U32, +nx: U32, +l: U32, +i: U32, p: Array<Cell> & Cell) -> IS:
  (env, s) = p
  IS{env, IKn{Co0{l, num(s)}, Co0{l, i}}, k, fh, nx}

def inst.co1(k: IK, +fh: U32, +nx: U32, +l: U32, +i: U32, p: Array<Cell> & Cell) -> IS:
  (env, s) = p
  IS{env, IKn{Co1{l, num(s)}, Co1{l, i}}, k, fh, nx}

def inst.lam(k: IK, +i: U32, f: Term, al: Al) -> IS:
  Al{env, n, fh, nx} = al
  IS{subst(env, i, Sub{Var{n}}), IGo{f}, ILam{i, n, k}, fh, nx}

def inst.dup(k: IK, +a: U32, +b: U32, q: Term, v2: Term, al: Al) -> IS:
  Al{env, n, fh, nx} = al
  IS{subst(subst(env, a, Num{n}), b, Num{n}), IGo{q}, IDupQ{a, b, v2, k}, fh, nx}

def inst.dux(k: IK, +a: U32, q: Term, v2: Term, al: Al) -> IS:
  Al{env, n, fh, nx} = al
  IS{subst(env, a, Num{n}), IGo{q}, IDuxQ{a, v2, k}, fh, nx}

@unsafe
def inst_run(s: IS) -> Ins:
  IS{env, m, k, fh, nx} = s
  match m:
    case IGo{t}:
      match t:
        case Var{i}:
          +j = i
          inst_run(inst.var(k, fh, nx, j, Array.swap(Cell, env, j, Nul{})))
        case Co0{l, i}:
          +j = i
          inst_run(inst.co0(k, fh, nx, l, j, Array.swap(Cell, env, j, Nul{})))
        case Co1{l, i}:
          +j = i
          inst_run(inst.co1(k, fh, nx, l, j, Array.swap(Cell, env, j, Nul{})))
        case Sup{l, a, b}:
          inst_run(IS{env, IGo{a}, IKA{SSup{l}, b, k}, fh, nx})
        case Dup{a, b, v, q}:
          inst_run(IS{env, IGo{v}, IDupV{a, b, q, k}, fh, nx})
        case Dux{a, v, q}:
          inst_run(IS{env, IGo{v}, IDuxV{a, q, k}, fh, nx})
        case Lam{i, f}:
          inst_run(inst.lam(k, i, f, alloc(env, fh, nx, Nul{})))
        case Drp{f}:
          inst_run(IS{env, IGo{f}, IK1{SDrp{}, k}, fh, nx})
        case App{f, x}:
          inst_run(IS{env, IGo{f}, IKA{SApp{}, x, k}, fh, nx})
        case Use{f}:
          inst_run(IS{env, IGo{f}, IK1{SUse{}, k}, fh, nx})
        case Pak{p, t}:
          inst_run(IS{env, IGo{t}, IK1{SPak{p}, k}, fh, nx})
        case Won{p}:
          inst_run(IS{env, IKn{Won{p}, Won{p}}, k, fh, nx})
        case Tup{a, b}:
          inst_run(IS{env, IGo{a}, IKA{STup{}, b, k}, fh, nx})
        case Get{f}:
          inst_run(IS{env, IGo{f}, IK1{SGet{}, k}, fh, nx})
        case Mat{f, g}:
          inst_run(IS{env, IGo{f}, IKA{SMat{}, g, k}, fh, nx})
        case Era{}:
          inst_run(IS{env, IKn{Era{}, Era{}}, k, fh, nx})
        case One{}:
          inst_run(IS{env, IKn{One{}, One{}}, k, fh, nx})
        case Ref{n}:
          inst_run(IS{env, IKn{Ref{n}, Ref{n}}, k, fh, nx})
        case _:
          inst_run(IS{env, IKn{Era{}, Era{}}, k, fh, nx})
    case IKn{t1, t2}:
      match k:
        case IEnd{}:
          Ins{env, t1, t2, fh, nx}
        case IKA{sh, b, q}:
          inst_run(IS{env, IGo{b}, IKB{sh, t1, t2, q}, fh, nx})
        case IKB{sh, a1, a2, q}:
          inst_run(IS{env, IKn{node2(sh, a1, t1), node2(sh, a2, t2)}, q, fh, nx})
        case IK1{sh, q}:
          inst_run(IS{env, IKn{node1(sh, t1), node1(sh, t2)}, q, fh, nx})
        case IDupV{a, b, q, r}:
          inst_run(inst.dup(r, a, b, q, t2, alloc(env, fh, nx, Sha{t1})))
        case IDupQ{a, b, v2, q}:
          inst_run(IS{env, IKn{t1, Dup{a, b, v2, t2}}, q, fh, nx})
        case IDuxV{a, q, r}:
          inst_run(inst.dux(r, a, q, t2, alloc(env, fh, nx, Haf{t1})))
        case IDuxQ{a, v2, q}:
          inst_run(IS{env, IKn{t1, Dux{a, v2, t2}}, q, fh, nx})
        case ILam{i, n, q}:
          inst_run(IS{env, IKn{Lam{n, t1}, Lam{i, t2}}, q, fh, nx})

def inst(env: Array<Cell>, t: Term, +fh: U32, +nx: U32) -> Ins:
  inst_run(IS{env, IGo{t}, IEnd{}, fh, nx})

# The evaluator
# =============
#
# Every helper answers the next S; run matches the stack and the mode.

# wnf_end: the remainder copied, the book restored, back to the loop
def ref_end(book: Array<Term>, k: Kont, +c: U32, p: Path, ins: Ins) -> S:
  Ins{env, w, u, fh, nx} = ins
  S{env, path_put(p, book, u), Go{w}, k, c, fh, nx}

# a Var read its cell: the substitution continues (the cell is free),
# else the variable is stuck
def go_var(book: Array<Term>, k: Kont, +c: U32, +fh: U32, +nx: U32, +i: U32, p: Array<Cell> & Cell) -> S:
  (env, s) = p
  match s:
    case Sub{t}:
      S{env, book, Go{t}, k, c, i, nx}
    case u:
      S{subst(env, i, u), book, Sk{Var{i}}, k, c, fh, nx}

# a dup var read its cell (left empty): the twin's copy, or an
# unresolved value evaluated under a Dpk frame, or stuck
def go_cov(book: Array<Term>, k: Kont, +c: U32, +fh: U32, +nx: U32, +l: U32, +i: U32, +sd: U32, p: Array<Cell> & Cell) -> S:
  (env, s) = p
  match s:
    case Sub{t}:
      S{subst(env, i, Num{fh}), book, Go{t}, k, c, i, nx}
    case Sha{v}:
      S{env, book, Go{v}, Dpk{l, i, sd, 1, k}, c, fh, nx}
    case Haf{v}:
      S{env, book, Go{v}, Dpk{l, i, sd, 0, k}, c, fh, nx}
    case u:
      S{subst(env, i, u), book, Sk{cov(sd, l, i)}, k, c, fh, nx}

# a @ref: its template moves out of the book; a body-is-Mat with a
# pending Arg defers (K_DISP), else the fused-binder walk starts
def go_ref(env: Array<Cell>, +c: U32, +fh: U32, +nx: U32, +r: U32, k: Kont, p: Array<Term> & Term) -> S:
  match k:
    case Arg{x, q}:
      (book, s) = p
      match s:
        case Mat{f, g}:
          S{env, book_put(book, r, Mat{f, g}), Go{x}, Rfk{r, q}, (c + 1 : U32), fh, nx}
        case u:
          S{env, book, Rf{u, Prt{r}}, Arg{x, q}, (c + 1 : U32), fh, nx}
    case q:
      (book, s) = p
      S{env, book, Rf{s, Prt{r}}, q, (c + 1 : U32), fh, nx}

# Application
# -----------

def app_sup(book: Array<Term>, k: Kont, +c: U32, +l: U32, a: Term, b: Term, al: Al) -> S:
  Al{env, n, fh, nx} = al
  S{env, book, Kn{Sup{l, App{a, Co0{l, n}}, App{b, Co1{l, n}}}}, k, (c + 1 : U32), fh, nx}

def app(env: Array<Cell>, book: Array<Term>, k: Kont, +c: U32, +fh: U32, +nx: U32, w: Term, x: Term) -> S:
  match w:
    case Lam{i, f}:
      S{subst(env, i, Sub{x}), book, Go{f}, k, (c + 1 : U32), fh, nx}
    case Drp{f}:
      S{env, book, Go{f}, k, (c + 1 : U32), fh, nx}
    case Sup{l, a, b}:
      app_sup(book, k, c, l, a, b, alloc(env, fh, nx, Sha{x}))
    case Era{}:
      S{env, book, Kn{Era{}}, k, (c + 1 : U32), fh, nx}
    case Use{f}:
      S{env, book, Go{x}, Usk{f, k}, c, fh, nx}
    case Mat{f, g}:
      S{env, book, Go{x}, Mtk{f, g, k}, c, fh, nx}
    case Get{f}:
      S{env, book, Go{x}, Gtk{f, k}, c, fh, nx}
    case u:
      S{env, book, Sk{App{u, x}}, k, c, fh, nx}

def use_sup(book: Array<Term>, k: Kont, +c: U32, +m: U32, x: Term, y: Term, al: Al) -> S:
  Al{env, n, fh, nx} = al
  S{env, book, Kn{Sup{m, App{Use{Co0{m, n}}, x}, App{Use{Co1{m, n}}, y}}}, k, (c + 1 : U32), fh, nx}

def use(env: Array<Cell>, book: Array<Term>, k: Kont, +c: U32, +fh: U32, +nx: U32, w: Term, f: Term) -> S:
  match w:
    case One{}:
      S{env, book, Go{f}, k, (c + 1 : U32), fh, nx}
    case Era{}:
      S{env, book, Kn{Era{}}, k, (c + 1 : U32), fh, nx}
    case Sup{m, x, y}:
      use_sup(book, k, c, m, x, y, alloc(env, fh, nx, Sha{f}))
    case u:
      S{env, book, Sk{App{Use{f}, u}}, k, c, fh, nx}

def mat_bit(env: Array<Cell>, book: Array<Term>, k: Kont, +c: U32, +fh: U32, +nx: U32, f: Term, g: Term, y: Term, z: Bool) -> S:
  match z:
    case True{}:
      S{env, book, Go{f}, Arg{y, k}, (c + 1 : U32), fh, nx}
    case False{}:
      S{env, book, Go{g}, Arg{y, k}, (c + 1 : U32), fh, nx}

def mat_sup(book: Array<Term>, k: Kont, +c: U32, +m: U32, x: Term, y: Term, al: Al2) -> S:
  Al2{env, n, p, fh, nx} = al
  S{env, book, Kn{Sup{m, App{Mat{Co0{m, n}, Co0{m, p}}, x}, App{Mat{Co1{m, n}, Co1{m, p}}, y}}}, k, (c + 1 : U32), fh, nx}

def mat(env: Array<Cell>, book: Array<Term>, k: Kont, +c: U32, +fh: U32, +nx: U32, w: Term, f: Term, g: Term) -> S:
  match w:
    case Pak{b, t}:
      mat_bit(env, book, k, c, fh, nx, f, g, pak_pop(b, t), bit0(b))
    case Won{b}:
      mat_bit(env, book, k, c, fh, nx, f, g, won_pop(b), bit0(b))
    case Era{}:
      S{env, book, Kn{Era{}}, k, (c + 1 : U32), fh, nx}
    case Sup{m, x, y}:
      mat_sup(book, k, c, m, x, y, alloc2(env, fh, nx, Sha{f}, Sha{g}))
    case u:
      S{env, book, Sk{App{Mat{f, g}, u}}, k, c, fh, nx}

def get_sup(book: Array<Term>, k: Kont, +c: U32, +m: U32, x: Term, y: Term, al: Al) -> S:
  Al{env, n, fh, nx} = al
  S{env, book, Kn{Sup{m, App{Get{Co0{m, n}}, x}, App{Get{Co1{m, n}}, y}}}, k, (c + 1 : U32), fh, nx}

def get(env: Array<Cell>, book: Array<Term>, k: Kont, +c: U32, +fh: U32, +nx: U32, w: Term, f: Term) -> S:
  match w:
    case Tup{a, b}:
      S{env, book, Go{f}, Arg{a, Arg{b, k}}, (c + 1 : U32), fh, nx}
    case Era{}:
      S{env, book, Kn{Era{}}, k, (c + 1 : U32), fh, nx}
    case Sup{m, x, y}:
      get_sup(book, k, c, m, x, y, alloc(env, fh, nx, Sha{f}))
    case u:
      S{env, book, Sk{App{Get{f}, u}}, k, c, fh, nx}

# K_DISP: a deferred body-is-Mat @ref meets its scrutinee's whnf
def dsp_end(book: Array<Term>, k: Kont, +c: U32, +r: U32, w: Term, ins: Ins) -> S:
  Ins{env, v, u, fh, nx} = ins
  match v:
    case Mat{fi, gi}:
      mat(env, path_put(Prt{r}, book, u), k, c, fh, nx, w, fi, gi)
    case v2:
      S{env, path_put(Prt{r}, book, u), Sk{App{v2, w}}, k, c, fh, nx}

def dsp_bit(env: Array<Cell>, book: Array<Term>, k: Kont, +c: U32, +fh: U32, +nx: U32, +r: U32, f: Term, g: Term, y: Term, z: Bool) -> S:
  match z:
    case True{}:
      S{env, book, Rf{f, Pm0{g, Prt{r}}}, Arg{y, k}, (c + 1 : U32), fh, nx}
    case False{}:
      S{env, book, Rf{g, Pm1{f, Prt{r}}}, Arg{y, k}, (c + 1 : U32), fh, nx}

def dsp(env: Array<Cell>, k: Kont, +c: U32, +fh: U32, +nx: U32, +r: U32, w: Term, p: Array<Term> & Term) -> S:
  match w:
    case Pak{b, t}:
      (book, s) = p
      match s:
        case Mat{f, g}:
          dsp_bit(env, book, k, c, fh, nx, r, f, g, pak_pop(b, t), bit0(b))
        case u:
          S{env, book_put(book, r, u), Sk{App{Ref{r}, Pak{b, t}}}, k, c, fh, nx}
    case Won{b}:
      (book, s) = p
      match s:
        case Mat{f, g}:
          dsp_bit(env, book, k, c, fh, nx, r, f, g, won_pop(b), bit0(b))
        case u:
          S{env, book_put(book, r, u), Sk{App{Ref{r}, Won{b}}}, k, c, fh, nx}
    case u:
      (book, s) = p
      match s:
        case Mat{f, g}:
          dsp_end(book, k, c, r, u, inst(env, Mat{f, g}, fh, nx))
        case v:
          S{env, book_put(book, r, v), Sk{App{Ref{r}, u}}, k, c, fh, nx}

# Duplication
# -----------

# a fires; b parks in cell i or dies with it
def settle_go(env: Array<Cell>, book: Array<Term>, k: Kont, +c: U32, +fh: U32, +nx: U32, +i: U32, a: Term, b: Term, dead: Bool) -> S:
  match dead:
    case True{}:
      S{subst(env, i, Num{fh}), book, Go{a}, k, (c + 1 : U32), i, nx}
    case False{}:
      S{subst(env, i, Sub{b}), book, Go{a}, k, (c + 1 : U32), fh, nx}

def settle_if(env: Array<Cell>, book: Array<Term>, k: Kont, +c: U32, +fh: U32, +nx: U32, +i: U32, +fl: U32, a: Term, b: Term, left: Bool) -> S:
  match left:
    case True{}:
      settle_go(env, book, k, c, fh, nx, i, a, b, U32.is_eq(fl, 0))
    case False{}:
      settle_go(env, book, k, c, fh, nx, i, b, a, U32.is_eq(fl, 0))

def settle(env: Array<Cell>, book: Array<Term>, k: Kont, +c: U32, +fh: U32, +nx: U32, +i: U32, +sd: U32, +fl: U32, a: Term, b: Term) -> S:
  settle_if(env, book, k, c, fh, nx, i, fl, a, b, U32.is_eq(sd, 0))

def dup_sup(book: Array<Term>, k: Kont, +c: U32, +i: U32, +sd: U32, +fl: U32, +l: U32, +m: U32, al: Al2) -> S:
  Al2{env, n, p, fh, nx} = al
  settle(env, book, k, c, fh, nx, i, sd, fl, Sup{m, Co0{l, n}, Co0{l, p}}, Sup{m, Co1{l, n}, Co1{l, p}})

def dup_sup_if(env: Array<Cell>, book: Array<Term>, k: Kont, +c: U32, +fh: U32, +nx: U32, +i: U32, +sd: U32, +fl: U32, +l: U32, +m: U32, x: Term, y: Term, same: Bool) -> S:
  match same:
    case True{}:
      settle(env, book, k, c, fh, nx, i, sd, fl, x, y)
    case False{}:
      dup_sup(book, k, c, i, sd, fl, l, m, alloc2(env, fh, nx, Sha{x}, Sha{y}))

def dup_lam(book: Array<Term>, k: Kont, +c: U32, +i: U32, +sd: U32, +fl: U32, +l: U32, +j: U32, al: Al3) -> S:
  Al3{env, n, p, r, fh, nx} = al
  settle(subst(env, j, Sub{Sup{l, Var{p}, Var{r}}}), book, k, c, fh, nx, i, sd, fl, Lam{p, Co0{l, n}}, Lam{r, Co1{l, n}})

def dup_drp(book: Array<Term>, k: Kont, +c: U32, +i: U32, +sd: U32, +fl: U32, +l: U32, al: Al) -> S:
  Al{env, n, fh, nx} = al
  settle(env, book, k, c, fh, nx, i, sd, fl, Drp{Co0{l, n}}, Drp{Co1{l, n}})

def dup_use(book: Array<Term>, k: Kont, +c: U32, +i: U32, +sd: U32, +fl: U32, +l: U32, al: Al) -> S:
  Al{env, n, fh, nx} = al
  settle(env, book, k, c, fh, nx, i, sd, fl, Use{Co0{l, n}}, Use{Co1{l, n}})

def dup_get(book: Array<Term>, k: Kont, +c: U32, +i: U32, +sd: U32, +fl: U32, +l: U32, al: Al) -> S:
  Al{env, n, fh, nx} = al
  settle(env, book, k, c, fh, nx, i, sd, fl, Get{Co0{l, n}}, Get{Co1{l, n}})

def dup_tup(book: Array<Term>, k: Kont, +c: U32, +i: U32, +sd: U32, +fl: U32, +l: U32, al: Al2) -> S:
  Al2{env, n, p, fh, nx} = al
  settle(env, book, k, c, fh, nx, i, sd, fl, Tup{Co0{l, n}, Co0{l, p}}, Tup{Co1{l, n}, Co1{l, p}})

def dup_mat(book: Array<Term>, k: Kont, +c: U32, +i: U32, +sd: U32, +fl: U32, +l: U32, al: Al2) -> S:
  Al2{env, n, p, fh, nx} = al
  settle(env, book, k, c, fh, nx, i, sd, fl, Mat{Co0{l, n}, Co0{l, p}}, Mat{Co1{l, n}, Co1{l, p}})

def dup_pak(book: Array<Term>, k: Kont, +c: U32, +i: U32, +sd: U32, +fl: U32, +l: U32, +p: U32, al: Al) -> S:
  Al{env, n, fh, nx} = al
  settle(env, book, k, ((c + (p >> 24n)) - 1 : U32), fh, nx, i, sd, fl, Pak{p, Co0{l, n}}, Pak{p, Co1{l, n}})

def dup(env: Array<Cell>, book: Array<Term>, k: Kont, +c: U32, +fh: U32, +nx: U32, +l: U32, +i: U32, +sd: U32, +fl: U32, w: Term) -> S:
  match w:
    case Era{}:
      settle(env, book, k, c, fh, nx, i, sd, fl, Era{}, Era{})
    case One{}:
      settle(env, book, k, c, fh, nx, i, sd, fl, One{}, One{})
    case Sup{m, x, y}:
      dup_sup_if(env, book, k, c, fh, nx, i, sd, fl, l, m, x, y, U32.is_eq(l, m))
    case Lam{j, f}:
      dup_lam(book, k, c, i, sd, fl, l, j, alloc3(env, fh, nx, Sha{f}, Nul{}, Nul{}))
    case Drp{f}:
      dup_drp(book, k, c, i, sd, fl, l, alloc(env, fh, nx, Sha{f}))
    case Use{f}:
      dup_use(book, k, c, i, sd, fl, l, alloc(env, fh, nx, Sha{f}))
    case Get{f}:
      dup_get(book, k, c, i, sd, fl, l, alloc(env, fh, nx, Sha{f}))
    case Pak{p, t}:
      match t:
        case One{}:
          settle(env, book, k, (c + (p >> 24n) : U32), fh, nx, i, sd, fl, Pak{p, One{}}, Pak{p, One{}})
        case u:
          dup_pak(book, k, c, i, sd, fl, l, p, alloc(env, fh, nx, Sha{u}))
    case Won{p}:
      settle(env, book, k, (c + (p >> 24n) : U32), fh, nx, i, sd, fl, Won{p}, Won{p})
    case Tup{a, b}:
      dup_tup(book, k, c, i, sd, fl, l, alloc2(env, fh, nx, Sha{a}, Sha{b}))
    case Mat{f, g}:
      dup_mat(book, k, c, i, sd, fl, l, alloc2(env, fh, nx, Sha{f}, Sha{g}))
    case u:
      S{env, book, Sk{u}, Dpk{l, i, sd, fl, k}, c, fh, nx}

# Normalization
# -------------

def nf_lam(book: Array<Term>, k: Kont, +c: U32, +fh: U32, +nx: U32, +i: U32, f: Term, p: Array<Cell> & Cell) -> S:
  (env, q) = p
  +n = (num(q) + 1 : U32)
  S{subst(subst(env, 0, Num{n}), i, Sub{Nam{n}}), book, Go{f}, NfK{N1{SAbs{n}, k}}, c, fh, nx}

# the whnf under an NfK frame: children get normalized left to right
def nf(env: Array<Cell>, book: Array<Term>, k: Kont, +c: U32, +fh: U32, +nx: U32, w: Term) -> S:
  match w:
    case Sup{l, a, b}:
      S{env, book, Go{a}, NfK{N2A{SSup{l}, b, k}}, c, fh, nx}
    case Tup{a, b}:
      S{env, book, Go{a}, NfK{N2A{STup{}, b, k}}, c, fh, nx}
    case Mat{f, g}:
      S{env, book, Go{f}, NfK{N2A{SMat{}, g, k}}, c, fh, nx}
    case Pak{p, t}:
      S{env, book, Go{t}, NfK{N1{SPak{p}, k}}, c, fh, nx}
    case Use{f}:
      S{env, book, Go{f}, NfK{N1{SUse{}, k}}, c, fh, nx}
    case Get{f}:
      S{env, book, Go{f}, NfK{N1{SGet{}, k}}, c, fh, nx}
    case Drp{f}:
      S{env, book, Go{f}, NfK{N1{SDrp{}, k}}, c, fh, nx}
    case Lam{i, f}:
      nf_lam(book, k, c, fh, nx, i, f, Array.swap(Cell, env, 0, Nul{}))
    case u:
      S{env, book, Kn{u}, k, c, fh, nx}

# The loop
# --------

@unsafe
def run(s: S) -> Out:
  S{env, book, m, k, c, fh, nx} = s
  match m:
    case Go{t}:
      match t:
        case App{f, x}:
          run(S{env, book, Go{f}, Arg{x, k}, c, fh, nx})
        case Var{i}:
          +j = i
          run(go_var(book, k, c, fh, nx, j, Array.swap(Cell, env, j, Num{fh})))
        case Co0{l, i}:
          +j = i
          run(go_cov(book, k, c, fh, nx, l, j, 0, Array.swap(Cell, env, j, Nul{})))
        case Co1{l, i}:
          +j = i
          run(go_cov(book, k, c, fh, nx, l, j, 1, Array.swap(Cell, env, j, Nul{})))
        case Ref{r}:
          +r2 = r
          run(go_ref(env, c, fh, nx, r2, k, Array.swap(Term, book, r2, Era{})))
        case u:
          run(S{env, book, Kn{u}, k, c, fh, nx})
    case Rf{t, p}:
      match t:
        case Lam{i, f}:
          match k:
            case Arg{x, q}:
              run(S{subst(env, i, Sub{x}), book, Rf{f, Plm{i, p}}, q, (c + 1 : U32), fh, nx})
            case q:
              run(ref_end(book, q, c, p, inst(env, Lam{i, f}, fh, nx)))
        case Drp{f}:
          match k:
            case Arg{x, q}:
              run(S{env, book, Rf{f, Pdr{p}}, q, (c + 1 : U32), fh, nx})
            case q:
              run(ref_end(book, q, c, p, inst(env, Drp{f}, fh, nx)))
        case u:
          run(ref_end(book, k, c, p, inst(env, u, fh, nx)))
    case Sk{w}:
      match k:
        case Arg{x, q}:
          run(S{env, book, Sk{App{w, x}}, q, c, fh, nx})
        case Usk{f, q}:
          run(S{env, book, Sk{App{Use{f}, w}}, q, c, fh, nx})
        case Mtk{f, g, q}:
          run(S{env, book, Sk{App{Mat{f, g}, w}}, q, c, fh, nx})
        case Gtk{f, q}:
          run(S{env, book, Sk{App{Get{f}, w}}, q, c, fh, nx})
        case Dpk{l, i, sd, fl, q}:
          run(S{subst(env, i, park(fl, w)), book, Sk{cov(sd, l, i)}, q, c, fh, nx})
        case Rfk{r, q}:
          run(S{env, book, Sk{App{Ref{r}, w}}, q, c, fh, nx})
        case q:
          run(S{env, book, Kn{w}, q, c, fh, nx})
    case Kn{w}:
      match k:
        case Arg{x, q}:
          run(app(env, book, q, c, fh, nx, w, x))
        case Usk{f, q}:
          run(use(env, book, q, c, fh, nx, w, f))
        case Mtk{f, g, q}:
          run(mat(env, book, q, c, fh, nx, w, f, g))
        case Gtk{f, q}:
          run(get(env, book, q, c, fh, nx, w, f))
        case Dpk{l, i, sd, fl, q}:
          run(dup(env, book, q, c, fh, nx, l, i, sd, fl, w))
        case Rfk{r, q}:
          +r2 = r
          run(dsp(env, q, c, fh, nx, r2, w, Array.swap(Term, book, r2, Era{})))
        case NfK{q}:
          run(nf(env, book, q, c, fh, nx, w))
        case N2A{sh, b, q}:
          run(S{env, book, Go{b}, NfK{N2B{sh, w, q}}, c, fh, nx})
        case N2B{sh, a, q}:
          run(S{env, book, Kn{node2(sh, a, w)}, q, c, fh, nx})
        case N1{sh, q}:
          run(S{env, book, Kn{node1(sh, w)}, q, c, fh, nx})
        case _:
          Out{env, book, w, c}

# Show
# ====

# one display-name digit
def nam_digit(d: U32) -> String:
  SCon{Chr{str_at(alphabet(), U32.to_nat(d))}, ""}

# a name: base-64 digits, most significant first (print_name); one: n
# is a single digit; d bounds the digits
def nam_show(d: Nat, one: Bool, +n: U32) -> String:
  match d one:
    case 0n _:
      ""
    case 1n+p True{}:
      nam_digit(n)
    case 1n+p False{}:
      +h = (n >> 6n : U32)
      nam_show(p, U32.is_lt(h, 64), h) ++ nam_digit(U32.and(n, 63))

# a name from its code
def nam(+n: U32) -> String:
  nam_show(6n, U32.is_lt(n, 64), n)

# the constructors a run word opens, outermost first; n: bits left
def bits_open(n: Nat, +w: U32) -> String:
  match n:
    case 0n:
      ""
    case 1n+p:
      "#" ++ pick(String, bit0(w), "0", "1") ++ "{" ++ bits_open(p, (w >> 1n : U32))

def bits_close(n: Nat) -> String:
  match n:
    case 0n:
      ""
    case 1n+p:
      "}" ++ bits_close(p)

def run_len(+p: U32) -> Nat:
  U32.to_nat((p >> 24n : U32))

def term_show(t: Term) -> String:
  match t:
    case Nam{n}:
      nam(n)
    case Abs{n, f}:
      lam() ++ nam(n) ++ "." ++ term_show(f)
    case Lam{i, f}:
      lam() ++ nam(i) ++ "." ++ term_show(f)
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
      "&" ++ nam(l) ++ "{" ++ term_show(a) ++ "," ++ term_show(b) ++ "}"
    case Tup{a, b}:
      "#(" ++ term_show(a) ++ "," ++ term_show(b) ++ ")"
    case Pak{p, x}:
      bits_open(run_len(p), p) ++ term_show(x) ++ bits_close(run_len(p))
    case Won{p}:
      bits_open(run_len(p), p) ++ "()" ++ bits_close(run_len(p))
    case App{f, x}:
      "(" ++ term_show(f) ++ " " ++ term_show(x) ++ ")"
    case u:
      "<var>"

# Main
# ====

# the env: 2^20 cells (cell 0 holds the display-name counter)
def env_new() -> Array<Cell>:
  Array.new(Cell, 20n, Nul{})

def out(o: Out) -> IO(Unit):
  Out{env, book, w, c} = o
  IO.print(term_show(w) ++ "\n- Itrs: " ++ U32.show(c) ++ " interactions")

# the depth of an array with room for n entries; f: the bits left to try
def book_depth(f: Nat, +n: U32, +d: Nat) -> Nat:
  match f:
    case 0n:
      d
    case 1n+p:
      pick(Nat, U32.is_le(n, (1 << d : U32)), d, book_depth(p, n, 1n+d))

# the definitions written into the book
def book_load(es: List<&2, Ent>, a: Array<Term>) -> Array<Term>:
  match es:
    case Con{Ent{ix, t}, r}:
      book_load(r, book_put(a, ix, t))
    case Nil{}:
      a

def ents_has.go(eq: Bool, e: Ent, p: List<&2, Ent> & Bool) -> List<&2, Ent> & Bool:
  (r, b) = p
  (e <> r, eq || b)

# is definition ix among the parsed ones
def ents_has(es: List<&2, Ent>, +ix: U32) -> List<&2, Ent> & Bool:
  match es:
    case Con{Ent{i, t}, r}:
      +j = i
      ents_has.go(U32.is_eq(j, ix), Ent{j, t}, ents_has(r, ix))
    case Nil{}:
      (Nil{}, False{})

# @main normalized and printed; a book without it is an error
def book_run.fin(+ix: U32, +n: U32, +vc: U32, p: List<&2, Ent> & Bool) -> IO(Unit):
  (es, ok) = p
  match ok:
    case True{}:
      out(run(S{env_new(), book_load(es, Array.new(Term, book_depth(32n, n, 0n), Era{})),
        Go{Ref{ix}}, NfK{End{}}, 0, 0, vc}))
    case False{}:
      IO.print("undefined function @main")

def book_run.go(es: List<&2, Ent>, +vc: U32, p: Names & U32) -> IO(Unit):
  (ns, ix) = p
  Names{m, n} = ns
  +i = ix
  book_run.fin(i, n, vc, ents_has(es, i))

# the parsed definitions run: binder ids end at vc, fresh ids follow
def book_run(es: List<&2, Ent>, s: St) -> IO(Unit):
  St{h, src, sc, vc, ns} = s
  book_run.go(es, vc, names_find(ns, "main"))

def main() -> IO(Unit):
  prog()(book_run, st_new(src(), Nil{}, 1, Names{Map.new(&2, U32), 0}))
