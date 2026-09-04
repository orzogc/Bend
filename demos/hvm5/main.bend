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
# term is dropping it. The env is an Array of cells indexed by binder
# id: a lambda's cell holds its argument (Sub) once applied; a dup's
# cell holds the value until a side asks (Sha), then the twin's copy.
# A cell read by its variable, or by the second dup side, goes to the
# free list, and a dropped term is walked so its cells follow (hvm5.c's
# collect); a fresh id comes from the free list, else it is the next
# one. The book is an Array of bodies by definition index (the parser
# numbers names as it meets them), each a template whose binder ids
# count from 0: a reference takes as many fresh ids and copies the
# template over them (term_inst).
#
# The evaluator is one loop over a Step: the env, the registers (book,
# interaction count, free list, next id, last display name), a mode (a
# term to evaluate, a whnf to deliver, a dropped term to free) and a
# continuation chain that is hvm5.c's stack. Strong normalization runs in the same loop: an NfK
# frame normalizes the children of the whnf it receives, Rb1/Rb2 frames
# rebuild the node. Every helper takes the env, the registers and the
# stack and answers the next Step; the loop matches the mode and the
# top frame.
#
# The parser is a continuation monad over the parser state, in
# do-notation: a primitive is a def over the continuation and the
# state. An error prints and stops: nothing after it runs. A form that
# looks ahead before it reads more terms resumes as a phase (Ph) of
# term, the one recursive parser.
#
# Names and labels are codes, as in hvm5.c: six bits per character of
# the display alphabet, first character highest. hvm5.c dies on a stuck
# redex (a lambda-bound variable in head position); here a stuck term
# is its own whnf. A dead dup side keeps its copy. Both leave the
# printed normal form and the interaction count unchanged.
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
  Cov{+l: U32, i: U32, +s: Bool}
  Nam{n: U32}
  Era{}
  Sup{+l: U32, a: Term, b: Term}
  Dup{+l: U32, i: U32, v: Term, k: Term}
  Lam{i: U32, f: Term}
  Drp{f: Term}
  App{f: Term, x: Term}
  One{}
  Use{f: Term}
  Pak{+bs: List<&2, Bool>, t: Term}
  Tup{a: Term, b: Term}
  Get{f: Term}
  Mat{f: Term, g: Term}
  Ref{ix: U32}

# Cell: an env slot: a substitution, a dup value not yet copied, nothing.
type Cell is Data:
  Sub{t: Term}
  Sha{v: Term}
  Nul{}

# Def: a book entry: the binder ids its body uses, and the body.
type Def is Data:
  Def{n: Nat, t: Term}

# Ids: fresh ids by position: a Braun tree (position 0 at the node,
# odd positions left, even positions right).
type Ids is Data:
  INil{}
  INode{+i: U32, l: Ids, r: Ids}

# Regs: the registers: the book, the interaction count, the free list,
# the next id, the last display name.
type Regs is Type:
  Regs{book: Array<Def>, +c: U32, fl: List<&2, U32>, +nx: U32, +nm: U32}

# Tk: the registers after fresh ids were taken, and the ids.
type Tk is Type:
  Tk{r: Regs, +ids: Ids}

# Mode: a term to evaluate, a whnf to deliver to the top frame, or a
# dropped term to free.
type Mode is Data:
  Go{t: Term}
  Kn{w: Term}
  Fr{t: Term}

# Kont: the stack. Arg: a pending argument. Elk: an eliminator waiting
# for its scrutinee. Dpk: dup cell i (label l) waiting for its value,
# side s asking. NfK: the whnf arriving gets normalized deeper. Rb1,
# Rb2: a node rebuilt from its normalized children. Frk: a term still
# to free. Nxt: the mode to resume once the freeing is done.
type Kont is Type:
  Arg{x: Term, k: Kont}
  Elk{e: Term, k: Kont}
  Dpk{+l: U32, i: U32, +s: Bool, k: Kont}
  NfK{k: Kont}
  Rb1{f: Term -> Term, k: Kont}
  Rb2{f: Term -> Term -> Term, b: Term, k: Kont}
  Frk{t: Term, k: Kont}
  Nxt{m: Mode, k: Kont}
  End{}

# Step: the machine.
type Step is Type:
  Step{env: Array<Cell>, m: Mode, k: Kont, r: Regs}

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

# Bind: a scoped binder: its name, its occurrence term, its use count.
type Bind is Data:
  Bind{+nm: String, +t: Term, +u: U32}

# Names: the definition names met so far, each with its index; the
# next index.
type Names is Data:
  Names{m: Map<&2, U32>, +n: U32}

# Ent: a parsed definition: its index and its body.
type Ent is Data:
  Ent{ix: U32, d: Def}

# St: the parser state: the head form, the source (blanks skipped),
# the scope, the next binder id, the names.
type St is Data:
  St{+h: Hc, src: String, sc: List<&2, Bind>, +vc: U32, ns: Names}

# Dp: a dup's sides: both dead, or bound with the label and the id.
type Dp is Data:
  Dead{}
  Live{l: U32, i: U32}

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
  k(vc, St{h, src, Bind{x, Var{vc}, 0} <> sc, (vc + 1 : U32), ns})

def bindc.go(
  dead: Bool,
  l: U32,
  a: String,
  b: String,
  k: Dp -> St -> IO(Unit),
  s: St
) -> IO(Unit):
  match dead:
    case True{}:
      k(Dead{}, s)
    case False{}:
      St{h, src, sc, vc, ns} = s
      +m = l
      k(Live{m, vc}, St{h, src,
        Bind{b, Cov{m, vc, True{}}, 0} <> (Bind{a, Cov{m, vc, False{}}, 0} <> sc),
        (vc + 1 : U32), ns})

# a dup's sides pushed onto the scope, unless both are dead
def bindc(l: U32, a: String, b: String, k: Dp -> St -> IO(Unit), s: St) -> IO(Unit):
  +a2 = a
  +b2 = b
  bindc.go(String.eq(a2, "-") && String.eq(b2, "-"), l, a2, b2, k, s)

def pop.go(ok: Bool, nm: String, u: U32) -> P(Unit):
  match ok:
    case True{}:
      P.pure(Unit, Unit{})
    case False{}:
      fail(Unit, "non-linear variable: " ++ nm ++ " used " ++ U32.show(u) ++ " times")

# the innermost binder popped: used once, unless it is the dead side "-"
def pop(k: Unit -> St -> IO(Unit), s: St) -> IO(Unit):
  St{h, src, sc, vc, ns} = s
  match sc:
    case Con{Bind{nm, t, u}, r}:
      pop.go(U32.is_eq(u, 1) || String.eq(nm, "-"), nm, u)(k, St{h, src, r, vc, ns})
    case Nil{}:
      k(Unit{}, St{h, src, Nil{}, vc, ns})

# the binder count, reset for the next definition
def count(k: Nat -> St -> IO(Unit), s: St) -> IO(Unit):
  St{h, src, sc, vc, ns} = s
  k(U32.to_nat(vc), St{h, src, sc, 0, ns})

# is the innermost binder named nm
def sc_head(+sc: List<&2, Bind>, +nm: String) -> Bool:
  match sc:
    case Con{Bind{n, t, u}, r}:
      String.eq(n, nm)
    case Nil{}:
      False{}

def sc_find.go(
  b: Bind,
  p: List<&2, Bind> & Maybe<&2, Term>
) -> List<&2, Bind> & Maybe<&2, Term>:
  (r, m) = p
  (b <> r, m)

# the nearest binder named nm, its use counted; eq: is it the innermost
def sc_find(sc: List<&2, Bind>, eq: Bool, +nm: String) -> List<&2, Bind> & Maybe<&2, Term>:
  match sc eq:
    case Con{Bind{n, t, u}, r} True{}:
      (Bind{n, t, (u + 1 : U32)} <> r, Some{t})
    case Con{b, r} False{}:
      +r2 = r
      sc_find.go(b, sc_find(r2, sc_head(r2, nm), nm))
    case Nil{} _:
      (Nil{}, None{})

def look.go(
  nm: String,
  k: Term -> St -> IO(Unit),
  h: Hc,
  src: String,
  vc: U32,
  ns: Names,
  p: List<&2, Bind> & Maybe<&2, Term>
) -> IO(Unit):
  (r, m) = p
  match m:
    case Some{t}:
      k(t, St{h, src, r, vc, ns})
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
    case PDup{Live{l, i}, v}:
      do P<Term>:
        q : Term <- term(Trm{})
        Unit <- pop
        Unit <- pop
        return Dup{l, i, v, q}

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
        v : Nat <- count
        e : Bool <- eof
        book(e, Ent{ix, Def{v, t}} <> es)

# the definitions of the source
def prog() -> P(List<&2, Ent>):
  do P<List<&2, Ent>>:
    e : Bool <- eof
    book(e, Nil{})

# Evaluator
# =========
#
# Each helper takes the env, the registers and the stack and answers
# the next Step. Env reads are Array.swap results opened by the helper.

# i at position 0, every other position moved up by one
def ids_cons(t: Ids, i: U32) -> Ids:
  match t:
    case INil{}:
      INode{i, INil{}, INil{}}
    case INode{j, l, r}:
      INode{i, ids_cons(r, j), l}

def odd(+n: U32) -> Bool:
  U32.is_eq(U32.and(n, 1), 1)

# the id at position n; z: is n zero, o: is n odd
def ids_at(t: Ids, z: Bool, o: Bool, n: U32) -> U32:
  match t z o:
    case INode{i, l, r} True{} _:
      i
    case INode{i, l, r} False{} True{}:
      +m = (n >> 1n : U32)
      ids_at(l, U32.is_eq(m, 0), odd(m), m)
    case INode{i, l, r} False{} False{}:
      +m = ((n >> 1n : U32) - 1 : U32)
      ids_at(r, U32.is_eq(m, 0), odd(m), m)
    case INil{} _ _:
      0

def id_of(ids: Ids, +n: U32) -> U32:
  ids_at(ids, U32.is_eq(n, 0), odd(n), n)

# n fresh ids: the free list first, then the next ids
def take(n: Nat, r: Regs, ids: Ids) -> Tk:
  match n:
    case 0n:
      Tk{r, ids}
    case 1n+p:
      Regs{book, c, fl, nx, nm} = r
      match fl:
        case Con{i, f}:
          take(p, Regs{book, c, f, nx, nm}, ids_cons(ids, i))
        case Nil{}:
          take(p, Regs{book, c, Nil{}, (nx + 1 : U32), nm}, ids_cons(ids, nx))

# cell i freed
def free(r: Regs, i: U32) -> Regs:
  Regs{book, c, fl, nx, nm} = r
  Regs{book, c, i <> fl, nx, nm}

# n interactions counted
def ticks(r: Regs, n: U32) -> Regs:
  Regs{book, c, fl, nx, nm} = r
  Regs{book, (c + n : U32), fl, nx, nm}

# a template copied over fresh ids: binder id i becomes the id at
# position i
def term_inst(+ids: Ids, t: Term) -> Term:
  match t:
    case Var{i}:
      Var{id_of(ids, i)}
    case Cov{l, i, s}:
      Cov{l, id_of(ids, i), s}
    case Sup{l, x, y}:
      Sup{l, term_inst(ids, x), term_inst(ids, y)}
    case Dup{l, i, v, k}:
      Dup{l, id_of(ids, i), term_inst(ids, v), term_inst(ids, k)}
    case Lam{i, f}:
      Lam{id_of(ids, i), term_inst(ids, f)}
    case Drp{f}:
      Drp{term_inst(ids, f)}
    case App{f, x}:
      App{term_inst(ids, f), term_inst(ids, x)}
    case Use{f}:
      Use{term_inst(ids, f)}
    case Pak{bs, x}:
      Pak{bs, term_inst(ids, x)}
    case Tup{x, y}:
      Tup{term_inst(ids, x), term_inst(ids, y)}
    case Get{f}:
      Get{term_inst(ids, f)}
    case Mat{f, g}:
      Mat{term_inst(ids, f), term_inst(ids, g)}
    case u:
      u

# a variable read its cell: a substitution continues and the cell is
# free, else the variable is free
def cell_var(r: Regs, k: Kont, +i: U32, p: Array<Cell> & Cell) -> Step:
  (env, cell) = p
  match cell:
    case Sub{t}:
      Step{env, Go{t}, k, free(r, i)}
    case _:
      Step{env, Kn{Var{i}}, k, r}

# a dup variable read its cell: the twin's copy and the cell is free,
# or the value still to copy (evaluated under a Dpk frame), or nothing
def cell_cov(r: Regs, k: Kont, +l: U32, +i: U32, +s: Bool, p: Array<Cell> & Cell) -> Step:
  (env, cell) = p
  match cell:
    case Sub{t}:
      Step{env, Go{t}, k, free(r, i)}
    case Sha{v}:
      Step{env, Go{v}, Dpk{l, i, s, k}, r}
    case Nul{}:
      Step{env, Kn{Cov{l, i, s}}, k, r}

def def_ref.go(env: Array<Cell>, k: Kont, t: Term, tk: Tk) -> Step:
  Tk{r, ids} = tk
  Step{env, Go{term_inst(ids, t)}, k, r}

# a reference: the template copied over fresh ids (one interaction)
def def_ref(
  env: Array<Cell>,
  k: Kont,
  c: U32,
  fl: List<&2, U32>,
  nx: U32,
  nm: U32,
  p: Array<Def> & Def
) -> Step:
  (book, d) = p
  Def{n, t} = d
  def_ref.go(env, k, t, take(n, Regs{book, (c + 1 : U32), fl, nx, nm}, INil{}))

def term_app.sup(env: Array<Cell>, k: Kont, +l: U32, a: Term, b: Term, x: Term, tk: Tk) -> Step:
  Tk{r, ids} = tk
  +j = id_of(ids, 0)
  Step{Array.set(Cell, env, j, Sha{x}),
    Kn{Sup{l, App{a, Cov{l, j, False{}}}, App{b, Cov{l, j, True{}}}}}, k, r}

# a whnf applied to x
def term_app(env: Array<Cell>, r: Regs, k: Kont, w: Term, x: Term) -> Step:
  match w:
    case Lam{i, f}:
      Step{Array.set(Cell, env, i, Sub{x}), Go{f}, k, ticks(r, 1)}
    case Drp{f}:
      Step{env, Fr{x}, Nxt{Go{f}, k}, ticks(r, 1)}
    case Era{}:
      Step{env, Fr{x}, Nxt{Kn{Era{}}, k}, ticks(r, 1)}
    case Sup{l, a, b}:
      term_app.sup(env, k, l, a, b, x, take(1n, ticks(r, 1), INil{}))
    case Use{f}:
      Step{env, Go{x}, Elk{Use{f}, k}, r}
    case Mat{f, g}:
      Step{env, Go{x}, Elk{Mat{f, g}, k}, r}
    case Get{f}:
      Step{env, Go{x}, Elk{Get{f}, k}, r}
    case u:
      Step{env, Kn{App{u, x}}, k, r}

# a run over t, or t itself when the run is empty
def bits_pak(bs: List<&2, Bool>, t: Term) -> Term:
  match bs:
    case Nil{}:
      t
    case r:
      Pak{r, t}

# an eliminator meets a sup: the sup's children get the eliminator,
# whose children they share through fresh cells
def term_elim.on(
  env: Array<Cell>,
  r: Regs,
  k: Kont,
  +m: U32,
  x: Term,
  y: Term,
  +ids: Ids,
  e: Term
) -> Step:
  match e:
    case Use{f}:
      +j = id_of(ids, 0)
      Step{Array.set(Cell, env, j, Sha{f}),
        Kn{Sup{m, App{Use{Cov{m, j, False{}}}, x}, App{Use{Cov{m, j, True{}}}, y}}}, k, r}
    case Get{f}:
      +j = id_of(ids, 0)
      Step{Array.set(Cell, env, j, Sha{f}),
        Kn{Sup{m, App{Get{Cov{m, j, False{}}}, x}, App{Get{Cov{m, j, True{}}}, y}}}, k, r}
    case Mat{f, g}:
      +j = id_of(ids, 0)
      +j2 = id_of(ids, 1)
      Step{Array.set(Cell, Array.set(Cell, env, j, Sha{f}), j2, Sha{g}),
        Kn{Sup{m,
          App{Mat{Cov{m, j, False{}}, Cov{m, j2, False{}}}, x},
          App{Mat{Cov{m, j, True{}}, Cov{m, j2, True{}}}, y}}}, k, r}
    case u:
      Step{env, Kn{App{u, Sup{m, x, y}}}, k, r}

def term_elim.sup(env: Array<Cell>, k: Kont, m: U32, x: Term, y: Term, e: Term, tk: Tk) -> Step:
  Tk{r, ids} = tk
  term_elim.on(env, r, k, m, x, y, ids, e)

# a match: the arm of bit b continues on x, the other arm is freed
def term_elim.mat(env: Array<Cell>, r: Regs, k: Kont, b: Bool, f: Term, g: Term, x: Term) -> Step:
  match b:
    case False{}:
      Step{env, Fr{g}, Nxt{Go{f}, Arg{x, k}}, r}
    case True{}:
      Step{env, Fr{f}, Nxt{Go{g}, Arg{x, k}}, r}

# an eliminator meets its scrutinee's whnf
def term_elim(env: Array<Cell>, r: Regs, k: Kont, e: Term, w: Term) -> Step:
  match e w:
    case Use{f} One{}:
      Step{env, Go{f}, k, ticks(r, 1)}
    case Get{f} Tup{a, b}:
      Step{env, Go{f}, Arg{a, Arg{b, k}}, ticks(r, 1)}
    case Mat{f, g} Pak{Con{b, bs}, t}:
      term_elim.mat(env, ticks(r, 1), k, b, f, g, bits_pak(bs, t))
    case u Era{}:
      Step{env, Fr{u}, Nxt{Kn{Era{}}, k}, ticks(r, 1)}
    case Mat{f, g} Sup{m, x, y}:
      term_elim.sup(env, k, m, x, y, Mat{f, g}, take(2n, ticks(r, 1), INil{}))
    case u Sup{m, x, y}:
      term_elim.sup(env, k, m, x, y, u, take(1n, ticks(r, 1), INil{}))
    case u v:
      Step{env, Kn{App{u, v}}, k, r}

# does a dup of label l meet a sup of its own label
def dup_same(+l: U32, w: Term) -> Bool:
  match w:
    case Sup{m, a, b}:
      U32.is_eq(l, m)
    case u:
      False{}

# the fresh cells a dup of w takes
def dup_cells(same: Bool, w: Term) -> Nat:
  match w:
    case Lam{j, f}:
      3n
    case Tup{a, b}:
      2n
    case Mat{f, g}:
      2n
    case Sup{m, a, b}:
      pick(Nat, same, 0n, 2n)
    case Drp{f}:
      1n
    case Use{f}:
      1n
    case Get{f}:
      1n
    case Pak{bs, One{}}:
      0n
    case Pak{bs, t}:
      1n
    case u:
      0n

# a dup settles: the asking side's copy continues, the twin's parks in
# the cell (one interaction)
def term_dup.fin(env: Array<Cell>, r: Regs, k: Kont, i: U32, s: Bool, a: Term, b: Term) -> Step:
  match s:
    case False{}:
      Step{Array.set(Cell, env, i, Sub{b}), Go{a}, k, ticks(r, 1)}
    case True{}:
      Step{Array.set(Cell, env, i, Sub{a}), Go{b}, k, ticks(r, 1)}

# a dup cell meets its value's whnf: one layer copied, the children
# shared through fresh cells; a sup of the same label is the two
# copies; a stuck value parks back
def term_dup.on(
  env: Array<Cell>,
  r: Regs,
  k: Kont,
  +l: U32,
  +i: U32,
  +s: Bool,
  +ids: Ids,
  same: Bool,
  w: Term
) -> Step:
  match same w:
    case _ Era{}:
      term_dup.fin(env, r, k, i, s, Era{}, Era{})
    case _ One{}:
      term_dup.fin(env, r, k, i, s, One{}, One{})
    case _ Lam{x, f}:
      +j = id_of(ids, 0)
      +j2 = id_of(ids, 1)
      +j3 = id_of(ids, 2)
      term_dup.fin(
        Array.set(Cell, Array.set(Cell, env, j, Sha{f}), x, Sub{Sup{l, Var{j2}, Var{j3}}}),
        r, k, i, s, Lam{j2, Cov{l, j, False{}}}, Lam{j3, Cov{l, j, True{}}})
    case _ Drp{f}:
      +j = id_of(ids, 0)
      term_dup.fin(Array.set(Cell, env, j, Sha{f}), r, k, i, s,
        Drp{Cov{l, j, False{}}}, Drp{Cov{l, j, True{}}})
    case _ Use{f}:
      +j = id_of(ids, 0)
      term_dup.fin(Array.set(Cell, env, j, Sha{f}), r, k, i, s,
        Use{Cov{l, j, False{}}}, Use{Cov{l, j, True{}}})
    case _ Get{f}:
      +j = id_of(ids, 0)
      term_dup.fin(Array.set(Cell, env, j, Sha{f}), r, k, i, s,
        Get{Cov{l, j, False{}}}, Get{Cov{l, j, True{}}})
    case _ Tup{a, b}:
      +j = id_of(ids, 0)
      +j2 = id_of(ids, 1)
      term_dup.fin(Array.set(Cell, Array.set(Cell, env, j, Sha{a}), j2, Sha{b}), r, k, i, s,
        Tup{Cov{l, j, False{}}, Cov{l, j2, False{}}}, Tup{Cov{l, j, True{}}, Cov{l, j2, True{}}})
    case _ Mat{f, g}:
      +j = id_of(ids, 0)
      +j2 = id_of(ids, 1)
      term_dup.fin(Array.set(Cell, Array.set(Cell, env, j, Sha{f}), j2, Sha{g}), r, k, i, s,
        Mat{Cov{l, j, False{}}, Cov{l, j2, False{}}}, Mat{Cov{l, j, True{}}, Cov{l, j2, True{}}})
    case True{} Sup{m, a, b}:
      term_dup.fin(env, r, k, i, s, a, b)
    case False{} Sup{m, a, b}:
      +j = id_of(ids, 0)
      +j2 = id_of(ids, 1)
      term_dup.fin(Array.set(Cell, Array.set(Cell, env, j, Sha{a}), j2, Sha{b}), r, k, i, s,
        Sup{m, Cov{l, j, False{}}, Cov{l, j2, False{}}}, Sup{m, Cov{l, j, True{}}, Cov{l, j2, True{}}})
    case _ Pak{bs, One{}}:
      term_dup.fin(env, ticks(r, bits_len(bs)), k, i, s, Pak{bs, One{}}, Pak{bs, One{}})
    case _ Pak{bs, t}:
      +j = id_of(ids, 0)
      term_dup.fin(Array.set(Cell, env, j, Sha{t}), ticks(r, (bits_len(bs) - 1 : U32)), k, i, s,
        Pak{bs, Cov{l, j, False{}}}, Pak{bs, Cov{l, j, True{}}})
    case _ u:
      Step{Array.set(Cell, env, i, Sha{u}), Kn{Cov{l, i, s}}, k, r}

def term_dup.go(env: Array<Cell>, k: Kont, l: U32, i: U32, s: Bool, same: Bool, w: Term, tk: Tk) -> Step:
  Tk{r, ids} = tk
  term_dup.on(env, r, k, l, i, s, ids, same, w)

# a dup cell (label l, id i, side s asking) meets its value's whnf
def term_dup(env: Array<Cell>, r: Regs, k: Kont, w: Term, +l: U32, i: U32, s: Bool) -> Step:
  +v = w
  +same = dup_same(l, v)
  term_dup.go(env, k, l, i, s, same, v, take(dup_cells(same, v), r, INil{}))

# a term freed to the end: the next term to free, or the mode to resume
def term_free.pop(env: Array<Cell>, r: Regs, k: Kont) -> Step:
  match k:
    case Frk{t, q}:
      Step{env, Fr{t}, q, r}
    case Nxt{m, q}:
      Step{env, m, q, r}
    case q:
      Step{env, Kn{Era{}}, q, r}

# a dropped variable: its substitution, if any, is freed with its cell
def free_var(r: Regs, k: Kont, +i: U32, p: Array<Cell> & Cell) -> Step:
  (env, cell) = p
  match cell:
    case Sub{t}:
      Step{env, Fr{t}, k, free(r, i)}
    case _:
      term_free.pop(env, r, k)

# a dropped dup variable: the twin's parked copy is freed with the cell;
# a value not yet copied stays for the twin
def free_cov(r: Regs, k: Kont, +i: U32, p: Array<Cell> & Cell) -> Step:
  (env, cell) = p
  match cell:
    case Sub{t}:
      Step{env, Fr{t}, k, free(r, i)}
    case Sha{v}:
      term_free.pop(Array.set(Cell, env, i, Sha{v}), r, k)
    case Nul{}:
      term_free.pop(env, r, k)

# a dropped term walked: a lambda's variable will read an eraser (the
# variable may live outside, in a dup's copy), a dup's cell is free
def term_free(env: Array<Cell>, r: Regs, k: Kont, t: Term) -> Step:
  match t:
    case Var{i}:
      +j = i
      free_var(r, k, j, Array.swap(Cell, env, j, Nul{}))
    case Cov{l, i, s}:
      +j = i
      free_cov(r, k, j, Array.swap(Cell, env, j, Nul{}))
    case Lam{i, f}:
      Step{Array.set(Cell, env, i, Sub{Era{}}), Fr{f}, k, r}
    case Dup{l, i, v, q}:
      Step{env, Fr{v}, Frk{q, k}, free(r, i)}
    case App{f, x}:
      Step{env, Fr{f}, Frk{x, k}, r}
    case Sup{l, a, b}:
      Step{env, Fr{a}, Frk{b, k}, r}
    case Tup{a, b}:
      Step{env, Fr{a}, Frk{b, k}, r}
    case Mat{f, g}:
      Step{env, Fr{f}, Frk{g, k}, r}
    case Drp{f}:
      Step{env, Fr{f}, k, r}
    case Use{f}:
      Step{env, Fr{f}, k, r}
    case Get{f}:
      Step{env, Fr{f}, k, r}
    case Pak{bs, x}:
      Step{env, Fr{x}, k, r}
    case u:
      term_free.pop(env, r, k)

# a live lambda gets the next display name
def term_nf.lam(env: Array<Cell>, k: Kont, i: U32, f: Term, r: Regs) -> Step:
  Regs{book, c, fl, nx, nm} = r
  +n = (nm + 1 : U32)
  Step{Array.set(Cell, env, i, Sub{Nam{n}}), Go{f}, NfK{Rb1{x => Lam{n, x}, k}},
    Regs{book, c, fl, nx, n}}

# a whnf to normalize: its children normalize left to right and the
# node is rebuilt (a stuck application too, so no reference survives)
def term_nf(env: Array<Cell>, r: Regs, k: Kont, w: Term) -> Step:
  match w:
    case Sup{l, a, b}:
      Step{env, Go{a}, NfK{Rb2{x => y => Sup{l, x, y}, b, k}}, r}
    case Tup{a, b}:
      Step{env, Go{a}, NfK{Rb2{x => y => Tup{x, y}, b, k}}, r}
    case Mat{f, g}:
      Step{env, Go{f}, NfK{Rb2{x => y => Mat{x, y}, g, k}}, r}
    case Pak{bs, t}:
      Step{env, Go{t}, NfK{Rb1{x => Pak{bs, x}, k}}, r}
    case Use{f}:
      Step{env, Go{f}, NfK{Rb1{x => Use{x}, k}}, r}
    case Get{f}:
      Step{env, Go{f}, NfK{Rb1{x => Get{x}, k}}, r}
    case Drp{f}:
      Step{env, Go{f}, NfK{Rb1{x => Drp{x}, k}}, r}
    case App{f, x}:
      Step{env, Go{f}, NfK{Rb2{a => b => App{a, b}, x, k}}, r}
    case Lam{i, f}:
      term_nf.lam(env, k, i, f, r)
    case u:
      Step{env, Kn{u}, k, r}

# the loop: a term steps, a whnf goes to the top frame; End answers
# the normal form and the interaction count
@unsafe
def step_run(s: Step) -> Term & U32:
  Step{env, m, k, r} = s
  match m:
    case Go{t}:
      match t:
        case App{f, x}:
          step_run(Step{env, Go{f}, Arg{x, k}, r})
        case Var{i}:
          +j = i
          step_run(cell_var(r, k, j, Array.swap(Cell, env, j, Nul{})))
        case Cov{l, i, sd}:
          +j = i
          step_run(cell_cov(r, k, l, j, sd, Array.swap(Cell, env, j, Nul{})))
        case Dup{l, i, v, q}:
          step_run(Step{Array.set(Cell, env, i, Sha{v}), Go{q}, k, r})
        case Ref{ix}:
          Regs{book, c, fl, nx, nm} = r
          step_run(def_ref(env, k, c, fl, nx, nm, Array.get(Def, book, ix)))
        case u:
          step_run(Step{env, Kn{u}, k, r})
    case Fr{t}:
      step_run(term_free(env, r, k, t))
    case Kn{w}:
      match k:
        case End{}:
          Regs{book, c, fl, nx, nm} = r
          (w, c)
        case Arg{x, q}:
          step_run(term_app(env, r, q, w, x))
        case Elk{e, q}:
          step_run(term_elim(env, r, q, e, w))
        case Dpk{l, i, sd, q}:
          step_run(term_dup(env, r, q, w, l, i, sd))
        case NfK{q}:
          step_run(term_nf(env, r, q, w))
        case Rb1{f, q}:
          step_run(Step{env, Kn{f(w)}, q, r})
        case Rb2{f, b, q}:
          step_run(Step{env, Go{b}, NfK{Rb1{f(w), q}}, r})
        case Frk{t, q}:
          step_run(Step{env, Fr{t}, q, r})
        case Nxt{m, q}:
          step_run(Step{env, m, q, r})

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
      nam(n)
    case Lam{n, f}:
      lam() ++ nam(n) ++ "." ++ term_show(f)
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
    case Pak{bs, x}:
      bits_open(bs) ++ term_show(x) ++ bits_close(bs)
    case App{f, x}:
      "(" ++ term_show(f) ++ " " ++ term_show(x) ++ ")"
    case u:
      "<var>"

# Main
# ====

# the env: 2^20 cells; the free list keeps the live set small
def env_new() -> Array<Cell>:
  Array.new(Cell, 20n, Nul{})

def out(p: Term & U32) -> IO(Unit):
  (w, c) = p
  IO.print(term_show(w) ++ "\n- Itrs: " ++ U32.show(c) ++ " interactions")

# the depth of an array with room for n entries; f: the bits left to try
def book_depth(f: Nat, +n: U32, +d: Nat) -> Nat:
  match f:
    case 0n:
      d
    case 1n+p:
      pick(Nat, U32.is_le(n, (1 << d : U32)), d, book_depth(p, n, 1n+d))

# the definitions written into the book
def book_load(es: List<&2, Ent>, a: Array<Def>) -> Array<Def>:
  match es:
    case Con{Ent{ix, d}, r}:
      book_load(r, Array.set(Def, a, ix, d))
    case Nil{}:
      a

# is definition ix among the parsed ones
def ents_has(es: List<&2, Ent>, +ix: U32) -> Bool:
  match es:
    case Con{Ent{i, d}, r}:
      U32.is_eq(i, ix) || ents_has(r, ix)
    case Nil{}:
      False{}

# @main normalized and printed; a book without it is an error
def book_run.fin(es: List<&2, Ent>, ix: U32, n: U32, ok: Bool) -> IO(Unit):
  match ok:
    case True{}:
      out(step_run(Step{env_new(), Go{Ref{ix}}, NfK{End{}},
        Regs{book_load(es, Array.new(Def, book_depth(32n, n, 0n), Def{0n, Era{}})), 0, Nil{}, 0, 0}}))
    case False{}:
      IO.print("undefined function @main")

def book_run.go(es: List<&2, Ent>, p: Names & U32) -> IO(Unit):
  (ns, ix) = p
  Names{m, n} = ns
  +e = es
  +i = ix
  book_run.fin(e, i, n, ents_has(e, i))

def book_run(es: List<&2, Ent>, s: St) -> IO(Unit):
  St{h, src, sc, vc, ns} = s
  book_run.go(es, names_find(ns, "main"))

def main() -> IO(Unit):
  prog()(book_run, st_new(src(), Nil{}, 0, Names{Map.new(&2, U32), 0}))
