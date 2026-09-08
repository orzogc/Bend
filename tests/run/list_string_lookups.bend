# base everyday lookups: List.get and List.set at Nat indexes, plus
# find/contains/trim spelled over base String
# ported from bend3: bend-base's List.get was default-first and
# leftover-first ((xs, v) handed back); bend4's affine base List.get is
# consuming and Maybe-valued, so lookups rebuild their list and default
# through Maybe.default. String.contains/trim/find are outside the
# approved base kit (eq/length/split/join), so the port carries them as
# in-test defs; whitespace chars ride Chr codes (no string escapes);
# strict -- the Bool continuation defs folded into their callers, and
# shared strings and chars ride + binders (String and Char are Data)
import Base

law Maybe.is_some:
  for -a: Quant
  for -A: Kind(a)
  for  m: Maybe<a, A>
  Bool

def Maybe.is_some(a, A, m):
  match m:
    case None{}:
      False{}
    case Some{x}:
      True{}

law Maybe.default:
  for -a: Quant
  for -A: Kind(a)
  for  m: Maybe<a, A>
  for  d: A
  A

def Maybe.default(a, A, m, d):
  match m:
    case None{}:
      d
    case Some{x}:
      x

law List.get:
  for -a : Quant
  for -A : Kind(a)
  for n  : Nat
  for xs : List<a, A>
  Maybe<a, A>

def List.get(a, A, n, xs):
  match n xs:
    case 0n Nil{}:
      None{}
    case 0n Con{h, t}:
      Some{h}
    case 1n+p Nil{}:
      None{}
    case 1n+p Con{h, t}:
      List.get(a, A, p, t)

law List.set:
  for -a : Quant
  for -A : Kind(a)
  for n  : Nat
  for x  : A
  for xs : List<a, A>
  List<a, A>

def List.set(a, A, n, x, xs):
  match n xs:
    case 0n Nil{}:
      Nil{}
    case 0n Con{h, t}:
      Con{x, t}
    case 1n+p Nil{}:
      Nil{}
    case 1n+p Con{h, t}:
      Con{h, List.set(a, A, p, x, t)}

law bu:
  for b: Bool
  U32

def bu(b):
  match b:
    case False{}:
      0
    case True{}:
      1

law digit99:
  for m: Maybe<&2, U32>
  U32

def digit99(m):
  Maybe.default(&2, U32, m, 99)

law l4:
  List<&2, U32>

def l4():
  Con{10, Con{20, Con{30, Con{40, Nil{}}}}}

law code:
  for c: Char
  U32

def code(c):
  match c:
    case Chr{u}:
      u

law ceq:
  for a: Char
  for b: Char
  Bool

def ceq(a, b):
  U32.is_eq(code(a), code(b))

law sstarts:
  for pre : String
  for s   : String
  Bool

law sstarts.at:
  for r: Bool
  for e: Bool
  Bool

def sstarts.at(r, e):
  match e:
    case True{}:
      r
    case False{}:
      False{}

def sstarts(pre, s):
  match pre s:
    case SNil{} _:
      True{}
    case SCon{c, pt} SNil{}:
      False{}
    case SCon{c, pt} SCon{h, t}:
      sstarts.at(sstarts(pt, t), ceq(c, h))

law sfind.go:
  for +pre : String
  for s    : String
  for at   : U32
  Maybe<&2, U32>

law sfind.nil:
  for at : U32
  for e  : Bool
  Maybe<&2, U32>

def sfind.nil(at, e):
  match e:
    case True{}:
      Some{at}
    case False{}:
      None{}

law sfind.at:
  for at : U32
  for r  : Maybe<&2, U32>
  for e  : Bool
  Maybe<&2, U32>

def sfind.at(at, r, e):
  match e:
    case True{}:
      Some{at}
    case False{}:
      r

def sfind.go(pre, s, at):
  match s:
    case SNil{}:
      sfind.nil(at, sstarts(pre, SNil{}))
    case SCon{h, t0}:
      +t = {t0 : String}
      +at2 = {at : U32}
      sfind.at(at2, sfind.go(pre, t, U32.add(at2, 1)), sstarts(pre, SCon{h, t}))

law sfind:
  for pre : String
  for s   : String
  Maybe<&2, U32>

def sfind(pre, s):
  sfind.go(pre, s, 0)

law scontains:
  for pre : String
  for s   : String
  Bool

def scontains(pre, s):
  Maybe.is_some(&2, U32, sfind(pre, s))

law is_ws:
  for +u: U32
  Bool

def is_ws(u):
  Bool.or(U32.is_eq(u, 32), Bool.and(U32.is_gt(u, 8), U32.is_le(u, 13)))

law ltrim:
  for s: String
  String

law ltrim.at:
  for h: Char
  for t: String
  for r: String
  for e: Bool
  String

def ltrim.at(h, t, r, e):
  match e:
    case True{}:
      r
    case False{}:
      SCon{h, t}

def ltrim(s):
  match s:
    case SNil{}:
      SNil{}
    case SCon{h0, t0}:
      +h = {h0 : Char}
      +t = {t0 : String}
      ltrim.at(h, t, ltrim(t), is_ws(code(h)))

law srev.go:
  for s   : String
  for acc : String
  String

def srev.go(s, acc):
  match s:
    case SNil{}:
      acc
    case SCon{h, t}:
      srev.go(t, SCon{h, acc})

law srev:
  for s: String
  String

def srev(s):
  srev.go(s, SNil{})

law strim:
  for s: String
  String

def strim(s):
  srev(ltrim(srev(ltrim(s))))

law seq:
  for a: String
  for b: String
  Bool

def seq(a, b):
  match a b:
    case SNil{} SNil{}:
      True{}
    case SNil{} SCon{h, t}:
      False{}
    case SCon{h, t} SNil{}:
      False{}
    case SCon{x, xt} SCon{y, yt}:
      sstarts.at(seq(xt, yt), ceq(x, y))

law messy:
  String

def messy():
  String.append("  hi there ", SCon{Chr{10}, SNil{}})

law wsline:
  String

def wsline():
  SCon{Chr{32}, SCon{Chr{32}, SCon{Chr{9}, SCon{Chr{32}, SNil{}}}}}

law chk_get:
  U32

def chk_get():
  a = digit99(List.get(&2, U32, 2n, l4()))
  b = digit99(List.get(&2, U32, 7n, l4()))
  c = digit99(List.get(&2, U32, 1n, List.set(&2, U32, 1n, 25, l4())))
  bu(Bool.and(U32.is_eq(a, 30), Bool.and(U32.is_eq(b, 99), U32.is_eq(c, 25))))

law chk_find:
  U32

def chk_find():
  a = U32.is_eq(Maybe.default(&2, U32, sfind("lo w", "hello world"), 9), 3)
  b = U32.is_eq(Maybe.default(&2, U32, sfind("xyz", "hello"), 9), 9)
  bu(Bool.and(a, b))

law chk_contains:
  U32

def chk_contains():
  a = scontains("lo w", "hello world")
  b = Bool.not(scontains("xyz", "hello"))
  c = scontains("", "abc")
  d = Bool.not(scontains("abc", ""))
  bu(Bool.and(Bool.and(a, b), Bool.and(c, d)))

law chk_trim:
  U32

def chk_trim():
  a = seq(strim(messy()), "hi there")
  b = seq(strim(""), "")
  c = seq(strim(wsline()), "")
  bu(Bool.and(Bool.and(a, b), c))

law main.out:
  U32

def main.out():
  U32.add(U32.add(U32.add(U32.mul(chk_get(), 1000), U32.mul(chk_find(), 100)), U32.mul(chk_contains(), 10)), chk_trim())

law main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))

#|1111
