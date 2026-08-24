# base everyday lookups: List.get and List.set at Nat indexes, plus
# find/contains/trim spelled over base String
# ported from bend3: bend-base's List.get was default-first and
# leftover-first ((xs, v) handed back); bend4's affine base List.get is
# consuming and Maybe-valued, so lookups rebuild their list and default
# through Maybe.default. String.contains/trim/find are outside the
# approved base kit (eq/length/split/join), so the port carries them as
# in-test defs; whitespace chars ride Chr codes (no string escapes);
# strict -- the Bool continuation defs folded into their callers, and
# shared strings and chars ride local Chr/Str Copy witnesses
import Base

assert Maybe.is_some:
  forall -A: Type
  forall m: Maybe<A>
  Bool

def Maybe.is_some(A, m):
  match m:
    case None{}:
      False{}
    case Some{x}:
      True{}

assert Maybe.default:
  forall -A: Type
  forall m: Maybe<A>
  forall d: A
  A

def Maybe.default(A, m, d):
  match m:
    case None{}:
      d
    case Some{x}:
      x

assert List.get:
  forall -A: Type
  forall n: Nat
  forall xs: List<A>
  Maybe<A>

def List.get(A, n, xs):
  match n xs:
    case 0n Nil{}:
      None{}
    case 0n Con{h, t}:
      Some{h}
    case 1n+p Nil{}:
      None{}
    case 1n+p Con{h, t}:
      List.get(A, p, t)

assert List.set:
  forall -A: Type
  forall n: Nat
  forall x: A
  forall xs: List<A>
  List<A>

def List.set(A, n, x, xs):
  match n xs:
    case 0n Nil{}:
      Nil{}
    case 0n Con{h, t}:
      Con{x, t}
    case 1n+p Nil{}:
      Nil{}
    case 1n+p Con{h, t}:
      Con{h, List.set(A, p, x, t)}

assert Chr.copy:
  forall c: Char
  Copy(Char, c) & Copy(Char, c)

def Chr.copy(c):
  match c:
    case Chr{n}:
      ((nx, ne), (ny, nf)) = U32.copy(n)
      e1 = Equal.cong(U32, Char, z => Chr{z}, n, nx, ne)
      e2 = Equal.cong(U32, Char, z => Chr{z}, n, ny, nf)
      ((Chr{nx}, e1), (Chr{ny}, e2))

assert Str.copy:
  forall s: String
  Copy(String, s) & Copy(String, s)

def Str.copy(s):
  match s:
    case SNil{}:
      ((SNil{}, {==}), (SNil{}, {==}))
    case SCon{h, t}:
      ((hx, he), (hy, hf)) = Chr.copy(h)
      ((tx, te), (ty, tf)) = Str.copy(t)
      s10 = Equal.cong(Char, String, z => SCon{z, t}, h, hx, he)
      s11 = Equal.cong(String, String, z => SCon{hx, z}, t, tx, te)
      t11 = Equal.trans(String, SCon{h, t}, SCon{hx, t}, SCon{hx, tx}, s10, s11)
      s20 = Equal.cong(Char, String, z => SCon{z, t}, h, hy, hf)
      s21 = Equal.cong(String, String, z => SCon{hy, z}, t, ty, tf)
      t21 = Equal.trans(String, SCon{h, t}, SCon{hy, t}, SCon{hy, ty}, s20, s21)
      ((SCon{hx, tx}, t11), (SCon{hy, ty}, t21))

assert bu:
  forall b: Bool
  U32

def bu(b):
  match b:
    case False{}:
      0
    case True{}:
      1

assert digit99:
  forall m: Maybe<U32>
  U32

def digit99(m):
  Maybe.default(U32, m, 99)

assert l4:
  List<U32>

def l4():
  Con{10, Con{20, Con{30, Con{40, Nil{}}}}}

assert code:
  forall c: Char
  U32

def code(c):
  match c:
    case Chr{u}:
      u

assert ceq:
  forall a: Char
  forall b: Char
  Bool

def ceq(a, b):
  U32.is_eq(code(a), code(b))

assert sstarts:
  forall pre: String
  forall s: String
  Bool

def sstarts(pre, s):
  match pre s:
    case SNil{} _:
      True{}
    case SCon{c, pt} SNil{}:
      False{}
    case SCon{c, pt} SCon{h, t}:
      match ceq(c, h):
        case True{}:
          sstarts(pt, t)
        case False{}:
          False{}

assert sfind.go:
  forall +pre: (+ String ~ Str.copy)
  forall s: String
  forall at: U32
  Maybe<U32>

def sfind.go(pre, s, at):
  match s:
    case SNil{}:
      match sstarts(pre, SNil{}):
        case True{}:
          Some{at}
        case False{}:
          None{}
    case SCon{h, t0}:
      +t = {t0 : (+ String ~ Str.copy)}
      match sstarts(pre, SCon{h, t}):
        case True{}:
          Some{at}
        case False{}:
          sfind.go(pre, t, U32.add(at, 1))

assert sfind:
  forall pre: String
  forall s: String
  Maybe<U32>

def sfind(pre, s):
  sfind.go(pre, s, 0)

assert scontains:
  forall pre: String
  forall s: String
  Bool

def scontains(pre, s):
  Maybe.is_some(U32, sfind(pre, s))

assert is_ws:
  forall +u: +U32
  Bool

def is_ws(u):
  Bool.or(U32.is_eq(u, 32), Bool.and(U32.is_gt(u, 8), U32.is_le(u, 13)))

assert ltrim:
  forall s: String
  String

def ltrim(s):
  match s:
    case SNil{}:
      SNil{}
    case SCon{h0, t}:
      +h = {h0 : (+ Char ~ Chr.copy)}
      match is_ws(code(h)):
        case True{}:
          ltrim(t)
        case False{}:
          SCon{h, t}

assert srev.go:
  forall s: String
  forall acc: String
  String

def srev.go(s, acc):
  match s:
    case SNil{}:
      acc
    case SCon{h, t}:
      srev.go(t, SCon{h, acc})

assert srev:
  forall s: String
  String

def srev(s):
  srev.go(s, SNil{})

assert strim:
  forall s: String
  String

def strim(s):
  srev(ltrim(srev(ltrim(s))))

assert seq:
  forall a: String
  forall b: String
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
      match ceq(x, y):
        case True{}:
          seq(xt, yt)
        case False{}:
          False{}

assert messy:
  String

def messy():
  String.append("  hi there ", SCon{Chr{10}, SNil{}})

assert wsline:
  String

def wsline():
  SCon{Chr{32}, SCon{Chr{32}, SCon{Chr{9}, SCon{Chr{32}, SNil{}}}}}

assert chk_get:
  U32

def chk_get():
  a = digit99(List.get(U32, 2n, l4()))
  b = digit99(List.get(U32, 7n, l4()))
  c = digit99(List.get(U32, 1n, List.set(U32, 1n, 25, l4())))
  bu(Bool.and(U32.is_eq(a, 30), Bool.and(U32.is_eq(b, 99), U32.is_eq(c, 25))))

assert chk_find:
  U32

def chk_find():
  a = U32.is_eq(Maybe.default(U32, sfind("lo w", "hello world"), 9), 3)
  b = U32.is_eq(Maybe.default(U32, sfind("xyz", "hello"), 9), 9)
  bu(Bool.and(a, b))

assert chk_contains:
  U32

def chk_contains():
  a = scontains("lo w", "hello world")
  b = Bool.not(scontains("xyz", "hello"))
  c = scontains("", "abc")
  d = Bool.not(scontains("abc", ""))
  bu(Bool.and(Bool.and(a, b), Bool.and(c, d)))

assert chk_trim:
  U32

def chk_trim():
  a = seq(strim(messy()), "hi there")
  b = seq(strim(""), "")
  c = seq(strim(wsline()), "")
  bu(Bool.and(Bool.and(a, b), c))

assert main.out:
  U32

def main.out():
  U32.add(U32.add(U32.add(U32.mul(chk_get(), 1000), U32.mul(chk_find(), 100)), U32.mul(chk_contains(), 10)), chk_trim())

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
1111
$$ bend % --seq
1111
exit 0
$$ bend % --par
1111
exit 0
$$ bend % --js
1111
exit 0
