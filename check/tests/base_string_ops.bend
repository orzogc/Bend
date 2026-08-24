# String at runtime: length/concat/reverse/eq/contains/trim/upper/split/
# take/drop/join, each law one bit
# ported from bend3: bend-base's String helpers are inlined over bend4's
# String (SNil/SCon, Chr codes); find yields Maybe<U32>; split takes the
# separator's char code; take/drop counts become Nat
# (97 <= x is spelled U32.is_le(97, x): tocl lacks u32_is_ge, see
# run_word_compare's yellow); strict -- the continuation defs folded
# into their callers' case trees, shared codes +U32, and the find
# needle rides local Chr/Str Copy witnesses
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

assert bu:
  forall b: Bool
  U32

def bu(b):
  match b:
    case False{}:
      0
    case True{}:
      1

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

assert slen:
  forall s: String
  U32

def slen(s):
  match s:
    case SNil{}:
      0
    case SCon{h, t}:
      U32.add(1, slen(t))

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

assert seq_:
  forall a: String
  forall b: String
  Bool

def seq_(a, b):
  match a b:
    case SNil{} SNil{}:
      True{}
    case SNil{} SCon{h, t}:
      False{}
    case SCon{h, t} SNil{}:
      False{}
    case SCon{Chr{x}, t1} SCon{Chr{y}, t2}:
      match U32.is_eq(x, y):
        case True{}:
          seq_(t1, t2)
        case False{}:
          False{}

assert starts:
  forall p: String
  forall s: String
  Bool

def starts(p, s):
  match p s:
    case SNil{} _:
      True{}
    case SCon{h, t} SNil{}:
      False{}
    case SCon{Chr{x}, t1} SCon{Chr{y}, t2}:
      match U32.is_eq(x, y):
        case True{}:
          starts(t1, t2)
        case False{}:
          False{}

assert sfind:
  forall +p: (+ String ~ Str.copy)
  forall s: String
  Maybe<U32>

def sfind(p, s):
  match s:
    case SNil{}:
      match starts(p, SNil{}):
        case True{}:
          Some{0}
        case False{}:
          None{}
    case SCon{h, t0}:
      +t = {t0 : (+ String ~ Str.copy)}
      match starts(p, SCon{h, t}):
        case True{}:
          Some{0}
        case False{}:
          match sfind(p, t):
            case None{}:
              None{}
            case Some{i}:
              Some{U32.add(i, 1)}

assert triml:
  forall s: String
  String

def triml(s):
  match s:
    case SNil{}:
      SNil{}
    case SCon{Chr{x0}, t}:
      +x = {x0 : +U32}
      match U32.is_eq(x, 32):
        case True{}:
          triml(t)
        case False{}:
          SCon{Chr{x}, t}

assert strim:
  forall s: String
  String

def strim(s):
  srev(triml(srev(triml(s))))

assert supper:
  forall s: String
  String

def supper(s):
  match s:
    case SNil{}:
      SNil{}
    case SCon{Chr{x0}, t}:
      +x = {x0 : +U32}
      match Bool.and(U32.is_le(97, x), U32.is_le(x, 122)):
        case True{}:
          SCon{Chr{U32.sub(x, 32)}, supper(t)}
        case False{}:
          SCon{Chr{x}, supper(t)}

assert ssplit.push:
  forall c: Char
  forall ps: List<String>
  List<String>

def ssplit.push(c, ps):
  match ps:
    case Nil{}:
      Con{SCon{c, SNil{}}, Nil{}}
    case Con{h, t}:
      Con{SCon{c, h}, t}

assert ssplit:
  forall +sep: +U32
  forall s: String
  List<String>

def ssplit(sep, s):
  match s:
    case SNil{}:
      Con{SNil{}, Nil{}}
    case SCon{Chr{x0}, t}:
      +x = {x0 : +U32}
      match U32.is_eq(x, sep):
        case True{}:
          Con{SNil{}, ssplit(sep, t)}
        case False{}:
          ssplit.push(Chr{x}, ssplit(sep, t))

assert sjoin.go:
  forall +sep: (+ String ~ Str.copy)
  forall t: List<String>
  forall h: String
  String

def sjoin.go(sep, t, h):
  match t:
    case Nil{}:
      h
    case Con{h2, t2}:
      String.append(h, String.append(sep, sjoin.go(sep, t2, h2)))

assert sjoin:
  forall +sep: (+ String ~ Str.copy)
  forall xs: List<String>
  String

def sjoin(sep, xs):
  match xs:
    case Nil{}:
      SNil{}
    case Con{h, t}:
      sjoin.go(sep, t, h)

assert stake:
  forall n: Nat
  forall s: String
  String

def stake(n, s):
  match n s:
    case 0n _:
      SNil{}
    case 1n+p SNil{}:
      SNil{}
    case 1n+p SCon{h, t}:
      SCon{h, stake(p, t)}

assert sdrop:
  forall n: Nat
  forall s: String
  String

def sdrop(n, s):
  match n s:
    case 0n s2:
      s2
    case 1n+p SNil{}:
      SNil{}
    case 1n+p SCon{h, t}:
      sdrop(p, t)

assert llens:
  forall xs: List<String>
  U32

def llens(xs):
  match xs:
    case Nil{}:
      0
    case Con{h, t}:
      U32.add(1, llens(t))

assert main.out:
  U32

def main.out():
  b0 = bu(U32.is_eq(slen(String.append("foo", "bar")), 6))
  b1 = bu(seq_(srev("abc"), "cba"))
  b2 = bu(Maybe.is_some(U32, sfind("an", "banana")))
  b3 = U32.sub(1, bu(Maybe.is_some(U32, sfind("xy", "banana"))))
  b4 = bu(U32.is_eq(slen(strim("  hi  ")), 2))
  b5 = bu(seq_(supper("ab"), "AB"))
  b6 = bu(U32.is_eq(llens(ssplit(44, "a,bb,c")), 3))
  b7 = bu(seq_(stake(2n, "abcd"), "ab"))
  b8 = bu(seq_(sdrop(2n, "abcd"), "cd"))
  b9 = bu(seq_(sjoin(",", Con{"a", Con{"b", Nil{}}}), "a,b"))
  b10 = bu(U32.is_eq(Maybe.default(U32, sfind("an", "banana"), 99), 1))
  U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(b0, b1), b2), b3), b4), b5), b6), b7), b8), b9), b10)

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
11
$$ bend % --seq
11
exit 0
$$ bend % --par
11
exit 0
$$ bend % --js
11
exit 0
