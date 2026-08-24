# string algorithms: replace the FIRST occurrence via find/take/drop,
# replace-all-chars via split/join, count occurrences by walking finds
# ported from bend3: bend-base's String helpers are inlined (find as
# Maybe<U32>, split by char code); occurrence fuel becomes Nat; strict
# -- the continuation defs folded into their callers' case trees, and
# shared strings ride + binders over local Chr/Str Copy witnesses
import Base

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

assert replace1:
  forall +s: (+ String ~ Str.copy)
  forall +at: +U32
  forall n: U32
  forall w: String
  String

def replace1(s, at, n, w):
  String.append(stake(U32.to_nat(at), s), String.append(w, sdrop(U32.to_nat(U32.add(at, n)), s)))

assert occurs:
  forall fuel: Nat
  forall +p: (+ String ~ Str.copy)
  forall +s: (+ String ~ Str.copy)
  U32

def occurs(fuel, p, s):
  match fuel:
    case 0n:
      99
    case 1n+f:
      match sfind(p, s):
        case Some{i}:
          U32.add(1, occurs(f, p, sdrop(U32.to_nat(U32.add(i, 1)), s)))
        case None{}:
          0

assert main.out:
  U32

def main.out():
  b0 = bu(seq_(replace1("banana", Maybe.default(U32, sfind("an", "banana"), 99), 2, "X"), "bXana"))
  b1 = bu(seq_(sjoin("-", ssplit(44, "a,b,c")), "a-b-c"))
  b2 = bu(U32.is_eq(occurs(5n, "an", "banana"), 2))
  b3 = bu(U32.is_eq(occurs(5n, "zz", "banana"), 0))
  U32.add(U32.add(U32.add(b0, b1), b2), b3)

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
4
$$ bend % --seq
4
exit 0
$$ bend % --par
4
exit 0
$$ bend % --js
4
exit 0
