# the new base text surface at runtime: Nat.show/Nat.read round trips
# and rejections, String.cmp's code-point order (a shorter prefix
# sorts first), eq/length edges, and split/join round trips
import Base

assert Char.eq:
  forall a: Char
  forall b: Char
  (Char & Char) & Bool

def Char.eq(a, b):
  ((a2, b2), c) = Char.cmp(a, b)
  ((a2, b2), Cmp.is_eq(c))

assert String.split.push:
  forall c: Char
  forall ps: List<String>
  List<String>

def String.split.push(c, ps):
  match ps:
    case Nil{}:
      Con{SCon{c, SNil{}}, Nil{}}
    case Con{h, t}:
      Con{SCon{c, h}, t}

assert String.split:
  forall s: String
  forall sep: Char
  List<String>

def String.split(s, sep):
  match s:
    case SNil{}:
      Con{SNil{}, Nil{}}
    case SCon{h, t}:
      ((h2, sep2), e) = Char.eq(h, sep)
      match e:
        case True{}:
          Con{SNil{}, String.split(t, sep2)}
        case False{}:
          String.split.push(h2, String.split(t, sep2))

assert String.join.go:
  forall xs: List<String>
  forall h: String
  forall sep: String
  String

def String.join.go(xs, h, sep):
  match xs:
    case Nil{}:
      h
    case Con{h2, t2}:
      (s1, s2) = String.copy(sep)
      String.append(h, String.append(s1, String.join.go(t2, h2, s2)))

assert String.join:
  forall xs: List<String>
  forall sep: String
  String

def String.join(xs, sep):
  match xs:
    case Nil{}:
      SNil{}
    case Con{h, t}:
      String.join.go(t, h, sep)

assert List.length:
  forall -A: Type
  forall xs: List<A>
  Nat

def List.length(A, xs):
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      1n+List.length(A, t)

assert String.length:
  forall s: String
  Nat

def String.length(s):
  match s:
    case SNil{}:
      0n
    case SCon{h, t}:
      1n+String.length(t)

assert Nat.is_eq:
  forall a: Nat
  forall b: Nat
  Bool

def Nat.is_eq(a, b):
  Cmp.is_eq(Nat.cmp(a, b))

assert bu:
  forall b: Bool
  U32

def bu(b):
  match b:
    case False{}:
      0
    case True{}:
      1

assert rdn:
  forall s: String
  forall w: Nat
  Bool

def rdn(s, w):
  match Nat.read(s):
    case None{}:
      False{}
    case Some{v}:
      Nat.is_eq(v, w)

assert rdn_none:
  forall s: String
  Bool

def rdn_none(s):
  match Nat.read(s):
    case None{}:
      True{}
    case Some{v}:
      False{}

assert scmp:
  forall a: String
  forall b: String
  Cmp

def scmp(a, b):
  ((a2, b2), c) = String.cmp(a, b)
  c

assert llen:
  forall xs: List<String>
  Nat

def llen(xs):
  List.length(String, xs)

assert main.out:
  U32

def main.out():
  b0 = bu(String.eq(Nat.show(0n), "0"))
  b1 = bu(String.eq(Nat.show(105n), "105"))
  b2 = bu(rdn("678", 678n))
  b3 = bu(rdn(Nat.show(731n), 731n))
  b4 = bu(rdn_none("12x"))
  b5 = bu(rdn_none(""))
  b6 = bu(Cmp.is_lt(scmp("app", "apple")))
  b7 = bu(Cmp.is_gt(scmp("b", "apple")))
  b8 = bu(Cmp.is_eq(scmp("", "")))
  b9 = bu(Bool.not(String.eq("a", "b")))
  b10 = bu(Nat.is_eq(String.length(""), 0n))
  b11 = bu(Nat.is_eq(llen(String.split("", ',')), 1n))
  b12 = bu(Nat.is_eq(llen(String.split(",", ',')), 2n))
  b13 = bu(String.eq(String.join(String.split("x", ','), ","), "x"))
  s0 = U32.add(U32.add(U32.add(b0, b1), U32.add(b2, b3)), U32.add(U32.add(b4, b5), U32.add(b6, b7)))
  U32.add(s0, U32.add(U32.add(U32.add(b8, b9), U32.add(b10, b11)), U32.add(b12, b13)))

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
14
$$ bend % --seq
14
exit 0
$$ bend % --par
14
exit 0
$$ bend % --js
14
exit 0
