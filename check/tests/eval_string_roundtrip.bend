# Base String: split/join round-trips through a separator, and
# concat/length count code points. Pure.
# ported from bend3: String.split takes (s, sep-Char), String.join
# takes (xs, sep); lengths are Nats read back through U32.from_nat;
# concat is String.append
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

assert bu:
  forall b: Bool
  U32

def bu(b):
  match b:
    case False{}:
      0
    case True{}:
      1

assert main.out:
  U32

def main.out():
  b = bu(String.eq(String.join(String.split("a,b,c", ','), ","), "a,b,c"))
  l = U32.from_nat(List.length(String, String.split("a,b,c", ',')))
  n = U32.from_nat(String.length(String.append("ab", "cd")))
  U32.add(U32.add(b, U32.mul(l, 100)), U32.mul(n, 10))

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
341
$$ bend % --seq
341
exit 0
$$ bend % --par
341
exit 0
$$ bend % --js
341
exit 0
