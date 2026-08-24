# Map + Set: the crit-bit map behaves -- from_list, get with default,
# has, del, pop, right-biased union, code-point-ordered to_list, and
# Set as the Map<Unit> alias (add/has/del/to_list). bend3's
# map_set_ops in bend4's dialect: Map.get takes an explicit U32
# copier, and the order check rides Map.keys joined plus Map.values
# folded to digits, since re-matching a match arm's field binder
# (bend3's entry-by-entry destructure) is walled here. Five checks,
# one digit each, the original's golden.
import Base

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

assert Map.values.go:
  forall -V: Type
  forall m: Map<V>
  forall acc: List<V>
  List<V>

def Map.values.go(V, m, acc):
  match m:
    case MTip{}:
      acc
    case MLeaf{k, v}:
      Con{v, acc}
    case MNode{pos, lo, hi}:
      Map.values.go(V, lo, Map.values.go(V, hi, acc))

assert Map.values:
  forall -V: Type
  forall m: Map<V>
  List<V>

def Map.values(V, m):
  Map.values.go(V, m, Nil{})

assert Set.to_list:
  forall s: Set()
  List<String>

def Set.to_list(s):
  Map.keys(Unit, s)

assert u32cp:
  forall v: U32
  U32 & U32

def u32cp(v):
  ((a, e1), (b, e2)) = U32.copy(v)
  (a, b)

assert b2u:
  forall b: Bool
  U32

def b2u(b):
  match b:
    case False{}:
      0
    case True{}:
      1

assert got:
  forall x: Maybe<U32>
  forall w: U32
  U32

def got(x, w):
  match x:
    case None{}:
      0
    case Some{v}:
      b2u(U32.is_eq(v, w))

assert is_none:
  forall x: Maybe<U32>
  U32

def is_none(x):
  match x:
    case None{}:
      1
    case Some{v}:
      0

assert digits:
  forall vs: List<U32>
  forall acc: U32
  U32

def digits(vs, acc):
  match vs:
    case Nil{}:
      acc
    case Con{h, t}:
      digits(t, U32.add(U32.mul(acc, 10), h))

assert m3:
  Map<U32>

def m3():
  Map.from_list(U32, [("apple", 1), ("app", 2), ("banana", 3)])

assert chk_get:
  U32

def chk_get():
  (m1, a) = Map.get(U32, u32cp, 0, m3(), "apple")
  (m2, b) = Map.get(U32, u32cp, 0, m1, "app")
  (m3b, c) = Map.get(U32, u32cp, 99, m2, "nope")
  (m4, hb) = Map.has(U32, m3b, "banana")
  U32.mul(U32.mul(b2u(U32.is_eq(a, 1)), b2u(U32.is_eq(b, 2))), U32.mul(b2u(U32.is_eq(c, 99)), b2u(hb)))

assert chk_del:
  U32

def chk_del():
  (m1, h) = Map.has(U32, Map.del(U32, m3(), "app"), "app")
  (m2, a) = Map.get(U32, u32cp, 0, m1, "apple")
  (m3c, pv) = Map.pop(U32, m2, "banana")
  (m4, pv2) = Map.pop(U32, m3c, "banana")
  U32.mul(U32.mul(b2u(Bool.not(h)), b2u(U32.is_eq(a, 1))), U32.mul(got(pv, 3), is_none(pv2)))

assert chk_union:
  U32

def chk_union():
  (u1, x) = Map.get(U32, u32cp, 0, Map.union(U32, Map.from_list(U32, [("a", 1), ("b", 2)]), Map.from_list(U32, [("b", 20), ("c", 30)])), "a")
  (u2, y) = Map.get(U32, u32cp, 0, u1, "b")
  (u3, z) = Map.get(U32, u32cp, 0, u2, "c")
  U32.mul(U32.mul(b2u(U32.is_eq(x, 1)), b2u(U32.is_eq(y, 20))), b2u(U32.is_eq(z, 30)))

assert chk_order:
  U32

def chk_order():
  ks = String.join(Map.keys(U32, m3()), ",")
  b2u(Bool.and(String.eq(ks, "app,apple,banana"), U32.is_eq(digits(Map.values(U32, m3()), 0), 213)))

assert chk_set:
  U32

def chk_set():
  (s1, hx) = Set.has(Set.add(Set.add(Set.add(Set.new(), "x"), "y"), "x"), "x")
  (s2, hz) = Set.has(s1, "z")
  (t1, hy) = Set.has(Set.del(Set.add(Set.add(Set.new(), "x"), "y"), "y"), "y")
  (t2, hx2) = Set.has(t1, "x")
  ks = String.join(Set.to_list(s2), ",")
  U32.mul(U32.mul(b2u(hx), b2u(Bool.not(hz))), U32.mul(b2u(String.eq(ks, "x,y")), U32.mul(b2u(Bool.not(hy)), b2u(hx2))))

assert main.out:
  U32

def main.out():
  U32.add(U32.add(U32.mul(chk_get(), 10000), U32.mul(chk_del(), 1000)), U32.add(U32.add(U32.mul(chk_union(), 100), U32.mul(chk_order(), 10)), chk_set()))

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
11111
$$ bend % --seq
11111
exit 0
$$ bend % --par
11111
exit 0
$$ bend % --js
11111
exit 0
