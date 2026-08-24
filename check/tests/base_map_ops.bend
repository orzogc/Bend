# Map (string-keyed patricia tree): set/get/has/del/size/union --
# bend3's base_map_ops in bend4's dialect: Map.get takes an explicit
# U32 copier (no Data class copies an open V), sizes are Nat, and
# every op takes the map first. The seven checks and their sum are
# the original's.
import Base

assert Nat.is_eq:
  forall a: Nat
  forall b: Nat
  Bool

def Nat.is_eq(a, b):
  Cmp.is_eq(Nat.cmp(a, b))

assert Map.size:
  forall -V: Type
  forall m: Map<V>
  Nat

def Map.size(V, m):
  match m:
    case MTip{}:
      0n
    case MLeaf{k, v}:
      1n
    case MNode{pos, lo, hi}:
      Nat.add(Map.size(V, lo), Map.size(V, hi))

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

assert m3:
  Map<U32>

def m3():
  Map.set(U32, Map.set(U32, Map.set(U32, Map.new(U32), "a", 1), "b", 2), "a", 5)

assert chk_reads:
  U32

def chk_reads():
  (m1, x) = Map.get(U32, u32cp, 0, m3(), "a")
  (m2, y) = Map.get(U32, u32cp, 0, m1, "zz")
  (m4, h) = Map.has(U32, m2, "b")
  b0 = b2u(U32.is_eq(x, 5))
  b1 = b2u(U32.is_eq(y, 0))
  b2 = b2u(h)
  b3 = b2u(Nat.is_eq(Map.size(U32, m4), 2n))
  U32.add(U32.add(b0, b1), U32.add(b2, b3))

assert chk_del:
  U32

def chk_del():
  b2u(Nat.is_eq(Map.size(U32, Map.del(U32, m3(), "a")), 1n))

assert chk_union:
  U32

def chk_union():
  (u1, z) = Map.get(U32, u32cp, 0, Map.union(U32, Map.del(U32, m3(), "a"), Map.set(U32, Map.new(U32), "c", 9)), "c")
  b5 = b2u(Nat.is_eq(Map.size(U32, u1), 2n))
  b6 = b2u(U32.is_eq(z, 9))
  U32.add(b5, b6)

assert main.out:
  U32

def main.out():
  U32.add(chk_reads(), U32.add(chk_del(), chk_union()))

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
7
$$ bend % --seq
7
exit 0
$$ bend % --par
7
exit 0
$$ bend % --js
7
exit 0
