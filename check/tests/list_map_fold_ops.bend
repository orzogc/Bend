# bend3's list_map_fold_ops intent -- map/filter/fold/any/all over a
# list and map/fold over a Map -- in bend4's dialect. bend3 rode base
# comp (~) templates; those are ruled out whole here, and generic
# List.map is not affine-checkable, so each template call becomes a
# local first-order recursion at U32 (the walk bend3's splice would
# have minted). The seven checks and their sum are the original's.
import Base

assert String.length:
  forall s: String
  Nat

def String.length(s):
  match s:
    case SNil{}:
      0n
    case SCon{h, t}:
      1n+String.length(t)

assert b2u:
  forall b: Bool
  U32

def b2u(b):
  match b:
    case False{}:
      0
    case True{}:
      1

assert dbl:
  forall xs: List<U32>
  List<U32>

def dbl(xs):
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{U32.mul(h, 2), dbl(t)}

assert keep_gt1:
  forall xs: List<U32>
  List<U32>

def keep_gt1(xs):
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      ((h1, e1), (h2, e2)) = U32.copy(h)
      match U32.is_gt(h1, 1):
        case True{}:
          Con{h2, keep_gt1(t)}
        case False{}:
          keep_gt1(t)

assert suma:
  forall xs: List<U32>
  forall acc: U32
  U32

def suma(xs, acc):
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      suma(t, U32.add(acc, h))

assert anyeq2:
  forall xs: List<U32>
  Bool

def anyeq2(xs):
  match xs:
    case Nil{}:
      False{}
    case Con{h, t}:
      match U32.is_eq(h, 2):
        case True{}:
          True{}
        case False{}:
          anyeq2(t)

assert allpos:
  forall xs: List<U32>
  Bool

def allpos(xs):
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      match U32.is_gt(h, 0):
        case True{}:
          allpos(t)
        case False{}:
          False{}

assert mmul10:
  forall m: Map<U32>
  Map<U32>

def mmul10(m):
  match m:
    case MTip{}:
      MTip{}
    case MLeaf{k, v}:
      MLeaf{k, U32.mul(v, 10)}
    case MNode{pos, lo, hi}:
      MNode{pos, mmul10(lo), mmul10(hi)}

assert mfold:
  forall m: Map<U32>
  forall acc: U32
  U32

def mfold(m, acc):
  match m:
    case MTip{}:
      acc
    case MLeaf{k, v}:
      U32.add(acc, U32.add(v, U32.from_nat(String.length(k))))
    case MNode{pos, lo, hi}:
      mfold(hi, mfold(lo, acc))

assert main.out:
  U32

def main.out():
  a = b2u(U32.is_eq(suma(dbl([1, 2, 3]), 0), 12))
  b = b2u(U32.is_eq(suma(keep_gt1([1, 2, 3]), 0), 5))
  c = b2u(U32.is_eq(suma([1, 2, 3], 100), 106))
  d = b2u(anyeq2([1, 2, 3]))
  e = b2u(allpos([1, 2, 3]))
  g = b2u(U32.is_eq(mfold(mmul10(Map.from_list(U32, [("a", 1), ("b", 2)])), 0), 32))
  U32.add(U32.add(U32.add(U32.mul(a, 1000000), U32.mul(b, 100000)), U32.add(U32.mul(c, 10000), U32.mul(d, 1000))), U32.add(U32.add(U32.mul(e, 100), U32.mul(g, 10)), 1))

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
1111111
$$ bend % --seq
1111111
exit 0
$$ bend % --par
1111111
exit 0
$$ bend % --js
1111111
exit 0
