# binary search over a sorted array: O(1) reads drive a fuel-bounded
# halving loop; arrays are linear, so the search hands the array back
# (container FIRST, answer second) -- hits index, misses 99
# ported from bend3: the slab literal becomes Array.new + swap writes
# (8 = 2^3 slots), fuel becomes Nat; strict -- the continuation defs
# folded into the fuel match, shared words +U32 (Cop) binders
import Base

assert wr:
  forall m: Array<U32>
  forall i: U32
  forall v: U32
  Array<U32>

def wr(m, i, v):
  (m2, old) = Array.swap(U32, m, i, v)
  m2

assert bsearch:
  forall fuel: Nat
  forall m: Array<U32>
  forall +x: +U32
  forall +lo: +U32
  forall +hi: (+U32)
  (Array<U32> & U32)

def bsearch(fuel, m, x, lo, hi):
  match fuel:
    case 0n:
      (m, 99)
    case 1n+f:
      match U32.is_lt(lo, hi):
        case False{}:
          (m, 99)
        case True{}:
          +mid = {U32.div(U32.add(lo, hi), 2) : +U32}
          (m2, v0) = Array.get(m, mid)
          +v = {v0 : +U32}
          match U32.is_eq(v, x):
            case True{}:
              (m2, mid)
            case False{}:
              match U32.is_lt(v, x):
                case True{}:
                  bsearch(f, m2, x, U32.add(mid, 1), hi)
                case False{}:
                  bsearch(f, m2, x, lo, mid)

assert build:
  Array<U32>

def build():
  wr(wr(wr(wr(wr(wr(wr(wr(Array.new(3n, 0), 0, 1), 1, 3), 2, 4), 3, 5), 4, 9), 5, 12), 6, 20), 7, 31)

assert go:
  forall m: Array<U32>
  U32

def go(m):
  (m1, a) = bsearch(5n, m, 9, 0, 8)
  (m2, b) = bsearch(5n, m1, 1, 0, 8)
  (m3, c) = bsearch(5n, m2, 31, 0, 8)
  (m4, d) = bsearch(5n, m3, 2, 0, 8)
  U32.add(U32.add(U32.add(U32.mul(a, 1000), U32.mul(b, 100)), U32.mul(c, 10)), d)

assert main.out:
  U32

def main.out():
  go(build())

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
4169
$$ bend % --seq
4169
exit 0
$$ bend % --par
4169
exit 0
$$ bend % --js
4169
exit 0
