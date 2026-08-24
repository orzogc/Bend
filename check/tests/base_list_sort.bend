# List.sort (32-pass binary radix) on small, empty and high-bit inputs
# ported from bend3: bend-base's radix sort is inlined over bend4's List
# (Nil/Con) with the bit index as Nat; List.get becomes lget with a Nat
# index; strict -- the helper defs folded into their callers' case
# trees, shared words +U32, shared bit indexes +Nat
import Base

assert bu:
  forall b: Bool
  U32

def bu(b):
  match b:
    case False{}:
      0
    case True{}:
      1

assert lconcat:
  forall xs: List<U32>
  forall ys: List<U32>
  List<U32>

def lconcat(xs, ys):
  match xs:
    case Nil{}:
      ys
    case Con{h, t}:
      Con{h, lconcat(t, ys)}

assert lrev.go:
  forall xs: List<U32>
  forall acc: List<U32>
  List<U32>

def lrev.go(xs, acc):
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      lrev.go(t, Con{h, acc})

assert lrev:
  forall xs: List<U32>
  List<U32>

def lrev(xs):
  lrev.go(xs, Nil{})

assert spass:
  forall +b: +Nat
  forall xs: List<U32>
  forall zs: List<U32>
  forall os: List<U32>
  List<U32>

def spass(b, xs, zs, os):
  match xs:
    case Con{h0, t}:
      +h = {h0 : +U32}
      match U32.is_zero(U32.and(U32.shrn(b, h), 1)):
        case True{}:
          spass(b, t, Con{h, zs}, os)
        case False{}:
          spass(b, t, zs, Con{h, os})
    case Nil{}:
      lconcat(lrev(zs), lrev(os))

assert sgo:
  forall k: Nat
  forall +b: +Nat
  forall xs: List<U32>
  List<U32>

def sgo(k, b, xs):
  match k:
    case 0n:
      xs
    case 1n+j:
      sgo(j, 1n+b, spass(b, xs, Nil{}, Nil{}))

assert lsort:
  forall xs: List<U32>
  List<U32>

def lsort(xs):
  sgo(32n, 0n, xs)

assert digest.go:
  forall xs: List<U32>
  forall acc: U32
  U32

def digest.go(xs, acc):
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      digest.go(t, U32.add(U32.mul(acc, 10), h))

assert digest:
  forall xs: List<U32>
  U32

def digest(xs):
  digest.go(xs, 0)

assert lget:
  forall d: U32
  forall i: Nat
  forall xs: List<U32>
  (List<U32> & U32)

def lget(d, i, xs):
  match i xs:
    case 0n Nil{}:
      (Nil{}, d)
    case 0n Con{h0, t}:
      +h = {h0 : +U32}
      (Con{h, t}, h)
    case 1n+p Nil{}:
      (Nil{}, d)
    case 1n+p Con{h, t}:
      (t2, x) = lget(d, p, t)
      (Con{h, t2}, x)

assert big.x:
  forall big: List<U32>
  U32

def big.x(big):
  (b1, x) = lget(99, 0n, big)
  (b2, y) = lget(99, 1n, b1)
  (b3, z) = lget(99, 2n, b2)
  m3 = bu(U32.is_eq(x, 0))
  m4 = bu(U32.is_eq(y, 2147483648))
  m5 = bu(U32.is_eq(z, 4294967295))
  U32.add(U32.add(m3, m4), m5)

assert main.out:
  U32

def main.out():
  b0 = bu(U32.is_eq(digest(lsort(Con{5, Con{3, Con{9, Con{1, Con{4, Nil{}}}}}})), 13459))
  b1 = bu(U32.is_eq(digest(lsort(Nil{})), 0))
  b2 = bu(U32.is_eq(digest(lsort(Con{1, Con{2, Con{3, Nil{}}}})), 123))
  U32.add(U32.add(U32.add(b0, b1), b2), big.x(lsort(Con{4294967295, Con{0, Con{2147483648, Nil{}}}})))

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
6
$$ bend % --seq
6
exit 0
$$ bend % --par
6
exit 0
$$ bend % --js
6
exit 0
