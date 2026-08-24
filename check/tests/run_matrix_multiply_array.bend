# 3x3 matrix multiply over flat word arrays: dot-product loops threading
# TWO linear arrays through nested tuples; digest weighs all 9 cells
# ported from bend3: the 16-slot slabs become Array.new(4n, 0) + swap
# writes, loop counters become Nat with U32 images via U32.from_nat;
# strict -- the read defs folded into the counter matches, shared
# words +U32, walked Nats +Nat
import Base

assert wr:
  forall m: Array<U32>
  forall i: U32
  forall v: U32
  Array<U32>

def wr(m, i, v):
  (m2, old) = Array.swap(U32, m, i, v)
  m2

assert dot:
  forall k: Nat
  forall +i: +U32
  forall +j: +U32
  forall a: Array<U32>
  forall b: Array<U32>
  forall acc: U32
  (Array<U32> & (Array<U32> & U32))

def dot(k, i, j, a, b, acc):
  match k:
    case 0n:
      (a, (b, acc))
    case 1n+t0:
      +t = {t0 : +Nat}
      +tt = {U32.from_nat(t) : +U32}
      (a2, x) = Array.get(a, U32.add(U32.mul(i, 3), tt))
      (b2, y) = Array.get(b, U32.add(U32.mul(tt, 3), j))
      dot(t, i, j, a2, b2, U32.add(acc, U32.mul(x, y)))

assert cells:
  forall c: Nat
  forall a: Array<U32>
  forall b: Array<U32>
  forall acc: U32
  U32

def cells(c, a, b, acc):
  match c:
    case 0n:
      acc
    case 1n+t0:
      +t = {t0 : +Nat}
      +tt = {U32.from_nat(t) : +U32}
      (a2, (b2, v)) = dot(3n, U32.div(tt, 3), U32.mod(tt, 3), a, b, 0)
      cells(t, a2, b2, U32.add(acc, U32.mul(v, U32.add(tt, 1))))

assert builda:
  Array<U32>

def builda():
  wr(wr(wr(wr(wr(wr(wr(wr(wr(Array.new(4n, 0), 0, 1), 1, 2), 2, 3), 3, 4), 4, 5), 5, 6), 6, 7), 7, 8), 8, 9)

assert buildb:
  Array<U32>

def buildb():
  wr(wr(wr(wr(wr(wr(wr(wr(wr(Array.new(4n, 0), 0, 9), 1, 8), 2, 7), 3, 6), 4, 5), 5, 4), 6, 3), 7, 2), 8, 1)

assert main.out:
  U32

def main.out():
  cells(9n, builda(), buildb(), 0)

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
3825
$$ bend % --seq
3825
exit 0
$$ bend % --par
3825
exit 0
$$ bend % --js
3825
exit 0
