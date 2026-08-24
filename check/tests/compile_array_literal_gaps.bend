# u32 array: gaps + default, set (swap), get, fold
# ported from bend3: the ![..] literal becomes Array.new(3n, 7) plus
# swaps; the fold counter walks a +Nat with its U32 index rebuilt
# from the twice-read predecessor the Cop witness licenses, strict
import Base

assert wr:
  forall m: Array<U32>
  forall i: U32
  forall v: U32
  Array<U32>

def wr(m, i, v):
  (m2, old) = Array.swap(U32, m, i, v)
  m2

assert suma:
  forall +k: +Nat
  forall a: Array<U32>
  forall acc: U32
  U32

def suma(k, a, acc):
  match k:
    case 0n:
      (a2, x) = Array.get(a, 0)
      U32.add(acc, x)
    case 1n+p:
      (a2, x) = Array.get(a, U32.add(U32.from_nat(p), 1))
      suma(p, a2, U32.add(U32.mul(acc, 31), x))

assert main.out:
  U32

def main.out():
  (b2, old) = Array.swap(U32, wr(wr(wr(Array.new(3n, 7), 0, 11), 2, 22), 5, 33), 1, 99)
  (b3, x) = Array.get(b2, 1)
  suma(5n, b3, U32.add(old, x))

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
3065382255
$$ bend % --seq
3065382255
exit 0
$$ bend % --par
3065382255
exit 0
$$ bend % --js
3065382255
exit 0
