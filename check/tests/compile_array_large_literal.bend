# a large array: 1024 slots default-filled, three slots written, strided
# reads at 0, 100, .., 1000
# ported from bend3: the ![..] literal with a default becomes
# Array.new(10n, 3) plus swaps; the read counter walks a +Nat whose
# Cop witness licenses the twice-read predecessor, strict
import Base

assert wr:
  forall m: Array<U32>
  forall i: U32
  forall v: U32
  Array<U32>

def wr(m, i, v):
  (m2, old) = Array.swap(U32, m, i, v)
  m2

assert rd:
  forall +k: +Nat
  forall a: Array<U32>
  forall acc: U32
  U32

def rd(k, a, acc):
  match k:
    case 0n:
      (a2, x) = Array.get(a, 0)
      U32.add(acc, x)
    case 1n+p:
      (a2, x) = Array.get(a, U32.mul(U32.add(U32.from_nat(p), 1), 100))
      rd(p, a2, U32.add(acc, x))

assert main.out:
  U32

def main.out():
  rd(10n, wr(wr(wr(Array.new(10n, 3), 0, 7), 500, 20), 1000, 9), 0)

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
60
$$ bend % --seq
60
exit 0
$$ bend % --par
60
exit 0
$$ bend % --js
60
exit 0
