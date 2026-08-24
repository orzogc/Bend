# bend3's interp cost guard (492 interactions at depth 24) loses its
# counter -- bend4 has no --stats -- and keeps its value: the
# accumulator loop rides a Nat countdown with a U32 mirror (the 1+n
# arm re-used the pred, which affine bend4 spells as two arguments)
import Base

assert spin:
  forall n: Nat
  forall i: U32
  forall acc: U32
  U32

def spin(n, i, acc):
  match n:
    case Zero{}:
      acc
    case Succ{k}:
      ((i1, d1), (i2, d2)) = U32.copy(i)
      spin(k, i1 - 1, acc + i2)

assert main.out:
  Nat

def main.out():
  U32.to_nat(spin(24n, 24, 0))

assert main:
  IO(Unit)

def main():
  IO.print(String.append(Nat.show(main.out()), "n"))
$$ bend %
300n
$$ bend % --seq
300n
exit 0
$$ bend % --par
300n
exit 0
$$ bend % --js
300n
exit 0
