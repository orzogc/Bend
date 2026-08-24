# bend3's stale-taint fork grouping (a sibling whose taint dies in the
# unfold); bend4 has no taint pass, so the shape itself carries -- the
# recursive sibling rides a Nat countdown with a U32 mirror, the pure
# sibling folds, and the typed fork joins them: 9
import Base

assert tl:
  forall n: Nat
  forall i: U32
  forall a0: U32
  U32

def tl(n, i, a0):
  match n:
    case Zero{}:
      a0 * 2
    case Succ{k}:
      ((i1, d1), (i2, d2)) = U32.copy(i)
      tl(k, i1 - 1, i2)

assert hf:
  forall f: U32 -> U32
  forall x: U32
  U32

def hf(f, x):
  f(1) + 2

assert main.out:
  Nat

def main.out():
  & p0 : U32 = tl(10n, 10, 3) & p1 : U32 = hf(y => 5, 7);
  U32.to_nat(p0 + p1)

assert main:
  IO(Unit)

def main():
  IO.print(String.append(Nat.show(main.out()), "n"))
$$ bend %
9n
$$ bend % --seq
9n
exit 0
$$ bend % --par
9n
exit 0
$$ bend % --js
9n
exit 0
