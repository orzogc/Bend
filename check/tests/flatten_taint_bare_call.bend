# bend3's stale-taint bare-call variant (mid's recursion dies inside
# its own unfold); bend4 has no taint bits to go stale, so the sibling
# shape carries end to end -- the countdown on a Nat mirror, mid as a
# plain pure binding in the fork: 10
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

assert mid:
  forall x: U32
  U32

def mid(x):
  hf(y => 5, x) + 1

assert main.out:
  Nat

def main.out():
  & p0 : U32 = tl(10n, 10, 3) & p1 : U32 = mid(7);
  U32.to_nat(p0 + p1)

assert main:
  IO(Unit)

def main():
  IO.print(String.append(Nat.show(main.out()), "n"))
$$ bend %
10n
$$ bend % --seq
10n
exit 0
$$ bend % --par
10n
exit 0
$$ bend % --js
10n
exit 0
