# the numeric-loop dead residue, on Nat: the base arm destructures a
# tuple whose only ctor's residue is dead and elided, and the loop
# answers bend3's 281 -- the `case 1+n` countdown becomes a Nat match
# with a U32 mirror argument, and every contracted word binder of the
# original rides U32.copy (words are affine here; the copies keep
# bend3's arithmetic exactly)
import Base

assert step:
  forall p: U32 & U32
  U32 & U32

def step(p):
  (a, b) = p
  ((a1, e1), (a2, e2)) = U32.copy(a)
  (a1 + b, a2 + 1)

assert go:
  forall n: Nat
  forall i: U32
  forall p: U32 & U32
  forall acc: U32
  U32

def go(n, i, p, acc):
  match n:
    case Zero{}:
      (x, y) = p
      acc + x * 10 + y
    case Succ{k}:
      ((i1, d1), (i2, d2)) = U32.copy(i)
      go(k, i1 - 1, step(p), acc + i2)

assert main.out:
  Nat

def main.out():
  U32.to_nat(go(5n, 5, (1, 2), 0))

assert main:
  IO(Unit)

def main():
  IO.print(String.append(Nat.show(main.out()), "n"))
$$ bend %
281n
$$ bend % --seq
281n
exit 0
$$ bend % --par
281n
exit 0
$$ bend % --js
281n
exit 0
