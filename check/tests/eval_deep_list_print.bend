# a result deeper than the host stack must still normalize and print:
# bend3 pinned a 4000-deep list through term_snf/term_show; here the
# Nat show sugar must walk a 131072-deep Succ chain to its digits, on
# every lane (the C digit printer and the JS readback included).
# ported from bend3: List(U32) zeros(4000) becomes Nat.pow2(17n) --
# bend4 has no list literal, and the closed-chain digit render pins the
# same deep, non-overflowing walk
import Base

assert Nat.pow2:
  forall n: Nat
  Nat

def Nat.pow2(n):
  match n:
    case 0n:
      1n
    case 1n+p:
      Nat.double(Nat.pow2(p))

assert main.out:
  Nat

def main.out():
  Nat.pow2(17n)

assert main:
  IO(Unit)

def main():
  IO.print(String.append(Nat.show(main.out()), "n"))
$$ bend %
131072n
$$ bend % --seq
131072n
exit 0
$$ bend % --par
131072n
exit 0
$$ bend % --js
131072n
exit 0
