# the full-adder kit: sum(1,1,0) drops, carry(1,1,0) carries; encoded
# sum + 10*carry = 10, bend3's golden.
# ported from bend3: the Bit module becomes base Bool.full_add (a
# (Bool & Bool) tuple), Bit.to_u32 becomes a local Bool match
import Base

assert b2u:
  forall b: Bool
  U32

def b2u(b):
  match b:
    case False{}:
      0
    case True{}:
      1

assert main.out:
  U32

def main.out():
  match Bool.full_add(True{}, True{}, False{}):
    case (s, k):
      U32.add(b2u(s), U32.mul(b2u(k), 10))

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
10
$$ bend % --seq
10
exit 0
$$ bend % --par
10
exit 0
$$ bend % --js
10
exit 0
