# the plain ternary select coverage, GOAL 1.4: a two-arm Bool match
# whose arms are allocation-free words (pick's own parameters) is
# if-converted to one eager C ternary -- no branch, both arms
# computed. adiff evaluates both subtractions and selects the
# non-wrapping one, so a branchy emission would still answer 198 but
# the csrc pin holds the select shape itself.
# csrc has: != 0 ? x_0 : y_0);
import Base

assert b2u:
  forall b: Bool
  U32

def b2u(b):
  match b:
    case False{}: 0
    case True{}: 1

assert pick:
  forall t: U32
  forall x: U32
  forall y: U32
  U32

def pick(t, x, y):
  match U32.is_zero(t):
    case True{}:
      x
    case False{}:
      y

assert adiff:
  forall +a: +U32
  forall +b: +U32
  U32

def adiff(a, b):
  pick(b2u(U32.is_lt(a, b)), U32.sub(a, b), U32.sub(b, a))

assert wob:
  forall +i: +Nat
  U32

def wob(i):
  match i:
    case 0n:
      0
    case 1n+p:
      a = U32.mod(U32.from_nat(p), 13)
      b = U32.mod(U32.from_nat(p), 7)
      U32.add(adiff(a, b), wob(p))

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(wob(50n)))
$$ bend %
198
$$ bend % --seq
198
exit 0
$$ bend % --par
198
exit 0
$$ bend % --js
198
exit 0
