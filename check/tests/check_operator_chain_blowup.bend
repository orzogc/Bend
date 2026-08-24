# bend3's width-16 left-nested chain guarded the checker's exponential
# Op2 arm by interaction count; bend4 has no --stats, so the guard
# keeps its half that still speaks: the chain checks and answers on
# every lane through the infix ladder
import Base

assert f:
  forall x0: U32
  forall x1: U32
  forall x2: U32
  forall x3: U32
  forall x4: U32
  forall x5: U32
  forall x6: U32
  forall x7: U32
  forall x8: U32
  forall x9: U32
  forall xa: U32
  forall xb: U32
  forall xc: U32
  forall xd: U32
  forall xe: U32
  forall xf: U32
  U32

def f(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, xa, xb, xc, xd, xe, xf):
  (((((((((((((((x0 + x1) + x2) + x3) + x4) + x5) + x6) + x7) + x8) + x9) + xa) + xb) + xc) + xd) + xe) + xf)

assert main.out:
  Nat

def main.out():
  U32.to_nat(f(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15))

assert main:
  IO(Unit)

def main():
  IO.print(String.append(Nat.show(main.out()), "n"))
$$ bend %
120n
$$ bend % --seq
120n
exit 0
$$ bend % --par
120n
exit 0
$$ bend % --js
120n
exit 0
