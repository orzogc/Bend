# regression witness (90c7d14, respelled at 8d15057's request): the
# machine word has no structural view -- a direct U32 constructor match
# in USER code opens the Word(32n) field, which the C emission holds as
# an immediate, so tocl refuses loud. The witness no longer rides
# U32.copy: that spelling becomes an emission intrinsic, and this pin
# must survive it. The evaluator and the JS backend answer 14.
import Base

assert main.out:
  U32

def main.out():
  match U32.add(7, 7):
    case U32{w}:
      U32{w}

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
14
$$ bend % --seq
Error: a structural view of a machine word
exit 1
$$ bend % --js
14
exit 0
