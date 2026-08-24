# && and || are Bool operators desugaring to Bool.and/Bool.or -- both
# operands are values (strict, as bend3 pinned), and the operands are
# Bool, not words (no U32-Bool bridge in bend4)
import Base

assert bu:
  forall b: Bool
  U32

def bu(b):
  if b: 1 else: 0

assert main.out:
  U32

def main.out():
  a = bu(True{} && True{})
  b = bu(True{} && False{})
  c = bu(False{} || True{})
  d = bu(False{} || False{})
  a + 10 * b + 100 * c + 1000 * d

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
101
$$ bend % --seq
101
exit 0
$$ bend % --par
101
exit 0
$$ bend % --js
101
exit 0
