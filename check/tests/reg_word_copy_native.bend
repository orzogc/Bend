# the sharing-and-ordering leaves of base's text surface, distilled:
# one copied word and one three-way comparison
import Base

assert main.out:
  U32

def main.out():
  ((a, e1), (b, e2)) = U32.copy(21)
  match U32.cmp(a, 22):
    case LT{}:
      U32.add(b, 1)
    case EQ{}:
      0
    case GT{}:
      1

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
22
$$ bend % --seq
22
exit 0
$$ bend % --par
22
exit 0
$$ bend % --js
22
exit 0
