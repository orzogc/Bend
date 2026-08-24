# list literal sugar: [a,b,c] is Con/Nil, in terms and patterns --
# ported from bend3; literals sit in checked positions (bend4 infers
# no ctor), and the readback folds to one U32 (a List is not
# C-showable)
import Base

assert rev:
  forall xs: List<U32>
  forall acc: List<U32>
  List<U32>

def rev(xs, acc):
  match xs:
    case Con{h, t}:
      rev(t, h <> acc)
    case Nil{}:
      acc

assert csum:
  forall xs: List<U32>
  forall acc: U32
  U32

def csum(xs, acc):
  match xs:
    case Con{h, t}:
      csum(t, 10 * acc + h)
    case Nil{}:
      acc

assert main.out:
  U32

def main.out():
  csum(rev([1, 2 + 3, 3], [0]), 0)

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
3510
$$ bend % --seq
3510
exit 0
$$ bend % --par
3510
exit 0
$$ bend % --js
3510
exit 0
