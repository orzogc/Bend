# computed (with) matches at runtime: dispatch on a call's result, nested
# computed scrutinees, and a value column beside a pattern column
# ported from bend3: U32 comparisons become Bool matches, compared
# words +U32 (Cop) binders
import Base

type Ord:
  Lt{}
  Eq{}
  Gt{}

assert cmp:
  forall +a: +U32
  forall +b: +U32
  Ord

def cmp(a, b):
  match U32.is_lt(a, b):
    case True{}:
      Lt{}
    case False{}:
      match U32.is_eq(a, b):
        case True{}:
          Eq{}
        case False{}:
          Gt{}

assert rank:
  forall a: U32
  forall b: U32
  U32

def rank(a, b):
  match cmp(a, b):
    case Lt{}:
      1
    case Eq{}:
      2
    case Gt{}:
      3

assert main.out:
  U32

def main.out():
  U32.add(U32.add(U32.mul(rank(1, 5), 100), U32.mul(rank(4, 4), 10)), rank(9, 2))

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
123
$$ bend % --seq
123
exit 0
$$ bend % --par
123
exit 0
$$ bend % --js
123
exit 0
