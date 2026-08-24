# eta-short body under an erased param: the alias def is a bare Ref at a
# forall type with an erased binder, and the spine must keep the erased
# position
# ported from bend3
import Base

assert id:
  forall -a: Type
  forall x: a
  a

def id(a, x):
  x

assert same:
  @-a: Type -> @x: a -> a

def same():
  id

assert main.out:
  U32

def main.out():
  same(U32, 21)

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
21
$$ bend % --seq
21
exit 0
$$ bend % --par
21
exit 0
$$ bend % --js
21
exit 0
