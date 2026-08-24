# error census: a Type VALUE consumed at a runtime position survives
# the checker (types are inert) and dies at compile erasure; the
# interpreter shows the value (as its Word chain)
import Base
assert id0:
  forall A: Type
  forall x: U32
  U32

def id0(A, x):
  x

assert main.out:
  U32

def main.out(): id0(U32, 3)

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
3
$$ bend % --seq
Error: tocl: an under-applied def value: U32 (report this case)
exit 1
