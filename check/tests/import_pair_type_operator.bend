# A & B is core grammar (Pair via Sigma), gated on nothing but the
# name -- with Base it is Pair(A, B) (bend3 gated the bare & on
# `import Pair`)
import Base

assert main.out:
  U32

def main.out():
  (a, b) = {(3, 4) : U32 & U32}
  a * 10 + b

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
34
$$ bend % --seq
34
exit 0
$$ bend % --js
34
exit 0
