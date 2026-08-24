# an array read is an ordinary term: it takes an ascription like any
# other (bend3 pinned annotation placement on its slab reads)
import Base

assert main.out:
  U32

def main.out():
  (a2, x) = {Array.new(1n, 4)[0] : Array<U32> & U32}
  x

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
4
$$ bend % --seq
4
exit 0
$$ bend % --js
4
exit 0
