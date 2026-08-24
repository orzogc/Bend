# a dropped closure whose capture is an array: the drop must collect the
# captured tree (bend3 pinned its slab drop walk; the capture-drop is
# the dialect-neutral part)
# ported from bend3: the 2^17-slot slab becomes a 16-leaf Base Array
import Base

assert foo:
  forall a: Array<U32>
  forall x: U32
  U32

def foo(a, x):
  (a2, v) = Array.get(a, 12)
  U32.add(v, x)

assert main.out:
  U32

def main.out():
  g = foo(Array.new(4n, 7))
  5

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
5
$$ bend % --seq
5
exit 0
$$ bend % --par
5
exit 0
$$ bend % --js
5
exit 0
