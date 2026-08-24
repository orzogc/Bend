# an array flowing through a dynamically-applied closure must compile on
# every backend (bend3 pinned its prep unk-shape guard; the behavior is
# the dialect-neutral part)
# ported from bend3: [:U32] literals become Base Array trees (Array.new),
# @-swaps become Array.swap/Array.get
import Base

assert app:
  forall f: Array<U32> -> Array<U32>
  forall a: Array<U32>
  Array<U32>

def app(f, a):
  f(a)

assert poke:
  forall a: Array<U32>
  Array<U32>

def poke(a):
  (a2, old) = Array.swap(U32, a, 0, 9)
  a2

assert main.out:
  U32

def main.out():
  (h3, x) = Array.get(app(poke, Array.new(0n, 1)), 0)
  x

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
9
$$ bend % --seq
9
exit 0
$$ bend % --par
9
exit 0
$$ bend % --js
9
exit 0
