# recursive def whose tail builds a ctor from two recursive calls, and a
# forked consumer
# ported from bend3: counters walk Nats, the fork becomes a Both{..} pair
import Base

type Tr:
  Lf{v: U32}
  Nd{a: Tr, b: Tr}

assert gen:
  forall +d: +Nat
  forall +i: +U32
  Tr

def gen(d, i):
  match d:
    case 0n:
      Lf{i}
    case 1n+p:
      Nd{gen(p, U32.mul(i, 2)), gen(p, U32.add(U32.mul(i, 2), 1))}

assert sum:
  forall t: Tr
  U32

def sum(t):
  match t:
    case Lf{v}:
      v
    case Nd{a, b}:
      Both{x, y} = {Both{sum(a), sum(b)} : Par<U32, U32>}
      U32.add(x, y)

assert main.out:
  U32

def main.out():
  sum(gen(6n, 0))

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
2016
$$ bend % --seq
2016
exit 0
$$ bend % --par
2016
exit 0
$$ bend % --js
2016
exit 0
