# zero-arg def referencing a recursive (forked) def, used as a bare value
# ported from bend3: counters walk Nats, forks become Both{..} pairs
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
      Both{l, r} = {Both{gen(p, U32.mul(i, 2)), gen(p, U32.add(U32.mul(i, 2), 1))} : Par<Tr, Tr>}
      Nd{l, r}

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

assert t:
  Tr

def t():
  gen(5n, 0)

assert main.out:
  U32

def main.out():
  sum(t)

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
496
$$ bend % --seq
496
exit 0
$$ bend % --par
496
exit 0
$$ bend % --js
496
exit 0
