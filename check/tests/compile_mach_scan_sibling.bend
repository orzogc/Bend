# mixed fork, calm sibling first: a leaf forking a discard-only callee
# beside a recursive self call must still loop, not respin
# ported from bend3: counters walk Nats, the fork a Both{..} pair
import Base

type Tr:
  Lf{v: U32}
  Nd{h: U32, l: Tr, r: Tr}

assert gen:
  forall +d: +Nat
  forall +s: +U32
  Tr

def gen(d, s):
  match d:
    case 0n:
      Lf{s}
    case 1n+p:
      Nd{U32.mul(s, 2654435761), gen(p, U32.add(U32.mul(s, 1664525), 1)), gen(p, U32.add(U32.mul(s, 214013), 3))}

assert burncalm:
  forall t: Tr
  U32

def burncalm(t):
  7

assert walk:
  forall t: Tr
  forall acc: U32
  U32

def walk(t, acc):
  match t:
    case Lf{v}:
      U32.add(acc, v)
    case Nd{h, l, r}:
      Both{a, b} = {Both{burncalm(r), walk(l, U32.add(acc, h))} : Par<U32, U32>}
      U32.add(a, b)

assert main.out:
  U32

def main.out():
  walk(gen(8n, 3), 0)

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
356721367
$$ bend % --seq
356721367
exit 0
$$ bend % --par
356721367
exit 0
$$ bend % --js
356721367
exit 0
