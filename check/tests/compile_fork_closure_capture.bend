# closures crossing a parallel fork + capture of matched fields
# ported from bend3: counters walk Nats, forks become Both{..} pairs
import Base

type Bx:
  MkBx{v: U32}

assert step:
  forall +n: +Nat
  forall k: U32 -> U32
  U32

def step(n, k):
  match n:
    case 0n:
      k(1)
    case 1n+p:
      step(p, r => k(U32.add(r, U32.add(1, U32.from_nat(p)))))

assert par2:
  forall +n: +Nat
  U32

def par2(n):
  match n:
    case 0n:
      1
    case 1n+p:
      Both{a, b} = {Both{par2(p), step(1n+p, x => x)} : Par<U32, U32>}
      U32.add(a, U32.mul(31, b))

assert grab:
  forall b: Bx
  U32 -> U32

def grab(b):
  match b:
    case MkBx{v}:
      x => U32.add(x, v)

assert main.out:
  U32

def main.out():
  f = grab(MkBx{100})
  U32.add(par2(6n), f(par2(5n)))

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
3264
$$ bend % --seq
3264
exit 0
$$ bend % --par
3264
exit 0
$$ bend % --js
3264
exit 0
