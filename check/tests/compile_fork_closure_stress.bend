# closure stress: capturing continuation chains (CPS) under a parallel
# fork tree; closures dispatch native mixers and recursive defs alike
# through the dynamic apply
# ported from bend3: shifts spell U32.shrn, shares become +binders,
# counters walk Nats, forks become Both{..} pairs
import Base

type Bx:
  MkBx{v: U32}

assert mix:
  forall +a: +U32
  U32

def mix(a):
  +b = {U32.mul(U32.xor(a, U32.shrn(16n, a)), 2246822519) : +U32}
  +c = {U32.mul(U32.xor(b, U32.shrn(13n, b)), 3266489917) : +U32}
  U32.xor(c, U32.shrn(16n, c))

assert open2:
  forall b: Bx
  U32

def open2(b):
  match b:
    case MkBx{v}:
      v

assert boxer:
  (U32 -> Bx) -> U32 -> U32

def boxer():
  f => x => open2(f(x))

assert cps:
  forall +n: +Nat
  forall k: U32 -> U32
  U32

def cps(n, k):
  match n:
    case 0n:
      k(1)
    case 1n+p:
      cps(p, r => k(mix(U32.add(r, U32.add(1, U32.from_nat(p))))))

assert leaf:
  forall +i: +U32
  U32

def leaf(i):
  U32.add(cps(U32.to_nat(U32.mod(i, 13)), x => U32.add(x, i)), boxer(x => MkBx{U32.add(x, 7)}, i))

assert tree:
  forall +d: +Nat
  forall +i: +U32
  U32

def tree(d, i):
  match d:
    case 0n:
      leaf(i)
    case 1n+p:
      Both{l, r} = {Both{tree(p, U32.mul(i, 2)), tree(p, U32.add(U32.mul(i, 2), 1))} : Par<U32, U32>}
      U32.add(l, r)

assert main.out:
  U32

def main.out():
  tree(2n, 0)

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
2298769217
$$ bend % --seq
2298769217
exit 0
$$ bend % --par
2298769217
exit 0
$$ bend % --js
2298769217
exit 0
