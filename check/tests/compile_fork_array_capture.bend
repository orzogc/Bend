# an array living across a fork
# ported from bend3: the 2-slot [:U32] literal becomes an explicit tree,
# the fork a Both{..} pair, the work counter a Nat
import Base

assert work:
  forall +n: +Nat
  U32

def work(n):
  match n:
    case 0n:
      1
    case 1n+p:
      U32.add(U32.add(1, U32.from_nat(p)), work(p))

assert f:
  forall a: Array<U32>
  U32

def f(a):
  (a2, x) = Array.get(a, 0)
  Both{r1, r2} = {Both{work(U32.to_nat(x)), work(7n)} : Par<U32, U32>}
  (a3, y) = Array.get(a2, 1)
  U32.add(U32.add(r1, r2), y)

assert main.out:
  U32

def main.out():
  f(ANode{ALeaf{4}, ALeaf{9}})

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
49
$$ bend % --seq
49
exit 0
$$ bend % --par
49
exit 0
$$ bend % --js
49
exit 0
