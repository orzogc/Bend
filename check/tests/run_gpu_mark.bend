# the GPU mark f!(x) has zero semantic content: interpreter and CPU-only
# compiled code treat it exactly as f(x)
# ported from bend3: depth becomes Nat, the fork a Par<> Both destructure
import Base

assert gmark:
  forall +d: +Nat
  U32

def gmark(d):
  match d:
    case 0n:
      3
    case 1n+p:
      Both{a, b} = {Both{gmark(p), gmark(p)} : Par<U32, U32>}
      U32.add(a, b)

assert main.out:
  U32

def main.out():
  x = gmark!(2n)
  y = gmark(2n)
  U32.add(U32.mul(x, 100), y)

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
1212
$$ bend % --seq
1212
exit 0
$$ bend % --par
1212
exit 0
$$ bend % --js
1212
exit 0
