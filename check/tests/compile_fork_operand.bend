# fork members that are not bare calls (ops over recursive calls)
# ported from bend3: the counter walks a Nat, the fork a Both{..} pair,
# the shared argument a +param
import Base

assert f:
  forall +n: +Nat
  U32

def f(n):
  match n:
    case 0n:
      1
    case 1n+p:
      U32.add(f(p), U32.add(1, U32.from_nat(p)))

assert g:
  forall +x: +Nat
  U32

def g(x):
  Both{a, b} = {Both{U32.add(f(x), 1), U32.mul(f(x), 2)} : Par<U32, U32>}
  U32.add(a, b)

assert main.out:
  U32

def main.out():
  g(10n)

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
169
$$ bend % --seq
169
exit 0
$$ bend % --par
169
exit 0
$$ bend % --js
169
exit 0
