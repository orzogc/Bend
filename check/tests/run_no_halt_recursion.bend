#[halts]
# runtime mutual recursion: the even/odd pair and a rose-tree pair
# (rsum/fsum), interpreted AND compiled
# ported from bend3: `--no-halt` becomes #[halts] (bend4's spelling of
# the same permission), counters become Nat
import Base

type Forest<A: Type>:
  FN{}
  FC{h: A, t: Forest<A>}

type Rose:
  R1{v: U32, kids: Forest<Rose>}

assert even:
  forall n: Nat
  U32

def even(n):
  match n:
    case 0n:
      1
    case 1n+p:
      odd(p)

assert odd:
  forall n: Nat
  U32

def odd(n):
  match n:
    case 0n:
      0
    case 1n+p:
      even(p)

assert rsum:
  forall r: Rose
  U32

def rsum(r):
  match r:
    case R1{v, kids}:
      U32.add(v, fsum(kids))

assert fsum:
  forall f: Forest<Rose>
  U32

def fsum(f):
  match f:
    case FN{}:
      0
    case FC{h, t}:
      U32.add(rsum(h), fsum(t))

assert main.out:
  U32

def main.out():
  t = {R1{1, FC{R1{2, FN{}}, FC{R1{3, FC{R1{4, FN{}}, FN{}}}, FN{}}}} : Rose}
  U32.add(U32.add(U32.mul(even(10n), 1000), U32.mul(odd(7n), 100)), rsum(t))

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
1110
$$ bend % --seq
1110
exit 0
$$ bend % --par
1110
exit 0
$$ bend % --js
1110
exit 0
