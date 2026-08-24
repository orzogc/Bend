# erased arg on a recursive def
# ported from bend3: the counter walks a Nat
import Base

type BoxR<-T: Type>:
  MkBoxR{v: T}

assert rep:
  forall -T: Type
  forall n: Nat
  forall b: BoxR<T>
  BoxR<T>

def rep(T, n, b):
  match n:
    case 0n:
      b
    case 1n+p:
      rep(T, p, b)

assert get:
  forall -T: Type
  forall b: BoxR<T>
  T

def get(T, b):
  match b:
    case MkBoxR{v}:
      v

assert main.out:
  U32

def main.out():
  get(U32, rep(U32, 5n, MkBoxR{9}))

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
