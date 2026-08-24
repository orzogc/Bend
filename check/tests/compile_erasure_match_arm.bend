# runtime erasure at a binderless lambda-match arm: the erased ctor
# field rides into the arm head and drops against the callee's erased
# param
# ported from bend3: the spin counter walks a Nat, its U32 image rebuilt
import Base

type Ev:
  MkEv{-t: U32, v: Nat}

assert spinr:
  forall +n: +Nat
  forall acc: U32
  U32

def spinr(n, acc):
  match n:
    case 0n:
      acc
    case 1n+p:
      spinr(p, U32.add(acc, U32.add(1, U32.from_nat(p))))

assert uset:
  forall -t: U32
  forall v: Nat
  U32

def uset(t, v):
  spinr(v, 1)

assert f:
  Ev -> U32

def f():
  \{MkEv: uset}

assert main.out:
  U32

def main.out():
  U32.add(f(MkEv{7, 3n}), f(MkEv{1, 2n}))

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
11
$$ bend % --seq
11
exit 0
$$ bend % --par
11
exit 0
$$ bend % --js
11
exit 0
