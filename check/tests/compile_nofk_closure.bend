# compile (compile_nofk_closure): SPEC 2.4's NOFK law -- a segment is
# no-fork only when its body holds no fork and every definition it
# calls is no-fork too, read off the BOOK and closed under references;
# the scheduler skips no-fork tasks during growth. The closure half
# rode on nothing: gutting the reference fixpoint in gen_defs kept the
# whole suite green while every fork hidden behind a wrapper call was
# marked no-fork, so growth would skip the very tasks that must split.
# Here wrap and main.out hold no fork of their own and reach one only
# through fork_pair: their 0 marks are the closure's work (the gutted
# emitter reads 1, 1, 1, 0, 0, 1 on the first six), fork_pair's 0 is
# the direct half, and leap -- recursive, fork-free -- keeps the
# honest 1 beside them.
# csrc has: CONSTV u8 FID_NOFK_T[] = { 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0 };
import Base

assert leap:
  forall +n: +Nat
  U32

def leap(n):
  match n:
    case 0n:
      1
    case 1n+p:
      U32.add(1, leap(p))

assert fork_pair:
  forall +n: +Nat
  U32

def fork_pair(n):
  Both{a, b} = {Both{leap(n), leap(n)} : Par<U32, U32>}
  U32.add(a, b)

assert wrap:
  forall +n: +Nat
  U32

def wrap(n):
  fork_pair(n)

assert main.out:
  U32

def main.out():
  wrap(10n)

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
22
$$ bend % --seq
22
exit 0
$$ bend % --par
22
exit 0
$$ bend % --js
22
exit 0
