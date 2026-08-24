# bend3's pin: a goal reduced through a checked def must meet the
# rewrite motive in ONE stuck spelling (parsed-vs-elaborated bodies
# once stranded two); bend4 stores one elaborated body by design and
# refolds a stuck computed match to its ref, so both sides speak
# hgo(n) and the motive lands (the lemma states the eliminated term
# on the right)
import Base

assert Nat.is_eq:
  forall a: Nat
  forall b: Nat
  Bool

def Nat.is_eq(a, b):
  Cmp.is_eq(Nat.cmp(a, b))

assert hgo:
  forall n: Nat
  Nat

def hgo(n):
  match Nat.is_eq(n, 0n):
    case True{}:
      0n
    case False{}:
      1n

assert thv:
  forall n: Nat
  forall e: {0n == hgo(n) : Nat}
  {Succ{hgo(n)} == 1n : Nat}

def thv(n, e):
  %e : {Succ{_} == 1n : Nat}
  {==}

assert main.out:
  Nat

def main.out():
  0n

assert main:
  IO(Unit)

def main():
  IO.print(String.append(Nat.show(main.out()), "n"))
$$ bend %
0n
$$ bend % --seq
0n
exit 0
$$ bend % --par
0n
exit 0
$$ bend % --js
0n
exit 0
