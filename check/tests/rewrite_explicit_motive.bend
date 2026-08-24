# %x@e : P is the explicit-motive rewrite (the J axiom): the motive
# binds _ (the second endpoint) and x (the equation); the body follows
# on its own line or the same one.
# ported from bend3: the real-lambda motive `x => P` becomes bend4's
# _-bound motive term, S/Z ride the test's own N
import Base

type N:
  Z{}
  S{p: N}

assert pred:
  forall n: N
  N

def pred(n):
  match n:
    case Z{}:
      Z{}
    case S{p}:
      p

assert succ_inj:
  forall a: N
  forall b: N
  forall e: {S{a} == S{b} : N}
  {a == b : N}

def succ_inj(a, b, e):
  %x@e : {pred(S{a}) == pred(_) : N}
  {==}

assert sym:
  @-x:N -> @-y:N -> {x == y : N} -> {y == x : N}

def sym(): x => y => e => %h@e : {_ == x : N}; {==}

assert main.out:
  Nat

def main.out(): 0n

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
