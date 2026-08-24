# bend3's zero-semantics mark: f!(x) is f(x) to checker and evaluator,
# and marks in a parallel let ride as plain calls. bend4's bang
# carries the same law through its typed fork-let; the generic
# pick!(x, y) half is gone with def<A> (ruled out, collides with
# infix <). Countdowns ride +Nat (the fork re-uses its pred;
# Nat.copy owns the copy), f's pred re-use a U32 mirror
import Base

assert f:
  forall n: Nat
  forall i: U32
  U32

def f(n, i):
  match n:
    case Zero{}:
      1
    case Succ{k}:
      ((i1, d1), (i2, d2)) = U32.copy(i)
      f(k, i1 - 1) + i2

assert g:
  forall +d: +Nat
  U32

def g(d):
  match d:
    case Zero{}:
      f(3n, 3)
    case Succ{k}:
      & a : U32 = g!(k) & b : U32 = g(k);
      a + b

assert main.out:
  Nat

def main.out():
  U32.to_nat(g(2n))

assert main:
  IO(Unit)

def main():
  IO.print(String.append(Nat.show(main.out()), "n"))
$$ bend %
28n
$$ bend % --seq
28n
exit 0
$$ bend % --par
28n
exit 0
$$ bend % --js
28n
exit 0
