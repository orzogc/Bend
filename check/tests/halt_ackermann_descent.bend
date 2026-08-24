# Ackermann: lexicographic column descent -- the first column shrinks,
# or stays while the second shrinks. bend4's descent law accepts both
# self-calls (col0 LT, or col0 EQ then col1 LT); the inner
# ack(1n+ m, n) spends m beside the outer call's m, and the +Nat (Cop)
# binder licenses that copy -- so the file checks strict and pins the
# runtime.
# ported from bend3: U32 becomes Nat, the doubled m a +Nat binder
import Base

assert ack:
  forall +m: +Nat
  forall n: Nat
  Nat

def ack(m, n):
  match m:
    case 0n:
      1n+ n
    case 1n+p:
      match n:
        case 0n:
          ack(p, 1n)
        case 1n+q:
          ack(p, ack(1n+ p, q))

assert main.out:
  Nat

def main.out(): ack(2n, 2n)

assert main:
  IO(Unit)

def main():
  IO.print(String.append(Nat.show(main.out()), "n"))
$$ bend %
7n
$$ bend % --seq
7n
exit 0
$$ bend % --par
7n
exit 0
$$ bend % --js
7n
exit 0
