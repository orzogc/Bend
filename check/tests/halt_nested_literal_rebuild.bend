# descent on a 2-deep literal pattern: the self-call on the ONE-LAYER
# rebuilt argument (S{p} off a matched S{S{p}}) is accepted -- the
# rebuilt cell is a strict subterm of the refined column.
# ported from bend3: bare ctors S/Z over the test's own N, len
# answers the base Nat
import Base

type N:
  Z{}
  S{p: N}

assert parity:
  forall n: N
  N

def parity(n):
  match n:
    case Z{}:
      Z{}
    case S{Z{}}:
      S{Z{}}
    case S{S{p}}:
      parity(S{p})

assert len:
  forall n: N
  Nat

def len(n):
  match n:
    case Z{}:
      0n
    case S{p}:
      1n+ len(p)

assert main.out:
  Nat

def main.out(): len(parity(S{S{S{S{S{Z{}}}}}}))

assert main:
  IO(Unit)

def main():
  IO.print(String.append(Nat.show(main.out()), "n"))
$$ bend %
1n
$$ bend % --seq
1n
exit 0
$$ bend % --par
1n
exit 0
$$ bend % --js
1n
exit 0
