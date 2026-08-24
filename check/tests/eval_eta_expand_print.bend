# an eta-expanded wrapper prints as written: x => id(x) does not
# collapse to the bare ref (conversion is up to eta, printing is not).
# ported from bend3: the U32-Nat type moves to base Nat
import Base

assert id:
  forall n: Nat
  Nat

def id(n):
  match n:
    case 0n:
      0n
    case 1n+p:
      Succ{id(p)}

assert main:
  @n:Nat -> Nat

def main():
  x => id(x)
$$ bend %
x => id(x)
