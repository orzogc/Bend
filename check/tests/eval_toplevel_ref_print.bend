# a top-level ref as main's value prints as the bare name: snf keeps
# an unapplied def closed.
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
  id
$$ bend %
id
