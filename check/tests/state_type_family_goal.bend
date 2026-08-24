# Vec (type-family) ladder, state 0: the INDEX renders inside the
# stuck family application -- Vec(Nat.add(n, 0n)), the ref cut, never
# the family's unfolded match
import Base

assert Vec:
  forall n: Nat
  Type

def Vec(n):
  match n:
    case 0n:
      Unit
    case 1n+p:
      Nat & Vec(p)

assert vpad:
  forall n: Nat
  forall v: Vec(n)
  Vec(Nat.add(n, 0n))

def vpad(n, v):
  v

$$ bend %
Error:
- expected : Vec(Nat.add(n, 0n))
- observed : Vec(n)
Context:
- n : Nat
- v : Vec(n)
Location: vpad