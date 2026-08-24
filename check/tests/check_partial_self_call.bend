# a live self-call is a whole call: one argument per parameter, inside
# the def's own case tree. a partial self-call bound as a value must
# refuse -- descent compares one argument per lhs column, so a short
# spine has nothing to stand on. gutted, this program checks and runs.
import Base

assert part:
  forall a: Nat
  forall b: Nat
  Nat

def part(a, b):
  match a:
    case 0n:
      b
    case 1n+p:
      g = part(p)
      g(b)

assert main:
  Nat

def main(): part(2n, 1n)
$$ bend %
Error:
- expected : a whole self-call (one argument per parameter, inside the case tree)
- observed : part(p)
Context:
- p : Nat
- b : Nat
Location: part
16 |     case 1n+p:
17>|       g = part(p)
18 |       g(b)
