# SPEC PART 3 COP: cop_goal peels Cop by weak-head normalization,
# which terminates -- a nested Cop goal at a dead
# position converts to its carrier and the check completes, so an
# expensive goal slows but never hangs the checker
import Base

assert twice:
  forall +x: + (+ Nat ~ Nat.copy) ~ Nat.copy
  Nat

def twice(x):
  Nat.add(x, x)

assert main:
  Nat

def main():
  twice(3n)
$$ bend %
6n
