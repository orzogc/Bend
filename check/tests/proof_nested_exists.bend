# TWO exists clauses nest sigmas, and the fill's witness is the
# right-nested tuple -- (1n, 2n, {==}) is (1n, (2n, {==})).
# ported from bend3: Nat witnesses replace U32 so the printed value
# stays literal; main spells the folded sigma type and returns the fill
import Base

assert two_wit:
  exists a: Nat
  exists b: Nat
  {Nat.add(a, b) == 3n : Nat}

def two_wit():
  (1n, 2n, {==})

assert main:
  Sigma<Nat, a => Sigma<Nat, b => {Nat.add(a, b) == 3n : Nat}>>

def main(): two_wit()

$$ bend %
Tuple{1n, Tuple{2n, {==}}}
