# Parallel sum -- the laws. Claims about the fork/join tree: it computes
# the same as the sequential loop seq over the 2^d numbers from i, and
# it has exactly 2^d leaves (starting one number later adds one per
# leaf). PROOF.bend must prove every one, by induction on the depth.
import Base
import ./main.bend as Par

# LAW: the parallel tree equals its sequential meaning: the tree of
# depth d at i is the loop that adds i, i + 1, .., i + 2^d - 1 one by
# one, for any d and i.
law tree_is_seq:
  for +d: Nat
  for +i: Nat
  {Par.sum_nat(d, i) == Par.seq(Par.pow2(d), i) : Nat}

# LAW: the tree has 2^d leaves: starting one number later adds 2^d to
# the sum, one per leaf, for any d and i (stated with the shifted tree
# on the right, the side a rewrite eliminates).
law tree_leaves:
  for +d: Nat
  for +i: Nat
  {Par.add(Par.sum_nat(d, i), Par.pow2(d)) == Par.sum_nat(d, 1n+i) : Nat}

# LAW: the U32 instance main runs computes the same numbers: depth 4
# at 0 is 0 + 1 + .. + 15 = 120 (closed, by evaluation).
law sum_span:
  {Par.sum(4n, 0) == 120 : U32}
