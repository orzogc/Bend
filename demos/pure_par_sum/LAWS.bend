# Parallel sum -- the laws. Claims about sum(d, i), the fork/join tree
# that adds the 2^d numbers from i: a leaf is its number; a node is the
# sum of its two halves, the right half starting 2^d numbers later; and
# a closed tree adds the numbers it spans. PROOF.bend must prove every one.
import Base
import ./main.bend as Par

# LAW: a leaf is its number: the tree of depth 0 at i sums to i, for
# any i.
law sum_leaf:
  for +i: U32
  {Par.sum(0n, i) == i : U32}

# LAW: a fork joins as the sum of its halves: the tree of depth d + 1 at
# i is the tree of depth d at i plus the tree of depth d at i + 2^d, for
# any d and i (the fork/join equals the two halves added).
law sum_split:
  for +d: Nat
  for +i: U32
  {Par.sum(1n+d, i) == (Par.sum(d, i) + Par.sum(d, (i + U32.shln(1, d) : U32)) : U32) : U32}

# LAW: a closed tree adds the numbers it spans: depth 4 at 0 is
# 0 + 1 + .. + 15 = 120, and depth 3 at 5 is 5 + 6 + .. + 12, added one
# by one.
law sum_span:
  {Par.sum(4n, 0) == 120 : U32}
  & {Par.sum(3n, 5) == (5 + 6 + 7 + 8 + 9 + 10 + 11 + 12 : U32) : U32}
