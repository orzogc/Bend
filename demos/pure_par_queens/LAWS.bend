# Parallel N-queens -- the laws. Claims about the search: every board
# the fork tree returns is safe (no two queens attack each other), so
# every solution counted is one; and the fork tree computes the same
# boards as the flat loop over the first row's columns, so the
# parallel search has its sequential meaning. PROOF.bend must prove
# every one. A Bool fact is stated with True{} on the left, the side a
# rewrite keeps.
import Base
import ./main.bend as Q

# LAW: the search is sound: every board the fork tree of any depth
# returns, from any first column, for any rows left and any board
# size, is safe.
law fork_safe:
  for +d: Nat
  for +i: Nat
  for +r: Nat
  for +n: Nat
  {True{} == Q.all_safe(Q.fork(d, i, r, n)) : Bool}

# LAW: every solution of the n x n board is safe, for any n and any
# fork depth d.
law boards_safe:
  for  n: Nat
  for +d: Nat
  {True{} == Q.all_safe(Q.boards(n, d)) : Bool}

# LAW: the parallel tree equals its sequential meaning: the fork tree
# of depth d from column i returns the boards of the flat loop over
# the 2^d columns i, i + 1, .., i + 2^d - 1, in order.
law fork_is_flat:
  for +d: Nat
  for +i: Nat
  for +r: Nat
  for +n: Nat
  {Q.fork(d, i, r, n) == Q.flat(Q.pow2(d), i, r, n) : List<&2, List<&2, Nat>>}

# LAW: the classic counts: the boards 4, 5 and 6 have 2, 10 and 4
# solutions (closed, by evaluation).
law counts:
  {Q.queens(4n, 2n) == 2n : Nat}
  & {Q.queens(5n, 3n) == 10n : Nat}
  & {Q.queens(6n, 3n) == 4n : Nat}
