# Parallel N-queens -- the laws. Claims about the search: the fork tree
# joins by addition at every depth; the backtracker ends a chain in two
# ways (a row with no free column keeps the count, a board with no row
# left adds one); the boards 1 to 6 have their classic counts; and a
# wider fork space gives the same count. PROOF.bend must prove every one.
import Base
import ./main.bend as Q

# LAW: a fork joins as the sum of its halves: the tree of depth d + 1
# at the index i counts what the tree of depth d at i and the tree of
# depth d at i + 2^d count together, for any board and prefix shape.
law fork_split:
  for +d: Nat
  for +i: U32
  for +k: Nat
  for +w: Nat
  for +left: Nat
  for +full: U32
  {Q.fork(1n+d, i, k, w, left, full)
    == (Q.fork(d, i, k, w, left, full) + Q.fork(d, (i + (1 << d) : U32), k, w, left, full) : U32) : U32}

# LAW: the backtracker ends a chain in two ways: a row with no free
# column (the flag is True) keeps the count acc, for any words; a board
# with no row left adds one to acc, whatever the flag and the words.
law solve_ends:
  for +g: Nat
  for +p: Nat
  for z: Bool
  for +cand: U32
  for +cols: U32
  for +ld: U32
  for +rd: U32
  for +full: U32
  for +acc: U32
  {Q.solve(1n+g, 1n+p, True{}, cand, cols, ld, rd, full, acc) == acc : U32}
  & {Q.solve(1n+g, 0n, z, cand, cols, ld, rd, full, acc) == (acc + 1 : U32) : U32}

# LAW: the classic counts: the boards 1 to 6 have 1, 0, 0, 2, 10 and 4
# solutions (the width w is the bits of a column: 2^w >= n).
law counts:
  {Q.queens(1n, 0n) == 1 : U32}
  & {Q.queens(2n, 1n) == 0 : U32}
  & {Q.queens(3n, 2n) == 0 : U32}
  & {Q.queens(4n, 2n) == 2 : U32}
  & {Q.queens(5n, 3n) == 10 : U32}
  & {Q.queens(6n, 3n) == 4 : U32}

# LAW: a wider fork space gives the same count: 3 bits per column name
# columns beyond the 4 x 4 board, which are never free, so the extra
# leaves count nothing.
law width:
  {Q.queens(4n, 3n) == Q.queens(4n, 2n) : U32}
