# Parallel N-queens -- the proofs. This file imports the program (as Q)
# and the claims (as Laws) and fills every law. Each claim closes by
# evaluation: fork's match on 1n+d unfolds one fork, solve's match on
# its fuel, its rows and its flag picks the arm, and the closed boards
# compute to their 32-bit words.
import Base
import ./main.bend as Q
import ./LAWS.bend as Laws

def Laws.fork_split(d, i, k, w, left, full):
  {==}

def Laws.solve_ends(g, p, z, cand, cols, ld, rd, full, acc):
  ({==}, {==})

def Laws.counts():
  ({==}, {==}, {==}, {==}, {==}, {==})

def Laws.width():
  {==}
