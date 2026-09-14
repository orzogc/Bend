# Parallel sum -- the proofs. This file imports the program (as Par) and
# the claims (as Laws) and fills every law. Each claim closes by
# evaluation: sum's match on 0n or 1n+d unfolds one level of the tree,
# and the closed trees compute to their 32-bit words.
import Base
import ./main.bend as Par
import ./LAWS.bend as Laws

def Laws.sum_leaf(i):
  {==}

def Laws.sum_split(d, i):
  {==}

def Laws.sum_span():
  ({==}, {==})
