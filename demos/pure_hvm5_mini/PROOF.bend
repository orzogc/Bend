# HVM5 in Bend -- the proofs. This file imports the interpreter (as
# Hvm) and the claims (as Laws) and fills every law. The cursor law is
# an induction on the source and the position; the run-word law is a
# case split on the bit, after which both sides compute; the name and
# depth laws compute outright.

import Base
import ./main.bend as Hvm
import ./LAWS.bend as Laws

def Laws.at_drop(s, n):
  match s n:
    case SNil{} 0n:
      {==}
    case SNil{} 1n+p:
      {==}
    case SCon{Chr{c}, t} 0n:
      {==}
    case SCon{Chr{c}, t} 1n+p:
      Laws.at_drop(t, p)

def Laws.run_push_pop(b):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.name_round_trip():
  {==}

def Laws.book_depth_fits():
  {==}
