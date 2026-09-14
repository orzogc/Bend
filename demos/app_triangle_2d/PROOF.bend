# Triangle -- the proofs. This file imports the program (as App) and
# the claims (as Laws) and fills every law. The U32 words are Base's
# 32-bit Word model, so Tri.inside on a literal point computes to a
# Bool; click_outside matches the down flag, the one Bool the event
# branches on, and then computes.
import Base
import ./main.bend as App
import ./LAWS.bend as Laws

def Laws.click_inside(n):
  {==}

def Laws.click_outside(n, d, x, y):
  match d:
    case True{}:
      ({==}, {==})
    case False{}:
      ({==}, {==})

def Laws.quits(n):
  ({==}, {==})

def Laws.code_off_strip(small, lit, away):
  ({==}, {==}, {==})
