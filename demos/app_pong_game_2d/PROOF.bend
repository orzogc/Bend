# Pong -- the proofs. This file imports the game (as Game) and the
# claims (as Laws) and fills every law. Each claim is closed by
# evaluation: the game's U32 words are Base's 32-bit Word model, so the
# checker computes every step; the claim about an arbitrary state opens
# its Pong record with a match first.
import Base
import ./main.bend as Game
import ./LAWS.bend as Laws

def Laws.quits(g):
  match g:
    case Game.Pong{ly, ry, held, bx, by, vx, vy}:
      ({==}, {==})

def Laws.paddle_field(y):
  ({==}, {==}, {==}, {==})

def Laws.bounce(v):
  ({==}, {==}, {==})

def Laws.ball_orange(pad, none):
  {==}

def Laws.first_step():
  {==}
