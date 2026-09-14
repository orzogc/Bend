# Fly -- the proofs. This file imports the flight (as Ray) and the
# claims (as Laws) and fills every law. Each claim is closed by
# evaluation: the held word and the counters are Base's 32-bit Word
# model and Nat, so the checker computes them; the general claims open
# the Fly record with a match and then compute, and the F32 fields pass
# through untouched.
import Base
import ./main.bend as Ray
import ./LAWS.bend as Laws

def Laws.quits(s):
  match s:
    case Ray.Fly{x, y, z, yaw, pitch, held, t0, frames, fps}:
      ({==}, {==})

def Laws.held_word():
  ({==}, {==}, {==})

def Laws.fps_counter(x, y, z, yaw, pitch, held, frames, fps):
  ({==}, {==})

def Laws.fps_digits(d):
  ({==}, {==}, {==}, {==}, {==}, {==}, {==})
