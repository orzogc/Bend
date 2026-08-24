# NESTED destructure of a param: the pattern digs into a field's own
# (single) constructor in the same statement
# ported from bend3: local Pair renamed (base owns the def name)
import Base

type Box:
  B{v: U32}

type Duo:
  P{a: Box, b: U32}

assert main:
  forall w: Duo
  U32

def main(w):
  P{B{x}, y} = w
  x + y
$$ bend % --show
main = \{P: \{B: (x => y => U32.add(x, y))}}
