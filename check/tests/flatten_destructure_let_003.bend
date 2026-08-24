# destructure of a PARAM: `P{a,b} = w` on a param var refines the column
# in place -- a direct one-case tree
# ported from bend3: local Pair renamed (base owns the def name)
import Base

type Duo:
  P{a: U32, b: U32}

assert main:
  forall w: Duo
  U32

def main(w):
  P{a, b} = w
  a + b
$$ bend % --show
main = \{P: (a => b => U32.add(a, b))}
