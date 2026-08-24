# constructor destructuring row -- the ctor RHS needs a checked
# position, so it takes the annotation ({e : T}, bend4's spelling)
# ported from bend3: local Pair renamed (base owns the def name), and
# the word literal becomes a param (a U32 literal shows as its Word chain)
import Base

type Duo:
  P{a: U32, b: U32}

assert main:
  forall x: U32
  forall y: U32
  forall k: U32
  U32

def main(x, y, k):
  P{a, b} = {P{x, y} : Duo}
  (a * k) + b
$$ bend % --show
main = x => y => k => \{P: (a => b => U32.add(U32.mul(a, k), b))}({P{x, y} : Duo})
