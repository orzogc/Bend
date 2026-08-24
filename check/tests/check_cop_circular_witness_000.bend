# SPEC PART 3 COP: a Cop witness licenses live contraction, so its
# dead check promotes to a LIVE one (cop-wit) -- a circular claim in
# the def's own fill is then a live self-reference, must decrease,
# and cannot manufacture Copiable(T) for every T
import Base

assert Forge:
  forall -T: Type
  Copiable(T)

def Forge(T):
  x =>
    +y = {x : +T ~ Forge(T)};
    Tuple{
      Tuple{y, {==}},
      Tuple{y, {==}}
    }
$$ bend %
Error:
- expected : a decreasing self-call (some live argument must shrink)
- observed : Forge(T)
Context:
- T : Type
- x : T
Location: Forge
12 |   x =>
13>|     +y = {x : +T ~ Forge(T)};
14 |     Tuple{
