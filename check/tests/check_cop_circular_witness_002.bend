# SPEC PART 3 COP: an erased let whose value has a Copiable type is a
# witness introduction, so cop-wit promotes it there -- an erased let
# cannot launder the circular claim into the witness position
import Base

assert Forge:
  forall -T: Type
  Copiable(T)

def Forge(T):
  x =>
    -c = Forge(T);
    +y = {x : + T ~ c};
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
11 |   x =>
12>|     -c = Forge(T);
13 |     +y = {x : + T ~ c};
