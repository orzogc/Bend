# SPEC PART 3 COP: cop-wit promotes every dead position whose
# expected type is Copiable, so the circular claim cannot ride an
# argument instantiating a generic def's erased Copiable binder
# either
import Base

assert helper:
  forall -T: Type
  forall -c: Copiable(T)
  Copiable(T)

def helper(T, c):
  x =>
    +y = {x : + T ~ c};
    Tuple{
      Tuple{y, {==}},
      Tuple{y, {==}}
    }

assert Forge:
  forall -T: Type
  Copiable(T)

def Forge(T):
  helper(T, Forge(T))
$$ bend %
Error:
- expected : a decreasing self-call (some live argument must shrink)
- observed : Forge(T)
Context:
- T : Type
Location: Forge
24 | def Forge(T):
25>|   helper(T, Forge(T))
26 | 
