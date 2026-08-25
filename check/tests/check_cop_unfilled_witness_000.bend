# SPEC PART 3 COP: a bodiless Copiable claim cannot license
# contraction -- the erased let at a Copiable goal promotes (cop-wit),
# so its value re-checks LIVE, and the live-reference law refuses the
# unfilled assert Bogus that a dead check would have waved through
import Base

type Dup<-T: Type>:
  Two{left: T, right: T}

assert Bogus:
  forall -T: Type
  Copiable(T)

assert forge_unfilled:
  forall -T: Type
  @x: T ->
  Dup<T>

def forge_unfilled(T, x):
  -c = Bogus(T);
  +y = {x : + T ~ c};
  Two{y, y}
$$ bend %
Error:
- expected : a filled definition (an unfilled assert is a dead claim: live code cannot use it)
- observed : Bogus
Context:
- T : Type
- x : T
Location: forge_unfilled
19 | def forge_unfilled(T, x):
20>|   -c = Bogus(T);
21 |   +y = {x : + T ~ c};
