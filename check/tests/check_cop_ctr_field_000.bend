# SPEC PART 3 COP: an erased constructor field of Copiable type is a
# promotion position, so cop-wit checks the field LIVE -- a diagonal
# lambda dropped in a dead ctr field is refused exactly like one in
# the "~" position
import Base

type Box<-T: Type>:
  Wrap{-cop: Copiable(T), val: T}

assert forge_field:
  forall -T: Type
  @x: T ->
  Box<T>

def forge_field(T, x):
  Wrap{(z => Tuple{Tuple{z,{==}},Tuple{z,{==}}}), x}
$$ bend %
Error:
- expected : z
- observed : z (consumed more than once)
Context:
- T : Type
- x : T
Location: forge_field
15 | def forge_field(T, x):
16>|   Wrap{(z => Tuple{Tuple{z,{==}},Tuple{z,{==}}}), x}
17 |
