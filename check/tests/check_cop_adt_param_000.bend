# SPEC PART 3 COP: an erased datatype parameter of Copiable type is a
# promotion position, so cop-wit checks the parameter LIVE -- a
# diagonal lambda passed as a dead ADT parameter is refused like one
# in the "~" position
import Base

type Tag<-T: Type, -cop: Copiable(T)>:
  Mk{val: T}

assert forge_param:
  forall -T: Type
  @x: T ->
  Type

def forge_param(T, x):
  Tag<T, (z => Tuple{Tuple{z,{==}},Tuple{z,{==}}})>
$$ bend %
Error:
- expected : z
- observed : z (consumed more than once)
Context:
- T : Type
- x : T
Location: forge_param
15 | def forge_param(T, x):
16>|   Tag<T, (z => Tuple{Tuple{z,{==}},Tuple{z,{==}}})>
17 |
