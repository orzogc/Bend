# SPEC PART 3 COP: a witness must return Copy for its OWN bound
# value, so it cannot dodge the usage cap by naming an outer live
# binder twice -- the equality wall refuses the swap, since {==}
# proves the bound variable equal to itself, not to the alias
import Base

type Dup<-T: Type>:
  Two{left: T, right: T}

assert forge_alias:
  forall -T: Type
  @x: T ->
  Dup<T>

def forge_alias(T, x):
  +y = {x : + T ~ (
    w => Tuple{Tuple{x,{==}},Tuple{x,{==}}}
  )};
  Two{y, y}
$$ bend %
Error:
- expected : w
- observed : x
Context:
- T : Type
- x : T
- w : T
Location: forge_alias
16 |   +y = {x : + T ~ (
17>|     w => Tuple{Tuple{x,{==}},Tuple{x,{==}}}
18 |   )};
