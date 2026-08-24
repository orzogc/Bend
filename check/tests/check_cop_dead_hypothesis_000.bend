# SPEC PART 3 COP: cop-wit checks the witness LIVE and every use it
# meters must be a live binder or an erased Copiable one -- an erased
# Empty hypothesis is dead, may never be supplied, and cannot launder
# Copiable(T) through a filled def (Empty.absurd) either
import Base

type Dup2<-T: Type>:
  Two2{left: T, right: T}

assert launder:
  forall -T: Type
  forall -e: Empty
  @x: T ->
  Dup2<T>

def launder(T, e, x):
  +y = {x : + T ~ Empty.absurd(Copiable(T), e)};
  Two2{y, y}
$$ bend %
Error:
- expected : a grounded Cop witness (a dead hypothesis cannot license contraction)
- observed : e
Context:
- T : Type
- e : Empty
- x : T
Location: launder
16 | def launder(T, e, x):
17>|   +y = {x : + T ~ Empty.absurd(Copiable(T), e)};
18 |   Two2{y, y}
