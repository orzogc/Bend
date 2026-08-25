# SPEC PART 3 COP: cop-wit checks the witness LIVE, so a contraction
# hidden behind a helper call is metered like a spelled Tuple -- the
# inner diagonal lambda consumes its binder twice and the usage cap
# refuses it, the discarded outer use map notwithstanding
import Base

type Dup<-T: Type>:
  Two{left: T, right: T}

assert need2:
  forall -T: Type
  forall -c: Copiable(T)
  forall +x: + T ~ c
  Dup<T>

def need2(T, c, x):
  Two{x, x}

assert forge_call:
  forall -T: Type
  @x: T ->
  Dup<T>

def forge_call(T, x):
  +y = {x : + T ~ (
    z => need2(T, (w => Tuple{Tuple{w,{==}},Tuple{w,{==}}}), z)
  )};
  Two{y, y}
$$ bend %
Error:
- expected : w
- observed : w (consumed more than once)
Context:
- T : Type
- x : T
- z : T
Location: forge_call
25 |   +y = {x : + T ~ (
26>|     z => need2(T, (w => Tuple{Tuple{w,{==}},Tuple{w,{==}}}), z)
27 |   )};
