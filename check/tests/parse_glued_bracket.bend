# a bare underapplied generic def at a concrete type errors with its
# generalized type.
# ported from bend3: def-level <A> params become an erased -A: Type bind
import Base

assert id2:
  forall -A: Type
  forall x: A
  A

def id2(A, x):
  x

assert main:
  U32

def main(): id2
$$ bend %
Error:
- expected : U32
- observed : @-A:Type -> @x:A -> A
Location: main
16 | 
17>| def main(): id2
18 |
