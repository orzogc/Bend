# bend3's cid-pair ctor representation (boxed and word rows chosen per
# field type variable); bend4's emitter has no cid pairs and the
# test's generic defs are ruled out with def<A> (collides with infix
# <) -- the family's own head dies at parse
import Base

type Box7<-A: Type>:
  Box7{x: A}

assert wrap:
  forall -A: Type
  forall x: A
  Result<U32, A>

def wrap<A>(x):
  Done{x}

assert main:
  U32

def main():
  0
$$ bend %
Error:
- expected : '('
- observed : '<'
Location:
14 | 
15>| def wrap<A>(x):
16 |   Done{x}
