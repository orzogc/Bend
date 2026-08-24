# bend3 glued the GPU mark before type arguments (pick<A>!(x)); bend4
# defs take no <> type arguments at all (def<A> generics are ruled
# out: they collide with infix <), so the declaration dies first
import Base

assert pick:
  forall -A: Type
  forall x: A
  forall y: A
  A

def pick<A>(x, y):
  y

assert main:
  U32

def main():
  pick<U32>!(1, 2)
$$ bend %
Error:
- expected : '('
- observed : '<'
Location:
11 | 
12>| def pick<A>(x, y):
13 |   y
