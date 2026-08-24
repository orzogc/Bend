# error census: matching a non-datatype scrutinee (a function) is the
# bare a-datatype mismatch
import Base
type MB:
  Z{}

assert f:
  forall h: U32 -> U32
  U32

def f(h):
  match h:
    case Z{}:
      0

assert main:
  U32

def main(): f(x => x)

$$ bend %
Error:
- expected : a datatype
- observed : @_:U32 -> U32
Location: f
12 |   match h:
13>|     case Z{}:
14 |       0
