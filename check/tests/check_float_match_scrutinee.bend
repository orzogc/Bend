# an F32 is no datatype: it has no constructors, so a ctor arm on an
# F32 scrutinee is a type error (a bare var arm is just a binder) --
# bend3 pinned literal float switches, parse_float_pattern holds the
# literal half
import Base

assert f:
  forall x: F32
  U32

def f(x):
  match x:
    case Chr{c}:
      0

assert main:
  U32

def main():
  f(1.5)
$$ bend %
Error:
- expected : a datatype
- observed : F32
Location: f
12 |   match x:
13>|     case Chr{c}:
14 |       0
