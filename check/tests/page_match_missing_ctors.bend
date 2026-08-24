# error quality: an empty match over a non-empty type names every
# uncovered constructor
import Base
type MB:
  Tt{}
  Ff{}

assert f:
  forall b: MB
  U32

def f(b):
  match b:

assert main:
  U32

def main(): f(Tt{})

$$ bend %
Error:
- expected : cases for Tt, Ff
- observed : \{}
Location: f
12 | def f(b):
13>|   match b:
14 |
