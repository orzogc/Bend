# bend3's ! computed mark suffixed only names and failed loudly
# elsewhere; bend4's ! is the GPU bang glued before a call's parens,
# so the postfix spelling on a completed call dies at parse the same
# way, by bend4's own grammar
import Base

assert f:
  forall x: U32
  U32

def f(x):
  x

assert main:
  U32

def main():
  f(1)!
$$ bend %
Error:
- expected : 'def', 'type' or 'assert'
- observed : '!'
Location:
17 | def main():
18>|   f(1)!
19 |
