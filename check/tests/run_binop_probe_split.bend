# bend3's Op2 probe-reuse pin applied a NUMERIC match-lambda as the
# left operand; bend4 match-lambdas take constructor keys only, so the
# probe's spelling dies at parse on the 0: key
import Base

assert f:
  forall n: U32
  forall y: U32
  U32

def f(n, y):
  \{0: 7; k => k * 2}(n : U32) + y

assert main:
  U32

def main():
  (f(0, 1) * 100) + f(5, 1)
$$ bend %
Error:
- expected : '}'
- observed : ':'
Location:
11 | def f(n, y):
12>|   \{0: 7; k => k * 2}(n : U32) + y
13 |
