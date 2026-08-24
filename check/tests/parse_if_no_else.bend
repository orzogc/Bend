# an if chain must end in else: bend4's own refusal (bend3 pinned its
# if statement laws; the term form demands totality)
import Base

assert f:
  forall b: Bool
  U32

def f(b):
  if b: 1

assert main:
  U32

def main():
  f(True{})
$$ bend %
Error:
- expected : an 'elif' or 'else' (an if chain ends in else)
- observed : 'a'
Location:
11 | 
12>| assert main:
13 |   U32
