# bend3 imports parsed anywhere in the file; bend4 imports are leading
# lines only, by design -- one after a def dies at parse
import Base

assert f:
  forall x: U32
  U32

def f(x):
  x

import /late/mod.bend as L

assert main:
  U32

def main():
  0
$$ bend %
Error:
- expected : 'def', 'type' or 'assert'
- observed : 'i'
Location:
11 | 
12>| import /late/mod.bend as L
13 |
