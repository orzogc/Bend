# bend3's slab literal declared its capacity forever ([1:5, _:0; 2]);
# bend4's Array has no capacity, default or literal -- the spelling is
# the refusal
import Base

assert main:
  U32

def main():
  m : [:U32] = ![1:5, _:0; 2]
  m[1]
$$ bend %
Error:
- expected : 'def', 'type' or 'assert'
- observed : ':'
Location:
 9 | def main():
10>|   m : [:U32] = ![1:5, _:0; 2]
11 |   m[1]
