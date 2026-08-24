# bend3 resolved a comparison at a Type goal to the install relation,
# immune to local rebinding; bend4 has no comparison-at-Type sugar at
# all -- < is the term-level word guard, and the Type-position
# spelling dies asking for its U32 operand
import Base

assert bogus:
  3n < 2n

def bogus():
  Unit{}

assert main:
  U32

def main():
  0
$$ bend %
Error:
- expected : U32
- observed : 3n
Location:
7 | assert bogus:
8>|   3n < 2n
9 |
