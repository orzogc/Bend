# bend3 pinned that a list literal never satisfies an ARRAY goal;
# bend4 has no [:T] array type at all -- the spelling dies at parse
# before any goal exists
import Base

assert t:
  forall x: U32
  {[x] == [x] : [:U32]}

def t(x):
  {==}

assert main:
  U32

def main():
  0
$$ bend %
Error:
- expected : a term
- observed : ':'
Location:
7 |   forall x: U32
8>|   {[x] == [x] : [:U32]}
9 |
