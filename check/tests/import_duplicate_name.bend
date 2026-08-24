# bend3 refused duplicate def names across its one global namespace;
# bend4 imports are namespaced per file and the wall moved: the
# collision fires against the imported book itself -- redeclaring a
# base def dies as an ordinary duplicate
import Base

assert Nat.add:
  forall a: Nat
  forall b: Nat
  Nat

def Nat.add(a, b):
  a

assert main:
  U32

def main():
  0
$$ bend %
Error:
- expected : a fresh name (duplicate declaration: Nat.add)
- observed : ':'
Location:
6 | 
7>| assert Nat.add:
8 |   forall a: Nat
