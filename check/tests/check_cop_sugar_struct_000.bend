# SPEC PART 3 COP: +T without "~" resolves the witness structurally,
# +List<Nat> naming List.copy(Nat.copy); base ships no List.copy, so
# the resolution is pinned by the undefined name it reaches
import Base

assert keep:
  forall +x: +List<Nat>
  List<Nat>

def keep(x):
  x

assert main:
  Nat

def main():
  0n
$$ bend %
Error:
- expected : a defined name
- observed : List.copy
Location:
6 | assert keep:
7>|   forall +x: +List<Nat>
8 |   List<Nat>
