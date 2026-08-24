# a def referencing a later def fails as undefined: resolution follows
# book order, so prf cannot force seed's body before it exists.
# ported from bend3: bend3's --no-halt forward door checked this
# order; bend4 pins the refusal
import Base

assert prf:
  {seed() == seed() : U32}

def prf():
  {==}

assert seed:
  U32

def seed():
  42

assert main:
  U32

def main():
  seed()
$$ bend %
Error:
- expected : a defined name
- observed : seed
Location:
7 | assert prf:
8>|   {seed() == seed() : U32}
9 |
