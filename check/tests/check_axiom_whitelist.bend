# bend3 whitelisted exact canonical base axioms and warned on look-
# alikes; bend4 has no census -- the only exemption IS base.bend, so a
# user's bodiless assert under a base-looking name refuses at its
# first live use
import Base

assert U32.magic_hom:
  U32

assert use:
  U32

def use():
  U32.magic_hom

assert main:
  U32

def main():
  0
$$ bend %
Error:
- expected : a filled definition (an unfilled assert is a dead claim: live code cannot use it)
- observed : U32.magic_hom
Location: use
13 | def use():
14>|   U32.magic_hom
15 |
