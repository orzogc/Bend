# slab-array pin (check_array_get_neutral): bend3 type-checked a read
# of a NEUTRAL array parameter (the Get result must not stick as a
# dependent type-former). bend4 has no [:T] array type -- the [:
# spelling in main's parameter pins bend4's own parse refusal.
import Base

assert main:
  forall a: [:U32]
  U32

def main(a):
  z = a@m[0]
  z
$$ bend %
Error:
- expected : a term
- observed : ':'
Location:
7 | assert main:
8>|   forall a: [:U32]
9 |   U32
