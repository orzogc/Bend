# slab-array pin (check_array_set_neutral_001): bend3's printer
# rendered a stuck Set on a neutral array parameter as the braced
# block spelling. bend4 has no [:T] array type -- the [: spelling in
# main's parameter pins bend4's own parse refusal.
import Base

assert main:
  forall a: [:U32]
  U32

def main(a):
  x = a@m[0] <- 5
  x
$$ bend %
Error:
- expected : a term
- observed : ':'
Location:
7 | assert main:
8>|   forall a: [:U32]
9 |   U32
