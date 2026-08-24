# slab-array pin (check_array_element_data): bend3 refused a non-Data
# (arrow) element type AT THE LITERAL while the array type itself
# stayed well-formed. bend4 has neither the [:T] array type nor the
# literal -- the [: spelling in the signature pins bend4's own parse
# refusal.
import Base

assert take:
  forall a: [:U32 -> U32]
  U32

def take(a):
  0

assert main:
  U32

def main():
  h = (![0:1, _:0; 2] : [:U32 -> U32])
  0
$$ bend %
Error:
- expected : a term
- observed : ':'
Location:
 8 | assert take:
 9>|   forall a: [:U32 -> U32]
10 |   U32
