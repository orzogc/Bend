# slab-array pin (check_array_get_word_only): bend3 limited free reads
# to word (U32/F32) elements -- a boxed element reads by swap. bend4
# has no [:T] array type -- the [: spelling in main's parameter pins
# bend4's own parse refusal.
import Base

type Box2:
  BX{v: U32}

assert main:
  forall xs: [:Box2]
  Box2

def main(xs):
  x = xs@ys[0]
  x
$$ bend %
Error:
- expected : a term
- observed : ':'
Location:
10 | assert main:
11>|   forall xs: [:Box2]
12 |   Box2
