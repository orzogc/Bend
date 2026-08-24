# slab-array pin (check_array_not_data): bend3's array boundary --
# contraction is free on Data and arrays are not Data, so an aliased
# array binder stayed a Usage error. bend4 has no [:T] array type --
# the [: spelling in f's parameters pins bend4's own parse refusal
# (bend4 is affine at every type; the capture twins pin that wall).
import Base

assert f:
  forall a: [:U32]
  forall b: [:U32]
  U32

def f(a, b):
  x = a@a1[0]
  y = b@b1[0]
  x + y

assert main:
  U32

def main():
  arr = (![0:5, _:0; 1] : [:U32])
  f(arr, arr)
$$ bend %
Error:
- expected : a term
- observed : ':'
Location:
 8 | assert f:
 9>|   forall a: [:U32]
10 |   forall b: [:U32]
