# comp-splice pin (spec_mint_count): bend3's comp-lambda mint-count cost
# guard (a recursive template's knot tied structurally, counted under
# --stats). bend4 has neither comp mints nor a stats surface; the ~
# binder pins bend4's own parse refusal. (bend3's number switch on the
# counter respells as base Nat recursion.)
import Base

assert each:
  forall n: Nat
  forall ~g: U32 -> U32
  forall x: U32
  U32

def each(n, g, x):
  match n:
    case 0n:
      g(x)
    case 1n+k:
      each(k, g, g(x))

assert u0:
  forall x: U32
  U32

def u0(x):
  each(3n, y => y + 1, x) + each(2n, y => y * 2, x)

assert main:
  U32

def main():
  u0(1)
$$ bend %
Error:
- expected : a name
- observed : '~'
Location:
 9 |   forall n: Nat
10>|   forall ~g: U32 -> U32
11 |   forall x: U32
