# comp-splice pin (spec_mint_count): bend3's comp-lambda mint-count cost
# guard (a recursive template's knot tied structurally, counted under
# --stats). bend has no stats surface; a ~ clause after a plain one
# heads no template (only leading ~ clauses do), so g is an erased
# binder, and its live use in the fill is refused. (bend3's number
# switch on the counter respells as base Nat recursion.)
import Base

law each:
  for n: Nat
  for ~g: U32 -> U32
  for x: U32
  U32

def each(n, g, x):
  match n:
    case 0n:
      g(x)
    case 1n+k:
      each(k, g, g(x))

law u0:
  for x: U32
  U32

def u0(x):
  (each(3n, y => (y + 1 : U32), x) + each(2n, y => (y * 2 : U32), x) : U32)

law main:
  U32

def main():
  u0(1)

#|Error:
#|- expected : -g
#|- observed : g
#|Location: each
#|14 |
#|15>| def each(n, g, x):
#|16 |   match n:
#|exit 1
