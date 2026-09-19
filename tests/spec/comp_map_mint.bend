# comp-splice pin (spec_comp_map_mint): bend3's map story -- a ~ param
# spliced at check time, minting one first-order def. bend's ~ law map
# checks once, f an opaque constant; the call passes f without ~, so the
# instance binds f as an erased runtime binder, and its live use is
# refused.
import Base

type L is Data:
  C{h: U32, t: L}
  N{}

law map:
  for ~f: U32 -> U32
  for xs: L
  L

def map(f, xs):
  match xs:
    case C{h, t}:
      C{f(h), map(f, t)}
    case N{}:
      N{}

law total:
  for xs: L
  U32

def total(xs):
  match xs:
    case C{h, t}:
      (h + total(t) : U32)
    case N{}:
      0

law main:
  U32

def main():
  total(map(x => (x + 1 : U32), C{1, C{2, C{3, N{}}}}))

#|Error:
#|- expected : -f
#|- observed : f
#|Location: map~0
#|16 |
#|17>| def map(f, xs):
#|18 |   match xs:
#|exit 1
