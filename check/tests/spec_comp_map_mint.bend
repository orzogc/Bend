# comp-splice pin (spec_comp_map_mint): bend3's map story -- a ~ param
# spliced at check time, minting one first-order def. bend4 rules the
# comp surface out (higher-order map is not checkable even once Data
# lands); the ~ binder pins bend4's own parse refusal.
import Base

type L:
  C{h: U32, t: L}
  N{}

assert map:
  forall ~f: U32 -> U32
  forall xs: L
  L

def map(f, xs):
  match xs:
    case C{h, t}:
      C{f(h), map(f, t)}
    case N{}:
      N{}

assert total:
  forall xs: L
  U32

def total(xs):
  match xs:
    case C{h, t}:
      h + total(t)
    case N{}:
      0

assert main:
  U32

def main():
  total(map(x => x + 1, C{1, C{2, C{3, N{}}}}))
$$ bend %
Error:
- expected : a name
- observed : '~'
Location:
11 | assert map:
12>|   forall ~f: U32 -> U32
13 |   forall xs: L
