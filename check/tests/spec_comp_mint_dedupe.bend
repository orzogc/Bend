# comp-splice pin (spec_comp_mint_dedupe): bend3's filter/fold shapes
# with per-site mint counting. bend4 rules the comp surface out
# (filter/map are not checkable libs); the ~ binder pins bend4's own
# parse refusal. (bend3's `x % 2` oddness respells through U32.and.)
import Base

type L:
  C{h: U32, t: L}
  N{}

assert filter:
  forall ~p: U32 -> Bool
  forall xs: L
  L

def filter(p, xs):
  match xs:
    case C{h, t}:
      if p(h):
        C{h, filter(p, t)}
      else:
        filter(p, t)
    case N{}:
      N{}

assert fold:
  forall ~f: U32 -> U32 -> U32
  forall xs: L
  forall z: U32
  U32

def fold(f, xs, z):
  match xs:
    case C{h, t}:
      fold(f, t, f(h, z))
    case N{}:
      z

assert nums:
  L

def nums():
  C{1, C{2, C{3, C{4, N{}}}}}

assert odds:
  L

def odds():
  filter(x => U32.is_ne(U32.and(x, 1), 0), nums())

assert main:
  U32

def main():
  fold(a => b => a + b, odds(), 0)
$$ bend %
Error:
- expected : a name
- observed : '~'
Location:
11 | assert filter:
12>|   forall ~p: U32 -> Bool
13 |   forall xs: L
