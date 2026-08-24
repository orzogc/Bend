# comp-splice pin (spec_comp_late_param): bend3 accepted a comp param
# declared AFTER the matched column (the commuting application). bend4
# has no comp surface; the ~ in the second binder position pins bend4's
# own parse refusal at that spot.
import Base

type L:
  C{h: U32, t: L}
  N{}

assert each:
  forall xs: L
  forall ~f: U32 -> U32
  L

def each(xs, f):
  match xs:
    case C{h, t}:
      C{f(h), each(t, f)}
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
  total(each(C{1, C{2, C{3, N{}}}}, x => x * 2))
$$ bend %
Error:
- expected : a name
- observed : '~'
Location:
12 |   forall xs: L
13>|   forall ~f: U32 -> U32
14 |   L
