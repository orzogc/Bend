# comp-splice pin (spec_comp_late_param): bend3 accepted a comp param
# declared AFTER the matched column (the commuting application). a ~
# clause after a plain one heads no template (only leading ~ clauses
# do), so f is an erased binder, and its live use in the fill is
# refused.
import Base

type L is Data:
  C{h: U32, t: L}
  N{}

law each:
  for xs: L
  for ~f: U32 -> U32
  L

def each(xs, f):
  match xs:
    case C{h, t}:
      C{f(h), each(t, f)}
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
  total(each(C{1, C{2, C{3, N{}}}}, x => (x * 2 : U32)))

#|Error:
#|- expected : -f
#|- observed : f
#|Context:
#|- h : U32
#|- t : L
#|Location: each
#|16 |
#|17>| def each(xs, f):
#|18 |   match xs:
#|exit 1
