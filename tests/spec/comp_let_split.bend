# comp-splice pin (spec_comp_let_split): bend3's let-bound generic
# template call whose spec split a computed match. bend's ~ law keep
# checks once with p an opaque constant, up to its match on p(h): a
# computed scrutinee, which never specializes, by design. (bend3's
# number switch in the predicate respells through U32.is_gt.)
import Base

type B2 is Data:
  T{}
  F{}

type L<-A: Type> is Type:
  C{h: A, t: L<A>}
  N{}

law keep:
  for -A: Type
  for ~p: A -> B2
  for xs: L<A>
  L<A>

def keep(A, p, xs):
  match xs:
    case C{h, t}:
      match p(h):
        case T{}:
          C{h, keep(A, p, t)}
        case F{}:
          keep(A, p, t)
    case N{}:
      N{}

law total:
  for xs: L<U32>
  U32

def total(xs):
  match xs:
    case C{h, t}:
      (h + total(t) : U32)
    case N{}:
      0

law b2:
  for x: U32
  B2

def b2(x):
  match U32.is_gt(x, 1):
    case True{}:
      T{}
    case False{}:
      F{}

law main:
  U32

def main():
  total(keep(U32, x => b2(x), C{1, C{2, C{3, N{}}}}))

#|Error:
#|- message  : a parameter or field scrutinee (a match cannot scrutinize a computed value: give it its own def)
#|Location:
#|24 |     case C{h, t}:
#|25>|       match p(h):
#|26 |         case T{}:
#|exit 1
