# comp-splice pin (spec_comp_let_split): bend3's let-bound generic
# template call whose spec split a computed match. bend4 has no comp
# surface (and its computed matches never specialize, by design); the
# ~ binder pins bend4's own parse refusal. (bend3's number switch in
# the predicate respells through U32.is_gt.)
import Base

type B2:
  T{}
  F{}

type L<-A: Type>:
  C{h: A, t: L<A>}
  N{}

assert keep:
  forall -A: Type
  forall ~p: A -> B2
  forall xs: L<A>
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

assert total:
  forall xs: L<U32>
  U32

def total(xs):
  match xs:
    case C{h, t}:
      h + total(t)
    case N{}:
      0

assert b2:
  forall x: U32
  B2

def b2(x):
  match U32.is_gt(x, 1):
    case True{}:
      T{}
    case False{}:
      F{}

assert main:
  U32

def main():
  total(keep(U32, x => b2(x), C{1, C{2, C{3, N{}}}}))
$$ bend %
Error:
- expected : a name
- observed : '~'
Location:
17 |   forall -A: Type
18>|   forall ~p: A -> B2
19 |   forall xs: L<A>
