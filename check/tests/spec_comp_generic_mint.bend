# comp-splice pin (spec_comp_generic_mint): bend3's generic template --
# the exact List.map shape, one mint per site with the instantiation
# baked in. bend4 rules the comp surface out (map is not checkable even
# once Data lands); bend3's def<A,B> respells as erased -A/-B binders
# and the ~ binder pins bend4's own parse refusal.
import Base

type L<-A: Type>:
  C{h: A, t: L<A>}
  N{}

assert map:
  forall -A: Type
  forall -B: Type
  forall ~f: A -> B
  forall xs: L<A>
  L<B>

def map(A, B, f, xs):
  match xs:
    case C{h, t}:
      C{f(h), map(A, B, f, t)}
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

assert main:
  U32

def main():
  total(map(U32, U32, x => x + 1, C{1, C{2, N{}}}))
$$ bend %
Error:
- expected : a name
- observed : '~'
Location:
14 |   forall -B: Type
15>|   forall ~f: A -> B
16 |   forall xs: L<A>
