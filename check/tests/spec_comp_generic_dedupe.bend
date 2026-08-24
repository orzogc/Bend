# comp-splice pin (spec_comp_generic_dedupe): bend3's generic battery --
# capture through a generic template, two type-pair instantiations,
# per-site minting. bend4 has no comp surface; def<A,B> respells as
# erased -A/-B binders and the ~ binder pins bend4's own parse refusal.
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

assert shift:
  forall k: U32
  forall xs: L<U32>
  L<U32>

def shift(k, xs):
  map(U32, U32, x => x + k, xs)

assert main:
  U32

def main():
  total(shift(10, C{1, C{2, N{}}}))
$$ bend %
Error:
- expected : a name
- observed : '~'
Location:
13 |   forall -B: Type
14>|   forall ~f: A -> B
15 |   forall xs: L<A>
