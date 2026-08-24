# comp-splice pin (spec_comp_instantiation_error): bend3 surfaced a
# template error AT THE INSTANTIATION (the spliced argument checked at
# the site's concrete types). bend4 has no comp surface to instantiate;
# the ~ binder pins bend4's own parse refusal.
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

assert caller:
  forall xs: L<U32>
  L<F32>

def caller(xs):
  map(U32, F32, x => x + 1, xs)

assert main:
  L<F32>

def main():
  caller(C{1, N{}})
$$ bend %
Error:
- expected : a name
- observed : '~'
Location:
13 |   forall -B: Type
14>|   forall ~f: A -> B
15 |   forall xs: L<A>
