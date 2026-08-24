# comp-splice pin (spec_comp_capture_linear): bend3's capture honesty,
# negative side -- a recursive template capturing a closure-typed var
# died BadUsage at the instantiation (closures never contract). bend4
# has no comp surface at all; the ~ binder pins bend4's own parse
# refusal (the affine wall itself is pinned by the capture twins).
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

assert bad:
  forall g: U32 -> U32
  forall xs: L
  L

def bad(g, xs):
  map(x => g(x), xs)

assert main:
  L

def main():
  bad(y => y + 1, C{1, C{2, N{}}})
$$ bend %
Error:
- expected : a name
- observed : '~'
Location:
12 | assert map:
13>|   forall ~f: U32 -> U32
14 |   forall xs: L
