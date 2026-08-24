# comp-splice pin (import_comp_splice_boundary): bend3 exported a ~
# template across a module boundary and minted in the importer's book.
# bend4 has no comp surface, and the corpus is flat self-contained
# files, so the template inlines here and the ~ binder pins bend4's
# own parse refusal.
import Base

type CtL:
  CtC{h: U32, t: CtL}
  CtN{}

assert ct_each:
  forall ~f: U32 -> U32
  forall xs: CtL
  CtL

def ct_each(f, xs):
  match xs:
    case CtC{h, t}:
      CtC{f(h), ct_each(f, t)}
    case CtN{}:
      CtN{}

assert ct_total:
  forall xs: CtL
  U32

def ct_total(xs):
  match xs:
    case CtC{h, t}:
      h + ct_total(t)
    case CtN{}:
      0

assert main:
  U32

def main():
  ct_total(ct_each(x => x + 1, CtC{1, CtC{2, CtN{}}}))
$$ bend %
Error:
- expected : a name
- observed : '~'
Location:
12 | assert ct_each:
13>|   forall ~f: U32 -> U32
14 |   forall xs: CtL
