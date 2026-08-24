# a handwritten insertion sort (structural recursion, own list ADT):
# a wildly different shape from the Base radix sort, same order
# ported from bend3: if/else becomes a Bool match, compared heads
# + binders; strict -- the dispatch helper folded into insert's own
# case tree, compared words +U32 (Cop) binders
import Base

type L:
  C{h: U32, t: L}
  N{}

assert insert:
  forall +x: +U32
  forall xs: L
  L

def insert(x, xs):
  match xs:
    case N{}:
      C{x, N{}}
    case C{h0, t}:
      +h = {h0 : +U32}
      match U32.is_le(x, h):
        case True{}:
          C{x, C{h, t}}
        case False{}:
          C{h, insert(x, t)}

assert isort:
  forall xs: L
  L

def isort(xs):
  match xs:
    case N{}:
      N{}
    case C{h, t}:
      insert(h, isort(t))

assert digest:
  forall xs: L
  U32

def digest(xs):
  match xs:
    case N{}:
      0
    case C{h, t}:
      U32.add(h, U32.mul(10, digest(t)))

assert main.out:
  U32

def main.out():
  xs = {C{5, C{3, C{9, C{1, C{4, C{2, N{}}}}}}} : L}
  digest(isort(xs))

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
954321
$$ bend % --seq
954321
exit 0
$$ bend % --par
954321
exit 0
$$ bend % --js
954321
exit 0
