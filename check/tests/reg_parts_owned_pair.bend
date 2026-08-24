# regression witness (f72dc46): a fused record's OWNED fields obey the
# use counts -- a Parts-bound pair holding a cow'd block was once
# rebuilt at every use (two Tuples aliasing one array, use-after-free)
# and never dropped in the arm that ignores it (a leak). The doubled
# read rides the local Arr/Pair copy witnesses, strict.
import Base

assert Arr.copy:
  forall t: Array<U32>
  Copy(Array<U32>, t) & Copy(Array<U32>, t)

def Arr.copy(t):
  match t:
    case ALeaf{x}:
      ((xx, xe), (xy, xf)) = U32.copy(x)
      e1 = Equal.cong(U32, Array<U32>, z => ALeaf{z}, x, xx, xe)
      e2 = Equal.cong(U32, Array<U32>, z => ALeaf{z}, x, xy, xf)
      ((ALeaf{xx}, e1), (ALeaf{xy}, e2))
    case ANode{xs, ys}:
      ((ax, ae), (ay, af)) = Arr.copy(xs)
      ((bx, be), (by, bf)) = Arr.copy(ys)
      s10 = Equal.cong(Array<U32>, Array<U32>, z => ANode{z, ys}, xs, ax, ae)
      s11 = Equal.cong(Array<U32>, Array<U32>, z => ANode{ax, z}, ys, bx, be)
      t11 = Equal.trans(Array<U32>, ANode{xs, ys}, ANode{ax, ys}, ANode{ax, bx}, s10, s11)
      s20 = Equal.cong(Array<U32>, Array<U32>, z => ANode{z, ys}, xs, ay, af)
      s21 = Equal.cong(Array<U32>, Array<U32>, z => ANode{ay, z}, ys, by, bf)
      t21 = Equal.trans(Array<U32>, ANode{xs, ys}, ANode{ay, ys}, ANode{ay, by}, s20, s21)
      ((ANode{ax, bx}, t11), (ANode{ay, by}, t21))

assert Pair.copy:
  forall -c1: Copiable(Array<U32>)
  forall -c2: Copiable(U32)
  forall t: Array<U32> & U32
  Copy(Array<U32> & U32, t) & Copy(Array<U32> & U32, t)

def Pair.copy(c1, c2, t):
  (a, b) = t
  ((ax, ae), (ay, af)) = Arr.copy(a)
  ((bx, be), (by, bf)) = U32.copy(b)
  s10 = Equal.cong(Array<U32>, Array<U32> & U32, z => (z, b), a, ax, ae)
  s11 = Equal.cong(U32, Array<U32> & U32, z => (ax, z), b, bx, be)
  t11 = Equal.trans(Array<U32> & U32, (a, b), (ax, b), (ax, bx), s10, s11)
  s20 = Equal.cong(Array<U32>, Array<U32> & U32, z => (z, b), a, ay, af)
  s21 = Equal.cong(U32, Array<U32> & U32, z => (ay, z), b, by, bf)
  t21 = Equal.trans(Array<U32> & U32, (a, b), (ay, b), (ay, by), s20, s21)
  (((ax, bx), t11), ((ay, by), t21))

assert rd:
  forall a: Array<U32>
  U32

def rd(a):
  match a:
    case ALeaf{x}:
      x
    case ANode{xs, ys}:
      U32.add(rd(xs), rd(ys))

assert mk:
  Array<U32>

def mk():
  ANode{ANode{ALeaf{1}, ALeaf{2}}, ANode{ALeaf{3}, ALeaf{4}}}

assert go:
  forall p: Array<U32> & U32
  U32

def go(p):
  match p:
    case Tuple{b, o}:
      U32.add(rd(b), o)

assert use2:
  forall +p: (+ (Array<U32> & U32) ~ Pair.copy(Arr.copy, U32.copy))
  U32

def use2(p):
  U32.add(go(p), go(p))

assert pick2:
  forall c: Bool
  forall p: Array<U32> & U32
  U32

def pick2(c, p):
  match c:
    case True{}:
      go(p)
    case False{}:
      5

assert main.out:
  U32

def main.out():
  a = use2(Array.swap(U32, mk(), 1, 9))
  b = pick2(False{}, Array.swap(U32, mk(), 2, 8))
  c = pick2(True{}, Array.swap(U32, mk(), 0, 6))
  U32.add(a, U32.add(b, c))

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
59
$$ bend % --seq
59
exit 0
$$ bend % --par
59
exit 0
$$ bend % --js
59
exit 0
