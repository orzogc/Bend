# regression witness (bc040b8 lineage): a KEPT Array binder answers
# through the copy-on-write, both aliases whole -- bc040b8 walled this
# shape loud; the ARR turns replaced the wall with the real cow. The
# kept binder rides the local Arr.copy witness, strict.
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

assert rd:
  forall a: Array<U32>
  U32

def rd(a):
  match a:
    case ALeaf{x}:
      x
    case ANode{xs, ys}:
      U32.add(rd(xs), rd(ys))

assert main.out:
  U32

def main.out():
  +a = {ANode{ANode{ALeaf{1}, ALeaf{2}}, ANode{ALeaf{3}, ALeaf{4}}} : (+ Array<U32> ~ Arr.copy)}
  (b, old) = Array.swap(U32, a, 2, 50)
  U32.add(rd(b), U32.add(rd(a), old))

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
70
$$ bend % --seq
70
exit 0
$$ bend % --par
70
exit 0
$$ bend % --js
70
exit 0
