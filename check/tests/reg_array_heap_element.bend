# regression witness (2ff58c0): an Array of heap-owning elements keeps
# tag, cid and RFC bit through the round trip -- the flat lane once
# packed every element into a u32 cell, so a two-constructor element
# came back as a bare loc and every match fell into the last arm. The
# shared read rides the local Cell/Arr copy witnesses, strict.
import Base

type Cell:
  CA{v: U32}
  CB{}

assert Cell.copy:
  forall c: Cell
  Copy(Cell, c) & Copy(Cell, c)

def Cell.copy(c):
  match c:
    case CA{v}:
      ((vx, ve), (vy, vf)) = U32.copy(v)
      e1 = Equal.cong(U32, Cell, z => CA{z}, v, vx, ve)
      e2 = Equal.cong(U32, Cell, z => CA{z}, v, vy, vf)
      ((CA{vx}, e1), (CA{vy}, e2))
    case CB{}:
      ((CB{}, {==}), (CB{}, {==}))

assert Arr.copy:
  forall -c: Copiable(Cell)
  forall t: Array<Cell>
  Copy(Array<Cell>, t) & Copy(Array<Cell>, t)

def Arr.copy(c, t):
  match t:
    case ALeaf{x}:
      ((xx, xe), (xy, xf)) = Cell.copy(x)
      e1 = Equal.cong(Cell, Array<Cell>, z => ALeaf{z}, x, xx, xe)
      e2 = Equal.cong(Cell, Array<Cell>, z => ALeaf{z}, x, xy, xf)
      ((ALeaf{xx}, e1), (ALeaf{xy}, e2))
    case ANode{xs, ys}:
      ((ax, ae), (ay, af)) = Arr.copy(c, xs)
      ((bx, be), (by, bf)) = Arr.copy(c, ys)
      s10 = Equal.cong(Array<Cell>, Array<Cell>, z => ANode{z, ys}, xs, ax, ae)
      s11 = Equal.cong(Array<Cell>, Array<Cell>, z => ANode{ax, z}, ys, bx, be)
      t11 = Equal.trans(Array<Cell>, ANode{xs, ys}, ANode{ax, ys}, ANode{ax, bx}, s10, s11)
      s20 = Equal.cong(Array<Cell>, Array<Cell>, z => ANode{z, ys}, xs, ay, af)
      s21 = Equal.cong(Array<Cell>, Array<Cell>, z => ANode{ay, z}, ys, by, bf)
      t21 = Equal.trans(Array<Cell>, ANode{xs, ys}, ANode{ay, ys}, ANode{ay, by}, s20, s21)
      ((ANode{ax, bx}, t11), (ANode{ay, by}, t21))

assert cw:
  forall c: Cell
  U32

def cw(c):
  match c:
    case CA{v}:
      v
    case CB{}:
      100

assert csum:
  forall a: Array<Cell>
  U32

def csum(a):
  match a:
    case ALeaf{x}:
      cw(x)
    case ANode{xs, ys}:
      U32.add(csum(xs), csum(ys))

assert mkc:
  Array<Cell>

def mkc():
  ANode{ANode{ALeaf{CA{7}}, ALeaf{CB{}}}, ANode{ALeaf{CA{30}}, ALeaf{CB{}}}}

assert shared:
  forall +a: (+ Array<Cell> ~ Arr.copy(Cell.copy))
  U32

def shared(a):
  U32.add(csum(a), csum(a))

assert main.out:
  U32

def main.out():
  (b, old) = Array.swap(Cell, mkc(), 1, CA{5})
  U32.add(csum(b), U32.add(cw(old), shared(mkc())))

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
716
$$ bend % --seq
716
exit 0
$$ bend % --par
716
exit 0
$$ bend % --js
716
exit 0
