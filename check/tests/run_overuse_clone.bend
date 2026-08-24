# over-use at runtime: a Tree consumed by two different walks, a WORD
# used three times, and a bare Data binder used twice -- identical
# results on every lane
# ported from bend3: bend3's checker-planted deep copies become explicit
# + Cop binders over the local Tree.copy witness (bend4 core has no
# implicit duplication);
# the bend3 `--eval --stats` block is bend3-only and is dropped
import Base

type Tree:
  TL{v: U32}
  TN{a: Tree, b: Tree}

assert Tree.copy:
  forall t: Tree
  Copy(Tree, t) & Copy(Tree, t)

def Tree.copy(t):
  match t:
    case TL{v}:
      ((vx, ve), (vy, vf)) = U32.copy(v)
      s10 = Equal.cong(U32, Tree, z => TL{z}, v, vx, ve)
      s20 = Equal.cong(U32, Tree, z => TL{z}, v, vy, vf)
      ((TL{vx}, s10), (TL{vy}, s20))
    case TN{a, b}:
      ((ax, ae), (ay, af)) = Tree.copy(a)
      ((bx, be), (by, bf)) = Tree.copy(b)
      s10 = Equal.cong(Tree, Tree, z => TN{z, b}, a, ax, ae)
      s11 = Equal.cong(Tree, Tree, z => TN{ax, z}, b, bx, be)
      t11 = Equal.trans(Tree, TN{a, b}, TN{ax, b}, TN{ax, bx}, s10, s11)
      s20 = Equal.cong(Tree, Tree, z => TN{z, b}, a, ay, af)
      s21 = Equal.cong(Tree, Tree, z => TN{ay, z}, b, by, bf)
      t21 = Equal.trans(Tree, TN{a, b}, TN{ay, b}, TN{ay, by}, s20, s21)
      ((TN{ax, bx}, t11), (TN{ay, by}, t21))

assert tsum:
  forall t: Tree
  U32

def tsum(t):
  match t:
    case TL{v}:
      v
    case TN{a, b}:
      U32.add(tsum(a), tsum(b))

assert depth.go:
  forall +d: +U32
  forall +e: +U32
  U32

def depth.go(d, e):
  match U32.is_gt(d, e):
    case True{}:
      U32.add(d, 1)
    case False{}:
      U32.add(e, 1)

assert depth:
  forall t: Tree
  U32

def depth(t):
  match t:
    case TL{v}:
      0
    case TN{a, b}:
      depth.go(depth(a), depth(b))

assert both:
  forall +t: +Tree
  U32

def both(t):
  U32.add(U32.mul(tsum(t), 10), depth(t))

assert wshare:
  forall x: U32
  forall +s: +U32
  U32

def wshare(x, s):
  U32.add(U32.add(U32.add(x, s), s), s)

assert main.out:
  U32

def main.out():
  t = {TN{TN{TL{1}, TL{2}}, TN{TL{3}, TN{TL{4}, TL{5}}}} : Tree}
  a = both(t)
  +u = {TN{TL{6}, TL{7}} : +Tree}
  b = U32.add(tsum(u), tsum(u))
  U32.add(U32.add(U32.mul(a, 100), b), wshare(1, 2))

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
15333
$$ bend % --seq
15333
exit 0
$$ bend % --par
15333
exit 0
$$ bend % --js
15333
exit 0
