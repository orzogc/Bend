# a lambda owns what it captures: a def that uses its argument AND
# returns a lambda that also uses it -- the closure owns its instance,
# the original dies in make's body. Pre-fix (bend3) this read freed
# memory when main applied f.
# ported from bend3: the doubled tree takes a +Tree Cop binder over
# the local Tree.copy witness, depth rides Nat, the answer reads back
# via U32.to_nat
import Base

type Tree:
  Lf{v: U32}
  Nd{l: Tree, r: Tree}

assert Tree.copy:
  forall t: Tree
  Copy(Tree, t) & Copy(Tree, t)

def Tree.copy(t):
  match t:
    case Lf{v}:
      ((vx, ve), (vy, vf)) = U32.copy(v)
      s10 = Equal.cong(U32, Tree, z => Lf{z}, v, vx, ve)
      s20 = Equal.cong(U32, Tree, z => Lf{z}, v, vy, vf)
      ((Lf{vx}, s10), (Lf{vy}, s20))
    case Nd{l, r}:
      ((lx, le), (ly, lf)) = Tree.copy(l)
      ((rx, re), (ry, rf)) = Tree.copy(r)
      s10 = Equal.cong(Tree, Tree, z => Nd{z, r}, l, lx, le)
      s11 = Equal.cong(Tree, Tree, z => Nd{lx, z}, r, rx, re)
      t11 = Equal.trans(Tree, Nd{l, r}, Nd{lx, r}, Nd{lx, rx}, s10, s11)
      s20 = Equal.cong(Tree, Tree, z => Nd{z, r}, l, ly, lf)
      s21 = Equal.cong(Tree, Tree, z => Nd{ly, z}, r, ry, rf)
      t21 = Equal.trans(Tree, Nd{l, r}, Nd{ly, r}, Nd{ly, ry}, s20, s21)
      ((Nd{lx, rx}, t11), (Nd{ly, ry}, t21))

assert build:
  forall +d: +Nat
  forall +x: +U32
  Tree

def build(d, x):
  match d:
    case 0n:
      Lf{x}
    case 1n+e:
      Nd{build(e, U32.add(x, x)), build(e, U32.add(U32.add(x, x), 1))}

assert tsum:
  forall t: Tree
  U32

def tsum(t):
  match t:
    case Lf{v}:
      v
    case Nd{l, r}:
      U32.add(tsum(l), tsum(r))

assert make:
  forall +x: +Tree
  Unit -> U32

def make(x):
  a = tsum(x)
  u => U32.add(a, tsum(x))

assert main.out:
  Nat

def main.out():
  t = build(3n, 1)
  f = make(t)
  U32.to_nat(f(Unit{}))

assert main:
  IO(Unit)

def main():
  IO.print(String.append(Nat.show(main.out()), "n"))
$$ bend %
184n
$$ bend % --seq
184n
exit 0
$$ bend % --par
184n
exit 0
$$ bend % --js
184n
exit 0
