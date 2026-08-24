# the tail-loop retention class: each iteration takes one more handle
# off the shared tree, consumes it whole, and recurses -- sharing
# frees per iteration, nothing accumulates across 4096 rounds over a
# 63-node tree.
# ported from bend3: +Tree rides the Cop binder over Tree.copy, the
# counter becomes Nat; no interp lane (4096 structural-Word tree sums
# need minutes there)
import Base

type Tree:
  Lf{v: U32}
  Nd{a: Tree, b: Tree}

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
    case Nd{a, b}:
      ((ax, ae), (ay, af)) = Tree.copy(a)
      ((bx, be), (by, bf)) = Tree.copy(b)
      s10 = Equal.cong(Tree, Tree, z => Nd{z, b}, a, ax, ae)
      s11 = Equal.cong(Tree, Tree, z => Nd{ax, z}, b, bx, be)
      t11 = Equal.trans(Tree, Nd{a, b}, Nd{ax, b}, Nd{ax, bx}, s10, s11)
      s20 = Equal.cong(Tree, Tree, z => Nd{z, b}, a, ay, af)
      s21 = Equal.cong(Tree, Tree, z => Nd{ay, z}, b, by, bf)
      t21 = Equal.trans(Tree, Nd{a, b}, Nd{ay, b}, Nd{ay, by}, s20, s21)
      ((Nd{ax, bx}, t11), (Nd{ay, by}, t21))

assert gen:
  forall +d: +Nat
  forall +i: +U32
  Tree

def gen(d, i):
  match d:
    case 0n:
      Lf{i}
    case 1n+e:
      Nd{gen(e, U32.mul(i, 2)), gen(e, U32.add(U32.mul(i, 2), 1))}

assert sum:
  forall t: Tree
  U32

def sum(t):
  match t:
    case Lf{v}:
      v
    case Nd{a, b}:
      U32.add(sum(a), sum(b))

assert spin:
  forall n: Nat
  forall +t: +Tree
  forall acc: U32
  U32

def spin(n, t, acc):
  match n:
    case 0n:
      U32.add(acc, sum(t))
    case 1n+m:
      spin(m, t, U32.add(acc, sum(t)))

assert main.out:
  Nat

def main.out():
  U32.to_nat(spin(4096n, gen(5n, 1), 0))

assert main:
  IO(Unit)

def main():
  IO.print(String.append(Nat.show(main.out()), "n"))
$$ bend % --seq
6227440n
exit 0
$$ bend % --par
6227440n
exit 0
$$ bend % --js
6227440n
exit 0
