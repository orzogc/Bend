# two forked walks consume ONE shared tree across threads: the fork
# siblings each take a counted handle, their matches unshare layer by
# layer, and the last consumer frees. Values exact under 8 threads.
# ported from bend3: the & fork sugar spells the Par<> Both
# destructure, +Tree the Cop binder over Tree.copy; no interp lane (the
# structural Word evaluator overflows its host stack on the 1024-leaf
# double walk)
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
      Both{l, r} = {Both{gen(e, U32.mul(i, 2)), gen(e, U32.add(U32.mul(i, 2), 1))} : Par<Tree, Tree>}
      Nd{l, r}

assert sum:
  forall t: Tree
  U32

def sum(t):
  match t:
    case Lf{v}:
      v
    case Nd{a, b}:
      Both{x, y} = {Both{sum(a), sum(b)} : Par<U32, U32>}
      U32.add(x, y)

assert two:
  forall +t: +Tree
  U32

def two(t):
  Both{a, b} = {Both{sum(t), sum(t)} : Par<U32, U32>}
  U32.add(a, b)

assert main.out:
  Nat

def main.out():
  U32.to_nat(two(gen(10n, 1)))

assert main:
  IO(Unit)

def main():
  IO.print(String.append(Nat.show(main.out()), "n"))
$$ bend % --seq
3144704n
exit 0
$$ bend % --par
3144704n
exit 0
$$ bend % --js
3144704n
exit 0
