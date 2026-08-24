# drop-driven collection on shared values: peek reads only the left
# spine of the shared tree (the right children drop), and waste never
# uses its tree argument at all -- a whole-value drop. Values exact.
# ported from bend3: the +Tree ascription becomes a + let (bend4's +
# is a Cop binder over the local Tree.copy witness, not a type),
# depth rides Nat
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

assert peek:
  forall t: Tree
  U32

def peek(t):
  match t:
    case Lf{v}:
      v
    case Nd{a, b}:
      peek(a)

assert waste:
  forall t: Tree
  forall x: U32
  U32

def waste(t, x):
  x

assert main.out:
  Nat

def main.out():
  +t = {gen(5n, 1) : +Tree}
  a = peek(t)
  b = waste(t, 7)
  U32.to_nat(U32.add(a, b))

assert main:
  IO(Unit)

def main():
  IO.print(String.append(Nat.show(main.out()), "n"))
$$ bend %
39n
$$ bend % --seq
39n
exit 0
$$ bend % --par
39n
exit 0
$$ bend % --js
39n
exit 0
