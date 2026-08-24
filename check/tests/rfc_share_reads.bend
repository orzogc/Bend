# a shared value read twice: each extra use of the + handle is a
# retain, every match unshares one layer, values stay exact -- the
# whole-tree double walk answers twice the single sum.
# ported from bend3: +Tree rides the Cop binder over Tree.copy. The
# csrc pins hold the segments to the SHARED path, where bend3 pinned
# sha_move/seq_sha_step: the Nd build seals its fields ref-counted
# (rfc_seal) and foo's second read of x is a keep (term_keep bumps
# the count -- nothing copied), never a clone.
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

assert bar:
  forall x: Tree
  U32

def bar(x):
  match x:
    case Lf{v}:
      v
    case Nd{a, b}:
      U32.add(bar(a), bar(b))

assert foo:
  forall +x: +Tree
  U32

def foo(x):
  a = bar(x)
  b = bar(x)
  U32.add(a, b)

assert main.out:
  Nat

def main.out():
  U32.to_nat(foo(gen(5n, 1)))

# csrc has: = rfc_seal(e, h_
# csrc has: = term_keep(e,

assert main:
  IO(Unit)

def main():
  IO.print(String.append(Nat.show(main.out()), "n"))
$$ bend %
3040n
$$ bend % --seq
3040n
exit 0
$$ bend % --par
3040n
exit 0
$$ bend % --js
3040n
exit 0
