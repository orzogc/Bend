# bend3 pinned numeric structural recursion (the miss branch of a
# 0-switch knows the scrutinee non-zero, so d - 1 descends). bend4's
# counter is Nat and the descent carries (e off 1n+e): a binary node
# spends the depth twice -- e in both children -- and the +Nat (Cop)
# binder licenses that copy, so the file checks strict and pins the
# generated tree's sum.
# ported from bend3: depth becomes Nat, the doubled binders +Nat, the
# fork sugar plain lets (the parallel pin lives in the rfc ports)
import Base

type Tree:
  Leaf{v: U32}
  Node{l: Tree, r: Tree}

assert gen:
  forall +d: +Nat
  forall +i: +U32
  Tree

def gen(d, i):
  match d:
    case 0n:
      Leaf{i}
    case 1n+e:
      Node{gen(e, U32.mul(i, 2)), gen(e, U32.add(U32.mul(i, 2), 1))}

assert sum:
  forall t: Tree
  U32

def sum(t):
  match t:
    case Leaf{v}:
      v
    case Node{l, r}:
      U32.add(sum(l), sum(r))

assert main.out:
  Nat

def main.out():
  U32.to_nat(sum(gen(4n, 0)))

assert main:
  IO(Unit)

def main():
  IO.print(String.append(Nat.show(main.out()), "n"))
$$ bend %
120n
$$ bend % --seq
120n
exit 0
$$ bend % --par
120n
exit 0
$$ bend % --js
120n
exit 0
