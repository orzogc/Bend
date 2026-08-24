# a pure main through every backend, fork tree included: the built
# binary prints the result word and exits 0.
# ported from bend3: the fork depth becomes Nat fuel (bend4 has no
# word patterns), `a & b = x & y` becomes the Par<> Both destructure,
# shared binders take +Nat/+U32 (Cop); bend3's result-word exit code
# is bend3 CLI behavior -- bend4 binaries print and exit 0
import Base

assert leaf:
  forall +i: +U32
  U32

def leaf(i):
  U32.mul(i, i)

assert tree:
  forall +d: +Nat
  forall +i: +U32
  U32

def tree(d, i):
  match d:
    case 0n:
      leaf(i)
    case 1n+e:
      Both{a, b} = {Both{tree(e, U32.mul(i, 2)), tree(e, U32.add(U32.mul(i, 2), 1))} : Par<U32, U32>}
      U32.add(a, b)

assert main.out:
  U32

def main.out():
  tree(3n, 1)

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
1100
$$ bend % --seq
1100
exit 0
$$ bend % --par
1100
exit 0
$$ bend % --js
1100
exit 0
