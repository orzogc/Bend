# fork shapes per the GUIDE: a width-2 tree, a width-4 burst and a width-8
# burst in ONE statement each; T=1 execution pins the joined result
# ported from bend3: `a & b = x & y` forks become Par<> Both destructures,
# tree depth becomes Nat, the shared index a +U32 (Cop) binder
import Base

assert leaf:
  forall +i: +U32
  U32

def leaf(i):
  U32.add(U32.mul(i, i), 1)

assert tree:
  forall +d: +Nat
  forall +i: +U32
  U32

def tree(d, i):
  match d:
    case 0n:
      leaf(i)
    case 1n+p:
      Both{a, b} = {Both{tree(p, U32.mul(i, 2)), tree(p, U32.add(U32.mul(i, 2), 1))} : Par<U32, U32>}
      U32.add(a, b)

assert burst4:
  forall +i: +U32
  U32

def burst4(i):
  Both{a, Both{b, Both{c, d}}} = {Both{leaf(i), Both{leaf(U32.add(i, 1)), Both{leaf(U32.add(i, 2)), leaf(U32.add(i, 3))}}} : Par<U32, Par<U32, Par<U32, U32>>>}
  U32.add(U32.add(U32.add(a, b), c), d)

assert burst8:
  forall +i: +U32
  U32

def burst8(i):
  Both{a, Both{b, Both{c, Both{d, Both{e, Both{f, Both{g, h}}}}}}} = {Both{leaf(i), Both{leaf(U32.add(i, 1)), Both{leaf(U32.add(i, 2)), Both{leaf(U32.add(i, 3)), Both{leaf(U32.add(i, 4)), Both{leaf(U32.add(i, 5)), Both{leaf(U32.add(i, 6)), leaf(U32.add(i, 7))}}}}}}} : Par<U32, Par<U32, Par<U32, Par<U32, Par<U32, Par<U32, Par<U32, U32>>>>>>>}
  U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(a, b), c), d), e), f), g), h)

assert main.out:
  U32

def main.out():
  U32.add(U32.add(U32.mul(tree(3n, 0), 10000), U32.mul(burst4(1), 100)), burst8(1))

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
1483612
$$ bend % --seq
1483612
exit 0
$$ bend % --par
1483612
exit 0
$$ bend % --js
1483612
exit 0
