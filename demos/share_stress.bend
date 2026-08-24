#[halts]
import Base
# RC + fork stress: every path of the sharing runtime in one small
# program. build forks its halves (a parallel-let of whole task calls);
# tri shares one heap tree THREE ways and consumes each pointer
# differently (two destructive folds and a shallow probe), so
# redirectors mint, bump, open by shallow copy and collapse; dropper
# shares and then drops one pointer (the count path); nest re-shares a
# shared tree through a helper (redirector bump, no second redirector);
# cow shares an Array, swaps through one pointer and reads both (the
# copy-on-write path). Expected: 23561 = 23441 + 120, verified against
# the interpreter and byte-stable across 1 and 8 threads (the census
# fail-stops on any lost or doubled owner).

type Tr:
  L{v: U32}
  N{a: Tr, b: Tr}

assert build:
  forall +d: Nat
  forall +x: U32
  Tr

def build(d, x):
  match d:
    case 0n:
      L{x}
    case 1n+p:
      Both{a, b} = {Both{build(p, U32.mul(x, 2)), build(p, U32.add(U32.mul(x, 2), 1))} : Par<Tr, Tr>}
      N{a, b}

assert sum:
  forall t: Tr
  U32

def sum(t):
  match t:
    case L{v}:
      v
    case N{a, b}:
      Both{x, y} = {Both{sum(a), sum(b)} : Par<U32, U32>}
      U32.add(x, y)

assert depth:
  forall t: Tr
  U32

def depth(t):
  match t:
    case L{v}:
      0
    case N{a, b}:
      match U32.is_gt(depth(a), depth(b)):
        case True{}:
          1
        case False{}:
          1

assert tri:
  forall +t: Tr
  U32

def tri(t):
  U32.add(sum(t), U32.add(sum(t), depth(t)))

assert dropper:
  forall +t: Tr
  U32

def dropper(t):
  x = sum(t)
  y = t
  x

assert helper:
  forall +u: Tr
  U32

def helper(u):
  U32.add(sum(u), sum(u))

assert nest:
  forall +t: Tr
  U32

def nest(t):
  U32.add(helper(t), helper(t))

assert mk:
  Array<U32>

def mk():
  ANode{ANode{ALeaf{1}, ALeaf{2}}, ANode{ALeaf{3}, ALeaf{4}}}

assert rd:
  forall a: Array<U32>
  U32

def rd(a):
  match a:
    case ALeaf{x}:
      x
    case ANode{xs, ys}:
      U32.add(rd(xs), rd(ys))

assert cow:
  forall +a: Array<U32>
  U32

def cow(a):
  (b, old) = Array.swap(U32, a, 0, 100)
  U32.add(rd(b), U32.add(rd(a), old))

assert main.out:
  U32

def main.out():
  p = tri(build(6n, 1))
  q = dropper(build(5n, 3))
  r = nest(build(4n, 7))
  U32.add(U32.add(p, U32.add(q, r)), cow(mk()))

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
