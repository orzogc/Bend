# bend3's gen_church miniature: an open-closure compose chain under
# binders. Its checker counter is gone (no --stats); the pipeline
# itself carries whole and answers on every lane
import Base

assert comp:
  forall f: U32 -> U32
  forall g: U32 -> U32
  U32 -> U32

def comp(f, g):
  x => f(g(x))

assert c0:
  forall k: U32
  U32 -> U32

def c0(k):
  comp(x => x + 0, x => x + k)

assert c1:
  forall k: U32
  U32 -> U32

def c1(k):
  comp(x => x + 1, c0(k))

assert c2:
  forall k: U32
  U32 -> U32

def c2(k):
  comp(x => x + 2, c1(k))

assert c3:
  forall k: U32
  U32 -> U32

def c3(k):
  comp(x => x + 3, c2(k))

assert ap:
  forall f: U32 -> U32
  forall x: U32
  U32

def ap(f, x):
  f(x)

assert main.out:
  Nat

def main.out():
  U32.to_nat(ap(c3(4), 10))

assert main:
  IO(Unit)

def main():
  IO.print(String.append(Nat.show(main.out()), "n"))
$$ bend %
20n
$$ bend % --seq
20n
exit 0
$$ bend % --par
20n
exit 0
$$ bend % --js
20n
exit 0
