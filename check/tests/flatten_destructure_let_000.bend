# destructuring let: `Ctr{..} = v` is a one-case match; on a param var it
# refines the column in place, on a computed value it opens a with-group
# ported from bend3: local Pair renamed (base owns the def name), and
# the word literals become params (a U32 literal shows as its Word chain)
import Base

type Duo:
  P{a: U32, b: U32}

assert swap:
  forall p: Duo
  Duo

def swap(p):
  P{a, b} = p
  P{b, a}

assert mk:
  forall n: U32
  forall o: U32
  Duo

def mk(n, o):
  P{n, o}

assert go:
  forall n: U32
  forall o: U32
  forall k: U32
  U32

def go(n, o, k):
  P{a, b} = mk(n, o)
  (a * k) + b

assert main:
  forall p: Duo
  forall k: U32
  U32

def main(p, k):
  P{x, y} = swap(p)
  (x * k) + y
$$ bend % --show
swap = \{P: (a => b => P{b, a})}
mk = n => o => P{n, o}
go = n => o => k => \{P: (a => b => U32.add(U32.mul(a, k), b))}(mk(n, o))
main = p => k => \{P: (x => y => U32.add(U32.mul(x, k), y))}(swap(p))
