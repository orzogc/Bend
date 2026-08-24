# audit 002 inverted, carried: bend3's Lone binder of Data type could be
# spent at any live quantity through the planted deep copy. bend4 spells
# the same clone as twin's +x binder licensed by the local N.copy
# witness, strict, and the block proves the clone semantics end-to-end:
# both copies of the tree are consumed independently.
# ported from bend3: the numeric nat(n) match becomes U32.to_nat + Nat
# recursion; ctor names bare and unique (Nat -> N, Pair -> Pr5)
import Base

type N:
  Z{}
  S{p: N}
type Pr5:
  MkPr5{a: N, b: N}

assert N.copy:
  forall n: N
  Copy(N, n) & Copy(N, n)

def N.copy(n):
  match n:
    case Z{}:
      ((Z{}, {==}), (Z{}, {==}))
    case S{p}:
      ((px, pe), (py, pf)) = N.copy(p)
      s10 = Equal.cong(N, N, z => S{z}, p, px, pe)
      s20 = Equal.cong(N, N, z => S{z}, p, py, pf)
      ((S{px}, s10), (S{py}, s20))

assert twin:
  forall +x: +N
  Pr5

def twin(x):
  MkPr5{x, x}

assert nat.go:
  forall m: Nat
  N

def nat.go(m):
  match m:
    case Zero{}:
      Z{}
    case Succ{q}:
      S{nat.go(q)}

assert nat:
  forall k: U32
  N

def nat(k):
  nat.go(U32.to_nat(k))

assert val:
  forall x: N
  U32

def val(x):
  match x:
    case Z{}:
      0
    case S{p}:
      1 + val(p)

assert main.out:
  U32

def main.out():
  match twin(nat(21)):
    case MkPr5{a, b}:
      val(a) + val(b)

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
42
$$ bend % --seq
42
exit 0
$$ bend % --par
42
exit 0
$$ bend % --js
42
exit 0
