# THE PROOF IDIOM: an arm's field feeds the IH, a lemma premise and the
# goal -- the one-field-many-premises shape bend3's Data contraction
# existed to type. bend4 core is affine for every type, so the many
# spends ride a + scrutinee licensed by the local N.copy witness (the
# honest respell of Data's checker-planted copies), strict. The value
# block runs the program.
# ported from bend3: rewrites carry explicit motives and fold right into
# left, so plus_succ is stated with the eliminated term on the right;
# the numeric nat(n) match becomes U32.to_nat + Nat recursion
import Base

type N:
  Z{}
  S{p: N}

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

assert plus:
  forall a: N
  forall b: N
  N

def plus(a, b):
  match a:
    case Z{}:
      b
    case S{ap}:
      S{plus(ap, b)}

assert double:
  forall n: N
  N

def double(n):
  match n:
    case Z{}:
      Z{}
    case S{p}:
      S{S{double(p)}}

assert plus_succ:
  forall a: N
  forall -b: N
  {S{plus(a, b)} == plus(a, S{b}) : N}

def plus_succ(a, b):
  match a:
    case Z{}:
      {==}
    case S{ap}:
      %plus_succ(ap, b) : {S{S{plus(ap, b)}} == S{_} : N}
      {==}

assert double_plus:
  forall +n: +N
  {double(n) == plus(n, n) : N}

def double_plus(n):
  match n:
    case Z{}:
      {==}
    case S{p}:
      %plus_succ(p, p) : {S{S{double(p)}} == S{_} : N}
      %double_plus(p) : {S{S{double(p)}} == S{S{_}} : N}
      {==}

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
  val(double(nat(10)))

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
20
$$ bend % --seq
20
exit 0
$$ bend % --par
20
exit 0
$$ bend % --js
20
exit 0
