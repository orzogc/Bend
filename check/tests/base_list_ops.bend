# List pipelines: range/map/filter/fold, plus zip/reverse/head/tail/
# get/set/count/any/all. A recursive combinator cannot bind a closure
# (a function type owns no Copiable witness), so each map/filter/fold/
# any/all spells its worker inline as its own def; zip/reverse/head/
# tail/set stay generic. reg_closure_keep_generic pins the kept-binder
# residue at an erased type variable.
# ported from bend3: bend-base's List helpers are inlined over bend4's
# List (Nil/Con); indexes and range counters become Nat; list literals
# become explicit Con chains; the set and count continuation pairs
# fold into single defs (mutual defs cannot tie), and every doubled
# word wears +U32, a Cop
import Base

assert bu:
  forall b: Bool
  U32

def bu(b):
  match b:
    case False{}:
      0
    case True{}:
      1

assert sqr:
  forall +x: +U32
  U32

def sqr(x):
  U32.mul(x, x)

assert digest.go:
  forall xs: List<U32>
  forall acc: U32
  U32

def digest.go(xs, acc):
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      digest.go(t, U32.add(U32.mul(acc, 10), h))

assert digest:
  forall xs: List<U32>
  U32

def digest(xs):
  digest.go(xs, 0)

assert lmsq:
  forall xs: List<U32>
  List<U32>

def lmsq(xs):
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{sqr(h), lmsq(t)}

assert lminc:
  forall xs: List<U32>
  List<U32>

def lminc(xs):
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{U32.add(h, 1), lminc(t)}

assert lfodd:
  forall xs: List<U32>
  List<U32>

def lfodd(xs):
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      +h2 = {h : +U32}
      match Bool.not(U32.is_eq(U32.mod(h2, 2), 0)):
        case True{}:
          Con{h2, lfodd(t)}
        case False{}:
          lfodd(t)

assert lrange.go:
  forall +n: +Nat
  forall acc: List<U32>
  List<U32>

def lrange.go(n, acc):
  match n:
    case 0n:
      acc
    case 1n+p:
      lrange.go(p, Con{U32.from_nat(p), acc})

assert lrange:
  forall n: Nat
  List<U32>

def lrange(n):
  lrange.go(n, Nil{})

assert lsum:
  forall xs: List<U32>
  U32

def lsum(xs):
  match xs:
    case Nil{}:
      0
    case Con{h, t}:
      U32.add(h, lsum(t))

assert lrev.go:
  forall -A: Type
  forall xs: List<A>
  forall acc: List<A>
  List<A>

def lrev.go(A, xs, acc):
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      lrev.go(A, t, Con{h, acc})

assert lrev:
  forall -A: Type
  forall xs: List<A>
  List<A>

def lrev(A, xs):
  lrev.go(A, xs, Nil{})

assert lzip:
  forall -A: Type
  forall -B: Type
  forall xs: List<A>
  forall ys: List<B>
  List<(A & B)>

def lzip(A, B, xs, ys):
  match xs ys:
    case Nil{} Nil{}:
      Nil{}
    case Nil{} Con{h, t}:
      Nil{}
    case Con{h, t} Nil{}:
      Nil{}
    case Con{h1, t1} Con{h2, t2}:
      Con{(h1, h2), lzip(A, B, t1, t2)}

assert llen:
  forall -A: Type
  forall xs: List<A>
  U32

def llen(A, xs):
  match xs:
    case Nil{}:
      0
    case Con{h, t}:
      U32.add(1, llen(A, t))

assert lhead:
  forall -A: Type
  forall d: A
  forall xs: List<A>
  A

def lhead(A, d, xs):
  match xs:
    case Nil{}:
      d
    case Con{h, t}:
      h

assert ltail:
  forall -A: Type
  forall xs: List<A>
  List<A>

def ltail(A, xs):
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      t

assert lset.z:
  forall -A: Type
  forall v: A
  forall xs: List<A>
  List<A>

def lset.z(A, v, xs):
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{v, t}

assert lset:
  forall -A: Type
  forall i: Nat
  forall v: A
  forall xs: List<A>
  List<A>

def lset(A, i, v, xs):
  match i:
    case 0n:
      lset.z(A, v, xs)
    case 1n+p:
      match xs:
        case Nil{}:
          Nil{}
        case Con{h, t}:
          Con{h, lset(A, p, v, t)}

assert lcount:
  forall +x: +U32
  forall xs: List<U32>
  U32

def lcount(x, xs):
  match xs:
    case Nil{}:
      0
    case Con{h, t}:
      match U32.is_eq(h, x):
        case True{}:
          U32.add(1, lcount(x, t))
        case False{}:
          lcount(x, t)

assert lany4:
  forall xs: List<U32>
  Bool

def lany4(xs):
  match xs:
    case Nil{}:
      False{}
    case Con{h, t}:
      match U32.is_gt(h, 4):
        case True{}:
          True{}
        case False{}:
          lany4(t)

assert lall0:
  forall xs: List<U32>
  Bool

def lall0(xs):
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      match U32.is_gt(h, 0):
        case True{}:
          lall0(t)
        case False{}:
          False{}

assert main.out:
  U32

def main.out():
  b0 = bu(U32.is_eq(digest(lrange(5n)), 1234))
  b1 = bu(U32.is_eq(digest(lmsq(Con{1, Con{2, Con{3, Nil{}}}})), 149))
  b2 = bu(U32.is_eq(digest(lfodd(Con{1, Con{2, Con{3, Con{4, Con{5, Nil{}}}}}})), 135))
  b3 = bu(U32.is_eq(lsum(lminc(lrange(4n))), 10))
  b4 = bu(U32.is_eq(digest(lrev(U32, Con{1, Con{2, Con{3, Nil{}}}})), 321))
  b5 = bu(U32.is_eq(llen((U32 & U32), lzip(U32, U32, Con{1, Con{2, Con{3, Nil{}}}}, Con{4, Con{5, Nil{}}})), 2))
  b6 = bu(U32.is_eq(lhead(U32, 99, Con{7, Con{8, Nil{}}}), 7))
  b7 = bu(U32.is_eq(digest(ltail(U32, Con{7, Con{8, Con{9, Nil{}}}})), 89))
  b8 = bu(U32.is_eq(digest(lset(U32, 1n, 5, Con{1, Con{2, Con{3, Nil{}}}})), 153))
  b9 = bu(U32.is_eq(lcount(2, Con{2, Con{1, Con{2, Con{2, Nil{}}}}}), 3))
  b10 = bu(lany4(Con{1, Con{5, Nil{}}}))
  b11 = bu(lall0(Con{1, Con{5, Nil{}}}))
  U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(b0, b1), b2), b3), b4), b5), b6), b7), b8), b9), b10), b11)

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
12
$$ bend % --seq
12
exit 0
$$ bend % --par
12
exit 0
$$ bend % --js
12
exit 0
