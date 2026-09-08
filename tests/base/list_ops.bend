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
# word binds + (U32 is Data)
import Base

law bu:
  for b: Bool
  U32

def bu(b):
  match b:
    case False{}:
      0
    case True{}:
      1

law sqr:
  for +x: U32
  U32

def sqr(x):
  U32.mul(x, x)

law digest.go:
  for xs  : List<&2, U32>
  for acc : U32
  U32

def digest.go(xs, acc):
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      digest.go(t, U32.add(U32.mul(acc, 10), h))

law digest:
  for xs: List<&2, U32>
  U32

def digest(xs):
  digest.go(xs, 0)

law lmsq:
  for xs: List<&2, U32>
  List<&2, U32>

def lmsq(xs):
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{sqr(h), lmsq(t)}

law lminc:
  for xs: List<&2, U32>
  List<&2, U32>

def lminc(xs):
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{U32.add(h, 1), lminc(t)}

law lfodd.put:
  for h2 : U32
  for r  : List<&2, U32>
  for f  : Bool
  List<&2, U32>

def lfodd.put(h2, r, f):
  match f:
    case True{}:
      Con{h2, r}
    case False{}:
      r

law lfodd:
  for xs: List<&2, U32>
  List<&2, U32>

def lfodd(xs):
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      +h2 = h
      lfodd.put(h2, lfodd(t), Bool.not(U32.is_eq(U32.mod(h2, 2), 0)))

law lrange.go:
  for +n  : Nat
  for acc : List<&2, U32>
  List<&2, U32>

def lrange.go(n, acc):
  match n:
    case 0n:
      acc
    case 1n+p:
      lrange.go(p, Con{U32.from_nat(p), acc})

law lrange:
  for n: Nat
  List<&2, U32>

def lrange(n):
  lrange.go(n, Nil{})

law lsum:
  for xs: List<&2, U32>
  U32

def lsum(xs):
  match xs:
    case Nil{}:
      0
    case Con{h, t}:
      U32.add(h, lsum(t))

law lrev.go:
  for -a  : Quant
  for -A  : Kind(a)
  for xs  : List<a, A>
  for acc : List<a, A>
  List<a, A>

def lrev.go(a, A, xs, acc):
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      lrev.go(a, A, t, Con{h, acc})

law lrev:
  for -a : Quant
  for -A : Kind(a)
  for xs : List<a, A>
  List<a, A>

def lrev(a, A, xs):
  lrev.go(a, A, xs, Nil{})

law lzip:
  for -a : Quant
  for -A : Kind(a)
  for -b : Quant
  for -B : Kind(b)
  for xs : List<a, A>
  for ys : List<b, B>
  List<&1, A & B>

def lzip(a, A, b, B, xs, ys):
  match xs ys:
    case Nil{} Nil{}:
      Nil{}
    case Nil{} Con{h, t}:
      Nil{}
    case Con{h, t} Nil{}:
      Nil{}
    case Con{h1, t1} Con{h2, t2}:
      Con{(h1, h2), lzip(a, A, b, B, t1, t2)}

law llen:
  for -a : Quant
  for -A : Kind(a)
  for xs : List<a, A>
  U32

def llen(a, A, xs):
  match xs:
    case Nil{}:
      0
    case Con{h, t}:
      U32.add(1, llen(a, A, t))

law lhead:
  for -a : Quant
  for -A : Kind(a)
  for d  : A
  for xs : List<a, A>
  A

def lhead(a, A, d, xs):
  match xs:
    case Nil{}:
      d
    case Con{h, t}:
      h

law ltail:
  for -a : Quant
  for -A : Kind(a)
  for xs : List<a, A>
  List<a, A>

def ltail(a, A, xs):
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      t

law lset.z:
  for -a : Quant
  for -A : Kind(a)
  for v  : A
  for xs : List<a, A>
  List<a, A>

def lset.z(a, A, v, xs):
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{v, t}

law lset:
  for -a : Quant
  for -A : Kind(a)
  for i  : Nat
  for v  : A
  for xs : List<a, A>
  List<a, A>

def lset(a, A, i, v, xs):
  match i:
    case 0n:
      lset.z(a, A, v, xs)
    case 1n+p:
      match xs:
        case Nil{}:
          Nil{}
        case Con{h, t}:
          Con{h, lset(a, A, p, v, t)}

law lcount:
  for +x : U32
  for xs : List<&2, U32>
  U32

def lcount(x, xs):
  match xs:
    case Nil{}:
      0
    case Con{h, t}:
      U32.add(bu(U32.is_eq(h, x)), lcount(x, t))

law lany4.put:
  for f: Bool
  for r: Bool
  Bool

def lany4.put(f, r):
  match f:
    case True{}:
      True{}
    case False{}:
      r

law lany4:
  for xs: List<&2, U32>
  Bool

def lany4(xs):
  match xs:
    case Nil{}:
      False{}
    case Con{h, t}:
      lany4.put(U32.is_gt(h, 4), lany4(t))

law lall0.put:
  for f: Bool
  for r: Bool
  Bool

def lall0.put(f, r):
  match f:
    case True{}:
      r
    case False{}:
      False{}

law lall0:
  for xs: List<&2, U32>
  Bool

def lall0(xs):
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      lall0.put(U32.is_gt(h, 0), lall0(t))

law main.out:
  U32

def main.out():
  b0 = bu(U32.is_eq(digest(lrange(5n)), 1234))
  b1 = bu(U32.is_eq(digest(lmsq(Con{1, Con{2, Con{3, Nil{}}}})), 149))
  b2 = bu(U32.is_eq(digest(lfodd(Con{1, Con{2, Con{3, Con{4, Con{5, Nil{}}}}}})), 135))
  b3 = bu(U32.is_eq(lsum(lminc(lrange(4n))), 10))
  b4 = bu(U32.is_eq(digest(lrev(&2, U32, Con{1, Con{2, Con{3, Nil{}}}})), 321))
  b5 = bu(U32.is_eq(llen(&1, (U32 & U32), lzip(&2, U32, &2, U32, Con{1, Con{2, Con{3, Nil{}}}}, Con{4, Con{5, Nil{}}})), 2))
  b6 = bu(U32.is_eq(lhead(&2, U32, 99, Con{7, Con{8, Nil{}}}), 7))
  b7 = bu(U32.is_eq(digest(ltail(&2, U32, Con{7, Con{8, Con{9, Nil{}}}})), 89))
  b8 = bu(U32.is_eq(digest(lset(&2, U32, 1n, 5, Con{1, Con{2, Con{3, Nil{}}}})), 153))
  b9 = bu(U32.is_eq(lcount(2, Con{2, Con{1, Con{2, Con{2, Nil{}}}}}), 3))
  b10 = bu(lany4(Con{1, Con{5, Nil{}}}))
  b11 = bu(lall0(Con{1, Con{5, Nil{}}}))
  U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(b0, b1), b2), b3), b4), b5), b6), b7), b8), b9), b10), b11)

law main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))

#|12
