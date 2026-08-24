# the affine base List kit: get/set at Nat indexes (Maybe out, OOB set
# is a no-op), head/tail/is_empty edges, concat, and zip's pair walk --
# nine checks packed positionally into one U32
import Base

assert List.length:
  forall -A: Type
  forall xs: List<A>
  Nat

def List.length(A, xs):
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      1n+List.length(A, t)

assert List.append:
  forall -A: Type
  forall xs: List<A>
  forall ys: List<A>
  List<A>

def List.append(A, xs, ys):
  match xs:
    case Nil{}:
      ys
    case Con{h, t}:
      Con{h, List.append(A, t, ys)}

assert Maybe.default:
  forall -A: Type
  forall m: Maybe<A>
  forall d: A
  A

def Maybe.default(A, m, d):
  match m:
    case None{}:
      d
    case Some{x}:
      x

assert List.is_empty:
  forall -A: Type
  forall xs: List<A>
  Bool

def List.is_empty(A, xs):
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      False{}

assert List.head:
  forall -A: Type
  forall xs: List<A>
  Maybe<A>

def List.head(A, xs):
  match xs:
    case Nil{}:
      None{}
    case Con{h, t}:
      Some{h}

assert List.tail:
  forall -A: Type
  forall xs: List<A>
  List<A>

def List.tail(A, xs):
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      t

assert List.get:
  forall -A: Type
  forall n: Nat
  forall xs: List<A>
  Maybe<A>

def List.get(A, n, xs):
  match n xs:
    case 0n Nil{}:
      None{}
    case 0n Con{h, t}:
      Some{h}
    case 1n+p Nil{}:
      None{}
    case 1n+p Con{h, t}:
      List.get(A, p, t)

assert List.set:
  forall -A: Type
  forall n: Nat
  forall x: A
  forall xs: List<A>
  List<A>

def List.set(A, n, x, xs):
  match n xs:
    case 0n Nil{}:
      Nil{}
    case 0n Con{h, t}:
      Con{x, t}
    case 1n+p Nil{}:
      Nil{}
    case 1n+p Con{h, t}:
      Con{h, List.set(A, p, x, t)}

assert List.concat:
  forall -A: Type
  forall xss: List<List<A>>
  List<A>

def List.concat(A, xss):
  match xss:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      List.append(A, h, List.concat(A, t))

assert List.zip:
  forall -A: Type
  forall -B: Type
  forall xs: List<A>
  forall ys: List<B>
  List<(A & B)>

def List.zip(A, B, xs, ys):
  match xs ys:
    case Nil{} Nil{}:
      Nil{}
    case Nil{} Con{h, t}:
      Nil{}
    case Con{h, t} Nil{}:
      Nil{}
    case Con{a, at} Con{b, bt}:
      Con{(a, b), List.zip(A, B, at, bt)}

assert bu:
  forall b: Bool
  U32

def bu(b):
  match b:
    case False{}:
      0
    case True{}:
      1

assert digit99:
  forall m: Maybe<U32>
  U32

def digit99(m):
  Maybe.default(U32, m, 99)

assert l4:
  List<U32>

def l4():
  Con{10, Con{20, Con{30, Con{40, Nil{}}}}}

assert l2:
  List<U32>

def l2():
  Con{1, Con{2, Nil{}}}

assert zsum:
  forall xs: List<(U32 & U32)>
  U32

def zsum(xs):
  match xs:
    case Nil{}:
      0
    case Con{(x, y), t}:
      U32.add(U32.add(x, y), zsum(t))

assert nlen:
  forall xs: List<U32>
  U32

def nlen(xs):
  U32.from_nat(List.length(U32, xs))

assert main.out:
  U32

def main.out():
  b0 = bu(U32.is_eq(digit99(List.get(U32, 2n, l4())), 30))
  b1 = bu(U32.is_eq(digit99(List.get(U32, 7n, l4())), 99))
  b2 = bu(U32.is_eq(digit99(List.head(U32, List.set(U32, 0n, 5, l2()))), 5))
  b3 = bu(U32.is_eq(nlen(List.set(U32, 5n, 9, l2())), 2))
  b4 = bu(U32.is_eq(nlen(List.concat(U32, Con{Con{1, Nil{}}, Con{Con{2, Con{3, Nil{}}}, Nil{}}})), 3))
  b5 = bu(U32.is_eq(zsum(List.zip(U32, U32, Con{1, Con{2, Con{3, Nil{}}}}, Con{4, Con{5, Nil{}}})), 12))
  b6 = bu(U32.is_eq(digit99(List.head(U32, List.tail(U32, Con{7, Con{8, Nil{}}}))), 8))
  b7 = bu(List.is_empty(U32, Nil{}))
  b8 = bu(Bool.not(List.is_empty(U32, l2())))
  d0 = U32.add(U32.mul(b0, 10), b1)
  d1 = U32.add(U32.mul(d0, 10), b2)
  d2 = U32.add(U32.mul(d1, 10), b3)
  d3 = U32.add(U32.mul(d2, 10), b4)
  d4 = U32.add(U32.mul(d3, 10), b5)
  d5 = U32.add(U32.mul(d4, 10), b6)
  d6 = U32.add(U32.mul(d5, 10), b7)
  U32.add(U32.mul(d6, 10), b8)

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
111111111
$$ bend % --seq
111111111
exit 0
$$ bend % --par
111111111
exit 0
$$ bend % --js
111111111
exit 0
