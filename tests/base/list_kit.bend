# the affine base List kit: get/set at Nat indexes (Maybe out, OOB set
# is a no-op), head/tail/is_empty edges, concat, and zip's pair walk --
# nine checks packed positionally into one U32
import Base

law List.length:
  for -a : Quant
  for -A : Kind(a)
  for xs : List<a, A>
  Nat

def List.length(a, A, xs):
  match xs:
    case Nil{}:
      0n
    case h <> t:
      1n+List.length(a, A, t)

law List.append:
  for -a : Quant
  for -A : Kind(a)
  for xs : List<a, A>
  for ys : List<a, A>
  List<a, A>

def List.append(a, A, xs, ys):
  match xs:
    case Nil{}:
      ys
    case h <> t:
      h <> List.append(a, A, t, ys)

law Maybe.default:
  for -a: Quant
  for -A: Kind(a)
  for  m: Maybe<a, A>
  for  d: A
  A

def Maybe.default(a, A, m, d):
  match m:
    case None{}:
      d
    case Some{x}:
      x

law List.is_empty:
  for -a : Quant
  for -A : Kind(a)
  for xs : List<a, A>
  Bool

def List.is_empty(a, A, xs):
  match xs:
    case Nil{}:
      True{}
    case h <> t:
      False{}

law List.head:
  for -a : Quant
  for -A : Kind(a)
  for xs : List<a, A>
  Maybe<a, A>

def List.head(a, A, xs):
  match xs:
    case Nil{}:
      None{}
    case h <> t:
      Some{h}

law List.tail:
  for -a : Quant
  for -A : Kind(a)
  for xs : List<a, A>
  List<a, A>

def List.tail(a, A, xs):
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      t

law List.get:
  for -a : Quant
  for -A : Kind(a)
  for n  : Nat
  for xs : List<a, A>
  Maybe<a, A>

def List.get(a, A, n, xs):
  match n xs:
    case 0n Nil{}:
      None{}
    case 0n h <> t:
      Some{h}
    case 1n+p Nil{}:
      None{}
    case 1n+p h <> t:
      List.get(a, A, p, t)

law List.set:
  for -a : Quant
  for -A : Kind(a)
  for n  : Nat
  for x  : A
  for xs : List<a, A>
  List<a, A>

def List.set(a, A, n, x, xs):
  match n xs:
    case 0n Nil{}:
      Nil{}
    case 0n h <> t:
      x <> t
    case 1n+p Nil{}:
      Nil{}
    case 1n+p h <> t:
      h <> List.set(a, A, p, x, t)

law List.concat:
  for -a  : Quant
  for -A  : Kind(a)
  for xss : List<a, List<a, A>>
  List<a, A>

def List.concat(a, A, xss):
  match xss:
    case Nil{}:
      Nil{}
    case h <> t:
      List.append(a, A, h, List.concat(a, A, t))

law List.zip:
  for -a : Quant
  for -A : Kind(a)
  for -b : Quant
  for -B : Kind(b)
  for xs : List<a, A>
  for ys : List<b, B>
  List<&1, A & B>

def List.zip(a, A, b, B, xs, ys):
  match xs ys:
    case Nil{} Nil{}:
      Nil{}
    case Nil{} h <> t:
      Nil{}
    case h <> t Nil{}:
      Nil{}
    case x <> xt y <> yt:
      (x, y) <> List.zip(a, A, b, B, xt, yt)

law bu:
  for b: Bool
  U32

def bu(b):
  match b:
    case False{}:
      0
    case True{}:
      1

law digit99:
  for m: Maybe<&2, U32>
  U32

def digit99(m):
  Maybe.default(&2, U32, m, 99)

law l4:
  List<&2, U32>

def l4():
  [10, 20, 30, 40]

law l2:
  List<&2, U32>

def l2():
  [1, 2]

law zsum:
  for xs: List<&1, U32 & U32>
  U32

def zsum(xs):
  match xs:
    case Nil{}:
      0
    case (x, y) <> t:
      U32.add(U32.add(x, y), zsum(t))

law nlen:
  for xs: List<&2, U32>
  U32

def nlen(xs):
  U32.from_nat(List.length(&2, U32, xs))

law main.out:
  U32

def main.out():
  b0 = bu(U32.is_eq(digit99(List.get(&2, U32, 2n, l4())), 30))
  b1 = bu(U32.is_eq(digit99(List.get(&2, U32, 7n, l4())), 99))
  b2 = bu(U32.is_eq(digit99(List.head(&2, U32, List.set(&2, U32, 0n, 5, l2()))), 5))
  b3 = bu(U32.is_eq(nlen(List.set(&2, U32, 5n, 9, l2())), 2))
  b4 = bu(U32.is_eq(nlen(List.concat(&2, U32, [[1], [2, 3]])), 3))
  b5 = bu(U32.is_eq(zsum(List.zip(&2, U32, &2, U32, [1, 2, 3], [4, 5])), 12))
  b6 = bu(U32.is_eq(digit99(List.head(&2, U32, List.tail(&2, U32, [7, 8]))), 8))
  b7 = bu(List.is_empty(&2, U32, Nil{}))
  b8 = bu(Bool.not(List.is_empty(&2, U32, l2())))
  d0 = U32.add(U32.mul(b0, 10), b1)
  d1 = U32.add(U32.mul(d0, 10), b2)
  d2 = U32.add(U32.mul(d1, 10), b3)
  d3 = U32.add(U32.mul(d2, 10), b4)
  d4 = U32.add(U32.mul(d3, 10), b5)
  d5 = U32.add(U32.mul(d4, 10), b6)
  d6 = U32.add(U32.mul(d5, 10), b7)
  U32.add(U32.mul(d6, 10), b8)

law main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))

#|111111111
