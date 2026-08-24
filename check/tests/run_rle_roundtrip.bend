# run-length encoding: list -> (count, value) pairs -> expanded back;
# the round trip is the pin
# ported from bend3: bend-base's List helpers are inlined over bend4's
# List (Nil/Con); strict -- the run and expand helpers folded into
# their callers' case trees, the shared code list a + binder over a
# local list-of-pairs Copy witness
import Base

assert Pair.copy:
  forall -c1: Copiable(U32)
  forall -c2: Copiable(U32)
  forall t: U32 & U32
  Copy(U32 & U32, t) & Copy(U32 & U32, t)

def Pair.copy(c1, c2, t):
  (a, b) = t
  ((ax, ae), (ay, af)) = U32.copy(a)
  ((bx, be), (by, bf)) = U32.copy(b)
  s10 = Equal.cong(U32, U32 & U32, z => (z, b), a, ax, ae)
  s11 = Equal.cong(U32, U32 & U32, z => (ax, z), b, bx, be)
  t11 = Equal.trans(U32 & U32, (a, b), (ax, b), (ax, bx), s10, s11)
  s20 = Equal.cong(U32, U32 & U32, z => (z, b), a, ay, af)
  s21 = Equal.cong(U32, U32 & U32, z => (ay, z), b, by, bf)
  t21 = Equal.trans(U32 & U32, (a, b), (ay, b), (ay, by), s20, s21)
  (((ax, bx), t11), ((ay, by), t21))

assert Listp.copy:
  forall -c: Copiable(U32 & U32)
  forall t: List<(U32 & U32)>
  Copy(List<(U32 & U32)>, t) & Copy(List<(U32 & U32)>, t)

def Listp.copy(c, t):
  match t:
    case Nil{}:
      ((Nil{}, {==}), (Nil{}, {==}))
    case Con{h, tl}:
      ((hx, he), (hy, hf)) = Pair.copy(U32.copy, U32.copy, h)
      ((tx, te), (ty, tf)) = Listp.copy(c, tl)
      s10 = Equal.cong(U32 & U32, List<(U32 & U32)>, z => Con{z, tl}, h, hx, he)
      s11 = Equal.cong(List<(U32 & U32)>, List<(U32 & U32)>, z => Con{hx, z}, tl, tx, te)
      t11 = Equal.trans(List<(U32 & U32)>, Con{h, tl}, Con{hx, tl}, Con{hx, tx}, s10, s11)
      s20 = Equal.cong(U32 & U32, List<(U32 & U32)>, z => Con{z, tl}, h, hy, hf)
      s21 = Equal.cong(List<(U32 & U32)>, List<(U32 & U32)>, z => Con{hy, z}, tl, ty, tf)
      t21 = Equal.trans(List<(U32 & U32)>, Con{h, tl}, Con{hy, tl}, Con{hy, ty}, s20, s21)
      ((Con{hx, tx}, t11), (Con{hy, ty}, t21))

assert bu:
  forall b: Bool
  U32

def bu(b):
  match b:
    case False{}:
      0
    case True{}:
      1

assert lconcat:
  forall xs: List<U32>
  forall ys: List<U32>
  List<U32>

def lconcat(xs, ys):
  match xs:
    case Nil{}:
      ys
    case Con{h, t}:
      Con{h, lconcat(t, ys)}

assert lrepeat:
  forall n: Nat
  forall +v: +U32
  List<U32>

def lrepeat(n, v):
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      Con{v, lrepeat(p, v)}

assert lrevp.go:
  forall xs: List<(U32 & U32)>
  forall acc: List<(U32 & U32)>
  List<(U32 & U32)>

def lrevp.go(xs, acc):
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      lrevp.go(t, Con{h, acc})

assert lrevp:
  forall xs: List<(U32 & U32)>
  List<(U32 & U32)>

def lrevp(xs):
  lrevp.go(xs, Nil{})

assert llenp:
  forall xs: List<(U32 & U32)>
  U32

def llenp(xs):
  match xs:
    case Nil{}:
      0
    case Con{h, t}:
      U32.add(1, llenp(t))

assert rle:
  forall xs: List<U32>
  forall +cur: +U32
  forall n: U32
  forall acc: List<(U32 & U32)>
  List<(U32 & U32)>

def rle(xs, cur, n, acc):
  match xs:
    case Nil{}:
      lrevp(Con{(n, cur), acc})
    case Con{h0, t}:
      +h = {h0 : +U32}
      match U32.is_eq(h, cur):
        case False{}:
          rle(t, h, 1, Con{(n, cur), acc})
        case True{}:
          rle(t, cur, U32.add(n, 1), acc)

assert expand:
  forall ps: List<(U32 & U32)>
  List<U32>

def expand(ps):
  match ps:
    case Nil{}:
      Nil{}
    case Con{(n, v), t}:
      lconcat(lrepeat(U32.to_nat(n), v), expand(t))

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

assert go:
  forall xs: List<U32>
  U32

def go(xs):
  match xs:
    case Con{h, t}:
      +code = {rle(t, h, 1, Nil{}) : (+ List<(U32 & U32)> ~ Listp.copy(Pair.copy(U32.copy, U32.copy)))}
      U32.add(U32.mul(bu(U32.is_eq(llenp(code), 3)), 10), bu(U32.is_eq(digest(expand(code)), 777299)))
    case Nil{}:
      0

assert main.out:
  U32

def main.out():
  go(Con{7, Con{7, Con{7, Con{2, Con{9, Con{9, Nil{}}}}}}})

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
11
$$ bend % --seq
11
exit 0
$$ bend % --par
11
exit 0
$$ bend % --js
11
exit 0
