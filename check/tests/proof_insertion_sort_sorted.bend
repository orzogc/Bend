# FLAGSHIP: certified insertion sort, strict. The comparator returns an
# evidence SUM (LEOr), so the proof matches the same ordering fact the
# program branched on; SortedB carries the lower bound as an
# accumulator, making the insert lemma's IH fit exactly. Proved:
# sortedness + length preservation.
# ported from bend3: bend3's elaborator specialized a computed-match
# goal in place and its dec/insert pair was mutual; bend4
# passes the recursive result INTO dec, so the pair untangles, and each
# proof replays insert's dispatch through a framed match whose motive
# keeps dec folded over the cell -- the arms then specialize and the IH
# sits in the OG arm, a direct structural self-call. List.copy is the
# honest Copiable(List<Nat>) witness carrying the double spends
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

assert LE:
  forall a: Nat
  forall b: Nat
  Type

def LE(a, b):
  match a:
    case 0n:
      Unit
    case 1n+a1:
      match b:
        case 0n:
          Empty
        case 1n+b1:
          LE(a1, b1)

type LEOr<-x: Nat, -h: Nat>:
  OL{e: LE(x, h)}
  OG{e: LE(h, x)}

assert le_case:
  forall x: Nat
  forall h: Nat
  LEOr<x, h>

def le_case(x, h):
  match x, h:
    case 0n, 0n:
      OL{Unit{}}
    case 0n, 1n+b:
      OL{Unit{}}
    case 1n+a, 0n:
      OG{Unit{}}
    case 1n+a, 1n+b:
      match le_case(a, b):
        case OL{e}:
          OL{e}
        case OG{e}:
          OG{e}

assert List.copy:
  forall -c: Copiable(Nat)
  forall t: List<Nat>
  Copy(List<Nat>, t) & Copy(List<Nat>, t)

def List.copy(c, t):
  match t:
    case Nil{}:
      ((Nil{}, {==}), (Nil{}, {==}))
    case Con{h, tl}:
      ((hx, he), (hy, hf)) = Nat.copy(h)
      ((tx, te), (ty, tf)) = List.copy(c, tl)
      s10 = Equal.cong(Nat, List<Nat>, z => Con{z, tl}, h, hx, he)
      s11 = Equal.cong(List<Nat>, List<Nat>, z => Con{hx, z}, tl, tx, te)
      t11 = Equal.trans(List<Nat>, Con{h, tl}, Con{hx, tl}, Con{hx, tx}, s10, s11)
      s20 = Equal.cong(Nat, List<Nat>, z => Con{z, tl}, h, hy, hf)
      s21 = Equal.cong(List<Nat>, List<Nat>, z => Con{hy, z}, tl, ty, tf)
      t21 = Equal.trans(List<Nat>, Con{h, tl}, Con{hy, tl}, Con{hy, ty}, s20, s21)
      ((Con{hx, tx}, t11), (Con{hy, ty}, t21))

assert dec:
  forall x: Nat
  forall h: Nat
  forall t: List<Nat>
  forall r: List<Nat>
  forall c: LEOr<x, h>
  List<Nat>

def dec(x, h, t, r, c):
  match c:
    case OL{e}:
      Con{x, Con{h, t}}
    case OG{e}:
      Con{h, r}

assert insert:
  forall +x: +Nat
  forall +xs: +List<Nat>
  List<Nat>

def insert(x, xs):
  match xs:
    case Nil{}:
      Con{x, Nil{}}
    case Con{h, t}:
      dec(x, h, t, insert(x, t), le_case(x, h))

assert isort:
  forall xs: List<Nat>
  List<Nat>

def isort(xs):
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      insert(h, isort(t))

assert SortedB:
  forall xs: List<Nat>
  forall lo: Nat
  Type

def SortedB(xs, lo):
  match xs:
    case Nil{}:
      Unit
    case Con{h, t}:
      (LE(lo, h) & SortedB(t, h))

assert sorted_ins:
  forall xs: List<Nat>
  forall -lo: Nat
  forall +x: +Nat
  forall sx: SortedB(xs, lo)
  forall lx: LE(lo, x)
  SortedB(insert(x, xs), lo)

def sorted_ins(xs, lo, x, sx, lx):
  match xs:
    case Nil{}:
      (lx, Unit{})
    case Con{h, t}:
      (lh, st) = sx
      match c : LEOr<x, h> = le_case(x, h):
        case OL{e}:
          (lx, e, st)
        case OG{e}:
          (lh, sorted_ins(t, h, x, st, e))
        return SortedB(dec(x, h, t, insert(x, t), c), lo)

assert sorted_isort:
  forall +xs: +List<Nat>
  SortedB(isort(xs), 0n)

def sorted_isort(xs):
  match xs:
    case Nil{}:
      Unit{}
    case Con{h, t}:
      sorted_ins(isort(t), 0n, h, sorted_isort(t), Unit{})

assert len_ins:
  forall +x: +Nat
  forall xs: List<Nat>
  {1n+List.length(Nat, xs) == List.length(Nat, insert(x, xs)) : Nat}

def len_ins(x, xs):
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      match c : LEOr<x, h> = le_case(x, h):
        case OL{e}:
          {==}
        case OG{e}:
          %len_ins(x, t) : {2n+List.length(Nat, t) == 1n+_ : Nat}
          {==}
        return {1n+List.length(Nat, Con{h, t}) == List.length(Nat, dec(x, h, t, insert(x, t), c)) : Nat}

assert len_isort:
  forall +xs: +List<Nat>
  {List.length(Nat, isort(xs)) == List.length(Nat, xs) : Nat}

def len_isort(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      %len_ins(h, isort(t)) : {_ == 1n+List.length(Nat, t) : Nat}
      %len_isort(t) : {1n+List.length(Nat, isort(t)) == 1n+_ : Nat}
      {==}

assert s:
  List<Nat>

def s(): isort(Con{2n, Con{0n, Con{1n, Nil{}}}})

assert main:
  List<Nat>

def main(): s()
$$ bend %
Con{0n, Con{1n, Con{2n, Nil{}}}}
