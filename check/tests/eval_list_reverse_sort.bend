# base List: reverse is involutive and an insertion sort orders (dupes
# kept) on concrete lists -- closed by conversion alone, no output.
# ported from bend3: list literals become Con/Nil spines, bend3-base
# List.sort becomes a local insertion sort (bend4 base has none); the
# compare-and-rebuild double use takes + Cop binders over a local
# List.copy witness
import Base

assert List.copy:
  forall -c: Copiable(U32)
  forall t: List<U32>
  Copy(List<U32>, t) & Copy(List<U32>, t)

def List.copy(c, t):
  match t:
    case Nil{}:
      ((Nil{}, {==}), (Nil{}, {==}))
    case Con{h, tl}:
      ((hx, he), (hy, hf)) = U32.copy(h)
      ((tx, te), (ty, tf)) = List.copy(c, tl)
      s10 = Equal.cong(U32, List<U32>, z => Con{z, tl}, h, hx, he)
      s11 = Equal.cong(List<U32>, List<U32>, z => Con{hx, z}, tl, tx, te)
      t11 = Equal.trans(List<U32>, Con{h, tl}, Con{hx, tl}, Con{hx, tx}, s10, s11)
      s20 = Equal.cong(U32, List<U32>, z => Con{z, tl}, h, hy, hf)
      s21 = Equal.cong(List<U32>, List<U32>, z => Con{hy, z}, tl, ty, tf)
      t21 = Equal.trans(List<U32>, Con{h, tl}, Con{hy, tl}, Con{hy, ty}, s20, s21)
      ((Con{hx, tx}, t11), (Con{hy, ty}, t21))

assert List.reverse.go:
  forall -A: Type
  forall xs: List<A>
  forall acc: List<A>
  List<A>

def List.reverse.go(A, xs, acc):
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      List.reverse.go(A, t, Con{h, acc})

assert List.reverse:
  forall -A: Type
  forall xs: List<A>
  List<A>

def List.reverse(A, xs):
  List.reverse.go(A, xs, Nil{})

assert l123:
  List<U32>

def l123():
  Con{1, Con{2, Con{3, Nil{}}}}

assert l321:
  List<U32>

def l321():
  Con{3, Con{2, Con{1, Nil{}}}}

assert insert:
  forall +x: +U32
  forall +xs: (+ List<U32> ~ List.copy(U32.copy))
  List<U32>

def insert(x, xs):
  match xs:
    case Nil{}:
      Con{x, Nil{}}
    case Con{h, t}:
      match U32.is_le(x, h):
        case True{}:
          Con{x, Con{h, t}}
        case False{}:
          Con{h, insert(x, t)}

assert sort:
  forall xs: List<U32>
  List<U32>

def sort(xs):
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      insert(h, sort(t))

assert rev:
  {List.reverse(U32, l123) == l321 : List<U32>}

def rev():
  {==}

assert rev2:
  {List.reverse(U32, List.reverse(U32, l123)) == l123 : List<U32>}

def rev2():
  {==}

assert srt:
  {sort(Con{3, Con{1, Con{2, Con{3, Nil{}}}}}) == Con{1, Con{2, Con{3, Con{3, Nil{}}}}} : List<U32>}

def srt():
  {==}
$$ bend %

