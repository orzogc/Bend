# FLAGSHIP: list algebra over the Base accumulator reverse, generic
# over element types -- the reverse.go/append lemma tower up to
# reverse(append a b) = append(reverse b, reverse a) and the reverse
# involution, plus map-over-append at a concrete lambda literal.
# ported from bend3: List.concat/reverse_go become base List.append/
# List.reverse.go; every rewrite carries an explicit motive, and each
# lemma is stated with the term its callers eliminate on the right
# (cat_nil, rgo_cat and rev_cat_go flip); map is local (+f) and the
# double spends ride Cop binders over erased Copiable witnesses --
# dotted or named, dead at formation -- so the tower checks strict;
# check instantiates rev_rev with the honest List.copy(U32.copy)
import Base

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

assert cat_nil:
  forall -A: Type
  forall xs: List<A>
  {xs == List.append(A, xs, Nil{}) : List<A>}

def cat_nil(A, xs):
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      %cat_nil(A, t) : {Con{h, t} == Con{h, _} : List<A>}
      {==}

assert cat_assoc:
  forall -A: Type
  forall a: List<A>
  forall b: List<A>
  forall c: List<A>
  {List.append(A, List.append(A, a, b), c) == List.append(A, a, List.append(A, b, c)) : List<A>}

def cat_assoc(A, a, b, c):
  match a:
    case Nil{}:
      {==}
    case Con{h, t}:
      %cat_assoc(A, t, b, c) : {Con{h, List.append(A, List.append(A, t, b), c)} == Con{h, _} : List<A>}
      {==}

assert rgo_cat:
  forall -A: Type
  forall -w: Copiable(List<A>)
  forall +xs: (+ List<A> ~ w)
  forall +acc: (+ List<A> ~ w)
  {List.append(A, List.reverse.go(A, xs, Nil{}), acc) == List.reverse.go(A, xs, acc) : List<A>}

def rgo_cat(A, w, xs, acc):
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      %rgo_cat(A, w, t, Con{h, acc}) : {List.append(A, List.reverse.go(A, t, Con{h, Nil{}}), acc) == _ : List<A>}
      %rgo_cat(A, w, t, Con{h, Nil{}}) : {List.append(A, _, acc) == List.append(A, List.reverse.go(A, t, Nil{}), Con{h, acc}) : List<A>}
      %cat_assoc(A, List.reverse.go(A, t, Nil{}), Con{h, Nil{}}, acc) : {List.append(A, List.append(A, List.reverse.go(A, t, Nil{}), Con{h, Nil{}}), acc) == _ : List<A>}
      {==}

assert rev_cat_go:
  forall -A: Type
  forall -w: Copiable(List<A>)
  forall +a: (+ List<A> ~ w)
  forall +b: (+ List<A> ~ w)
  {List.append(A, List.reverse.go(A, b, Nil{}), List.reverse.go(A, a, Nil{})) == List.reverse.go(A, List.append(A, a, b), Nil{}) : List<A>}

def rev_cat_go(A, w, a, b):
  match a:
    case Nil{}:
      rgo_cat(A, w, b, Nil{})
    case Con{h, t}:
      %rgo_cat(A, w, List.append(A, t, b), Con{h, Nil{}}) : {List.append(A, List.reverse.go(A, b, Nil{}), List.reverse.go(A, t, Con{h, Nil{}})) == _ : List<A>}
      %rev_cat_go(A, w, t, b) : {List.append(A, List.reverse.go(A, b, Nil{}), List.reverse.go(A, t, Con{h, Nil{}})) == List.append(A, _, Con{h, Nil{}}) : List<A>}
      %rgo_cat(A, w, t, Con{h, Nil{}}) : {List.append(A, List.reverse.go(A, b, Nil{}), _) == List.append(A, List.append(A, List.reverse.go(A, b, Nil{}), List.reverse.go(A, t, Nil{})), Con{h, Nil{}}) : List<A>}
      %cat_assoc(A, List.reverse.go(A, b, Nil{}), List.reverse.go(A, t, Nil{}), Con{h, Nil{}}) : {_ == List.append(A, List.append(A, List.reverse.go(A, b, Nil{}), List.reverse.go(A, t, Nil{})), Con{h, Nil{}}) : List<A>}
      {==}

assert rev_cat:
  forall -A: Type
  forall -w: Copiable(List<A>)
  forall +a: (+ List<A> ~ w)
  forall +b: (+ List<A> ~ w)
  {List.append(A, List.reverse(A, b), List.reverse(A, a)) == List.reverse(A, List.append(A, a, b)) : List<A>}

def rev_cat(A, w, a, b):
  rev_cat_go(A, w, a, b)

assert rev_rev:
  forall -A: Type
  forall -w: Copiable(List<A>)
  forall +a: (+ List<A> ~ w)
  {List.reverse(A, List.reverse(A, a)) == a : List<A>}

def rev_rev(A, w, a):
  match a:
    case Nil{}:
      {==}
    case Con{h, t}:
      %rgo_cat(A, w, t, Con{h, Nil{}}) : {List.reverse.go(A, _, Nil{}) == Con{h, t} : List<A>}
      %rev_cat_go(A, w, List.reverse.go(A, t, Nil{}), Con{h, Nil{}}) : {_ == Con{h, t} : List<A>}
      %rev_rev(A, w, t) : {List.append(A, Con{h, Nil{}}, List.reverse.go(A, List.reverse.go(A, t, Nil{}), Nil{})) == Con{h, _} : List<A>}
      {==}

assert map:
  forall -A: Type
  forall -B: Type
  forall -f.copy: Copiable(A -> B)
  forall +f: (+ (A -> B) ~ f.copy)
  forall xs: List<A>
  List<B>

def map(A, B, f.copy, f, xs):
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{f(h), map(A, B, f.copy, f, t)}

assert map_cat:
  forall -mw: Copiable(U32 -> U32)
  forall -lw: Copiable(List<U32>)
  forall +a: (+ List<U32> ~ lw)
  forall b: List<U32>
  {map(U32, U32, mw, x => U32.add(x, 1), List.append(U32, a, b)) == List.append(U32, map(U32, U32, mw, x => U32.add(x, 1), a), map(U32, U32, mw, x => U32.add(x, 1), b)) : List<U32>}

def map_cat(mw, lw, a, b):
  match a:
    case Nil{}:
      {==}
    case Con{h, t}:
      %map_cat(mw, lw, t, b) : {Con{U32.add(h, 1), map(U32, U32, mw, x => U32.add(x, 1), List.append(U32, t, b))} == Con{U32.add(h, 1), _} : List<U32>}
      {==}

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

assert check:
  {List.reverse(U32, List.reverse(U32, Con{1, Con{2, Con{3, Nil{}}}})) == Con{1, Con{2, Con{3, Nil{}}}} : List<U32>}

def check(): rev_rev(U32, List.copy(U32.copy), Con{1, Con{2, Con{3, Nil{}}}})

assert main:
  {List.reverse(U32, List.reverse(U32, Con{1, Con{2, Con{3, Nil{}}}})) == Con{1, Con{2, Con{3, Nil{}}}} : List<U32>}

def main(): check()
$$ bend %
{==}
