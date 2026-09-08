# FLAGSHIP: list algebra over the Base accumulator reverse, generic
# over element types -- the reverse.go/append lemma tower up to
# reverse(append a b) = append(reverse b, reverse a) and the reverse
# involution, plus map-over-append at a concrete named function.
# ported from bend3: List.concat/reverse_go become base List.append/
# List.reverse.go; every rewrite carries an explicit motive, and each
# lemma is stated with the term its callers eliminate on the right
# (cat_nil, rgo_cat and rev_cat_go flip); the element type is Data so
# List<&2, A> is Data and the double spends ride plain + binders; map
# rides a named inc (a function is never +), so the tower checks strict;
# check instantiates rev_rev at U32
import Base

law List.append:
  for -A : Data
  for xs : List<&2, A>
  for ys : List<&2, A>
  List<&2, A>

def List.append(A, xs, ys):
  match xs:
    case Nil{}:
      ys
    case Con{h, t}:
      Con{h, List.append(A, t, ys)}

law List.reverse.go:
  for -A  : Data
  for xs  : List<&2, A>
  for acc : List<&2, A>
  List<&2, A>

def List.reverse.go(A, xs, acc):
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      List.reverse.go(A, t, Con{h, acc})

law List.reverse:
  for -A : Data
  for xs : List<&2, A>
  List<&2, A>

def List.reverse(A, xs):
  List.reverse.go(A, xs, Nil{})

law cat_nil:
  for -A : Data
  for xs : List<&2, A>
  {xs == List.append(A, xs, Nil{}) : List<&2, A>}

def cat_nil(A, xs):
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      %cat_nil(A, t) : {Con{h, t} == Con{h, _} : List<&2, A>}
      {==}

law cat_assoc:
  for -A: Data
  for  a: List<&2, A>
  for  b: List<&2, A>
  for  c: List<&2, A>
  {List.append(A, List.append(A, a, b), c) == List.append(A, a, List.append(A, b, c)) : List<&2, A>}

def cat_assoc(A, a, b, c):
  match a:
    case Nil{}:
      {==}
    case Con{h, t}:
      %cat_assoc(A, t, b, c) : {Con{h, List.append(A, List.append(A, t, b), c)} == Con{h, _} : List<&2, A>}
      {==}

law rgo_cat:
  for -A   : Data
  for +xs  : List<&2, A>
  for +acc : List<&2, A>
  {List.append(A, List.reverse.go(A, xs, Nil{}), acc) == List.reverse.go(A, xs, acc) : List<&2, A>}

def rgo_cat(A, xs, acc):
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      %rgo_cat(A, t, Con{h, acc}) : {List.append(A, List.reverse.go(A, t, Con{h, Nil{}}), acc) == _ : List<&2, A>}
      %rgo_cat(A, t, Con{h, Nil{}}) : {List.append(A, _, acc) == List.append(A, List.reverse.go(A, t, Nil{}), Con{h, acc}) : List<&2, A>}
      %cat_assoc(A, List.reverse.go(A, t, Nil{}), Con{h, Nil{}}, acc) : {List.append(A, List.append(A, List.reverse.go(A, t, Nil{}), Con{h, Nil{}}), acc) == _ : List<&2, A>}
      {==}

law rev_cat_go:
  for -A: Data
  for +a: List<&2, A>
  for +b: List<&2, A>
  {List.append(A, List.reverse.go(A, b, Nil{}), List.reverse.go(A, a, Nil{})) == List.reverse.go(A, List.append(A, a, b), Nil{}) : List<&2, A>}

def rev_cat_go(A, a, b):
  match a:
    case Nil{}:
      rgo_cat(A, b, Nil{})
    case Con{h, t}:
      %rgo_cat(A, List.append(A, t, b), Con{h, Nil{}}) : {List.append(A, List.reverse.go(A, b, Nil{}), List.reverse.go(A, t, Con{h, Nil{}})) == _ : List<&2, A>}
      %rev_cat_go(A, t, b) : {List.append(A, List.reverse.go(A, b, Nil{}), List.reverse.go(A, t, Con{h, Nil{}})) == List.append(A, _, Con{h, Nil{}}) : List<&2, A>}
      %rgo_cat(A, t, Con{h, Nil{}}) : {List.append(A, List.reverse.go(A, b, Nil{}), _) == List.append(A, List.append(A, List.reverse.go(A, b, Nil{}), List.reverse.go(A, t, Nil{})), Con{h, Nil{}}) : List<&2, A>}
      %cat_assoc(A, List.reverse.go(A, b, Nil{}), List.reverse.go(A, t, Nil{}), Con{h, Nil{}}) : {_ == List.append(A, List.append(A, List.reverse.go(A, b, Nil{}), List.reverse.go(A, t, Nil{})), Con{h, Nil{}}) : List<&2, A>}
      {==}

law rev_cat:
  for -A: Data
  for +a: List<&2, A>
  for +b: List<&2, A>
  {List.append(A, List.reverse(A, b), List.reverse(A, a)) == List.reverse(A, List.append(A, a, b)) : List<&2, A>}

def rev_cat(A, a, b):
  rev_cat_go(A, a, b)

law rev_rev:
  for -A: Data
  for +a: List<&2, A>
  {List.reverse(A, List.reverse(A, a)) == a : List<&2, A>}

def rev_rev(A, a):
  match a:
    case Nil{}:
      {==}
    case Con{h, t}:
      %rgo_cat(A, t, Con{h, Nil{}}) : {List.reverse.go(A, _, Nil{}) == Con{h, t} : List<&2, A>}
      %rev_cat_go(A, List.reverse.go(A, t, Nil{}), Con{h, Nil{}}) : {_ == Con{h, t} : List<&2, A>}
      %rev_rev(A, t) : {List.append(A, Con{h, Nil{}}, List.reverse.go(A, List.reverse.go(A, t, Nil{}), Nil{})) == Con{h, _} : List<&2, A>}
      {==}

law inc:
  for x: U32
  U32

def inc(x):
  U32.add(x, 1)

law map_inc:
  for xs: List<&2, U32>
  List<&2, U32>

def map_inc(xs):
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{inc(h), map_inc(t)}

law map_cat:
  for +a: List<&2, U32>
  for  b: List<&2, U32>
  {map_inc(List.append(U32, a, b)) == List.append(U32, map_inc(a), map_inc(b)) : List<&2, U32>}

def map_cat(a, b):
  match a:
    case Nil{}:
      {==}
    case Con{h, t}:
      %map_cat(t, b) : {Con{inc(h), map_inc(List.append(U32, t, b))} == Con{inc(h), _} : List<&2, U32>}
      {==}

law check:
  {List.reverse(U32, List.reverse(U32, Con{1, Con{2, Con{3, Nil{}}}})) == Con{1, Con{2, Con{3, Nil{}}}} : List<&2, U32>}

def check(): rev_rev(U32, Con{1, Con{2, Con{3, Nil{}}}})

law main:
  {List.reverse(U32, List.reverse(U32, Con{1, Con{2, Con{3, Nil{}}}})) == Con{1, Con{2, Con{3, Nil{}}}} : List<&2, U32>}

def main(): check()

#|{==}
