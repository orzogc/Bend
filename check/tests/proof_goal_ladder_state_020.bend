# goal ladder, tower state 1 (after the rgo_cat rewrite at Con{h, acc}).
# ported from bend3: the ladder rides the ported bend4 development, so
# the pinned page is bend4's own goal at the same proof state
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
      Type
$$ bend %
Error:
- expected : {List.append(A, List.reverse.go(A, t, Con{h, Nil{}}), acc) == List.append(A, List.reverse.go(A, t, Nil{}), Con{h, acc}) : List<A>}
- observed : Type
Context:
- A   : Type
- w   : @x:List<A> -> &_:(&y:List<A> -> {x == y : List<A>}) -> &y:List<A> -> {x == y : List<A>}
- h   : A
- t   : List<A>
- acc : +List<A> ~ w
Location: rgo_cat
59 |       %rgo_cat(A, w, t, Con{h, acc}) : {List.append(A, List.reverse.go(A, t, Con{h, Nil{}}), acc) == _ : List<A>}
60>|       Type
61 |
