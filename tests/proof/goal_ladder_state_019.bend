# goal ladder, Base reverse.go/append tower, cons state 0.
# ported from bend3: the ladder rides the ported bend4 development, so
# the pinned page is bend4's own goal at the same proof state
import Base

law List.append:
  for -A: Data
  for xs: List<&2, A>
  for ys: List<&2, A>
  List<&2, A>

def List.append(A, xs, ys):
  match xs:
    case Nil{}:
      ys
    case Con{h, t}:
      Con{h, List.append(A, t, ys)}

law List.reverse.go:
  for -A: Data
  for xs: List<&2, A>
  for acc: List<&2, A>
  List<&2, A>

def List.reverse.go(A, xs, acc):
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      List.reverse.go(A, t, Con{h, acc})

law cat_assoc:
  for -A: Data
  for a: List<&2, A>
  for b: List<&2, A>
  for c: List<&2, A>
  {List.append(A, List.append(A, a, b), c) == List.append(A, a, List.append(A, b, c)) : List<&2, A>}

def cat_assoc(A, a, b, c):
  match a:
    case Nil{}:
      {==}
    case Con{h, t}:
      %cat_assoc(A, t, b, c) : {Con{h, List.append(A, List.append(A, t, b), c)} == Con{h, _} : List<&2, A>}
      {==}

law rgo_cat:
  for -A: Data
  for +xs: List<&2, A>
  for +acc: List<&2, A>
  {List.append(A, List.reverse.go(A, xs, Nil{}), acc) == List.reverse.go(A, xs, acc) : List<&2, A>}

def rgo_cat(A, xs, acc):
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      Type

#|Error:
#|- expected : {List.append(A, List.reverse.go(A, t, Con{h, Nil{}}), acc) == List.reverse.go(A, t, Con{h, acc}) : List<&2, A>}
#|- observed : Type
#|Context:
#|- A   : Data
#|- h   : A
#|- t   : List<&2, A>
#|- acc : List<&2, A>
#|Location: rgo_cat
#|57 |     case Con{h, t}:
#|58>|       Type
#|59 |
#|exit 1
