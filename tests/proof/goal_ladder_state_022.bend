# goal ladder, tower state 3 (after cat_assoc): reassociation -- the
# residual closes by conversion.
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
    case h <> t:
      h <> List.append(A, t, ys)

law List.reverse.go:
  for -A: Data
  for xs: List<&2, A>
  for acc: List<&2, A>
  List<&2, A>

def List.reverse.go(A, xs, acc):
  match xs:
    case Nil{}:
      acc
    case h <> t:
      List.reverse.go(A, t, h <> acc)

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
    case h <> t:
      %cat_assoc(A, t, b, c) : {h <> List.append(A, List.append(A, t, b), c) == h <> _ : List<&2, A>}
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
    case h <> t:
      %rgo_cat(A, t, h <> acc) : {List.append(A, List.reverse.go(A, t, [h]), acc) == _ : List<&2, A>}
      %rgo_cat(A, t, [h]) : {List.append(A, _, acc) == List.append(A, List.reverse.go(A, t, Nil{}), h <> acc) : List<&2, A>}
      %cat_assoc(A, List.reverse.go(A, t, Nil{}), [h], acc) : {List.append(A, List.append(A, List.reverse.go(A, t, Nil{}), [h]), acc) == _ : List<&2, A>}
      Type

#|Error:
#|- expected : {List.append(A, List.append(A, List.reverse.go(A, t, []), [h]), acc) == List.append(A, List.append(A, List.reverse.go(A, t, []), [h]), acc) : List<&2, A>}
#|- observed : Type
#|Context:
#|- A   : Data
#|- h   : A
#|- t   : List<&2, A>
#|- acc : List<&2, A>
#|Location: rgo_cat
#|61 |       %cat_assoc(A, List.reverse.go(A, t, Nil{}), [h], acc) : {List.append(A, List.append(A, List.reverse.go(A, t, Nil{}), [h]), acc) == _ : List<&2, A>}
#|62>|       Type
#|63 |
#|exit 1
