# base List: reverse is involutive and an insertion sort orders (dupes
# kept) on concrete lists -- closed by conversion alone, no output.
# ported from bend3: list literals become Con/Nil spines, bend3-base
# List.sort becomes a local insertion sort (bend4 base has none); the
# compare-and-rebuild double use takes + binders (List<&2, U32> is
# Data, so it duplicates)
import Base

law List.reverse.go:
  for -a  : Quant
  for -A  : Kind(a)
  for xs  : List<a, A>
  for acc : List<a, A>
  List<a, A>

def List.reverse.go(a, A, xs, acc):
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      List.reverse.go(a, A, t, Con{h, acc})

law List.reverse:
  for -a : Quant
  for -A : Kind(a)
  for xs : List<a, A>
  List<a, A>

def List.reverse(a, A, xs):
  List.reverse.go(a, A, xs, Nil{})

law l123:
  List<&2, U32>

def l123():
  Con{1, Con{2, Con{3, Nil{}}}}

law l321:
  List<&2, U32>

def l321():
  Con{3, Con{2, Con{1, Nil{}}}}

law insert.put:
  for +x: U32
  for  h: U32
  for +t: List<&2, U32>
  for  r: List<&2, U32>
  for  f: Bool
  List<&2, U32>

def insert.put(x, h, t, r, f):
  match f:
    case True{}:
      Con{x, Con{h, t}}
    case False{}:
      Con{h, r}

law insert:
  for +x  : U32
  for +xs : List<&2, U32>
  List<&2, U32>

def insert(x, xs):
  match xs:
    case Nil{}:
      Con{x, Nil{}}
    case Con{h, t}:
      insert.put(x, h, t, insert(x, t), U32.is_le(x, h))

law sort:
  for xs: List<&2, U32>
  List<&2, U32>

def sort(xs):
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      insert(h, sort(t))

law rev:
  {List.reverse(&2, U32, l123) == l321 : List<&2, U32>}

def rev():
  {==}

law rev2:
  {List.reverse(&2, U32, List.reverse(&2, U32, l123)) == l123 : List<&2, U32>}

def rev2():
  {==}

law srt:
  {sort(Con{3, Con{1, Con{2, Con{3, Nil{}}}}}) == Con{1, Con{2, Con{3, Con{3, Nil{}}}}} : List<&2, U32>}

def srt():
  {==}

#|All terms check.
