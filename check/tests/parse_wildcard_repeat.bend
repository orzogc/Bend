# audit: `_` is a repeatable wildcard: many in one pattern and in def
# params.
# ported from bend3: the destructure statement needs a one-ctor type
type Unit11:
  Uu11{}

type Pp11:
  Pq11{a: Unit11, b: Unit11}

assert fst:
  forall p: Pp11
  forall _: Unit11
  forall _: Unit11
  Unit11

def fst(p, _, _):
  match p:
    case Pq11{x, _}:
      x

assert snd:
  forall p: Pp11
  Unit11

def snd(p):
  Pq11{_, y} = p
  y

assert main:
  Unit11

def main(): fst(Pq11{Uu11{}, Uu11{}}, Uu11{}, Uu11{})
$$ bend %
Uu11{}
