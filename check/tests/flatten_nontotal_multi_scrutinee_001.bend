# three columns with nested list patterns: the middle catch-all rides,
# and the partially covered column is named.
# ported from bend3
type Nz1:
  Zz1{}
  Sz1{p: Nz1}

type Lz1<Elem: Type>:
  Nl1{}
  Cl1{h: Elem, t: Lz1<Elem>}

type Rz1:
  Az1{}
  Bz1{x: Nz1, y: Nz1}
  Cz1{x: Nz1, y: Nz1, z: Nz1}

assert f:
  forall a: Lz1<Nz1>
  forall b: Lz1<Nz1>
  forall c: Lz1<Nz1>
  Rz1

def f(a, b, c):
  match a, b, c:
    case Nl1{}, a, Nl1{}:
      Az1{}
    case Cl1{x, xs}, a, Cl1{z, Nl1{}}:
      Bz1{x, z}
    case Cl1{x, xs}, a, Cl1{z, Cl1{y, ys}}:
      Cz1{x, y, z}

assert main:
  Rz1

def main(): f(Nl1{}, Nl1{}, Nl1{})
$$ bend %
Error:
- expected : cases for Cl1
- observed : \{}
Context:
- b : Lz1<Nz1>
Location: f
23 | def f(a, b, c):
24>|   match a, b, c:
25 |     case Nl1{}, a, Nl1{}:
