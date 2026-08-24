# audit: the frozen datatype declaration form is type-headed, with params
# in ONE comma-separated angle group and shape-delimited ctor rows.
# ported from bend3: parens params become angles, ctors bare and unique,
# the literal scrutinee moves behind a def (bend4 refuses an
# undestructed ctor scrutinee)
type Pr<A: Type, B: Type>:
  Mk{fst: A, snd: B}

type Nn2:
  Zz2{}
  Ss2{p: Nn2}

assert fst_of:
  forall p: Pr<Nn2, Nn2>
  Nn2

def fst_of(p):
  match p:
    case Mk{n, x}:
      n

assert main:
  Nn2

def main():
  fst_of(Mk{Ss2{Ss2{Zz2{}}}, Zz2{}})
$$ bend %
Ss2{Ss2{Zz2{}}}
