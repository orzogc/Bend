# a match application with an ANNOTATED scrutinee: stuck on the param,
# the application shows
type Nt:
  Zn{}
  Sn{p: Nt}

type R:
  A{}
  B{x: Nt}

assert main:
  forall n: Nt
  R

def main(n):
  (\{Zn: A{}; Sn: (x => B{x})})({n : Nt})
$$ bend % --show
main = n => \{Zn: A{}; Sn: (x => B{x})}({n : Nt})
