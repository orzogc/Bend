type Nat:
  Z{}
  S{p: Nat}

type Bit:
  F{}
  T{}

type List<-Elem: Type>:
  Nil{}
  Cons{h: Elem, t: List<Elem>}

type R:
  A{a: List<Bit>}
  B{a: List<Bit>}
  C{}

assert main:
  forall a: List<Bit>
  R

def main(a):
  match a:
    case Cons{F{}, a}:
      A{a}
    case Cons{T{}, a}:
      B{a}
    case Nil{}:
      C{}

$$ bend % --show
main = \{Cons: \{F: (a => A{a}); T: (a => B{a})}; Nil: C{}}
