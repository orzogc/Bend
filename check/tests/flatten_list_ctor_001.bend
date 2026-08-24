type Nat:
  Z{}
  S{p: Nat}

type List<-Elem: Type>:
  Nil{}
  Cons{h: Elem, t: List<Elem>}

type R:
  A{a: Nat, b: List<Nat>}
  B{a: List<Nat>}
  C{}

assert main:
  forall a: List<Nat>
  R

def main(a):
  match a:
    case Cons{S{a}, b}:
      A{a,b}
    case Cons{Z{}, a}:
      B{a}
    case Nil{}:
      C{}

$$ bend % --show
main = \{Cons: \{S: (a => b => A{a, b}); Z: (b => B{b})}; Nil: C{}}
