type Nat:
  Z{}
  S{p: Nat}

type List<-Elem: Type>:
  Nil{}
  Cons{h: Elem, t: List<Elem>}

type R:
  A{a: Nat, b: List<Nat>}
  B{a: Nat, b: List<Nat>}
  C{}

assert main:
  forall a: List<Nat>
  R

def main(a):
  match a:
    case Cons{S{S{a}}, b}:
      A{a,b}
    case Cons{a, b}:
      B{a,b}
    case Nil{}:
      C{}

$$ bend % --show
main = \{Cons: \{S: \{S: (a => b => A{a, b}); (_9 => b => B{S{_9}, b})}; (_7 => b => B{_7, b})}; Nil: C{}}
