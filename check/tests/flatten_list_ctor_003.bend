type Nat:
  Z{}
  S{p: Nat}
type List<-Elem: Type>:
  Nil{}
  Cons{h: Elem, t: List<Elem>}
type R:
  A{a: Nat, b: List<Nat>}
  B{}
  C{a: Nat, b: List<Nat>}
  D{}

assert main:
  forall a: List<Nat>
  R

def main(a):
  match a:
    case Cons{S{a}, b}:
      A{a,b}
    case Cons{Z{}, Nil{}}:
      B{}
    case Cons{Z{}, Cons{a, b}}:
      C{a,b}
    case Nil{}:
      D{}

$$ bend % --show
main = \{Cons: \{S: (a => b => A{a, b}); Z: \{Nil: B{}; Cons: (a => b => C{a, b})}}; Nil: D{}}
