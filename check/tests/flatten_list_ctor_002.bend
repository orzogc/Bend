type Nat:
  Z{}
  S{p: Nat}
type List<-Elem: Type>:
  Nil{}
  Cons{h: Elem, t: List<Elem>}
type R:
  A{a: Nat, b: Nat, c: List<Nat>}
  B{a: Nat, b: List<Nat>}
  C{}

assert main:
  forall a: List<Nat>
  R

def main(a):
  match a:
    case Cons{S{a}, Cons{b, c}}:
      A{a,b,c}
    case Cons{a, b}:
      B{a,b}
    case Nil{}:
      C{}

$$ bend % --show
main = \{Cons: \{S: (a => \{Cons: (b => c => A{a, b, c}); (_10 => B{S{a}, _10})}); (_9 => _10 => B{_9, _10})}; Nil: C{}}
