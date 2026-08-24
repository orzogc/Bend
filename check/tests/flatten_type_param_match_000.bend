type Nat:
  Z{}
  S{p: Nat}

type List<-Elem: Type>:
  Nil{}
  Cons{h: Elem, t: List<Elem>}

assert main:
  forall A: Type
  forall b: List<Nat>
  forall c: List<Nat>
  List<Nat>

def main(A, b, c):
  match A, b, c:
    case A, Nil{}, b:
      Nil{}
    case A, Cons{c, d}, b:
      d

$$ bend % --show
main = A => \{Nil: (c => Nil{}); Cons: (c => d => c => d)}
