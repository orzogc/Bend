type Nat:
  Z{}
  S{p: Nat}
type List<-Elem: Type>:
  Nil{}
  Cons{h: Elem, t: List<Elem>}
type R:
  A{}
  B{a: Nat, b: List<Nat>}
  C{a: Nat, b: List<Nat>, c: List<Nat>}
  D{a: Nat, b: Nat, c: List<Nat>, d: List<Nat>}

assert main:
  forall a: Nat
  forall b: List<Nat>
  forall c: List<Nat>
  R

def main(a, b, c):
  match a, b, c:
    case Z{}, a, b:
      A{}
    case S{a}, Nil{}, b:
      B{a,b}
    case S{a}, Cons{Z{}, b}, c:
      C{a,b,c}
    case S{a}, Cons{S{b}, c}, d:
      D{a,b,c,d}

$$ bend % --show
main = \{Z: (b => c => A{}); S: (a => \{Nil: (c => B{a, c}); Cons: \{Z: (b => c => C{a, b, c}); S: (b => b => c => D{a, b^1, b, c})}})}
