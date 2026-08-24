type Nat:
  Z{}
  S{p: Nat}
type List<-Elem: Type>:
  Nil{}
  Cons{h: Elem, t: List<Elem>}
type R:
  A{a: Nat, b: List<Nat>}
  B{a: Nat, b: Nat, c: List<Nat>}
  C{a: Nat}
  D{a: Nat, b: List<Nat>}
  E{a: Nat, b: List<Nat>}
  F{}

assert main:
  forall a: List<Nat>
  R

def main(a):
  match a:
    case Cons{S{S{a}}, Cons{Z{}, b}}:
      A{a,b}
    case Cons{S{a}, Cons{b, c}}:
      B{a,b,c}
    case Cons{S{a}, Nil{}}:
      C{a}
    case Cons{Z{}, Cons{S{a}, b}}:
      D{a,b}
    case Cons{a, b}:
      E{a,b}
    case Nil{}:
      F{}

$$ bend % --show
main = \{Cons: \{S: \{S: (a => \{Cons: \{Z: (b => A{a, b}); (_20 => b => B{S{a}, _20, b})}; Nil: C{S{a}}; (_17 => E{S{S{a}}, _17})}); (_18 => \{Cons: (b => c => B{_18, b, c}); Nil: C{_18}; (_17 => E{S{_18}, _17})})}; Z: \{Cons: \{S: (a => b => D{a, b}); (_18 => b => E{Z{}, Cons{_18, b}})}; (_17 => E{Z{}, _17})}; (_16 => _17 => E{_16, _17})}; Nil: F{}}
