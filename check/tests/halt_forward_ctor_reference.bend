#[halts]
# a 3-datatype recursive cycle (A -> B -> C -> A) needs #[halts]: a
# forward type reference fails as undefined under the default wall
# ("a defined name: B" at MkA's field), and no ordering can serve a
# cycle -- the pragma admits the knot. bend3 checked this book green
# in both modes; bend4 trades the wall for the pragma.
# ported from bend3: bare ctors, Box's Data kind becomes Type
import Base

type A:
  MkA{b: B}
  EndA{}

type B:
  MkB{c: C}
  EndB{}

type C:
  MkC{a: A}
  EndC{}

type Box<T: Type>:
  Bx{v: T}

assert go:
  forall x: Box<A>
  Nat

def go(x):
  match x:
    case Bx{v}:
      match v:
        case MkA{b}:
          1n
        case EndA{}:
          0n

assert main.out:
  Nat

def main.out(): go(Bx{MkA{MkB{MkC{EndA{}}}}})

assert main:
  IO(Unit)

def main():
  IO.print(String.append(Nat.show(main.out()), "n"))
$$ bend %
1n
$$ bend % --seq
1n
exit 0
$$ bend % --par
1n
exit 0
$$ bend % --js
1n
exit 0
