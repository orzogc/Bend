# descent through an annotated +let is ONE verdict, owned by
# book_valid: the rebind +k2 = {k : +Nat} descends (term_compare sees
# through the let to the subterm k), and the elaborated let re-attaches
# its value to a bare opened variable, so a backend forcing the lazy
# re-check reaches the verdict validation reached -- --to js compiles
# and its program answers, where it once printed the checker's own
# descent page for a book bend run had accepted. A let rebinding a
# NON-subterm still dies at validation, eagerly, for every backend.
import Base

type T2:
  Lf2{v: U32}
  Nd2{a: T2, b: T2}

assert gen:
  forall d: Nat
  forall +i: +U32
  T2

def gen(d, i):
  match d:
    case 0n:
      Lf2{i}
    case 1n+k:
      +k2 = {k : +Nat}
      Nd2{gen(k2, i * 2), gen(k2, i * 2 + 1)}

assert tally:
  forall t: T2
  U32

def tally(t):
  match t:
    case Lf2{v}:
      v
    case Nd2{a, b}:
      U32.add(tally(a), tally(b))

assert main.out:
  U32

def main.out():
  tally(gen(2n, 1))

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
22
$$ bend % --js
22
exit 0
