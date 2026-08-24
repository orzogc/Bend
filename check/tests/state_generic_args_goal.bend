# tuple ladder, state 0: a generic def's erased Type args display in
# the stuck call, and the context shows the sigma spelling of the pair
# (&_:Nat -> Nat), never a match literal
import Base

assert swap:
  forall -A: Type
  forall -B: Type
  forall p: A & B
  B & A

def swap(A, B, p):
  (a, b) = p
  (b, a)

assert swap_swap:
  forall p: Nat & Nat
  {swap(Nat, Nat, swap(Nat, Nat, p)) == p : Nat & Nat}

def swap_swap(p):
  {==}

$$ bend %
Error:
- expected : swap(Nat, Nat, swap(Nat, Nat, p))
- observed : p
Context:
- p : &_:Nat -> Nat
Location: swap_swap
20 | def swap_swap(p):
21>|   {==}
22 |
