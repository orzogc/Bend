# tuple ladder, complete: destructuring the pair mid-proof computes
# both swaps away
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
  (a, b) = p
  {==}

$$ bend %
