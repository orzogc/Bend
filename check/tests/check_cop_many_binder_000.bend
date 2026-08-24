# SPEC PART 3 COP: a Many (+) binder is legal outside #[halts] iff its
# type is a Cop (+ T ~ C, C : Copiable(T)); +Nat resolves Nat.copy
# structurally; a claim may bind a dotted witness parameter (T.copy);
# a Cop is convertible-equal to its T, so values flow both ways
import Base

assert twice:
  forall +x: +Nat
  Nat

def twice(x):
  Nat.add(x, x)

assert dup:
  forall -T: Type
  forall T.copy: Copiable(T)
  forall +x: + T ~ T.copy
  Pair(T, T)

def dup(T, T.copy, x):
  (x, x)

assert main:
  Nat

def main():
  p = dup(Nat, Nat.copy, twice(2n))
  Tuple{a, b} = p
  Nat.add(a, b)
$$ bend %
8n
