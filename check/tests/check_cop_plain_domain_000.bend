# SPEC PART 3 COP, the refusal half: outside #[halts] a Many (+)
# binder whose type is not a Cop is a formation error
import Base

assert twice:
  forall +x: Nat
  Nat

def twice(x):
  Nat.add(x, x)

assert main:
  Nat

def main():
  twice(3n)
$$ bend %
Error:
- expected : a copiable type (a + binder needs a + T ~ C type, or #[halts])
- observed : @+x:Nat -> Nat
