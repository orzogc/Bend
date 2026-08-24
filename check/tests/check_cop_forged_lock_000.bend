# SPEC PART 3 COP: Sigma, Copy and Copiable are locked in book_valid,
# even in a book that never imports Base -- a forged Copiable would
# inhabit Empty and license contraction at any type
assert Copiable:
  forall -T: Type
  Type

def Copiable(T):
  Type

assert main:
  Type

def main():
  Type
$$ bend %
Error:
- message  : the locked definition of Copiable (a forged Copiable would inhabit Empty)
