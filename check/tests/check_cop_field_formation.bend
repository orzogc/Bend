# the Cop condition binds ADT telescopes: a + entry in a constructor's
# telescope demands a Cop type, or the datatype would hand every match
# arm an unlicensed Many binder. book_valid refuses the declaration
# itself; main never checks.
import Base

type BadT:
  MkB{+f: Nat}

assert main:
  Nat

def main(): 0n
$$ bend %
Error:
- message  : a copiable type (a + binder needs a + T ~ C type)
Location: MkB
