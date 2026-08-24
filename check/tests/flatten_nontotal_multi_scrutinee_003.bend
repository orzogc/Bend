# multi-scrutinee match: a non-exhaustive case set still errors
# NotTotal.
# ported from bend3
type Bity0:
  Ob{}
  Ib{}

assert mix:
  forall a: Bity0
  forall b: Bity0
  Bity0

def mix(a, b):
  match a, b:
    case Ob{}, Ob{}:
      Ob{}
    case Ib{}, Ib{}:
      Ib{}

assert main:
  Bity0

def main(): mix(Ob{}, Ob{})
$$ bend %
Error:
- expected : cases for Ib
- observed : \{}
Location: mix
13 | def mix(a, b):
14>|   match a, b:
15 |     case Ob{}, Ob{}:
