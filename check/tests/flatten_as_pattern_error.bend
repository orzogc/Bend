# bend3 refused `as` on a multi-scrutinee match (one name, two
# columns); bend4 has no as binder at all -- the words read as extra
# scrutinees and the pattern count refuses at the same early spot
import Base

assert both:
  forall a: Bool
  forall b: Bool
  U32

def both(a, b):
  match Bool.not(a), b as e:
    case True{}, True{}:
      1
    case x, y:
      0

assert main:
  U32

def main():
  0
$$ bend %
Error:
- expected : 4 patterns (one per scrutinee)
- observed : '
'
Location:
12 |   match Bool.not(a), b as e:
13>|     case True{}, True{}:
14 |       1
