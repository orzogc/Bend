# a lambda is not a pattern: the case head is refused with the pattern
# grammar (a binder or a constructor).
# ported from bend3
type Nu:
  Zu{}
  Su{p: Nu}

type Ru:
  Au{}

assert f:
  forall a: Nu
  Ru

def f(a):
  match a:
    case x => x:
      Au{}

assert main:
  Ru

def main(): f(Zu{})
$$ bend %
Error:
- expected : a pattern (a binder or a constructor)
- observed : x => x
Location:
16 |   match a:
17>|     case x => x:
18 |       Au{}
