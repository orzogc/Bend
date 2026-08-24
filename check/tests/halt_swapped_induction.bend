# the AI-loop's classic bad proof: an induction whose IH swaps the
# columns is not a descent. bend3 refused it with a type mismatch off
# its accepted swap; bend4 refuses the swap itself -- b sits in a's
# column with no subterm relation, so the IH is refused as
# non-decreasing. Never accepted in either dialect.
# ported from bend3: bare ctors S/Z over the test's own N; add is
# spelled on N so the equation stays inside one datatype
type N:
  S{p: N}
  Z{}

assert add:
  forall a: N
  forall b: N
  N

def add(a, b):
  match a:
    case Z{}:
      b
    case S{p}:
      S{add(p, b)}

assert swapped:
  forall a: N
  forall b: N
  {add(a, b) == add(b, a) : N}

def swapped(a, b):
  match a:
    case Z{}:
      swapped(b, Z{})
    case S{p}:
      swapped(b, S{p})

assert main:
  N

def main(): Z{}
$$ bend %
Error:
- expected : a decreasing self-call (some live argument must shrink)
- observed : swapped(b, Z{})
Context:
- b : N
Location: swapped
31 |     case Z{}:
32>|       swapped(b, Z{})
33 |     case S{p}:
