# bend3's NSI ledger closed this gate arm by arm; bend4 refuses the
# same file at the descent wall: loop(f(y)) under the minted lambda is
# a whole self-call whose argument f(y) shrinks no column.
# ported from bend3: bare ctors, main returns the test's own type
type T:
  C{f: T -> T}
  N{}

assert apply1:
  forall g: T -> T
  forall v: T
  T

def apply1(g, v):
  g(v)

assert loop:
  forall t: T
  T

def loop(t):
  match t:
    case C{f}:
      apply1(y => loop(f(y)), C{z => z})
    case t:
      t

assert main:
  T

def main(): N{}
$$ bend %
Error:
- expected : a decreasing self-call (some live argument must shrink)
- observed : loop(f(y))
Context:
- f : @_:T -> T
- y : T
Location: loop
23 |     case C{f}:
24>|       apply1(y => loop(f(y)), C{z => z})
25 |     case t:
