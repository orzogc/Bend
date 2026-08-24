# descent rejects minting: the argument spends a fresh lambda each
# round (with f = id the call rebuilds C{y => y} forever) -- f(C{y =>
# y}) shrinks no column, so the self-call is refused.
# ported from bend3: bare ctors, main returns the test's own type
type T:
  C{f: T -> T}
  N{}

assert loop:
  forall t: T
  T

def loop(t):
  match t:
    case C{f}:
      loop(f(C{y => y}))
    case t:
      t

assert main:
  T

def main(): N{}
$$ bend %
Error:
- expected : a decreasing self-call (some live argument must shrink)
- observed : loop(f(C{y => y}))
Context:
- f : @_:T -> T
Location: loop
15 |     case C{f}:
16>|       loop(f(C{y => y}))
17 |     case t:
