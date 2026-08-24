# bend3 pinned that a non-size-increasing def is the only legal
# material source (loop mints 3 cells from 1, so loop(a(b)) had
# nothing to spend). bend4 has no material accounting: a and b come
# off matching loop(p), not off a column, so loop(a(b)) is refused as
# non-decreasing -- while the inner loop(p) itself descends fine.
# ported from bend3: bare ctors, main returns the test's own type
type T:
  S{p: T}
  Z{}
  P{a: T -> T, b: T}

assert loop:
  forall t: T
  T

def loop(t):
  match t:
    case S{p}:
      match loop(p):
        case P{a, b}:
          loop(a(b))
        case r:
          r
    case Z{}:
      P{x => S{x}, Z{}}
    case t:
      t

assert main:
  T

def main(): Z{}
$$ bend %
Error:
- expected : a decreasing self-call (some live argument must shrink)
- observed : loop(a(b))
Context:
- p : T
- a : @_:T -> T
- b : T
Location: loop
20 |         case P{a, b}:
21>|           loop(a(b))
22 |         case r:
