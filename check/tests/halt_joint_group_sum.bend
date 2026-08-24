# bend3 pinned that its NSI group rule may not pool a multi-argument
# call's columns (grow shrinks only the SUM, so More's field x is no
# smaller than column a -- accepting loop inhabits Empty). bend4 has no
# group rule at all: x comes off matching grow(a, fallback, b), not off
# a column, so the self-call is refused as non-decreasing outright.
# ported from bend3: bare ctors, Empty spelled as the base Empty
import Base

type T:
  S{p: T}
  Z{}

type Step:
  More{x: T}

assert grow:
  forall a: T
  forall fallback: Step
  forall b: T
  Step

def grow(a, fallback, b):
  match b:
    case S{q}:
      More{a}
    case z:
      fallback

assert loop:
  forall a: T
  forall fallback: Step
  forall b: T
  Empty

def loop(a, fallback, b):
  match grow(a, fallback, b):
    case More{x}:
      loop(x, More{Z{}}, b)

assert main:
  Empty

def main(): loop(Z{}, More{Z{}}, S{Z{}})
$$ bend %
Error:
- expected : a decreasing self-call (some live argument must shrink)
- observed : loop(x, More{Z{}}, b)
Context:
- a        : T
- fallback : Step
- b        : T
- x        : T
Location: loop
37 |     case More{x}:
38>|       loop(x, More{Z{}}, b)
39 |
