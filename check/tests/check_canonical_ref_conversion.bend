# conversion is CANONICAL at the ref head: two distinct defs with
# byte-identical case trees do NOT convert applied to an opaque var --
# a stuck dispatch keeps its own ref spelling.
# ported from bend3
import Base

type Nc:
  Zc{}
  Sc{p: Nc}

assert f:
  forall t: Nc
  U32

def f(t):
  match t:
    case Zc{}:
      0
    case Sc{p}:
      1

assert g:
  forall t: Nc
  U32

def g(t):
  match t:
    case Zc{}:
      0
    case Sc{p}:
      1

assert eq:
  forall t: Nc
  {f(t) == g(t) : U32}

def eq(t):
  {==}

assert main:
  U32

def main(): 0
$$ bend %
Error:
- expected : f(t)
- observed : g(t)
Context:
- t : Nc
Location: eq
37 | def eq(t):
38>|   {==}
39 |
