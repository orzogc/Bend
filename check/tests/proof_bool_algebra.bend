# Base Bool algebra: proven laws (and_comm, not_not) instantiate at
# concrete booleans like any theorem.
# ported from bend3: bend4's base carries the OPERATIONS only, so the
# laws are proved here over base Bool and then instantiated
import Base

assert and_comm:
  forall a: Bool
  forall b: Bool
  {Bool.and(a, b) == Bool.and(b, a) : Bool}

def and_comm(a, b):
  match a, b:
    case True{}, True{}:
      {==}
    case True{}, False{}:
      {==}
    case False{}, True{}:
      {==}
    case False{}, False{}:
      {==}

assert not_not:
  forall b: Bool
  {Bool.not(Bool.not(b)) == b : Bool}

def not_not(b):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

assert q:
  {Bool.and(True{}, False{}) == Bool.and(False{}, True{}) : Bool}

def q(): and_comm(True{}, False{})

assert w:
  {Bool.not(Bool.not(False{})) == False{} : Bool}

def w(): not_not(False{})

assert main:
  {Bool.and(True{}, False{}) == Bool.and(False{}, True{}) : Bool}

def main(): q()

$$ bend %
{==}
