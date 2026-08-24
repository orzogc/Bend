# regression (AUDIT 2b): a framed cell's value mentioning an earlier
# cell resolves to THE CELL, never past it -- the flatten once applied
# raw values as siblings, so `a` here silently became the top-level def
# and frame(True{}) answered False{}. Bound as sequential lets, the
# reference reaches the cell and the double consumption refuses loud.
import Base

assert a:
  Bool

def a():
  False{}

assert frame:
  forall b: Bool
  Bool

def frame(b):
  match a : Bool = b, c : Bool = a:
    case x, y:
      y
  return Bool

assert main:
  Bool

def main():
  frame(True{})
$$ bend %
Error:
- expected : a
- observed : a (consumed more than once)
Context:
- b : Bool
Location: frame
18 | def frame(b):
19>|   match a : Bool = b, c : Bool = a:
20 |     case x, y:
