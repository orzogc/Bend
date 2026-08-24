# char and string literals as patterns.
# ported from bend3: Base's String/Char, Bool result
import Base

assert is_hi:
  forall s: String
  Bool

def is_hi(s):
  match s:
    case "hi":
      True{}
    case s:
      False{}

assert main:
  Bool

def main(): is_hi("hi")
$$ bend %
True{}
