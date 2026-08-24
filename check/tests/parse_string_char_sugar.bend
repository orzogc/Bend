# char and string literal sugar: 'a' is Chr{code} and "ab" is an SCon
# chain, so the two concatenate through one String walk.
# ported from bend3: bend3's local Char/List become Base's Char/String
import Base

assert cat:
  forall a: String
  forall b: String
  String

def cat(a, b):
  match a:
    case SCon{h, t}:
      SCon{h, cat(t, b)}
    case SNil{}:
      b

assert main:
  String

def main(): cat("Hi,\n\t", SCon{'π', " 'q' \"z\""})
$$ bend %
"Hi,\n\tπ 'q' \"z\""
