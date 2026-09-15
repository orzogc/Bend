# Hello world: the smallest IO program. greet(name) is its pure part:
# it wraps a name in "Hello, " and "!". main prints greet("world").
# The Spec section holds the string measures the laws talk about: a
# string's length, its first and last character, and its tail. Try it:
#
#   bend demos/io_hello_world/main.bend
import Base

# Spec
# ----

# the number of characters of a string
def length(s: String) -> Nat:
  match s:
    case SNil{}:
      0n
    case SCon{h, t}:
      1n+length(t)

# the first character of a string, or d when the string is empty
def head(s: String, d: Char) -> Char:
  match s:
    case SNil{}:
      d
    case SCon{h, t}:
      h

# the last character of a string, or d when the string is empty
def last(s: String, d: Char) -> Char:
  match s:
    case SNil{}:
      d
    case SCon{h, t}:
      last(t, h)

# the string after its first n characters
def drop(n: Nat, s: String) -> String:
  match n:
    case 0n:
      s
    case 1n+p:
      match s:
        case SNil{}:
          SNil{}
        case SCon{h, t}:
          drop(p, t)

# Program
# -------

# the greeting for a name
def greet(name: String) -> String:
  "Hello, " ++ (name ++ "!")

def main() -> IO(Unit):
  IO.print(greet("world"))
