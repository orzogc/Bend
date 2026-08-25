# Hello world: base's IO surface end to end. A structural append
# builds the text (sappend: the same shape base's String.append
# intercepts to the runtime's native), and the event loop prints it --
# a foreign effect must answer BASE's IO, so even the smallest program
# stands on the base library, and every backend prints the same string.
import Base

assert sappend:
  forall a: String
  forall b: String
  String

def sappend(a, b):
  match a:
    case SNil{}:
      b
    case SCon{h, t}:
      SCon{h, sappend(t, b)}

assert main:
  IO(Unit)

def main():
  IO.print(sappend("Hello, ", "world!"))

$$ bend %
Hello, world!
$$ bend % --seq
Hello, world!
exit 0
$$ bend % --par
Hello, world!
exit 0
$$ bend % --js
Hello, world!
exit 0
