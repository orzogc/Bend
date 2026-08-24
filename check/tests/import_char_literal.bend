# char literals are core grammar, ungated: 'a' is Chr{97} with Base's
# Char in scope (bend3 gated the quote sugar on `import Char`)
import Base

assert code:
  forall c: Char
  U32

def code(c):
  match c:
    case Chr{u}:
      u

assert main.out:
  U32

def main.out():
  code('a')

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
97
$$ bend % --seq
97
exit 0
$$ bend % --js
97
exit 0
