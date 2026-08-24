# the != form is core grammar, gated on nothing -- with Base in scope
# it checks at any type (bend3 gated the sugar on `import Empty`)
import Base

assert cneq:
  Type

def cneq():
  {'a' != 'b' : Char}

assert main:
  Nat

def main():
  9n
$$ bend %
9n
