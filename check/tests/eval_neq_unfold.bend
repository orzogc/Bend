# {a != b : T} desugars at parse time to {a == b : T} -> Empty: no
# negated Eql node and no minted def exist anywhere (bend3 minted
# Empty.Not; bend4 unfolds structurally in the parser)
import Base

assert NEQ01:
  Type

def NEQ01():
  {0n != 1n : Nat}

assert main:
  Type

def main():
  NEQ01()
$$ bend %
@_:{0n == 1n : Nat} -> Empty