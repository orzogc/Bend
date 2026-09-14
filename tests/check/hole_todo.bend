# ?TODO is the quiet hole: it checks at any goal, so an unfinished
# proof still checks (the CLI notes the TODO on a plain run)
import Base

law th:
  for n: Nat
  {Nat.add(n, 0n) == n : Nat}

def th(n):
  ?TODO

law main:
  U32

def main(): 7

#|7
