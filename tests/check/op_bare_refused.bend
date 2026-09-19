# an operator takes its type from the ( .. : T) around its expression and
# from nothing else: a bare + is refused at the + itself, on its own line,
# with the repair spelled with that operator
import Base

def sum3(a: Nat, b: Nat, c: Nat) -> Nat:
  a
  + b
  + c

def main() -> Nat:
  sum3(1n, 2n, 3n)

#|Error:
#|- message  : an operator with its type (( .. : T) around the expression gives it, as in (a + b : Nat))
#|Location:
#| 8 |   + b
#| 9>|   + c
#|10 | 
#|exit 1
