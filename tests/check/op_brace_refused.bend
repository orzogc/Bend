# braces ascribe a type and name no operator: a bare * inside {.. : Nat}
# is refused like any other, and the repair is (a * b : Nat) inside them
import Base

def main() -> Nat:
  {2n * 3n : Nat}

#|Error:
#|- message  : an operator with its type (( .. : T) around the expression gives it, as in (a * b : Nat))
#|Location:
#|5 | def main() -> Nat:
#|6>|   {2n * 3n : Nat}
#|7 | 
#|exit 1
