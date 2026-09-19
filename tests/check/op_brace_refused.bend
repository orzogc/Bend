# braces ascribe a type and name no operator: a bare * inside {.. : Nat}
# is refused like any other, and the repair is (a * b : Nat) inside them
import Base

def main() -> Nat:
  {2n * 3n : Nat}

#|Error:
#|- message  : an operator with its type (( .. : T) around the expression gives it, as in (a * b : Nat))
#|  Sorry: this is a small break after the launch. Versions 2.0.0 to 2.0.16
#|  read an operator with no type as Nat, against the language's own rule.
#|  If this compiled before, put the type on the expression: a * b
#|  becomes (a * b : Nat).
#|Location:
#|5 | def main() -> Nat:
#|6>|   {2n * 3n : Nat}
#|7 | 
#|exit 1
