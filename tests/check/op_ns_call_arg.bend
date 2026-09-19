# a ( .. : T) does not reach an operator inside a call's argument: the +
# here is Nat's, so the annotation names nothing and is refused with the
# repair, instead of quietly naming the + through the call
import Base

def id_u(x: U32) -> U32: x

def main() -> U32:
  (id_u(2 + 3) : U32)

#|Error:
#|- message  : an operator with its type (( .. : T) around the expression gives it, as in (a + b : Nat))
#|  Sorry: this is a small break after the launch. Versions 2.0.0 to 2.0.16
#|  read an operator with no type as Nat, against the language's own rule.
#|  If this compiled before, put the type on the expression: a + b
#|  becomes (a + b : Nat).
#|Location:
#| 8 | def main() -> U32:
#| 9>|   (id_u(2 + 3) : U32)
#|10 | 
#|exit 1
