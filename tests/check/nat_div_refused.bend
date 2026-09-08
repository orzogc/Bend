# `/` and `%` name T.div and T.mod, and T defaults to Nat, which has
# Nat.divmod only: the call is refused as an undefined name
import Base

def main() -> Nat:
  (7n / 2n : Nat)

#|Error:
#|- expected : a defined name
#|- observed : Nat.div
#|Location: main
#|5 | def main() -> Nat:
#|6>|   (7n / 2n : Nat)
#|7 |
#|exit 1
