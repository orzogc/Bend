# the old Nat spelling +n is no operator: a + glued to a name heads
# a binder, so the body ends at 1n and the top level meets a stray +
import Base

def main() -> Nat:
  1n +n 2n

#|Error:
#|- expected : 'def', 'type' or 'law'
#|- observed : '+'
#|Location:
#|5 | def main() -> Nat:
#|6>|   1n +n 2n
#|7 |
#|exit 1
