# the growing self-call, doubling: the argument's key doubles per level,
# so the key wall (32768 chars) refuses the call at the instance whose
# self-call crosses it
import Base

def inc(n: Nat) -> Nat:
  1n+n

def grow(~f: Nat -> Nat, x: Nat) -> Nat:
  match x:
    case 0n:
      f(0n)
    case 1n+p:
      grow(~(y => f(f(y))), p)

def main() -> Nat:
  grow(~inc, 2n)

#|Error:
#|- expected : a ~ argument that stops growing (32768 key chars at most)
#|- observed : grow
#|Context:
#|- p : Nat
#|Location: grow~9
#|13 |     case 1n+p:
#|14>|       grow(~(y => f(f(y))), p)
#|15 |
#|exit 1
