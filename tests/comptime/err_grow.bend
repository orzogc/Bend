# a self-call whose compile-time argument grows one node per level never
# reaches a shared instance: each instance's check mints the next, and past
# the key wall (32768 chars) the checker refuses the call, in the instance
# whose self-call crosses it
import Base

def inc(n: Nat) -> Nat:
  1n+n

def grow(~f: Nat -> Nat, x: Nat) -> Nat:
  match x:
    case 0n:
      f(0n)
    case 1n+p:
      grow(~(y => inc(f(y))), p)

def main() -> Nat:
  grow(~inc, 2n)

#|Error:
#|- expected : a ~ argument that stops growing (32768 key chars at most)
#|- observed : grow
#|Context:
#|- p : Nat
#|Location: grow~237
#|14 |     case 1n+p:
#|15>|       grow(~(y => inc(f(y))), p)
#|16 |
#|exit 1
