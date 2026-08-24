# string escapes are real characters: \n is one Char, \\ is one Char.
# ported from bend3: List.length over Chars becomes a local String
# walk returning Nat (bend4 base has no length)
import Base

assert slen:
  forall s: String
  Nat

def slen(s):
  match s:
    case SNil{}:
      0n
    case SCon{h, t}:
      Succ{slen(t)}

assert main.out:
  Pair(Nat, Nat)

def main.out():
  (slen("a\nb"), slen("\\"))

assert main:
  IO(Unit)

def main():
  Tuple{a, b} = main.out()
  s = String.append(Nat.show(a), String.append("n, ", String.append(Nat.show(b), "n}")))
  IO.print(String.append("Tuple{", s))
$$ bend %
Tuple{3n, 1n}
$$ bend % --seq
Tuple{3n, 1n}
exit 0
$$ bend % --par
Tuple{3n, 1n}
exit 0
$$ bend % --js
Tuple{3n, 1n}
exit 0
