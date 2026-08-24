# bend3's ':'-qualified canonical import names had to pass the C
# sanitizer; bend4 imports alias whole files and the corpus is flat
# single files, so no canonical name exists -- the value half carries:
# the same fold over string chars answers on every lane
import Base

assert len6:
  forall s: String
  U32

def len6(s):
  match s:
    case SCon{Chr{c}, t}:
      1 + len6(t)
    case SNil{}:
      0

assert main.out:
  Nat

def main.out():
  U32.to_nat((len6("hello") * 10) + len6(""))

assert main:
  IO(Unit)

def main():
  IO.print(String.append(Nat.show(main.out()), "n"))
$$ bend %
50n
$$ bend % --seq
50n
exit 0
$$ bend % --par
50n
exit 0
$$ bend % --js
50n
exit 0
