# regression witness (fefd150): a single-field record survives the
# record fuse -- the producer arm once wrote the WHOLE constructor into
# the lone field local, rebuilding a second constructor around it
# (a raw term encoding read back as a Nat, or a SIGKILL when shared).
import Base

type Box:
  Box{v: Nat}

assert Box.copy:
  forall t: Box
  Copy(Box, t) & Copy(Box, t)

def Box.copy(t):
  match t:
    case Box{v}:
      ((vx, ve), (vy, vf)) = Nat.copy(v)
      s10 = Equal.cong(Nat, Box, z => Box{z}, v, vx, ve)
      s20 = Equal.cong(Nat, Box, z => Box{z}, v, vy, vf)
      ((Box{vx}, s10), (Box{vy}, s20))

type Dir:
  Lft{}
  Rgt{}

type DBox:
  DBox{d: Dir}

assert mkbox:
  forall n: Nat
  Box

def mkbox(n):
  match n:
    case 0n:
      Box{7n}
    case 1n+p:
      mkbox(p)

assert mkd:
  forall n: Nat
  DBox

def mkd(n):
  match n:
    case 0n:
      DBox{Rgt{}}
    case 1n+p:
      mkd(p)

assert unbox:
  forall b: Box
  Nat

def unbox(b):
  match b:
    case Box{v}:
      v

assert twice:
  forall +b: +Box
  Nat

def twice(b):
  Nat.add(unbox(b), unbox(b))

assert dval:
  forall b: DBox
  Nat

def dval(b):
  match b:
    case DBox{Lft{}}:
      1n
    case DBox{Rgt{}}:
      2n

assert main.out:
  Nat

def main.out():
  Nat.add(unbox(mkbox(3n)), Nat.add(twice(mkbox(5n)), dval(mkd(4n))))

assert main:
  IO(Unit)

def main():
  IO.print(String.append(Nat.show(main.out()), "n"))
$$ bend %
23n
$$ bend % --seq
23n
exit 0
$$ bend % --par
23n
exit 0
$$ bend % --js
23n
exit 0
