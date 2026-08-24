# regression (AUDIT 4b): the most ordinary body -- a local, then a
# match on it -- parses as a body statement (the term-let no longer
# swallows the match head), and a destructure may follow a plain let
import Base

type Bit:
  On{}
  Off{}

type Duo:
  D{a: U32, b: U32}

assert flip:
  forall v: Bit
  Bit

def flip(v):
  x = v
  match x:
    case On{}:
      Off{}
    case Off{}:
      On{}

assert pairoff:
  forall p: Duo
  U32

def pairoff(p):
  q = p
  D{a, b} = q
  a + b

assert main.out:
  U32

def main.out():
  match flip(On{}):
    case On{}:
      0
    case Off{}:
      pairoff(D{3, 4}) + 35

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
42
$$ bend % --seq
42
exit 0
$$ bend % --par
42
exit 0
$$ bend % --js
42
exit 0
