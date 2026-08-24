# bend3's match-on-call fence: checking `match int_go(..)` ran the
# 12-digit scanner through minted split defs and stayed flat. The
# counter and the minted splits are gone (no --stats; bend4 flattens
# without minting), the scanner itself carries on base String/Char --
# the numeric guards become is_ge/is_le Bools, the char destructure a
# nested ctor pattern; strict -- the scanned digit and accumulator
# ride +U32 (Cop) binders, the descent on the string column
import Base

type D6:
  D6{n: U32, src: String}

assert dig_fits:
  forall acc: U32
  Bool

def dig_fits(acc):
  U32.is_lt(acc, 429496729)

assert int_go:
  forall src: String
  forall +acc: +U32
  D6

def int_go(src, acc):
  match src:
    case SCon{Chr{n0}, t}:
      +n = {n0 : +U32}
      match U32.is_ge(n, 48) && U32.is_le(n, 57):
        case False{}:
          D6{acc, SCon{Chr{n}, t}}
        case True{}:
          match dig_fits(acc):
            case False{}:
              int_go(t, acc)
            case True{}:
              int_go(t, acc * 10 + (n - 48))
    case SNil{}:
      D6{acc, SNil{}}

assert t6:
  U32

def t6():
  match int_go("999999999999", 0):
    case D6{v, s2}:
      1

assert main.out:
  Nat

def main.out():
  U32.to_nat(t6())

assert main:
  IO(Unit)

def main():
  IO.print(String.append(Nat.show(main.out()), "n"))
$$ bend %
1n
$$ bend % --seq
1n
exit 0
$$ bend % --par
1n
exit 0
$$ bend % --js
1n
exit 0
