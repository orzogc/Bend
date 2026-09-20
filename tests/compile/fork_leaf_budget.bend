# A leaf handed off from a forky segment under ! runs on a lane stack of
# STAK_LEN words on the device: three exit words and one a level, so 2045
# levels fill it exactly. One more dies with the ERR_DEEP line on the device
# (before the bound ended at the static image, lanes under it kept a 2049th
# word over the image instead); the host runs the same leaf on its 2 GiB
# stack at any depth.
import Base

def deep(+n: Nat) -> U32:
  match n:
    case 0n:
      0
    case 1n+p:
      U32.add(1, deep(p))

def two(+n: Nat) -> U32:
  c = deep(2045n)
  a b = deep(n) deep(n)
  U32.add(U32.add(a, b), c)

def main() -> IO(Unit):
  IO.print(U32.show(two!(1n)))

#|2047
