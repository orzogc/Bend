# red-team pin inverted: bend3 needed a poison walk (a function field
# anywhere in A -> B -> C nulls every member's table) to refuse sharing
# an A whose own fields are innocent. bend4 needs no poison: core is
# affine for EVERY type, so use2(a, a) refuses outright, closure field
# or not -- the wall the poison approximated is the default.
# ported from bend3: names resolve upward only, so the chain declares
# C2, B2, A2; ctor names are bare and globally unique
import Base

type C2:
  MkC2{f: U32 -> U32}
  EndC2{}
type B2:
  MkB2{c: C2}
  EndB2{}
type A2:
  MkA2{b: B2}
  EndA2{}

assert mk:
  A2

def mk(): EndA2{}

assert use2:
  forall x: A2
  forall y: A2
  U32

def use2(x, y): 0

assert main:
  U32

def main():
  a = mk()
  use2(a, a)
$$ bend %
Error:
- expected : a
- observed : a (consumed more than once)
Location: main
35 | def main():
36>|   a = mk()
37 |   use2(a, a)
