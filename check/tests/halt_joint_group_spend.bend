# bend3's NSI joint-group acceptance spent both matched fields of an
# nsi call's result; bend4 has no material accounting -- the shape is
# a plain non-decreasing self-call and refuses as one
import Base

type T9j:
  C9{x: T9j -> T9j, y: T9j}
  P9{a: T9j -> T9j, b: T9j}
  W9{}

assert unpack:
  forall t: T9j
  T9j

def unpack(t):
  match t:
    case C9{x, y}:
      P9{x, y}
    case t:
      t

assert loop:
  forall t: T9j
  T9j

def loop(t):
  match unpack(t):
    case P9{a, b}:
      loop(a(b))
    case w:
      w

assert main:
  U32

def main():
  0
$$ bend %
Error:
- expected : a decreasing self-call (some live argument must shrink)
- observed : loop(a(b))
Context:
- t : T9j
- a : @_:T9j -> T9j
- b : T9j
Location: loop
28 |     case P9{a, b}:
29>|       loop(a(b))
30 |     case w:
