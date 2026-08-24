# comp-splice pin (spec_comp_capture_erase): bend3 took a capture's
# quantity from the specialized body's own uses, so an all-erased
# capture erased at the caller too. bend4 has no comp surface; the ~
# binder pins bend4's own parse refusal. (bend3's () Unit literal is
# respelled Unit{}: bend4 has no unit literal.)
import Base

type D:
  Da{f0: F32, -f1: U32}

assert cp:
  forall ~f: Unit -> (F32 & D)
  forall x: Unit
  (F32 & D)

def cp(f, x):
  f(x)

assert mk:
  forall -n: U32
  Unit

def mk(n):
  Unit{}

assert rd:
  forall x: (F32 & D)
  U32

def rd(x):
  match x:
    case (a, b):
      F32.to_u32(a)

assert main:
  U32

def main():
  rd(cp(z => (19.0, Da{3.0, 7}), mk(7)))
$$ bend %
Error:
- expected : a name
- observed : '~'
Location:
11 | assert cp:
12>|   forall ~f: Unit -> (F32 & D)
13 |   forall x: Unit
