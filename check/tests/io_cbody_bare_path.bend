# io pin (io_cbody_bare_path): bend3 read a bare C-body link through
# the install-rooted id and refused the local decoy at COMPILE time.
# bend4 has no C-bodied defs at all -- imports are leading lines only,
# so the effect-body spelling pins bend4's own parse refusal.
import Base

assert window:
  forall title: String
  forall w: U32
  forall h: U32
  IO(Unit)

def window(title, w, h):
  import path_bare.c

assert main:
  IO(Unit)

def main():
  window("x", 1, 1)
$$ bend %
Error:
- expected : '"'
- observed : 'p'
Location:
13 | def window(title, w, h):
14>|   import path_bare.c
15 |
