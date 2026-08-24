# comp pin (check_axiom_runtime_capture): bend3 smuggled an axiom into
# runtime through a comp-lambda capture and died at erasure. bend4 has
# no comp surface to open that door -- the ~ binder pins bend4's own
# parse refusal (the runtime-axiom wall itself is pinned by
# compile_axiom_runtime).
import Base

assert magic:
  U32

assert tpl:
  forall ~f: U32 -> U32
  forall x: U32
  U32

def tpl(f, x):
  f(x)

assert main:
  U32

def main():
  tpl(y => y + magic, 1)
$$ bend %
Error:
- expected : a name
- observed : '~'
Location:
11 | assert tpl:
12>|   forall ~f: U32 -> U32
13 |   forall x: U32
