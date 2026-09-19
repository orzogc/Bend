# comp pin (check_axiom_runtime_capture): bend3 smuggled an axiom into
# runtime through a comp-lambda capture and died at erasure. bend's ~
# law tpl checks once, f an opaque constant; the call passes f without
# ~, so the instance binds f as an erased runtime binder, and its live
# use is refused. (the runtime-axiom wall itself is pinned by
# compile_axiom_runtime.)
import Base

law magic:
  U32

law tpl:
  for ~f: U32 -> U32
  for x: U32
  U32

def tpl(f, x):
  f(x)

law main:
  U32

def main():
  tpl(y => (y + magic : U32), 1)

#|Error:
#|- expected : -f
#|- observed : f
#|Location: tpl~0
#|16 |
#|17>| def tpl(f, x):
#|18 |   f(x)
#|exit 1
