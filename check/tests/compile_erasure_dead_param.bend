# bend3 erased a - parameter at EMISSION even when the body mentioned
# it in dead positions; bend4's checker refuses every such mention
# outright, so the emission cases cannot exist -- the dead let's
# operand is the refusal
import Base

assert opnd:
  forall -x: U32
  U32

def opnd(x):
  y = x + 1
  0

assert main:
  U32

def main():
  opnd(5)
$$ bend %
Error:
- expected : -x
- observed : x
Location: opnd
