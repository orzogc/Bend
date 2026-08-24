# a `<-` bind line is do-block syntax ONLY: outside a do-block, `x <- e`
# is not grammar.
# ported from bend3: same law, bend4 error page
import Base

assert half:
  forall x: U32
  U32

def half(x): U32.div(x, 2)

assert main:
  U32

def main(): x <- half(10)
$$ bend %
Error:
- expected : 'def', 'type' or 'assert'
- observed : '<'
Location:
14 | 
15>| def main(): x <- half(10)
16 |
