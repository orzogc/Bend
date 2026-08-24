# a BARE literal lambda application cannot infer: the redex head is a
# lambda, so the term needs an annotation (in a checked position -- a
# call argument -- the same lambda is legal everywhere).
# ported from bend3: bend3 reduced the bare redex at elaboration; bend4
# pins the cannot-infer refusal
import Base

assert main:
  U32

def main(): (x => x)(3)
$$ bend %
Error:
- expected : an annotated term (cannot infer)
- observed : x => x
Location: main
10 | 
11>| def main(): (x => x)(3)
12 |
