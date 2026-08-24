# comp-splice pin (comp_splice_tuple_goal): bend3's tuple-goal templates
# (a generic ctor field holding a tuple of both worlds). bend4 has no
# comp surface; the ~ binder pins bend4's own parse refusal. (bend3's
# R.Done/R.Fail respell as bare RDone/RFail: bend4 ctor names are bare
# and Result owns Done/Fail.)
import Base

type R<-A: Type>:
  RDone{v: (U32 & A)}
  RFail{}

assert wrap:
  forall ~f: U32 -> U32
  forall x: U32
  (U32 & U32)

def wrap(f, x):
  (7, f(x))

assert main:
  U32

def main():
  (a, b) = wrap(y => y + 1, 34)
  a + b
$$ bend %
Error:
- expected : a name
- observed : '~'
Location:
12 | assert wrap:
13>|   forall ~f: U32 -> U32
14 |   forall x: U32
