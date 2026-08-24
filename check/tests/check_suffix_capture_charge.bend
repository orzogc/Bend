# bend3 priced a suffix capture (a let-bound value re-charged at every
# split leaf); bend4 has no splits: the let-then-match checks as a
# computed match on the let variable, the affine wall owns the class
# (the capture twins pin it), and main answers 0
import Base

assert use2:
  forall n: Nat
  U32

def use2(n):
  k = n
  match k:
    case Zero{}:
      0
    case Succ{p}:
      1

assert main:
  U32

def main():
  0
$$ bend %
U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
