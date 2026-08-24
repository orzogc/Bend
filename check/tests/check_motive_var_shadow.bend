# the rewrite motive is one term binding `_` alone: an inner lambda in
# the motive is an ordinary lambda, and only `_` names the rewritten
# position.
# ported from bend3: bend3's motive was a real lambda m => ..; bend4's
# motive binds _ and folds the right side into the left
import Base

type Bxc:
  Mkc{f: U32 -> U32}

assert ap:
  forall b: Bxc
  forall n: U32
  U32

def ap(b, n):
  match b:
    case Mkc{f}:
      f(n)

assert swap:
  forall a: U32
  forall b: U32
  forall e: {a == b : U32}
  {ap(Mkc{w => w}, a) == ap(Mkc{w => w}, b) : U32}

def swap(a, b, e):
  %h@e : {ap(Mkc{w => w}, a) == ap(Mkc{w => w}, _) : U32}; {==}

assert main:
  U32

def main(): ap(Mkc{w => w}, 7)
$$ bend %
U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
