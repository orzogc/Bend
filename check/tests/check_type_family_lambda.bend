# a lambda checked INTO Type is a type family: its binder is dead, and
# the family applies at use sites on both levels.
# ported from bend3
import Base

type Nl:
  Zl{}
  Sl{p: Nl}

assert fam:
  @_:Nl -> Type

def fam(): _ => U32

assert usef:
  forall n: Nl
  forall x: fam(n)
  fam(n)

def usef(n, x):
  x

assert main:
  fam(Zl{})

def main(): usef(Zl{}, 42)
$$ bend %
U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
