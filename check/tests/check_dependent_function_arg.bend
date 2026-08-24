# a dependent function as an ARGUMENT: f : @m:Nm -> P(m) checks against
# an opaque family P and instantiates at the call's index.
# ported from bend3
import Base

type Nm:
  Zm{}
  Sm{p: Nm}

assert Fam:
  forall n: Nm
  Type

def Fam(n):
  match n:
    case Zm{}:
      U32
    case Sm{p}:
      Nm

assert mk:
  forall n: Nm
  Fam(n)

def mk(n):
  match n:
    case Zm{}:
      3
    case Sm{p}:
      Sm{p}

assert apply:
  forall -P: @_:Nm -> Type
  forall f: @m:Nm -> P(m)
  forall n: Nm
  P(n)

def apply(P, f, n):
  f(n)

assert main:
  Fam(Zm{})

def main(): apply(Fam, mk, Zm{})
$$ bend %
U32{WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
