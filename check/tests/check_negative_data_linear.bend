# negative datatypes are allowed (no positivity checker): a HOAS-style
# Term with a function field is harmless when used linearly, since
# closures can never satisfy a shared demand.
# ported from bend3
import Base

type Tm:
  Lm{f: Tm -> Tm}
  Vm{n: U32}

assert app9:
  forall t: Tm
  forall x: Tm
  Tm

def app9(t, x):
  match t:
    case Lm{f}:
      f(x)
    case Vm{n}:
      Vm{n}

assert main:
  Tm

def main(): app9(Lm{x => x}, Vm{7})
$$ bend %
Vm{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
