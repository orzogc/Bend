# destructuring a DEPENDENT pair: (v, e) = q binds the witness and a
# proof whose type mentions it; the erased proof rides along.
# ported from bend3
import Base

assert use:
  forall q: &x:U32 -> {x == 3 : U32}
  U32

def use(q):
  (v, e) = q
  v

assert main:
  U32

def main(): use((3, {==}))
$$ bend %
U32{WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
