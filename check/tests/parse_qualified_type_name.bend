# qualified names are uniform across entry kinds: a datatype may be
# declared at `M.Name` too (its ctors stay bare -- they resolve exactly,
# never by qualification).
# ported from bend3
import Base

type Box.T<A: Type>:
  Mkbx{x: A}

assert box.get:
  forall b: Box.T<Unit>
  Unit

def box.get(b):
  match b:
    case Mkbx{x}:
      x

assert main:
  Unit

def main(): box.get(Mkbx{Unit{}})
$$ bend %
Unit{}
