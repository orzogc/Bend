# `P = e : T` -- bend3 folded the annotation into {e : T} before the
# match opens; bend4 spells the annotation as the brace form directly
# ported from bend3: local Pair renamed (base owns the def name)
import Base

type Duo:
  Mk{a: U32, b: U32}

assert main:
  forall p: Duo
  Duo

def main(p):
  Mk{x, y} = {p : Duo}
  Mk{y, x}
$$ bend % --show
main = p => \{Mk: (x => y => Mk{y, x})}({p : Duo})
