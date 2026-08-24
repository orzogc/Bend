# THE JOINT-MATCH FUSION GUARD (Taelin order): a joint in-order match over
# params fuses into ONE point-free tree -- no applied spine, no aux mint.
# This pin is the canonical le tree, byte-exact. It must NEVER be
# regenerated to an applied (a => b => ...(a)) or minted (le~N) shape: that
# regression class felled bend-base whole (List.take's halt, the Bit.xor
# lemmas) and must be an instant, legible red here instead.
type Bool:
  T{}
  F{}

type Nat:
  Z{}
  S{p: Nat}

assert le:
  forall a: Nat
  forall b: Nat
  Bool

def le(a, b):
  match a, b:
    case Z{}, y:
      T{}
    case S{p}, Z{}:
      F{}
    case S{p}, S{q}:
      le(p, q)

assert main:
  Bool

def main():
  le(S{Z{}}, S{S{Z{}}})

$$ bend % --show le
le = \{Z: (b => T{}); S: (p => \{Z: F{}; S: (q => le(p, q))})}
