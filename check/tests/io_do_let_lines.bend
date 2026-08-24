# let lines ride on do lines: a typed `y : U32 = 40` between binds is
# an ordinary let the monad desugar never touches (bend4's DoLet).
# The type position parses as a dom (no `=` suffix), so the let's own
# `=` survives to the do-statement reader - the c5ffbef fix, carried
# into this tree by the a34802d merge.
# ported from bend3: IO becomes base Result; bend3's untyped do-let
# (z = 2) does not exist in bend4's grammar and is not pinned here
import Base

assert run:
  Result<U32, U32>

def run():
  do Result<U32, U32>:
    x : U32 <- Done{2}
    y : U32 = 40
    return U32.add(x, y)

assert unwrap:
  forall r: Result<U32, U32>
  U32

def unwrap(r):
  match r:
    case Done{v}:
      v
    case Fail{x}:
      x

assert main:
  Nat

def main():
  U32.to_nat(unwrap(run()))
$$ bend %
42n
