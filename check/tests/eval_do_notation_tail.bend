# a raw expression as a do-block's last line is the monadic tail, used
# as-is; a bind line's type B is per-line (here Unit) while the head's
# last param stays the block's result type -- and the Fail
# short-circuits through Result.bind.
# ported from bend3: base Result (Done/Fail); bend4 has no match-in-do
# (match heads a def body, not a term), so the bend3 tail's match
# collapses to the pure tail it computed to; result 7 shown as a Nat
import Base

assert boom:
  @x:U32 -> Result<U32, Unit>

def boom():
  x => Fail{x}

assert run:
  Result<U32, U32>

def run():
  do Result<U32, U32>:
    u : Unit <- boom(7)
    Result.pure(U32, U32, 1)

assert unwrap:
  forall r: Result<U32, U32>
  U32

def unwrap(r):
  match r:
    case Done{v}:
      v
    case Fail{x}:
      x

assert main.out:
  Nat

def main.out():
  U32.to_nat(unwrap(run()))

assert main:
  IO(Unit)

def main():
  IO.print(String.append(Nat.show(main.out()), "n"))
$$ bend %
7n
$$ bend % --seq
7n
exit 0
$$ bend % --par
7n
exit 0
$$ bend % --js
7n
exit 0
