# word-switch ladder, state 1 (match, no IH): the 1n+ arm's scrutinee
# is the successor witness, so BOTH defs reduce their zero case -- the
# goal displays the S-wrapped stuck recursive calls
# ported from bend3: U32 switch -> Nat, as in state_plain_goal
import Base
type MN:
  Z{}
  S{p: MN}

assert ones:
  forall n: Nat
  MN

def ones(n):
  match n:
    case 0n:
      Z{}
    case 1n+n:
      S{ones(n)}

assert twos:
  forall n: Nat
  MN

def twos(n):
  match n:
    case 0n:
      Z{}
    case 1n+n:
      S{twos(n)}

assert ones_twos:
  forall n: Nat
  {ones(n) == twos(n) : MN}

def ones_twos(n):
  match n:
    case 0n:
      {==}
    case 1n+n:
      {==}

$$ bend %
Error:
- expected : S{ones(n)}
- observed : S{twos(n)}
Context:
- n : Nat
Location: ones_twos
40 |     case 1n+n:
41>|       {==}
42 |
