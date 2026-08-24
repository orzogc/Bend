# word-switch ladder, state 0: the whole goal stuck on the open var --
# both sides render as REF calls (never an internal match literal)
# ported from bend3: the U32 switch (case 0 / case 1+n) has no bend4
# surface, so the ladder counts on Nat (0n / 1n+n)
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
  {==}

$$ bend %
Error:
- expected : ones(n)
- observed : twos(n)
Context:
- n : Nat
Location: ones_twos
36 | def ones_twos(n):
37>|   {==}
38 |
