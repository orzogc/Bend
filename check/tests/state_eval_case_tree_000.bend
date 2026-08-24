# word-switch ladder, complete: the IH rewrite closes the miss arm;
# the checked proof's value displays as the REF chain (bend4's show
# refolds a stuck match to its ref -- bend3's --eval case-tree literal
# has no bend4 face; main's eta form replaces the --eval lane)
# ported from bend3: U32 switch -> Nat; rewrite takes its motive
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
      %ones_twos(n) : {S{ones(n)} == S{_} : MN}
      {==}

assert main:
  @n: Nat -> {ones(n) == twos(n) : MN}

def main():
  n => ones_twos(n)

$$ bend %
n => ones_twos(n)
