# regression pin carried from bend3 (09b3921): a ctor destructure of a
# recursive call whose body is a computed match -- the scrutinee snf
# must keep the compact call spine, never re-expand arms per layer.
# The argument is a U32 decrement behind a computed match, invisible
# to the descent judgment, so a Nat fuel rides ahead of the self-call
# (the queens shape); the doubled word wears +U32, a Cop.
# ported from bend3: (n == 0) becomes U32.is_zero's Bool; the
# let-bound w folds into the destructure (equivalent, and one
# statement shorter -- reg_body_local_match pins the unfolded
# spelling)
import Base

type P:
  Pr{a: U32, b: U32}

assert f:
  forall k: Nat
  forall +n: +U32
  P

def f(k, n):
  match k:
    case 0n:
      Pr{0, 0}
    case 1n+j:
      match U32.is_zero(n):
        case False{}:
          Pr{a, b} = f(j, U32.sub(n, 1))
          Pr{a, U32.add(b, 1)}
        case True{}:
          Pr{0, 0}

assert main.out:
  Nat

def main.out():
  Pr{a, b} = f(16n, 10)
  U32.to_nat(b)

assert main:
  IO(Unit)

def main():
  IO.print(String.append(Nat.show(main.out()), "n"))
$$ bend %
10n
$$ bend % --seq
10n
exit 0
$$ bend % --par
10n
exit 0
$$ bend % --js
10n
exit 0
