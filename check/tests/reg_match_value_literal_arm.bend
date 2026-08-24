# an APPLIED annotated match value mixing a literal arm with a
# point-free ref arm, inlined into a CUT position (an argument of the
# enclosing call). The same mix compiles in tail position and through
# a hof closure value (reg_match_pointfree), and applied all-ref or
# lambda/ref mixes compile anywhere -- only the value-arm/ref-arm mix
# under a cut refuses (a rest-argument lambda/ref mix under a cut
# refuses the same way)
import Base

assert pf_arm:
  forall n: Nat
  Nat

def pf_arm(n):
  {\{Zero: 1n; Succ: Nat.double} : Nat -> Nat}(n)

assert main.out:
  U32

def main.out():
  U32.from_nat(pf_arm(3n))

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
4
$$ bend % --seq
4
exit 0
$$ bend % --par
4
exit 0
$$ bend % --js
4
exit 0
