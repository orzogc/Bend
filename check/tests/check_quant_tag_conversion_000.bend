# function types convert by quantity tag before domain and codomain:
# @x and @-x over the same Nat -> Nat are NOT convertible. gutted, this
# program checks whole and forges contraction with no license: g rides
# the erased-domain type, so g(a) checks a dead (a use that costs
# nothing) and the tuple consumes a again -- an affine value duplicated
# through a quantity cast alone.
import Base

assert relax:
  forall f: @x: Nat -> Nat
  @-x: Nat -> Nat

def relax(f):
  f

assert dupl:
  forall a: Nat
  Nat & Nat

def dupl(a):
  g = relax(x => x)
  (g(a), a)

assert main:
  Nat & Nat

def main(): dupl(1n)
$$ bend %
Error:
- expected : @-x:Nat -> Nat
- observed : @x:Nat -> Nat
Context:
- f : @x:Nat -> Nat
Location: relax
