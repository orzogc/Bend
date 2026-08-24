# the quantity tag distinguishes Many from Lone even where Cop peeling
# makes the domains convertible: +Nat ~ Nat.copy peels to Nat, so the
# tag comparison is the ONLY wall between @+x: +Nat -> Nat and
# @x: Nat -> Nat. gutted, the two function types convert and a
# quantity cast needs no coercion at all.
import Base

assert relax:
  forall f: @+x: +Nat -> Nat
  @x: Nat -> Nat

def relax(f):
  f
$$ bend %
Error:
- expected : @x:Nat -> Nat
- observed : @+x:(+Nat ~ Nat.copy) -> Nat
Context:
- f : @+x:(+Nat ~ Nat.copy) -> Nat
Location: relax
