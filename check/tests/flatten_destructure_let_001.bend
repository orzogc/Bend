# bend3 pinned `P = e` as a statement AFTER a plain let; bend4 agrees:
# the plain let is a body statement, the destructure follows it, and
# the flatten renders the match-lambda applied to the destructured
# variable under the let
import Base

type Duo:
  P{a: U32, b: U32}

assert main:
  forall p: Duo
  U32

def main(p):
  q = p
  P{a, b} = q
  a - b
$$ bend % --show
main = p => q = p; \{P: (a => b => U32.sub(a, b))}(q)
