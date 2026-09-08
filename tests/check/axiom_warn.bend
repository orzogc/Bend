# an assert never filled is an OPEN CLAIM: the checker validates the
# asserted type, keeps the entry dead, and counts it as a TODO (the
# CLI report says so; --to refuses); a run still prints main, since
# nothing live touches the claim. base.bend keeps its axioms (the
# bodiless-native idiom). Live use stays pinned by check_axiom_use.
# ported from bend3: bend3 warned one line per axiom and accepted
type Nz1 is Data:
  Zn1{}
  Sn1{p: Nz1}

law ghost:
  for x: Nz1
  Nz1

law main:
  Nz1

def main(): Zn1{}

#|Zn1{}
