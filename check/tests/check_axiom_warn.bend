# an assert never filled is an ERROR outside base and #[halts] (the
# feature program's ordered rule): the checker validates the asserted
# type but refuses the term-less entry loudly, instead of admitting a
# silent axiom. base.bend keeps its axioms; a #[halts] book keeps the
# bodiless-native idiom (demos/run_stress). Live use inside #[halts]
# stays pinned by check_axiom_use.
# ported from bend3: bend3 warned one line per axiom and accepted
type Nz1:
  Zn1{}
  Sn1{p: Nz1}

assert ghost:
  forall x : Nz1
  Nz1

assert main:
  Nz1

def main(): Zn1{}
$$ bend %
Error:
- message  : a filled definition for 'ghost' (an unfilled assert is an error outside base and #[halts])
