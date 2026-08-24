# regression (AUDIT 2b, the legal half): a later framed cell whose TYPE
# mentions an earlier cell checks -- the sequential lets make the
# written telescope real. The import line carries AUDIT 6a's witness:
# extra spaces and a trailing comment lex like the rest of the file.
import   Base  # the import head obeys the lexer

assert dup_eq:
  forall m: Nat
  Nat

def dup_eq(m):
  match n : Nat = m, e : {n == n : Nat} = {==}:
    case k, pf:
      k
    return Nat

assert main:
  Nat

def main():
  dup_eq(3n)
$$ bend %
3n
