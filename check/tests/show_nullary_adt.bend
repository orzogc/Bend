# the shower prints a nullary ADT as its bare name: `U32<>` was
# emitted into every error and --show while the parser refuses that
# text, since <> is the cons operator (AUDIT 6b pinned); an applied
# ADT keeps its angle brackets
import Base

assert scalar:
  Type

def scalar():
  U32

assert table:
  Type

def table():
  Map<U32>

assert main:
  Nat

def main():
  U32.to_nat(3)
$$ bend % --show scalar
scalar = U32
$$ bend % --show table
table = Map<U32>
$$ bend %
3n
