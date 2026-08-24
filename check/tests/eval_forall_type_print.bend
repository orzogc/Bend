# evaluating a dependent forall TYPE prints the named-binder @ form
# (bend4 spells a zero-arg family instance U32<>).
# ported from bend3: the def becomes main (the CLI evaluates main only)
import Base

assert main:
  Type

def main():
  @n:U32 -> {n == n : U32}
$$ bend %
@n:U32 -> {n == n : U32}