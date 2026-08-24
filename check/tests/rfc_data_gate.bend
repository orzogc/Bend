#[halts]
# bend3's gate inverted by ruling: there +T was well-formed ONLY on a
# Data-kinded T (cloning a lambda was inconsistent), so +(U32 -> U32)
# refused at formation. bend4's + is a binder QUANTITY and sharing is
# generic over terms -- it reaches closures (the d580b83 class) -- so
# the same spelling is accepted under #[halts] and the shared f applies
# twice.
# ported from bend3: f spends twice (f(f(x))) to make the sharing live;
# the refusal golden becomes the value 4
import Base

assert ap:
  forall +f: U32 -> U32
  forall x: U32
  U32

def ap(f, x):
  f(f(x))

assert main.out:
  U32

def main.out(): ap(y => y + 1, 2)

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
