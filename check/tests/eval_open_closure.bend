# bend3's --eval printed an unapplied def normalized UNDER its binders;
# bend4's snf keeps a bare ref closed (eval_toplevel_ref_print pins
# that), and the open rendering lives on the --show lane: the parsed
# body prints with its params peeled, exactly bend3's shape
import Base

assert pipe:
  forall f: U32 -> U32
  forall g: U32 -> U32
  U32 -> U32

def pipe(f, g):
  x => g(f(x))

assert main:
  Nat

def main():
  U32.to_nat(pipe(a => a + 1, b => b * 2)(5))
$$ bend % --show pipe
pipe = f => g => x => g(f(x))
$$ bend %
12n
