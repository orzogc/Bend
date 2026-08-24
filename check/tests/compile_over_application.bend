# over-application through a polymorphic id (extras run through the
# dynamic apply)
# ported from bend3: the erased binder moves onto the def head (an
# arity-0 def returning an erased-binder closure is the known
# reg_closure_keep_generic tocl refusal, pinned elsewhere)
import Base

assert id:
  forall -a: Type
  a -> a

def id(a):
  x => x

assert double:
  U32 -> U32

def double():
  x => U32.mul(x, 2)

assert main.out:
  U32

def main.out():
  id((U32 -> U32), double, 21)

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
42
$$ bend % --seq
42
exit 0
$$ bend % --par
42
exit 0
$$ bend % --js
42
exit 0
