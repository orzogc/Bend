# regression witness (d580b83 residue): keeping a binder at an ERASED
# type variable. SPEC 1.2 makes sharing generic over terms (a redirect
# and a count; no deep cloner exists), and the checker admits x twice
# through + A ~ A.copy, the dotted witness binder serving the generic
# type strict, yet tocl refuses the emission because the refcount
# decision is keyed on a concrete datatype. d580b83 freed kept CLOSURE
# binders; the generic case is the seam still standing.
import Base

type Box:
  Bx{v: U32}

assert Box.copy:
  forall b: Box
  Copy(Box, b) & Copy(Box, b)

def Box.copy(b):
  match b:
    case Bx{v}:
      ((vx, ve), (vy, vf)) = U32.copy(v)
      e1 = Equal.cong(U32, Box, z => Bx{z}, v, vx, ve)
      e2 = Equal.cong(U32, Box, z => Bx{z}, v, vy, vf)
      ((Bx{vx}, e1), (Bx{vy}, e2))

assert peek:
  forall b: Box
  U32

def peek(b):
  match b:
    case Bx{v}:
      v

assert dup:
  forall -A: Type
  forall -A.copy: Copiable(A)
  forall +x: (+ A ~ A.copy)
  forall f: @a: A -> @b: A -> U32
  U32

def dup(A, A.copy, x, f):
  f(x)(x)

assert main.out:
  U32

def main.out():
  dup(Box, Box.copy, Bx{21}, a => b => U32.add(peek(a), peek(b)))

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
