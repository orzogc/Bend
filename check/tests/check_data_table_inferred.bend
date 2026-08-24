# bend3 computed Data-ness from ctor field syntax, never from an
# annotation: List(U32) shared by its table with no `: Data` spelled.
# bend4 never classifies -- sum(xs) + sum(xs) is a double spend for any
# type, and it rides the explicit +xs binder, its Cop annotation
# carrying the local List.copy witness, strict. The base List and the
# [..] literal carry the surface.
# ported from bend3: the local List type is bend4's base List (ctor
# names are global: Con/Nil), the literal wears the brace Ann
import Base

assert List.copy:
  forall -c: Copiable(U32)
  forall t: List<U32>
  Copy(List<U32>, t) & Copy(List<U32>, t)

def List.copy(c, t):
  match t:
    case Nil{}:
      ((Nil{}, {==}), (Nil{}, {==}))
    case Con{h, tl}:
      ((hx, he), (hy, hf)) = U32.copy(h)
      ((tx, te), (ty, tf)) = List.copy(c, tl)
      s10 = Equal.cong(U32, List<U32>, z => Con{z, tl}, h, hx, he)
      s11 = Equal.cong(List<U32>, List<U32>, z => Con{hx, z}, tl, tx, te)
      t11 = Equal.trans(List<U32>, Con{h, tl}, Con{hx, tl}, Con{hx, tx}, s10, s11)
      s20 = Equal.cong(U32, List<U32>, z => Con{z, tl}, h, hy, hf)
      s21 = Equal.cong(List<U32>, List<U32>, z => Con{hy, z}, tl, ty, tf)
      t21 = Equal.trans(List<U32>, Con{h, tl}, Con{hy, tl}, Con{hy, ty}, s20, s21)
      ((Con{hx, tx}, t11), (Con{hy, ty}, t21))

assert sum:
  forall xs: List<U32>
  U32

def sum(xs):
  match xs:
    case Con{h, tl}:
      h + sum(tl)
    case Nil{}:
      0

assert main.out:
  U32

def main.out():
  +xs = {[1, 2] : (+ List<U32> ~ List.copy(U32.copy))}
  sum(xs) + sum(xs)

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
6
$$ bend % --seq
6
exit 0
$$ bend % --par
6
exit 0
$$ bend % --js
6
exit 0
