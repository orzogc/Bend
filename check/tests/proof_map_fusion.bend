# map fusion, proved by induction: the lambdas specialize inside the
# equation, the cons arm's stuck heads align, and the IH rewrite closes
# the tails -- specialization, computation and rewriting in one proof.
# ported from bend3: bend3's List module map becomes a local map over the
# base List (bend4's base has no map); infix ops become U32.add/U32.mul;
# map spends f per element, a + binder over an erased Copiable witness
# (dead at Cop formation, never demanded live: every map mention sits
# inside an equation), so the proof checks strict
import Base

assert map:
  forall -A: Type
  forall -B: Type
  forall -f.copy: Copiable(A -> B)
  forall +f: (+ (A -> B) ~ f.copy)
  forall xs: List<A>
  List<B>

def map(A, B, f.copy, f, xs):
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{f(h), map(A, B, f.copy, f, t)}

assert fuse:
  forall -mw: Copiable(U32 -> U32)
  forall xs: List<U32>
  {map(U32, U32, mw, x => U32.add(x, 1), map(U32, U32, mw, x => U32.mul(x, 2), xs)) == map(U32, U32, mw, x => U32.add(U32.mul(x, 2), 1), xs) : List<U32>}

def fuse(mw, xs):
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      %fuse(mw, t) : {Con{U32.add(U32.mul(h, 2), 1), map(U32, U32, mw, x => U32.add(x, 1), map(U32, U32, mw, x => U32.mul(x, 2), t))} == Con{U32.add(U32.mul(h, 2), 1), _} : List<U32>}
      {==}

$$ bend %
