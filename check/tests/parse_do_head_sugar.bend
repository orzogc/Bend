# the do-head opens its type arguments with a GLUED angle group:
# `do M<A>:` is the form (bend3 pinned the <> sugar over an
# application head; bend4's grammar is the angle group itself).
# ported from bend3
type Nn3:
  Zz3{}
  Ss3{p: Nn3}

type Id_<A: Type>:
  MkId{v: A}

assert Id_.pure:
  forall -A: Type
  forall v: A
  Id_<A>

def Id_.pure(A, v):
  MkId{v}

assert Id_.bind:
  forall -A: Type
  forall -B: Type
  forall m: Id_<A>
  forall f: A -> Id_<B>
  Id_<B>

def Id_.bind(A, B, m, f):
  match m:
    case MkId{v}:
      f(v)

assert run:
  forall m: Id_<Nn3>
  Nn3

def run(m):
  match m:
    case MkId{v}:
      v

assert main:
  Nn3

def main():
  run(do Id_<Nn3>:
        x : Nn3 <- MkId{Ss3{Zz3{}}}
        return Ss3{x})
$$ bend %
Ss3{Ss3{Zz3{}}}
