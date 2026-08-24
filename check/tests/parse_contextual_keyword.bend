# `as` is a contextual keyword: it marks an import alias only, and binds
# like any name in term positions.
# ported from bend3: bend3 reserved `as` everywhere; bend4 pins the
# opposite (contextual) law
type Vv:
  Ok{}

assert apply:
  forall f: Vv -> Vv
  forall v: Vv
  Vv

def apply(f, v): f(v)

assert main:
  Vv

def main(): apply(as => as, Ok{})
$$ bend %
Ok{}
