# bare statements sequence in one body; a brace group with no top-level
# statement stays equation territory ({a == b : T} is an equation,
# never a statement)
# ported from bend3: word literals become ctor builds through a def (a
# let's ctor RHS cannot infer; a U32 literal shows as its Word chain)
type W:
  Z{}
  S{p: W}

assert inc:
  forall a: W
  W

def inc(a):
  S{a}

assert refl_w:
  {S{Z{}} == S{Z{}} : W}

def refl_w(): {==}
assert refl_f:
  {(x => x) == (x => x) : W -> W}

def refl_f(): {==}

assert main:
  forall a: W
  W

def main(a):
  x = inc(a)
  y = inc(x)
  z = inc(y)
  w = inc(z)
  w
$$ bend % --show
inc = a => S{a}
refl_w = {==}
refl_f = {==}
main = a => x = inc(a); y = inc(x); z = inc(y); w = inc(z); w
