# a failed proof is an ORDINARY local type error: the arm that forgot
# its IH rewrite reports the two stuck sides at the {==}, with context.
# ported from bend3
type Nh:
  Zh{}
  Sh{p: Nh}

assert add:
  forall a: Nh
  forall b: Nh
  Nh

def add(a, b):
  match a:
    case Zh{}:
      b
    case Sh{p}:
      Sh{add(p, b)}

assert add_zero:
  forall a: Nh
  {add(a, Zh{}) == a : Nh}

def add_zero(a):
  match a:
    case Zh{}:
      {==}
    case Sh{p}:
      {==}
$$ bend %
Error:
- expected : Sh{add(p, Zh{})}
- observed : Sh{p}
Context:
- p : Nh
Location: add_zero
28 |     case Sh{p}:
29>|       {==}
30 |
