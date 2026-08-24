# bend3's named-column alias `match (k = x)` names a column over the
# bare binder; bend4's match takes bare scrutinees only, so the alias
# form pins bend4's own refusal
# ported from bend3: the numeric column becomes a ctor column
type W:
  Z{}
  S{p: W}

assert main:
  forall x: W
  W

def main(x):
  match (k = x):
    case Z{}:
      Z{}
    case S{p}:
      x
$$ bend % --show
Error:
- expected : a term
- observed : ')'
Location:
13 | def main(x):
14>|   match (k = x):
15 |     case Z{}:
