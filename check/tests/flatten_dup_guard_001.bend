# bend3's ADT dup guard scrutinized the same var twice in one group;
# bend4's core is affine, so the same spelling pins bend4's own refusal
type Nat:
  Z{}
  S{p: Nat}

type R:
  R0{}
  R1{}

assert main:
  forall a: Nat
  R

def main(a):
  match a, a:
    case Z{}, x:
      R0{}
    case S{p}, x:
      R1{}
$$ bend % --show
Error:
- message  : match scrutinees in binder order (this variable is unbound, consumed, or out of order: reorder the match)
Location:
15 | def main(a):
16>|   match a, a:
17 |     case Z{}, x:
