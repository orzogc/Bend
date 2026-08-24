# bend3 pinned match blocks as terms (any checked position, e.g. a plain
# let's continuation); bend4 parses the let-then-match body but a plain
# let's bare-constructor value cannot infer, so the spelling pins that
# annotation demand (y = {S{x} : Nt} is the idiom)
type Nt:
  Z{}
  S{p: Nt}

type Bl:
  T{}
  F{}

assert main:
  forall x: Nt
  forall b: Bl
  Nt

def main(x, b):
  y = S{x}
  b_ = b
  match b_:
    case T{}:
      y
    case F{}:
      S{y}
$$ bend % --show
Error:
- expected : an annotated term (cannot infer)
- observed : S{x}
Context:
- x : Nt
- b : Bl
Location: main
18 | def main(x, b):
19>|   y = S{x}
20 |   b_ = b
