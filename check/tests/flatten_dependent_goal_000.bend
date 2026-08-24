# bend3's dependent computed match: the goal mentions the scrutinee
# even(n) and the with-equality rewrites it. bend4's computed match
# never specializes, by design, so the applied spelling pins bend4's
# own refusal
# ported from bend3: the numeric column becomes a ctor column
type Bl:
  T{}
  F{}

type W:
  Z{}
  S{p: W}

assert not:
  forall a: Bl
  Bl

def not(a):
  match a:
    case T{}:
      F{}
    case F{}:
      T{}

assert even:
  forall a: W
  Bl

def even(a):
  match a:
    case Z{}:
      T{}
    case S{n}:
      not(even(n))

assert main:
  forall n: W
  {not(not(even(n))) == even(n) : Bl}

def main(n):
  \{T: {==}; F: {==}}(even(n))
$$ bend % --show
Error:
- expected : not(not(even(n)))
- observed : even(n)
Context:
- n : W
Location: main
40 | def main(n):
41>|   \{T: {==}; F: {==}}(even(n))
42 |
