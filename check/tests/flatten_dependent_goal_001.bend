# bend3's nested dependent computed matches: the goal mentions both
# scrutinees. bend4's computed match never specializes, by design, so
# the applied spelling pins bend4's own refusal
# ported from bend3: the numeric columns become ctor columns
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

assert and:
  forall a: Bl
  forall b: Bl
  Bl

def and(a, b):
  match a, b:
    case T{}, b:
      b
    case F{}, b:
      F{}

assert pos:
  forall a: W
  Bl

def pos(a):
  match a:
    case Z{}:
      F{}
    case n:
      T{}

assert odd:
  forall a: W
  Bl

def odd(a):
  match a:
    case Z{}:
      F{}
    case S{n}:
      not(odd(n))

assert main:
  forall n: W
  {and(pos(n), odd(n)) == and(odd(n), pos(n)) : Bl}

def main(n):
  \{T: \{T: {==}; F: {==}}(odd(n)); F: \{T: {==}; F: {==}}(odd(n))}(pos(n))
$$ bend % --show
Error:
- expected : and(pos(n), odd(n))
- observed : and(odd(n), pos(n))
Context:
- n : W
Location: main
62 | def main(n):
63>|   \{T: \{T: {==}; F: {==}}(odd(n)); F: \{T: {==}; F: {==}}(odd(n))}(pos(n))
64 |
