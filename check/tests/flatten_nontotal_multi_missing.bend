# error quality: a match missing several constructors names each one.
# ported from bend3
type Abc:
  Aa1{}
  Bb1{}
  Cc1{}

assert f:
  forall x: Abc
  Abc

def f(x):
  match x:
    case Aa1{}:
      Aa1{}

assert main:
  Abc

def main(): f(Aa1{})
$$ bend %
Error:
- expected : cases for Bb1, Cc1
- observed : \{}
Location: f
12 | def f(x):
13>|   match x:
14 |     case Aa1{}:
