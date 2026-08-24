# comp pin (parse_comp_arrow_position): bend3's comp arrow -~> in a
# term-level type position (a let's type) named its own page. bend4 has
# no -~> arrow anywhere (and no typed let: the Ann brace {v : T} is the
# spelling); the arrow pins bend4's own parse refusal.
import Base

assert f:
  forall x: U32
  U32

def f(x):
  h = {y => y : U32 -~> U32}
  h(x)

assert main:
  U32

def main():
  f(3)
$$ bend %
Error:
- expected : a term
- observed : '~'
Location:
11 | def f(x):
12>|   h = {y => y : U32 -~> U32}
13 |   h(x)
