# operator chains are ordinary calls under the affine core: a binder
# consumed by two operands is refused (bend3 priced the chain; bend4
# walls it)
import Base

assert f:
  forall x: U32
  U32

def f(x):
  x + x

assert main:
  U32

def main():
  f(3)
$$ bend %
Error:
- expected : x
- observed : x (consumed more than once)
Location: f
