# the if/elif/else term: parse-time sugar emitting exactly the applied
# Bool match \{True: t; False: f}(c), elif chaining in the False arm.
# ported from bend3: conditions turn Bool (comparisons answer Bool,
# no U32 truthiness), re-tested binders ride + (affine core), and the
# dependent-goal half is dropped -- bend4's computed matches never
# specialize the goal, by design
import Base

assert g:
  forall x0: U32
  U32

def g(x0):
  +x = {x0 : +U32}
  if x < 3: 10 elif x < 6: 20 else: 30

assert g_twin:
  forall x0: U32
  U32

def g_twin(x0):
  +x = {x0 : +U32}
  \{False: \{False: 30; True: 20}(U32.is_lt(x, 6)); True: 10}(U32.is_lt(x, 3))

assert agree:
  forall x0: U32
  U32

def agree(x0):
  +x = {x0 : +U32}
  if U32.is_eq(g(x), g_twin(x)): 1 else: 0

assert nest:
  forall a: Bool
  forall b: Bool
  U32

def nest(a, b):
  if a:
    if b: 3 else: 2
  else:
    1

assert main.out:
  U32

def main.out():
  agree(0) + agree(2) + agree(3) + agree(5) + agree(6) + agree(9) + 10 * (nest(True{}, True{}) + nest(True{}, False{}) + nest(False{}, True{}))

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
66
$$ bend % --seq
66
exit 0
$$ bend % --par
66
exit 0
$$ bend % --js
66
exit 0
