# the dead branch is a term: \{} applied to an EMPTY-typed value checks
# against every goal (no cases to cover) and stays stuck on the param
type Emp:

assert main:
  forall e: Emp
  Emp

def main(e):
  (\{})(e)
$$ bend % --show
main = e => \{}(e)
