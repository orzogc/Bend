# a selected arm whose body is \{} answers \{}, not the refolded call
# (AUDIT 13 tail: the eliminator read the value as match failure);
# a genuinely stuck empty match still refolds to its ref.
import Base

assert pick:
  forall b: Bool
  @e:Empty -> Bool

def pick(b):
  match b:
    case True{}: \{}
    case False{}: \{}

assert use:
  forall e: Empty
  Bool

def use(e):
  Empty.absurd(Bool, e)

assert main:
  ((@e:Empty -> Bool) & (@e:Empty -> Bool))

def main():
  (pick(True{}), e => use(e))
$$ bend %
Tuple{\{}, e => Empty.absurd(Bool, e)}
