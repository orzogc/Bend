# regression (AUDIT 4a): an erased local that is then matched is
# refused -- body_flatten once beta-contracted the binder into a bare
# application, so the None quantity never reached the checker and the
# erased value was silently matched live
import Base

assert leak:
  forall z: Bool
  Bool

def leak(z):
  -x = {z : Bool}
  match x:
    case True{}:
      True{}
    case False{}:
      False{}

assert main:
  Bool

def main():
  True{}
$$ bend %
Error:
- expected : -x
- observed : x
Context:
- z : Bool
Location: leak
11 | def leak(z):
12>|   -x = {z : Bool}
13 |   match x:
