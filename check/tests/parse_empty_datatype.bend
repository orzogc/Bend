# audit: a zero-constructor datatype is `type Void:` -- the next
# def/type-headed entry ends it.
# ported from bend3: the match moves behind a def (no literal-ctor
# scrutinee), \{} eliminates the empty type
type Void:

type Uu1:
  One{}

assert absurd:
  forall v: Void
  Uu1

def absurd(v): \{}(v)

assert pick:
  forall u: Uu1
  Uu1

def pick(u):
  match u:
    case One{}:
      One{}

assert main:
  Uu1

def main():
  pick(One{})
$$ bend %
One{}
