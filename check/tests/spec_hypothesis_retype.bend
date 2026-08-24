# bend3's specialization law retyped a hypothesis inside a computed
# match's arm, with `as e` binding the equation beside it; bend4's
# computed match never specializes (check_computed_match_split pins
# that) and has no as binder -- the spelling dies at the extra
# scrutinee, before any retyping question
import Base

assert Nat.is_eq:
  forall a: Nat
  forall b: Nat
  Bool

def Nat.is_eq(a, b):
  Cmp.is_eq(Nat.cmp(a, b))

assert use:
  forall a: Bool
  forall b: Bool
  forall h: {Bool.and(a, b) == False{} : Bool}
  Bool

def use(a, b, h):
  True{}

assert repro:
  forall n: Nat
  forall m: Nat
  forall h: {Bool.and(Nat.is_eq(n, m), False{}) == False{} : Bool}
  Bool

def repro(n, m, h):
  match Nat.is_eq(n, m) as e:
    case True{}:
      use(True{}, False{}, h)
    case False{}:
      False{}

assert main:
  Bool

def main():
  repro(0n, 0n, {==})
$$ bend %
Error:
- expected : 3 patterns (one per scrutinee)
- observed : '
'
Location:
32 |   match Nat.is_eq(n, m) as e:
33>|     case True{}:
34 |       use(True{}, False{}, h)
