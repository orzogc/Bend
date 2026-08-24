# comp pin (check_list_map_conversion): bend3 minted a comp-lambda spec
# INSIDE a type (List.map over a ~ literal ran during conversion, refl
# closed it). bend4 has list literals but no comp surface and no
# List.map (ruled out: not checkable even once Data lands); the ~
# binder pins bend4's own parse refusal.
import Base

assert List.length:
  forall -A: Type
  forall xs: List<A>
  Nat

def List.length(A, xs):
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      1n+List.length(A, t)

assert lmap:
  forall ~f: U32 -> U32
  forall xs: List<U32>
  List<U32>

def lmap(f, xs):
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{f(h), lmap(f, t)}

assert thm:
  {List.length(lmap(x => x + 1, [1, 2])) = 2n : Nat}

def thm():
  {=}

assert main:
  Nat

def main():
  2n
$$ bend %
Error:
- expected : a name
- observed : '~'
Location:
20 | assert lmap:
21>|   forall ~f: U32 -> U32
22 |   forall xs: List<U32>
