# bend3's ++ died un-opened inside inferred types; bend4's ++ opens to
# String.append at parse, so an equation SPELLED with ++ meets its
# rewrite motive written on the opened call -- the append identity
# closes by induction through it (the comp ~ half of the original died
# with comp, pinned by the spec_comp refusals)
import Base

assert append_id:
  forall s: String
  {s ++ "" == s : String}

def append_id(s):
  match s:
    case SNil{}:
      {==}
    case SCon{c, t}:
      %append_id(t) : {SCon{c, String.append(t, "")} == SCon{c, _} : String}
      {==}

assert main.out:
  Nat

def main.out():
  0n

assert main:
  IO(Unit)

def main():
  IO.print(String.append(Nat.show(main.out()), "n"))
$$ bend %
0n
$$ bend % --seq
0n
exit 0
$$ bend % --par
0n
exit 0
$$ bend % --js
0n
exit 0
