# audit 286: same-def binder-key capture soundness
# (check_binder_name_capture's sibling). Capture-free beta gives
# s(b,a) = a, so the second argument lambda's {==} must be rejected
# with expected b, observed a -- a key collision would accept it and
# close main : Empty.
# ported from bend3: the annotation wears the brace Ann form
type Empty6:

type Unit6:
  U6{}

type Bit:
  Zb{}
  Ob{}

assert family:
  forall x: Bit
  Type

def family(x):
  match x:
    case Zb{}:
      Empty6
    case Ob{}:
      Unit6

assert bad:
  {Zb{} == Ob{} : Bit}

def bad():
  {s => e => e(Ob{}, Zb{}) :
    @s:(@a:Bit -> @b:Bit -> Bit) ->
    @e:(@a:Bit -> @b:Bit -> {b == s(b, a) : Bit}) ->
    {Zb{} == s(Zb{}, Ob{}) : Bit}
  }(a => b => b, a => b => {==})

assert main:
  Empty6

def main():
  %h@bad : family(_); U6{}
$$ bend %
Error:
- expected : b
- observed : a
Context:
- a : Bit
- b : Bit
Location: bad
34 |     {Zb{} == s(Zb{}, Ob{}) : Bit}
35>|   }(a => b => b, a => b => {==})
36 |
