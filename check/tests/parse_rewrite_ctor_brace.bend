# Cross-type ("untyped global") rewrite -- the faithful attack. Given e
# at carrier Opt(Empty)->Opt(Empty), an untyped substitution would
# coerce it into an Opt(Unit)->Opt(Unit) goal. The type-checked motive
# REJECTS this: the abstracted motive variable cannot have both carrier
# types.
# ported from bend3: bend4's rewrite spells the motive explicitly, and
# the guard fires as the carrier mismatch
type Emp8:

type Un8:
  Uu8{}

type Opt8<A: Type>:
  Zer8{}
  One8{x: A}

assert bad_fun:
  forall e: {(x => x) == (x => Zer8{}) : Opt8<Emp8> -> Opt8<Emp8>}
  {(x => x) == (x => Zer8{}) : Opt8<Un8> -> Opt8<Un8>}

def bad_fun(e):
  %q@e : {(x => x) == _ : Opt8<Un8> -> Opt8<Un8>}; {==}

assert main:
  Un8

def main(): Uu8{}
$$ bend %
Error:
- expected : @_:Opt8<Un8> -> Opt8<Un8>
- observed : @_:Opt8<Emp8> -> Opt8<Emp8>
Context:
- e : {(x => x) == (x => Zer8{}) : @_:Opt8<Emp8> -> Opt8<Emp8>}
- _ : @_:Opt8<Emp8> -> Opt8<Emp8>
- q : {(x => x) == _ : @_:Opt8<Emp8> -> Opt8<Emp8>}
Location: bad_fun