# a match after => owns its case rows wherever they sit: bend4's one
# layout law is the case-column rule for NESTED matches, so a top match
# takes shallower case rows too.
# ported from bend3: bend3 rejected cases left of the match keyword;
# bend4 pins the opposite (ownership by innermost match)
type Bb7:
  Tt7{}
  Ff7{}

assert notb:
  forall b: Bb7
  Bb7

def notb(b): match b:
  case Tt7{}:
    Ff7{}
  case Ff7{}:
    Tt7{}

assert main:
  Bb7

def main(): notb(Tt7{})
$$ bend %
Ff7{}
