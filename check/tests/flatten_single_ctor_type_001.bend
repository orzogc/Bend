# red-team pin: a computed (annotated) scrutinee whose type is a 1-ctor
# datatype flattens to the single case (no NotTotal, no default arm)
type W:
  Z{}
  S{p: W}

type One:
  Only{v: W}

assert mk:
  forall x: W
  One

def mk(x):
  Only{x}

assert main:
  forall o: One
  W

def main(o):
  \{Only: (v => S{v})}({o : One})
$$ bend % --show
mk = x => Only{x}
main = o => \{Only: (v => S{v})}({o : One})
