# 4-ctor enum ladder, complete: all four arms close by computation;
# the proof value refolds to the ref (main's eta form replaces --eval)
type Dir:
  Up{}
  Rt{}
  Dn{}
  Lf{}

assert turn:
  forall d: Dir
  Dir

def turn(d):
  match d:
    case Up{}:
      Rt{}
    case Rt{}:
      Dn{}
    case Dn{}:
      Lf{}
    case Lf{}:
      Up{}

assert back:
  forall d: Dir
  Dir

def back(d):
  match d:
    case Up{}:
      Dn{}
    case Rt{}:
      Lf{}
    case Dn{}:
      Up{}
    case Lf{}:
      Rt{}

assert turn_turn:
  forall d: Dir
  {turn(turn(d)) == back(d) : Dir}

def turn_turn(d):
  match d:
    case Up{}:
      {==}
    case Rt{}:
      {==}
    case Dn{}:
      {==}
    case Lf{}:
      {==}

assert main:
  @d: Dir -> {turn(turn(d)) == back(d) : Dir}

def main():
  d => turn_turn(d)

$$ bend %
d => turn_turn(d)
