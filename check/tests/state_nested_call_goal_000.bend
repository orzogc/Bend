# 4-ctor enum ladder, state 0: a NESTED stuck dispatch (turn(turn(d)))
# renders as the ref chain, no arm literal leaking
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
  {==}

$$ bend %
Error:
- expected : turn(turn(d))
- observed : back(d)
Context:
- d : Dir
Location: turn_turn
43 | def turn_turn(d):
44>|   {==}
45 |
