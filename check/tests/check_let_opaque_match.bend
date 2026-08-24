# bend3's sealed-let pin: a match on a let-bound 1e9-deep call
# dispatched on the abstract binder and never ran it. bend4 has no
# seal: a let-then-match is a computed match on the let variable and
# simply checks -- the literal-0 arm is a structural word pattern, the
# catch-all takes the rest, and main answers 0
import Base

assert probe:
  forall s: U32
  U32

def probe(s):
  w = s * 3
  match w:
    case 0:
      0
    case w:
      1

assert main:
  U32

def main():
  0
$$ bend %
U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
