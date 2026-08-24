# bend3's T/F word-wrap misfired ctor patterns on a numeric scrutinee
# and the page had to name the number; bend4 has no Bool wrap over
# words at all -- is_eq answers a real Bool, and a List row on it gets
# the constructor page naming Bool itself
import Base

assert main:
  U32

def main():
  match U32.is_eq(3, 3):
    case Con{h, t}:
      h
    case Nil{}:
      0
$$ bend %
Error:
- expected : a constructor of Bool (missing, or already matched)
- observed : \{Con: (h => t => h); Nil: U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
Location: main
11 |   match U32.is_eq(3, 3):
12>|     case Con{h, t}:
13 |       h
