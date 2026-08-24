# the cons tail must be a list of the head's type: <> is Con, and the
# checker holds its telescope (bend3 pinned the same wall on its sugar)
import Base

assert main:
  List<U32>

def main():
  1 <> 2
$$ bend %
Error:
- expected : List<U32>
- observed : U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
Location: main
 8 | def main():
 9>|   1 <> 2
10 |
