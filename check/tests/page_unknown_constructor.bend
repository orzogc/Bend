# error census: an arm tag NO datatype declares, matched over U32 --
# the page asks for a constructor of the scrutinee's type
import Base
assert main:
  U32 -> U32

def main(): \{Qux: 3}

$$ bend %
Error:
- expected : a constructor of U32 (missing, or already matched)
- observed : \{Qux: U32{WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
Location: main
6 | 
7>| def main(): \{Qux: 3}
8 |
