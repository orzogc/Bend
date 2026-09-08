# rewrite with a non-equation premise is refused (a rewrite's evidence
# must be an equation).
# ported from bend3: bend4's rewrite takes a mandatory motive, and the
# refusal fires at the evidence
import Base

law main:
  U32

def main(): %5 : U32; 1

#|Error:
#|- expected : an annotated term (cannot infer)
#|- observed : U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
#|Location: main
#| 9 | 
#|10>| def main(): %5 : U32; 1
#|11 |
#|exit 1
