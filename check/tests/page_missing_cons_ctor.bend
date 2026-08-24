# a list literal is Con/Nil whatever the goal: at a foreign type the
# checker refuses the constructor against the goal type (bend3's page
# hinted the missing List.Cons under sugar gating)
import Base

type Fx:
  Mk{}

assert main:
  Fx

def main():
  [1]
$$ bend %
Error:
- expected : Fx
- observed : Con{U32{WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, Nil{}}
Location: main
12 | def main():
13>|   [1]
14 |
