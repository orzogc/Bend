# no U32 truthiness: an if condition is Bool -- a literal word cannot
# even sit there (the applied match's scrutinee must infer, and a ctor
# does not; bend3's one-way U32-Bool bridge has no counterpart at all)
import Base

assert main:
  U32

def main():
  if 1: 2 else: 3
$$ bend %
Error:
- expected : an annotated term (cannot infer)
- observed : U32{WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
Location: main
 9 | def main():
10>|   if 1: 2 else: 3
11 |
