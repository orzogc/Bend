# bend3's capture attack named a local Not to launder the != desugar;
# bend4's != builds the DATATYPE Empty as an explicit node (no lexical
# lookup), so a binder named Empty cannot capture the codomain: sneaky's
# own return type already means real inequality, and the launder dies at
# its own definition, one fence earlier than the lookup spelling did
import Base

assert sneaky:
  forall -Empty: Type
  forall w: {1n == 1n : Nat} -> Empty
  {1n != 1n : Nat}

def sneaky(Empty, w):
  w

assert exploit:
  {1n != 1n : Nat}

def exploit():
  sneaky(Unit, e => Unit{})

assert main:
  U32

def main():
  0
$$ bend %
Error:
- expected : @_:{1n == 1n : Nat} -> Empty
- observed : @_:{1n == 1n : Nat} -> Empty
Context:
- Empty : Type
- w     : @_:{1n == 1n : Nat} -> Empty
Location: sneaky