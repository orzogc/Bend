# #841's exploit: a ( .. : T) around a template call once renamed the
# operators inside its ~ argument after the instance was keyed; the
# annotation now names only its own operator expression, and one that
# reaches no operator is refused with the repair
type Empty is Data:

type Unit is Data:
  Unit{}

def Nat.add(a: Type, b: Type) -> Type:
  Unit

def Bar.add(a: Type, b: Type) -> Type:
  Empty

def Pick(~x: Type) -> Type:
  x

def contradiction() -> (Pick(~Unit + Unit) : Bar):
  Unit{}

#|Error:
#|- message  : an operator with its type (( .. : T) around the expression gives it, as in (a + b : Nat))
#|  Sorry: this is a small break after the launch. Versions 2.0.0 to 2.0.16
#|  read an operator with no type as Nat, against the language's own rule.
#|  If this compiled before, put the type on the expression: a + b
#|  becomes (a + b : Nat).
#|Location:
#|18 | 
#|19>| def contradiction() -> (Pick(~Unit + Unit) : Bar):
#|20 |   Unit{}
#|exit 1
