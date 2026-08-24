# refusal pin: bend3 checked a Data-bound instantiation against the
# sort table at the CALL SITE (dup(Box) rejected because Box holds a
# closure). bend4 has no Data class at all -- the kind is not a name,
# and sharing is the + binder quantity under #[halts] -- so the
# faithful translation dies on the Data spelling itself.
# ported from bend3: ctor names bare and unique, Pair -> Pr2/MkPr2
import Base

type Bx2:
  MkBx2{f: U32 -> U32}
type Pr2<Elem: Type>:
  MkPr2{x: Elem, y: Elem}

assert mk2:
  Unit -> Bx2

def mk2(): u => MkBx2{x => x}

assert dup2:
  @-a: Data -> @x: a -> Pr2<a>

def dup2(): a => x => MkPr2{x, x}

assert main:
  Pr2<Bx2>

def main(): dup2(Bx2)(mk2(Unit{}))
$$ bend %
Error:
- expected : a defined name
- observed : Data
Location:
19 | assert dup2:
20>|   @-a: Data -> @x: a -> Pr2<a>
21 |
