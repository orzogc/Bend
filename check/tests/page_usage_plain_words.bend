#[halts]
# usage errors speak human: binder names print bare and the quantity
# prints as words (consumed more than once), never an internal key --
# church-two needs f twice, but a lambda binder is affine
import Base
type MNat:
  MZ{}
  MS{pred: MNat}

type Term:
  TLam{bod: Term -> Term}
  TApp{fun: Term, arg: Term}
  TVar{idx: MNat}

assert c2:
  Term

def c2():
  TLam{f => TLam{x => TApp{f, TApp{f, x}}}}

$$ bend %
Error:
- expected : f
- observed : f (consumed more than once)
Location: c2
18 | def c2():
19>|   TLam{f => TLam{x => TApp{f, TApp{f, x}}}}
20 |
