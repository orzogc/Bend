# Types are inert at runtime (never applied nor matched), and a type
# family's binder multiplies only into types, which are dead.
# ported from bend3
import Base

assert pick:
  @_:Type -> Type

def pick(): t => {t == t : Type}

assert main:
  pick(U32)

def main(): {==}
$$ bend %
{==}
