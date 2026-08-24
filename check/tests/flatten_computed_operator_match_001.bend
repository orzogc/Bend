# computed scrutinee, comparison expression, as bend4 spells it: the
# applied match-lambda over the call
# ported from bend3: == is no operator in bend4 (U32.is_eq), literals
# become params (a U32 literal shows as its Word chain)
import Base

assert main:
  forall n: U32
  forall m: U32
  forall p: U32
  forall q: U32
  U32

def main(n, m, p, q):
  \{True: p; False: q}(U32.is_eq(n, m))
$$ bend % --show
main = n => m => p => q => \{True: p; False: q}(U32.is_eq(n, m))
