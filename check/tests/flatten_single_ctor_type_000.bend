import Base

type T:
  K{a: U32, b: U32, c: U32}

type R:
  A{a: U32, b: U32, c: U32}
  B{y: T}

assert main:
  forall a: T
  R

def main(a):
  match a:
    case K{a,b,c}:
      A{a,b,c}
    case a:
      B{a}

$$ bend % --show
main = \{K: (a => b => c => A{a, b, c}); (a => B{a})}
