# a bounded loop whose fuel is a literal is a loop, not 40 copies of its
# body: the fold's fuel is the size of what an unfold adds, so a wide body
# stops it at once, while a small one still folds (#886)
import Base

def step(+a: U32, +b: U32, +c: U32, +d: U32, +e: U32, +f: U32) -> U32:
  ((((((a + b : U32) + c : U32) + d : U32) + e : U32) + f : U32) * 3 : U32)

def spin(n: Nat, +a: U32, +b: U32, +c: U32, +d: U32, +e: U32, +f: U32) -> U32:
  match n:
    case 0n:
      step(a, b, c, d, e, f)
    case 1n+p:
      spin(p, (a + 1 : U32), (b + a : U32), (c + b : U32), (d + c : U32),
        (e + d : U32), (f + e : U32))

def main() -> U32:
  spin(40n, 1, 2, 3, 4, 5, 6)

#|16795071
