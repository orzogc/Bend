# bend3's Cat read ++ at inferring positions over any List; bend4's ++
# reads String.append (the wider List reading stays pending the
# author), so the string halves carry at plain lets (re-used strings
# ride + String ~ Str.copy binders, strict) and the lengths answer on
# every lane
import Base

assert Chr.copy:
  forall c: Char
  Copy(Char, c) & Copy(Char, c)

def Chr.copy(c):
  match c:
    case Chr{n}:
      ((nx, ne), (ny, nf)) = U32.copy(n)
      e1 = Equal.cong(U32, Char, z => Chr{z}, n, nx, ne)
      e2 = Equal.cong(U32, Char, z => Chr{z}, n, ny, nf)
      ((Chr{nx}, e1), (Chr{ny}, e2))

assert Str.copy:
  forall s: String
  Copy(String, s) & Copy(String, s)

def Str.copy(s):
  match s:
    case SNil{}:
      ((SNil{}, {==}), (SNil{}, {==}))
    case SCon{h, t}:
      ((hx, he), (hy, hf)) = Chr.copy(h)
      ((tx, te), (ty, tf)) = Str.copy(t)
      s10 = Equal.cong(Char, String, z => SCon{z, t}, h, hx, he)
      s11 = Equal.cong(String, String, z => SCon{hx, z}, t, tx, te)
      t11 = Equal.trans(String, SCon{h, t}, SCon{hx, t}, SCon{hx, tx}, s10, s11)
      s20 = Equal.cong(Char, String, z => SCon{z, t}, h, hy, hf)
      s21 = Equal.cong(String, String, z => SCon{hy, z}, t, ty, tf)
      t21 = Equal.trans(String, SCon{h, t}, SCon{hy, t}, SCon{hy, ty}, s20, s21)
      ((SCon{hx, tx}, t11), (SCon{hy, ty}, t21))

assert String.length:
  forall s: String
  Nat

def String.length(s):
  match s:
    case SNil{}:
      0n
    case SCon{h, t}:
      1n+String.length(t)

assert go:
  forall +s: (+ String ~ Str.copy)
  forall +sh: (+ String ~ Str.copy)
  U32

def go(s, sh):
  a = s ++ "!"
  b = "> " ++ s
  d = "a" ++ ("b" ++ s)
  e = sh ++ sh
  U32.from_nat(Nat.add(Nat.add(String.length(a), String.length(b)), Nat.add(String.length(d), String.length(e))))

assert main.out:
  Nat

def main.out():
  U32.to_nat(go("hey", "!!"))

assert main:
  IO(Unit)

def main():
  IO.print(String.append(Nat.show(main.out()), "n"))
$$ bend %
18n
$$ bend % --seq
18n
exit 0
$$ bend % --par
18n
exit 0
$$ bend % --js
18n
exit 0
