# the first program a user writes on this tree: build a map, read it
# back through the copier idiom, then work strings and numbers through
# the sugars - split/join/length, infix arithmetic and compares, the
# if/elif term, ++, <> and the list literal, Nat.show and U32.show.
# one program crossing every feature the per-feature tests pin alone;
# the re-used string and word ride Cop-licensed + lets, strict
import Base

assert Char.eq:
  forall a: Char
  forall b: Char
  (Char & Char) & Bool

def Char.eq(a, b):
  ((a2, b2), c) = Char.cmp(a, b)
  ((a2, b2), Cmp.is_eq(c))

assert String.split.push:
  forall c: Char
  forall ps: List<String>
  List<String>

def String.split.push(c, ps):
  match ps:
    case Nil{}:
      Con{SCon{c, SNil{}}, Nil{}}
    case Con{h, t}:
      Con{SCon{c, h}, t}

assert String.split:
  forall s: String
  forall sep: Char
  List<String>

def String.split(s, sep):
  match s:
    case SNil{}:
      Con{SNil{}, Nil{}}
    case SCon{h, t}:
      ((h2, sep2), e) = Char.eq(h, sep)
      match e:
        case True{}:
          Con{SNil{}, String.split(t, sep2)}
        case False{}:
          String.split.push(h2, String.split(t, sep2))

assert String.join.go:
  forall xs: List<String>
  forall h: String
  forall sep: String
  String

def String.join.go(xs, h, sep):
  match xs:
    case Nil{}:
      h
    case Con{h2, t2}:
      (s1, s2) = String.copy(sep)
      String.append(h, String.append(s1, String.join.go(t2, h2, s2)))

assert String.join:
  forall xs: List<String>
  forall sep: String
  String

def String.join(xs, sep):
  match xs:
    case Nil{}:
      SNil{}
    case Con{h, t}:
      String.join.go(t, h, sep)

assert List.length:
  forall -A: Type
  forall xs: List<A>
  Nat

def List.length(A, xs):
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      1n+List.length(A, t)

assert String.length:
  forall s: String
  Nat

def String.length(s):
  match s:
    case SNil{}:
      0n
    case SCon{h, t}:
      1n+String.length(t)

assert u32cp:
  forall v: U32
  (U32 & U32)

def u32cp(v):
  ((a, e1), (b, e2)) = U32.copy(v)
  (a, b)

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

assert main.out:
  String

def main.out():
  m = Map.set(U32, Map.set(U32, Map.new(U32), "one", 1), "two", 2)
  (m2, got) = Map.get(U32, u32cp, 0, m, "two")
  parts = String.split("a,bb,ccc", ',')
  +joined = {String.join(parts, "-") : (+ String ~ Str.copy)}
  n = String.length(joined)
  +x = {123 + 877 * 2 : +U32}
  f = {if x < 2000: "lo" elif U32.is_eq(x, 2000): "eq" else: "hi" : String}
  lst = {got <> [3, 4] : List<U32>}
  ln = Nat.show(List.length(U32, lst))
  String.join([joined, Nat.show(n), U32.show(x), Nat.show(Nat.mul(7n, 6n)), f, "hel" ++ "lo", ln], " ")

assert main:
  IO(Unit)

def main():
  IO.print(main.out())
$$ bend %
a-bb-ccc 8 1877 42 lo hello 3
$$ bend % --seq
a-bb-ccc 8 1877 42 lo hello 3
exit 0
$$ bend % --par
a-bb-ccc 8 1877 42 lo hello 3
exit 0
$$ bend % --js
a-bb-ccc 8 1877 42 lo hello 3
exit 0
