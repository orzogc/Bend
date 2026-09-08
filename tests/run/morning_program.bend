# the first program a user writes on this tree: build a map, read it
# back through Map.get's default, then work strings and numbers through
# the sugars - split/join/length, infix arithmetic and compares, the
# if/elif term, ++, <> and the list literal, Nat.show and U32.show.
# one program crossing every feature the per-feature tests pin alone;
# the re-used string and word ride + lets (both Data), strict
import Base

law Char.eq:
  for a: Char
  for b: Char
  (Char & Char) & Bool

law Char.eq.fin:
  for w: (Char & Char) & Cmp
  (Char & Char) & Bool

def Char.eq.fin(w):
  ((a2, b2), c) = w
  ((a2, b2), Cmp.is_eq(c))

def Char.eq(a, b):
  Char.eq.fin(Char.cmp(a, b))

law String.split.push:
  for c  : Char
  for ps : List<&2, String>
  List<&2, String>

def String.split.push(c, ps):
  match ps:
    case Nil{}:
      Con{SCon{c, SNil{}}, Nil{}}
    case Con{h, t}:
      Con{SCon{c, h}, t}

law String.split.fin:
  for rec : (Char -> List<&2, String>)
  for w   : (Char & Char) & Bool
  List<&2, String>

def String.split.fin(rec, w):
  ((h2, sep2), e) = w
  match e:
    case True{}:
      Con{SNil{}, rec(sep2)}
    case False{}:
      String.split.push(h2, rec(sep2))

law String.split:
  for s: String
  Char -> List<&2, String>

def String.split(s):
  match s:
    case SNil{}:
      sep => Con{SNil{}, Nil{}}
    case SCon{h, t}:
      sep => String.split.fin(String.split(t), Char.eq(h, sep))

law String.join.fin:
  for h    : String
  for rec  : (String -> String)
  for +sep : String
  String

def String.join.fin(h, rec, sep):
  String.append(h, String.append(sep, rec(sep)))

law String.join.go:
  for xs : List<&2, String>
  for h  : String
  String -> String

def String.join.go(xs, h):
  match xs:
    case Nil{}:
      sep => h
    case Con{h2, t2}:
      sep => String.join.fin(h, String.join.go(t2, h2), sep)

law String.join:
  for xs  : List<&2, String>
  for sep : String
  String

def String.join(xs, sep):
  match xs:
    case Nil{}:
      SNil{}
    case Con{h, t}:
      String.join.go(t, h, sep)

law List.length:
  for -A : Data
  for xs : List<&2, A>
  Nat

def List.length(A, xs):
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      1n+List.length(A, t)

law String.length:
  for s: String
  Nat

def String.length(s):
  match s:
    case SNil{}:
      0n
    case SCon{h, t}:
      1n+String.length(t)

law main.out:
  String

law pickf.eq:
  for z2: Bool
  String

def pickf.eq(z2):
  match z2:
    case True{}:
      "eq"
    case False{}:
      "hi"

law pickf:
  for z1: Bool
  for z2: Bool
  String

def pickf(z1, z2):
  match z1:
    case True{}:
      "lo"
    case False{}:
      pickf.eq(z2)

law main.go:
  for w: Map<&2, U32> & U32
  String

def main.go(w):
  (m2, got) = w
  parts = String.split("a,bb,ccc", ',')
  +joined = {String.join(parts, "-") : String}
  n = String.length(joined)
  +x = (123 + 877 * 2 : U32)
  f = pickf(U32.is_lt(x, 2000), U32.is_eq(x, 2000))
  lst = {got <> [3, 4] : List<&2, U32>}
  ln = Nat.show(List.length(U32, lst))
  String.join([joined, Nat.show(n), U32.show(x), Nat.show(Nat.mul(7n, 6n)), f, "hel" ++ "lo", ln], " ")

def main.out():
  main.go(Map.get(U32, 0,
    Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "one", 1), "two", 2), "two"))

law main:
  IO(Unit)

def main():
  IO.print(main.out())

#|a-bb-ccc 8 1877 42 lo hello 3
