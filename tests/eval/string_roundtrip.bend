# Base String: split/join round-trips through a separator, and
# concat/length count code points. Pure.
# ported from bend3: String.split takes (s, +sep: Char), String.join.go
# takes (xs, h, +sep: String) -- both separators wear + (Char and
# String are Data);
# lengths are Nats read back through U32.from_nat; concat is
# String.append
import Base

law beq:
  for a: Char
  for b: Char
  Bool

def beq(a, b):
  String.eq(SCon{a, SNil{}}, SCon{b, SNil{}})

law String.split.push:
  for c  : Char
  for ps : List<&2, String>
  List<&2, String>

def String.split.push(c, ps):
  match ps:
    case Nil{}:
      [SCon{c, SNil{}}]
    case h <> t:
      SCon{c, h} <> t

law String.split.at:
  for h: Char
  for r: List<&2, String>
  for e: Bool
  List<&2, String>

def String.split.at(h, r, e):
  match e:
    case True{}:
      SNil{} <> r
    case False{}:
      String.split.push(h, r)

law String.split:
  for s    : String
  for +sep : Char
  List<&2, String>

def String.split(s, sep):
  match s:
    case SNil{}:
      [SNil{}]
    case SCon{h, t}:
      +hh = {h : Char}
      String.split.at(hh, String.split(t, sep), beq(hh, sep))

law String.join.go:
  for xs   : List<&2, String>
  for h    : String
  for +sep : String
  String

def String.join.go(xs, h, sep):
  match xs:
    case Nil{}:
      h
    case h2 <> t2:
      String.append(h, String.append(sep, String.join.go(t2, h2, sep)))

law String.join:
  for xs  : List<&2, String>
  for sep : String
  String

def String.join(xs, sep):
  match xs:
    case Nil{}:
      SNil{}
    case h <> t:
      String.join.go(t, h, sep)

law List.length:
  for -a : Quant
  for -A : Kind(a)
  for xs : List<a, A>
  Nat

def List.length(a, A, xs):
  match xs:
    case Nil{}:
      0n
    case h <> t:
      1n+List.length(a, A, t)

law String.length:
  for s: String
  Nat

def String.length(s):
  match s:
    case SNil{}:
      0n
    case SCon{h, t}:
      1n+String.length(t)

law bu:
  for b: Bool
  U32

def bu(b):
  match b:
    case False{}:
      0
    case True{}:
      1

law main.out:
  U32

def main.out():
  b = bu(String.eq(String.join(String.split("a,b,c", ','), ","), "a,b,c"))
  l = U32.from_nat(List.length(&2, String, String.split("a,b,c", ',')))
  n = U32.from_nat(String.length(String.append("ab", "cd")))
  U32.add(U32.add(b, U32.mul(l, 100)), U32.mul(n, 10))

law main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))

#|341
