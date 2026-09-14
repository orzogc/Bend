# readback with the language's sugars: nat/tuple/list/string/char
# spellings and a lambda in a list (quoted chars, an empty string as
# "", open lambdas spelled). A pure main's value is its normal form,
# taken at compile time, so the C and JS lanes print the same text.
# ported from bend3: numbers become Nats for readable goldens, Nat.min
# replaces the local min, the deep-chain half lives in
# eval_deep_list_print (the interpreter's show overflows past ~100k)
import Base

law Nat.min:
  for a: Nat
  for b: Nat
  Nat

def Nat.min(a, b):
  match a b:
    case 0n y:
      0n
    case 1n+ap 0n:
      0n
    case 1n+ap 1n+bp:
      1n+Nat.min(ap, bp)

law Nat.pow2:
  for n: Nat
  Nat

def Nat.pow2(n):
  match n:
    case 0n:
      1n
    case 1n+p:
      Nat.double(Nat.pow2(p))

law small:
  Pair(Nat, Maybe<&2, Nat>)

def small():
  (7n, Some{9n})

law sugars:
  List<&1, Pair(String, Char)>

def sugars():
  [("a\n", 'x'), ("", 'y')]

law funs:
  List<&1, @x:Nat -> Nat>

def funs():
  [x => Succ{x}]

law main:
  Pair(Nat, Pair(Nat, Pair(Pair(Nat, Maybe<&2, Nat>), Pair(List<&1, Pair(String, Char)>, List<&1, @x:Nat -> Nat>))))

def main():
  (Nat.pow2(12n), Nat.min(4n, 3n), small(), sugars(), funs())

#|(4096n, 3n, (7n, Some{9n}), [("a\n", 'x'), ("", 'y')], [x => 1n+x])
