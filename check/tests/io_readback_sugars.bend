# readback with the language's sugars: nat/tuple/list/string/char
# spellings and a lambda in a list, on the interpreter (quoted chars,
# an empty string as bare SNil{}, open lambdas spelled) and the JS
# backend (chars as strings, closures as <closure>); the C lane
# refuses the List (not showable) loud.
# ported from bend3: numbers become Nats for readable goldens, Nat.min
# replaces the local min, the deep-chain half lives in
# eval_deep_list_print (the interpreter's show overflows past ~100k)
import Base

assert Nat.min:
  forall a: Nat
  forall b: Nat
  Nat

def Nat.min(a, b):
  match a b:
    case 0n y:
      0n
    case 1n+ap 0n:
      0n
    case 1n+ap 1n+bp:
      1n+Nat.min(ap, bp)

assert Nat.pow2:
  forall n: Nat
  Nat

def Nat.pow2(n):
  match n:
    case 0n:
      1n
    case 1n+p:
      Nat.double(Nat.pow2(p))

assert small:
  Pair(Nat, Maybe<Nat>)

def small():
  (7n, Some{9n})

assert sugars:
  List<Pair(String, Char)>

def sugars():
  Con{("a\n", 'x'), Con{("", 'y'), Nil{}}}

assert funs:
  List<@x:Nat -> Nat>

def funs():
  Con{x => Succ{x}, Nil{}}

assert main:
  Pair(Nat, Pair(Nat, Pair(Pair(Nat, Maybe<Nat>), Pair(List<Pair(String, Char)>, List<@x:Nat -> Nat>))))

def main():
  (Nat.pow2(12n), Nat.min(4n, 3n), small(), sugars(), funs())
$$ bend %
Tuple{4096n, Tuple{3n, Tuple{Tuple{7n, Some{9n}}, Tuple{Con{Tuple{"a\n", 'x'}, Con{Tuple{SNil{}, 'y'}, Nil{}}}, Con{x => 1n+x, Nil{}}}}}}
$$ bend % --seq
Error: tocl: main must answer IO<T>: the event loop runs IO mains only (report this case)
exit 1
$$ bend % --js
Error: tojs: main must answer IO<T>: the event loop runs IO mains only
exit 1
