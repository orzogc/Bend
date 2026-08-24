# bend3's width-8 Word module and its on-import lemmas; bend4's base
# Word is width-generic, so the same kit instantiates at 8n directly:
# add computes (5 + 3 reads back 8n through Word.to_nat) and the
# add_comm/add_zero lemmas check at the fixed width
import Base

assert Word.add_zero:
  forall n: Nat
  forall w: Word(n)
  {Word.add(n, w, Word.zero(n)) == w : Word(n)}

def Word.add_zero(n, w):
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{False{}, t}:
          Equal.cong(Word(p), Word(1n+p), y => WCon{False{}, y}, Word.add(p, t, Word.zero(p)), t, Word.add_zero(p, t))
        case WCon{True{}, t}:
          Equal.cong(Word(p), Word(1n+p), y => WCon{True{}, y}, Word.add(p, t, Word.zero(p)), t, Word.add_zero(p, t))

assert w5:
  Word(8n)

def w5():
  WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}

assert w3:
  Word(8n)

def w3():
  WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}

assert comm_at_8:
  forall a: Word(8n)
  forall b: Word(8n)
  {Word.add(8n, a, b) == Word.add(8n, b, a) : Word(8n)}

def comm_at_8(a, b):
  Word.add_comm(8n, a, b)

assert zero_at_8:
  forall w: Word(8n)
  {Word.add(8n, w, Word.zero(8n)) == w : Word(8n)}

def zero_at_8(w):
  Word.add_zero(8n, w)

assert main.out:
  Nat

def main.out():
  Word.to_nat(8n, Word.add(8n, w5(), w3()))

assert main:
  IO(Unit)

def main():
  IO.print(String.append(Nat.show(main.out()), "n"))
$$ bend %
8n
$$ bend % --seq
8n
exit 0
$$ bend % --par
8n
exit 0
$$ bend % --js
8n
exit 0
