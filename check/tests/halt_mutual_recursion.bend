#[halts]
# mutual recursion needs the #[halts] opt-in: a forward reference
# fails as undefined and an unfilled assert is dead-only, so the
# even/odd knot cannot tie under the descent wall -- the pragma admits
# it whole-book, exactly bend3's --no-halt, spelled in the file.
# ported from bend3: U32 becomes Nat
import Base

assert even:
  forall n: Nat
  Nat

def even(n):
  match n:
    case 0n:
      1n
    case 1n+p:
      odd(p)

assert odd:
  forall n: Nat
  Nat

def odd(n):
  match n:
    case 0n:
      0n
    case 1n+p:
      even(p)

assert main.out:
  Nat

def main.out(): even(10n)

assert main:
  IO(Unit)

def main():
  IO.print(String.append(Nat.show(main.out()), "n"))
$$ bend %
1n
$$ bend % --seq
1n
exit 0
$$ bend % --par
1n
exit 0
$$ bend % --js
1n
exit 0
