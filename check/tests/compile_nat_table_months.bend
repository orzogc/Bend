# nat_table coverage, GOAL 1.4: a closed Nat match of three-plus
# constant word arms is the general embedded-data idiom (a month
# table), not a raytrace privilege -- it must compile to one deduped
# CONSTV table with a clamped TAB_AT lookup whose last entry is the
# Succ default. year() walks the table with a dynamic index, so the
# inliner cannot constant-fold the match away.
# csrc has: CONSTV u64 TAB_0[] = { 31ull, 28ull, 31ull, 30ull,
# csrc has: = TAB_AT(TAB_0,
import Base

assert days:
  forall m: Nat
  U32

def days(m):
  match m:
    case 0n: 31
    case 1n: 28
    case 2n: 31
    case 3n: 30
    case 4n: 31
    case 5n: 30
    case 6n: 31
    case 7n: 31
    case 8n: 30
    case 9n: 31
    case 10n: 30
    case 11n+k: 31

assert year:
  forall +m: +Nat
  U32

def year(m):
  match m:
    case 0n:
      0
    case 1n+p:
      U32.add(days(p), year(p))

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(year(12n)))
$$ bend %
365
$$ bend % --seq
365
exit 0
$$ bend % --par
365
exit 0
$$ bend % --js
365
exit 0
