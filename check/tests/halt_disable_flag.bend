#[halts]
# bend3's consistency trade was the --no-halt CLI flag; bend4's is the
# in-file #[halts] pragma -- under it boom : Empty = boom() checks
# (whole-book scope, no descent), the same unlock at the same price,
# spelled where the book can see it
import Base

assert boom:
  Empty

def boom():
  boom()

assert main.out:
  U32

def main.out():
  0

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
0
$$ bend % --seq
0
exit 0
$$ bend % --par
0
exit 0
$$ bend % --js
0
exit 0
