# Parallel sum: the smallest fork/join program. sum(d, i) adds the 2^d
# numbers i .. i + 2^d - 1 as a balanced tree: a leaf (d = 0) is its
# number; a node forks two halves with the parallel let `a b = f g`,
# waits for both and adds them. main calls sum!(16n, 0): the `!` sends
# the call to the GPU when the machine has one, else to every CPU core;
# interpreted, the same tree runs sequentially.
#
# Run:
#   bend demos/pure_par_sum/main.bend                    (interprets)
#   bend demos/pure_par_sum/main.bend -o sum && ./sum    (the GPU, or every core)
#   ./sum --gpu off                                      (every core)
#   ./sum --gpu off --threads 1                          (one core)
#
# main sums 0 .. 65535, which is 65535 * 65536 / 2 = 2147450880.
import Base

# sum
# ---
# the leaves i .. i + 2^d - 1 as a balanced fork/join tree: the left
# half starts at i, the right half 2^p numbers later
def sum(+d: Nat, +i: U32) -> U32:
  match d:
    case 0n:
      i
    case 1n+p:
      a b = sum(p, i) sum(p, (i + U32.shln(1, p) : U32))
      (a + b : U32)

def main() -> U32:
  sum!(16n, 0)
