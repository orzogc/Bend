# io (io_stack_fault_trap): a machine stack fault is LOUD - the one
# numbered line, never a silent death by signal. Every host machine
# stack (the event loop's own and each pool worker's) is a guarded
# mmap: a 16KB PROT_NONE page past the window, an altstack, and the
# SIGSEGV/SIGBUS trap answering "bend: error 10" before the abort.
# NOTHING drove it: gutting both sigaction lines kept the whole
# suite green while this program died by raw SIGBUS with an EMPTY
# stderr - the exact silent-loss class the numbered-error law
# forbids. The drive is honest WORK-phase recursion: a fork opens
# the pool, GROW skips the no-fork children, and WORK drains them
# in SEQ mode, where each level of a non-tail self-call pushes a
# real frame; the descent rides a Nat depth (U32.to_nat is O(1):
# Nat is a native immediate) matched ahead of the self-call, and
# 300M levels overrun the 2GB window into the guard page in under
# a second, on whichever lane owns the deep child.
# The JS walls join the numbered-error law at io_run: a cut there
# is a nested host call, so the host stack throws RangeError long
# before the machine's depth, and io_run's catch translates it into
# the C wall's own error 10 line, thrown as the one plain string
# both printers spell verbatim - the interpreter's catch on stdout,
# io_exit's on stderr - exit 1 either way, the compiled-JS deep-cut
# limit now loud AND numbered. The device half of the law (WL_ROOM posting
# ERR_DEEP on the strided device stacks) rides on no host drive, so
# a csrc pin holds it verbatim beside the four host trap sites.
# csrc has: mprotect((char*)p + len, 16384, PROT_NONE)
# csrc has: sigaction(SIGSEGV, &sa, NULL);
# csrc has: sigaction(SIGBUS, &sa, NULL);
# csrc has: err_fail(ERR_DEEP, "memory fault (machine stack overflow?)");
# csrc has: err_post(e.mem, ERR_DEEP); \
import Base

assert deep:
  forall n: Nat
  forall +a: +U32
  forall +b: +U32
  forall +c: +U32
  forall +d: +U32
  U32

def deep(n, a, b, c, d):
  match n:
    case 0n:
      a + b + c + d
    case 1n+p:
      x = deep(p, a + 1, b + 2, c + 3, d + 4)
      x + a + b + c + d

assert run:
  forall n: U32
  U32

def run(n):
  Both{x, y} = {Both{deep(U32.to_nat(n), 0, 0, 0, 0), deep(U32.to_nat(16), 1, 1, 1, 1)} : Par<U32, U32>}
  x + y

assert main:
  IO(U32)

def main():
  do IO<U32>:
    u : Unit <- IO.print(U32.show(run(300000000)))
    return 0
$$ bend %
bend: error 10: memory fault (machine stack overflow?)
$$ bend % --seq
bend: error 10: memory fault (machine stack overflow?)
signal SIGABRT
$$ bend % --par
bend: error 10: memory fault (machine stack overflow?)
signal SIGABRT
$$ bend % --js
bend: error 10: memory fault (machine stack overflow?)
exit 1
