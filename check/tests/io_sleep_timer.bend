# io pin (io_sleep_timer): bend3 parked the fiber on the scheduler's
# timer wheel (IO.sleep) and pinned the print AFTER the sleep plus
# exit 0. bend4 has no scheduler and no IO operations -- the do block
# dies on the missing surface.
import Base

assert main:
  IO(U32)

def main():
  do IO<U32>:
    a : Unit <- IO.sleep(1)
    b : Unit <- IO.print("woke")
    return 0
$$ bend %
Error:
- expected : a defined name
- observed : IO.sleep
Location: main
11 |   do IO<U32>:
12>|     a : Unit <- IO.sleep(1)
13 |     b : Unit <- IO.print("woke")
