# io (io_request_dead_fall): SPEC 2.4 -- no table encodes an offload
# path, and the request machinery falls DEAD in a program that never
# applies a closure dynamically: without FID_CLO_APPLY the foreign
# REQUEST segments and the FID_IO_EMIT case compile out of work_loop
# (a dead segment keeps its FID and its table rows; its label aliases
# FID_EXIT). Every bench main has this shape -- main IS one effect
# call, no IO.bind, whose m(R, k) applications keep FID_CLO_APPLY
# live -- so a bench's work_loop pays no extra dispatch case. The
# WORK_LOOP LAW makes this a speed mechanism: ANY added case costs
# ~2% SEQ on every bench, and the sequential column is exactly what
# --here cannot see. Gutting the dead-fall clause kept the whole
# suite green while every bench's work_loop gained a live
# WL_CASE(FID_IO_PRINT). The IO_EMIT half is structurally loud: its
# case sits behind #ifdef FID_CLO_APPLY in the template, so waking
# its label without the define refuses to compile.
import Base

law main:
  IO(Unit)

def main():
  IO.print("dead fall")

#|dead fall
