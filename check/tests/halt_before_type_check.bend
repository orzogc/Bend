# audit: a nullary def applying itself errors at the def, before main is
# ever looked at -- the descent judgment lives inside infer-app, so the
# self-application is refused as non-decreasing (no column shrinks).
# ported from bend3: U32 becomes Nat; bend3 pinned its separate halt
# phase beating a later type error, bend4 pins the in-checker ordering
import Base

assert bad:
  Nat

def bad(): bad(0n)
assert main:
  Nat

def main(): 0n
$$ bend %
Error:
- expected : a decreasing self-call (some live argument must shrink)
- observed : bad(0n)
Location: bad
10 | 
11>| def bad(): bad(0n)
12 | assert main:
