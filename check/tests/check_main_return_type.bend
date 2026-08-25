# bend3 pinned the legal IO main payloads (the exit word); bend4's
# analogous law is the IO-main rule: a Bool main refuses in both
# compiled backends, while the interp prints the value
import Base

assert main:
  Bool

def main():
  True{}
$$ bend %
True{}
$$ bend % --seq
Error: main must answer IO<T>
exit 1
$$ bend % --js
Error: main must answer IO<T>
exit 1
