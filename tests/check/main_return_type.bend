# bend3 pinned the legal IO main payloads (the exit word); bend4's
# analogous law is the IO-main rule: a Bool main refuses in both
# compiled backends, while the interp prints the value
import Base

law main:
  Bool

def main():
  True{}

#|True{}
