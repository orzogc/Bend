# bend3's Bag multiset module is absent from bend4's base: the head
# call is an undefined name
import Base

assert main:
  U32

def main():
  Bag.total(Bag.add(1, Bag.new()))
$$ bend %
Error:
- expected : a defined name
- observed : Bag.total
Location: main
 8 | def main():
 9>|   Bag.total(Bag.add(1, Bag.new()))
10 |
