# bend3's JSON number formatting (JSON.show of as_u/as_f reads) is
# absent from bend4 by ruling: the head call is an undefined name
import Base

assert main:
  String

def main():
  JSON.show(JSON.read("12.50"))
$$ bend %
Error:
- expected : a defined name
- observed : JSON.show
Location: main
 8 | def main():
 9>|   JSON.show(JSON.read("12.50"))
10 |
