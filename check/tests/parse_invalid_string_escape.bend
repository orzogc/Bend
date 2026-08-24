# error census: an unknown escape in a string literal is a located
# Syntax page.
# ported from bend3: String comes from Base (no backquote char-codes)
import Base

assert x:
  String

def x(): "a\qb"

assert main:
  U32

def main(): 0
$$ bend %
Error:
- expected : an escape (\n \t \r \0 \\ \' \")
- observed : 'b'
Location:
 8 | 
 9>| def x(): "a\qb"
10 |
