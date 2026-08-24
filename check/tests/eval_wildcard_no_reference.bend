# _ is never referenceable: a wildcard binder does not capture it, so
# a body naming _ is unbound and refused at check.
# ported from bend3: unchanged shape; the golden is bend4's refusal
import Base

assert main:
  @x:U32 -> U32

def main():
  _ => _
$$ bend %
Error:
- expected : a defined name
- observed : _^
Context:
- _ : U32
Location: main
 9 | def main():
10>|   _ => _
11 |
