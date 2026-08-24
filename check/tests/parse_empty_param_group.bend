# a datatype may spell an EMPTY angle group: `type K<>:` parses the same
# as `type K:`.
# ported from bend3: bend3 rejected the empty group; bend4 pins the
# opposite (the group is optional and may be empty)
type Nn4<>:
  Zz4{}

assert main:
  Nn4

def main(): Zz4{}
$$ bend %
Zz4{}
