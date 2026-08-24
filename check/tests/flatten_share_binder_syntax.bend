# bend3's `&x` share-binder let (`&y = v` binds y shared); bend4's core
# is affine and & prefixes only the typed fork-let, so the share-binder
# spelling pins bend4's own refusal (the array statement half lives in
# flatten_array_statement)
type Nt:
  Z{}
  S{p: Nt}

assert main:
  forall v: Nt
  Nt

def main(v):
  &y = v
  y
$$ bend % --show
Error:
- expected : ':'
- observed : '='
Location:
13 | def main(v):
14>|   &y = v
15 |   y
