# list literals and <> are ungated core grammar desugaring to Con/Nil:
# without Base those constructor names are simply unbound -- bend4's
# gating story (bend3 gated the parse on `import List`)
type Nx:
  Zx{}

assert main:
  Nx

def main():
  h = [Zx{}]
  Zx{}
$$ bend %
Error:
- expected : a declared constructor
- observed : Con{Zx{}, Nil{}}
Location: main
10 | def main():
11>|   h = [Zx{}]
12 |   Zx{}
