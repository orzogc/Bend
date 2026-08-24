# the != sugar is ungated core grammar desugaring to the Empty datatype
# node: without Base the datatype is simply undeclared -- bend4's whole
# gating story (bend3 gated the parse on `import Empty`)
type Nx:
  Zx{}

assert T0:
  Type

def T0():
  {Zx{} != Zx{} : Nx}

assert main:
  Nx

def main():
  Zx{}
$$ bend %
Error:
- message  : a declared datatype (unknown: Empty)
Context:
- _ : {Zx{} == Zx{} : Nx}
Location: T0