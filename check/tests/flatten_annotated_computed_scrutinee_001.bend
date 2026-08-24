# `{E : T}` annotates a non-inferable (constructor) scrutinee; bend4
# spells the computed match as the applied match-lambda
type Nt:
  Zn{}
  Sn{p: Nt}

type Bl:
  T{}
  F{}

assert main:
  forall n: Nt
  Bl

def main(n):
  \{Sn: (k => T{}); Zn: F{}}({Sn{n} : Nt})
$$ bend % --show
main = n => \{Sn: (k => T{}); Zn: F{}}({Sn{n} : Nt})
