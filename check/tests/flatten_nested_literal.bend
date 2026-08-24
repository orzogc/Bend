# nested ctor patterns with a literal inside: the inner column splits
# under the outer one
# ported from bend3: the numeric field becomes a ctor word, literal arm
# values become ctors (bend4 has no number patterns)
type W:
  Z{}
  S{p: W}

type Token:
  Num{n: W}
  Stop{}

type Env:
  Env{t: Token, backup: Token}

type R:
  K100{}
  KP{m: W}
  KK{k: W}
  K0{}

assert main:
  forall a: Env
  R

def main(a):
  match a:
    case Env{Num{Z{}}, backup}:
      K100{}
    case Env{Num{m}, backup}:
      KP{S{m}}
    case Env{Stop{}, Num{k}}:
      KK{k}
    case Env{Stop{}, Stop{}}:
      K0{}
$$ bend % --show
main = \{Env: \{Num: \{Z: (backup => K100{}); (_11 => backup => KP{S{_11}})}; Stop: \{Num: (k => KK{k}); Stop: K0{}}}}
