type Flag:
  On{}
  Off{}

type Cfg:
  Cfg{x: Flag, y: Flag, z: Flag}

assert main:
  forall a: Cfg
  Flag

def main(a):
  match a:
    case Cfg{On{},  On{},  a}:
      a
    case Cfg{On{},  Off{}, a}:
      a
    case Cfg{Off{}, a, On{}}:
      a
    case Cfg{Off{}, a, Off{}}:
      a

$$ bend % --show
main = \{Cfg: \{On: \{On: (a => a); Off: (a => a)}; Off: (_6 => \{On: _6; Off: _6})}}
