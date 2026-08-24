#[halts]
# closure ladder, complete: IH plus the shift lemma close the arm
# ported from bend3: the ~ comp param becomes a live +closure under
# #[halts]; the theorem is stated flipped (bend4's rewrite folds right
# into left, so the eliminated call sits on the RIGHT)
type MN:
  Z{}
  S{p: MN}

assert each:
  forall +n: MN
  forall +g: MN -> MN
  forall x: MN
  MN

def each(n, g, x):
  match n:
    case Z{}:
      g(x)
    case S{p}:
      each(p, g, g(x))

assert plus1:
  forall n: MN
  forall x: MN
  MN

def plus1(n, x):
  match n:
    case Z{}:
      S{x}
    case S{p}:
      S{plus1(p, x)}

assert pshift:
  forall p: MN
  forall x: MN
  {S{plus1(p, x)} == plus1(p, S{x}) : MN}

def pshift(p, x):
  match p:
    case Z{}:
      {==}
    case S{q}:
      %pshift(q, x) : {S{S{plus1(q, x)}} == S{_} : MN}
      {==}

assert spec_thm:
  forall +n: MN
  forall +x: MN
  {plus1(n, x) == each(n, y => S{y}, x) : MN}

def spec_thm(n, x):
  match n:
    case Z{}:
      {==}
    case S{p}:
      %spec_thm(p, S{x}) : {S{plus1(p, x)} == _ : MN}
      %pshift(p, x) : {S{plus1(p, x)} == _ : MN}
      {==}

assert main:
  @n: MN -> @x: MN -> {plus1(n, x) == each(n, y => S{y}, x) : MN}

def main():
  n => x => spec_thm(n, x)

$$ bend %
n => x => spec_thm(n, x)
