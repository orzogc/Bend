# Hurkens' paradox (powerful universe): proves Empty via contraction on
# forall-typed values, smuggled through box-wrapped applications. The
# paradox spells as bare over-use and dies at the first reused binder
# (f : pow2(x) -> x): in core v1 no live binding contracts at all.
# Type:Type consistency rests on exactly this rejection.
# ported from bend3: --> becomes the erased all, Data-gate wording
# becomes the affine wall
type Unt:
  Uu{}

assert box:
  @-a: Type -> @_:a -> @-w:Unt -> a

def box(): a => v => w => v

assert pow:
  @_:Type -> Type

def pow(): s => (s -> Type)

assert pow2:
  @_:Type -> Type

def pow2(): s => (pow(s) -> Type)

assert u:
  Type

def u(): @x: Type -> @_:(pow2(x) -> x) -> pow2(x)

assert bot:
  Type

def bot(): @p: Type -> p

assert neg:
  @_:Type -> Type

def neg(): a => (a -> bot)

assert tauinner:
  @x: Type -> @_:(pow2(x) -> x) -> @_:pow(x) -> @-w:Unt -> pow(u)

def tauinner(): x => f => p => w => y => p(f(y(x)(f)))

assert tau:
  @_:pow2(u) -> u

def tau(): t => x => f => p => t(tauinner(x)(f)(p)(Uu{}))

assert wtau:
  @-w:Unt -> @_:pow2(u) -> u

def wtau(): w => tau

assert sig:
  @_:u -> pow2(u)

def sig(): s => s(u)(wtau(Uu{}))

assert domd:
  @_:u -> Type

def domd(): z => @q: pow(u) -> @_:sig(z)(q) -> q(tau(sig(z)))

assert delta:
  pow(u)

def delta(): y => neg(domd(y))

assert wom:
  @-w:Unt -> pow2(u)

def wom(): w => p => @x: u -> @_:sig(x)(p) -> p(x)

assert omega:
  u

def omega(): tau(wom(Uu{}))

assert rty:
  Type

def rty(): @p: pow(u) -> @_:(@x: u -> @_:sig(x)(p) -> p(x)) -> p(omega)

assert r:
  rty

def r(): p => h => h(box(u)(omega)(Uu{}))(box(sig(omega)(p))(x => h(tau(sig(x))))(Uu{}))

assert mty:
  Type

def mty(): @x: u -> @_:sig(x)(delta) -> delta(x)

assert m:
  mty

def m(): x => h2 => h3 =>
      h3(box(pow(u))(delta)(Uu{}))(h2)(box(domd(tau(sig(x))))(p => h3(tauinner(u)(wtau(Uu{}))(p)(Uu{})))(Uu{}))

assert false:
  bot

def false(): r(delta)(m)(box(rty)(r)(Uu{}))

assert main:
  Unt

def main(): Uu{}
$$ bend %
Error:
- expected : f
- observed : f (consumed more than once)
Context:
- x : Type
Location: tauinner
43 | 
44>| def tauinner(): x => f => p => w => y => p(f(y(x)(f)))
45 |
