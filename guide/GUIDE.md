# The Bend Guide

Bend is Python's syntax, Haskell's semantics, Lean-style proofs without
tactics, and parallelism from one line. Programs are pure, strict and total;
values are immutable and used once by default. One source runs as
multithreaded C, as a Metal or CUDA kernel, and as JavaScript.

## Hello

Bend runs under [Bun](https://bun.com): clone `HigherOrderCO/bend4` and
symlink `bend2/main.ts` as `bend`.

```python
import Base

def main() -> IO(Unit):
  IO.print("Hello, world!")
```

`bend hello.bend` checks the file and runs `main` on an in-memory JS backend.
`bend hello.bend -o hello` builds a native binary (a program with a `!`
builds its GPU program too: keep `hello.gpu` beside the binary).
`-o hello.c` or `-o hello.js` emits the source instead. A `main` that is not
`IO` prints as a value; a file with no `main` just checks. `bend --help` has
the rest of the CLI; `bend base` prints the prelude, `bend base --types` its
types, `bend base Nat` one name and everything under it: the reference is the
source.

## A program

```python
type Shape is Data:            # Data: values may be reused; Type: used once
  Circle{+r: U32}              # a +field may be reused wherever it lands
  Rect{w: U32, h: U32}

def area(s: Shape) -> U32:
  match s:                     # opens s: fields move out, the node is freed
    case Circle{r}:
      (3 * r * r : U32)        # operators name methods of the type after ":"
    case Rect{w, h}:
      (w * h : U32)

def len(-A: Type, xs: List<A>) -> U32:   # -A: erased type parameter
  match xs:
    case Nil{}:
      0
    case Con{h, t}:
      (1 + len(A, t) : U32)    # every argument is written: len(U32, xs)

def main() -> U32:
  a = area(Rect{2, 3})         # a let infers its type from a call
  b = len(U32, [1, 2, 3])      # a bare literal would need {v : T}
  (a + b : U32)
```

`42` is a `U32`, `1.5` an `F32`, `3n` a `Nat` (unary: `0n`, and `1n+p` matches
the successor of `p`), `'A'` a `Char`, `"abc"` a `String`, `[1, 2]` a `List`,
`(a, b)` a pair of type `A & B`. Comparisons answer `Bool`; `U32.is_eq` is
equality (`==` is the equality *type*). There is no `if`: a `Bool` is matched
like any value, and a match opens a parameter or a field, never a computed
value, so the caller computes and a helper decides. `match a, b:` takes several
scrutinees; patterns nest; `_` catches the rest. There is no match on a word:
count on `Nat`, compute on `U32`. `x => body` is a lambda, `A -> B` its type;
a closure is used once, a top-level def as often as you like. Operators are
`Base` defs (`+` is `T.add`); the untyped default is `Nat`; `h <> t` conses,
`++` appends strings, `a[i]` reads an `Array<T>` (a flat, one-owner tree of
`2^d` slots; `m2 = m[i] <- v` writes in place, O(1)). `Base`'s list kit is
`List.map`: write the recursion you need.

## Parallelism

```python
def pow2(+d: Nat) -> U32:      # +d: used twice below, so d is marked reusable
  match d:
    case 0n:
      1
    case 1n+p:
      a b = pow2(p) pow2(p)    # the parallel let: two names, two calls
      (a + b : U32)
```

`a b = f(x) g(y)` is Bend's only parallelism primitive. To the checker it is
two ordinary lets; to the compiler a fork: each call becomes a task, the rest
of the body runs when all are done, and a recursive fork is a tree of tasks
that fills every core (`./pow2 --parallel off` uses one thread). No locks are
needed: values are affine, so siblings share nothing, and a pure fork has no
order to keep. Tasks are dealt once and never stolen, so keep siblings
balanced; an unbalanced fork is correct, only slower. Mark a call with `!`,
`pow2!(20n)`, and the task tree under it runs on the GPU, nothing copied (host
and device share one address space); the checker ignores the mark and a binary
with no device runs it on the CPU. Balanced trees of uniform scalar work win on
the GPU (mandelbrot, nbody); divergent work (n-queens) stays faster on the CPU.
A binary takes `--threads N`, `--parallel on|off`, `--gpu on|off`,
`--gpu-memory 4GB`.

## Proofs

A type can be written apart from its body, as a `law` (the claim) that a `def`
(the proof) fills. The checker sees no difference; a human reads the law and
skips the proof. A law with no def is an open claim: types may mention it, live
code may not call it, and the report counts a TODO. Another file fills it
through an import alias (`import ./claims.bend as C`, then `def C.name(..):`),
which is how a [ProofMarket](https://proofmarket.com) bounty is claimed.

A proposition is a type: `Unit` is true, `Empty` false, `{a == b : T}` is
equality and `{==}` proves it when both sides compute to the same term.
Anything richer is a def that returns a `Type`:

```python
def IsEven(n: Nat) -> Type:
  match n:
    case 0n:
      Unit
    case 1n+0n:
      Empty
    case 2n+p:
      IsEven(p)

def half(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+0n:
      0n
    case 2n+p:
      1n+half(p)

law half_ok:                   # for lines, then the result
  for x: Nat
  for e: IsEven(x)
  {Nat.double(half(x)) == x : Nat}

def half_ok(x, e):
  match x:
    case 0n:
      {==}                     # the goal computed to {0n == 0n : Nat}
    case 1n+0n:
      match e:                 # e : Empty, so no cases: the arm is closed
    case 2n+p:
      %half_ok(p, e) : {2n+Nat.double(half(p)) == 2n+_ : Nat}
      {==}
```

Matching refines the goal in each arm, and the recursive call is the induction
hypothesis. The rewrite `%e : P` takes `e : {a == b : T}` and folds `b` back
into `a` wherever the motive `P` marks `_`; the goal must be `P` with `b` at
the marks, and the rest of the body proves `P` with `a` there. Drop it and the
checker answers with the spot where the two sides part: expected
`2n+Nat.double(half(p))`, observed `2n+p`, the context, the line. `for -x:
T` binds an erased hypothesis, `for +x: T` a reusable one, `for x: T where
P(x)` pairs `x` with evidence, and `exs y: T` asks the proof to produce a `y`:
`half_exists(x, e)` answers `(half(x), half_ok(x, e))`. A constructor clash
is refuted by a discriminating motive: rewrite `e : {1n == 0n : Nat}` through
`disc(_)`, where `disc` sends `0n` to `Unit` and `1n+p` to `Empty`, and answer
`Unit{}` (`{a != b : T}` is `{a == b : T} -> Empty`; `Equal.sym`, `Equal.trans`
and `Equal.cong` are in `Base`).

The checker is one bidirectional pass with no unification, implicit arguments,
tactics or type classes: every type argument is written, every `do` bind is
annotated, and in exchange checking is linear in the code and every error is
local. `?TODO` leaves a goal open (the file checks, marked incomplete); `?name`
reports the goal at that spot. Every def terminates: a recursive call must pass
a pattern variable bound under a constructor of the matching parameter (`n -
1` proves nothing, so loops count on `Nat`), and a def calls only itself and
what is above it, so mutual recursion folds into one def with a phase
argument. A loop bounded by the world carries a `Nat` fuel, or wears
`@unsafe`, which skips its descent check and makes the report say so.
`demos/nat_proofs` is a commutative semiring; `paper/BendTT.pdf` is the theory.

## Quantities

A binder is used once (`x`), erased (`-x`: types, proofs, generics, gone at run
time) or reused (`+x`). Values move: into calls, into constructors, into the
match that opens them; dropping is free; dead positions (types, erased
arguments, equation endpoints, motives) count nothing. `+` needs kind `Data`:
`U32`, `Nat`, `Bool`, `String` and every equation are `Data`; functions,
arrays, `IO(A)` and handles are `Type`, reused by hand or not at all. A `+`
scrutinee hands out `+` fields. A datatype takes one quantity per parameter (a
bare name in its header), so a container is as reusable as its element:
`List<&2, U32>` (also `+List<U32>`) may be reused, `List<&1, U32>` (also
`List<U32>`) may not, and generic code takes the quantity as an erased
argument, `def length(a, -A: Kind(a), xs: List<a, A>)`, called `length(&2, U32,
[1])` or `length(&1, U32 -> U32, [y => y])`. Every refusal is one of two
errors: `expected : Data, observed : Type`, or `x (consumed more than once)`.

## IO

```python
def main() -> IO(Unit):
  do IO<Unit>:                                        # sugar over bind, pure
    Unit <- IO.write("Hello, ")                       # discard
    name : String <- IO.try(String, IO.get_env("USER"))   # bind
    k : U32 = 2                                       # let
    IO.die(Unit, k, name)                             # the value; or return v
```

`IO` is defined in `Base`; only the event loop that runs each effect is built
in. The kit covers stdout, stderr, the environment, files, TCP and UDP
(`bend base IO`, `File`, `TCP`, `UDP`). A fallible effect answers `Result<&1,
&1, U32 & String, A>`: `IO.try` unwraps it or dies, `IO.pass` lifts one.
Handles are affine and come back beside the `Result`, so even a failure hands
them back. `do` works for `Maybe` and `Result` too. `demos/http_server` is a
complete server.

**Concurrency.** One event loop runs many computations, as Node runs
callbacks: each is sequential Bend code stepping to its next effect, and one
that must wait (a socket, a sleep, a file read) parks alone. `IO.spawn(A, act)`
starts one; `Chan.new(A, room)` opens a channel (`Chan.send`, `Chan.recv` parks
until a value arrives, `Chan.close`); `IO.fork(A, act)` spawns and answers the
channel its value arrives on, `IO.join(A, c)` takes it. `IO.sleep(ms)` parks,
`IO.now()` is a clock. Pure code inside a step still runs on every core:
parallelism is the pool and the GPU, concurrency the loop. The process ends
when every computation has answered, with `IO.die`'s code, or with a deadlock
message when computations remain and nothing is pending.

**Foreign fills.** An effect is a def whose body is `import "./effs/x.js"`
(plus a `.c` twin for native builds); the host function is the def's name
lowercased, dots to underscores, over the backend's own values. A fill must
answer `IO`, and only the event loop runs it: there is no other FFI, so proofs,
totality and the GPU never see host code. `bend2/effs/` has one file per
effect, and the C side (`io_eff`, `io_work` for calls that block) reads off any
of them.

**Graphics.** A frame is an `Image` quadtree (`Pix{color}` fills a quadrant,
`Qua{tl, tr, bl, br}` splits it) and an `App<S>` is `App{view, tick}`: `view`
answers the state beside its image, `tick` folds a frame's events (`Key`,
`Mouse`, `Move`, `Close`) into the next state in IO, `None` to quit.
`App.run(~S, ~app, title, w, h, state)` ticks once per frame in a window;
without a display `Window.open` fails. `demos/pong_game` is the smallest real
one; `demos/ray_tracer` marches every pixel on the GPU with one `!`.

## Modules

`import ./lib/util.bend as Util` names the file's defs `Util.x`; the alias is
for this file only, and dots are just characters (`U32.show` needs no module).
`import 0x<hash>/main.bend as P` is a content-addressed package, fetched from
the hub on a miss and checked against its hash. `bend file.bend --publish`
uploads the file and everything it imports as one package (no `?TODO`; an
open law is fine, so a claim can precede its proof), mines a few seconds of
proof of work in place of an account, and prints the import line.
`bend-lang.org/hub/0x<hash>` shows any package, each name linked.

**Templates.** A `def` whose leading parameters have `~` parses once and
compiles to its own copy per distinct tuple of `~` arguments, substituted as
syntax, so `List.map(~Nat, ~Nat, ~(x => Nat.add(x, 1n)), xs)` is the loop you
would write by hand, with no closure at run time:

```python
def List.map(~A: Type, ~B: Type, ~f: A -> B, xs: List<A>) -> List<B>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{f(h), List.map(~A, ~B, ~f, t)}
```

A `~` argument must be closed (no local of the caller: pass it at run time),
and a template calls only templates declared above it.

**From JavaScript.** Imported instead of run, `bend2/main.ts` makes a `.bend`
file a module (`node --import ./bend2/main.ts app.mjs`, or `preload` it in
`bunfig.toml`): `import Game from "./game.bend"` exports every non-IO def over
its live arguments, `Game.step({ $: "Up" }, 1)`; constructors are `{$: "Name",
field: value}`, `Nat` a `BigInt`, `Bool`, `U32` and `String` native. `bend
page.html -o dist` bundles a page with the loader on.

## Under the hood

Compiled code is a flat worklist machine with no C stack: a def is a segment, a
call a jump, a fork a join task plus one child per call, dealt over a 128 x 128
grid of lanes that grow until full and then drain alone. A term is one 64-bit
word; there is no garbage collector: a match frees its node on the spot and `+`
values carry a count. The same C source is the host program and the GPU
kernel; `paper/BendRT.pdf` has the design and the numbers. In the theory, terms
check live (they run) or dead (they only check); a dead term may inhabit
`Empty`, nothing promotes dead to live, and that wall, with the usage cap, is
why `Type : Type` and negative datatypes are consistent without universe levels
or a positivity check. `bend2/bend.lean` mechanizes the core as the checker
runs it.
