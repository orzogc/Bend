# The Bend Guide

Bend has Python's syntax, Haskell's semantics, Lean-style proofs without
tactics, and parallelism from one line: `a b = f(x) g(y)`. Programs are pure,
strict and total; values are immutable and used once by default. One source
runs as multithreaded C, as a Metal or CUDA kernel, and as JavaScript.

## Get started

Bend runs under [Bun](https://bun.com):

```bash
git clone https://github.com/HigherOrderCO/bend4
ln -s "$PWD/bend4/bend2/main.ts" ~/.bun/bin/bend
```

```python
import Base

def main() -> IO(Unit):
  IO.print("Hello, world!")
```

`bend hello.bend` checks the file and runs `main` on an in-memory JS backend. A
non-`IO` `main` prints as a value; a file without `main` just checks. `bend
hello.bend -o hello` writes `hello.c` and builds it with `clang`, with the GPU
when Metal or CUDA links. Keep the `.c` beside the binary: it compiles the GPU
kernels from it at launch. `Base` is the prelude: `bend base` prints it, `bend
base --types` its types, `bend base Nat` one name and what is under it. `bend
guide` prints this file, `bend --help` the rest.

## Parallelism

2^20 as a 20-level tree with a 1 at every leaf. `Nat` is unary (`0n`; `1n+p` is
the successor of `p`); `match` opens a value by its constructors:

```python
def pow2(+d: Nat) -> U32:
  match d:
    case 0n:
      1
    case 1n+p:
      a b = pow2(p) pow2(p)
      (a + b : U32)

def main() -> IO(Unit):
  IO.print(U32.show(pow2(20n)))
```

`bend pow2.bend -o pow2 && ./pow2` prints 1048576 on every core; `--parallel
off` uses one thread. `a b = pow2(p) pow2(p)` is the **parallel let**, the only
parallelism primitive: n names, n calls, one line. The checker sees n lets in
the outer scope, none seeing another. The compiler sees a fork: one task per
call, the rest of the body running when all are done. A recursive fork is a
tree of tasks, which is how one line fills thousands of cores. No locks: values
are **affine**, so siblings share nothing (`+d` allows reuse; see
[Quantities](#quantities)), and a pure fork has no order to keep. Tasks are
dealt once and never stolen, so keep siblings balanced; an unbalanced fork is
correct, only slower.

**How it compiles.** `-o` emits one C file: program, runtime, scheduler.
Compiled code is a flat machine with no C stack: a def is a segment, a call a
jump. A fork is a *join* task (the code after it) plus one child per call, each
filling a slot of the join. Tasks spread over the *cube*, a 128 x 128 grid of
lanes: a growth phase runs forking tasks until every lane has work, then each
lane drains its share alone, the fork running as stack frames on one thread.
The heap is one flat span shared by every thread and the GPU. A binary exits 0
or with its `IO.die` code, and takes:

- `--threads N`: default the CPU count, at most 128.
- `--parallel on|off`: off is one thread and no GPU.
- `--gpu on|off`: default on when a device is found.
- `--gpu-memory 4GB`: the device span, 2GB on Metal, the whole card on CUDA.

`-o pow2.c` emits the C alone (`clang -std=c11 -O3 pow2.c -lpthread -lm -o
pow2` builds it CPU-only); `-o pow2.js` emits sequential JavaScript on the host
GC, which is what `bend pow2.bend` runs in memory; `-o` repeats. `--checkup` on
a file of imports reports each module alone, as `bend module.bend` would; the
binary runs one as `./main module`, and a module the combined book refuses (a
name its file binds and Base's sugar also names) is reported as `Left out of
the binary:`.

**GPU.** `pow2!(20n)` runs the task tree under the call on the GPU. The checker
ignores `!`; without a device the call runs on the CPU. The device compiles
only what a `!` reaches (plus every closure), so the shader stays small. Host
and device share one address space, nothing is copied, and they never compute
at once. Balanced trees of uniform scalar leaves win there (mandelbrot, nbody);
divergent or skewed work (n-queens, symbolic regression) stays faster on the
CPU. `bench/runtime/` has sixteen programs; `paper/BendRT.pdf` the design and
numbers.

## Claims and proofs

A type is written inline (`def f(x: U32) -> U32:`) or as a `law` (the claim)
that a `def` (the body) fills; the checker sees no difference, but when the
type is a theorem a human reads the law and nobody reads the proof. A law with
no def is an open claim: a type may mention it, live code may not call it, the
report counts it as a TODO. Another file fills it through an import alias
(`import ./claims.bend as C`, then `def C.name(..):`); that is how a
[ProofMarket](https://proofmarket.com) bounty is claimed.

A claim is `for` lines, `exs` lines, then the result, a body like a def's (lets
may lead to the final type). `for -x: T` is erased, `for +x: T` reusable; `for
x: T where P(x)` packs a hypothesis with `x` into a pair; `exs y: T` asks the
body to *produce* a `y`. A proposition is a type: `Unit` is true (one value),
`Empty` false (none), `{a == b : T}` equality, proved by `{==}` when both sides
compute to the same term. Anything richer is a def that returns a `Type`:

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

law half_ok:
  for x: Nat
  for e: IsEven(x)
  {Nat.double(half(x)) == x : Nat}

def half_ok(x, e):
  match x:
    case 0n:
      {==}
    case 1n+0n:
      match e:
    case 2n+p:
      %half_ok(p, e) : {2n+Nat.double(half(p)) == 2n+_ : Nat}
      {==}
```

Matching `x` refines the goal per arm: at `0n` it computes to `{0n == 0n :
Nat}`; at `1n+0n` the evidence `e` computes to `Empty`, and the empty match (no
cases) closes the arm; at `2n+p` the recursive call is the induction
hypothesis. The rewrite `%e : P` takes `e : {a == b : T}` and folds `b` back
into `a` where the motive `P` marks `_`: the goal must be `P` with `b` at the
marks, and the rest of the body proves `P` with `a` there. Without it the
checker shows where the sides part:

```
Error:
- expected : 2n+Nat.double(half(p))
- observed : 2n+p
Context:
- p : Nat
- e : IsEven(p)
Location: half_ok
32 |     case 2n+p:
33>|       {==}
34 | 
```

An `exs` is a pair of witness and proof (`+x`, since both calls consume it); a
constructor clash dies by a discriminating motive:

```python
law half_exists:
  for +x: Nat
  for e: IsEven(x)
  exs y: Nat
  {Nat.double(y) == x : Nat}

def half_exists(x, e):
  (half(x), half_ok(x, e))

def disc(n: Nat) -> Type:
  match n:
    case 0n:
      Unit
    case 1n+p:
      Empty

law one_ne_zero:
  {1n != 0n : Nat}

def one_ne_zero(e):
  %Equal.sym(Nat, 1n, 0n, e) : disc(_)
  Unit{}
```

`{a != b : T}` is `{a == b : T} -> Empty`; `Equal.sym`, `Equal.trans` and
`Equal.cong` are in `Base`.

**The checker** is one bidirectional pass: inference for variables and
applications, checking for the rest, conversion (both sides computed, compared
up to eta) where they meet. No unification, metavariables, implicit arguments,
tactics or type classes: every type argument is written (`id(U32, 42)`), every
`do` bind annotated, every literal in a `let` typed (`x = {10 : U32}`).
Checking is linear in the code size and every error is local: expected,
observed, context, line. `?TODO` leaves a goal open (the file checks, marked
incomplete); `?name` reports the goal at that spot as an error.

**Termination.** Every def terminates. A live recursive call must shrink a
parameter structurally: some argument is a pattern variable bound under a
constructor of that parameter (columns compare left to right, erased ones
skipped). `n - 1` and `n > 0` prove nothing, only the pattern does, so loops
count on `Nat`. A def may call itself and what is above it, never below; mutual
recursion folds into one def with a phase argument. A loop bounded by the world
(a server) carries a `Nat` fuel it drops per step, seeded through `U32.to_nat`,
or wears `@unsafe`, which skips its descent check and makes the report say so
(`1 term annotated as unsafe. The code is well-typed, but may contain logical
paradoxes.`):

```python
@unsafe
def forever(n: Nat) -> Nat:
  forever(n)
```

`demos/nat_proofs/main.bend` is a full commutative-semiring development;
`paper/BendTT.pdf` is the theory.

## The language

**Datatypes.** `type` declares constructors and a kind: `Data` may be reused,
`Type` may not. Fields are reached by pattern matching only, which moves them
out and frees the node. There is no `if`: a `Bool` is matched like any value. A
match opens a *parameter* or a *field* (in the order bound), never a computed
value: the caller computes, a helper decides. One match takes several
scrutinees (`match a, b:` with `case True{}, False{}:`), patterns nest, and `_`
catches the rest:

```python
type Shape is Data:
  Circle{+r: U32}
  Rect{w: U32, h: U32}

def area(s: Shape) -> U32:
  match s:
    case Circle{r}:
      (3 * r * r : U32)
    case Rect{w, h}:
      (w * h : U32)
```

**Values.** `42` is a `U32`, the 32-bit word; `1.5` an `F32` (`F32.sqrt` to
`F32.atan2`); `3n` a `Nat`; `'A'` a `Char`; `"abc"` a `String` (a chain of
`Char`; `++` appends); `[1, 2, 3]` a `List` (`h <> t` is cons); `(a, b)` a pair
of type `A & B`, longer tuples nesting right. Operators name the methods of the
type after `:` in the parens around them, `(a + b * c : U32)`, else `Nat`;
comparisons answer `Bool`; equality is a call (`U32.is_eq`; the `==` token is
the equality type). Each number type has `.show`, `.read` (to a `Maybe`) and
conversions like `U32.to_nat` and `F32.to_u32`. Division by zero answers `0`
for `/` and `a` for `%`. There is no match on a word: count on `Nat`, compute
on `U32`. The [appendix](#appendix-operators) lists every operator. `Base`'s
list kit is `List.map`: write the recursion you need.

**Functions.** `x => body` is a lambda, `A -> B` its type (`@x: A -> B` when
`B` depends on `x`). A closure captures its scope and is used once: function
types are `Type`, so no `+` binds one; top-level defs are called freely. A type
parameter is an erased argument, `-A: Type`, passed at every call: `id(U32,
42)`. A body is statements, then one expression, one per line: `x = v` binds
the inferred value (a literal needs `{v : T}`); `+x = v` binds a reusable value
(its type must be `Data`); `K{a, b} = p` and `(a, b) = p` open a parameter or
field; `a b = f(x) g(y)` forks; `m2 = m[i] <- v` writes an array.

**Arrays.** `Array<T>` is a perfect binary tree of `2^d` slots, stored flat by
the C backend: `a[i]` reads and `a[i] <- v` writes in place, O(1), pure because
an array has one owner (`Array<T>` is `Type`). Indices wrap at the length.
`Array.new(T, d, v)` builds one; a read answers the pair `Array<U32> & U32`,
opened in a helper by `(m, x) = r`. `Array.get` and `Array.new` take any `Data`
element (`a[i]` is the `U32` case), `Array.set` and `Array.swap` any element;
`Array.swap` and `Array.size` answer the array with the old element or the
length. `Base` also has `Map<a, V>`, an immutable string-keyed tree, and
`Set()` over it.

**IO.** `main` answers `IO(A)`; `do` chains actions. A line binds (`x : T <-
act`), discards (`T <- act`), lets (`x : T = v`) or returns (`return v`); the
last line is the block's value:

```python
def main() -> IO(Unit):
  do IO<Unit>:
    Unit <- IO.write("Hello, ")
    name : String <- IO.try(String, IO.get_env("USER"))
    Unit <- IO.print(name)
    IO.die(Unit, 2, "bye")
```

`IO.die` prints to stderr and exits with its code. `do` desugars to `M.bind`
and `M.pure`, so `Maybe` and `Result` take it too (`do Maybe<&2, U32>:`). `IO`
is defined in `Base`, a continuation over `IO.OP`; only the event loop that
runs each emitted effect is built in. The kit: stdout, stderr, environment,
files, TCP, UDP (`IO.print`, `File.open`, `TCP.listen`, `UDP.bind` and kin). A
fallible effect answers `Result<&1, &1, U32 & String, A>`, `Done` or
`Fail{(errno, message)}`; `IO.try(A, act)` unwraps one or dies, `IO.pass(A, r)`
lifts a `Result` in hand. Handles (`File`, `Socket`, `Listener`) are affine and
come back *outside* the `Result`, `H & Result<..>`, even on failure. Bytes ride
`String`s, one byte per `Char`. `demos/http_server` is a complete server.

**Concurrency.** A program is a set of computations run by one event loop, as
Node runs callbacks: each is sequential Bend code stepping to its next effect,
and an effect that must wait (a socket with no data, a sleep, a file read on a
helper thread) parks only its own computation while the loop runs another. A
computation yields only when it parks or ends; a print, `IO.now` or `IO.spawn`
does not. Pure code inside a step still runs on every core: parallelism comes
from the pool and the GPU, concurrency from the loop. The loop polls sockets
and timers when nothing can step. The process ends when every computation has
answered (main's return alone ends nothing), with `IO.die`'s code from any
computation, or with 1 and a deadlock message when computations remain and
nothing is pending.

- `IO.spawn(A, act)`: starts `act` as its own computation; answers at once.
- `Chan.new(A, room)`: a `Chan<A>`, a Data handle any computation may copy,
  holding up to `room` values (0: each value goes straight from sender to
  receiver).
- `Chan.send(A, c, v)`: `True`, or `False` on a closed channel.
- `Chan.recv(A, c)`: `Some{v}`, parking until one arrives, or `None` once the
  channel is closed and drained.
- `Chan.close(A, c)`: a parked sender answers `False`, what is queued still
  drains, and the channel's row goes once empty.
- `IO.fork(A, act)`: spawns `act` and answers the channel its value arrives on;
  `IO.join(A, c)` takes it and closes the channel.
- `IO.sleep(ms)` parks for a span; `IO.now()` reads a monotonic clock in ms.

Handles share one table of 4096 rows; `Chan.new` past it fail-stops.

**Foreign fills.** An effect is a def whose body is import lines naming a `.c`
and a `.js` file. You can add your own:

```python
def Text.rev(text: String) -> IO(String):
  import "./effs/text_rev.js"
```

```js
// effs/text_rev.js
function text_rev(text) {
  return Array.from(text).reverse().join("");
}
```

The host function is the def's name lowercased, dots to underscores, over the
backend's own values. The `.js` serves `bend file.bend` and `-o .js`; a native
build needs the `.c` twin. A fill must answer `IO`, and only the event loop
runs it: there is no other FFI, so proofs, totality and the GPU never see host
code. One file holds one effect and its helpers; the IO API is comp.ts's, so a
def and its two files delete clean.

- C: `io_eff(FID, CID, run, need)` registers `Term run(Env e, Term* f, IoWork*
  w)`, which runs on the loop thread: `need` 0 at once, `IO_READ` once the
  socket in field 0 is readable, `IO_TIME` after field 0 milliseconds.
- Blocking work must leave the loop: `run` decodes its arguments into `w`
  (plain C) and answers `io_work(w, call, pack)`; `call(w)` runs on a helper
  thread touching only `w` and the handle table; `pack(e, w)` builds the answer
  back on the loop.
- JS: a `<name>_need` function answering `{read: kind}` or `{time: true}` tells
  the lane what to `poll` for.

**Graphics.** A frame is an `Image`, a quadtree: `Pix{color}` (0x00RRGGBB)
fills its quadrant, `Qua{tl, tr, bl, br}` splits one. A w x h window shows the
smallest 2^k square covering it, top-left, clipped. An `Event` is `Key{code,
down}`, `Mouse{x, y, button, down}`, `Move{x, y}` or `Close{}` (the close
button; the window stays until closed).

- `Window.open(title, w, h)`: a `Window` in a `Result`, in device pixels;
  `Fail` without a display.
- `Window.frame(window, image)`: shows it at the display's rate; answers the
  handle, the same image and the events since the last frame, oldest first.
- `Window.close`: closes.
- `App<S>` is `App{view, tick}`: `view` answers the state beside its `Image`
  (a linear state threads through; a Data state answers `(s, image)`); `tick`
  folds a frame's events into the next state in IO, `None` to quit.
- `App.run(~S, ~app, title, w, h, state)`: a tick per frame in a window;
  `App.play(~S, ~app, frames, state)`: the same over scripted frames, unseen.

The smallest app:

```python
type Dot is Data:
  Dot{x: U32, y: U32}

def Dot.view(d: Dot) -> Dot & Image:
  Dot{x, y} = d
  +a = x
  +b = y
  (Dot{a, b}, Pix{(a << 16n .|. b : U32)})

def Dot.tick(events: List<Event>, d: Dot) -> IO(Maybe<Dot>):
  match events:
    case Nil{}:
      IO.pure(Maybe<Dot>, Some{d})
    case Con{Close{}, rest}:
      IO.pure(Maybe<Dot>, None{})
    case Con{Move{x, y}, rest}:
      Dot.tick(rest, Dot{x, y})
    case Con{e, rest}:
      Dot.tick(rest, d)

def main() -> IO(Unit):
  App.run(~Dot, ~App{Dot.view, Dot.tick}, "Dot", 256, 256, Dot{0, 0})
```

Key codes are AppKit's: the first UTF-16 unit of the key's character,
lowercased (space 32, enter 13, tab 9, escape 27, backspace 127); function keys
as they are (up 63232, down 63233, left 63234, right 63235); a key with no
character (a modifier) 65536 plus its hardware code. Mouse positions are device
pixels from the top-left; buttons are 0 left, 1 right, 2 middle. A hidden or
minimized window paces at one frame per second. Build with `-o`: without a
display (the JS backend, a CPU-only binary, no session) `Window.open` answers
`Fail(ENOTSUP, "Window.open: no display")`. `demos/pong_game` draws a few
hundred nodes per frame; `demos/ray_tracer` ray-marches every pixel on the GPU
with one `!`.

**Imports** come first in a file:

```python
import Base
import ./lib/util.bend as Util
```

A file's namespace is its path without `.bend`. `as Util` is an alias for this
file only: `Util.inc` names `lib/util.inc`, and `def Util.inc_one(x):` here
fills a law `util.bend` left open. Names are dotted and dots are just
characters: `U32.show` needs no module. `import 0x<hash>/path.bend as P` is a
content-addressed package, read from `$BEND_STORE` (default `~/.bend/store`)
and fetched from `$BEND_HUB` (default hub.bend-lang.org) on a miss, each file
checked against the package's manifest and the manifest against the hash.
Cycles are rejected.

**Publishing.** `bend file.bend --publish` checks the file and uploads what the
loader read (every imported `.bend`, `.c` and `.js` at its path from the file's
directory; base and other packages left out) as one package, then prints its
hash and the import line others use:

```
0x3f1c9e2a7b4d5e6f8a9b0c1d2e3f4a5b
import 0x3f1c9e2a7b4d5e6f8a9b0c1d2e3f4a5b/main.bend as Main
```

The hash names the bytes, so a change is a new package. A `?TODO` does not
publish; an open `law` does, so a claim can precede its proof. There are no
accounts: a publish carries a proof of work of about two seconds of a laptop's
cores per 256 KiB (every core mines), and a package is 16 MiB at most. The hub
checks nothing else; importers check every package with their own checker.
`bend-lang.org/hub/0x<hash>` shows a package with each name linked to its
definition; `hub.bend-lang.org/0x<hash>/manifest` lists its files.

**Templates.** A `def` whose first parameter has `~` is a template: its text
parses once, and each call with a distinct tuple of `~` arguments compiles to
its own copy, `T~n`, with the arguments substituted as syntax. Base's
`List.map` is one, called as `List.map(~Nat, ~Nat, ~(x => Nat.add(x, 1n)),
xs)`:

```python
def List.map(~A: Type, ~B: Type, ~f: A -> B, xs: List<A>) -> List<B>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{f(h), List.map(~A, ~B, ~f, t)}
```

The call compiles to the loop you would write by hand, with no closure at run
time: inside the template `f(h)` is the argument applied, so a `~` lambda there
is a macro. Every type parameter a `~` parameter's type mentions is `~` too. A
`~` argument must be closed (no local of the caller) and under 2048 characters;
otherwise the call stays a plain call of the template's name, which the checker
refuses as a defined name: pass the local at run time. A template may only call
templates declared above it. A `~` on a runtime position joins the key: write
`~` only at compile-time positions. A `~` lambda headed by a `let`, and a
curried macro whose body is a constructor, do not inline: the checker cannot
infer them inside the instance.

## Quantities

A binder has one of three quantities: `x` (used once), `-x` (erased: types,
proofs, generics; gone at run time), `+x` (used many times). Values move: into
calls, into constructors, into the match that opens them; dropping is free.
Dead positions (types, erased arguments, equation endpoints, motives) count
nothing.

`+` forms only at kind `Data`. Every type has a kind `Kind(q)`: `Data` is
`Kind(&2)`, `Type` is `Kind(&1)`, and a `Data` constructor holds only `Data`
fields. `U32`, `F32`, `Nat`, `Bool`, `Char`, `String`, `Set()` and every
equation are `Data`; function types, `Array<T>`, `IO(A)` and the handles are
`Type`. A `+` scrutinee hands out `+` fields, and a field declared `+` is
reusable even in an affine holder. There is no copy function: a `Type` value is
reused by hand or not at all.

A datatype takes one quantity per parameter (a bare name in its header), and
`Kind(a)` is the kind of the types of that quantity, so a container is as
reusable as its element: `List<&2, U32>` may be reused, `List<&1, U32>` (also
spelled `List<U32>`) may not, and the two are different types; `+List<U32>`
spells the first. Generic code takes the quantity as an erased parameter:

```python
type Box<a, -A: Kind(a)> is Kind(a):
  Box{x: A}

def length(a, -A: Kind(a), xs: List<a, A>) -> U32:
  match xs:
    case Nil{}:
      0
    case Con{h, t}:
      (1 + length(a, A, t) : U32)
```

`length(&2, U32, [1, 2, 3])` and `length(&1, U32 -> U32, [y => y])` both check.
`A & B` is `Sigma<&1, &1, A, _ => B>`, the affine pair; the `&2` one may sit
under `+`. Every refusal is one of two errors: `expected : Data, observed :
Type`, or `x (consumed more than once)`.

## The theory and the runtime

Terms check in two modes: live (runs) and dead (only checks). A dead term may
diverge and may inhabit `Empty`; nothing promotes dead to live. That wall, with
the usage cap, lets Bend keep `Type : Type`, impredicativity and negative
datatypes (`type Trm is Type: Lam{f: Trm -> Trm}` is accepted) with no universe
levels and no positivity check: every classical paradox contracts a
function-typed binding, and no function type is `Data`. Equality is
intensional, elimination is J (`%`), conversion is up to eta, and there is no
funext. The core is mechanized in Lean (`bend2/bend.lean`), rules as the
checker runs them: confluent, sound along live steps, normalizing, consistent.

A term is one 64-bit word; words, floats, small `Nat`s and nullary constructors
are unboxed. There is no garbage collector: a match frees its node on the spot,
often reusing it for the arm's own constructor, and `+` values carry a count
and are never cloned. Compiled code is one flat worklist machine, so recursion
depth is bounded by memory, not the C stack. The same C source is the host
program and the Metal or CUDA kernel.

## Bend as a JS library

Imported instead of run, `bend2/main.ts` is a loader that makes a `.bend` file
a module: under node, `node --import ./bend2/main.ts app.mjs`; under Bun,
`preload = ["./bend2/main.ts"]` in `bunfig.toml`.

```python
type Move is Data:
  Up{}
  Down{}

def step(m: Move, pos: U32) -> U32:
  match m:
    case Up{}:
      (pos + 1 : U32)
    case Down{}:
      (pos - 1 : U32)
```

```js
import Game from "./game.bend";

console.log(Game.step({ $: "Up" }, 1));   // 2
```

Every filled non-IO def is exported and takes only its live arguments, in one
call or curried (`Game.step({ $: "Up" })(1)`). A constructor is `{$: "Name",
field: value, ...}`, a closure a function, `Nat` a `BigInt`; `Bool`, `U32` and
`String` are native. `bend page.html -o dist` bundles a page for the browser
with the loader on.

## Appendix: operators

Higher binds tighter; every operator is a named def in `Base`.

| level | operators             | meaning                                          |
|-------|-----------------------|--------------------------------------------------|
| 1     | `A & B`, `A \| B`     | pair type, `Either` type (right-assoc)           |
| 2     | `\|\|`                | `Bool.or`                                        |
| 3     | `&&`                  | `Bool.and`                                       |
| 4     | `< <= > >=`           | `T.is_lt`, `T.is_le`, `T.is_gt`, `T.is_ge`       |
| 5     | `h <> t`, `a ++ b`    | cons, `String.append` (right-assoc)              |
| 6-8   | `.\|. .^. .&.`        | `T.or`, `T.xor`, `T.and`                         |
| 9     | `x << n`, `x >> n`    | `T.shln`, `T.shrn`: shifts by a `Nat`            |
| 10    | `+ -`                 | `T.add`, `T.sub`                                 |
| 11    | `* / %`               | `T.mul`, `T.div`, `T.mod` (`%` needs spaces)     |

`T` is the type after `:` in the parens around the operators, `(a + b * c :
U32)`, else `Nat` (which has `Nat.divmod`, no `div` or `mod`); inner parens
inherit it, a call argument is `f((a + b : U32), c)`, and an index `a[i + 1]`
is `U32`. An operator headed by `>` needs a space before it. `f!(x)` marks a
call for the GPU; `a[i]` and `a[i] <- v` are the array sugars. `@x: A -> B` and
`&x: A -> B` are the dependent function and pair types; `&1` and `&2` are
quantities, `a <&> b` their meet, `Kind(q)` a kind.
