# The Bend Guide

Bend is a programming language with Python's syntax, Haskell's semantics, a
proof system in the style of Lean (without tactics), and parallelism from
one line: `a b = f(x) g(y)`. Programs are pure, strict and total; values are
immutable and, by default, used once. One source runs as multithreaded C,
as a Metal or CUDA kernel, and as JavaScript.

## Get started

Bend runs under [Bun](https://bun.com):

```bash
git clone https://github.com/HigherOrderCO/bend4
cd bend4
ln -s "$PWD/bend2/main.ts" ~/.bun/bin/bend   # links ~/.bun/bin/bend
```

```python
import Base

def main() -> IO(Unit):
  IO.print("Hello, world!")
```

```bash
bend hello.bend             # checks, then runs main: Hello, world!
bend hello.bend -o hello    # builds the native binary
./hello                     # Hello, world!
```

`Base` is the prelude. `bend file.bend` runs `main` on an in-memory JS
backend; a `main` that is not `IO` is printed as a value instead, and a file
with no `main` just checks. `-o` writes `hello.c` beside the binary and
builds it with `clang`, GPU-enabled when Metal (macOS) or CUDA links, CPU-only
otherwise. Leave the `.c` where it is: the binary reads it at launch to
compile its GPU kernels.

## Parallelism

This sums the numbers from 0 to 2^24 - 1 by splitting the range in half,
24 times. `Nat` is the unary natural (`0n`; `1n+p` is the successor of `p`)
and `match` opens a value by its constructors:

```python
import Base

def sum(+d: Nat, +i: U32) -> U32:
  match d:
    case 0n:
      i
    case 1n+p:
      a b = sum(p, (i * 2 : U32)) sum(p, (i * 2 + 1 : U32))
      (a + b : U32)

def main() -> IO(Unit):
  IO.print(U32.show(sum(24n, 0)))
```

```bash
bend sum.bend -o sum
./sum                  # 4286578688, on every core
./sum --parallel off   # 4286578688, on one thread
```

`a b = sum(p, i * 2) sum(p, i * 2 + 1)` is the **parallel let**: n names,
n calls, one per name, on one line. It is Bend's only parallelism
primitive. To the checker it is n ordinary lets, each checked in the outer
scope, so no sibling sees another. To the compiler it is a fork: each call
becomes a task, and the rest of the body runs when all of them are done. A
recursive def that forks builds a tree of tasks, which is how one line fans
out to thousands of cores.

Two rules make this safe with no locks. Values are **affine**: a variable is
consumed once, so siblings own their arguments and share nothing (`+d` and
`+i` license reuse, and only because `Nat` and `U32` are `Data`; see
[Quantities](#quantities)). And Bend is pure, so a fork has no order to
keep. What the runtime asks of you is balance: siblings should carry about
equal work, because tasks are dealt out once and never stolen. An
unbalanced fork is still correct, only slower.

### How it compiles

`-o` builds one C file: your program, the runtime and the scheduler.
Compiled code is a flat machine with no C call stack: each def is a
segment and calls are jumps. The fork above becomes a *join* task (the
code after the fork) waiting for two results, and two child tasks, each
delivering into one slot of the join. Tasks are dealt across the *cube*, a
128 x 128 grid of lanes: a growth phase runs forking tasks until every lane has
work, then each lane drains its share to the end, alone, where the same
fork runs as a chain of stack frames on one thread. The heap is one flat
span shared by every thread and the GPU.

A binary takes `--threads N` (default: the CPU count, at most 128),
`--parallel on|off` (off: one thread, no GPU), `--gpu on|off` (default: on
if a device is found), `--gpu-memory 4GB` (the device span: 2GB on Metal,
the whole card on CUDA). It exits 0, or with its `IO.die` code.

To hold the source yourself, `bend sum.bend -o sum.c` emits the C file
(`clang -std=c11 -O3 sum.c -lpthread -lm -o sum` builds it CPU-only), and
`-o sum.js` emits plain JavaScript: the same program, sequential, host
GC. `bend sum.bend` runs that JS in memory, so it is also the interpreter.
`-o` repeats: `bend sum.bend -o sum -o sum.js` builds both. A `main` that
is not `IO` prints its value on every backend; a file of imports checked
with `--checkup` reports each module alone (as `bend module.bend` would)
and the binary it builds runs one of them: `./main module`. A module the
combined book refuses (a name its file binds and Base's sugar also names)
is reported as `Left out of the binary:` and stays out.

**GPU.** Mark a call with `!` and the task tree under it runs on the GPU:
`sum!(24n, 0)`. The mark means nothing to the checker, and a binary with no
device runs it on the CPU. The device compiles only the code a `!` can
reach (and every closure), so its shader stays small however large the
program. Host and device share one address space, so nothing is copied;
the CPU and the GPU never compute at the same time. What
wins on a GPU is a balanced tree of uniform scalar leaves (mandelbrot,
nbody); divergent or skewed work (n-queens, symbolic regression) stays
faster on the CPU.
`bench/runtime/` holds sixteen worked programs; `paper/BendRT.pdf` has the
design and the numbers.

## Claims and proofs

A def can state its type inline, or as a `law` (the claim) filled by a
`def` (the body):

```python
def double(x: U32) -> U32:
  (x * 2 : U32)

law triple:
  for x: U32
  U32

def triple(x):
  (x * 3 : U32)
```

Both are the same to the checker. The split matters when the type is a
theorem: the law is what a human reads, the def is a proof nobody needs
to read. A law with no def is an open claim: a type may mention it,
live code may not call it, and the report counts it as a TODO. Another file can fill it through an import alias
(`import ./claims.bend as C`, then `def C.name(..):`); that is how a
[ProofMarket](https://proofmarket.com) bounty is claimed.

A claim is `for` lines, then `exs` lines, then the result, a body
like a def's: lets may lead to the final type.
`for -x: T` binds an erased parameter and `for +x: T` a reusable one;
`for x: T where P(x)` packs a hypothesis with `x` into a pair;
`exs y: T` asks the body to *produce* a `y`. A proposition is a type:
`Unit` is the true one (one value), `Empty` the false one (none),
`{a == b : T}` is equality, and its one proof is `{==}`, accepted when both
sides compute to the same term. Anything richer is a def that returns a
`Type`. Here is a program and a proof about it:

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

Matching `x` refines the goal in each arm. At `0n` it is
`{Nat.double(half(0n)) == 0n : Nat}`, which computes to `{0n == 0n : Nat}`.
At `1n+0n` the evidence `e : IsEven(1n+0n)` computes to `Empty`, and the
empty match (no cases) closes the arm. At `2n+p` the goal is
`{2n+Nat.double(half(p)) == 2n+p : Nat}`, and the recursive call is the
induction hypothesis, `{Nat.double(half(p)) == p : Nat}`. The rewrite
`%e : P` takes `e : {a == b : T}` and folds `b` back into `a` wherever the
motive `P` marks `_`: the goal must be `P` with `b` at the marks, and the
rest of the body proves `P` with `a` there. Drop the rewrite and the checker
answers with the spot where the two sides part:

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

An `exs` is a pair of witness and proof (`+x`, since both calls consume
`x`):

```python
law half_exists:
  for +x: Nat
  for e: IsEven(x)
  exs y: Nat
  {Nat.double(y) == x : Nat}

def half_exists(x, e):
  (half(x), half_ok(x, e))
```

A constructor clash dies by a discriminating motive:

```python
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
`Equal.cong` ship in `Base`.

**What the checker does, and does not.** It is one bidirectional pass:
inference for variables and applications, checking for everything else,
and conversion (both sides computed, compared up to eta) where they meet.
There is no unification, metavariable, implicit argument, tactic or type
class. Every type argument is written (`id(U32, 42)`), every
`do` bind is annotated, and a literal in a `let` carries its type
(`x = {10 : U32}`). In exchange, checking is linear in the code size and
every error is local: expected, observed, context, line. `?TODO` leaves a
goal open (the file checks, marked incomplete); `?name` reports the goal at
that spot as an error.

**Termination.** Every def terminates. A live recursive call must shrink a
parameter structurally: some argument is a pattern variable bound under a
constructor of that parameter (columns compare left to right; erased ones
are skipped). `n - 1` and `n > 0` prove nothing; only the pattern does, so
loops count on `Nat`. A def may call itself and what is above it, never
below: mutual recursion folds into one def with a phase argument. A loop
bounded by the world (a server) carries a `Nat` fuel it drops per step,
seeded through `U32.to_nat`; or it wears `@unsafe`, which skips its
descent check and makes the report say so:

```python
@unsafe
def forever(n: Nat) -> Nat:
  forever(n)
```

```
All 288 definitions check, with 1 annotated as unsafe.
The code is well-typed, but may contain logical paradoxes.
```

`demos/nat_proofs/main.bend` is a full commutative-semiring development;
`paper/BendTT.pdf` is the theory.

## The language

**Datatypes.** `type` declares constructors and a kind: `Data` for values
that may be reused, `Type` for values that may not. Fields are reached by
pattern matching only, which moves them out and frees the node:

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

There is no `if`. A condition is a `Bool`, matched like any value, and a
match opens a *parameter* or a *field* (in the order they were bound),
never a computed value: the caller computes, a helper decides. One match
takes several scrutinees, patterns nest, and `_` catches the rest:

```python
def fizz(n: U32, by3: Bool, by5: Bool) -> String:
  match by3, by5:
    case True{}, True{}:
      "FizzBuzz"
    case True{}, False{}:
      "Fizz"
    case False{}, True{}:
      "Buzz"
    case _, _:
      U32.show(n)

def go(+n: U32) -> String:
  fizz(n, U32.is_eq((n % 3 : U32), 0), U32.is_eq((n % 5 : U32), 0))
```

**Values.** `42` is a `U32`, the 32-bit word; `1.5` is an `F32`, with
`F32.sqrt` to `F32.atan2`; `3n` is a `Nat`, unary: `1n+p` is a successor.
Operators name the methods of the type after `:` in the parens around
them, `(a + b * c : U32)`, else `Nat`; comparisons answer `Bool`, and equality is a call
(`U32.is_eq`; the `==` token is the equality type). `'A'` is a `Char`,
`"abc"` a `String` (a chain of `Char`;
`++` appends), `[1, 2, 3]` a `List` (`h <> t` is cons) and `(a, b)` a pair
of type `A & B`; longer tuples nest to the right. Each number type has
`.show`, `.read` (to a `Maybe`) and conversions such as `U32.to_nat` and
`F32.to_u32`. Division by zero answers `0` for `/` and `a` for `%`. There
is no match on a word: count on `Nat`, compute on `U32`. The
[appendix](#appendix-operators) lists every operator; `Base`'s list kit is
`List.map`, so write the recursion you need.

```python
def len(xs: List<U32>) -> U32:
  match xs:
    case Nil{}:
      0
    case Con{h, t}:
      (1 + len(t) : U32)
```

**Functions.** `x => body` is a lambda and `A -> B` its type (`@x: A -> B`
when `B` depends on `x`). A closure captures its scope and is used once:
function types are `Type`, so no `+` binds one; top-level defs may be
called freely. A type parameter is an erased argument, written
`-A: Type` and passed at every call: `id(U32, 42)`.

```python
def apply(f: U32 -> U32, x: U32) -> U32:
  f(x)

def main() -> IO(Unit):
  k = {10 : U32}
  IO.print(U32.show(apply(y => (y + k : U32), 1)))
```

A body is statements, then one expression: `x = v` binds the inferred
value (a literal needs `{v : T}`); `+x = v` binds a reusable value (its
type must be `Data`); `K{a, b} = p` and `(a, b) = p` open a parameter or
a field; `a b = f(x) g(y)` forks; `m2 = m[i] <- v` writes an array. One
statement per line.

**Arrays.** `Array<T>` is a perfect binary tree of `2^d` slots that the C
backend stores flat: `a[i]` reads and `a[i] <- v` writes in place, O(1),
and the language stays pure because an array has one owner (`Array<T>` is
`Type`). Indices wrap at the length. `Array.new(T, d, v)` builds one; a
read answers the pair `Array<U32> & U32`, opened by a helper:

```python
def read3(r: Array<U32> & U32) -> U32:
  (m, x) = r
  x

def main() -> IO(Unit):
  m = Array.new(U32, 2n, 0)
  m2 = m[7] <- 7
  IO.print(U32.show(read3(m2[3])))
```

`Array.get` and `Array.new` take any `Data` element (`a[i]` is the `U32`
case), `Array.set` and `Array.swap` any element; `Array.swap` and
`Array.size` answer the array with the old element or the length.
`Base` also has `Map<a, V>`, an immutable string-keyed tree, and `Set()`
over it.

**IO and effects.** `main` answers `IO(A)`, and `do` chains actions. A line
binds (`x : T <- act`), discards (`T <- act`), lets (`x : T = v`) or
returns (`return v`); the last line is the block's value:

```python
def main() -> IO(Unit):
  do IO<Unit>:
    Unit <- IO.write("Hello, ")
    name : String <- IO.try(String, IO.get_env("USER"))
    Unit <- IO.print(name)
    IO.die(Unit, 2, "bye")
```

`IO.die` writes its message to stderr and exits with its code. `do` is
sugar over `M.bind` and `M.pure`, so it works for `Maybe` and `Result` too
(`do Maybe<&2, U32>:`). `IO` itself is a `Base` definition, a continuation
over one `IO.OP` datatype; what is built in is the event loop that runs
each emitted effect, in order.

The kit covers stdout and stderr, the environment, files, and TCP and UDP
sockets (`IO.print`, `File.open`, `TCP.listen`, `UDP.bind` and their
families). Every fallible effect answers
`Result<&1, &1, U32 & String, A>` (`Done` or `Fail{(errno, message)}`):
`IO.try(A, act)` runs one and unwraps it, dying on `Fail`; `IO.pass(A, r)`
lifts a `Result` in hand. Handles (`File`, `Socket`, `Listener`) are
affine, and an op that consumes one answers `H & Result<..>`, the handle
*outside* the `Result`, so even a failure hands it back. Bytes ride
`String`s, one byte per `Char`. `demos/http_server/main.bend` is a complete
server over this kit.

**Concurrency.** A program is a set of computations that one event loop
runs, as Node runs callbacks: each computation is sequential Bend code
that steps to its next effect; an effect that must wait (a socket with no
data, a sleep, a file read on a helper thread) parks only its own
computation, and the loop runs another. `IO.spawn(A, act)` starts `act` as
a computation of its own and answers at once; a computation talks to
another through a `Chan<A>`, a Data handle both may copy: `Chan.new(A,
room)` opens one holding up to `room` values (room 0 hands each value
straight from a sender to a receiver), `Chan.send(A, c, v)` answers `True`
or, on a closed channel, `False`; `Chan.recv(A, c)` answers `Some{v}`,
parking until one arrives, or `None` once the channel is closed and
drained; `Chan.close(A, c)` closes it: a parked sender answers `False`,
what is queued still drains, and the channel's row goes once it is empty.
`IO.fork(A, act)` spawns `act` and answers the channel its value arrives
on; `IO.join(A, c)` takes it and closes the channel. `IO.sleep(ms)` parks
for a span, `IO.now()` reads a monotonic clock in milliseconds. The process
ends when every computation has answered (main's return alone ends
nothing), with `IO.die`'s code from any computation, or with 1 and a
deadlock message when computations remain and nothing is pending. The
loop polls sockets and timers when no computation can step. Handles
share one table of 4096 rows; `Chan.new` past it fail-stops. A pure
computation inside a step still runs on every core: parallelism comes from
the pool and the GPU, concurrency from the loop.

```python
def work(ms: U32, +n: U32) -> IO(U32):
  do IO<U32>:
    Unit <- IO.sleep(ms)
    Unit <- IO.print(String.append("done ", U32.show(n)))
    return n

def main() -> IO(Unit):
  do IO<Unit>:
    a : Chan<U32> <- IO.fork(U32, work(30, 1))
    b : Chan<U32> <- IO.fork(U32, work(10, 2))
    x : U32 <- IO.join(U32, a)
    y : U32 <- IO.join(U32, b)
    IO.print(U32.show((x + y : U32)))
```

Each effect is a **foreign fill**: a def whose body is import lines naming
a `.c` and a `.js` file. You can add your own:

```python
def Text.rev(text: String) -> IO(String):
  import "./effs/text_rev.js"

def main() -> IO(Unit):
  do IO<Unit>:
    s : String <- Text.rev("bend")
    IO.print(s)
```

```js
// effs/text_rev.js
function text_rev(text) {
  return Array.from(text).reverse().join("");
}
```

The host function is named after the def, lowercased, dots to underscores;
it takes and returns the backend's own values. A `.js` file serves
`bend file.bend` and `-o .js`; a native build needs a `.c` twin. In C an effect registers with `io_eff(FID, CID,
run, need)` and `Term run(Env e, Term* f, IoWork* w)` runs on the loop
thread: a `need` of 0 runs it at once; `IO_READ` first waits for the
socket in its first field to be readable, `IO_TIME` sleeps its first
field's milliseconds. A call that may block must not run on the loop: the
run decodes its arguments into `w` (plain C) and answers `io_work(w, call, pack)`; `call(w)` then runs on a helper
thread and touches only `w` and the handle table, and `pack(e, w)` builds
the answer back on the loop. An effect file holds one effect and its own
helpers; the runtime IO API is comp.ts's, so a def and its two files delete
clean. A computation yields only when it
parks or ends: a print, `IO.now` or `IO.spawn` does not. The JS lane waits on sockets and timers through `poll`, told by a `<name>_need` function answering `{read: kind}` or
`{time: true}`. A foreign fill must answer `IO`, and only the event loop
runs it. There is no other FFI, so proofs, totality and the GPU never see
host code.

**Graphics.** A frame is an `Image`, a quadtree: `Pix{color}` (0x00RRGGBB)
fills its quadrant, `Qua{tl, tr, bl, br}` splits one. A w x h window shows
the smallest 2^k square covering it, top-left, clipped. An `Event` is
`Key{code, down}`, `Mouse{x, y, button, down}`, `Move{x, y}` or `Close{}`
(the close button; the window stays until closed). `Window.open(title, w,
h)` answers a `Window` in a `Result` (w and h in device pixels; a Fail
without a display). `Window.frame(window, image)` shows it at the
display's rate and answers the handle, the same image and the events since
the last frame, oldest first. `Window.close` closes. An `App<S>` is
`App{view, tick}`: `view` answers the state beside its `Image`, so a linear
state threads through and a Data state answers `(s, image)`; `tick` folds
a frame's events into the next state in IO and answers `None` to quit.
`App.run(~S, ~app, title, w, h, state)` runs a tick per frame in a window;
`App.play(~S, ~app, frames, state)` runs it over scripted frames without
one. The smallest app:

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
lowercased (space 32, enter 13, tab 9, escape 27, backspace 127); the
function keys as they are (up 63232, down 63233, left 63234, right 63235);
a key with no character (a modifier) 65536 plus its hardware code. Mouse
positions are device pixels from the top-left; buttons are 0 left, 1
right, 2 middle. A hidden or minimized window paces at one frame per
second. Build with `-o`: the JS backend has no display and refuses
`Window.open`. `demos/pong_game` draws a few hundred nodes per frame;
`demos/ray_tracer` ray-marches every pixel on the GPU with one `!`.

**Imports.** Import lines come first in a file:

```python
import Base
import ./lib/util.bend as Util
```

A file's namespace is its path without `.bend`; `as Util` is an alias for
this file only, so `Util.inc` names `lib/util.inc`, and a
`def Util.inc_one(x):` here fills a law that `util.bend` left open.
Names are dotted and dots are just characters: `U32.show` needs no module.
An `import 0x<hash>/path.bend as P` line is a content-addressed package,
read from `$BEND_STORE` (default `~/.bend/store`) and fetched from
`$BEND_HUB` (default proofmarket.com) on a miss. Cycles are rejected.

**Templates.** A `def` whose first parameter has `~` is a template: its
text parses once, and each call with a distinct tuple of `~` arguments
compiles to its own copy of the def, `T~n`, with the arguments substituted
as syntax. Base's `List.map` is one, written as:

```python
def List.map(~A: Type, ~B: Type, ~f: A -> B, xs: List<A>) -> List<B>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{f(h), List.map(~A, ~B, ~f, t)}
```

A call writes `~` at the leading positions and compiles to the loop you
would write by hand, with no closure at run time:

```python
def main() -> List<Nat>:
  List.map(~Nat, ~Nat, ~(x => Nat.add(x, 1n)), [1n, 2n, 3n])
```

Inside the template `f(h)` is the argument applied: a `~` lambda applied
there is a macro. Every type parameter that a `~` parameter's type mentions
is `~` too. A `~` argument must be closed (no local of the caller inside
it): an open one leaves the call a plain call of the template's name, which
the checker refuses as a defined name; pass the local at run time.

A `~` argument tuple over 2048 characters, like an open one, leaves the
call plain. A template's text may only call templates declared above it. A
`~` on a runtime position joins the key: write `~` only at compile-time
positions. A `~` lambda headed by a `let`, and a curried macro whose body
is a constructor, do not inline: the checker cannot infer them inside the
instance.

## Advanced

### Quantities

Every binder has one of three quantities: `x` (used once), `-x` (erased:
types, proofs, generics; gone at run time), `+x` (used many times). Values
move: into calls, into constructors, into the match that opens them;
dropping is free. Dead positions (types, erased arguments, equation
endpoints, motives) count nothing.

`+` forms only at kind `Data`. Every type has a kind `Kind(q)`: `Data` is
`Kind(&2)`, `Type` is `Kind(&1)`, and a `Data` constructor holds only
`Data` fields. `U32`, `F32`, `Nat`, `Bool`, `Char`, `String`, `Set()` and
every equation are `Data`; function types, `Array<T>`, `IO(A)` and the
handles are `Type`. A `+` scrutinee hands out `+` fields, and a field
declared `+` is reusable even in an affine holder. There is no copy
function: a `Type` value is reused by hand or not at all.

A datatype takes one quantity per parameter (a bare name in its header),
and `Kind(a)` is the kind of the types of that quantity, so a container is
as reusable as its element: `List<&2, U32>` may be reused, `List<&1, U32>`
(also spelled `List<U32>`) may not, and the two are different types;
`+List<U32>` spells the first. Generic code takes the quantity as an
erased parameter:

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

`length(&2, U32, [1, 2, 3])` and `length(&1, U32 -> U32, [y => y])` both
check. `A & B` is `Sigma<&1, &1, A, _ => B>`, the affine pair; the `&2`
one may sit under `+`. Every refusal is one of two errors: `expected :
Data, observed : Type`, or `x (consumed more than once)`.

### The theory, briefly

Terms check in two modes: live (runs) and dead (only checks). A dead term
may diverge and may inhabit `Empty`; nothing promotes dead to live. That
wall, with the usage cap, is why Bend keeps `Type : Type`, impredicativity
and negative datatypes (`type Trm is Type: Lam{f: Trm -> Trm}` is
accepted) with no universe levels and no positivity check: every classical
paradox contracts a function-typed binding, and no function type is
`Data`. Equality is intensional, elimination is J (`%`), conversion is up
to eta, and there is no funext. The core is mechanized in Lean
(`bend2/bend.lean`), rules as the checker runs them: confluent, sound
along live steps, normalizing and consistent with `Type : Type` and
negative datatypes.

### The runtime, briefly

A term is one 64-bit word; words, floats, small `Nat`s and nullary
constructors are unboxed. There is no garbage collector: a match frees its
node on the spot, often reusing it for the arm's own constructor, and `+`
values carry a count and are never cloned. Compiled code is one flat
worklist machine, so recursion depth is bounded by memory, not by the C
stack. The same C source is the host program and the Metal or CUDA kernel.

### Bend as a JS library

Imported instead of run, `bend2/main.ts` is a loader that makes a `.bend`
file a module. Under node, register it on the command line; under Bun,
preload it once:

```bash
node --import ./bend2/main.ts app.mjs
```

```toml
# bunfig.toml
preload = ["./bend2/main.ts"]
```

```python
import Base

type Move is Data:
  Up{}
  Down{}

type State is Data:
  State{pos: U32, won: Bool}

def init() -> State:
  State{0, False{}}

def step(s: State, m: Move) -> State:
  State{pos, won} = s
  match m:
    case Up{}:
      State{(pos + 1 : U32), won}
    case Down{}:
      State{(pos - 1 : U32), won}
```

```js
import Game from "./game.bend";

let st = Game.init();
st = Game.step(st, { $: "Up" });
console.log(st.pos, st.won);   // 1 false
```

Every filled non-IO def is exported and takes only its live arguments,
in one call or curried (`Game.step(st)({ $: "Up" })`). A constructor is
`{$: "Name", field: value, ...}`, a closure is a function, `Nat` is a
`BigInt`; `Bool`, `U32` and `String` are native.
`bend page.html -o dist` bundles a page for the browser with the loader
on.

### Coming from Lean or Agda

No tactics, no implicits, no unification, no universe levels, no
positivity check, no funext, no holes but `?TODO`. In exchange: a checker
you can read, `Type : Type` without paradox, proofs that are ordinary
recursive programs, and every accepted program compiles to GC-free parallel
C.

## Appendix: operators

Higher binds tighter; every operator is a named def in `Base`.

| level | operators | meaning |
|---|---|---|
| 1 | `A & B`, `A \| B` | pair type, `Either` type (right-assoc) |
| 2 | `\|\|` | `Bool.or` |
| 3 | `&&` | `Bool.and` |
| 4 | `< <= > >=` | `T.is_lt`, `T.is_le`, `T.is_gt`, `T.is_ge` |
| 5 | `h <> t`, `a ++ b` | cons, `String.append` (right-assoc) |
| 6-8 | `.\|. .^. .&.` | `T.or`, `T.xor`, `T.and` |
| 9 | `x << n`, `x >> n` | `T.shln`, `T.shrn`: shifts by a `Nat` |
| 10 | `+ -` | `T.add`, `T.sub` |
| 11 | `* / %` | `T.mul`, `T.div`, `T.mod` (`%` needs spaces) |

`T` is the type after `:` in the parens around the operators,
`(a + b * c : U32)`, else `Nat` (which has `Nat.divmod`, no `div` or
`mod`); inner parens inherit it, a call argument
is `f((a + b : U32), c)`, and an index `a[i + 1]` is `U32`. An operator
headed by `>` needs a space before it. `f!(x)` marks a call for
the GPU; `a[i]` and `a[i] <- v` are the array sugars. `@x: A -> B` and
`&x: A -> B` are the dependent function and pair types; `&1` and `&2` are
quantities, `a <&> b` their meet, `Kind(q)` a kind.
