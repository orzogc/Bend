# Bend

In the post-AGI economy, what still matters for a programming language? Two things:

1. It must be **fast**. Check and run on CPUs & GPUs at *lightning speed*.

2. Vibe-coding must **work**. Agents using it must produce *correct code*.

That's it. Nothing else matters. Bend addresses both. And nothing else.

![Bend, in five minutes](media/intro.gif)

## Bend runs FAST

**Target:** be as fast as C on the CPU, as fast as CUDA on the GPU. **Status:**

![Single-core benchmarks](media/single_core.svg)

Strong types, linearity and purity let Bend compete with hand-written C on one
core and scale to thousands of CPU or GPU threads, with near-ideal speedups at
near-zero effort. It is up to 100x faster than Bend 1, with f32, u32, mutable
arrays, 8 TB of heap and zero interaction-net overhead. The compiler is new:
expect bugs and programs that under-perform C or CUDA. If you find one, please
write an issue.

## Bend checks FAST

**Target:** outperform every proof assistant by several OOMs. **Status:**

![Checker benchmarks](media/checker.svg)

As AI models get faster, compile times become the bottleneck of software
engineering. Other proof assistants take minutes on a mid-sized codebase, making
proofs unviable. Bend is fully annotated, so checking is one linear
bidirectional pass that scales to huge codebases, and proofs stay practical. The
tradeoff is verbosity, but nobody writes code by hand anymore, and AI models
like the annotations.

## Bend vibe-coding WORKS (with proof!)

**Q:** How can I **trust** AI code without **reading** it?

**A:** Just ask your agent to write a **proof**.

Suppose you wrote a game that must be unbeatable: if the player grabs the flag,
you lose. In other languages, you'd write *tests*. But you can't test infinitely
many sequences of moves. On Bend, you state the law in `LAWS.bend`:

```python
# LAW: no move sequence leads to victory.
law you_cant_win:
  for moves: List<Move>           # any sequence of moves
  board = replay(start(), moves)  # replayed from the start
  is_won(board) == False          # never leads to victory
```

Then ask your agent: "before stopping, **prove the code is correct**". It writes
the proof into `PROOF.bend`, a certificate you neither write nor have to read:

```python
# PROOF: you_cant_win holds.
def you_cant_win(moves):
  # ... written by the AI
```

Once the proof lands, your code is correct. Mathematically.

> We must stress what this means. This is not a test. This is not an audit.
> This is a MATHEMATICAL PROOF. This is hard to grasp because it is uncommon.
> But that's what it is. Theorem proving is not new, just new to a super fast
> language. With Bend, the same intelligence that disproved the Jacobian
> Conjecture will now prove that your vibe coded SaaS never displays an
> uncentered div again. And that's beautiful.

**tl;dr with proofs, "make no mistakes" becomes enforceable**

The full game, proof included: [demos/app_win_is_bug_2d](demos/app_win_is_bug_2d).

# Examples

Bend's **syntax** is, essentially, "Python with dependent types".

```python
import Base

# Performs effects on the CPU.
def main() -> IO(Unit):
  do IO<Unit>:
    name : String <- IO.try(String, IO.get_env("USER"))
    IO.print("Hello, " ++ name)
```

**Parallelism** is achieved via divide-and-conquer.

`!` runs a call on the GPU. Host and device share one memory: nothing is copied.

```python
import Base

# Computes 2^d in parallel: a tree of d levels, one leaf per unit.
def pow2(+d: Nat) -> U32:
  match d:
    case 0n:
      1
    case 1n+p:
      a b = pow2(p) pow2(p)
      (a + b : U32)

# Runs pow2 on the GPU, via `!`.
def main() -> IO(Unit):
  result = pow2!(20n)
  IO.print(U32.show(result))
```

**Claims** are just laws with "for" and "exs" lines.

**Proofs** use a direct, inductive style.

```python
import Base

# CLAIM: for every nat x, x + 0 equals x.
law add_zero:
  for x: Nat
  {Nat.add(x, 0n) == x : Nat}

# PROOF: induction on `x`, one rewrite (`%`) per step.
def add_zero(x):
  match x:
    case 0n:
      {==}
    case 1n+xp:
      %add_zero(xp) : {1n+Nat.add(xp, 0n) == 1n+_ : Nat}
      {==}
```

For more examples, check:
- [demos](demos): some curated demos.
- [bend2/base.bend](bend2/base.bend): the base library.
- [bench/runtime](bench/runtime): all the benchmarks.

# Get Started

### 1. Install:

```bash
curl -fsSL https://bend-lang.com/install.sh | sh
```

### 2. Save a Hello World:

```python
import Base

def main() -> IO(Unit):
  IO.print("Hello, world!")
```

### 3. Check, Compile, Run:

```bash
bend hello.bend             # check + run
bend hello.bend -o hello    # compile to a native binary (a ! needs Metal or CUDA)
./hello                     # run!
```

### 4. Tell your agent to use Bend:

```
Build this project with Bend-Lang:
- run `bend guide` to learn it
- use **laws** to avoid mistakes
- use **parallel** to make it fast
```

Currently, Bend works best for back-end projects on Linux / OSX.

# References

- Guide: [GUIDE.md](guide/GUIDE.md), also printed by `bend guide`.
- Base: [base.bend](bend2/base.bend), the base library, also printed by `bend base`.
- Paper: [BendTT: An Affine Dependent Type Theory](paper/BendTT.pdf).
- Paper: [BendRT: A Parallel Runtime for CPUs and GPUs](paper/BendRT.pdf).
- Formalization: [bend.lean](bend2/bend.lean), Bend's core in Lean.

# Community

- Discord: https://discord.bend-lang.com
- Twitter/X: https://x.com/bendlang
- Reddit: https://www.reddit.com/r/bendlang/
- Issues: https://github.com/bendlang/bend/issues

# Limitations

- Bend 2 is a new language: Bend 1 programs and HVM do not carry over, and there is no migration path.
- Everything is annotated and nothing is inferred: types, quantities and motives are written by hand.
- Proofs are written by hand or by your AI: there are no tactics, no proof search and no automation.
- Proving a theorem in Bend takes more lines and more time than the same theorem in Lean or Rocq.
- Values are affine: a closure is called at most once and cannot be cloned; only data and arrays can.
- Recursion must be structural, mutual recursion is rejected, and every live function must terminate.
- A `match` inspects a parameter or a pattern variable, never a computed value, and there is no `if`.
- Numbers are `Nat`, `U32` and `F32`: no `U64`, `I64` or `F64`, since Metal has no double precision.
- `F32` is axiomatic: its operations have no proofs, so nothing about floating point can be proven.
- `U32` cannot be matched on, so loop counters are `Nat`s, and array indexes wrap around silently.
- Strings are linked lists of characters, not packed bytes, so text processing is slow and heavy.
- There is one universe and `Type : Type`, kept consistent by the live/dead wall, not by a hierarchy.
- There are no type classes or traits, and no macros beyond compile-time templates.
- Base is small: expect to write list, string and map helpers that other languages ship built in.
- Effects are few: print, env, time, sleep, spawn, channels, files, TCP, UDP, a window and audio.
- There is no TLS, HTTP library, JSON or regex; a new effect is C or JS that you write yourself.
- Targets are C, Metal, CUDA and JavaScript; Lua, Luau and Python are planned, not present.
- The JavaScript target runs on one core and has no graphics: `!`, Window and Audio are native only.
- One GPU per program, one event loop per program, and no distributed or multi-machine execution.
- The compiler emits one C file for the whole program: no separate compilation, no incremental builds.
- The heap is one 8 TB reservation with no garbage collector; only `+` values are reference counted.
- The compiler is far less mature than GCC or Clang, and unusual code can run well below C speed.
- Benchmarks are few, especially for the checker; the numbers above are honest but narrow.
- The compiler is significantly AI-written, and the Lean formalization covers the core only.
- Building a binary needs clang 19 or newer; `!` needs Metal on macOS or CUDA 12 on Linux.
- No Windows (WSL works); on Linux, Window needs `libx11-dev` and Audio needs `libasound2-dev`.
- The hub has no names, versions, accounts or search: a package is its hash, capped at 16 MiB.
- Error messages are terse; there is no debugger, profiler, formatter, REPL or language server.
- There is no editor support, no test framework and no documentation beyond the guide.

Most of these limitations are being addressed and will improve over time.

**BEND IS YOUNG. EXPECT BUGS AND [REPORT THEM](https://github.com/bendlang/bend/issues).**
