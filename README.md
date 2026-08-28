# Bend4

In the post-AGI economy, only two things still matter for a programming language.

1. It must be **fast**. Run on CPUs and GPUs at light speed.

2. It must be **correct**. Agents using it must produce bug-free code.

That's it. All else is fluff. Bend is both. And nothing else.

## Bend4 runs FAST

**Target:** as fast as C on the CPU, as fast as CUDA in the GPU.

**State:**

![Single-core benchmarks](docs/assets/single_core.svg)

## Bend4 checks FAST

**Target:** outperform every proof assistant by several OOMs.

**State:**

![Checker benchmarks](docs/assets/checker.svg)

## Bend4 programs are CORRECT

**Q:** How can I **trust** AI code without **reading** it?

**A:** Just demand a **proof**.

Here's how it works. SUppose you implemented a trading game, and you wanted to
prevent bugs like cloning assets. In other languages, you'd write *tests*. But
there are infinitely many game states. You can't test them all. On Bend, you can
ask your AI to write a **proof** instead. It will output something like this:

```python
# CLAIM: for every game state, for every sequence of trades,
# the count of every item in the game stays EXACTLY the same.
assert no_cloned_items:
  forall t: &List<Trade>
  forall g: Game
  {items(run(t, g)) == items(g) : Bag}

# PROOF: the `no_cloned_items` assert holds.
def no_cloned_items(ts, g):
  # ... this is long. your AI writes that ...
```

Once that is done, the property holds. Mathematically. Assets can't be cloned.

> We must stress what this means. This is not a test. This is not an audit.
> This is a MATHEMATICAL PROOF. This is hard to believe because it is not a
> common feature. But that's what it is. Theorem proving is not new, it is just
> new to a super fast language. With Bend, the same intelligence that disproved
> the Jacobian Conjecture will now prove mathematically that your vibe coded
> SaaS never displays an uncentered div again. And that's beautiful.

**tl;dr with proofs, "make no mistakes" becomes enforceable**

# Examples

Bend's syntax is, essentially, "Python with dependent types". Every `def` fills
a prior `assert`, which states its type:

```python
import Base

# Performs effects on the CPU.
assert main:
  IO(Unit)

def main():
  do IO<Unit>:
    name : String <- IO.try(String, IO.get_env("USER"))
    IO.print("Hello, " ++ name)
```

**Parallelism** is achieved via divide-and-conquer. `!` is used for GPU
evaluation.  Memory is fully unified. Passing arbitrary data and closures from
CPU to GPU is O(0) operation.

```python
import Base

# Sums a range of numbers in parallel.
assert sum:
  forall +d: Nat
  forall +i: U32
  U32

def sum(d, i):
  match d:
    case 0n:
      i
    case 1n+p:
      a b = sum(p, i * 2) sum(p, i * 2 + 1)
      a + b

# Runs sum on the GPU, via `!`.
assert main:
  IO(Unit)

def main():
  IO.print(U32.show(sum!(24n, 0)))
```

**Claims** are just asserts with "foralls" and "exists".

**Proofs** use a direct, inductive style.

```python
import Base

# Claim: "for all numbers a, b and c, a + (b + c) equals (a + b) + c".
assert add_assoc:
  forall a: Nat
  forall -b: Nat
  forall -c: Nat
  {Nat.add(a, Nat.add(b, c)) == Nat.add(Nat.add(a, b), c) : Nat}

# Proof: induction on `a`, one rewrite (`%`) per step.
def add_assoc(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_assoc(p, b, c) : {1n+Nat.add(p, Nat.add(b, c)) == 1n+_ : Nat}
      {==}
```

For more examples, check:
- [demos](demos): some curated demos.
- [bend2/base.bend](bend2/base.bend): the base library.
- [bench/runtime](bench/runtime): all the benchmarks.

To learn more, read:
- [GUIDE.md](docs/GUIDE.md): a complete guide.


# Get Started

### 1. Install:

```bash
# needs Bun 1.3+ (https://bun.com) and macOS on Apple Silicon
git clone https://github.com/HigherOrderCO/bend4
cd bend4
bun .devs/scripts/install.ts   # puts `bend` on the PATH (~/.bun/bin)
```

### 2. Save a Hello World:

```python
import Base

assert main:
  IO(Unit)

def main():
  IO.print("Hello, world!")
```

### 3. Check, Compile, Run:

```bash
bend hello.bend               # check + run
bend hello.bend --to hello.c  # compile to C
cc -std=c11 -O3 hello.c -o hello -lpthread
./hello                       # run!
```

### 4. Read the Guide:

Everything else you need is in [Bend's GUIDE.md](docs/GUIDE.md). Read it!

## Formalization

- Bend's theory is [formalized in Lean](bend2/bend.lean). Read the paper: [BendTT: A Linear Dependent Type Theory](docs/BendTT.pdf).

- The runtime is also documented. Read the paper: [BendRT: A Parallel Runtime for CPUs and GPUs](docs/BendRT.pdf)
