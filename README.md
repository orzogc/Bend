# Bend4

In the post-AGI economy, what still matters for a programming language? Two things:

1. It must be **fast**. Check and run on CPUs & GPUs at *lightning speed*.

2. Its programs must **work**. Agents using it must produce *correct code*.

That's it. All else is fluff. Bend addresses both. And nothing else.

## Bend4 runs FAST

**Target:** be as fast as C on the CPU, as fast as CUDA on the GPU. **Status:**

![Single-core benchmarks](docs/assets/single_core.svg)

Strong types, linearity and purity let Bend compete with hand-written C in
single-core performance, and it scales to thousands of CPU or GPU threads, with
near-ideal speedups, near-zero programmer effort. Compared to Bend 1, this
version is up to 100x faster, supports f32, u32, mutable arrays, up to 8 TB of
heap memory, all with zero interaction net overhead. The compiler is still new,
so expect bugs and defective programs (where it under-performs C or CUDA).
These will be fixed as the pipeline matures. If you ever come across one, please
write an issue.

## Bend4 checks FAST

**Target:** outperform every proof assistant by several OOMs. **Status:**

![Checker benchmarks](docs/assets/checker.svg)

As AI models become faster, compilation times become a critical bottleneck on
the software engineering process. Alternative proof languages often take several
minutes to check a medium sized codebase, making proofs unviable. Since Bend is
fully annotated, checking is done by a linear bidirectional pass, meaning it
scales to massive codebases without losing performance, making proofs truly
practical. The tradeoff is that Bend is a bit verbose, but nobody is writing
code anymore, and AI models even appreciate the extra annotations.

## Bend4 programs WORK (with proof!)

**Q:** How can I **trust** AI code without **reading** it?

**A:** Just ask your agent to write a **proof**.

Here's how it works. Suppose you implemented a trading game, and you wanted to
prevent bugs like cloning assets. In other languages, you'd write *tests*. But
there are infinitely many game states. You can't test them all. On Bend, you ask
your agent: "before stopping, **prove that your code is correct**". It outputs:

```python
# CLAIM: no sequence of trades can result in cloned assets
assert no_cloned_assets:
  forall ts: +List<Trade>
  forall g: Game
  {assets(run(ts, g)) == assets(g) : Bag}

# PROOF: the `no_cloned_assets` assert holds.
def no_cloned_assets(ts, g):
  # (LONG. leave this part for the AI!)
```

And that's it. Once that proof lands, your code is correct. Mathematically.

> We must stress what this means. This is not a test. This is not an audit.
> This is a MATHEMATICAL PROOF. This is hard to grasp because it is not a common
> feature. But that's what it is. Theorem proving is not new, it is just new to
> a super fast language. With Bend, the same intelligence that disproved the
> Jacobian Conjecture will now prove that your vibe coded SaaS never displays an
> uncentered div again. And that's beautiful.

**tl;dr with proofs, "make no mistakes" becomes enforceable**

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

# Sums a range of numbers in parallel.
def sum(+d: Nat, +i: U32) -> U32:
  match d:
    case 0n:
      i
    case 1n+p:
      a b = sum(p, i * 2) sum(p, i * 2 + 1)
      a + b

# Runs sum on the GPU, via `!`.
def main() -> IO(Unit):
  result = sum!(24n, 0)
  IO.print(U32.show(result))
```

**Claims** are just asserts with "foralls" and "exists".

**Proofs** use a direct, inductive style.

```python
import Base

# CLAIM: for all nums a, b and c, a + (b + c) equals (a + b) + c.
assert add_assoc:
  forall  a: Nat
  forall -b: Nat
  forall -c: Nat
  {Nat.add(a, Nat.add(b, c)) == Nat.add(Nat.add(a, b), c) : Nat}

# PROOF: induction on `a`, one rewrite (`%`) per step.
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

# Get Started

### 1. Install:

```bash
# needs Bun 1.3+ (https://bun.com) and a C compiler; Metal or CUDA for the GPU
git clone https://github.com/HigherOrderCO/bend4
cd bend4
bun .devs/scripts/install.ts   # puts `bend` on the PATH (~/.bun/bin)
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
bend hello.bend -o hello    # compile to a native binary (GPU-enabled when Metal or CUDA links)
./hello                     # run!
```

### 4. Read the Guide:

Everything else you need is in [Bend's GUIDE.md](docs/GUIDE.md). Read it!

## Formalization

- Bend's core is [formalized in Lean](bend2/bend.lean). Read the paper: [BendTT: An Affine Dependent Type Theory](docs/BendTT.pdf).

- The runtime is also documented. Read the paper: [BendRT: A Parallel Runtime for CPUs and GPUs](docs/BendRT.pdf)
