// Check-time benchmark generator: Bend3's checker suite
// (.devs/bench/checker/_gen_.ts there), ported 1-to-1 to the Bend4
// dialect. One shared plan -- module kinds, call wiring and literal
// sizes are pure functions of the module index, unchanged from Bend3 --
// and one renderer, so the two languages check the same workload: same
// datatypes, same functions, same lemmas, same proof granularity, each
// spelled in the language's normal idiom. Bend4's idiom differs from
// Bend3's exactly where the core differs: a definition is an assert
// plus a fill, an equation spells ==, a rewrite states its motive
// (there is no unification), and a binder consumed twice is spelled +.
// Four benches carry #[halts] (their algorithms duplicate binders and
// a fresh algebra owns no Copiable witness); generics validates
// strict. Five benches, each sized by a module count n:
//
//   defs     program-shaped code, no proofs: modules of small
//            first-order functions over a shared Nat and List, each
//            calling earlier modules
//   proofs   algebraic lemma families: modules cycle a fresh
//            unary-nat algebra (add: zero/succ/comm), a list algebra
//            (cat/len: nil/assoc/len_cat) and a tree algebra
//            (mirror/size: involution/preservation via the shared
//            add_comm)
//   compute  type-level computation: theorems mul(a,b) == mul(b,a) on
//            unary literals closed by conversion alone, plus values of
//            the computed type family Tup(n)
//   trees    evaluation speed, after smalltt's ForceTree/TreeConv:
//            per module, alltrue(full(f)) == T by conversion, and
//            mirror(full(m)) == full(m) -- both sides normalize the
//            whole tree
//   generics polymorphic instantiation: a prelude of generic
//            Box/Pair/Option/List utilities; each module mints a
//            fresh atom type and checks it through the library, type
//            arguments explicit (the Bend idiom)

export type Bench = "defs" | "proofs" | "compute" | "trees" | "generics";

export const BENCHES: Bench[] = ["defs", "proofs", "compute", "trees", "generics"];

// The shared plan
// ---------------

// compute-bench literal sizes: a*b unfold steps per theorem, sizes
// varied so no checker can specialize on one shape
export function plan_lit(i: number): { a: number; b: number; k: number } {
  return { a: 8 + ((i * 5) % 24), b: 8 + ((i * 11) % 24), k: 4 + ((i * 3) % 28) };
}

// trees-bench sizes: full-tree depths per module, varied the same way
export function plan_tree(i: number): { f: number; m: number } {
  return { f: 7 + ((i * 5) % 6), m: 6 + ((i * 3) % 5) };
}

// generics-bench sizes: Box nesting depth per module
export function plan_box(i: number): number {
  return 2 + ((i * 5) % 4);
}

// defs-bench wiring: the Nat -> Nat function a module composes with is
// the most recent one an earlier module produced
export function plan_prev(i: number): string {
  for (let j = i - 1; j >= 0; j--) {
    if (j % 3 === 0) {
      return "fa" + String(j);
    }
    if (j % 3 === 2) {
      return "gc" + String(j);
    }
  }
  return "dbl";
}

// Render
// ------

// gen_def: the assert/def pair -- Bend4's one spelling of a definition
function gen_def(name: string, doms: string[], ret: string, binds: string[], body: string): string {
  const claim = doms.map((d) => "  forall " + d + "\n").join("");
  return "assert " + name + ":\n" + claim + "  " + ret + "\n\n"
    + "def " + name + "(" + binds.join(", ") + "):\n" + body + "\n\n";
}

function gen_prelude(bench: Bench): string {
  let s = bench === "generics" ? "" : "#[halts]\n\n";
  s += "type Nat:\n  Z{}\n  S{pred: Nat}\n\n";
  s += gen_def("add", ["a: Nat", "b: Nat"], "Nat", ["a", "b"],
    "  match a:\n    case Z{}:\n      b\n    case S{a}:\n      S{add(a, b)}");
  if (bench === "defs" || bench === "compute") {
    s += gen_def("mul", ["a: Nat", "+b: Nat"], "Nat", ["a", "b"],
      "  match a:\n    case Z{}:\n      Z{}\n    case S{a}:\n      add(b, mul(a, b))");
  }
  if (bench === "defs") {
    s += gen_def("dbl", ["+x: Nat"], "Nat", ["x"], "  add(x, x)");
    s += "type L:\n  Ln{}\n  Lc{head: Nat, tail: L}\n\n";
    s += gen_def("cat", ["xs: L", "ys: L"], "L", ["xs", "ys"],
      "  match xs:\n    case Ln{}:\n      ys\n    case Lc{h, t}:\n      Lc{h, cat(t, ys)}");
  }
  if (bench === "proofs") {
    s += gen_lemmas("Nat", "Z", "S", "add");
  }
  if (bench === "compute" || bench === "trees") {
    s += gen_def("n0", [], "Nat", [], "  Z{}");
    for (let k = 1; k <= (bench === "trees" ? 13 : 32); k++) {
      s += gen_def("n" + String(k), [], "Nat", [], "  S{n" + String(k - 1) + "()}");
    }
  }
  if (bench === "compute") {
    s += "type Duo<-A: Type, -B: Type>:\n  Duo{fst: A, snd: B}\n\n";
    s += gen_def("Tup", ["n: Nat"], "Type", ["n"],
      "  match n:\n    case Z{}:\n      Nat\n    case S{p}:\n      Duo<Nat, Tup(p)>");
  }
  if (bench === "trees") {
    s += "type Bool:\n  T{}\n  F{}\n\n";
    s += gen_def("and", ["a: Bool", "b: Bool"], "Bool", ["a", "b"],
      "  match a:\n    case T{}:\n      b\n    case F{}:\n      F{}");
    s += "type Tree:\n  L{}\n  N{lft: Tree, rgt: Tree}\n\n";
    s += gen_def("full", ["+n: Nat"], "Tree", ["n"],
      "  match n:\n    case Z{}:\n      L{}\n    case S{p}:\n      N{full(p), full(p)}");
    s += gen_def("mirror", ["t: Tree"], "Tree", ["t"],
      "  match t:\n    case L{}:\n      L{}\n    case N{l, r}:\n      N{mirror(r), mirror(l)}");
    s += gen_def("alltrue", ["t: Tree"], "Bool", ["t"],
      "  match t:\n    case L{}:\n      T{}\n    case N{l, r}:\n      and(alltrue(l), alltrue(r))");
  }
  if (bench === "generics") {
    s += "type Bx<-A: Type>:\n  Bx{val: A}\n\n";
    s += "type Pr<-A: Type, -B: Type>:\n  MkP{fst: A, snd: B}\n\n";
    s += "type Opt<-A: Type>:\n  No{}\n  Yes{val: A}\n\n";
    s += "type Lst<-A: Type>:\n  Nl{}\n  Cs{head: A, tail: Lst<A>}\n\n";
    s += gen_def("ubx", ["-A: Type", "b: Bx<A>"], "A", ["A", "b"],
      "  match b:\n    case Bx{x}:\n      x");
    s += gen_def("swp", ["-A: Type", "-B: Type", "p: Pr<A, B>"], "Pr<B, A>", ["A", "B", "p"],
      "  match p:\n    case MkP{a, b}:\n      MkP{b, a}");
    s += gen_def("pmap", ["-A: Type", "-B: Type", "-C: Type", "f: A -> B", "p: Pr<A, C>"], "Pr<B, C>", ["A", "B", "C", "f", "p"],
      "  match p:\n    case MkP{a, c}:\n      MkP{f(a), c}");
    s += gen_def("getor", ["-A: Type", "d: A", "v: Opt<A>"], "A", ["A", "d", "v"],
      "  match v:\n    case No{}:\n      d\n    case Yes{x}:\n      x");
    s += gen_def("omap", ["-A: Type", "-B: Type", "f: A -> B", "v: Opt<A>"], "Opt<B>", ["A", "B", "f", "v"],
      "  match v:\n    case No{}:\n      No{}\n    case Yes{x}:\n      Yes{f(x)}");
    s += gen_def("llen", ["-A: Type", "xs: Lst<A>"], "Nat", ["A", "xs"],
      "  match xs:\n    case Nl{}:\n      Z{}\n    case Cs{h, t}:\n      S{llen(A, t)}");
  }
  return s;
}

// gen_lemmas: the add algebra's lemma family -- zero, succ, comm --
// over a nat-shaped type. The prelude states it on the shared Nat and
// every proofs module of kind A restates it on a fresh algebra; the
// statements sit in rewrite direction (the term each proof eliminates
// on the right) and every rewrite spells its motive.
function gen_lemmas(T: string, Z: string, S: string, f: string): string {
  const z = Z + "{}";
  let s = "";
  s += gen_def(f + "_zero", ["a: " + T], "{" + f + "(a, " + z + ") == a : " + T + "}", ["a"],
    "  match a:\n    case " + z + ":\n      {==}\n    case " + S + "{a}:\n"
    + "      %" + f + "_zero(a) : {" + S + "{" + f + "(a, " + z + ")} == " + S + "{_} : " + T + "}\n      {==}");
  s += gen_def(f + "_succ", ["a: " + T, "-b: " + T], "{" + S + "{" + f + "(a, b)} == " + f + "(a, " + S + "{b}) : " + T + "}", ["a", "b"],
    "  match a:\n    case " + z + ":\n      {==}\n    case " + S + "{a}:\n"
    + "      %" + f + "_succ(a, b) : {" + S + "{" + S + "{" + f + "(a, b)}} == " + S + "{_} : " + T + "}\n      {==}");
  s += gen_def(f + "_comm", ["a: " + T, "+b: " + T], "{" + f + "(a, b) == " + f + "(b, a) : " + T + "}", ["a", "b"],
    "  match a:\n    case " + z + ":\n"
    + "      %" + f + "_zero(b) : {_ == " + f + "(b, " + z + ") : " + T + "}\n      {==}\n    case " + S + "{a}:\n"
    + "      %" + f + "_succ(b, a) : {" + S + "{" + f + "(a, b)} == _ : " + T + "}\n"
    + "      %" + f + "_comm(a, b) : {" + S + "{" + f + "(a, b)} == " + S + "{_} : " + T + "}\n      {==}");
  return s;
}

function gen_module(bench: Bench, i: number): string {
  const I = String(i);
  if (bench === "defs") {
    const p = plan_prev(i);
    if (i % 3 === 0) {
      return gen_def("fa" + I, ["x: Nat"], "Nat", ["x"],
        "  match x:\n    case Z{}:\n      " + p + "(S{Z{}})\n    case S{q}:\n      S{fa" + I + "(q)}")
        + gen_def("ga" + I, ["x: Nat", "y: Nat"], "Nat", ["x", "y"],
          "  add(fa" + I + "(x), " + p + "(y))");
    } else if (i % 3 === 1) {
      return gen_def("fb" + I, ["xs: L"], "L", ["xs"],
        "  match xs:\n    case Ln{}:\n      Ln{}\n    case Lc{h, t}:\n      Lc{" + p + "(h), fb" + I + "(t)}");
    } else {
      return gen_def("fc" + I, ["xs: L"], "Nat", ["xs"],
        "  match xs:\n    case Ln{}:\n      Z{}\n    case Lc{h, t}:\n      add(" + p + "(h), fc" + I + "(t))")
        + gen_def("gc" + I, ["+x: Nat"], "Nat", ["x"],
          "  fc" + I + "(Lc{x, Lc{" + p + "(x), Ln{}}})");
    }
  }
  if (bench === "proofs") {
    if (i % 3 === 0) {
      const T = "An" + I;
      return "type " + T + ":\n  Az" + I + "{}\n  As" + I + "{pred: " + T + "}\n\n"
        + gen_def("aadd" + I, ["a: " + T, "b: " + T], T, ["a", "b"],
          "  match a:\n    case Az" + I + "{}:\n      b\n    case As" + I + "{a}:\n      As" + I + "{aadd" + I + "(a, b)}")
        + gen_lemmas(T, "Az" + I, "As" + I, "aadd" + I);
    } else if (i % 3 === 1) {
      const T = "Bl" + I, N = "Bn" + I + "{}", C = "Bc" + I, cat = "bcat" + I, len = "blen" + I;
      const cxs = cat + "(" + cat + "(t, ys), zs)", cys = cat + "(t, " + cat + "(ys, zs))";
      return "type " + T + ":\n  Bn" + I + "{}\n  " + C + "{head: Nat, tail: " + T + "}\n\n"
        + gen_def(cat, ["xs: " + T, "ys: " + T], T, ["xs", "ys"],
          "  match xs:\n    case " + N + ":\n      ys\n    case " + C + "{h, t}:\n      " + C + "{h, " + cat + "(t, ys)}")
        + gen_def(len, ["xs: " + T], "Nat", ["xs"],
          "  match xs:\n    case " + N + ":\n      Z{}\n    case " + C + "{h, t}:\n      S{" + len + "(t)}")
        + gen_def(cat + "_nil", ["xs: " + T], "{" + cat + "(xs, " + N + ") == xs : " + T + "}", ["xs"],
          "  match xs:\n    case " + N + ":\n      {==}\n    case " + C + "{h, t}:\n"
          + "      %" + cat + "_nil(t) : {" + C + "{h, " + cat + "(t, " + N + ")} == " + C + "{h, _} : " + T + "}\n      {==}")
        + gen_def(cat + "_assoc", ["xs: " + T, "-ys: " + T, "-zs: " + T],
          "{" + cat + "(" + cat + "(xs, ys), zs) == " + cat + "(xs, " + cat + "(ys, zs)) : " + T + "}", ["xs", "ys", "zs"],
          "  match xs:\n    case " + N + ":\n      {==}\n    case " + C + "{h, t}:\n"
          + "      %" + cat + "_assoc(t, ys, zs) : {" + C + "{h, " + cxs + "} == " + C + "{h, _} : " + T + "}\n      {==}")
        + gen_def(len + "_cat", ["xs: " + T, "-ys: " + T],
          "{add(" + len + "(xs), " + len + "(ys)) == " + len + "(" + cat + "(xs, ys)) : Nat}", ["xs", "ys"],
          "  match xs:\n    case " + N + ":\n      {==}\n    case " + C + "{h, t}:\n"
          + "      %" + len + "_cat(t, ys) : {S{add(" + len + "(t), " + len + "(ys))} == S{_} : Nat}\n      {==}");
    } else {
      const T = "Ct" + I, L = "Cl" + I, N = "Cn" + I, mir = "cmir" + I, size = "csize" + I;
      const ml = mir + "(" + mir + "(l))", mr = mir + "(" + mir + "(r))";
      const sl = size + "(" + mir + "(l))", sr = size + "(" + mir + "(r))";
      return "type " + T + ":\n  " + L + "{val: Nat}\n  " + N + "{lft: " + T + ", rgt: " + T + "}\n\n"
        + gen_def(mir, ["t: " + T], T, ["t"],
          "  match t:\n    case " + L + "{v}:\n      " + L + "{v}\n    case " + N + "{l, r}:\n      " + N + "{" + mir + "(r), " + mir + "(l)}")
        + gen_def(size, ["t: " + T], "Nat", ["t"],
          "  match t:\n    case " + L + "{v}:\n      S{Z{}}\n    case " + N + "{l, r}:\n      add(" + size + "(l), " + size + "(r))")
        + gen_def(mir + "_mir", ["t: " + T], "{" + mir + "(" + mir + "(t)) == t : " + T + "}", ["t"],
          "  match t:\n    case " + L + "{v}:\n      {==}\n    case " + N + "{l, r}:\n"
          + "      %" + mir + "_mir(l) : {" + N + "{" + ml + ", " + mr + "} == " + N + "{_, r} : " + T + "}\n"
          + "      %" + mir + "_mir(r) : {" + N + "{" + ml + ", " + mr + "} == " + N + "{" + ml + ", _} : " + T + "}\n      {==}")
        + gen_def(size + "_mir", ["+t: " + T], "{" + size + "(" + mir + "(t)) == " + size + "(t) : Nat}", ["t"],
          "  match t:\n    case " + L + "{v}:\n      {==}\n    case " + N + "{l, r}:\n"
          + "      %" + size + "_mir(r) : {add(" + sr + ", " + sl + ") == add(" + size + "(l), _) : Nat}\n"
          + "      %" + size + "_mir(l) : {add(" + sr + ", " + sl + ") == add(_, " + sr + ") : Nat}\n"
          + "      %add_comm(" + sl + ", " + sr + ") : {_ == add(" + sl + ", " + sr + ") : Nat}\n      {==}");
    }
  }
  if (bench === "trees") {
    const { f, m } = plan_tree(i);
    const fm = "full(n" + String(m) + "())";
    return gen_def("ft" + I, [], "{alltrue(full(n" + String(f) + "())) == T{} : Bool}", [], "  {==}")
      + gen_def("mt" + I, [], "{mirror(" + fm + ") == " + fm + " : Tree}", [], "  {==}");
  }
  if (bench === "generics") {
    const K = "K" + I, Ka = "Ka" + I, Kb = "Kb" + I, d = plan_box(i);
    const nest = (j: number): string => (j === 0 ? K : "Bx<" + nest(j - 1) + ">");
    let bx = "x";
    for (let j = 0; j < d; j++) {
      bx = "Bx{" + bx + "}";
    }
    let ub = "b";
    for (let j = d - 1; j >= 0; j--) {
      ub = "ubx(" + nest(j) + ", " + ub + ")";
    }
    return "type " + K + ":\n  " + Ka + "{val: Nat}\n  " + Kb + "{}\n\n"
      + gen_def("bx" + I, ["x: " + K], nest(d), ["x"], "  " + bx)
      + gen_def("ub" + I, ["b: " + nest(d)], K, ["b"], "  " + ub)
      + gen_def("sw" + I, ["p: Pr<" + K + ", Nat>"], "Pr<Nat, " + K + ">", ["p"],
        "  swp(" + K + ", Nat, p)")
      + gen_def("pm" + I, ["p: Pr<Nat, " + K + ">"], "Pr<" + K + ", " + K + ">", ["p"],
        "  pmap(Nat, " + K + ", " + K + ", x => " + Ka + "{x}, p)")
      + gen_def("go" + I, ["v: Opt<" + K + ">"], K, ["v"],
        "  getor(" + K + ", " + Kb + "{}, v)")
      + gen_def("om" + I, ["v: Opt<Nat>"], "Opt<" + K + ">", ["v"],
        "  omap(Nat, " + K + ", x => " + Ka + "{x}, v)")
      + gen_def("ln" + I, ["xs: Lst<Pr<" + K + ", Nat>>"], "Nat", ["xs"],
        "  llen(Pr<" + K + ", Nat>, xs)")
      + gen_def("cs" + I, ["x: " + K, "y: " + K], "Lst<" + K + ">", ["x", "y"],
        "  Cs{x, Cs{y, Nl{}}}");
  }
  const { a, b, k } = plan_lit(i);
  let tv = "Z{}";
  for (let d = 0; d < k; d++) {
    tv = "Duo{Z{}, " + tv + "}";
  }
  const na = "n" + String(a) + "()", nb = "n" + String(b) + "()";
  return gen_def("cm" + I, [], "{mul(" + na + ", " + nb + ") == mul(" + nb + ", " + na + ") : Nat}", [], "  {==}")
    + gen_def("tv" + I, [], "Tup(n" + String(k) + "())", [], "  " + tv);
}

// Entry
// -----

export function gen(bench: Bench, n: number): string {
  let s = gen_prelude(bench);
  for (let i = 0; i < n; i++) {
    s += gen_module(bench, i);
  }
  return s;
}
