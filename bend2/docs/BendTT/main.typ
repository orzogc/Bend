// BendTT: An Affine Dependent Type Theory
// Build: typst compile main.typ ../../../docs/BendTT.pdf
//
// Solarized-light theme for the site build. Set solarized = false for a
// plain black-on-white document: colors revert and NOTHING else changes.
#let solarized = true

#let solbg   = if solarized { rgb("#FDF6E3") } else { white }
#let solhi   = if solarized { rgb("#EEE8D5") } else { luma(235) }
#let solfg   = if solarized { rgb("#073642") } else { black }
#let solblue = if solarized { rgb("#268BD2") } else { rgb("#1A45A8") }
#let solcyan = if solarized { rgb("#2AA198") } else { rgb("#1A45A8") }
#let solgreen = if solarized { rgb("#859900") } else { rgb("#1A6B27") }

// Page and text. Two columns; the title block spans both via a parent-
// scoped float.
#set page(
  paper: "us-letter",
  margin: (x: 54pt, top: 66pt, bottom: 60pt),
  columns: 2,
  fill: solbg,
  header: context {
    let p = counter(page).get().first()
    if p > 1 {
      set text(size: 8pt)
      if calc.even(p) [#p #h(1fr) Victor Taelin] else [BendTT: An Affine Dependent Type Theory #h(1fr) #p]
    }
  },
)
#set columns(gutter: 20pt)
#set text(font: "Libertinus Serif", size: 10pt, fill: solfg)
#set par(justify: true, leading: 0.52em, spacing: 0.52em, first-line-indent: 1em)
#show link: set text(fill: solcyan)
#show ref: set text(fill: solblue)
#show cite: set text(fill: solgreen)

// Headings, ACM-flavored.
#set heading(numbering: "1.1")
#show heading: it => {
  set text(fill: solfg)
  let big = it.level == 1
  block(above: if big { 1.4em } else { 1.2em }, below: if big { 0.7em } else { 0.6em },
    text(size: if big { 12pt } else { 10pt }, weight: "bold", {
      if it.numbering != none {
        counter(heading).display(it.numbering)
        h(if big { 0.9em } else { 0.7em })
      }
      it.body
    }))
}

// Monospace names (theorems, file names).
#let co(body) = text(font: "DejaVu Sans Mono", size: 0.82em, body)

// Code blocks: shaded, monospace, unbreakable.
#show raw.where(block: true): it => block(
  breakable: false,
  fill: solhi, inset: 6pt, radius: 2pt, width: 100%,
  text(font: "DejaVu Sans Mono", size: 7.5pt, it))
#show raw.where(block: false): it => box(
  fill: solhi, inset: (x: 2pt), outset: (y: 2pt), radius: 1pt,
  text(font: "DejaVu Sans Mono", size: 0.82em, it))

// Notation.
#let Ty = $sans("Type")$
#let Da = $sans("Data")$
#let Qn = $sans("Quant")$
#let Kd(g) = $sans("Kind")(#g)$
#let tri = sym.triangle.stroked.small.r
#let uz = sym.nothing
#let fam(D, r) = $#D^#r$
#let JJ(G, q, t, T, p) = $#G scripts(tack.r)_#q #t : #T thin tri thin #p$

// An inference rule: premises over a line over the conclusion.
#let rule(concl, ..prems) = {
  let ps = prems.pos()
  box(grid(
    align: center + bottom,
    inset: (x: 0.35em, y: 0.3em),
    ..if ps.len() > 0 { (ps.join(h(1.4em)),) } else { () },
    grid.hline(stroke: 0.5pt + solfg),
    concl,
  ))
}

// A block of rules: each argument is one row (an array of rules).
#let rules(..rows) = stack(spacing: 1.1em, ..rows.pos().map(r =>
  align(center, box(r.join(h(1.7em))))))

#set figure(placement: top, gap: 1em)
#show figure.caption: it => {
  set text(size: 9pt)
  set par(first-line-indent: 0em)
  align(left)[*#it.supplement #context it.counter.display(it.numbering).* #it.body]
}

// ---------------------------------------------------------------------
// Title block, full width.

#place(top + center, scope: "parent", float: true, {
  set par(first-line-indent: 0em)
  v(10pt)
  text(size: 17.3pt, weight: "bold")[BendTT: An Affine Dependent Type Theory]
  v(2pt)
  text(size: 11pt)[Victor Taelin]
  linebreak()
  text(size: 10pt)[Higher Order Company]
  linebreak()
  text(size: 10pt)[Rio de Janeiro, Brazil]
  linebreak()
  text(size: 10pt, link("mailto:taelin@higherorderco.com", "taelin@higherorderco.com"))
  v(8pt)
  align(left, block(stroke: 0.5pt + solfg, inset: 6pt, width: 100%, {
    set text(size: 8pt)
    set par(justify: true)
    align(left)[#smallcaps[AI Disclosure.] Bend and BendTT were designed by
    the human author. This paper was written by Claude Fable 5.1 from the
    author's code and design choices, and reviewed by the author. The Lean
    mechanization was human-specified, AI-proven, and checked by Lean.]
  }))
  v(2pt)
})

// ---------------------------------------------------------------------

#heading(numbering: none, outlined: false)[Abstract]

BendTT is the type theory of the Bend programming language. It has one
sort with #Ty : #Ty, no universe hierarchy, datatypes with no
positivity restriction, and it is consistent. The reason is a usage
discipline: a value is consumed at most once unless the _kind_ of its
type says otherwise. Every type has a kind $#Kd($q$)$ over a quantity
$q$; a binder marked `+` may be consumed any number of times, and it
forms only when its type's kind is $#Da = #Kd($omega$)$. A function type
is never #Da, and a datatype earns #Da at every constructor. So no
closure is ever copied, and every known paradox of #Ty : #Ty or of
negative datatypes copies a closure. Recursion passes one syntactic
descent over the definition's own case tree. Erased code is free and
may diverge; nothing promotes it to live. There is no unification and
there are no tactics: a claim is an `assert`, a proof is the `def` that
fills it, and the match is the eliminator. We state the calculus, show
how each attack dies, and describe a Lean 4 mechanization of the
all-affine fragment.

= Introduction <sec:intro>

Bend is a functional language with dependent types and a parallel
runtime @bendrt2026. Its checker implements a small type theory, BendTT,
and this paper is about the one thing in it that is not standard: BendTT
keeps #Ty : #Ty, impredicative quantification and recursive datatypes
with negative occurrences, and it stays consistent.

The engines of the classical paradoxes all copy a function: Girard's
paradox and its Hurkens form apply a function-typed value to itself
@girard1972 @hurkens1995, and Curry's paradox through a negative
datatype applies a node's field to a copy of the node @curry1942.
Logics without contraction admit naive comprehension @grishin1982
@girard1998 @terui2004. BendTT carries that idea into a dependent type
theory, where it replaces the universe hierarchy and the positivity
check: a live variable is consumed at most once, and a function is
never an exception.

Affinity alone would make the language useless: a proof feeds one
hypothesis to the induction hypothesis and to a lemma. Bend restores
reuse through the kind of a type. A binder may be marked `+`, and then
its type must have kind #Da. A datatype declares its kind and the
checker earns it at every constructor; a function type is #Ty\; a
proposition is #Da because its evidence is erased. The license to copy
is a property of a _type_, never a proof carried by a _term_: there is
no modality, no copy class, no clone function. This inverts
quantitative type theory @mcbride2016 @atkey2018 @brady2021, where
$omega$ is the ordinary binder and consistency comes from the universe
hierarchy the theory keeps. Here $1$ is the ordinary binder and $omega$
is a permission a type earns. One rule shows the difference: an
argument that enters a `+` binder is counted once, where QTT scales its
usage by $omega$; @sec:price says what that costs. Everything else is
chosen to be cheap: one bidirectional pass @dunfieldkrishnaswami2021
with a usage counter per binder, no unification, one syntactic test per
self-call, and a dead fragment that costs nothing, may diverge, and is
erased before the runtime, which moves every value by default.

= The Calculus <sec:calculus>

BendTT is one file of TypeScript, `bend2/bend.ts`: parser, printer,
pattern flattener, evaluator and checker. Evaluation, conversion, typing
and validation are about a thousand lines over one `Term` type whose
binders are host functions @pfenningelliott1988. Every rule below is a
derivation comment beside its case in that file.

== Terms, Quantities, Kinds <sec:terms>

#figure(kind: image, supplement: [Figure], caption: [Terms, in the
surface syntax. $q$ is a quantity sigil: `-` for $0$, none for $1$, `+`
for $omega$. A family $D$ carries an unspellable set $r$ of
already-matched constructors. Kinds are terms: $#Ty = #Kd($&1$)$ and
$#Da = #Kd($&2$)$.], {
  set text(size: 9.5pt)
  grid(
    columns: (auto, auto),
    align: (left, left),
    column-gutter: 1.6em,
    row-gutter: 0.45em,
    grid.cell(colspan: 2, $t, A, B ::=$),
    [`x`, `k`], [variable, reference to a definition],
    [`@q x: A -> B`], [function type],
    [`x => f`, `f(a)`], [abstraction, application],
    [`q x = v; b`], [let (not recursive)],
    [`Kind(g)`, `Quant`], [a kind, the sort of quantities],
    [`&0 &1 &2`, `g <&> h`], [quantity literals, the meet],
    [`D<p..>`, `C{a..}`], [family instance, constructor],
    [`\{C: h; m}`, `\{}`], [match: peel one constructor; empty match],
    [`{a == b : T}`, `{==}`], [propositional equality, reflexivity],
    [`%e : P; f`], [rewrite by $e$ through motive $P$],
    [`{x : T}`, `?name`], [annotation, hole],
  )
}) <fig:terms>

@fig:terms lists the term formers; types are terms. A binder carries a
quantity $q in {0, 1, omega}$, spelled `-x`, `x` and `+x`: erased,
affine, reusable. Every type has a _kind_ $#Kd($g$)$ where $g$ is a
quantity term: a literal, a variable of the sort #Qn, or a meet
$g inter.sq h$ (surface `<&>`). Conversion orders kinds by the quantity
order, $#Kd($g$) lt.eq #Kd($h$)$ when $h lt.eq g$: #Da fits every kind,
every kind fits #Ty, a kind fits a meet when it fits either side, a
meet fits a kind only when both its sides do, and a stuck quantity
fits only itself. The meet reduces only when forced: $omega$ is its identity, $0$
absorbs, two literals meet, and a stuck side stays stuck, so no
declaration order can decide a meet early.

A _book_ is an ordered list of declarations. `type D<p..> is Kind(G):`
declares a family with parameters and a kind, then its constructors,
each a telescope of fields tipped at `D<p..>`. `assert k: T` declares a
name at a closed type and a later `def k(x..):` fills it. Until its fill
a name is an _axiom_: it may appear in types and other dead positions,
and live code may not consume it. A definition may reference itself
only through the descent rule of @sec:descent, and never a later name,
so the reference graph is acyclic and mutual recursion cannot split a
loop across two definitions. The flattener compiles `match`/`case`
blocks into a case tree of one-constructor peels @maranget2008,
uncovered rows becoming the empty match. A match scrutinizes only a
parameter or a field bound by an enclosing match; a computed scrutinee
is an error that says to give it its own definition (@sec:proofs).

== Reduction and Conversion <sec:reduction>

Evaluation is weak head reduction. A lambda applied steps; a let
substitutes; a reference unfolds only when its spine reaches its
declared arity and it has a body, so an axiom and an underapplied
definition are stuck values; a match meeting its constructor passes the
fields to the arm, and any other constructor falls whole to the default
$m$, whose domain records the peeled constructor in $r$; a rewrite
sheds when its evidence reaches `{==}`. When a definition's match
sticks on a variable, the evaluator answers the definition applied to
that variable, not the exposed case tree, so goals stay in the
vocabulary of the source; this refolding is what lets an induction
hypothesis match a goal (@sec:proofs).

Conversion $A lt.eq B$ is reduce-and-compare at every node, up to
$eta$ for functions, and it is a preorder, not an equality: directional
at kinds and at match residuals (more constructors peeled fits fewer),
domains of a function type swapped, quantities exact, and every part
that flows both ways (an argument, a parameter, a field, an equation
endpoint) compared as a symmetric $A equiv B$. Reflexivity uses
$equiv$: `{==}` does not prove `{Data == Type : Type}`, which J could
transport into a cast. Conversion may diverge on dead code; a hang
accepts nothing (@sec:price).

== Typing <sec:typing>

#figure(placement: top, scope: "parent", caption: [Typing, the rules
that differ from the textbook. #JJ($Gamma$, $q$, $t$, $T$, $pi$) reads:
under the book and context $Gamma$, at demand $q in {0, 1}$, $t$ has
type $T$ and consumes $pi$, a map from variables to quantities. A dot is
a measure the rule drops. $pi + pi'$ adds pointwise ($1 + 1 = omega$),
$pi union.sq pi'$ takes the pointwise maximum, $q' tri q$ is $0$ when
$q' = 0$ and $q$ otherwise, and $r dot q'$ is $0$, $q'$ or $q' + q'$ as
$r$ is $0$, $1$ or $omega$. In #smallcaps[ref], a live reference needs a
filled or native body, and a self-reference needs its pending spine to
descend (@sec:descent). In #smallcaps[mat], $F_i$ and $q_i$ are the
constructor's fields at the family's parameters. The rest: a
constructor $C{a_1...}$ at $#fam($D$, $r$) thin p_1...$ with $C in.not r$,
and a family instance $D thin p_1...$ at $#Kd($G[p_1...]$)$, check each
argument at the gate like #smallcaps[app]\; a let $q' x = v"; " b$ is
$(lambda x. thin b) thin v$ with $v$ inferred and its type checked dead
at $#Kd($q'$)$; ${a == b : A}$ : #Da with all three parts dead, and
${==}$ proves it when $a equiv b$; $#Kd($g$)$ : #Ty with $g$ dead at
#Qn, and $g inter.sq h$ : #Qn checks both sides at the ambient demand
and adds their measures.],
{
  set text(size: 9.5pt)
  let gate(a, b) = $#a thin tri thin #b$
  rules(
    (rule(JJ($Gamma$, $q$, $x$, $A$, $x^q$), $(x : q' A) in Gamma$),
     rule(JJ($Gamma$, $q$, $k$, $T$, $uz$), $"book"(k) : T$, $q = 1 arrow.r.double k "filled, self-call descends"$),
     rule(JJ($Gamma$, $q$, $forall^(q') x:A. thin B$, $#Ty$, $uz$),
       JJ($Gamma$, $0$, $A$, Kd($q'$), $dot$), JJ($Gamma, x : q' A$, $0$, $B$, $#Ty$, $dot$))),
    (rule(JJ($Gamma$, $q$, $lambda x. thin f$, $forall^(q') x:A. thin B$, $pi backslash x$),
       JJ($Gamma, x : q' A$, $q$, $f$, $B$, $pi$), $pi(x) lt.eq q'$),
     rule(JJ($Gamma$, $q$, $f thin a$, $B[x := a]$, $pi + pi'$),
       JJ($Gamma$, $q$, $f$, $forall^(q') x:A. thin B$, $pi$),
       JJ($Gamma$, gate($q'$, $q$), $a$, $A$, $pi'$)),
     rule(JJ($Gamma$, $q$, $t$, $T$, $pi$), JJ($Gamma$, $q$, $t$, $A$, $pi$), $A lt.eq T$)),
    (rule(JJ($Gamma$, $q$, $lambda{C: thin h"; " m}$, $forall^(q') s : #fam($D$, $r$) thin p_1.... thin P$, $pi union.sq pi'$),
       $C in.not r$, $q = 1 arrow.r.double q' eq.not 0$,
       JJ($Gamma$, $q$, $h$, $forall^(q_i dot q') x_i : F_i. thin P thin (C{x_1...})$, $pi$),
       JJ($Gamma$, $q$, $m$, $forall^(q') s : #fam($D$, $r union {C}$) thin p_1.... thin P$, $pi'$)),
     rule(JJ($Gamma$, $q$, $lambda{}$, $forall^(q') s : #fam($D$, $r$) thin p_1.... thin P$, $uz$),
       $q = 1 arrow.r.double q' eq.not 0$,
       $#fam($D$, $r$) "has no constructor left, or a live" (x : E) in Gamma "with" E "empty"$)),
    (rule(JJ($Gamma$, $q$, $% e : P"; " f$, $T$, $pi + pi'$),
       JJ($Gamma$, $q$, $e$, ${a == b : A}$, $pi$),
       JJ($Gamma$, $0$, $P$, $forall x:A. thin {a == x : A} arrow.r #Ty$, $dot$),
       $P thin b thin e lt.eq T$,
       JJ($Gamma$, $q$, $f$, $P thin a thin {==}$, $pi'$)),),
  )
}) <fig:typing>

@fig:typing gives the rules. Inference synthesizes, checking pushes a
goal into the introduction forms, and the two meet at conversion. Both
directions carry a _demand_ $q$: $0$ checks a term dead, $1$ live.
There is no demand $omega$: a term checked at demand $omega$ would let a
binder inside it contract, and Atkey shows this also breaks
substitution @atkey2018. Sequential premises add their measures, the
arms of a match join since one of them runs, and a binder validates
$pi(x) lt.eq q'$ when it closes: two live uses of an affine binder
saturate to $omega$ and fail there. A reference costs nothing: code is
free.

_The dead fragment is free._ Types in premises, binder domains,
equality endpoints and rewrite motives check at demand $0$, where the
measure is dropped. A dead term may mention consumed variables, may
diverge, and may inhabit `Empty`. No rule coerces dead to live: an
erased binder's uses count at $0$, and a match on an erased scrutinee
is refused in a live region.

_Reuse is gated, not scaled._ An argument to a binder of quantity $q'$
checks at demand $q' tri q$, dead if the binder is erased and the
ambient demand otherwise, and its measure adds once. So a value bound
once may enter a `+` binder, and the callee copies it: _certify-once_.
It is licensed because the `+` binder's domain checked against #Da when
the function type formed, and a #Da value holds nothing affine
(@sec:kinds). A match hands each field out at the field's quantity
times the scrutinee's, so a `+` scrutinee makes its plain fields
reusable.

_Matching is consumption._ A match is a value of function type, and
applying it consumes the scrutinee. The arm receives the fields at a
goal specialized to the rebuilt constructor, $P thin (C{x_1...})$:
dependent elimination with no generated eliminator and no unification.
The default receives the scrutinee with $C$ peeled onto $r$, and the
empty match closes the chain when no constructor remains, or when a
_live_ binder in scope has an emptied type; an erased one proves
nothing, since dead code inhabits it.

_Equality is the J axiom with an explicit motive._ From
$e : {a == b : A}$, a rewrite maps a goal $P thin b thin e$ to the
obligation $P thin a thin {==}$; the programmer writes $P$, and it
checks dead. The evidence runs, so it checks at the ambient demand. An
equation is #Da: its evidence is erased, and a closed live proof
normalizes to `{==}`, so copying it copies nothing.

== Kinds Are Earned <sec:kinds>

A `+` binder forms only over a #Da type, so the security of the theory
rests on what may be #Da. The rules assign kinds by shape: a function
type is #Ty, because a closure captures; an equation is #Da\; a family
has the kind it declares, $#Kd($G$)$ over its parameters. The book
validator earns the declaration: for each constructor it walks the
telescope, parameters then fields, in the real constructor context, and
checks a binder of quantity $q$ against $#Kd($q$)$ and a _live_ field
against the declared $#Kd($G$)$; the tip must be the family applied to
its own parameters, in order. From the base library:

```
type List<a, -A: Kind(a)> is Kind(a):
  Nil{}
  Con{head: A, tail: List<a, A>}

type Sigma<a, b, -A: Kind(a),
           -B: @-x: A -> Kind(b)>
  is Kind(a <&> b):
  Tuple{fst: A, snd: B(fst)}
```

A list is as reusable as its element; a pair is reusable when both
halves are. `Nat`, `Bool`, `U32` and `String` are #Da\; `Array`, the IO
handles and the effect type are #Ty. A recursive occurrence is assumed
at the declared kind, with no fixed point: a live value is a finite
tree, so the invariant that a #Da value holds nothing affine follows by
induction on the value. Values never weaken with their kinds:
`List<&2, Nat>` and `List<&1, Nat>` are different types. Generic code
takes the quantity as an erased parameter (`forall -a: Quant`), under
which `+` is refused, since `Kind(a)` does not reduce to #Da\; the
license appears only after instantiation.

== Descent <sec:descent>

Self-reference passes one test, run against the definition's own case
tree. Walking the body, the checker rebuilds the definition's left-hand
side: a lambda binds the next _column_, a match peels the current column
into a constructor of fresh field columns. At a live self-reference the
pending arguments compare against the columns left to right, erased
columns skipped: each must equal its column until one is a _strict
subterm_ of it, the same constructor with a strictly smaller field, or a
term sitting inside one of the pattern's fields. Arguments past the
decreasing one are free, so Ackermann passes: its inner call shrinks the
first column, its outer call keeps it and shrinks the second. The
comparison sees through lets, so `+p = p0` keeps `p` a subterm. No sizes
are computed: this is a minimal member of the structural-recursion
family @gimenez1994 @abelaltenkirch2002, chosen because it is one pass
and trivial to audit. Dead demands skip the test, so a type may recurse
freely; that is what makes `R = @-x: R -> Empty` definable, and it is
harmless because dead code never runs.

= Why It Is Consistent <sec:consistency>

In a functional language there are two ways to loop: self-application
and recursion. Descent closes the second. This section is about the
first, and about why the copy license cannot be forged. Every example is
a test in the repository, and the messages are the checker's own.

== Self-Application Dies at the Counter

$omega = (lambda x. thin x thin x)(lambda x. thin x thin x)$ uses its
binder twice, so the measure saturates to $omega$, and a plain binder
refuses it. The only binder that admits two uses is `+x`, and `+x` forms
only over a #Da type. No function type is #Da:

```
assert dupf:
  forall +f: Nat -> Nat
  Nat

- expected : Data
- observed : Type
```

Hurkens' paradox @hurkens1995 is twenty definitions long in Bend and
typechecks up to `tauinner`, the first place a function-typed variable
is used twice; it dies there with `f (consumed more than once)`.
Impredicativity and #Ty : #Ty do no harm on their own.

== Negative Types Are Legal, and Harmless

There is no positivity check. A HOAS-style term type is a fine
declaration, and its evaluator is a fine program:

```
type Trm is Type:
  Lam{f: Trm -> Trm}
  Num{n: U32}

def app(t: Trm, x: Trm) -> Trm:
  match t:
    case Lam{f}:
      f(x)
    case Num{n}:
      Num{n}
```

Curry's engine, `omega(Lam{f}) = f(Lam{f})`, needs the field `f` twice
and dies at the counter like `dupf`. A `Data` declaration cannot hold
the function either: `MkBox{f: Nat -> Nat}` under `type Box is Data`
fails its field with `expected Data, observed Type`. So a negative field
sits only in an affine type, where it is used at most once, and a value
of a negative type is at worst an inert closure.

== The License Cannot Be Forged

Every attack we know of tries to obtain #Da for something affine. The
_copy paradox_ is the sharpest. In a theory whose contractible types
are reusable, the type of copies of $x$, `&y: T -> {x == y : T}`, has
the single inhabitant `(x, {==})`, and copying that pair copies $x$.
Here it must be a datatype with a declared kind, and its live field
`y: T` has kind #Ty, which #Da does not admit: the declaration fails at
its constructor. A _constructor-local quantity_ fails the same way: a
constructor that binds its own `L: Quant` and stores a field at
`Kind(L)` is refused under `Data`, since a local `L` is never assumed
to be `&2`. A _dead hypothesis_ licenses nothing: an erased `-e: Empty`
or `-c: Copiable(T)` in scope may never be supplied, and a `+` needs a
kind that _reduces_ to #Da, which a type stuck on dead evidence never
does. A _quantity equation_ `{&1 == &2 : Quant}` is a legal type with
no live proof, and a rewrite through it yields a value whose type is a
stuck rewrite: nothing applies it. The _meet_ charges both operands, so
`q <&> &2` is not a free copy of `q`. A _quantity cast_ fails at
conversion: `@x: A -> B` and `@-x: A -> B` are different types. A _base
name_ cannot be refilled by a later file, and a _foreign fill_ must
answer the base library's `IO` type, so no import line can spell a
duplicator. A _circular fill_ of `Forge(T): Data` is a live self-call
with no shrinking column, refused by descent.

== The Claims, and Their Price <sec:price>

For a book that validates, the theory claims subject reduction,
progress, weak normalization of closed live terms, and no closed live
inhabitant of `Empty`. The last three are stated at the live demand
because dead code may rest on an axiom, diverge, or inhabit `Empty` by
design: erased code is specification, not proof. Conversion, and so the
checker, is a semi-decision procedure, as it already is in theories
with divergent types @coquand1991: a hang is "inconclusive", never
"accepted". The stance is soundness on accept, not checker totality, in
the line of NuPRL and Zombie @constablesmith1987 @casinghino2014.

Certify-once has a price. Term-substitution reduction does not preserve
the usage measure: unfold `f(+x)` at `f(y)` and `y` counts twice under
its plain binder. So subject reduction for usage is claimed for weak
by-value reduction of closed terms, the only reduction the machine
performs: when `f` unfolds, `y` is a value whose resources were consumed
once, and the copy is #Da, which owns nothing. Three invariants outside
the checker carry this. No pass duplicates a term: the evaluator shares
every argument, let value and field in a memoized cell, and the
compiler is strict. A type with runtime ownership (a file, a socket, an
array) is declared #Ty, never #Da\; this is a property of the base
library, not a rule. A compiler may drop a copy the source spelled,
never add one @bendrt2026. QTT avoids the question by scaling the
argument's measure, which it can afford because $omega$ is its default;
with $1$ as the default, scaling would leave only closed data
reusable.

One escape hatch exists and is always disclosed. A definition marked
`@unsafe` skips descent and forms its `+` binders at any kind; the
checker reports every book that uses one, so a clean report means none
of the claims above is waived.

= Proofs Without Tactics <sec:proofs>

A claim is an `assert` and a proof is the `def` that fills it. `forall`
folds to a function type, `exists` to a dependent pair, `where` packs a
hypothesis onto a binder; `{a != b : T}` is a function into `Empty`.
An unfilled claim is a `TODO`: the checker counts it, the compiler
refuses it, and no unproven name reaches live code.

The match is the eliminator. Matching a parameter refines the claim in
each arm: the goal in the `1n+p` arm of a claim about `a` is the claim
at `1n+p`, evaluated, with stuck self-calls refolded to source form.
The induction hypothesis is the recursive call, and descent makes it
valid. There is no unification, and there are no metavariables,
implicit arguments or tactics: the assert of a helper _is_ the motive
of its match, which is why a computed scrutinee must go to its own
definition. Rewriting is J with the motive written out: given
`e : {a == b : T}`, the motive marks with `_` the places where `b`
stands, the goal must be the motive at `b`, and the body proves it at
`a`. So one states an equation with the term to eliminate on the
right. The whole idiom, checked by Bend:

```
def add(a: Nat, b: Nat) -> Nat:
  match a:
    case 0n:
      b
    case 1n+p:
      1n+add(p, b)

assert zero:
  forall a: Nat
  {a == add(a, 0n) : Nat}

def zero(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %zero(p) : {1n+p == 1n+_ : Nat}
      {==}

assert comm:
  forall  a: Nat
  forall +b: Nat
  {add(a, b) == add(b, a) : Nat}

def comm(a, b):
  match a:
    case 0n:
      zero(b)
    case 1n+p:
      %succ(b, p) : {1n+add(p, b) == _ : Nat}
      %comm(p, b) : {1n+add(p, b) == 1n+_ : Nat}
      {==}
```

In the successor arm of `zero` the goal evaluates to
`{1n+p == 1n+add(p, 0n)}`; the hypothesis `zero(p)` proves
`{p == add(p, 0n)}`, and the rewrite folds `add(p, 0n)` back into `p`,
leaving reflexivity. `comm` needs `b` twice, in the lemma `succ`
(`{1n+add(a, b) == add(a, 1n+b)}`, by the same induction) and in the
hypothesis; `Nat` is #Da, so `+b` licenses it. This is the idiom that
affinity alone forbids and the kind restores. Statements are free: at
demand $0$ a theorem may quantify over functions and repeat variables
at will. Affinity constrains what runs, never what is said.

= Erasure and the Runtime <sec:erasure>

The checker elaborates as it checks: it returns the term with every
node annotated by its type, and stores it for the compiler @bendrt2026.
Erased binders, arguments and fields drop. Kinds, quantities, function
types, family instances, equations and reflexivity become nothing; a
rewrite compiles to its body. What survives is the live fragment:
constructors with their live fields, lambdas over live binders,
matches, and calls. A closed live proof is `{==}` and vanishes whole.

The usage discipline then pays twice. The checker needed only a counter
per binder, threaded through the one pass it already makes. The runtime
needs no garbage collector: a value has one owner, so a match frees its
scrutinee as it opens it, arrays update in place, and a forked task
carries no lock. Where a `+` licensed reuse, the compiler places a
counted share or a borrow, and nowhere else. Reuse was derived from the
kind of a type and never proved by a term, so the runtime never runs a
copy the source did not spell.

= The Mechanization <sec:mech>

`bend2/bend.lean` mechanizes the core in Lean 4 @demoura2021, checked
with a plain `lean` invocation: about twenty thousand lines, no `sorry`,
no axiom declarations. Its first part is a specification that mirrors
`bend.ts` section by section, in de Bruijn syntax; its second part
proves the claims of @tab:claims.

#figure(caption: [Claims and theorems in `bend.lean`, for the
all-affine fragment.], {
  set text(size: 9pt)
  table(
    columns: (auto, auto),
    align: (left, left),
    stroke: none,
    table.hline(stroke: 0.6pt + solfg),
    table.header([Claim], [Theorem]),
    table.hline(stroke: 0.4pt + solfg),
    [Confluence], co[church_rosser_holds],
    [Subject reduction (weak, measure $lt.eq$)], co[subject_reduction_holds],
    [Progress (live)], co[progress_holds],
    [Normalization (weak, live)], co[normalization_holds],
    [Consistency (live)], co[consistency_holds],
    [The dead boundary, as a witness], co[consistency_none_boundary],
    table.hline(stroke: 0.6pt + solfg),
  )
}) <tab:claims>

The scope is exact and narrower than the language. The file mechanizes
the _all-affine_ fragment: no `+` binder, no #Da, no kinds and no meet;
$omega$ exists only inside the measure, where it is always a violation.
The Data layer of @sec:kinds, certify-once included, is argued in
@sec:price and audited by the tests; it is not a theorem. The file also
lists the smaller places where the checker is more permissive than the
model, such as the empty match under a live emptied binder and descent
skipped at dead demand. Normalization and consistency are proven with
recursive definitions included, by a Dershowitz--Manna multiset measure
@dershowitzmanna1979 over pending references. The boundary is a
witness, not a caveat: in a well-formed book with a negative type,
Curry's self-application term checks _dead_ at an empty family
(`dead_omega_check`) and provably never live. The specification was
written and reviewed by humans; the proofs were written by an AI system
and are checked by Lean: trust the checker, audit the statements.

= Discussion <sec:discussion>

_What affinity takes away._ Contraction on closures. The standard
`map`, whose function is applied once per element, is ill-typed: `f`
would need `+`, and a function type is never #Da. Code is free, so a
top-level definition may be called any number of times and maps
specialized to a named function cover the common cases; but the
closure-heavy style of Haskell does not transfer. Bend accepts this on
purpose: the runtime wants the same restriction @bendrt2026.

_What it keeps._ On the program side the baseline is C: first-order
data, machine words, arrays updated in place, code called by name. That
fragment passes through affinity untouched. On the proof side the reach
is larger: statements are erased and cost nothing, and live proofs draw
their reuse from #Da, which is where induction lives. Nothing prevents
adding a universe hierarchy later; but Bend needs affinity anyway, and
#Ty : #Ty buys impredicative encodings and type-computing definitions
no predicative hierarchy accepts.

_Related work._ Linear and dependent types meet in LLF
@cervesatopfenning2002 and in @krishnaswami2015; the quantitative line
@mcbride2016 @atkey2018 @brady2021 and the graded line @moon2021
@abel2023graded are closest in mechanism, and all keep a universe
hierarchy. Recent linear dependent theories still add universe levels
to avoid Girard's paradox @fuxi2023, or reach an impredicative universe
through a model rather than #Ty : #Ty @speight2026. To our knowledge
none uses the absence of contraction _for_ consistency. Among
mechanized metatheories of practical kernels @abel2018 @sozeau2020
@carneiro2024, ours proves normalization rather than assuming it.

_Limitations._ The consistency result is syntactic, relative to Lean's
own foundation, with no semantic model. The Data layer is argued and
audited, not mechanized; formalizing it is the next planned extension.
Equality is intensional, with no extensionality principle. And the
theorems are about the calculus, not the code.

BendTT buys consistency with affinity instead of a universe hierarchy,
earns reuse from the kind of a type instead of a proof, checks recursion
with a descent rule an auditor can read in an afternoon, and erases
everything that does not run. Nothing in it is difficult, and that is
the point.

#{
  show heading: set text(size: 12pt)
  set text(size: 8pt)
  bibliography("refs.bib",
    title: [References],
    style: "association-for-computing-machinery")
}
