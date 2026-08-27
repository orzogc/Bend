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
// scoped float, the native mechanism for full-width front matter.
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
  if it.level == 1 {
    block(above: 1.4em, below: 0.7em, text(size: 12pt, weight: "bold", {
      if it.numbering != none {
        counter(heading).display(it.numbering)
        h(0.9em)
      }
      it.body
    }))
  } else {
    block(above: 1.2em, below: 0.6em, text(size: 10pt, weight: "bold", {
      if it.numbering != none {
        counter(heading).display(it.numbering)
        h(0.7em)
      }
      it.body
    }))
  }
}

// Inline term syntax, boxed like `code`.
#let ic(body) = box(fill: solhi, inset: (x: 2pt), outset: (y: 2pt), radius: 1pt, body)

// Monospace names (Lean theorems, file names, surface syntax).
#let co(body) = text(font: "DejaVu Sans Mono", size: 0.82em, body)

// Code blocks: shaded, monospace, unbreakable.
#show raw.where(block: true): it => block(
  breakable: false,
  fill: solhi, inset: 6pt, radius: 2pt, width: 100%,
  text(font: "DejaVu Sans Mono", size: 7.7pt, it))
#show raw.where(block: false): it => box(
  fill: solhi, inset: (x: 2pt), outset: (y: 2pt), radius: 1pt,
  text(font: "DejaVu Sans Mono", size: 0.82em, it))

// Notation.
#let Ty = $sans("Type")$
#let conv = sym.tilde.eq
#let stepto = sym.arrow.r.long
#let arr(q) = $scripts(arrow.r)^#q$
#let tri = sym.triangle.stroked.small.r
#let uz = sym.nothing
#let fam(D, r) = $#D^#r$

// An inference rule: premises over a line over the conclusion. The line
// spans the wider of the two, with symmetric padding on both sides of it.
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

// Figures: top-anchored floats, with a caption gap wider than a text line.
#set figure(placement: top, gap: 1em)

// Figure captions, ACM-flavored: bold label, period, left-justified.
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
    the human author. This paper was written by Claude Fable 5, based on
    the author's code and design choices, and thoroughly reviewed by the
    author. The Lean formalization was human-specified, AI-proven, and
    checked by Lean.]
  }))
  v(2pt)
})

// ---------------------------------------------------------------------

#heading(numbering: none, outlined: false)[Abstract]

BendTT is the proof kernel of the Bend programming language: a
dependent type theory with a single sort satisfying #Ty : #Ty, no
universe hierarchy, and no positivity restriction on its recursive
datatypes. It is nevertheless consistent, because the calculus is
completely affine: no live value may be consumed more than once,
duplication of any kind is unwritable in the kernel, and every
classical paradox needs to duplicate a function at some point.
Recursion is checked by a lexicographic strict-subterm descent
over each definition's own case tree, and only the live level must
terminate: dead code and types may diverge. Duplication returns at
the surface as a grade on kinds: a datatype declares whether its
values are reusable, the checker verifies the claim at every
constructor, and only a value of a reusable kind may be consumed
freely; the kernel itself has no such rule. Everything else is
standard, by design. We define the calculus, argue
informally that it terminates, and describe a Lean 4 mechanization
of its metatheory: confluence, subject reduction, progress, weak
normalization, and consistency, with no unproven obligations. This
is a working document and will evolve with the language.

= Introduction <sec:intro>

BendTT is the proof kernel of Bend, a programming language built
around dependent types, affine values, and a parallel runtime.
This paper defines the kernel, explains why it is consistent, and
points to the mechanized proof.

The paper contributes no new machinery to type theory, and is not
meant to. Its purpose is to document the theory behind Bend, as a
reference for users and auditors. Nearly every ingredient is
deliberately standard: user-declared datatype families with
dependent elimination; plain small-step reduction; intensional
equality with rewriting. The exception, and the only part a type
theorist may find surprising, is that BendTT admits #Ty : #Ty and
unrestricted recursive types, negative occurrences included, yet
remains consistent. The reason is affinity: a value can never be
used more than once, and the engines behind the classical
paradoxes all duplicate a $forall$-typed value at some point, so
none of them typechecks. That contraction, not impredicativity,
powers the paradoxes is an old observation. Grišin proved naive
set comprehension consistent over a logic without contraction
@grishin1982, and Girard and Terui rebuilt naive set theories over
light and affine linear logics @girard1998 @terui2004. BendTT
transplants that principle into a dependent type theory, where it
replaces the universe hierarchy outright, and the result is
mechanized in Lean 4 (@sec:mech). An earlier version of this
kernel carried a built-in judgment classifying the types whose
values may be copied; the present kernel goes further and admits
_no_ duplication at all: the copying permit moved out of the
kernel and into the surface, as a grade each datatype declares
and the checker verifies against its constructors
(@sec:grades).

The implemented language is larger than the kernel: machine words
and floats, flat arrays, and the surface grade system itself
exist in the implementation and are not yet formalized
(@sec:bend); those gaps are listed exactly. The calculus also
deliberately leaves room for extensions such as quotients and
extensionality principles, which require a redesign of
propositional equality.

For context, the language this kernel serves, in one paragraph.
Bend is a Python-shaped functional language with dependent types.
A declaration is an #co[assert], the full type, plus a #co[def],
its fill; #co[match]/#co[case] blocks over top-level parametric
datatypes flatten into case trees, machine 32-bit words and floats
and flat arrays ride beside them, propositional equality rewrites
through explicit motives, and every definition passes the descent
check. Values are affine by default; a binder marked #co[+] may be
consumed freely, and its type must be of the reusable kind
#co[Data] under the grade system of @sec:grades. One program hint,
the fork #co[let], drives a
bulk-synchronous runtime: programs compile to a standalone C file
that runs on CPU threads and on Apple-Silicon GPUs
@bendrt2026. The checker is bidirectional, with no unification, no
metavariables, and no implicit arguments anywhere. Excluding the
parser and the printer, the reference checker is a few thousand
lines of TypeScript.

= The Calculus <sec:calculus>

The calculus is a handful of definitions: terms and books,
reduction, quantities, typing, and the descent rule for recursion.
The first two are nearly conventional; the unconventional points
are flagged as they appear.

== Terms and Books <sec:terms>

#figure(caption: [Terms. One syntactic category: types are terms.
$q$ ranges over the quantities of @sec:quantities. A family head
$#fam($D$, $r$)$ carries the set $r$ of constructors a match has
already peeled, empty when written; constructors and families are
_heads_, saturated by ordinary application.], {
  set text(size: 9.5pt)
  grid(
    columns: (auto, auto),
    align: (left, left),
    column-gutter: 1.6em,
    row-gutter: 0.45em,
    grid.cell(colspan: 2, $t, A, B ::=$),
    $quad x$, [variable],
    $quad "@"k$, [reference to definition $k$],
    $quad #Ty$, [the sort],
    $quad forall^q x:A. thin B$, [function type],
    $quad lambda x. thin t$, [abstraction],
    $quad t thin u$, [application],
    $quad q thin x = t"; " u$, [let (not recursive)],
    $quad #fam($D$, $r$) thin p_1 ... p_n$, [datatype family, applied],
    $quad C{t_1, ..., t_n}$, [constructor of a family],
    $quad lambda{C:thin h"; " m}$, [match: peel one constructor],
    $quad lambda{}$, [empty match],
    $quad {a = b : T}$, [propositional equality],
    $quad {=}$, [reflexivity],
    $quad % thin e : P"; " f$, [rewrite by $e$ through motive $P$],
  )
}) <fig:terms>

@fig:terms gives the term formers. Types are terms, and any term
may appear anywhere. Four remarks.

First, datatypes are primitive, and they are the programmer's own.
A _book_ carries, beside its definitions, a list of datatype
families: a family signature is a telescope of parameters tipped
at #Ty, and each constructor is a telescope of erased parameters
then fields, tipped at the family applied to exactly its own
parameters, in order. There is no positivity restriction: a field
may mention the family to the left of an arrow, and
#ic[Trm: Lam{f: Trm $arr(1)$ Trm}] is a legal declaration.
@sec:term explains why that is harmless. There is also no
elimination principle to generate: the eliminator is the match.

Second, the match is a _peel_, not a table:
#ic[$lambda{C:thin h"; " m}$] applied to a $C$-headed value passes
the constructor's fields to $h$, and any other constructor falls
through to the default $m$, whose domain records $C$ in the
family's peeled set $r$, which conversion ignores. A full case
split is a chain of peels ending at the empty match
#ic[$lambda{}$], which eliminates a family with every constructor
peeled; the implementation's #co[match]/#co[case] blocks flatten
to exactly this shape. Eliminators are ordinary values that
consume their scrutinee by application, so a definition written as
nested lambdas and matches is a case tree, the shape the descent
rule of @sec:descent walks.

Third, the rewrite #ic[$% thin e : P"; " f$] carries its motive
$P$ in the term, a two-binder function over the carrier and the
equation. This is the J axiom and nothing more: from
$e : {a = b : T}$, the rewrite maps a goal $P thin b thin e$ to an
obligation $P thin a thin {=}$. The motive is written by the
programmer, not synthesized: Bend has no unification, so wherever
a motive is needed, the source states it (@sec:bend). Equality
here is the quiet, old-fashioned kind, on purpose: intensional,
computationally irrelevant, with no function extensionality and no
higher-dimensional structure; anything fancier is deferred
(@sec:conclusion).

Fourth, a book is _ordered_, and a definition is two events. An
#co[assert] declares a closed type; until its fill arrives, the
name is an _axiom_: it may be referenced in dead positions but
never consumed live, so an axiom can state anything and prove
nothing. A #co[def] fills a prior assert with a closed body,
checked live against the asserted type. Definition $k$ may
reference $"@"j$ for $j < k$ freely, and itself only through the
descent rule of @sec:descent; a reference to a _later_ name is
refused outright, so the reference graph is acyclic by
construction and mutual recursion cannot smuggle a loop past the
wall. References carry code, not resources: $"@"k$ costs nothing
in the usage accounting below.

== Reduction <sec:reduction>

#figure(caption: [Reduction. $n_k$ is definition $k$'s declared
arity; the $"@"k$ rule fires at weak strength only when the spine
is saturated, at strong strength at any arity, and the
$eta$-contraction is strong-only. The congruent closure comes at
two strengths: _strong_ reduction may enter any subterm, _weak_
reduction never enters a binder. Conversion $a conv b$ is
joinability under strong reduction.], {
  set text(size: 9.5pt)
  grid(
    columns: (auto, auto, auto),
    align: (right, center, left),
    column-gutter: 0.6em,
    row-gutter: 0.5em,
    $(lambda x. thin f) thin a$, $stepto$, $f[x := a]$,
    $q thin x = v"; " b$, $stepto$, $b[x := v]$,
    $"@"k thin a_1 ... a_(n_k)$, $stepto$, $beta(k) thin a_1 ... a_(n_k)$,
    $"@"D$, $stepto$, $#fam($D$, $uz$)$,
    $lambda{C:thin h"; " m} thin (C{p_1..., x_1...})$, $stepto$, $h thin x_1 ... x_n$,
    $lambda{C:thin h"; " m} thin (C'{...})$, $stepto$, $m thin (C'{...})$,
    $% thin {=} : P"; " f$, $stepto$, $f$,
    $lambda x. thin F thin x quad (x in.not F)$, $stepto$, $F$,
  )
}) <fig:reduction>

@fig:reduction lists the interactions. A reference unfolds only at
saturation and only with a body: an underapplied or unfilled
reference spine is a stuck weak-head value, which is what makes an
axiom inert and lets the checker keep goals in the vocabulary of
the source. At strong strength, conversion's reach, a reference
may unfold at any arity, and $eta$-contraction applies, so a
saturating argument can unfold what an underapplied definition
kept closed and conversion is up to $eta$ for functions. A bare
nullary family reference steps to its family head; a
_parameterized_ family head is deliberately stuck and has no bare
spelling: $D chevron.l p_1, ... chevron.r$ is the one way to write it.
A match meeting its constructor takes the fields (the erased
parameters $p_i$ are skipped); any other constructor falls to the
default, whole. A rewrite sheds when its evidence reaches
#ic[${=}$]; for closed live terms, canonicity guarantees it does.
Values are the type formers, constructor- and family-headed
spines, function values, and stuck reference spines.

There is nothing else: no side conditions, no strategy. Affinity
is enforced by the typing judgment, which counts usage at check
time (@sec:typing); reduction itself never blocks. Which claims
hold at which strength is stated exactly in @sec:claims.

== Quantities and Usage <sec:quantities>

Binders carry a quantity $q in {0, 1}$: erased or affine, spelled
#co[-x] and #co[x] in the surface. Throughout, _affine_ means
dropping is free and duplicating does not exist. A third value
$omega$ exists only inside the usage accounting, where it means
"consumed more than once" and is always a violation: no rule of
the kernel forms an $omega$ binder, and the surface spelling
#co[+x] belongs to the grade system of @sec:grades, not to the
kernel.

Usage is tracked by the judgment itself. A derivation returns a
_usage vector_ $pi$, a finitely supported map from variables to
quantities, recording what the term consumed. We write $uz$ for
the empty vector, $x^q$ for the singleton, $pi + pi'$ for the
pointwise saturating sum ($1 + 1 = omega$), $pi union.sq pi'$ for
the pointwise join (match arms: one branch runs, so arms share),
and $pi backslash x$ for removal. Quantities are ordered
$0 lt.eq 1 lt.eq omega$, and a binder of quantity $q$ admits any
measured usage $lt.eq q$. There is no scaling operation and no
multiplication anywhere: an argument's demand is _gated_, not
multiplied, by the function's domain quantity, written
$q' triangle.r.small q$, which is $0$ when the domain is erased
and the ambient demand $q$ otherwise.

== Typing <sec:typing>

#let JJ(G, q, t, T, p) = $#G scripts(tack.r)_#q #t : #T thin tri thin #p$

#figure(placement: top, scope: "parent", caption: [Typing. The
judgment #JJ($Gamma$, $q$, $t$, $T$, $pi$) reads: under book
$beta$ (left implicit) and context $Gamma$, at demand
$q in {0, 1}$, term $t$ has type $T$ consuming $pi$. $q' tri.r q$
is the gate of @sec:quantities (demand $0$ when $q' = 0$, else
$q$). In #smallcaps[ref], the side condition is that a _live_
reference needs a filled body: an axiom types only at demand $0$.
In #smallcaps[ctr], $"tele"(C, r)$ is constructor $C$'s declared
telescope, its tip's family head re-annotated with any peeled set
$r$ not containing $C$, which is what lets a scrutinee re-check at
the peeled domain of a match's default. In #smallcaps[mat],
$"arms"(C, p_1..., q', B)$ is $C$'s field telescope with the
parameters instantiated at $p_1...$, each field's quantity gated
by $q'$, tipped at $B$ applied to the constructor rebuilt from the
fields. Conversion in side conditions is relative to $beta$.], {
  set text(size: 9.5pt)
  let gate(a, b) = $#a thin triangle.r.small thin #b$
  rules(
    (rule(JJ($Gamma$, $q$, $x$, $T$, $x^q$), $(x : T) in Gamma$),
     rule(JJ($Gamma$, $q$, $"@"k$, $T$, $uz$), $beta(k) = (T, t)$, $q eq.not 0 arrow.r.double t eq.not "unfilled"$),
     rule(JJ($Gamma$, $q$, $#Ty$, $#Ty$, $uz$)),
     rule(JJ($Gamma$, $q$, $"@"D$, $#Ty$, $uz$), $beta(D) "a nullary family"$)),
    (rule(JJ($Gamma$, $q$, $#fam($D$, $r$)$, $"sig"(D)$, $uz$), $beta(D) "a family"$),
     rule(JJ($Gamma$, $q$, $C$, $"tele"(C, r)$, $uz$), $C "a constructor"$, $C in.not r$),
     rule(JJ($Gamma$, $q$, $forall^(q') x:A. thin B$, $#Ty$, $uz$),
       $q' eq.not omega$,
       JJ($Gamma$, $0$, $A$, $#Ty$, $dot$), JJ($Gamma, x:A$, $0$, $B$, $#Ty$, $dot$))),
    (rule(JJ($Gamma$, $q$, $lambda x. thin f$, $forall^(q') x:A. thin B$, $pi backslash x$),
       JJ($Gamma, x:A$, $q$, $f$, $B$, $pi$),
       $pi(x) lt.eq q'$),
     rule(JJ($Gamma$, $q$, $f thin a$, $B[x := a]$, $pi + pi'$),
       $q' eq.not omega$,
       JJ($Gamma$, $q$, $f$, $forall^(q') x:A. thin B$, $pi$),
       JJ($Gamma$, gate($q'$, $q$), $a$, $A$, $pi'$))),
    (rule(JJ($Gamma$, $q$, $q_b thin x = v"; " b$, $B$, $pi' + (pi backslash x)$),
       $q_b eq.not omega$,
       JJ($Gamma$, gate($q_b$, $q$), $v$, $A$, $pi'$),
       JJ($Gamma, x:A$, $q$, $b$, $B$, $pi$),
       $pi(x) lt.eq q_b$,
       $x in.not B$),),
    (rule(JJ($Gamma$, $q$, ${a = b : T}$, $#Ty$, $uz$),
       JJ($Gamma$, $0$, $T$, $#Ty$, $dot$), JJ($Gamma$, $0$, $a$, $T$, $dot$),
       JJ($Gamma$, $0$, $b$, $T$, $dot$)),
     rule(JJ($Gamma$, $q$, ${=}$, ${a = b : T}$, $uz$), $a conv b$)),
    (rule(JJ($Gamma$, $q$, $% thin e : P"; " f$, $P thin b thin e$, $pi + pi'$),
       JJ($Gamma$, $q$, $e$, ${a = b : T}$, $pi$),
       JJ($Gamma$, $0$, $P$, $forall^0 x:T. thin {a = x : T} arr(1) #Ty$, $dot$),
       JJ($Gamma$, $q$, $f$, $P thin a thin {=}$, $pi'$)),),
    (rule(JJ($Gamma$, $q$, $lambda{C: thin h"; " m}$, $forall^(q') (#fam($D$, $r$) thin p_1...). thin B$, $pi union.sq pi'$),
       $C in.not r$,
       $q eq.not 0 arrow.r.double q' eq.not 0$,
       JJ($Gamma$, $q$, $h$, $"arms"(C, p_1..., q', B)$, $pi$),
       JJ($Gamma$, $q$, $m$, $forall^(q') (#fam($D$, $r union {C}$) thin p_1...). thin B$, $pi'$)),),
    (rule(JJ($Gamma$, $q$, $lambda{}$, $forall^(q') (#fam($D$, $r$) thin p_1...). thin B$, $uz$),
       $"every" C "of" D in r$,
       $q eq.not 0 arrow.r.double q' eq.not 0$),
     rule(JJ($Gamma$, $q$, $t$, $B$, $pi$),
       JJ($Gamma$, $q$, $t$, $A$, $pi$), $A conv B$)),
  )
}) <fig:typing>

@fig:typing gives the rules. The judgment
#JJ($Gamma$, $q$, $t$, $T$, $pi$) carries a _demand_ $q$: the
quantity at which the term is being consumed. Most of the figure
is what any reader would guess; the content is in the following
five points.

_The wall is total._ There is no rule that forms an $omega$
binder: the function-type rule and the let rule refuse the
quantity outright, so contraction is not restricted, it is
unwritable. A binder's measured usage must fit its declared
quantity when it closes ($pi(x) lt.eq q'$), and two live uses
saturate the measure to $omega$, which no binder satisfies. This
single check is the consistency mechanism (@sec:term); the
implemented language re-admits contraction only through the
surface grade system of @sec:grades, which the kernel never sees
as a rule.

_The erased fragment is free._ At demand $0$ nothing is charged:
a dead premise's measure is unconstrained and the rule that checks
it dead drops it from the conclusion (written $dot$ in the
figure). Types in premises, equality endpoints, motives, and
erased arguments all check dead. Erased code is specification, not
proof; it can even inhabit an empty family (@sec:claims), and no
rule coerces dead to live.

_Matching is consumption._ In a live region a match's domain
quantity must be live ($q eq.not 0 arrow.r.double q' eq.not 0$):
an erased scrutinee cannot be inspected by running code. The arm
receives the constructor's fields at quantities gated by the
scrutinee's, the default receives the scrutinee with the handled
constructor peeled onto the family head, and the two usages _join_
rather than add, since one branch runs. The empty match closes a
family whose every constructor is peeled.

_Equality is dead where it states and live where it runs._ The
equation's components live in the type and are checked erased, so
a proof may mention already-consumed variables there for free,
which is the idiom inductive proofs live on. The evidence of a
rewrite, by contrast, runs (to #ic[${=}$]), so it is checked at
the ambient demand; the motive is checked dead.

_Conversion, and no totality._ The conversion rule moves the goal
along $conv$ and is the only mode switch. Nothing makes checking
total: conversion may diverge on dead code, and the checker is a
semi-decision procedure. This is deliberate; see
@sec:term-partial.

== Descent: the Recursion Rule <sec:descent>

Self-reference passes one test, run on the definition's own case
tree. Walking the body, the checker rebuilds the definition's
left-hand side: a lambda binds the next _column_, a match peels
the current column into a constructor of fresh field columns, and
at every leaf each self-reference must head a whole call whose
arguments _descend_ against the columns: reading left to right and
skipping erased columns, every argument compares equal to its
column until one is a _strict subterm_ of it, the same constructor
with at least one strictly smaller field, or a term sitting inside
one of the pattern's fields, one constructor peel deep. Arguments
past the decreasing one are unconstrained. No sizes are computed
and no size-change graph exists: the order is syntactic, the
comparison sees through lets and annotations, and the whole check
is one pass over the elaborated body. Erased columns are skipped
because erased data cannot be matched by live code, so it can
never carry the decrease.

Concretely:

```
assert add:
  forall n: Nat
  forall m: Nat
  Nat

def add(n, m):
  match n:
    case 0n:
      m
    case 1n+p:
      1n + add(p, m)
```

The successor arm binds #co[p] one peel inside #co[n], so the
self-call's first column is strictly smaller and the second is
never consulted. A lexicographic pair descends the same way:
#co[ack(1n+i, 0n)] may call #co[ack(i, 1n)] (first column
smaller, second free) and #co[ack(1n+i, 1n+j)] may call
#co[ack(1n+i, j)] (first equal, second smaller). To be clear about
the ambition: this is a minimal member of the structural-recursion
family @gimenez1994 @abelaltenkirch2002 @leejones2001, chosen
because it is trivial to audit, and it is the rule the
implementation runs, not an idealization of it.

== Books, and the Claims <sec:claims>

A book $beta$ is _well-formed_ ($sans("Ok")$) when, in the empty
context: every family signature and constructor telescope checks
dead against #Ty and has its declared shape, each constructor
tipping at its own family; every definition's type checks dead
against #Ty; every filled body checks _live_ against its type;
and every body's case tree descends, with no reference at or
beyond its own index except the guarded self-call. There is no
separate termination checker bolted onto the language:
$sans("Ok")$ _is_ the language. The metatheory then promises, for
every $sans("Ok")$ book $beta$:

+ _Confluence_: strong reduction is Church-Rosser, so $conv$ is a
  sensible equality.
+ _Subject reduction_: if #JJ($Gamma$, $q$, $t$, $T$, $pi$) with
  $q eq.not omega$ and $t stepto t'$ by a weak step, then
  #JJ($Gamma$, $q$, $t'$, $T$, $pi'$) with $pi' lt.eq pi$: a step
  never grows the affine measure, and never wakes an erased
  variable.
+ _Progress_: a closed term well-typed at a live demand is a value
  or takes a weak step.
+ _Normalization_: a closed term with #JJ([], $1$, $t$, $T$, $pi$)
  reduces weakly to a value _of its type_.
+ _Consistency_: for any family with no constructors, there is no
  closed $t$ with #JJ([], $1$, $t$, $"Empty"$, $pi$).

The hypotheses are exact, and the mechanization proves it. At
demand $0$ the calculus deliberately inhabits empty families
(erased code is specification, @sec:typing), so claim (5)'s live
demand is necessary, and the boundary is itself a theorem
(@sec:mech). Progress is claimed at live demand because an axiom
is stuck by design: dead code may rest on an unfilled assert.
Strong reduction is not strongly normalizing even on live
well-typed values (a value may step inside itself forever), so
claim (4)'s weak reachability is the strongest normalization
statement that is true, and claim (2) draws the same line: a
$beta$ under a binder can duplicate the pending call of an affine
variable (@sec:discussion), so preservation holds at weak and
fails at strong. Terms whose type _is_ the sort are types, and the
type level may diverge by design.

= Why It Terminates <sec:term>

In a functional language there are only two ways to loop:
self-application and recursion. BendTT closes them independently,
and the two walls are simple enough to state in a paragraph each.

== Self-Application Dies at the Usage Check

Consider $omega = (lambda x. thin x thin x) thin (lambda x. thin x thin x)$.
The body $x thin x$ uses $x$ twice, so its measure saturates to
$omega$; but no binder admits a measure of $omega$, and the
function-type former refuses the quantity outright, so the term is
unwritable at _any_ type, at any live demand. There is no
side-channel to guard: where the predecessor design had to argue
that its copyable class excluded functions, this kernel has
nothing to exclude, because nothing copies. Curry's paradox
through a negative recursive type @curry1942, and Girard's paradox
through impredicativity @girard1972 @hurkens1995, both bottleneck
through duplicating a $forall$-typed value, and die at the same
check. Neither a universe hierarchy nor a positivity check is
needed.

The point is sharpest at a negative type. The declaration
#ic[Trm: Lam{f: Trm $arr(1)$ Trm}] is a legal family, the
classical paradox vehicle, and a higher-order-abstract-syntax
embedding over it is a perfectly fine book: by the claims it is a
consistent, terminating development. The paradox engine must apply
#ic[$lambda x. thin dots x dots x dots$] to itself, needs its
binder twice, and dies. Nothing guards the negativity except
affinity, and the mechanization exhibits exactly this: a
well-formed book with a negative type in which Curry's
self-application term typechecks _dead_ at an empty family, and
provably never live (@sec:mech).

== Recursion Dies at the Descent

Every live self-call repeats its columns until one argument sits
strictly inside its own pattern, one constructor peel deeper.
Constructor values in the live fragment are finite trees, so the
lexicographic order on peels is well-founded and the chain of
self-calls bottoms out; erased columns, which escape the usage
wall, are skipped by the descent for the same reason they escape
it: they can never reach live code. Even a HOAS-style loop,
$"loop" thin (C{f}) = "loop" thin (f thin (C{f}))$, fails: the
argument of the self-call is an application, not a subterm of the
pattern. And because a book is ordered and a body may not
reference a later name, mutual recursion cannot bypass the wall by
splitting a loop across two definitions.

Together: no live term can duplicate anything, every recursive
call shrinks its own case tree's columns, and erased code, which
escapes both walls, is never consumed at a live demand. Hence
every closed live term normalizes and no empty family is inhabited
live. @sec:mech makes this argument formal; the informal version
above is faithful to it.

== What May Diverge <sec:term-partial>

The _dead level_ is exempt on purpose. Types may loop; erased
positions may loop; so conversion, and with it the checker, is a
semi-decision procedure, as conversion checking in dependent type
theories already is @coquand1991. A non-halting check reads as
"inconclusive", never as acceptance: the stance is
soundness-on-accept, not checker totality. Consistency requires
terminating _proofs_, not a terminating checker; NuPRL ran
divergent computation inside a consistent logic in the 1980s
@constablesmith1987, and Zombie/Trellys combined a consistent
fragment with a partial one in a single language @casinghino2014.
BendTT draws the line at the demand: live terms terminate, dead
terms and types need not.

= The Grade System <sec:grades>

#let Gr = $sans("Grade")$
#let Da = $sans("Data")$
#let g1 = $"&1"$
#let g2 = $"&2"$
#let Kd(g) = $sans("Kind")(#g)$

The kernel forbids contraction; programs still need it, an
inductive proof feeds one field to the induction hypothesis and a
lemma at once. Bend re-admits it through a _grade on every kind_.
The one sort of the kernel splits: a type's kind is #Kd($g$) over
a grade $g$, either #g1 (affine) or #g2 (reusable), with
#Ty $=$ #Kd(g1) and #Da $=$ #Kd(g2). A binder of quantity $omega$
(surface #co[+x], or the local #co[+x = v]) is permitted if and
only if its type's kind reduces to #Da. This is the only
duplication mechanism in the language; nothing else contracts.

#figure(caption: [The grade extension. The rules of @fig:typing
stay; these are added over them. $a inter.sq b$ is the grade
_meet_ (surface #co[<\&>]), which reduces only against a literal:
$#g1 inter.sq b stepto #g1$, $a inter.sq #g1 stepto #g1$,
$#g2 inter.sq b stepto b$, $a inter.sq #g2 stepto a$, and a meet of two
stuck grades is stuck. The last two rules are the subsumptions:
every kind weakens to #Ty and #Da weakens to every kind, so #Da
is the bottom, #Ty the top, and nothing weakens to #Da. A family
signature now tips at #Kd($G$), so through #smallcaps[app] a
family applied to its parameters has kind #Kd($G[p_1...]$).], {
  set text(size: 9.5pt)
  rules(
    (rule(JJ($Gamma$, $q$, Gr, $#Ty$, $uz$)),
     rule(JJ($Gamma$, $q$, g1, Gr, $uz$)),
     rule(JJ($Gamma$, $q$, g2, Gr, $uz$)),
     rule(JJ($Gamma$, $q$, Kd($g$), $#Ty$, $uz$), JJ($Gamma$, $0$, $g$, Gr, $dot$)),
     rule(JJ($Gamma$, $q$, $a inter.sq b$, Gr, $uz$), JJ($Gamma$, $0$, $a$, Gr, $dot$), JJ($Gamma$, $0$, $b$, Gr, $dot$))),
    (rule(JJ($Gamma$, $q$, $forall^omega x:A. thin B$, $#Ty$, $uz$),
       JJ($Gamma$, $0$, $A$, Da, $dot$), JJ($Gamma, x:A$, $0$, $B$, $#Ty$, $dot$)),
     rule(JJ($Gamma$, $q$, $omega thin x = v"; " b$, $B$, $pi' + (pi backslash x)$),
       JJ($Gamma$, $0$, $A$, Da, $dot$),
       JJ($Gamma$, $q$, $v$, $A$, $pi'$),
       JJ($Gamma, x:A$, $q$, $b$, $B$, $pi$),
       $x in.not B$)),
    (rule(JJ($Gamma$, $q$, ${a = b : T}$, Da, $uz$),
       JJ($Gamma$, $0$, $T$, $#Ty$, $dot$), JJ($Gamma$, $0$, $a$, $T$, $dot$),
       JJ($Gamma$, $0$, $b$, $T$, $dot$)),
     rule(JJ($Gamma$, $q$, $t$, $#Ty$, $pi$), JJ($Gamma$, $q$, $t$, Kd($g$), $pi$)),
     rule(JJ($Gamma$, $q$, $t$, Kd($g$), $pi$), JJ($Gamma$, $q$, $t$, Da, $pi$))),
  )
}) <fig:grades>

@fig:grades gives the rules. Three points carry the design.

_Kinds are assigned by shape, and weaken one way._ A function type
is #Ty: a closure captures, so it is never reusable, whatever its
domain and codomain. An equation is #Da: its evidence is erased,
and a closed live proof is #ic[${=}$], so there is nothing inside
to duplicate. A datatype declares its own kind, and the declared
grade may depend on the parameters. At the conversion rule every
kind converts to #Ty and #Da converts to every kind, so a #Da type
is accepted wherever any kind is expected, and nothing converts to
#Da. Values do not weaken with
their kinds: #co[List<\&2, A>] and #co[List<\&1, A>] are distinct
types, and generic code is _grade-polymorphic_, taking the grade
as an erased parameter (#co[forall -a: Grade]). A $omega$ binder
needs a kind whose grade _reduces_ to #g2, so a parameter grade
licenses nothing: a polymorphic function cannot duplicate its
argument, and #co[+] becomes available only after instantiation.

_Declarations earn their grade._ A datatype is declared
#co[type D\<p_1, .., p_n\> is Kind(G):] with $G$ a grade over the
parameters; a bare name in the telescope is sugar for an erased
#Gr parameter. The book validator reads $G$ off the signature and
then, for each constructor, infers every field's kind in the real
constructor context, parameters then fields, and demands that a
_live_ field's grade $H$ be _entailed_ by $G$, written
$G models H$. Entailment is over atoms:
$"atoms"(#g2) = nothing$, $"atoms"(#g1) = {#g1}$,
$"atoms"(a inter.sq b) = "atoms"(a) union "atoms"(b)$, a stuck grade
is its own atom, and $G models H$ holds when
$#g1 in "atoms"(G)$ or $"atoms"(H) subset.eq "atoms"(G)$ up to
conversion. So #g2 entails only grades that reduce to #g2, #g1
entails everything, and a parameter grade entails itself. An
erased field is absent from storage and dead, and is exempt. From
the base library:

#block(breakable: false)[
```
type List<a, -A: Kind(a)> is Kind(a):
  Nil{}
  Con{head: A, tail: List<a, A>}

type Sigma<a, b, -A: Kind(a), -B: @-x: A -> Kind(b)>
  is Kind(a <&> b):
  Tuple{fst: A, snd: B(fst)}
```
]

#co[List] is as reusable as its element; a pair is reusable when
both halves are; #co[Nat], #co[Bool], #co[U32] and #co[String] are
declared at #Da, so an inductive proof may bind a predecessor with
#co[+] and feed it to the induction hypothesis and a lemma at
once.

_Nothing affine hides in #Da._ The entailment check, run in the
real constructor context, closes every hiding place we know of.
A _function field_ has kind #Ty, whose atom #g1 no #g2 or
parameter grade contains, so a closure can sit only in a family
declared at #Ty: where the predecessor design had to argue that
its copyable class excluded functions, this check refuses them per
declaration. An _equation_ holds nothing that runs; rewriting
consumes it once, like any value, and duplicating #ic[${=}$]
duplicates nothing. An _existential_ takes the meet of its
components: the type of copies of $x$, #co[\&y: T -> {x == y : T}],
has the single inhabitant #co[(x, {==})], and a system that treats
that contractible type as reusable duplicates $x$ with it; here its
kind is #Kd($a inter.sq #g2$) $=$ #Kd($a$), the grade of $T$ itself.
A _recursive type_ needs no fixed point: the declaration's own
kind is assumed at its own occurrences, and this is sound because
a live value is a finite tree, so the invariant, a #Da value holds
no live affine value, follows by induction on the value, the
recursive field being the induction hypothesis. A
_constructor-local abstraction_, a constructor that binds its own
erased type or grade and stores a field at it, is refused: the
field's kind is #Kd(g1) or #Kd($g$) for a local $g$, and neither
atom occurs in $G$, which is spelled over the family's parameters
only. A _grade equation_, #co[{\&1 == \&2 : Grade}], can be stated,
since endpoints are dead, and a rewrite through it produces a term
of type #Da from a function type, licensing a $omega$ binder over
it; this is harmless, because that type is a stuck rewrite, which
no lambda checks against and no application eliminates, so the
binder duplicates only stuck terms, and it stays stuck while the
evidence does. The evidence sheds only at #ic[${=}$], which needs
#g1 $conv$ #g2, so no closed live proof of the equation exists,
and a dead one never reaches live code.

The grade system is an implementation extension, not a kernel
rule, and it is stated here with that honesty: the mechanization
of @sec:mech covers the affine kernel, in which #g2 does not
exist, and the consistency of the live fragment under the
extension is a conjecture, backed by hostile audits rather than a
theorem. The argument for it is elementary: a #Da declaration's
constructors hold only #Da fields, so a structural clone of any
#Da value is an ordinary recursive Bend definition over its
declaration, one match per constructor, one rewrite per equation,
and consuming a $omega$ binder $n$ times abbreviates $n - 1$ such
clones the program could have written by hand. Mechanizing that
elaboration is planned work. Grades are erased at runtime, like
types. No escape hatch stands beside the system: an earlier pragma
let a file opt out of the duplication condition and the descent,
and it was removed once the whole corpus checked without it; the
affine usage cap had never been part of the trade.

= The Mechanization <sec:mech>

The metatheory is mechanized in a single Lean 4 file,
#co[bend2/bend.lean] in the Bend repository, checked with a plain
#co[lean] invocation: no libraries, no build system. The file has
two parts. #smallcaps[Part I] (under a thousand lines) is the
specification, and is the part a human should read: quantities,
syntax (de Bruijn), reduction at two strengths, typing, descent,
$sans("Ok")$, and the five claims stated as propositions,
mirroring the implementation's own core section by section;
@sec:calculus restates it in mathematical notation.
#smallcaps[Part II] ($tilde$19k lines) proves the claims. There
are no #co[sorry]s and the file declares no axioms of its own.

#figure(caption: [The claims and their theorems in
#co[bend.lean].], {
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
    [Normalization (weak, live, typed value)], co[normalization_holds],
    [Consistency (live)], co[consistency_holds],
    [The dead boundary, as a witness], co[consistency_none_boundary],
    table.hline(stroke: 0.6pt + solfg),
  )
}) <tab:claims>

The techniques are conventional where they can be. Confluence is
Takahashi's parallel reduction and complete developments
@takahashi1995. Subject reduction goes through generation and
substitution lemmas with the usage accounting threaded through;
the "$omega$ is never a demand" discipline of @sec:typing is what
makes the substitution lemma true, and the theorem is sharper than
preservation alone: the affine measure never grows along a weak
step. Normalization and consistency are proven _in full,
recursive definitions included_, by a hand-rolled well-founded
measure: a Dershowitz--Manna multiset @dershowitzmanna1979 of
_charges_, each pricing one pending reference by a per-column size
tuple plus a slack slot, paired with the weight of a typed live
erasure of the term. Ordinary interactions keep the charges and
strictly drop the weight, the affine beta lands at most one live
copy; spending a reference runs its case tree against the call's
arguments, and the descent columns reprice every self-call
strictly below the spent tuple, the slack slot paying for
underapplied suspensions. Consistency is normalization plus
canonical forms at an empty family.

The boundaries of the claims are witnesses, not caveats: the file
exhibits a well-formed book with a negative recursive type in
which Curry's $omega$ term checks _dead_ at an empty family
(#co[dead_omega_check], packaged as
#co[consistency_none_boundary]), which is exactly why claims (4)
and (5) demand liveness.

Provenance, stated plainly: the specification was written and
reviewed by humans; the proofs of #smallcaps[Part II] were written
by an AI system (Claude Fable 5, Anthropic) and are checked by
Lean. The humans audited the statements, not the proof bodies. We
consider this trust story acceptable because it is the one proof
assistants offer in general: trust the checker, audit the
statements.

= From BendTT to Bend <sec:bend>

The reference implementation is a bidirectional checker
@pierceturner2000 @dunfieldkrishnaswami2021 for this discipline,
plus surface features. The differences from the calculus are
engineering, not logic; we list them, and the ones that are
genuine extensions are flagged as unformalized.

_Patterns and motives._ Bend's #co[match]/#co[case] blocks
flatten into case trees of the one-constructor peel
@augustsson1985 @maranget2008: first row wins, uncovered cases
become the empty match, and exhaustiveness is the checker's
concern, not the parser's, an unreachable hole is exactly a
well-typed empty match. Because there is no unification, a match
whose motive genuinely depends on its scrutinees is written
_framed_: the source states the motive, and the flattener rebuilds
the tree annotated with it. This is a design commitment, not a
gap: every feature known to make checking slow or unpredictable,
metavariables, implicit arguments, global search, was left out,
because Bend aims at checking large codebases at ordinary-compiler
speeds.

_Binders and elaboration._ The checker represents binder bodies as
host-language closures (higher-order abstract syntax
@pfenningelliott1988 @chlipala2008): substitution is application
in the host, and no de Bruijn machinery exists outside the
formalization. Combined with conversion by reduce-and-compare, the
checker is in effect an evaluator in the style of normalization by
evaluation @bergerschwichtenberg1991. It elaborates as it checks,
annotating every layer; the elaborated body is stored on the
definition and consumed by the compiler, never re-consumed by the
checker itself.

_Asserts, fills, and the world._ The assert/fill split of
@sec:terms is the surface's own declaration form, and it carries
the language's one doorway to effects: a fill whose body is a list
of foreign imports is an effectful primitive, allowed only at the
base library's #co[IO] type and run only by the event loop, so an
axiom can be stuck and still name an effect the runtime performs.
The typed interface stays honest: a foreign name is stuck for
conversion, live-usable for the event loop, and nothing else.

_Unformalized extensions._ Machine 32-bit words and floats (the
float family is axiomatic in the base library), flat arrays with
in-place backends, the base library's native representations, and
the grade system of @sec:grades, whose kernel-side meaning is the
elaboration argument given there. The compiler is bound by a cost
law the checker sets: it may drop a cost the source spelled, a
licensed reuse may become a counted share or a borrow, but it may
never add a clone or a retain the source did not spell
@bendrt2026. None of these features interacts with the
consistency argument, and formalizing the grade system is the
next planned extension of the mechanization.

= Discussion <sec:discussion>

== What Affinity Takes Away

The honest price is contraction on closures. The standard

$ "map" : forall^1 f:(A arr(1) B). thin forall^1 x s:"List" thin A. thin "List" thin B $

is ill-typed: $f$ is used once per element, its binder would need
$omega$, and a function type is #Ty, never #Da: a closure
captures, and no declaration can grade it reusable. There is no
workaround that smuggles a closure copy in. The practical
escape is that _code_ is free: a top-level definition may be
referenced any number of times, so specialized maps, or maps over
#Da in place of closures, cover the common idioms; but
first-class closure-heavy style does not transfer. Bend accepts
this deliberately: the restriction is also what the runtime wants
@bendrt2026, and years of writing in this discipline suggest the
loss is bearable.

== Expressiveness

A consistency proof means little if little can be said under it,
so we state the reach directly. On the program side the baseline
is C: first-order data, machine words, arrays updated in place,
top-level code called by name. That fragment passes through
affinity untouched, and it is the one scripts, servers, games and
operating systems are written in, none of which ever needed a
copied closure. What does not transfer is a style, the Haskell
one, not a class of programs.

On the proof side the freedom is larger, not smaller. Statements
are erased: at demand $0$ occurrences cost nothing, so a theorem
may quantify over functions, repeat variables, and apply anything
freely; affinity constrains what runs, never what is said. Live
proofs draw their duplication from #Da, the reusable kind of
first-order data, which is what induction wants: the base library
declares its naturals, words and strings at #Da, derives its
equality kit (congruence, symmetry, transitivity, each a single
rewrite), and proves commutativity of addition on 32-bit words,
checked by Bend itself.
Theorems whose subjects are first-order, most of mathematics,
never meet the restriction at all.

== Anticipated Objections

_"This is just QTT."_ The quantities come from McBride and Atkey
@mcbride2016 @atkey2018, and the restriction of demands to
${0, 1}$ mirrors Atkey's. But QTT admits $omega$ binders at every
type, so QTT with #Ty : #Ty is Girard-inconsistent; its
consistency comes from the universe hierarchy it keeps. BendTT
has no $omega$ binders at all, no scaling and no semiring, and
the copying permit is a surface grade that each datatype
declares and the checker verifies (@sec:grades): the absence
carries the entire weight the hierarchy would.

_"Equality needs non-linear variables:
$"refl" : forall a. thin {a = a : T}$ mentions $a$ twice."_
Occurrences in types cost nothing; only live demands count.
$"refl" = lambda a. thin {=}$ checks with an erased binder: the
equation's components are erased, and the proof term carries
nothing. Rewriting with an equation consumes the equation once,
like any other value.

_"Without positivity you get Curry's paradox."_ The Curry term
exists and typechecks _dead_, the mechanization exhibits it at an
empty family in a well-formed book with a negative type
(#co[consistency_none_boundary]), but no live judgment accepts
it: the duplication it needs is unwritable. The boundary is a
theorem rather than an apology.

_"Reduction can break affinity under a $lambda$."_ Yes: a strong
step under a binder can duplicate the _pending call_ of an affine
variable by substituting it into a body that repeats its own
binder in a dead position. No evaluator takes such a step: checker
and runtime evaluate weakly, and claims (2) and (4) are stated at
weak reduction for this reason; consistency asks nothing more,
since evaluating a closed program only fires closed redexes.

_"The checker can loop."_ Yes, on dead code, by design
(@sec:term-partial). A hang accepts nothing, and the deployed
checker is deterministic, so the same program is admitted or
rejected identically on every machine.

_"Erased code can inhabit #co[Empty]; is that not inconsistency?"_
No: erased code is specification. Nothing live can consume an
erased inhabitant, no rule coerces dead to live, and the theorems
quantify over live judgments. The mechanization states this
boundary as a theorem rather than hiding it.

_"A #co[Data] declaration could hide a closure."_ It cannot:
the book validator checks every live field of every constructor
against the declared grade, in the constructor's own context, and
a function type is #Ty there, as is any constructor-local type or
grade (@sec:grades). And the grade system lives outside the
kernel: the mechanized claims do not rest on it.

_"Why not just use universes?"_ Universes are the orthodox road,
and nothing prevents adding a hierarchy to BendTT later. But Bend
needs affinity anyway, for its runtime; reusing it for consistency
means one mechanism where there would otherwise be two, plus level
arithmetic, cumulativity, and universe polymorphism. #Ty : #Ty
also buys real expressivity: impredicative encodings and
type-computing definitions that no predicative hierarchy accepts.

== Limitations

The consistency result is syntactic: normalization plus canonical
forms, formalized in Lean. It therefore holds relative to the
consistency of Lean's own foundation. There is no semantic model:
no set-theoretic, denotational or realizability interpretation,
and no conservativity result over an established theory. A model
would explain _why_ affinity carries the weight, not only that it
does; realizability for linear dependent theories @speight2026
looks like a starting point, and this is future work. Conversion
is joinability of reduction with $eta$ for functions and nothing
for pairs. The grade system is argued and audited, but not yet
mechanized, and the consistency of the live fragment under it is
a conjecture (@sec:grades). And the theorems are about the
calculus, not the code: the reference checker is ordinary
unverified software, and @sec:bend's correspondence is an
engineering claim, not a theorem.

== Related Work

Linear-plus-dependent systems go back to LLF @cervesatopfenning2002
and continue through
@krishnaswami2015 @vakar2015 @fukishida2020 @luozhang2016; the
quantitative line @mcbride2016 @atkey2018 @brady2021 @moon2021 is
the closest in mechanism, and Abel et al. mechanized a graded
theory with a predicative universe @abel2023graded. To our
knowledge none of these uses the absence of contraction _for_
consistency: a 2023 linear dependent type theory still adds
universe levels "to avoid Girard's paradox" @fuxi2023, and recent
work on impredicativity in linear dependent theories obtains an
impredicative universe, not #Ty : #Ty, via a realizability model
@speight2026. The consistent-logic-with-partiality line is
@constablesmith1987 @casinghino2014 @weirich2017, and
per-definition termination certificates are ACL2's definitional
principle @kaufmannmoore2000. Mechanized metatheories of practical
kernels include @abel2018 @sozeau2020 @carneiro2024; ours is
smaller in scope but proves normalization rather than assuming it.
The small-kernel tradition runs from Automath
@debruijn1980 @barendregtgeuvers2001 through LCF and HOL Light
@gordon1979 @harrison2009; Bend's predecessor kernels in the same
ecosystem were based on self types @fustump2014 @stump2017.

= Conclusion <sec:conclusion>

BendTT buys consistency with affinity instead of a universe
hierarchy, checks recursion with a descent rule simple enough to
audit in an afternoon, and is mechanized end to end, recursive
definitions included. The one liberty its predecessor took inside
the kernel, a built-in class of copyable types, has been evicted:
the kernel now refuses all duplication, and the surface earns it
back with grades, declared per datatype and verified at every
constructor. Nothing in the calculus is difficult, and that is
the point: it is meant to be read, audited, and extended. The
mechanization will keep growing toward the implemented language,
the grade system first, and perhaps toward stronger equalities:
we watch the higher observational line, Narya in particular
@narya2024, as the likely shape of that redesign.

#heading(numbering: none, outlined: false)[Acknowledgments]

The proofs in #co[bend.lean] were written by Claude Fable 5
(Anthropic) and checked by Lean 4; this text was drafted with the
same model. Thanks to the Higher Order Company team for
discussions.

#{
  show heading: set text(size: 12pt)
  set text(size: 8pt)
  bibliography("refs.bib",
    title: [References],
    style: "association-for-computing-machinery")
}
