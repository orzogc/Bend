-- HUMAN NOTE: the (massive) file below is near entirely AI written, including
-- all proofs, but that is not relevant, because the proofs are mechanically
-- checked by Lean, so, only the spec (which is relatively small) matters!
-- 
-- Sadly, even the spec itself has drifted from what Bend's core implements, in
-- some important ways, most notably in how Data kinding is handled. As launch
-- approaches, we didn't have time to fully update it; it takes several days for
-- AI models to rework the proofs after a spec change; so, we leave it as is for
-- now, and will update later.
-- 
-- Currently, the most surprising contribution of this file is a mechanization
-- of a consistent proof language with Type:Type and negative recursive types.
-- The core insight is that we exploit linear types to forbid the contraction of
-- functions, while still allowing cloning lower order values. This inhibits the
-- source of most paradoxes: Girard's, Russell's, Curry's and the like all are
-- manifestations of self-replicating lambdas (like `λf.f(f) λf.f(f)`), which
-- are not representable in this theory. With this, the consistency becomes
-- relatively trivial, and the only reason this file is massive is that the
-- proofs are still written by AI, which struggles to craft concise arguments.
-- 
-- ----------------------------------------------------------------------------
-- 
-- ============================================================================
-- BEND-CORE — the bend2-core affine calculus
-- ============================================================================
--
-- A model of the Bend core (the core sections of bend2/bend.ts, Types
-- through Valid): language, reduction, typing, descent, and the claims.
-- The model has drifted from the shipped checker; the divergences are
-- listed below, and a resync covering the full core is in progress. PART I is the SPEC — the parts a human must
-- read. PART II is the metatheory appendix proving the claims.
--
-- THE HEADLINE. A dependent calculus with Type : Type, impredicativity,
-- and negative recursive types, made consistent not by a universe
-- hierarchy or a positivity check but by a usage wall: the calculus is
-- COMPLETELY AFFINE. Two checking demands only — None (dead) and Lone
-- (live) — and no duplication of any kind: Many is unspellable here
-- (the checker rejects a Many binder at formation) and survives only
-- inside the usage measure, where it means "consumed more than once"
-- and is always a violation. THIS IS THE LARGEST DIVERGENCE FROM THE
-- SHIPPED LANGUAGE: bend.ts licenses duplication through the Data
-- layer, whose + binder, + field and certify-once promotion have no
-- counterpart here, and whose usage metatheory holds only for weak
-- by-value reduction of closed terms and rests on three invariants
-- outside the checker — see divergence (2). This file mechanizes the
-- all-&1 fragment. Every live self-call
-- descends lexicographically on the definition's own case-tree
-- columns, and no rule coerces dead to live. In a functional language
-- there are only two ways to loop: self-replicating lambdas (dead on
-- arrival: no live binding contracts at all) and recursion (closed by
-- descent). Dead code is specification, not proof: it may diverge and
-- may inhabit Empty, and the claims are stated for the live fragment
-- only.
--
-- THE SYNTAX is one Term type, de Bruijn, first-order. Datatypes are
-- user-declared families in the book: a family signature is a telescope
-- of parameters tipped at Type; a constructor is a telescope of (erased)
-- parameters then fields tipped at the family applied to its own
-- parameters. In this formalization the family former (Adt a r) and the
-- constructor former (Ctr a c) are HEADS, applied through ordinary App:
-- a saturated constructor value is an application spine. Mat is the one-
-- constructor peel: (Mat a c h m) applied to a c-headed spine passes the
-- FIELDS to h; any other constructor falls to m, whose domain records c
-- as peeled (the r list on Adt). Efq eliminates a family with every
-- constructor peeled. Eql/Rfl/Rwt are propositional equality: endpoints
-- and carrier are dead, Rfl proves conversion, Rwt rewrites through a
-- motive that is dead.
--
-- THE MAP. Part I mirrors bend2/bend.ts's core section by section:
--
--   bend.ts section   | here          | contents
--   ------------------|---------------|--------------------------------
--   Types             | §1 Types      | Quant, Uses, Term, Ctx, DefD,
--                     |               | CtrD, AdtD, TLD, Book
--   Quant             | §2 Quant      | add, join, le, dem
--   Uses              | §3 Uses       | zero, one, add, join, tail, le
--   Term              | §4 Term       | apps/spine (term_apply/unapply),
--                     |               | shift, subst, Closed, the J
--                     |               | motive, the lhs algebra (lhs_ext)
--   Ctx, Ctrs, Book   | §5 Ctx/Book   | get, tld, adt, defn, ctr
--   Compare           | §6 Compare    | PEq/PLt (EQ/LT verdicts),
--                     |               | SpineLt (the descent loop)
--   Tele              | §7 Tele       | FTele, WTele, STele, shapes
--   WNF, SNF          | §8 Equal      | Step/Red (wnf/snf), Conv (compare)
--   Check             | §9 Check      | the one judgment (infer+check)
--   LHS, (infer-ref)  | §10 Descent   | Guard (the self-call rule),
--                     |               | Tree (the lhs threading)
--   Valid             | §11 Valid     | Book.Ok (book_valid)
--   (header claims)   | §12 Claims    | the five claims as Props
--
-- NOT MODELED. Char, PMap, the number sections (Nat, Word, U32, F32),
-- Show, Parse, Flatten and the import system are parsing and pipeline
-- concerns with no counterpart here;
-- U32/SCon/SNil string literals are base.bend constructors, not
-- calculus.
--
-- Beyond those, bend.ts and this file DIVERGE in ten places, listed in
-- full below. Each is a PERMISSION the implementation adds: bend.ts
-- accepts every book this file types, PLUS books that use (1)-(10), and
-- the theorems below do not cover those. (1)-(5) are mechanisms with no
-- counterpart here at all, and (2) is the largest: the whole Data layer.
-- (6)-(10) are narrower: the mechanism exists on both sides, but Book.Ok
-- pins a SHAPE syntactically where validation reaches it by
-- normalization or replaces it with a spot test, so a book may check and
-- still fail Book.Ok. Do not read the claims as covering more than this
-- list allows.
--
-- (1) the kind system: every type has a kind Kind(q) over a quantity
--     q : Quant, &1 (Lone) or &2 (Many); Type = Kind(&1), Data =
--     Kind(&2); at check-any Kind(g) fits Kind(h) when h <= g, so Data
--     fits every kind and every kind fits Type, never else.
--     A binder q x (at All/Let formation and over ADT telescopes)
--     checks its type against Kind(q), so a Many binder needs a type
--     whose kind fits Data under term_equal's order.
--     A function type is Type, an equation is Data, a datatype declares
--     its kind Kind(G), and adt_valid checks every live field's type
--     against Kind(G) (a + field against Data), in the real
--     constructor context; the meet a <&> b is the minimum, reduced
--     only when forced, and both its operands check at the ambient
--     demand and add their measures. Here every kind is Kind(&1):
--     Quant, &2 and the meet are absent.
-- (2) THE WHOLE DATA LAYER, which is to say every way bend.ts licenses
--     a SECOND use. This file mechanizes the all-&1 fragment: Many is
--     unspellable, it survives only inside the usage measure, and there
--     it is always a violation. bend.ts instead has a + binder, a + let
--     and a + field, each forming only at Data, and it has PROMOTION:
--     an argument to a q binder checks at demand dem(q, qt) and its
--     measure adds ONCE, UNSCALED (certify-once), so a Lone Data value
--     may enter a + binder and the callee copies it. QTT forbids that
--     -- Atkey scales the argument's measure by the binder's omega, so
--     a 1 never becomes an omega -- and Bend allows it because its
--     default is Lone, where without promotion only closed data would
--     ever be reusable.
--     The price is a NARROWER THEOREM, and it is the reason this
--     divergence is the important one. Term-substitution reduction does
--     not preserve the measure: unfold f(+x) at f(y) and y counts twice
--     under its plain binder. So in bend.ts subject reduction for usage
--     is claimed only for WEAK BY-VALUE reduction of CLOSED terms, the
--     only reduction the machine performs. subject_reduction below is
--     indeed stated at Step .weak with q /= .Many, but over a calculus
--     in which the difficulty cannot arise at all, so it does not
--     witness the shipped language's version of the claim.
--     THREE INVARIANTS OUTSIDE THE CHECKER carry the difference, and
--     nothing here and nothing in bend.ts verifies any of them:
--       (a) no pass duplicates a term -- wnf shares every argument, let
--           value and field in a cell, and the compiler is strict;
--       (b) a type with runtime ownership (File, Socket, Array) is
--           Type, never Data -- a property of what base.bend declares,
--           not a rule the checker enforces;
--       (c) a compiler may drop a copy the source spelled, never add
--           one -- a property of comp.ts.
--     They live in the machine, in the library and in the compiler
--     respectively. Read them as the assumptions they are.
-- (3) check-efq's emptied-context clause: a LIVE context binder at an
--     emptied family admits an empty match with constructors remaining
--     (ctx_dead); the efq rule here demands every constructor peeled.
-- (4) base-native and foreign asserts are live-usable with no body
--     (the b flag, the effect fills); the ref rule here demands a body
--     at live demand — their steps are the backends', not the calculus.
--     Two consequences ride along. base is the only file whose defs
--     carry b, so base alone can build a live recursive CYCLE: the
--     descent test fires only on a self-call (tm.k = lhs.def), and the
--     source-order wall that stops user mutual recursion never sees a
--     b-flagged pending ref. And a bodiless assert is an axiom the
--     checker trusts outright. Neither is covered here.
-- (5) term_compare follows a let-bound variable to its value before
--     comparing; PEq here is syntactic on variables.
-- (6) a definition's arity is read by NORMALIZATION, not syntax.
--     Book.Ok demands d.ty.NAll d.n, a literal All node per parameter,
--     while def_valid takes its binders through tele_unbind and
--     term_check reaches each All the same way. So a def may declare
--     its type as a Ref that merely unfolds to a function type:
--     assert AF: Type / def AF(): Type -> Type / assert id: AF /
--     def id(x): x checks, though NAll 1 (Ref AF) is False.
-- (7) a constructor telescope's parameter binders need not be ERASED.
--     WTele demands .All .None K B for each of the pn parameters, while
--     adt_valid takes each binder's own quantity as given and treats
--     only FIELDS specially, and parse_adt copies the source
--     quantities. So type Box<a: Type> is Type: Wrap{v: a} checks
--     while CtrD.Shape is False. base writes every such parameter
--     erased, so this is user-only ground, and it grants no ownership:
--     Ctr and Mat instantiate the parameters through tele_fill and bind
--     only the ctr.n fields, so the binder is a phantom.
-- (8) the datatype shapes are matched AFTER normalization. STele,
--     AdtD.Shape, FTele, WTele and CtrD.Shape all demand syntactic
--     telescopes, while tele_unbind, tele_head and adt_valid's closing
--     term_wnf accept them normalized — so a family's declared kind may
--     be an alias that unfolds to Data. The alias is itself checked and
--     its normal form is what every field is then checked against, so
--     this is a coverage gap, not a false kind. Same shape as (6).
-- (9) the constructor tip is INSPECTED, not checked. Book.Ok checks the
--     whole constructor telescope against Type, which in particular
--     validates its tip against the family signature; adt_valid checks
--     each domain and then only tests that the normalized tip is the
--     family applied to its own parameters, in order, with an empty
--     residual. A Book built programmatically could give a constructor
--     domains that disagree with its signature and still pass; a PARSED
--     book cannot, since parse_adt builds every constructor telescope
--     from the one params array. Unreachable from a .bend file.
-- (10) the descent check is SKIPPED at dead demand. Guard here is
--     demand-blind: it is structural over the whole body and its ref
--     rule requires j < k, so a bare self-reference fails wherever it
--     sits, and Book.Ok demands Tree unconditionally. term_infer's Ref
--     case tests descent only in the LIVE branch of the demand switch,
--     so a self-reference inside a type, an erased argument, an
--     equality endpoint or a rewrite motive is accepted with no descent
--     at all. This is what makes a negative recursive type definable in
--     bend.ts — R = @-x: R -> Empty — and it is deliberate: rule zero
--     of .devs/WONTFIX.txt states the checker may diverge on any input,
--     there is no termination check on dead code, and a hang accepts
--     nothing. The theorems here simply do not reach such a book.
--
-- ONE ESCAPE HATCH, and it is bend.ts's. An @unsafe def opts out of the
-- wall: its self-calls skip descent (the u flag on lhs) and its binder
-- domains form + at any kind (lhs_kind relaxes Many to Lone), so the
-- walls proved below are NOT unconditional there. It is always
-- disclosed — cli_report prints "with K annotated as unsafe." — so a
-- book that reports a clean verdict uses none, and for those books the
-- list above is the whole of the difference.
--
-- MODELED faithfully: Rwt is
-- the J axiom (two-binder motive: goal P(b, e), body P(a, {==})); the
-- descent skips erased columns (lhs.qs) and a missing quantity counts
-- live; assert is a bodiless def, dead-only — a live reference to an
-- unfilled def is a type error, so progress is claimed at live demand
-- (dead code may be stuck on an axiom, by design); WEAK reference
-- unfolding is arity-gated exactly as term_wnf (a def fires only when
-- its spine reaches full arity; an underapplied or bodiless reference
-- spine is a stuck weak value); conversion has FULL eta for functions
-- (the occ-guarded contraction λ(F 0) → F when 0 is absent in F)
-- together with strength-strong unfolding at any arity (drefS), which
-- realizes term_equal's "a saturating argument can unfold what an
-- underapplied def kept closed" as joinability; a family reference
-- never unfolds through the run machinery — a nullary one steps to
-- its canonical Adt node (aref) and types at Type (the refA rule), a
-- parameterized one is stuck and has NO typing rule (infer-ref
-- rejects a bare family head; D<..> is the one spelling); and the
-- descent is the plain quantity-masked lexicographic strict-subterm
-- comparison.
--
-- QUANTITIES. None | Lone, spelled -x, x on a binder.
--   add  (sequential): None + q = q; a second live use saturates to Many,
--                      which no binder satisfies
--   join (branches):   pointwise max
-- Lone is affine: zero or one live use. A textual occurrence is not
-- usage: dead occurrences cost nothing (a dead premise checks at demand
-- None and its measure is dropped by the rule that checks it). Demands
-- are {None, Lone} only; Many is a measure value, never a demand.
--
-- REDUCTION.
--   beta  ((λ f) a)                     → f[0 := a]
--   let   (let q v; b)                  → b[0 := v]
--   dref  @k·as, |as| = arity           → book[k].body·as   (defs, == term_wnf)
--   drefS @k·as, STRONG only            → book[k].body·as   (any arity)
--   eta   λ(F 0), STRONG, 0 ∉ F         → F[0 := ·]         (functions)
--   aref  @a, a nullary                 → Adt a []          (families; a
--                                         parameterized head is stuck)
--   matc  (Mat a c h m) (Ctr a c)·ps·xs → h·xs              (|ps| = pn, |xs| = fn)
--   matm  (Mat a c h m) (Ctr a' c')·as  → m ((Ctr a' c')·as)  ((a',c') ≠ (a,c))
--   rwt   (Rwt {==} P f)                → f
-- The congruent closure comes at two strengths, one rule set read twice:
-- STRONG may enter any subterm (conversion's reach — Conv is joinability
-- of strong runs); WEAK never enters a binder (Lam body, Let body, All
-- codomain). Values are weak-head: type formers, function values,
-- Adt/Ctr-headed spines, and stuck reference spines (underapplied or
-- bodiless, == term_wnf's break-focus).
--
-- TYPING. One judgment, Check β q Γ t T π: at demand q, t has type T
-- consuming π. The var rule charges the ambient demand at its index;
-- binders validate measured ≤ declared on close; join at Mat branches,
-- add everywhere else. A type position, an erased argument, an equality
-- endpoint or a motive checks dead (demand None); the boundary is
-- sealed: no rule coerces dead to live. Heads (Ref, Adt, Ctr) get their
-- telescope types from the book (a bare nullary family head types at
-- Type, refA) and applications go through the one app
-- rule, whose argument demand is the domain quantity gated by the
-- ambient demand (dem). cnv is the only mode switch.
--
-- DESCENT. Tree β k lhs n t walks definition k's case tree rebuilding
-- the definition's own left-hand side: a Lam binds the next column, a
-- Mat peels the next column into a constructor of fresh fields, and at
-- any leaf Guard β k cols t demands that every self-reference heads a
-- whole call whose arguments compare against the columns EQ..EQ then
-- one strictly-smaller (PLt: a strict subterm one constructor peel
-- deep). References j ≥ k are forbidden outright (the book is ordered),
-- so mutual recursion cannot bypass the wall.
--
-- THE CLAIMS, over any Ok book:
-- (1) confluence of strong reduction; (2) subject reduction along WEAK
-- steps, with the affine measure never growing; (3) progress; (4) weak
-- normalization of closed live terms to a value of their type; (5)
-- consistency: no closed live term inhabits an empty family.
--
-- PROVEN in PART II: claims (1), (2) and (3) are the theorems
-- church_rosser_holds, subject_reduction_holds and progress_holds
-- (progress at live demand: an unfilled assert is stuck by design);
-- and the boundary is a theorem, not an apology:
-- consistency_none_boundary types Curry's omega at an empty family in
-- the DEAD fragment of an Ok book with a negative type, which is
-- exactly why claims (4) and (5) demand Lone. Example books live as
-- .bend files in the repo, checked by bend.ts itself.
--
-- Claims (4) and (5) are PROVEN IN FULL — recursive definitions
-- included — as the theorems normalization_holds and
-- consistency_holds, via the master engine (§NM). The measure is
-- lexicographic: a multiset of CHARGES under the Dershowitz-Manna
-- order (§NO), then the unit weight of the typed live erasure
-- Era β Γ t T u. A charge prices one pending reference by its
-- per-column size tuple plus a slack slot; the charged guard CG (§NC)
-- threads the charges through the erasure. Ordinary interactions
-- (beta, let, match, rwt) keep the charges and strictly drop the
-- weight — the affine beta lands at most one live copy (Era.sub).
-- A reference spend runs the definition's case tree against the
-- call's deepened arguments (Tree.drive, §ND): every leaf reprices
-- its self-calls strictly below the spent tuple, descent columns
-- pinning strictly smaller constructor sizes and the slack slot
-- paying for underapplied suspensions (Tree.suspend). Pinned
-- arguments stay rigid through evaluation because they are settled
-- pairs (PinOk): dead-token junk is never entered, and era-paired
-- deep values (DeepP β) return unchanged from the master. The plain-
-- book specialization survives as normalization_plain (§NZ).
--
-- Layout (the bend.ts order): §1 Types  §2 Quant  §3 Uses  §4 Term
--         §5 Ctx/Book  §6 Compare  §7 Tele  §8 Equal  §9 Check
--         §10 Descent  §11 Valid  §12 Claims — then PART II, the
--         metatheory.
-- ============================================================================

namespace BendCore

-- ============================================================================
-- §1 Types (== bend.ts Types)
-- ============================================================================

inductive Quant : Type
  | None
  | Lone
  | Many
deriving DecidableEq

abbrev Uses := Nat → Quant

inductive Term : Type
  | Var : Nat → Term                          -- x
  | Ref : Nat → Term                          -- @k
  | Typ : Term                                -- Type
  | All : Quant → Term → Term → Term          -- @q x:A -> B   (binds in B)
  | Lam : Term → Term                         -- x => f        (binds)
  | App : Term → Term → Term                  -- f(x)
  | Adt : Nat → List Nat → Term               -- family head, peeled ctrs
  | Ctr : Nat → Nat → Term                    -- constructor head (family, index)
  | Mat : Nat → Nat → Term → Term → Term      -- \{c: h; m}
  | Efq : Term                                -- \{}
  | Eql : Term → Term → Term → Term           -- {a == b : T}
  | Rfl : Term                                -- {==}
  | Rwt : Term → Term → Term → Term           -- %e : P; f
  | Let : Quant → Term → Term → Term          -- q x = v; f    (binds in f)
deriving DecidableEq

-- a definition: n case-tree columns, a closed type, a closed body
structure DefD : Type where
  n    : Nat
  qs   : List Quant
  ty   : Term
  body : Option Term
deriving DecidableEq

-- a constructor: field count and closed telescope type
-- (pn erased parameters, then fn fields, tipped at the family applied
-- to its own parameters — the shape is enforced by Book.Ok)
structure CtrD : Type where
  fn : Nat
  ty : Term
deriving DecidableEq

-- a family: parameter count, closed signature, constructors
structure AdtD : Type where
  pn   : Nat
  sig  : Term
  ctrs : List CtrD
deriving DecidableEq

inductive TLD : Type
  | adt : AdtD → TLD
  | defn : DefD → TLD
deriving DecidableEq

abbrev Book := List TLD

abbrev Ctx := List Term

-- ============================================================================
-- §2 Quant (== bend.ts Quant)
-- ============================================================================

def Quant.add : Quant → Quant → Quant
  | .None, q     => q
  | q,     .None => q
  | _,     _     => .Many

def Quant.join : Quant → Quant → Quant
  | .None, q     => q
  | .Lone, .None => .Lone
  | .Lone, q     => q
  | .Many, _     => .Many

def Quant.le : Quant → Quant → Prop
  | .None, _     => True
  | .Lone, .None => False
  | .Lone, _     => True
  | .Many, .Many => True
  | .Many, _     => False

-- the demand on an argument: an erased domain kills the demand, any
-- other domain passes the ambient demand through (bend.ts quant_dem)
def Quant.dem : Quant → Quant → Quant
  | .None, _  => .None
  | _,     qt => qt

-- ============================================================================
-- §3 Uses (== bend.ts Uses)
-- ============================================================================

def Uses.zero : Uses := fun _ => .None
def Uses.one (i : Nat) (q : Quant) : Uses := fun j => if j = i then q else .None
def Uses.add (a b : Uses) : Uses := fun i => Quant.add (a i) (b i)
def Uses.join (a b : Uses) : Uses := fun i => Quant.join (a i) (b i)
def Uses.tail (a : Uses) : Uses := fun i => a (i + 1)
def Uses.le (a b : Uses) : Prop := ∀ i, Quant.le (a i) (b i)

-- ============================================================================
-- §4 Term (== bend.ts Term: apply/unapply, shift, subst, the
-- lhs algebra; the compare relations follow the Book section, since
-- the Lean relations validate constructor arity against the book)
-- ============================================================================

def Term.apps : Term → List Term → Term
  | f, []      => f
  | f, a :: as => Term.apps (.App f a) as

-- a term is a head (never an App) — spine decompositions are unique
def Term.IsHead : Term → Prop
  | .App _ _ => False
  | _        => True

-- the spine decomposition: t = apps (spine t).1 (spine t).2 with a
-- non-App head
def Term.spine : Term → Term × List Term
  | .App f a => ((Term.spine f).1, (Term.spine f).2 ++ [a])
  | t        => (t, [])

def Term.shift (d : Nat) : Term → Term
  | .Var i         => if i < d then .Var i else .Var (i + 1)
  | .Ref k         => .Ref k
  | .Typ           => .Typ
  | .All q A B     => .All q (Term.shift d A) (Term.shift (d + 1) B)
  | .Lam f         => .Lam (Term.shift (d + 1) f)
  | .App f a       => .App (Term.shift d f) (Term.shift d a)
  | .Adt a r       => .Adt a r
  | .Ctr a c       => .Ctr a c
  | .Mat a c h m   => .Mat a c (Term.shift d h) (Term.shift d m)
  | .Efq           => .Efq
  | .Eql x y T     => .Eql (Term.shift d x) (Term.shift d y) (Term.shift d T)
  | .Rfl           => .Rfl
  | .Rwt e P f     => .Rwt (Term.shift d e) (Term.shift d P) (Term.shift d f)
  | .Let q v f     => .Let q (Term.shift d v) (Term.shift (d + 1) f)

def Term.subst (d : Nat) (w : Term) : Term → Term
  | .Var i         => if i = d then w else if d < i then .Var (i - 1) else .Var i
  | .Ref k         => .Ref k
  | .Typ           => .Typ
  | .All q A B     => .All q (Term.subst d w A) (Term.subst (d + 1) (Term.shift 0 w) B)
  | .Lam f         => .Lam (Term.subst (d + 1) (Term.shift 0 w) f)
  | .App f a       => .App (Term.subst d w f) (Term.subst d w a)
  | .Adt a r       => .Adt a r
  | .Ctr a c       => .Ctr a c
  | .Mat a c h m   => .Mat a c (Term.subst d w h) (Term.subst d w m)
  | .Efq           => .Efq
  | .Eql x y T     => .Eql (Term.subst d w x) (Term.subst d w y) (Term.subst d w T)
  | .Rfl           => .Rfl
  | .Rwt e P f     => .Rwt (Term.subst d w e) (Term.subst d w P) (Term.subst d w f)
  | .Let q v f     => .Let q (Term.subst d w v) (Term.subst (d + 1) (Term.shift 0 w) f)

def Term.Closed : Nat → Term → Prop
  | n, .Var i         => i < n
  | _, .Ref _         => True
  | _, .Typ           => True
  | n, .All _ A B     => A.Closed n ∧ B.Closed (n + 1)
  | n, .Lam f         => f.Closed (n + 1)
  | n, .App f a       => f.Closed n ∧ a.Closed n
  | _, .Adt _ _       => True
  | _, .Ctr _ _       => True
  | n, .Mat _ _ h m   => h.Closed n ∧ m.Closed n
  | _, .Efq           => True
  | n, .Eql a b T     => a.Closed n ∧ b.Closed n ∧ T.Closed n
  | _, .Rfl           => True
  | n, .Rwt e P f     => e.Closed n ∧ P.Closed n ∧ f.Closed n
  | n, .Let _ v f     => v.Closed n ∧ f.Closed (n + 1)

-- the J motive's type: over an equation {a == b : T}, the motive binds
-- the second endpoint and the equation itself
def Term.jmotive (a T : Term) : Term :=
  .All .Lone T (.All .Lone (.Eql (Term.shift 0 a) (.Var 0) (Term.shift 0 T))
    .Typ)

-- the left-hand-side algebra (bend.ts lhs_ext and term_apply)
def Term.applyB : Term → Term → Term
  | .Lam f, a => Term.subst 0 a f
  | f,      a => .App f a

def Term.occ (d : Nat) : Term → Nat
  | .Var i         => if i = d then 1 else 0
  | .Ref _         => 0
  | .Typ           => 0
  | .All _ A B     => Term.occ d A + Term.occ (d + 1) B
  | .Lam f         => Term.occ (d + 1) f
  | .App f a       => Term.occ d f + Term.occ d a
  | .Adt _ _       => 0
  | .Ctr _ _       => 0
  | .Mat _ _ h m   => Nat.max (Term.occ d h) (Term.occ d m)
  | .Efq           => 0
  | .Eql a b T     => Term.occ d a + Term.occ d b + Term.occ d T
  | .Rfl           => 0
  | .Rwt e P f     => Term.occ d e + Term.occ d P + Term.occ d f
  | .Let _ v b     => Term.occ d v + Term.occ (d + 1) b

def Term.shiftN : Nat → Term → Term
  | 0,     t => t
  | n + 1, t => Term.shift 0 (Term.shiftN n t)

def Term.lams : Nat → Term → Term
  | 0,     t => t
  | n + 1, t => .Lam (Term.lams n t)

def Term.rvars : Nat → List Term
  | 0     => []
  | n + 1 => .Var n :: Term.rvars n

def Term.lhsExt (lhs : Term) (a c fn : Nat) : Term :=
  Term.lams fn (Term.applyB (Term.shiftN fn lhs)
    (Term.apps (.Ctr a c) (Term.rvars fn)))

-- ============================================================================
-- §5 Ctx and Book (== bend.ts Ctx, Ctrs, Book)
-- ============================================================================

def Ctx.get : Ctx → Nat → Option Term
  | [], _         => none
  | T :: _, 0     => some (Term.shift 0 T)
  | _ :: Γ, i + 1 => (Ctx.get Γ i).map (Term.shift 0)

def Book.tld : Book → Nat → Option TLD
  | [], _         => none
  | d :: _, 0     => some d
  | _ :: β, k + 1 => Book.tld β k

def Book.adt (β : Book) (a : Nat) : Option AdtD :=
  match Book.tld β a with
  | some (.adt A) => some A
  | _             => none

def Book.defn (β : Book) (k : Nat) : Option DefD :=
  match Book.tld β k with
  | some (.defn d) => some d
  | _              => none

def AdtD.ctr : AdtD → Nat → Option CtrD :=
  fun A c => go A.ctrs c
where go : List CtrD → Nat → Option CtrD
  | [], _         => none
  | C :: _, 0     => some C
  | _ :: cs, c + 1 => go cs c

-- ============================================================================
-- §6 Compare (== bend.ts Compare and the infer-ref
-- descent loop: EQ columns then one strict subterm, erased columns
-- skipped)
-- ============================================================================

mutual
inductive PEq (β : Book) : Term → Term → Prop
  | var : PEq β (.Var i) (.Var i)
  | ctr : Book.adt β a = some A → AdtD.ctr A c = some C →
          ps.length = A.pn → xs.length = C.fn →
          PEqs β xs ys →
          PEq β (Term.apps (.Ctr a c) (ps ++ xs)) (Term.apps (.Ctr a c) ys)
inductive PEqs (β : Book) : List Term → List Term → Prop
  | nil  : PEqs β [] []
  | cons : PEq β x y → PEqs β xs ys → PEqs β (x :: xs) (y :: ys)
end

-- PLt β t p: t is a strict subterm of the pattern p — the same
-- constructor with pointwise <=-fields, at least one strict, or <= some
-- field of p (bend.ts term_compare's LT verdicts)
mutual
inductive PLt (β : Book) : Term → Term → Prop
  | subEq : Book.adt β a = some A → AdtD.ctr A c = some C →
            ys.length = C.fn → y ∈ ys → PEq β t y →
            PLt β t (Term.apps (.Ctr a c) ys)
  | subLt : Book.adt β a = some A → AdtD.ctr A c = some C →
            ys.length = C.fn → y ∈ ys → PLt β t y →
            PLt β t (Term.apps (.Ctr a c) ys)
  | ctr   : Book.adt β a = some A → AdtD.ctr A c = some C →
            ps.length = A.pn → xs.length = C.fn →
            PLts β xs ys →
            PLt β (Term.apps (.Ctr a c) (ps ++ xs)) (Term.apps (.Ctr a c) ys)
inductive PLts (β : Book) : List Term → List Term → Prop
  | here  : PLt β x y → PLes β xs ys → PLts β (x :: xs) (y :: ys)
  | there : PEq β x y → PLts β xs ys → PLts β (x :: xs) (y :: ys)
inductive PLes (β : Book) : List Term → List Term → Prop
  | nil    : PLes β [] []
  | consEq : PEq β x y → PLes β xs ys → PLes β (x :: xs) (y :: ys)
  | consLt : PLt β x y → PLes β xs ys → PLes β (x :: xs) (y :: ys)
end

-- SpineLt β qs j cols args: from column position j on, LIVE columns
-- compare EQ left to right until one is a strict subterm; an erased
-- column is skipped — erased data cannot be matched live and never
-- carries the decrease, only spurious mismatch (bend.ts infer-ref's
-- descent loop with lhs.qs; a missing quantity counts live)
inductive SpineLt (β : Book) (qs : List Quant) : Nat → List Term → List Term → Prop
  | here  : qs.getD j .Lone ≠ .None → PLt β t c →
            SpineLt β qs j (c :: cs) (t :: ts)
  | skip  : qs.getD j .Lone = .None → SpineLt β qs (j + 1) cs ts →
            SpineLt β qs j (c :: cs) (t :: ts)
  | there : qs.getD j .Lone ≠ .None → PEq β t c →
            SpineLt β qs (j + 1) cs ts →
            SpineLt β qs j (c :: cs) (t :: ts)

-- ============================================================================
-- §7 Tele (== bend.ts Tele: telescope shapes)
-- ============================================================================

-- FTele a r ps k T: T is a telescope of k more field binders tipped at
-- the family a (peeled r) applied to the instantiated parameters ps
-- (which shift as binders open)
def FTele (a : Nat) (r : List Nat) : List Term → Nat → Term → Prop
  | ps, 0,     T => T = Term.apps (.Adt a r) ps
  | ps, k + 1, T => ∃ qf F B, T = .All qf F B ∧
      FTele a r (ps.map (Term.shift 0)) k B

-- WTele a r ps pn fn T: T is a telescope of pn more erased parameter
-- binders then fn field binders, tipped at the family applied to the
-- parameters (those already instantiated in ps, then the pn to come)
def WTele (a : Nat) (r : List Nat) : List Term → Nat → Nat → Term → Prop
  | ps, 0,      fn, T => FTele a r ps fn T
  | ps, pn + 1, fn, T => ∃ K B, T = .All .None K B ∧
      WTele a r (ps.map (Term.shift 0) ++ [.Var 0]) pn fn B

-- STele n T: T is a telescope of n binders tipped at Type
-- an n-deep function-type prefix: the shape a definition's declared
-- arity promises of its type (bend.ts builds the type from the tele)
def Term.NAll : Nat → Term → Prop
  | 0, _ => True
  | n + 1, T => ∃ q A B, q ≠ .Many ∧ T = Term.All q A B ∧ Term.NAll n B

def STele : Nat → Term → Prop
  | 0,     T => T = .Typ
  | n + 1, T => ∃ q K B, T = .All q K B ∧ STele n B

-- the constructor telescope shape: pn erased parameters, then fn
-- fields, tipped at the family applied to its own parameters, in order
def CtrD.Shape (a pn : Nat) (C : CtrD) : Prop :=
  WTele a [] [] pn C.fn C.ty

-- the family signature shape: pn parameters tipped at Type
def AdtD.Shape (A : AdtD) : Prop :=
  STele A.pn A.sig



-- ============================================================================
-- §8 Equal (== bend.ts WNF/SNF/Compare: reduction at two strengths;
-- conversion is joinability of strong runs, eta and drefS included
-- — the header's MODELED-faithfully items)
-- ============================================================================

inductive Strength : Type
  | weak
  | strong

inductive Step (β : Book) (p : Strength) : Term → Term → Prop
  | beta  : Step β p (.App (.Lam f) a) (Term.subst 0 a f)
  | let_  : Step β p (.Let q v b) (Term.subst 0 v b)
  | dref  : Book.defn β k = some d → d.body = some b →
            (Term.spine s).1 = .Ref k →
            (Term.spine s).2.length = d.n →
            Step β p s (Term.apps b (Term.spine s).2)
  | drefS : p = .strong → Book.defn β k = some d → d.body = some b →
            (Term.spine s).1 = .Ref k →
            Step β p s (Term.apps b (Term.spine s).2)
  | aref  : Book.adt β k = some A → A.pn = 0 → Step β p (.Ref k) (.Adt k [])
  | matc  : Book.adt β a = some A → AdtD.ctr A c = some C →
            ps.length = A.pn → xs.length = C.fn →
            Step β p (.App (.Mat a c h m) (Term.apps (.Ctr a c) (ps ++ xs)))
                     (Term.apps h xs)
  | matm  : (a', c') ≠ (a, c) →
            Step β p (.App (.Mat a c h m) (Term.apps (.Ctr a' c') as))
                     (.App m (Term.apps (.Ctr a' c') as))
  | rwt   : Step β p (.Rwt .Rfl P f) f
  | eta   : p = .strong → Term.occ 0 F = 0 →
            Step β p (.Lam (.App F (.Var 0))) (Term.subst 0 .Typ F)
  | all_a : p = .strong → Step β p A A' → Step β p (.All q A B) (.All q A' B)
  | all_b : p = .strong → Step β p B B' → Step β p (.All q A B) (.All q A B')
  | lam_f : p = .strong → Step β p f f' → Step β p (.Lam f) (.Lam f')
  | app_f : Step β p f f' → Step β p (.App f a) (.App f' a)
  | app_a : Step β p a a' → Step β p (.App f a) (.App f a')
  | mat_h : Step β p h h' → Step β p (.Mat a c h m) (.Mat a c h' m)
  | mat_m : Step β p m m' → Step β p (.Mat a c h m) (.Mat a c h m')
  | eql_a : Step β p x x' → Step β p (.Eql x y T) (.Eql x' y T)
  | eql_b : Step β p y y' → Step β p (.Eql x y T) (.Eql x y' T)
  | eql_t : Step β p T T' → Step β p (.Eql x y T) (.Eql x y T')
  | rwt_e : Step β p e e' → Step β p (.Rwt e P f) (.Rwt e' P f)
  | rwt_p : Step β p P P' → Step β p (.Rwt e P f) (.Rwt e P' f)
  | rwt_f : Step β p f f' → Step β p (.Rwt e P f) (.Rwt e P f')
  | let_v : Step β p v v' → Step β p (.Let q v b) (.Let q v' b)
  | let_b : p = .strong → Step β p b b' → Step β p (.Let q v b) (.Let q v b')

inductive Red (β : Book) (p : Strength) : Term → Term → Prop
  | refl : Red β p t t
  | step : Step β p a b → Red β p b c → Red β p a c

def Conv (β : Book) (a b : Term) : Prop :=
  ∃ c, Red β .strong a c ∧ Red β .strong b c

theorem Step.strong (s : Step β p a b) : Step β .strong a b := by
  induction s with
  | beta => exact .beta
  | eta _ hocc => exact .eta _root_.rfl hocc
  | drefS _ hk hb hsp => exact .drefS _root_.rfl hk hb hsp
  | let_ => exact .let_
  | dref hk hb hsp hlen => exact .dref hk hb hsp hlen
  | aref hk h0 => exact .aref hk h0
  | matc h1 h2 h3 h4 => exact .matc h1 h2 h3 h4
  | matm h => exact .matm h
  | rwt => exact .rwt
  | all_a _ _ ih => exact .all_a rfl ih
  | all_b _ _ ih => exact .all_b rfl ih
  | lam_f _ _ ih => exact .lam_f rfl ih
  | app_f _ ih => exact .app_f ih
  | app_a _ ih => exact .app_a ih
  | mat_h _ ih => exact .mat_h ih
  | mat_m _ ih => exact .mat_m ih
  | eql_a _ ih => exact .eql_a ih
  | eql_b _ ih => exact .eql_b ih
  | eql_t _ ih => exact .eql_t ih
  | rwt_e _ ih => exact .rwt_e ih
  | rwt_p _ ih => exact .rwt_p ih
  | rwt_f _ ih => exact .rwt_f ih
  | let_v _ ih => exact .let_v ih
  | let_b _ _ ih => exact .let_b rfl ih

theorem Red.strong (r : Red β p a b) : Red β .strong a b := by
  induction r with
  | refl => exact .refl
  | step s _ ih => exact .step s.strong ih

theorem Red.trans (r1 : Red β p a b) (r2 : Red β p b c) : Red β p a c := by
  induction r1 with
  | refl => exact r2
  | step s _ ih => exact .step s (ih r2)

theorem Red.one (s : Step β p a b) : Red β p a b := .step s .refl

-- Adt/Ctr-headed application spines: the constructor-tree values
inductive Spinal : Term → Prop
  | adt : Spinal (.Adt a r)
  | ctr : Spinal (.Ctr a c)
  | app : Spinal f → Spinal (.App f a)

-- weak-head values: a reference kept closed by its arity gate (or by
-- an unfilled assert) is stuck, and stuck is a value (bend.ts wnf
-- breaks focus below arity and on a null body)
inductive Term.Value (β : Book) : Term → Prop
  | typ   : Term.Value β .Typ
  | all   : Term.Value β (.All q A B)
  | lam   : Term.Value β (.Lam f)
  | mat   : Term.Value β (.Mat a c h m)
  | efq   : Term.Value β .Efq
  | eql   : Term.Value β (.Eql a b T)
  | rfl   : Term.Value β .Rfl
  | spine : Spinal t → Term.Value β t
  | stuck : Book.defn β k = some d →
            args.length < d.n ∨ d.body = none →
            Term.Value β (Term.apps (.Ref k) args)

-- ============================================================================
-- §9 Check (== bend.ts Check: one bidirectional judgment; the
-- descent guard follows, mirroring infer-ref's self-call rule and
-- the lhs threading)
-- ============================================================================

-- Insts T ps T': T' is the telescope T with its first |ps| binders
-- instantiated at ps (the constructor's erased parameters, supplied by
-- the goal in bend.ts, spelled in the term here)
inductive Insts : Term → List Term → Term → Prop
  | nil  : Insts T [] T
  | cons : Insts (Term.subst 0 p B) ps T' →
           Insts (.All q A B) (p :: ps) T'

-- MatGoal q' n B s tel G: G is the goal for a match arm handling a
-- constructor with n fields — the instantiated field telescope tel,
-- each field's demand gated by the scrutinee quantity q', tipped at the
-- motive B applied to the constructor spine s rebuilt from the fields
-- (bend.ts term_check_mat_goal)
inductive MatGoal (q' : Quant) : Nat → Term → Term → Term → Term → Prop
  | zero : MatGoal q' 0 B s tel (Term.subst 0 s B)
  | succ : MatGoal q' n (Term.shift 1 B) (.App (Term.shift 0 s) (.Var 0)) Bf G →
           MatGoal q' (n + 1) B s (.All qf F Bf) (.All (Quant.dem qf q') F G)

-- retip r n ty: reannotate the Adt head at the tip of an n-binder
-- telescope with the peeled set r. A constructor checks against the
-- REMAINDER of its family (bend.ts ctrs_find over book_adt's filtered
-- constructors): its head type here carries any peeled set that does
-- not contain it, which is what lets a mismatched scrutinee re-check at
-- the peeled domain of a match's tail.
def Term.retip (r : List Nat) : Nat → Term → Term
  | 0, t =>
    match (Term.spine t).1 with
    | .Adt a _ => Term.apps (.Adt a r) (Term.spine t).2
    | _        => t
  | n + 1, .All q A B => .All q A (Term.retip r n B)
  | _ + 1, t => t

-- Check β q Γ t T π: at demand q, t has type T consuming π. Demands are
-- {None, Lone} only in any derivation rooted at Book.Ok; Many is a
-- measure value. Dead premises (demand None) leave their measure
-- unconstrained — a None-demand derivation only ever measures None
-- (Check.none_uses, PART II) — and the rule that checks a premise dead
-- drops its measure from the conclusion, as in bend.ts.
inductive Check (β : Book) : Quant → Ctx → Term → Term → Uses → Prop
  -- Γ[i] = T
  -- ------------------------- var
  -- Γ ⊢ x_i : T ~ {i : q}
  | var : Ctx.get Γ i = some T →
          Check β q Γ (.Var i) T (Uses.one i q)
  -- β[k] = def(T, v)
  -- ------------------------- ref
  -- Γ ⊢ @k : T ~ {}
  | ref : Book.defn β k = some d →
          (q ≠ .None → d.body ≠ none) →
          Check β q Γ (.Ref k) d.ty Uses.zero
  -- β[k] = adt(sig, cs), nullary: the one bare-head spelling
  -- (a parameterized family head is an error: no rule, and the
  -- run machinery keeps it stuck)
  -- --------------------------------------------------------- ref-adt
  -- Γ ⊢ @k : Type ~ {}
  | refA : Book.adt β k = some A → A.pn = 0 →
           Check β q Γ (.Ref k) .Typ Uses.zero
  -- β[a] = adt(sig, cs)
  -- ------------------------- adt
  -- Γ ⊢ Adt a r : sig ~ {}
  | adt : Book.adt β a = some A →
          Check β q Γ (.Adt a r) A.sig Uses.zero
  -- β[a].cs[c] = ctr(T)    c not peeled by r
  -- ----------------------------------------- ctr
  -- Γ ⊢ Ctr a c : retip r T ~ {}
  | ctr : Book.adt β a = some A → AdtD.ctr A c = some C → c ∉ r →
          Check β q Γ (.Ctr a c) (Term.retip r (A.pn + C.fn) C.ty) Uses.zero
  -- ------------------------- typ
  -- Γ ⊢ Type : Type ~ {}
  | typ : Check β q Γ .Typ .Typ Uses.zero
  -- Γ ⊢ A : Type    Γ, A ⊢ B : Type    (both dead)
  -- where q' is - or plain (a Many binder is rejected at formation)
  -- ------------------------------------------------ all
  -- Γ ⊢ @q' A -> B : Type ~ {}
  | all : q' ≠ .Many →
          Check β .None Γ A .Typ πA →
          Check β .None (A :: Γ) B .Typ πB →
          Check β q Γ (.All q' A B) .Typ Uses.zero
  -- Γ, A ⊢ f : B ~ π    π[0] <= q'
  -- ------------------------------------------------ lam
  -- Γ ⊢ λ f : @q' A -> B ~ tail π
  | lam : Check β q (A :: Γ) f B π →
          Quant.le (π 0) q' →
          Check β q Γ (.Lam f) (.All q' A B) (Uses.tail π)
  -- Γ ⊢ f : @q' A -> B ~ πf    Γ ⊢ x : A ~ πx at demand dem q' q
  -- where q' is not Many (an argument is never scaled: no multiplication)
  -- ------------------------------------------------------------- app
  -- Γ ⊢ f(x) : B[0 := x] ~ πf + πx
  | app : q' ≠ .Many →
          Check β q Γ f (.All q' A B) πf →
          Check β (Quant.dem q' q) Γ x A πx →
          Check β q Γ (.App f x) (Term.subst 0 x B) (Uses.add πf πx)
  -- Γ ⊢ v : A ~ πv at demand dem qb q    Γ, A ⊢ b : T↑ ~ π    π[0] <= qb
  -- where qb is - or plain
  -- ------------------------------------------------------------------- let
  -- Γ ⊢ qb x = v; b : T ~ πv + tail π
  | let_ : qb ≠ .Many →
           Check β (Quant.dem qb q) Γ v A πv →
           Check β q (A :: Γ) b (Term.shift 0 T) π →
           Quant.le (π 0) qb →
           Check β q Γ (.Let qb v b) T (Uses.add πv (Uses.tail π))
  -- Γ ⊢ T : Type    Γ ⊢ a : T    Γ ⊢ b : T    (all dead)
  -- --------------------------------------------------- eql
  -- Γ ⊢ {a == b : T} : Type ~ {}
  | eql : Check β .None Γ T .Typ πT →
          Check β .None Γ a T πa →
          Check β .None Γ b T πb →
          Check β q Γ (.Eql a b T) .Typ Uses.zero
  -- a == b
  -- ------------------------------ rfl
  -- Γ ⊢ {==} : {a == b : T} ~ {}
  | rfl : Conv β a b →
          Check β q Γ .Rfl (.Eql a b T) Uses.zero
  -- Γ ⊢ e : {a == b : T} ~ πe
  -- Γ ⊢ P : @x:T -> @_:{a == x : T} -> Type    (dead; the J motive)
  -- Γ ⊢ f : P(a, {==}) ~ πf
  -- ------------------------------------------ rwt
  -- Γ ⊢ %e : P; f : P(b, e) ~ πe + πf
  | rwt : Check β q Γ e (.Eql a b T) πe →
          Check β .None Γ P (Term.jmotive a T) πP →
          Check β q Γ f (.App (.App P a) .Rfl) πf →
          Check β q Γ (.Rwt e P f) (.App (.App P b) e) (Uses.add πe πf)
  -- β[a].cs[c] : telescope, params instantiated at ps leaving telF
  -- Γ ⊢ h : fields of telF gated by q', tipped at B[Ctr a c · ps · fields] ~ πh
  -- Γ ⊢ m : @q' (Adt a (c :: r)) · ps -> B ~ πm
  -- where c is not already peeled, and q' is live in a live region
  -- --------------------------------------------------------------------- mat
  -- Γ ⊢ \{c: h; m} : @q' (Adt a r) · ps -> B ~ πh | πm
  | mat : Book.adt β a = some A → AdtD.ctr A c = some C →
          c ∉ r → ps.length = A.pn →
          (q ≠ .None → q' ≠ .None) →
          Insts C.ty ps telF →
          MatGoal q' C.fn B (Term.apps (.Ctr a c) ps) telF G →
          Check β q Γ h G πh →
          Check β q Γ m (.All q' (Term.apps (.Adt a (c :: r)) ps) B) πm →
          Check β q Γ (.Mat a c h m) (.All q' (Term.apps (.Adt a r) ps) B)
            (Uses.join πh πm)
  -- every constructor of β[a] is peeled, and q' is live in a live region
  -- --------------------------------------------------------------------- efq
  -- Γ ⊢ \{} : @q' (Adt a r) · ps -> B ~ {}
  | efq : Book.adt β a = some A →
          (∀ c, c < A.ctrs.length → c ∈ r) →
          (q ≠ .None → q' ≠ .None) →
          Check β q Γ .Efq (.All q' (Term.apps (.Adt a r) ps) B) Uses.zero
  -- Γ ⊢ t : A ~ π    A == B
  -- ------------------------ cnv
  -- Γ ⊢ t : B ~ π
  | cnv : Check β q Γ t A π → Conv β A B →
          Check β q Γ t B π

-- ============================================================================
-- §10 Descent (== bend.ts infer-ref self-call + lhs threading:
-- Guard at the leaves, Tree walks the case tree)
-- ============================================================================

-- Guard β k cols t: every reference in t is to an earlier definition,
-- except that @k itself may head a whole call whose arguments descend
-- against the columns (a live self-reference cannot escape as a value,
-- and the book is ordered, so mutual recursion cannot bypass the wall)
inductive Guard (β : Book) (k : Nat) (qs : List Quant) :
    List Term → Term → Prop
  | call : SpineLt β qs 0 cols args →
           (∀ x ∈ args, Guard β k qs cols x) →
           Guard β k qs cols (Term.apps (.Ref k) args)
  | var  : Guard β k qs cols (.Var i)
  | ref  : j < k → Guard β k qs cols (.Ref j)
  | typ  : Guard β k qs cols .Typ
  | all  : Guard β k qs cols A → Guard β k qs (cols.map (Term.shift 0)) B →
           Guard β k qs cols (.All q A B)
  | lam  : Guard β k qs (cols.map (Term.shift 0)) f →
           Guard β k qs cols (.Lam f)
  | app  : Guard β k qs cols f → Guard β k qs cols a →
           Guard β k qs cols (.App f a)
  | adt  : Guard β k qs cols (.Adt a r)
  | ctr  : Guard β k qs cols (.Ctr a c)
  | mat  : Guard β k qs cols h → Guard β k qs cols m →
           Guard β k qs cols (.Mat a c h m)
  | efq  : Guard β k qs cols .Efq
  | eql  : Guard β k qs cols x → Guard β k qs cols y →
           Guard β k qs cols T →
           Guard β k qs cols (.Eql x y T)
  | rfl  : Guard β k qs cols .Rfl
  | rwt  : Guard β k qs cols e → Guard β k qs cols P →
           Guard β k qs cols f →
           Guard β k qs cols (.Rwt e P f)
  | let_ : Guard β k qs cols v →
           Guard β k qs (cols.map (Term.shift 0)) b →
           Guard β k qs cols (.Let q v b)

-- Tree β k lhs n t: the case-tree walk of definition k's body,
-- rebuilding its own equation. n counts the columns still to bind: a
-- Lam binds the next column, a Mat peels it into a constructor of
-- fresh fields, and any leaf whose rebuilt lhs is a whole spine hands
-- over to Guard.
inductive Tree (β : Book) (k : Nat) (qs : List Quant) :
    Term → Nat → Term → Prop
  | bod : Guard β k qs cols t →
          Tree β k qs (Term.apps (.Ref k) cols) n t
  | lam : 0 < n →
          Tree β k qs (Term.applyB (Term.shift 0 lhs) (.Var 0)) (n - 1) f →
          Tree β k qs lhs n (.Lam f)
  | mat : 0 < n → Book.adt β a = some A → AdtD.ctr A c = some C →
          Tree β k qs (Term.lhsExt lhs a c C.fn) (n - 1 + C.fn) h →
          Tree β k qs lhs n m →
          Tree β k qs lhs n (.Mat a c h m)

-- PEq β t p: argument t matches column pattern p exactly. A pattern is a
-- variable or a constructor of patterns; constructor PATTERNS carry
-- fields only (they are built by the tree walk), while constructor
-- ARGUMENTS carry their erased parameters, which the comparison skips.
-- Both sides pin their field-list arity to the declared C.fn: bend.ts
-- constructor nodes are n-ary and always full, and the spine encoding
-- must say so explicitly.
-- ============================================================================
-- §11 Valid (== bend.ts Valid: book_valid)
-- ============================================================================

-- Book.Ok: each family's signature and constructor telescopes check
-- dead against Type and have the declared shape; each definition's type
-- checks dead against Type, its body checks LIVE against its type, and
-- its case tree descends. Guard forbids references at or beyond k
-- inside bodies, so a forward reference fails and mutual recursion
-- cannot bypass the wall.
def Book.Ok (β : Book) : Prop :=
  ∀ k t, Book.tld β k = some t →
    match t with
    | .adt A =>
        (∃ π, Check β .None [] A.sig .Typ π) ∧ A.Shape ∧
        ∀ c C, AdtD.ctr A c = some C →
          (∃ π, Check β .None [] C.ty .Typ π) ∧ CtrD.Shape k A.pn C
    | .defn d =>
        (∃ π, Check β .None [] d.ty .Typ π) ∧
        d.ty.NAll d.n ∧
        (∀ b, d.body = some b →
          (∃ π, Check β .Lone [] b d.ty π) ∧
          Tree β k d.qs (.Ref k) d.n b)

-- ============================================================================
-- §12 Claims (bend.ts states these in prose; §NZ/§NM prove them)
-- ============================================================================

def church_rosser : Prop :=
  ∀ (β : Book) (a b c : Term),
    Book.Ok β → Red β .strong a b → Red β .strong a c →
    ∃ d, Red β .strong b d ∧ Red β .strong c d

def subject_reduction : Prop :=
  ∀ (β : Book) (q : Quant) (Γ : Ctx) (t t' T : Term) (π : Uses),
    Book.Ok β → q ≠ .Many → Check β q Γ t T π → Step β .weak t t' →
    ∃ π', Uses.le π' π ∧ Check β q Γ t' T π'

def progress : Prop :=
  ∀ (β : Book) (q : Quant) (t T : Term) (π : Uses),
    Book.Ok β → q ≠ .None → Check β q [] t T π →
    Term.Value β t ∨ ∃ t', Step β .weak t t'

def normalization : Prop :=
  ∀ (β : Book) (t T : Term) (π : Uses),
    Book.Ok β → Check β .Lone [] t T π →
    ∃ v π', Red β .weak t v ∧ Term.Value β v ∧ Check β .Lone [] v T π'

def consistency : Prop :=
  ∀ (β : Book) (a : Nat) (A : AdtD) (r : List Nat) (ps : List Term)
    (t : Term) (π : Uses),
    Book.Ok β → Book.adt β a = some A → A.ctrs = [] →
    ¬ Check β .Lone [] t (Term.apps (.Adt a r) ps) π

end BendCore

-- ============================================================================
-- ============================================================================
--
-- PART II — THE METATHEORY
--
-- Everything below proves the claims of §12, and the
-- witnesses. Nothing below is needed to READ the language; nothing
-- above depends on anything below.
--
-- ============================================================================
-- ============================================================================

-- ============================================================================
-- METATHEORY §A — the de Bruijn algebra of Term.shift / Term.subst
-- ============================================================================

theorem getD_append_left {d0 : α} : ∀ (l1 l2 : List α) (j : Nat),
    j < l1.length → (l1 ++ l2).getD j d0 = l1.getD j d0 := by
  intro l1
  induction l1 with
  | nil => intro l2 j hj; simp at hj
  | cons x xs ih =>
    intro l2 j hj
    cases j with
    | zero => rfl
    | succ j =>
      show (xs ++ l2).getD j d0 = xs.getD j d0
      exact ih l2 j (by simp only [List.length_cons] at hj; omega)


theorem getD_append_right {d0 : α} : ∀ (l1 l2 : List α) (j : Nat),
    (l1 ++ l2).getD (l1.length + j) d0 = l2.getD j d0 := by
  intro l1
  induction l1 with
  | nil =>
    intro l2 j
    simp only [List.nil_append, List.length_nil, Nat.zero_add]
  | cons x xs ih =>
    intro l2 j
    simp only [List.cons_append, List.length_cons]
    rw [show xs.length + 1 + j = (xs.length + j) + 1 from by omega]
    show (xs ++ l2).getD (xs.length + j) d0 = l2.getD j d0
    exact ih l2 j

theorem getD_mem {dft : α} : ∀ (l : List α) (i : Nat), i < l.length →
    l.getD i dft ∈ l := by
  intro l
  induction l with
  | nil => intro i hi; exact absurd hi (by simp)
  | cons x xs ih =>
    intro i hi
    cases i with
    | zero => exact List.mem_cons_self
    | succ i =>
      refine List.mem_cons_of_mem x ?_
      exact ih i (by simp only [List.length_cons] at hi; omega)


theorem map_getD (f : α → γ) (d0 : γ) (d1 : α) :
    ∀ (l : List α) (j : Nat), j < l.length →
    (l.map f).getD j d0 = f (l.getD j d1) := by
  intro l
  induction l with
  | nil => intro j hj; exact absurd hj (by simp)
  | cons x xs ih =>
    intro j hj
    cases j with
    | zero => rfl
    | succ j =>
      exact ih j (by simp only [List.length_cons] at hj; omega)

namespace BendCore

theorem Term.shift_shift (t : Term) : ∀ (d e : Nat), d ≤ e →
    (t.shift e).shift d = (t.shift d).shift (e + 1) := by
  induction t <;> intro d e h
  case Var i =>
    simp only [Term.shift]
    repeat' split
    all_goals try simp only [Term.shift]
    repeat' split
    all_goals first
    | rfl
    | (exfalso; omega)
    | (simp only [Term.Var.injEq]; omega)
  all_goals simp [Term.shift, *, Nat.succ_le_succ h]

theorem Term.shift_shift0 (t : Term) (d : Nat) :
    Term.shift (d + 1) (Term.shift 0 t) = Term.shift 0 (Term.shift d t) :=
  (Term.shift_shift t 0 d (Nat.zero_le d)).symm

theorem Term.subst_shift (t : Term) : ∀ (d : Nat) (w : Term),
    Term.subst d w (t.shift d) = t := by
  induction t <;> intro d w
  case Var i =>
    simp only [Term.shift]
    repeat' split
    all_goals try simp only [Term.subst]
    repeat' split
    all_goals first
    | rfl
    | (exfalso; omega)
    | (simp only [Term.Var.injEq]; omega)
  all_goals simp [Term.shift, Term.subst, *]


theorem Term.shift_subst_lt (t : Term) : ∀ (d e : Nat) (w : Term), d ≤ e →
    (Term.subst e w t).shift d = Term.subst (e + 1) (w.shift d) (t.shift d) := by
  induction t <;> intro d e w h
  case Var i =>
    simp only [Term.subst]
    repeat' split
    all_goals try simp only [Term.shift]
    repeat' split
    all_goals try simp only [Term.subst]
    repeat' split
    all_goals first
    | rfl
    | (exfalso; omega)
    | (simp only [Term.Var.injEq]; omega)
  all_goals simp [Term.shift, Term.subst, Term.shift_shift, *, Nat.succ_le_succ h]

theorem Term.shift_jmotive (a T : Term) (d : Nat) :
    Term.shift d (Term.jmotive a T)
      = Term.jmotive (Term.shift d a) (Term.shift d T) := by
  show Term.All .Lone (Term.shift d T)
      (.All .Lone (.Eql (Term.shift (d + 1) (Term.shift 0 a)) (.Var 0)
        (Term.shift (d + 1) (Term.shift 0 T))) .Typ)
    = Term.All .Lone (Term.shift d T)
      (.All .Lone (.Eql (Term.shift 0 (Term.shift d a)) (.Var 0)
        (Term.shift 0 (Term.shift d T))) .Typ)
  rw [Term.shift_shift0, Term.shift_shift0]

theorem Term.subst_jmotive (a T : Term) (d : Nat) (w : Term) :
    Term.subst d w (Term.jmotive a T)
      = Term.jmotive (Term.subst d w a) (Term.subst d w T) := by
  show Term.All .Lone (Term.subst d w T)
      (.All .Lone (.Eql (Term.subst (d + 1) (Term.shift 0 w)
          (Term.shift 0 a)) (.Var 0)
        (Term.subst (d + 1) (Term.shift 0 w) (Term.shift 0 T))) .Typ)
    = Term.All .Lone (Term.subst d w T)
      (.All .Lone (.Eql (Term.shift 0 (Term.subst d w a)) (.Var 0)
        (Term.shift 0 (Term.subst d w T))) .Typ)
  rw [← Term.shift_subst_lt a 0 d w (Nat.zero_le d),
    ← Term.shift_subst_lt T 0 d w (Nat.zero_le d)]

theorem Term.shift_subst_ge (t : Term) : ∀ (d e : Nat) (w : Term), e ≤ d →
    (Term.subst e w t).shift d = Term.subst e (w.shift d) (t.shift (d + 1)) := by
  induction t <;> intro d e w h
  case Var i =>
    simp only [Term.subst]
    repeat' split
    all_goals try simp only [Term.shift]
    repeat' split
    all_goals try simp only [Term.subst]
    repeat' split
    all_goals first
    | rfl
    | (exfalso; omega)
    | (simp only [Term.Var.injEq]; omega)
  all_goals simp [Term.shift, Term.subst, Term.shift_shift, *, Nat.succ_le_succ h]

theorem Term.subst_subst (t : Term) : ∀ (d e : Nat) (w u : Term), e ≤ d →
    Term.subst d w (Term.subst e u t)
      = Term.subst e (Term.subst d w u) (Term.subst (d + 1) (w.shift e) t) := by
  induction t <;> intro d e w u h
  case Var i =>
    simp only [Term.subst]
    repeat' split
    all_goals try simp only [Term.subst, Term.subst_shift]
    repeat' split
    all_goals first
    | rfl
    | (exfalso; omega)
    | (simp only [Term.Var.injEq]; omega)
  all_goals simp [Term.subst, Term.shift_shift, Term.shift_subst_lt,
                  *, Nat.succ_le_succ h]

theorem Term.shift_subst0 (t w : Term) (d : Nat) :
    (Term.subst 0 w t).shift d = Term.subst 0 (w.shift d) (t.shift (d + 1)) :=
  Term.shift_subst_ge t d 0 w (Nat.zero_le d)

theorem Term.subst_subst0 (t w u : Term) (d : Nat) :
    Term.subst d w (Term.subst 0 u t)
      = Term.subst 0 (Term.subst d w u) (Term.subst (d + 1) (w.shift 0) t) :=
  Term.subst_subst t d 0 w u (Nat.zero_le d)

theorem Term.Closed.mono (t : Term) : ∀ (n m : Nat), t.Closed n → n ≤ m →
    t.Closed m := by
  induction t <;> intro n m hc h <;> simp only [Term.Closed] at *
  case Var => omega
  case All ihA ihB => exact ⟨ihA n m hc.1 h, ihB (n+1) (m+1) hc.2 (by omega)⟩
  case Lam ihf => exact ihf (n+1) (m+1) hc (by omega)
  case App ihf iha => exact ⟨ihf n m hc.1 h, iha n m hc.2 h⟩
  case Mat ihh ihm => exact ⟨ihh n m hc.1 h, ihm n m hc.2 h⟩
  case Eql iha ihb ihT =>
    exact ⟨iha n m hc.1 h, ihb n m hc.2.1 h, ihT n m hc.2.2 h⟩
  case Rwt ihe ihP ihf =>
    exact ⟨ihe n m hc.1 h, ihP n m hc.2.1 h, ihf n m hc.2.2 h⟩
  case Let ihv ihb => exact ⟨ihv n m hc.1 h, ihb (n+1) (m+1) hc.2 (by omega)⟩

theorem Term.shift_closed (t : Term) : ∀ (n d : Nat), t.Closed n → n ≤ d →
    t.shift d = t := by
  induction t <;> intro n d hc h <;> simp only [Term.Closed] at hc <;>
    simp only [Term.shift]
  case Var => rw [if_pos (by omega)]
  case All ihA ihB =>
    rw [ihA n d hc.1 h, ihB (n+1) (d+1) hc.2 (by omega)]
  case Lam ihf => rw [ihf (n+1) (d+1) hc (by omega)]
  case App ihf iha => rw [ihf n d hc.1 h, iha n d hc.2 h]
  case Mat ihh ihm => rw [ihh n d hc.1 h, ihm n d hc.2 h]
  case Eql iha ihb ihT =>
    rw [iha n d hc.1 h, ihb n d hc.2.1 h, ihT n d hc.2.2 h]
  case Rwt ihe ihP ihf =>
    rw [ihe n d hc.1 h, ihP n d hc.2.1 h, ihf n d hc.2.2 h]
  case Let ihv ihb =>
    rw [ihv n d hc.1 h, ihb (n+1) (d+1) hc.2 (by omega)]

theorem Term.occ_closed : ∀ (t : Term) (n d : Nat), t.Closed n → n ≤ d →
    Term.occ d t = 0 := by
  intro t
  induction t <;> intro n d hc hle <;>
    simp only [Term.occ, Term.Closed] at *
  case Var i => rw [if_neg (by omega)]
  case All ihA ihB =>
    rw [ihA n d hc.1 hle, ihB (n + 1) (d + 1) hc.2 (by omega)]
  case Lam ihf => exact ihf (n + 1) (d + 1) hc (by omega)
  case App ihf iha => rw [ihf n d hc.1 hle, iha n d hc.2 hle]
  case Mat ihh ihm =>
    rw [ihh n d hc.1 hle, ihm n d hc.2 hle]
    rfl
  case Eql iha ihb ihT =>
    rw [iha n d hc.1 hle, ihb n d hc.2.1 hle, ihT n d hc.2.2 hle]
  case Rwt ihe ihP ihf =>
    rw [ihe n d hc.1 hle, ihP n d hc.2.1 hle, ihf n d hc.2.2 hle]
  case Let ihv ihb =>
    rw [ihv n d hc.1 hle, ihb (n + 1) (d + 1) hc.2 (by omega)]

theorem Term.occ_subst_closed (hw : w.Closed 0) :
    ∀ (u : Term) (d i : Nat), i < d →
    Term.occ i (Term.subst d w u) = Term.occ i u := by
  intro u
  induction u <;> intro d i hid <;>
    simp only [Term.subst, Term.occ]
  case Var j =>
    by_cases h1 : j = d
    · rw [if_pos h1]
      rw [Term.occ_closed w 0 i hw (Nat.zero_le i)]
      rw [if_neg (by omega)]
    · rw [if_neg h1]
      by_cases h2 : d < j
      · rw [if_pos h2]
        simp only [Term.occ]
        rw [if_neg (by omega), if_neg (by omega)]
      · rw [if_neg h2]
        rfl
  case All ihA ihB =>
    rw [ihA d i hid,
      show Term.shift 0 w = w from Term.shift_closed w 0 0 hw (Nat.le_refl 0),
      ihB (d + 1) (i + 1) (by omega)]
  case Lam ihf =>
    rw [show Term.shift 0 w = w from Term.shift_closed w 0 0 hw (Nat.le_refl 0),
      ihf (d + 1) (i + 1) (by omega)]
  case App ihf iha => rw [ihf d i hid, iha d i hid]
  case Mat ihh ihm => rw [ihh d i hid, ihm d i hid]
  case Eql iha ihb ihT =>
    rw [iha d i hid, ihb d i hid, ihT d i hid]
  case Rwt ihe ihP ihf =>
    rw [ihe d i hid, ihP d i hid, ihf d i hid]
  case Let ihv ihb =>
    rw [ihv d i hid,
      show Term.shift 0 w = w from Term.shift_closed w 0 0 hw (Nat.le_refl 0),
      ihb (d + 1) (i + 1) (by omega)]

theorem Term.occ_shift_ge : ∀ (t : Term) (d e : Nat), e ≤ d →
    Term.occ (d + 1) (Term.shift e t) = Term.occ d t := by
  intro t
  induction t <;> intro d e he
  case Var i =>
    simp only [Term.shift]
    by_cases h1 : i < e
    · rw [if_pos h1]
      simp only [Term.occ]
      split <;> (try split) <;> omega
    · rw [if_neg h1]
      simp only [Term.occ]
      split <;> (try split) <;> omega
  all_goals simp [Term.shift, Term.occ, *, Nat.succ_le_succ he]

theorem Term.occ_apps (d : Nat) : ∀ (as : List Term) (f : Term),
    Term.occ d (Term.apps f as) = Term.occ d f + (as.map (Term.occ d)).sum := by
  intro as
  induction as with
  | nil => intro f; simp [Term.apps]
  | cons x xs ih =>
    intro f
    show Term.occ d (Term.apps (.App f x) xs) = _
    rw [ih (.App f x)]
    simp only [Term.occ, List.map, List.sum_cons]
    omega

-- substitution of a closed-value environment at depth d, one value at
-- a time — exactly the shape the drive's betas leave behind
def Term.msubstAt (d : Nat) : List Term → Term → Term
  | [],      t => t
  | v :: vs, t => Term.msubstAt d vs (Term.subst d v t)

theorem Term.occ_shift_lt : ∀ (t : Term) (i e : Nat), i < e →
    Term.occ i (Term.shift e t) = Term.occ i t := by
  intro t
  induction t <;> intro i e hie
  case Var j =>
    simp only [Term.shift]
    by_cases h1 : j < e
    · rw [if_pos h1]
    · rw [if_neg h1]
      simp only [Term.occ]
      rw [if_neg (by omega), if_neg (by omega)]
  all_goals simp [Term.shift, Term.occ, *, Nat.succ_lt_succ hie]

theorem Term.occ_shift_self : ∀ (t : Term) (e : Nat),
    Term.occ e (Term.shift e t) = 0 := by
  intro t
  induction t <;> intro e
  case Var j =>
    simp only [Term.shift]
    by_cases h1 : j < e
    · rw [if_pos h1]
      simp only [Term.occ]
      rw [if_neg (by omega)]
    · rw [if_neg h1]
      simp only [Term.occ]
      rw [if_neg (by omega)]
  all_goals simp [Term.shift, Term.occ, *]

-- occurrence bookkeeping for the eta rule: substitution at or above an
-- absent variable keeps it absent, and substituting an unused slot is
-- indifferent to the payload
theorem Term.occ_subst_lt_zero : ∀ (t : Term) (e i : Nat) (w : Term),
    i < e → Term.occ i t = 0 → Term.occ i w = 0 →
    Term.occ i (Term.subst e w t) = 0 := by
  intro t
  induction t <;> intro e i w hie ht hw <;>
    simp only [Term.subst, Term.occ] at ht ⊢
  case Var j =>
    by_cases h1 : j = e
    · rw [if_pos h1]; exact hw
    · rw [if_neg h1]
      by_cases h2 : e < j
      · rw [if_pos h2]
        simp only [Term.occ]
        rw [if_neg (by omega)]
      · rw [if_neg h2]
        simp only [Term.occ] at ht ⊢
        exact ht
  case All ihA ihB =>
    rw [ihA e i w hie (by omega) hw,
      ihB (e + 1) (i + 1) (Term.shift 0 w) (by omega) (by omega)
        (by rw [Term.occ_shift_ge w i 0 (Nat.zero_le i)]; exact hw)]
  case Lam ihf =>
    rw [ihf (e + 1) (i + 1) (Term.shift 0 w) (by omega) ht
      (by rw [Term.occ_shift_ge w i 0 (Nat.zero_le i)]; exact hw)]
  case App ihf iha =>
    rw [ihf e i w hie (by omega) hw, iha e i w hie (by omega) hw]
  case Mat ihh ihm =>
    rw [Nat.max_eq_zero_iff] at ht
    rw [ihh e i w hie (by omega) hw, ihm e i w hie (by omega) hw]
    simp
  case Eql iha ihb ihT =>
    rw [iha e i w hie (by omega) hw, ihb e i w hie (by omega) hw,
      ihT e i w hie (by omega) hw]
  case Rwt ihe ihP ihf =>
    rw [ihe e i w hie (by omega) hw, ihP e i w hie (by omega) hw,
      ihf e i w hie (by omega) hw]
  case Let ihv ihb =>
    rw [ihv e i w hie (by omega) hw,
      ihb (e + 1) (i + 1) (Term.shift 0 w) (by omega) (by omega)
        (by rw [Term.occ_shift_ge w i 0 (Nat.zero_le i)]; exact hw)]

theorem Term.occ_subst_zero : ∀ (t : Term) (e i : Nat) (w : Term),
    e ≤ i → Term.occ (i + 1) t = 0 → Term.occ i w = 0 →
    Term.occ i (Term.subst e w t) = 0 := by
  intro t
  induction t <;> intro e i w hei ht hw <;>
    simp only [Term.subst, Term.occ] at ht ⊢
  case Var j =>
    have hj : j ≠ i + 1 := by
      intro hj
      rw [if_pos hj] at ht
      simp at ht
    by_cases h1 : j = e
    · rw [if_pos h1]; exact hw
    · rw [if_neg h1]
      by_cases h2 : e < j
      · rw [if_pos h2]
        simp only [Term.occ]
        rw [if_neg (by omega)]
      · rw [if_neg h2]
        simp only [Term.occ]
        rw [if_neg (by omega)]
  case All ihA ihB =>
    rw [ihA e i w hei (by omega) hw,
      ihB (e + 1) (i + 1) (Term.shift 0 w) (by omega) (by omega)
        (by rw [Term.occ_shift_ge w i 0 (Nat.zero_le i)]; exact hw)]
  case Lam ihf =>
    rw [ihf (e + 1) (i + 1) (Term.shift 0 w) (by omega) ht
      (by rw [Term.occ_shift_ge w i 0 (Nat.zero_le i)]; exact hw)]
  case App ihf iha =>
    rw [ihf e i w hei (by omega) hw, iha e i w hei (by omega) hw]
  case Mat ihh ihm =>
    rw [Nat.max_eq_zero_iff] at ht
    rw [ihh e i w hei (by omega) hw, ihm e i w hei (by omega) hw]
    simp
  case Eql iha ihb ihT =>
    rw [iha e i w hei (by omega) hw, ihb e i w hei (by omega) hw,
      ihT e i w hei (by omega) hw]
  case Rwt ihe ihP ihf =>
    rw [ihe e i w hei (by omega) hw, ihP e i w hei (by omega) hw,
      ihf e i w hei (by omega) hw]
  case Let ihv ihb =>
    rw [ihv e i w hei (by omega) hw,
      ihb (e + 1) (i + 1) (Term.shift 0 w) (by omega) (by omega)
        (by rw [Term.occ_shift_ge w i 0 (Nat.zero_le i)]; exact hw)]

theorem Term.occ_zero_subst_irrel : ∀ (t : Term) (e : Nat) (w w' : Term),
    Term.occ e t = 0 → Term.subst e w t = Term.subst e w' t := by
  intro t
  induction t <;> intro e w w' ht <;>
    simp only [Term.subst, Term.occ] at ht ⊢
  case Var j =>
    by_cases h1 : j = e
    · exfalso
      rw [if_pos h1] at ht
      simp at ht
    · rw [if_neg h1, if_neg h1]
  case All ihA ihB =>
    rw [ihA e w w' (by omega),
      ihB (e + 1) (Term.shift 0 w) (Term.shift 0 w') (by omega)]
  case Lam ihf => rw [ihf (e + 1) (Term.shift 0 w) (Term.shift 0 w') ht]
  case App ihf iha => rw [ihf e w w' (by omega), iha e w w' (by omega)]
  case Mat ihh ihm =>
    rw [Nat.max_eq_zero_iff] at ht
    rw [ihh e w w' (by omega), ihm e w w' (by omega)]
  case Eql iha ihb ihT =>
    rw [iha e w w' (by omega), ihb e w w' (by omega), ihT e w w' (by omega)]
  case Rwt ihe ihP ihf =>
    rw [ihe e w w' (by omega), ihP e w w' (by omega), ihf e w w' (by omega)]
  case Let ihv ihb =>
    rw [ihv e w w' (by omega),
      ihb (e + 1) (Term.shift 0 w) (Term.shift 0 w') (by omega)]

theorem Term.subst_var_eq_subst_above : ∀ (t : Term) (d : Nat) (w : Term),
    Term.occ (d + 1) t = 0 →
    Term.subst d (.Var d) t = Term.subst (d + 1) w t := by
  intro t
  induction t <;> intro d w ht <;>
    simp only [Term.subst, Term.occ] at ht ⊢
  case Var j =>
    have hj : j ≠ d + 1 := by
      intro he
      rw [if_pos he] at ht
      simp at ht
    by_cases h1 : j = d
    · rw [if_pos h1, if_neg (by omega), if_neg (by omega), h1]
    · rw [if_neg h1]
      by_cases h2 : d < j
      · rw [if_pos h2, if_neg (by omega), if_pos (by omega)]
      · rw [if_neg h2, if_neg (by omega), if_neg (by omega)]
  case All ihA ihB =>
    rw [ihA d w (by omega)]
    have hs : Term.shift 0 (Term.Var d) = .Var (d + 1) := by
      simp only [Term.shift]
      rw [if_neg (by omega)]
    rw [hs, ihB (d + 1) (Term.shift 0 w) (by omega)]
  case Lam ihf =>
    have hs : Term.shift 0 (Term.Var d) = .Var (d + 1) := by
      simp only [Term.shift]
      rw [if_neg (by omega)]
    rw [hs, ihf (d + 1) (Term.shift 0 w) ht]
  case App ihf iha => rw [ihf d w (by omega), iha d w (by omega)]
  case Mat ihh ihm =>
    rw [Nat.max_eq_zero_iff] at ht
    rw [ihh d w (by omega), ihm d w (by omega)]
  case Eql iha ihb ihT =>
    rw [iha d w (by omega), ihb d w (by omega), ihT d w (by omega)]
  case Rwt ihe ihP ihf =>
    rw [ihe d w (by omega), ihP d w (by omega), ihf d w (by omega)]
  case Let ihv ihb =>
    rw [ihv d w (by omega)]
    have hs : Term.shift 0 (Term.Var d) = .Var (d + 1) := by
      simp only [Term.shift]
      rw [if_neg (by omega)]
    rw [hs, ihb (d + 1) (Term.shift 0 w) (by omega)]


theorem Term.subst_closed (t : Term) : ∀ (n d : Nat) (w : Term), t.Closed n →
    n ≤ d → Term.subst d w t = t := by
  induction t <;> intro n d w hc h <;> simp only [Term.Closed] at hc <;>
    simp only [Term.subst]
  case Var => rw [if_neg (by omega), if_neg (by omega)]
  case All ihA ihB =>
    rw [ihA n d w hc.1 h, ihB (n+1) (d+1) (w.shift 0) hc.2 (by omega)]
  case Lam ihf => rw [ihf (n+1) (d+1) (w.shift 0) hc (by omega)]
  case App ihf iha => rw [ihf n d w hc.1 h, iha n d w hc.2 h]
  case Mat ihh ihm => rw [ihh n d w hc.1 h, ihm n d w hc.2 h]
  case Eql iha ihb ihT =>
    rw [iha n d w hc.1 h, ihb n d w hc.2.1 h, ihT n d w hc.2.2 h]
  case Rwt ihe ihP ihf =>
    rw [ihe n d w hc.1 h, ihP n d w hc.2.1 h, ihf n d w hc.2.2 h]
  case Let ihv ihb =>
    rw [ihv n d w hc.1 h, ihb (n+1) (d+1) (w.shift 0) hc.2 (by omega)]

-- ============================================================================
-- METATHEORY §A2 — the spine kit: Term.apps algebra and inversion.
-- Constructor values are Adt/Ctr-headed application spines; these are
-- the lemmas that let the redex rules (matc, matm) and the canonical-
-- form arguments decompose them.
-- ============================================================================

theorem Term.apps_append (f : Term) (xs ys : List Term) :
    Term.apps f (xs ++ ys) = Term.apps (Term.apps f xs) ys := by
  induction xs generalizing f with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, Term.apps, ih]

theorem Term.apps_snoc (f : Term) (xs : List Term) (x : Term) :
    Term.apps f (xs ++ [x]) = .App (Term.apps f xs) x := by
  rw [Term.apps_append]; rfl

theorem getD_take {d0 : α} : ∀ (l : List α) (m i : Nat), i < m →
    (l.take m).getD i d0 = l.getD i d0 := by
  intro l
  induction l with
  | nil => intro m i _; simp [List.take]
  | cons x xs ih =>
    intro m i him
    cases m with
    | zero => omega
    | succ m =>
      cases i with
      | zero => rfl
      | succ i =>
        show (xs.take m).getD i d0 = xs.getD i d0
        exact ih m i (by omega)

theorem take_getD_self (d0 : α) : ∀ (l : List α) (m : Nat),
    l.length = m + 1 → l.take m ++ [l.getD m d0] = l := by
  intro l
  induction l with
  | nil => intro m h; simp at h
  | cons x xs ih =>
    intro m h
    cases m with
    | zero =>
      simp only [List.length_cons] at h
      cases xs with
      | nil => rfl
      | cons y ys => simp at h
    | succ m =>
      show x :: (xs.take m ++ [xs.getD m d0]) = x :: xs
      rw [ih m (by simp only [List.length_cons] at h; omega)]


theorem Term.shift_apps (d : Nat) (f : Term) (xs : List Term) :
    Term.shift d (Term.apps f xs)
      = Term.apps (Term.shift d f) (xs.map (Term.shift d)) := by
  induction xs generalizing f with
  | nil => rfl
  | cons x xs ih => simp only [Term.apps, List.map, ih, Term.shift]

theorem Term.subst_apps (d : Nat) (w f : Term) (xs : List Term) :
    Term.subst d w (Term.apps f xs)
      = Term.apps (Term.subst d w f) (xs.map (Term.subst d w)) := by
  induction xs generalizing f with
  | nil => rfl
  | cons x xs ih => simp only [Term.apps, List.map, ih, Term.subst]

theorem Term.subst_apps_closed (d : Nat) (w : Term) {b : Term}
    (hbc : b.Closed 0) : ∀ (xs : List Term),
    Term.subst d w (Term.apps b xs) = Term.apps b (xs.map (Term.subst d w)) := by
  intro xs
  rw [Term.subst_apps, Term.subst_closed b 0 d w hbc (Nat.zero_le d)]



theorem Term.spine_apps_of (g : Term) :
    ∀ (xs : List Term), Term.spine (Term.apps g xs)
      = ((Term.spine g).1, (Term.spine g).2 ++ xs) := by
  intro xs
  induction xs generalizing g with
  | nil => simp [Term.apps]
  | cons x rest ih =>
    show Term.spine (Term.apps (.App g x) rest) = _
    rw [ih (.App g x)]
    simp [Term.spine]

theorem Term.spine_apps {h : Term} (hh : h.IsHead) (xs : List Term) :
    Term.spine (Term.apps h xs) = (h, xs) := by
  have hs : Term.spine h = (h, []) := by
    cases h <;> first
    | rfl
    | exact absurd hh (by simp [Term.IsHead])
  rw [Term.spine_apps_of h xs, hs]
  simp

theorem Term.apps_spine : ∀ (t : Term),
    Term.apps (Term.spine t).1 (Term.spine t).2 = t := by
  intro t
  induction t <;> try rfl
  case App f a ihf _ =>
    show Term.apps (Term.spine f).1 ((Term.spine f).2 ++ [a]) = _
    rw [Term.apps_snoc, ihf]

theorem Term.apps_head_inv {h h' : Term} (hh : h.IsHead) (hh' : h'.IsHead)
    {xs ys : List Term} (heq : Term.apps h xs = Term.apps h' ys) :
    h = h' ∧ xs = ys := by
  have e := congrArg Term.spine heq
  rw [Term.spine_apps hh, Term.spine_apps hh'] at e
  exact ⟨congrArg Prod.fst e, congrArg Prod.snd e⟩

-- a Let is never a weak value (in particular not a stuck ref-spine)
theorem Term.Value.let_absurd (hv : Term.Value β (.Let qb v b)) :
    False := by
  generalize ht : Term.Let qb v b = t0 at hv
  cases hv with
  | spine hs => rw [← ht] at hs; cases hs
  | @stuck k2 d2 args2 hk2 hgate =>
    exact Term.noConfusion
      (Term.apps_head_inv (h := Term.Let qb v b) (h' := Term.Ref k2)
        (xs := []) trivial trivial ht).1
  | typ => exact Term.noConfusion ht
  | all => exact Term.noConfusion ht
  | lam => exact Term.noConfusion ht
  | mat => exact Term.noConfusion ht
  | efq => exact Term.noConfusion ht
  | eql => exact Term.noConfusion ht
  | rfl => exact Term.noConfusion ht

-- a Rwt is never a weak value either
theorem Term.Value.rwt_absurd (hv : Term.Value β (.Rwt e P f)) :
    False := by
  generalize ht : Term.Rwt e P f = t0 at hv
  cases hv with
  | spine hs => rw [← ht] at hs; cases hs
  | @stuck k2 d2 args2 hk2 hgate =>
    exact Term.noConfusion
      (Term.apps_head_inv (h := Term.Rwt e P f) (h' := Term.Ref k2)
        (xs := []) trivial trivial ht).1
  | typ => exact Term.noConfusion ht
  | all => exact Term.noConfusion ht
  | lam => exact Term.noConfusion ht
  | mat => exact Term.noConfusion ht
  | efq => exact Term.noConfusion ht
  | eql => exact Term.noConfusion ht
  | rfl => exact Term.noConfusion ht

-- an application is a value only as a constructor-headed spine or a
-- stuck (underapplied or bodiless) reference-headed spine
theorem Term.Value.app_inv (hv : Term.Value β (.App f a)) :
    Spinal f ∨
    ∃ k d, (Term.spine f).1 = .Ref k ∧ Book.defn β k = some d ∧
      ((Term.spine (Term.App f a)).2.length < d.n ∨ d.body = none) := by
  generalize ht : Term.App f a = t0 at hv
  cases hv with
  | spine hs =>
    rw [← ht] at hs
    cases hs with
    | app hs2 => exact Or.inl hs2
  | @stuck k2 d2 args2 hk2 hgate =>
    right
    have hsp : Term.spine (Term.App f a) = (.Ref k2, args2) := by
      rw [ht, Term.spine_apps (h := .Ref k2) trivial]
    refine ⟨k2, d2, ?_, hk2, ?_⟩
    · exact congrArg Prod.fst hsp
    · rw [Term.spine_apps (h := .Ref k2) trivial]
      exact hgate
  | typ => exact Term.noConfusion ht
  | all => exact Term.noConfusion ht
  | lam => exact Term.noConfusion ht
  | mat => exact Term.noConfusion ht
  | efq => exact Term.noConfusion ht
  | eql => exact Term.noConfusion ht
  | rfl => exact Term.noConfusion ht

-- a bare Ref is a value only when its definition is stuck: positive
-- arity or no body
theorem Term.Value.ref_cases (hv : Term.Value β (.Ref k)) :
    ∀ {d : DefD}, Book.defn β k = some d → 0 < d.n ∨ d.body = none := by
  intro d hk
  generalize ht : Term.Ref k = t0 at hv
  cases hv with
  | spine hs => rw [← ht] at hs; cases hs
  | @stuck k2 d2 args2 hk2 hgate =>
    obtain ⟨hkk, hargs⟩ :=
      Term.apps_head_inv (h := Term.Ref k) (h' := Term.Ref k2)
        (xs := []) trivial trivial ht
    injection hkk with hkk2
    subst hkk2
    rw [hk] at hk2
    injection hk2 with hd2
    subst hd2
    rcases hgate with h1 | h1
    · rw [← hargs] at h1
      exact Or.inl (Nat.lt_of_le_of_lt (Nat.zero_le _) h1)
    · exact Or.inr h1
  | typ => exact Term.noConfusion ht
  | all => exact Term.noConfusion ht
  | lam => exact Term.noConfusion ht
  | mat => exact Term.noConfusion ht
  | efq => exact Term.noConfusion ht
  | eql => exact Term.noConfusion ht
  | rfl => exact Term.noConfusion ht

-- an App equal to a spine over a head splits at the last argument
theorem apps_shape : ∀ (as : List Term) (h t : Term),
    Term.apps h as = t →
    (as = [] ∧ t = h) ∨
    ∃ as0 alast, as = as0 ++ [alast] ∧ t = .App (Term.apps h as0) alast := by
  intro as
  induction as with
  | nil => intro h t he; exact .inl ⟨_root_.rfl, he.symm⟩
  | cons x rest ih =>
    intro h t he
    rcases ih (.App h x) t he with ⟨h1, h2⟩ | ⟨r0, rl, h1, h2⟩
    · subst h1
      exact .inr ⟨[], x, _root_.rfl, h2⟩
    · subst h1
      exact .inr ⟨x :: r0, rl, _root_.rfl, h2⟩

theorem Term.app_eq_apps {h f a : Term} (hh : h.IsHead)
    {xs : List Term} (heq : Term.App f a = Term.apps h xs) :
    ∃ ys, xs = ys ++ [a] ∧ f = Term.apps h ys := by
  have e := congrArg Term.spine heq
  rw [Term.spine_apps hh] at e
  simp only [Term.spine] at e
  refine ⟨(Term.spine f).2, ?_, ?_⟩
  · have e2 := congrArg Prod.snd e
    simp only at e2
    exact e2.symm
  · have e1 : (Term.spine f).1 = h := congrArg Prod.fst e
    rw [← e1, Term.apps_spine]

-- a Ctr-headed spine is never a binder-former: the redex heads a spine
-- cannot be
theorem Term.apps_ctr_ne {a c : Nat} {as : List Term} {t : Term}
    (ht : t.IsHead) (hne : t ≠ .Ctr a c) :
    Term.apps (.Ctr a c) as ≠ t := by
  intro heq
  have e := congrArg Term.spine heq
  rw [Term.spine_apps (by trivial)] at e
  have hs : Term.spine t = (t, []) := by
    cases t <;> first
    | rfl
    | exact absurd ht (by simp [Term.IsHead])
  rw [hs] at e
  exact hne (congrArg Prod.fst e).symm

theorem Term.apps_adt_ne {a : Nat} {r : List Nat} {as : List Term} {t : Term}
    (ht : t.IsHead) (hne : t ≠ .Adt a r) :
    Term.apps (.Adt a r) as ≠ t := by
  intro heq
  have e := congrArg Term.spine heq
  rw [Term.spine_apps (by trivial)] at e
  have hs : Term.spine t = (t, []) := by
    cases t <;> first
    | rfl
    | exact absurd ht (by simp [Term.IsHead])
  rw [hs] at e
  exact hne (congrArg Prod.fst e).symm

def Term.size : Term → Nat
  | .Var _         => 1
  | .Ref _         => 1
  | .Typ           => 1
  | .All _ A B     => 1 + Term.size A + Term.size B
  | .Lam f         => 1 + Term.size f
  | .App f a       => 1 + Term.size f + Term.size a
  | .Adt _ _       => 1
  | .Ctr _ _       => 1
  | .Mat _ _ h m   => 1 + Term.size h + Term.size m
  | .Efq           => 1
  | .Eql a b T     => 1 + Term.size a + Term.size b + Term.size T
  | .Rfl           => 1
  | .Rwt e P f     => 1 + Term.size e + Term.size P + Term.size f
  | .Let _ v b     => 1 + Term.size v + Term.size b

theorem Term.size_spine_arg : ∀ (t : Term), ∀ x ∈ (Term.spine t).2,
    Term.size x < Term.size t := by
  intro t
  induction t with
  | App f a ihf iha =>
    intro x hx
    simp only [Term.spine] at hx
    rcases List.mem_append.mp hx with h1 | h2
    · have := ihf x h1
      simp only [Term.size]
      omega
    · rw [List.mem_singleton.mp h2]
      simp only [Term.size]
      omega
  | _ =>
    intro x hx
    first
    | exact nomatch hx
    | (simp only [Term.spine] at hx; exact nomatch hx)

theorem Term.size_pos : ∀ t : Term, 1 ≤ Term.size t := by
  intro t
  cases t <;> simp only [Term.size] <;> omega

-- ============================================================================
-- METATHEORY §B — confluence: parallel reduction and claim (1).
-- The parallel step develops redexes and congruences at once; the mat
-- redexes leave their spine arguments undeveloped (the congruent
-- closure catches them next lap), which keeps the relation first-order
-- and the diamond a derivation induction. Books must be closed for the
-- δ-rule to commute with substitution; Book.Ok implies that (§D).
-- ============================================================================

def Book.Closed (β : Book) : Prop :=
  ∀ k t, Book.tld β k = some t →
    match t with
    | .adt A  => A.sig.Closed 0 ∧ ∀ c C, AdtD.ctr A c = some C → C.ty.Closed 0
    | .defn d => d.ty.Closed 0 ∧ (∀ b, d.body = some b → b.Closed 0)

theorem Book.Closed.defn (hβ : Book.Closed β) (h : Book.defn β k = some d) :
    d.ty.Closed 0 ∧ (∀ b, d.body = some b → b.Closed 0) := by
  unfold Book.defn at h
  split at h
  case _ heq => cases h; exact hβ _ _ heq
  case _ => cases h

-- list drop kit
theorem drop_append (xs ys : List Term) :
    (xs ++ ys).drop xs.length = ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact ih

-- targeted spine transport: shifting or substituting under a
-- Ctr-headed spine maps the arguments and keeps the head
theorem Term.spine_shift_ctr {s : Term} (hh : (Term.spine s).1 = .Ctr a c)
    (d : Nat) : Term.spine (Term.shift d s)
      = (.Ctr a c, (Term.spine s).2.map (Term.shift d)) := by
  obtain ⟨ts, hts⟩ : ∃ ts, (Term.spine s).2 = ts := ⟨_, rfl⟩
  have hs : s = Term.apps (.Ctr a c) ts := by
    rw [← hts, ← hh]; exact (Term.apps_spine s).symm
  rw [hts, hs, Term.shift_apps, Term.spine_apps (by trivial)]
  rfl

theorem Term.spine_subst_ctr {s : Term} (hh : (Term.spine s).1 = .Ctr a c)
    (d : Nat) (w : Term) : Term.spine (Term.subst d w s)
      = (.Ctr a c, (Term.spine s).2.map (Term.subst d w)) := by
  obtain ⟨ts, hts⟩ : ∃ ts, (Term.spine s).2 = ts := ⟨_, rfl⟩
  have hs : s = Term.apps (.Ctr a c) ts := by
    rw [← hts, ← hh]; exact (Term.apps_spine s).symm
  rw [hts, hs, Term.subst_apps, Term.spine_apps (by trivial)]
  rfl

-- parallel reduction: every redex and congruence develops at once.
-- The mat rules treat the scrutinee as ONE developed premise and
-- extract its fields by spine surgery, which keeps the relation
-- first-order (no lists of sub-derivations).
inductive Par (β : Book) : Term → Term → Prop
  | var  : Par β (.Var i) (.Var i)
  | ref  : Par β (.Ref k) (.Ref k)
  | typ  : Par β .Typ .Typ
  | adt  : Par β (.Adt a r) (.Adt a r)
  | ctr  : Par β (.Ctr a c) (.Ctr a c)
  | efq  : Par β .Efq .Efq
  | rfl  : Par β .Rfl .Rfl
  | all  : Par β A A' → Par β B B' → Par β (.All q A B) (.All q A' B')
  | eta  : Term.occ 0 F = 0 → Par β F F' →
           Par β (.Lam (.App F (.Var 0))) (Term.subst 0 .Typ F')
  | lam  : Par β f f' → Par β (.Lam f) (.Lam f')
  | app  : Par β f f' → Par β a a' → Par β (.App f a) (.App f' a')
  | mat  : Par β h h' → Par β m m' → Par β (.Mat a c h m) (.Mat a c h' m')
  | eql  : Par β x x' → Par β y y' → Par β T T' →
           Par β (.Eql x y T) (.Eql x' y' T')
  | rwt  : Par β e e' → Par β P P' → Par β f f' →
           Par β (.Rwt e P f) (.Rwt e' P' f')
  | let_ : Par β v v' → Par β b b' → Par β (.Let q v b) (.Let q v' b')
  | beta : Par β f f' → Par β a a' →
           Par β (.App (.Lam f) a) (Term.subst 0 a' f')
  | letr : Par β v v' → Par β b b' →
           Par β (.Let q v b) (Term.subst 0 v' b')
  | dref : Book.defn β k = some d → d.body = some b →
           (Term.spine s).1 = .Ref k →
           (Term.spine s).2.length = args'.length →
           (∀ i, i < (Term.spine s).2.length →
             Par β ((Term.spine s).2.getD i .Typ) (args'.getD i .Typ)) →
           Par β s (Term.apps b args')
  | aref : Book.adt β k = some A → A.pn = 0 → Par β (.Ref k) (.Adt k [])
  | matc : Book.adt β a = some A → AdtD.ctr A c = some C →
           (Term.spine s).1 = .Ctr a c →
           (Term.spine s).2.length = A.pn + C.fn →
           Par β s s' → Par β h h' →
           Par β (.App (.Mat a c h m) s)
                 (Term.apps h' ((Term.spine s').2.drop A.pn))
  | matm : (Term.spine s).1 = .Ctr a' c' → (a', c') ≠ (a, c) →
           Par β s s' → Par β m m' →
           Par β (.App (.Mat a c h m) s) (.App m' s')
  | rwtr : Par β f f' → Par β (.Rwt .Rfl P f) f'

-- pointwise parallel reduction on lists (a plain relation)
inductive Pars (β : Book) : List Term → List Term → Prop
  | nil  : Pars β [] []
  | cons : Par β x y → Pars β xs ys → Pars β (x :: xs) (y :: ys)

theorem Par.refl : ∀ (t : Term), Par β t t := by
  intro t
  induction t with
  | Var i => exact .var
  | Ref k => exact .ref
  | Typ => exact .typ
  | All q A B ihA ihB => exact .all ihA ihB
  | Lam f ihf => exact .lam ihf
  | App f a ihf iha => exact .app ihf iha
  | Adt a r => exact .adt
  | Ctr a c => exact .ctr
  | Mat a c h m ihh ihm => exact .mat ihh ihm
  | Efq => exact .efq
  | Eql x y T ihx ihy ihT => exact .eql ihx ihy ihT
  | Rfl => exact .rfl
  | Rwt e P f ihe ihP ihf => exact .rwt ihe ihP ihf
  | Let q v b ihv ihb => exact .let_ ihv ihb

theorem Pars.refl : ∀ (xs : List Term), Pars β xs xs := by
  intro xs
  induction xs with
  | nil => exact .nil
  | cons x xs ih => exact .cons (Par.refl x) ih

theorem Pars.length (h : Pars β xs ys) : xs.length = ys.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem Pars.append (h1 : Pars β xs ys) (h2 : Pars β as bs) :
    Pars β (xs ++ as) (ys ++ bs) := by
  induction h1 with
  | nil => exact h2
  | cons hp _ ih => exact .cons hp ih

theorem Pars.snoc (h1 : Pars β xs ys) (h2 : Par β a b) :
    Pars β (xs ++ [a]) (ys ++ [b]) :=
  h1.append (.cons h2 .nil)

theorem Pars.drop (h : Pars β xs ys) : ∀ n, Pars β (xs.drop n) (ys.drop n) := by
  induction h with
  | nil => intro n; rw [List.drop_nil]; exact Pars.nil
  | cons hp hrest ih =>
    intro n
    cases n with
    | zero => exact .cons hp hrest
    | succ n => exact ih n

-- parallel congruence through a spine
theorem Par.apps (hh : Par β h h') (has : Pars β as as') :
    Par β (Term.apps h as) (Term.apps h' as') := by
  induction has generalizing h h' with
  | nil => exact hh
  | cons hp _ ih => exact ih (.app hh hp)

theorem Step.par (s : Step β p a b) : Par β a b := by
  induction s with
  | beta => exact .beta (Par.refl _) (Par.refl _)
  | eta _ hocc => exact .eta hocc (Par.refl _)
  | drefS _ hk hb hsp =>
    exact .dref hk hb hsp _root_.rfl (fun i _ => Par.refl _)
  | let_ => exact .letr (Par.refl _) (Par.refl _)
  | @dref k d b s2 hk hb hsp hlen =>
    exact Par.dref hk hb hsp _root_.rfl (fun i _ => Par.refl _)
  | aref hk h0 => exact .aref hk h0
  | matc h1 h2 h3 h4 =>
    rename_i a A c C h m ps xs
    have hd : ((Term.spine (Term.apps (.Ctr a c) (ps ++ xs))).2.drop A.pn) = xs := by
      rw [Term.spine_apps (by trivial)]
      show (ps ++ xs).drop A.pn = xs
      rw [← h3]
      exact drop_append ps xs
    have hp := Par.matc (m := m) h1 h2
      (by rw [Term.spine_apps (by trivial)])
      (by rw [Term.spine_apps (by trivial)]; simp [h3, h4])
      (Par.refl (Term.apps (.Ctr a c) (ps ++ xs))) (Par.refl h)
    rwa [hd] at hp
  | matm hne =>
    rename_i a' c' a c h m as
    exact Par.matm (s := Term.apps (.Ctr a' c') as)
      (by rw [Term.spine_apps (by trivial)]) hne (Par.refl _) (Par.refl _)
  | rwt => exact .rwtr (Par.refl _)
  | all_a _ _ ih => exact .all ih (Par.refl _)
  | all_b _ _ ih => exact .all (Par.refl _) ih
  | lam_f _ _ ih => exact .lam ih
  | app_f _ ih => exact .app ih (Par.refl _)
  | app_a _ ih => exact .app (Par.refl _) ih
  | mat_h _ ih => exact .mat ih (Par.refl _)
  | mat_m _ ih => exact .mat (Par.refl _) ih
  | eql_a _ ih => exact .eql ih (Par.refl _) (Par.refl _)
  | eql_b _ ih => exact .eql (Par.refl _) ih (Par.refl _)
  | eql_t _ ih => exact .eql (Par.refl _) (Par.refl _) ih
  | rwt_e _ ih => exact .rwt ih (Par.refl _) (Par.refl _)
  | rwt_p _ ih => exact .rwt (Par.refl _) ih (Par.refl _)
  | rwt_f _ ih => exact .rwt (Par.refl _) (Par.refl _) ih
  | let_v _ ih => exact .let_ ih (Par.refl _)
  | let_b _ _ ih => exact .let_ (Par.refl _) ih

-- Red congruence kit (strong)
theorem Red.all_a (r : Red β .strong A A') :
    Red β .strong (.All q A B) (.All q A' B) := by
  induction r with
  | refl => exact .refl
  | step s _ ih => exact .step (.all_a _root_.rfl s) ih

theorem Red.all_b (r : Red β .strong B B') :
    Red β .strong (.All q A B) (.All q A B') := by
  induction r with
  | refl => exact .refl
  | step s _ ih => exact .step (.all_b _root_.rfl s) ih

theorem Red.lam_f (r : Red β .strong f f') :
    Red β .strong (.Lam f) (.Lam f') := by
  induction r with
  | refl => exact .refl
  | step s _ ih => exact .step (.lam_f _root_.rfl s) ih

theorem Red.app_f (r : Red β .strong f f') :
    Red β .strong (.App f a) (.App f' a) := by
  induction r with
  | refl => exact .refl
  | step s _ ih => exact .step (.app_f s) ih

theorem Red.app_a (r : Red β .strong a a') :
    Red β .strong (.App f a) (.App f a') := by
  induction r with
  | refl => exact .refl
  | step s _ ih => exact .step (.app_a s) ih

theorem Red.mat_h (r : Red β .strong h h') :
    Red β .strong (.Mat a c h m) (.Mat a c h' m) := by
  induction r with
  | refl => exact .refl
  | step s _ ih => exact .step (.mat_h s) ih

theorem Red.mat_m (r : Red β .strong m m') :
    Red β .strong (.Mat a c h m) (.Mat a c h m') := by
  induction r with
  | refl => exact .refl
  | step s _ ih => exact .step (.mat_m s) ih

theorem Red.eql_a (r : Red β .strong x x') :
    Red β .strong (.Eql x y T) (.Eql x' y T) := by
  induction r with
  | refl => exact .refl
  | step s _ ih => exact .step (.eql_a s) ih

theorem Red.eql_b (r : Red β .strong y y') :
    Red β .strong (.Eql x y T) (.Eql x y' T) := by
  induction r with
  | refl => exact .refl
  | step s _ ih => exact .step (.eql_b s) ih

theorem Red.eql_t (r : Red β .strong T T') :
    Red β .strong (.Eql x y T) (.Eql x y T') := by
  induction r with
  | refl => exact .refl
  | step s _ ih => exact .step (.eql_t s) ih

theorem Red.rwt_e (r : Red β .strong e e') :
    Red β .strong (.Rwt e P f) (.Rwt e' P f) := by
  induction r with
  | refl => exact .refl
  | step s _ ih => exact .step (.rwt_e s) ih

theorem Red.rwt_p (r : Red β .strong P P') :
    Red β .strong (.Rwt e P f) (.Rwt e P' f) := by
  induction r with
  | refl => exact .refl
  | step s _ ih => exact .step (.rwt_p s) ih

theorem Red.rwt_f (r : Red β .strong f f') :
    Red β .strong (.Rwt e P f) (.Rwt e P f') := by
  induction r with
  | refl => exact .refl
  | step s _ ih => exact .step (.rwt_f s) ih

theorem Red.let_v (r : Red β .strong v v') :
    Red β .strong (.Let q v b) (.Let q v' b) := by
  induction r with
  | refl => exact .refl
  | step s _ ih => exact .step (.let_v s) ih

theorem Red.let_b (r : Red β .strong b b') :
    Red β .strong (.Let q v b) (.Let q v b') := by
  induction r with
  | refl => exact .refl
  | step s _ ih => exact .step (.let_b _root_.rfl s) ih

theorem Red.apps_head (r : Red β .strong h h') (xs : List Term) :
    Red β .strong (Term.apps h xs) (Term.apps h' xs) := by
  induction xs generalizing h h' with
  | nil => exact r
  | cons x xs ih => exact ih (Red.app_f r)

-- head reductions lift over an application spine
theorem Red.apps (h : Red β p f f') : ∀ (xs : List Term),
    Red β p (Term.apps f xs) (Term.apps f' xs) := by
  intro xs
  induction xs generalizing f f' with
  | nil => exact h
  | cons x rest ih =>
    show Red β p (Term.apps (.App f x) rest) (Term.apps (.App f' x) rest)
    refine ih ?_
    induction h with
    | refl => exact .refl
    | step s _ ih2 => exact .step (.app_f s) ih2

theorem Red.apps_congr {h : Term} : ∀ {args args' : List Term},
    args.length = args'.length →
    (∀ i, i < args.length →
      Red β .strong (args.getD i .Typ) (args'.getD i .Typ)) →
    Red β .strong (Term.apps h args) (Term.apps h args') := by
  intro args
  induction args generalizing h with
  | nil =>
    intro args' hlen _
    cases args' with
    | cons _ _ => simp at hlen
    | nil => exact .refl
  | cons a as ih =>
    intro args' hlen hred
    cases args' with
    | nil => simp at hlen
    | cons a' as' =>
      show Red β .strong (Term.apps (.App h a) as)
        (Term.apps (.App h a') as')
      refine Red.trans ?_ (ih (by
          simp only [List.length_cons] at hlen
          omega)
        (fun i hi => hred (i + 1) (by
          simp only [List.length_cons]
          omega)))
      exact Red.apps (Red.app_a (hred 0 (by simp))) as

-- stability: a parallel reduct of a Ctr-headed spine is a Ctr-headed
-- spine with pointwise-parallel arguments
theorem Par.ctr_spine_inv (hp : Par β s t) :
    ∀ {a c : Nat} {as : List Term}, s = Term.apps (.Ctr a c) as →
    ∃ as', t = Term.apps (.Ctr a c) as' ∧ Pars β as as' := by
  induction hp with
  | @eta F F' hocc hF ih =>
    intro a c as heq
    exact Term.noConfusion (Term.apps_head_inv
      (h := Term.Lam (.App F (.Var 0)))
      (h' := .Ctr a c) (xs := []) trivial trivial heq).1
  | ctr =>
    intro a c as heq
    obtain ⟨h1, h2⟩ := Term.apps_head_inv (h := Term.Ctr _ _) (by trivial)
      (by trivial) (xs := []) heq
    cases h1
    cases h2
    exact ⟨[], _root_.rfl, .nil⟩
  | app hf ha ihf _ =>
    intro a c as heq
    obtain ⟨ys, hys, hfy⟩ := Term.app_eq_apps (by trivial) heq
    obtain ⟨ys', hy1, hy2⟩ := ihf hfy
    subst hys hy1
    exact ⟨ys' ++ [_], (Term.apps_snoc _ _ _).symm,
      Pars.append hy2 (.cons ha .nil)⟩
  | var =>
    intro a c as heq
    exact absurd heq.symm (Term.apps_ctr_ne (by trivial) (fun h => nomatch h))
  | ref =>
    intro a c as heq
    exact absurd heq.symm (Term.apps_ctr_ne (by trivial) (fun h => nomatch h))
  | typ =>
    intro a c as heq
    exact absurd heq.symm (Term.apps_ctr_ne (by trivial) (fun h => nomatch h))
  | adt =>
    intro a c as heq
    exact absurd heq.symm (Term.apps_ctr_ne (by trivial) (fun h => nomatch h))
  | efq =>
    intro a c as heq
    exact absurd heq.symm (Term.apps_ctr_ne (by trivial) (fun h => nomatch h))
  | rfl =>
    intro a c as heq
    exact absurd heq.symm (Term.apps_ctr_ne (by trivial) (fun h => nomatch h))
  | all _ _ _ _ =>
    intro a c as heq
    exact absurd heq.symm (Term.apps_ctr_ne (by trivial) (fun h => nomatch h))
  | lam _ _ =>
    intro a c as heq
    exact absurd heq.symm (Term.apps_ctr_ne (by trivial) (fun h => nomatch h))
  | mat _ _ _ _ =>
    intro a c as heq
    exact absurd heq.symm (Term.apps_ctr_ne (by trivial) (fun h => nomatch h))
  | eql _ _ _ _ _ _ =>
    intro a c as heq
    exact absurd heq.symm (Term.apps_ctr_ne (by trivial) (fun h => nomatch h))
  | rwt _ _ _ _ _ _ =>
    intro a c as heq
    exact absurd heq.symm (Term.apps_ctr_ne (by trivial) (fun h => nomatch h))
  | let_ _ _ _ _ =>
    intro a c as heq
    exact absurd heq.symm (Term.apps_ctr_ne (by trivial) (fun h => nomatch h))
  | letr _ _ _ _ =>
    intro a c as heq
    exact absurd heq.symm (Term.apps_ctr_ne (by trivial) (fun h => nomatch h))
  | dref _ _ hsp _ _ _ =>
    intro a c as heq
    rw [heq, Term.spine_apps (by trivial)] at hsp
    exact Term.noConfusion hsp
  | aref _ =>
    intro a c as heq
    exact absurd heq.symm (Term.apps_ctr_ne (by trivial) (fun h => nomatch h))
  | rwtr _ _ =>
    intro a c as heq
    exact absurd heq.symm (Term.apps_ctr_ne (by trivial) (fun h => nomatch h))
  | beta _ _ _ _ =>
    intro a c as heq
    obtain ⟨ys, _, hfy⟩ := Term.app_eq_apps (by trivial) heq
    exact absurd hfy.symm (Term.apps_ctr_ne (by trivial) (fun h => nomatch h))
  | matc _ _ _ _ _ _ _ _ =>
    intro a c as heq
    obtain ⟨ys, _, hfy⟩ := Term.app_eq_apps (by trivial) heq
    exact absurd hfy.symm (Term.apps_ctr_ne (by trivial) (fun h => nomatch h))
  | matm _ _ _ _ _ _ =>
    intro a c as heq
    obtain ⟨ys, _, hfy⟩ := Term.app_eq_apps (by trivial) heq
    exact absurd hfy.symm (Term.apps_ctr_ne (by trivial) (fun h => nomatch h))

-- spine-form of stability
theorem Par.spine_stable (hp : Par β s t) (hh : (Term.spine s).1 = .Ctr a c) :
    (Term.spine t).1 = .Ctr a c ∧ Pars β (Term.spine s).2 (Term.spine t).2 := by
  have hs : s = Term.apps (.Ctr a c) (Term.spine s).2 := by
    rw [← hh]; exact (Term.apps_spine s).symm
  obtain ⟨as', ht, hps⟩ := hp.ctr_spine_inv hs
  rw [ht, Term.spine_apps (by trivial)]
  exact ⟨_root_.rfl, hps⟩

theorem Book.defn_adt_clash (hd : Book.defn β k = some d)
    (ha : Book.adt β k = some A) : False := by
  cases htld : Book.tld β k with
  | none =>
    unfold Book.defn at hd
    rw [htld] at hd
    cases hd
  | some t =>
    cases t with
    | adt A2 =>
      unfold Book.defn at hd
      rw [htld] at hd
      cases hd
    | defn d2 =>
      unfold Book.adt at ha
      rw [htld] at ha
      cases ha

theorem List.occ_sum_zero_of_getD (d : Nat) : ∀ (as : List Term),
    (∀ i, i < as.length → Term.occ d (as.getD i .Typ) = 0) →
    (as.map (Term.occ d)).sum = 0 := by
  intro as
  induction as with
  | nil => intro _; rfl
  | cons x xs ih =>
    intro h
    simp only [List.map, List.sum_cons]
    have h0 : Term.occ d x = 0 := h 0 (by simp)
    rw [h0, ih (fun i hi => h (i + 1) (by simp; omega))]

theorem List.occ_getD_zero_of_sum (d : Nat) : ∀ (as : List Term),
    (as.map (Term.occ d)).sum = 0 →
    ∀ i, i < as.length → Term.occ d (as.getD i .Typ) = 0 := by
  intro as
  induction as with
  | nil => intro _ i hi; simp at hi
  | cons x xs ih =>
    intro h i hi
    simp only [List.map, List.sum_cons] at h
    cases i with
    | zero =>
      show Term.occ d x = 0
      omega
    | succ i =>
      refine ih (by omega) i (by simp only [List.length_cons] at hi; omega)

theorem List.occ_sum_drop_le (d : Nat) (n : Nat) : ∀ (as : List Term),
    ((as.drop n).map (Term.occ d)).sum ≤ (as.map (Term.occ d)).sum := by
  intro as
  induction as generalizing n with
  | nil => simp
  | cons x xs ih =>
    cases n with
    | zero => exact Nat.le_refl _
    | succ n =>
      simp only [List.drop, List.map, List.sum_cons]
      exact Nat.le_trans (ih n) (by omega)

-- parallel reduction preserves absence of a variable (each rule either
-- keeps subterms, substitutes an absent slot, or splices a closed body)
theorem Par.occ_zero (hβ : Book.Closed β) (hp : Par β t t') :
    ∀ (d : Nat), Term.occ d t = 0 → Term.occ d t' = 0 := by
  induction hp with
  | var => exact fun _ h => h
  | ref => exact fun _ h => h
  | typ => exact fun _ h => h
  | adt => exact fun _ h => h
  | ctr => exact fun _ h => h
  | efq => exact fun _ h => h
  | rfl => exact fun _ h => h
  | aref _ => exact fun _ _ => _root_.rfl
  | all _ _ ihA ihB =>
    intro d h
    simp only [Term.occ] at h ⊢
    rw [ihA d (by omega), ihB (d + 1) (by omega)]
  | lam _ ihf =>
    intro d h
    simp only [Term.occ] at h ⊢
    exact ihf (d + 1) h
  | app _ _ ihf iha =>
    intro d h
    simp only [Term.occ] at h ⊢
    rw [ihf d (by omega), iha d (by omega)]
  | mat _ _ ihh ihm =>
    intro d h
    simp only [Term.occ] at h ⊢
    rw [Nat.max_eq_zero_iff] at h
    rw [ihh d (by omega), ihm d (by omega)]
    simp
  | eql _ _ _ iha ihb ihT =>
    intro d h
    simp only [Term.occ] at h ⊢
    rw [iha d (by omega), ihb d (by omega), ihT d (by omega)]
  | rwt _ _ _ ihe ihP ihf =>
    intro d h
    simp only [Term.occ] at h ⊢
    rw [ihe d (by omega), ihP d (by omega), ihf d (by omega)]
  | let_ _ _ ihv ihb =>
    intro d h
    simp only [Term.occ] at h ⊢
    rw [ihv d (by omega), ihb (d + 1) (by omega)]
  | beta _ _ ihf iha =>
    intro d h
    simp only [Term.occ] at h
    exact Term.occ_subst_zero _ 0 d _ (Nat.zero_le d)
      (ihf (d + 1) (by omega)) (iha d (by omega))
  | letr _ _ ihv ihb =>
    intro d h
    simp only [Term.occ] at h
    exact Term.occ_subst_zero _ 0 d _ (Nat.zero_le d)
      (ihb (d + 1) (by omega)) (ihv d (by omega))
  | @eta F F' hocc hF ihF =>
    intro d h
    simp only [Term.occ] at h
    exact Term.occ_subst_zero F' 0 d .Typ (Nat.zero_le d)
      (ihF (d + 1) (by omega)) _root_.rfl
  | @dref k dd b s2 args' hk hb hsp hlen2 hargs ih =>
    intro d h
    have hs2 : s2 = Term.apps (.Ref k) (Term.spine s2).2 := by
      have h0 := Term.apps_spine s2
      rw [hsp] at h0
      exact h0.symm
    rw [hs2, Term.occ_apps] at h
    rw [Term.occ_apps]
    have hb0 : Term.occ d b = 0 :=
      Term.occ_closed b 0 d ((hβ.defn hk).2 b hb) (Nat.zero_le d)
    rw [hb0]
    have hzs := List.occ_getD_zero_of_sum d (Term.spine s2).2 (by
      simp only [Term.occ] at h
      omega)
    have hz2 : (args'.map (Term.occ d)).sum = 0 := by
      refine List.occ_sum_zero_of_getD d args' ?_
      intro i hi
      exact ih i (by omega) d (hzs i (by omega))
    omega
  | @matc a A c C s2 s2' h0 h0' m0 hk hc hsp hlen hs hh ihs ihh =>
    intro d h
    simp only [Term.occ] at h
    rw [Term.occ_apps]
    have hh0 : Term.occ d h0 = 0 := by
      have hX : Nat.max (Term.occ d h0) (Term.occ d m0) = 0 := by omega
      exact (Nat.max_eq_zero_iff.mp hX).1
    have hs0 : Term.occ d s2' = 0 := ihs d (by omega)
    have hdec : s2' = Term.apps (Term.spine s2').1 (Term.spine s2').2 :=
      (Term.apps_spine s2').symm
    rw [hdec, Term.occ_apps] at hs0
    have hdrop := List.occ_sum_drop_le d A.pn (Term.spine s2').2
    have hh1 := ihh d hh0
    omega
  | @matm s2 a' c' a c s2' m0 m0' h0 hsp hne hs hm ihs ihm =>
    intro d h
    simp only [Term.occ] at h ⊢
    have hX : Nat.max (Term.occ d h0) (Term.occ d m0) = 0 := by omega
    rw [ihm d (Nat.max_eq_zero_iff.mp hX).2, ihs d (by omega)]
  | rwtr _ ihf =>
    intro d h
    simp only [Term.occ] at h
    exact ihf d (by omega)

theorem Par.red (hβ : Book.Closed β) (hp : Par β a b) :
    Red β .strong a b := by
  induction hp with
  | @eta F F' hocc hF ih =>
    have hocc' : Term.occ 0 F' = 0 := Par.occ_zero hβ hF 0 hocc
    exact Red.trans (Red.lam_f (Red.app_f ih))
      (Red.one (Step.eta _root_.rfl hocc'))
  | var => exact .refl
  | ref => exact .refl
  | typ => exact .refl
  | adt => exact .refl
  | ctr => exact .refl
  | efq => exact .refl
  | rfl => exact .refl
  | all _ _ ihA ihB => exact (Red.all_a ihA).trans (Red.all_b ihB)
  | lam _ ihf => exact Red.lam_f ihf
  | app _ _ ihf iha => exact (Red.app_f ihf).trans (Red.app_a iha)
  | mat _ _ ihh ihm => exact (Red.mat_h ihh).trans (Red.mat_m ihm)
  | eql _ _ _ ihx ihy ihT =>
    exact ((Red.eql_a ihx).trans (Red.eql_b ihy)).trans (Red.eql_t ihT)
  | rwt _ _ _ ihe ihP ihf =>
    exact ((Red.rwt_e ihe).trans (Red.rwt_p ihP)).trans (Red.rwt_f ihf)
  | let_ _ _ ihv ihb => exact (Red.let_v ihv).trans (Red.let_b ihb)
  | beta _ _ ihf iha =>
    exact (((Red.app_f (Red.lam_f ihf)).trans (Red.app_a iha)).trans
      (Red.one .beta))
  | letr _ _ ihv ihb =>
    exact (((Red.let_v ihv).trans (Red.let_b ihb)).trans (Red.one .let_))
  | @dref k d b s args' hk hb hsp hlen' hpar ih =>
    have hs : s = Term.apps (.Ref k) (Term.spine s).2 := by
      rw [← hsp]
      exact (Term.apps_spine s).symm
    have hstep : Step β .strong (Term.apps (.Ref k) args')
        (Term.apps b args') := by
      have h := Step.drefS (s := Term.apps (.Ref k) args') (p := .strong)
        _root_.rfl hk hb (by rw [Term.spine_apps (by trivial)])
      rw [Term.spine_apps (by trivial)] at h
      exact h
    rw [hs]
    refine Red.trans (Red.apps_congr hlen' ih) ?_
    exact Red.one hstep
  | aref hk h0 => exact Red.one (.aref hk h0)
  | matc h1 h2 h3 h4 hps hph ihs ihh =>
    rename_i a A c C s s' h h' m
    obtain ⟨hh', hargs⟩ := hps.spine_stable h3
    have hlen : (Term.spine s').2.length = A.pn + C.fn := by
      rw [← hargs.length]; exact h4
    obtain ⟨ts, hts⟩ : ∃ ts, (Term.spine s').2 = ts := ⟨_, _root_.rfl⟩
    rw [hts] at hlen
    rw [hts]
    have hs' : s' = Term.apps (.Ctr a c) (ts.take A.pn ++ ts.drop A.pn) := by
      rw [List.take_append_drop, ← hts, ← hh']
      exact (Term.apps_spine s').symm
    have hstep : Step β .strong (.App (.Mat a c h m) s')
        (Term.apps h (ts.drop A.pn)) := by
      rw [hs']
      exact Step.matc h1 h2 (by simp [List.length_take]; omega)
        (by simp [List.length_drop]; omega)
    exact ((Red.app_a ihs).trans (Red.one hstep)).trans
      (Red.apps_head ihh _)
  | matm h1 hne hps hphm ihs ihm =>
    rename_i s a' c' a c s' m m' h
    obtain ⟨hh', _⟩ := hps.spine_stable h1
    have hs' : s' = Term.apps (.Ctr a' c') (Term.spine s').2 := by
      rw [← hh']; exact (Term.apps_spine s').symm
    have hstep : Step β .strong (.App (.Mat a c h m) s') (.App m s') := by
      rw [hs']
      exact Step.matm hne
    exact ((Red.app_a ihs).trans (Red.one hstep)).trans (Red.app_f ihm)
  | rwtr _ ihf => exact (Red.one .rwt).trans ihf

-- parallel reduction commutes with shift (closed book: δ-bodies are
-- fixed points of shift)
theorem Par.shift (hβ : Book.Closed β) (hp : Par β t t') :
    ∀ d, Par β (t.shift d) (t'.shift d) := by
  induction hp with
  | @eta F F' hocc hF ih =>
    intro d
    show Par β (.Lam (.App (Term.shift (d + 1) F)
      (Term.shift (d + 1) (.Var 0))))
      (Term.shift d (Term.subst 0 .Typ F'))
    have h0 : Term.shift (d + 1) (Term.Var 0) = .Var 0 := by
      simp only [Term.shift]
      rw [if_pos (by omega)]
    have h1 : Term.shift d (Term.subst 0 .Typ F')
        = Term.subst 0 .Typ (Term.shift (d + 1) F') := by
      rw [Term.shift_subst_ge F' d 0 .Typ (Nat.zero_le d)]
      rfl
    rw [h0, h1]
    exact .eta (by
        rw [Term.occ_shift_lt F 0 (d + 1) (by omega)]
        exact hocc)
      (ih (d + 1))
  | var => intro d; simp only [Term.shift]; split <;> exact .var
  | ref => intro d; exact .ref
  | typ => intro d; exact .typ
  | adt => intro d; exact .adt
  | ctr => intro d; exact .ctr
  | efq => intro d; exact .efq
  | rfl => intro d; exact .rfl
  | all _ _ ihA ihB => intro d; exact .all (ihA d) (ihB (d + 1))
  | lam _ ihf => intro d; exact .lam (ihf (d + 1))
  | app _ _ ihf iha => intro d; exact .app (ihf d) (iha d)
  | mat _ _ ihh ihm => intro d; exact .mat (ihh d) (ihm d)
  | eql _ _ _ ihx ihy ihT => intro d; exact .eql (ihx d) (ihy d) (ihT d)
  | rwt _ _ _ ihe ihP ihf => intro d; exact .rwt (ihe d) (ihP d) (ihf d)
  | let_ _ _ ihv ihb => intro d; exact .let_ (ihv d) (ihb (d + 1))
  | beta _ _ ihf iha =>
    intro d
    rw [Term.shift_subst0]
    exact .beta (ihf (d + 1)) (iha d)
  | letr _ _ ihv ihb =>
    intro d
    rw [Term.shift_subst0]
    exact .letr (ihv d) (ihb (d + 1))
  | @dref k dd b s args' hk hb hsp hlen' hpar ih =>
    intro d
    have hc := (hβ.defn hk).2 _ hb
    have hs : s = Term.apps (.Ref k) (Term.spine s).2 := by
      rw [← hsp]
      exact (Term.apps_spine s).symm
    rw [hs, Term.shift_apps, Term.shift_apps]
    simp only [Term.shift]
    rw [Term.shift_closed b 0 d hc (Nat.zero_le d)]
    refine Par.dref hk hb
      (by rw [Term.spine_apps (by trivial)])
      (by
        rw [Term.spine_apps (by trivial)]
        simp only [List.length_map]
        exact hlen') ?_
    rw [Term.spine_apps (by trivial)]
    intro i hi
    simp only [List.length_map] at hi
    rw [map_getD (Term.shift d) .Typ .Typ _ i (by omega),
      map_getD (Term.shift d) .Typ .Typ args' i (by omega)]
    exact ih i (by omega) d
  | aref hk h0 => intro d; exact .aref hk h0
  | matc h1 h2 h3 h4 hps hph ihs ihh =>
    rename_i a A c C s s' h h' m
    intro d
    obtain ⟨hh', hargs⟩ := hps.spine_stable h3
    have e1 : (Term.spine (Term.shift d s)).1 = Term.Ctr a c := by
      rw [Term.spine_shift_ctr h3 d]
    have e2 : (Term.spine (Term.shift d s)).2.length = A.pn + C.fn := by
      rw [Term.spine_shift_ctr h3 d]; simpa using h4
    have e3 : Term.shift d (Term.apps h' ((Term.spine s').2.drop A.pn))
        = Term.apps (Term.shift d h')
            ((Term.spine (Term.shift d s')).2.drop A.pn) := by
      rw [Term.shift_apps, Term.spine_shift_ctr hh' d]
      show _ = Term.apps _ (((Term.spine s').2.map (Term.shift d)).drop A.pn)
      rw [List.map_drop]
    rw [show Term.shift d (.App (.Mat a c h m) s)
        = .App (.Mat a c (Term.shift d h) (Term.shift d m)) (Term.shift d s)
      from _root_.rfl, e3]
    exact Par.matc h1 h2 e1 e2 (ihs d) (ihh d)
  | matm h1 hne hps hphm ihs ihm =>
    rename_i s a' c' a c s' m m' h
    intro d
    exact Par.matm (by rw [Term.spine_shift_ctr h1 d]) hne (ihs d) (ihm d)
  | rwtr _ ihf => intro d; exact .rwtr (ihf d)

-- parallel reduction is closed under substitution of parallel-reduced
-- terms (the beta case of the diamond)
theorem Par.subst (hβ : Book.Closed β) (hp : Par β t t') :
    ∀ d {w w'}, Par β w w' → Par β (Term.subst d w t) (Term.subst d w' t') := by
  induction hp with
  | @eta F F' hocc hF ih =>
    intro d w w' hw
    show Par β (.Lam (.App
      (Term.subst (d + 1) (Term.shift 0 w) F)
      (Term.subst (d + 1) (Term.shift 0 w) (.Var 0))))
      (Term.subst d w' (Term.subst 0 .Typ F'))
    have h0 : Term.subst (d + 1) (Term.shift 0 w) (Term.Var 0)
        = .Var 0 := by
      simp only [Term.subst]
      rw [if_neg (by omega), if_neg (by omega)]
    have h1 : Term.subst d w' (Term.subst 0 .Typ F')
        = Term.subst 0 .Typ (Term.subst (d + 1) (Term.shift 0 w') F') := by
      rw [Term.subst_subst0 F' w' .Typ d]
      rfl
    rw [h0, h1]
    refine .eta ?_ (ih (d + 1) (Par.shift hβ hw 0))
    exact Term.occ_subst_lt_zero F (d + 1) 0 (Term.shift 0 w) (by omega)
      hocc (Term.occ_shift_self w 0)
  | var =>
    intro d w w' hw
    simp only [Term.subst]
    split
    · exact hw
    · split <;> exact .var
  | ref => intro d w w' _; exact .ref
  | typ => intro d w w' _; exact .typ
  | adt => intro d w w' _; exact .adt
  | ctr => intro d w w' _; exact .ctr
  | efq => intro d w w' _; exact .efq
  | rfl => intro d w w' _; exact .rfl
  | all _ _ ihA ihB =>
    intro d w w' hw
    exact .all (ihA d hw) (ihB (d + 1) (hw.shift hβ 0))
  | lam _ ihf =>
    intro d w w' hw
    exact .lam (ihf (d + 1) (hw.shift hβ 0))
  | app _ _ ihf iha =>
    intro d w w' hw
    exact .app (ihf d hw) (iha d hw)
  | mat _ _ ihh ihm =>
    intro d w w' hw
    exact .mat (ihh d hw) (ihm d hw)
  | eql _ _ _ ihx ihy ihT =>
    intro d w w' hw
    exact .eql (ihx d hw) (ihy d hw) (ihT d hw)
  | rwt _ _ _ ihe ihP ihf =>
    intro d w w' hw
    exact .rwt (ihe d hw) (ihP d hw) (ihf d hw)
  | let_ _ _ ihv ihb =>
    intro d w w' hw
    exact .let_ (ihv d hw) (ihb (d + 1) (hw.shift hβ 0))
  | beta _ _ ihf iha =>
    intro d w w' hw
    rw [Term.subst_subst0]
    exact .beta (ihf (d + 1) (hw.shift hβ 0)) (iha d hw)
  | letr _ _ ihv ihb =>
    intro d w w' hw
    rw [Term.subst_subst0]
    exact .letr (ihv d hw) (ihb (d + 1) (hw.shift hβ 0))
  | @dref k dd b s args' hk hb hsp hlen' hpar ih =>
    intro d w w' hw
    have hc := (hβ.defn hk).2 _ hb
    have hs : s = Term.apps (.Ref k) (Term.spine s).2 := by
      rw [← hsp]
      exact (Term.apps_spine s).symm
    rw [hs, Term.subst_apps, Term.subst_apps]
    simp only [Term.subst]
    rw [Term.subst_closed b 0 d w' hc (Nat.zero_le d)]
    refine Par.dref hk hb
      (by rw [Term.spine_apps (by trivial)])
      (by
        rw [Term.spine_apps (by trivial)]
        simp only [List.length_map]
        exact hlen') ?_
    rw [Term.spine_apps (by trivial)]
    intro i hi
    simp only [List.length_map] at hi
    rw [map_getD (Term.subst d w) .Typ .Typ _ i (by omega),
      map_getD (Term.subst d w') .Typ .Typ args' i (by omega)]
    exact ih i (by omega) d hw
  | aref hk h0 => intro d w w' _; exact .aref hk h0
  | matc h1 h2 h3 h4 hps hph ihs ihh =>
    rename_i a A c C s s' h h' m
    intro d w w' hw
    obtain ⟨hh', hargs⟩ := hps.spine_stable h3
    have e1 : (Term.spine (Term.subst d w s)).1 = Term.Ctr a c := by
      rw [Term.spine_subst_ctr h3 d w]
    have e2 : (Term.spine (Term.subst d w s)).2.length = A.pn + C.fn := by
      rw [Term.spine_subst_ctr h3 d w]; simpa using h4
    have e3 : Term.subst d w' (Term.apps h' ((Term.spine s').2.drop A.pn))
        = Term.apps (Term.subst d w' h')
            ((Term.spine (Term.subst d w' s')).2.drop A.pn) := by
      rw [Term.subst_apps, Term.spine_subst_ctr hh' d w']
      show _ = Term.apps _ (((Term.spine s').2.map (Term.subst d w')).drop A.pn)
      rw [List.map_drop]
    rw [show Term.subst d w (.App (.Mat a c h m) s)
        = .App (.Mat a c (Term.subst d w h) (Term.subst d w m))
            (Term.subst d w s)
      from _root_.rfl, e3]
    exact Par.matc h1 h2 e1 e2 (ihs d hw) (ihh d hw)
  | matm h1 hne hps hphm ihs ihm =>
    rename_i s a' c' a c s' m m' h
    intro d w w' hw
    exact Par.matm (by rw [Term.spine_subst_ctr h1 d w]) hne
      (ihs d hw) (ihm d hw)
  | rwtr _ ihf =>
    intro d w w' hw
    exact .rwtr (ihf d hw)

-- inversion: parallel reducts of the binder-formers keep their shape
theorem Par.lam_inv (hp : Par β (.Lam f) t) :
    (∃ f', t = .Lam f' ∧ Par β f f')
    ∨ (∃ G G', f = .App G (.Var 0) ∧ Term.occ 0 G = 0 ∧
        t = Term.subst 0 .Typ G' ∧ Par β G G') := by
  cases hp with
  | lam hf => exact Or.inl ⟨_, _root_.rfl, hf⟩
  | @eta G G' hocc hG =>
    exact Or.inr ⟨G, G', _root_.rfl, hocc, _root_.rfl, hG⟩
  | dref _ _ hsp _ _ => exact Term.noConfusion hsp

theorem Par.mat_inv (hp : Par β (.Mat a c h m) t) :
    ∃ h' m', t = .Mat a c h' m' ∧ Par β h h' ∧ Par β m m' := by
  cases hp with
  | mat hh hm => exact ⟨_, _, _root_.rfl, hh, hm⟩
  | dref _ _ hsp _ _ => exact Term.noConfusion hsp

theorem Par.rfl_inv (hp : Par β .Rfl t) : t = .Rfl := by
  cases hp with
  | rfl => rfl
  | dref _ _ hsp _ _ => exact Term.noConfusion hsp


-- a parallel reduct of a defined-reference-headed spine: either the
-- head survives with pointwise-parallel arguments, or the definition
-- fired (at or above arity) and the reduct is the body's spine
theorem Par.ref_spine_cases (hd : Book.defn β k = some d)
    (hp : Par β s t) :
    ∀ {as : List Term}, s = Term.apps (.Ref k) as →
    (∃ as', t = Term.apps (.Ref k) as' ∧ as.length = as'.length ∧
      (∀ i, i < as.length → Par β (as.getD i .Typ) (as'.getD i .Typ)))
    ∨ (∃ b as', d.body = some b ∧
      as.length = as'.length ∧
      (∀ i, i < as.length → Par β (as.getD i .Typ) (as'.getD i .Typ)) ∧
      t = Term.apps b as') := by
  induction hp with
  | @eta F F' hocc hF ih =>
    intro as heq
    exact Term.noConfusion (Term.apps_head_inv
      (h := Term.Lam (.App F (.Var 0)))
      (h' := .Ref k) (xs := []) trivial trivial heq).1
  | @app f f' a a' hf ha ihf iha =>
    intro as heq
    rcases apps_shape as _ _ heq.symm with ⟨h1, h2⟩ | ⟨as0, al, h1, h2⟩
    · exact Term.noConfusion h2
    · subst h1
      cases h2
      have hsnocp : ∀ (xs xs' : List Term) (x x' : Term),
          xs.length = xs'.length →
          (∀ i, i < xs.length →
            Par β (xs.getD i .Typ) (xs'.getD i .Typ)) →
          Par β x x' →
          ∀ i, i < (xs ++ [x]).length →
            Par β ((xs ++ [x]).getD i .Typ)
              ((xs' ++ [x']).getD i .Typ) := by
        intro xs xs' x x' hl hp hx i hi
        simp only [List.length_append, List.length_cons,
          List.length_nil] at hi
        by_cases hix : i < xs.length
        · rw [getD_append_left _ _ i hix,
            getD_append_left _ _ i (by omega)]
          exact hp i hix
        · have hie : i = xs.length := by omega
          subst hie
          rw [show xs.length = xs.length + 0 from _root_.rfl,
            getD_append_right,
            show xs.length + 0 = xs'.length + 0 from by omega,
            getD_append_right]
          exact hx
      rcases ihf _root_.rfl with ⟨as0', ht', hl', hp'⟩ |
        ⟨b, as0', hb, hl', hp', ht'⟩
      · subst ht'
        left
        refine ⟨as0' ++ [a'], by rw [Term.apps_snoc], by
          simp only [List.length_append, List.length_cons,
            List.length_nil]
          omega, hsnocp as0 as0' a a' hl' hp' ha⟩
      · subst ht'
        refine Or.inr ⟨b, as0' ++ [a'], hb, by
          simp only [List.length_append, List.length_cons,
            List.length_nil]
          omega, hsnocp as0 as0' a a' hl' hp' ha, by
          rw [Term.apps_snoc]⟩
  | @dref k2 d2 b2 s2 args2' hk2 hb2 hsp2 hlen2' hps2 ih2 =>
    intro as heq
    subst heq
    rw [Term.spine_apps (by trivial)] at hsp2 hlen2' hps2
    injection hsp2 with hkk
    subst hkk
    rw [hk2] at hd
    cases hd
    have h6 : as.length = args2'.length := hlen2'
    refine Or.inr ⟨b2, args2', hb2, h6, ?_, _root_.rfl⟩
    intro i hi
    exact hps2 i hi
  | @aref k2 A2 hk2 =>
    intro as heq
    rcases apps_shape as _ _ heq.symm with ⟨h1, h2⟩ | ⟨as0, al, h1, h2⟩
    · injection h2 with hkk
      subst hkk
      exact absurd hk2 (fun hA => Book.defn_adt_clash hd hA)
    · exact Term.noConfusion h2
  | ref =>
    intro as heq
    rcases apps_shape as _ _ heq.symm with ⟨h1, h2⟩ | ⟨as0, al, h1, h2⟩
    · subst h1
      left
      exact ⟨[], heq, _root_.rfl, fun i hi => absurd hi (by simp)⟩
    · exact Term.noConfusion h2
  | var =>
    intro as heq
    rcases apps_shape as _ _ heq.symm with ⟨h1, h2⟩ | ⟨as0, al, h1, h2⟩
      <;> exact Term.noConfusion h2
  | typ =>
    intro as heq
    rcases apps_shape as _ _ heq.symm with ⟨h1, h2⟩ | ⟨as0, al, h1, h2⟩
      <;> exact Term.noConfusion h2
  | adt =>
    intro as heq
    rcases apps_shape as _ _ heq.symm with ⟨h1, h2⟩ | ⟨as0, al, h1, h2⟩
      <;> exact Term.noConfusion h2
  | ctr =>
    intro as heq
    rcases apps_shape as _ _ heq.symm with ⟨h1, h2⟩ | ⟨as0, al, h1, h2⟩
      <;> exact Term.noConfusion h2
  | efq =>
    intro as heq
    rcases apps_shape as _ _ heq.symm with ⟨h1, h2⟩ | ⟨as0, al, h1, h2⟩
      <;> exact Term.noConfusion h2
  | rfl =>
    intro as heq
    rcases apps_shape as _ _ heq.symm with ⟨h1, h2⟩ | ⟨as0, al, h1, h2⟩
      <;> exact Term.noConfusion h2
  | all _ _ _ _ =>
    intro as heq
    rcases apps_shape as _ _ heq.symm with ⟨h1, h2⟩ | ⟨as0, al, h1, h2⟩
      <;> exact Term.noConfusion h2
  | lam _ _ =>
    intro as heq
    rcases apps_shape as _ _ heq.symm with ⟨h1, h2⟩ | ⟨as0, al, h1, h2⟩
      <;> exact Term.noConfusion h2
  | mat _ _ _ _ =>
    intro as heq
    rcases apps_shape as _ _ heq.symm with ⟨h1, h2⟩ | ⟨as0, al, h1, h2⟩
      <;> exact Term.noConfusion h2
  | eql _ _ _ _ _ _ =>
    intro as heq
    rcases apps_shape as _ _ heq.symm with ⟨h1, h2⟩ | ⟨as0, al, h1, h2⟩
      <;> exact Term.noConfusion h2
  | rwt _ _ _ _ _ _ =>
    intro as heq
    rcases apps_shape as _ _ heq.symm with ⟨h1, h2⟩ | ⟨as0, al, h1, h2⟩
      <;> exact Term.noConfusion h2
  | let_ _ _ _ _ =>
    intro as heq
    rcases apps_shape as _ _ heq.symm with ⟨h1, h2⟩ | ⟨as0, al, h1, h2⟩
      <;> exact Term.noConfusion h2
  | beta _ _ _ _ =>
    intro as heq
    rcases apps_shape as _ _ heq.symm with ⟨h1, h2⟩ | ⟨as0, al, h1, h2⟩
    · exact Term.noConfusion h2
    · injection h2 with h3 h4
      rcases apps_shape as0 _ _ h3.symm with ⟨h5, h6⟩ | ⟨as1, al1, h5, h6⟩
      · exact Term.noConfusion h6
      · exact Term.noConfusion h6
  | letr _ _ _ _ =>
    intro as heq
    rcases apps_shape as _ _ heq.symm with ⟨h1, h2⟩ | ⟨as0, al, h1, h2⟩
      <;> exact Term.noConfusion h2
  | matc _ _ _ _ _ _ _ _ =>
    intro as heq
    rcases apps_shape as _ _ heq.symm with ⟨h1, h2⟩ | ⟨as0, al, h1, h2⟩
    · exact Term.noConfusion h2
    · injection h2 with h3 h4
      rcases apps_shape as0 _ _ h3.symm with ⟨h5, h6⟩ | ⟨as1, al1, h5, h6⟩
      · exact Term.noConfusion h6
      · exact Term.noConfusion h6
  | matm _ _ _ _ _ _ =>
    intro as heq
    rcases apps_shape as _ _ heq.symm with ⟨h1, h2⟩ | ⟨as0, al, h1, h2⟩
    · exact Term.noConfusion h2
    · injection h2 with h3 h4
      rcases apps_shape as0 _ _ h3.symm with ⟨h5, h6⟩ | ⟨as1, al1, h5, h6⟩
      · exact Term.noConfusion h6
      · exact Term.noConfusion h6
  | rwtr _ _ =>
    intro as heq
    rcases apps_shape as _ _ heq.symm with ⟨h1, h2⟩ | ⟨as0, al, h1, h2⟩
      <;> exact Term.noConfusion h2

-- parallel congruence over an application spine
theorem Par.apps_congr {h h' : Term} (hh : Par β h h') :
    ∀ {args args' : List Term},
    args.length = args'.length →
    (∀ i, i < args.length →
      Par β (args.getD i .Typ) (args'.getD i .Typ)) →
    Par β (Term.apps h args) (Term.apps h' args') := by
  intro args
  induction args generalizing h h' with
  | nil =>
    intro args' hlen _
    cases args' with
    | cons _ _ => simp at hlen
    | nil => exact hh
  | cons a as ih =>
    intro args' hlen hp
    cases args' with
    | nil => simp at hlen
    | cons a' as' =>
      show Par β (Term.apps (.App h a) as) (Term.apps (.App h' a') as')
      refine ih (.app hh (hp 0 (by simp))) (by
          simp only [List.length_cons] at hlen
          omega)
        (fun i hi => hp (i + 1) (by
          simp only [List.length_cons]
          omega))

-- assemble pointwise joins into a joined list
theorem Par.pointwise_join : ∀ (n : Nat) (f g : Nat → Term),
    (∀ i, i < n → ∃ q, Par β (f i) q ∧ Par β (g i) q) →
    ∃ qs : List Term, qs.length = n ∧
      (∀ i, i < n →
        Par β (f i) (qs.getD i .Typ) ∧ Par β (g i) (qs.getD i .Typ)) := by
  intro n
  induction n with
  | zero =>
    intro f g h
    exact ⟨[], _root_.rfl, fun i hi => absurd hi (by omega)⟩
  | succ m ih =>
    intro f g h
    obtain ⟨q0, hq0⟩ := h 0 (by omega)
    obtain ⟨qs, hql, hqs⟩ := ih (fun i => f (i + 1)) (fun i => g (i + 1))
      (fun i hi => h (i + 1) (by omega))
    refine ⟨q0 :: qs, by simp [hql], ?_⟩
    intro i hi
    cases i with
    | zero => exact hq0
    | succ j => exact hqs j (by omega)

-- ============================================================================
-- METATHEORY §B2 — the diamond and claim (1). Induction on the first
-- derivation, inversion on the second; the mat cases are fed by spine
-- stability, the beta/let cases by Par.subst.
-- ============================================================================

theorem Par.diamond (hβ : Book.Closed β) :
    ∀ {t p1 p2 : Term}, Par β t p1 → Par β t p2 →
    ∃ q, Par β p1 q ∧ Par β p2 q := by
  suffices hall : ∀ (n : Nat) {t p1 p2 : Term}, Term.size t ≤ n →
      Par β t p1 → Par β t p2 → ∃ q, Par β p1 q ∧ Par β p2 q by
    intro t p1 p2 h1 h2
    exact hall (Term.size t) (Nat.le_refl _) h1 h2
  intro n
  induction n with
  | zero =>
    intro t p1 p2 hsz _ _
    have := Term.size_pos t
    omega
  | succ n IH =>
  intro t p1 p2 hsz h1 h2
  -- the eta interaction, shared by both orientations: one side
  -- contracts the wrapper, the other reduces inside the body
  have hetalam : ∀ {F F' B2' : Term}, Term.size F + 3 ≤ n + 1 →
      Term.occ 0 F = 0 → Par β F F' → Par β (.App F (.Var 0)) B2' →
      ∃ q, Par β (Term.subst 0 .Typ F') q ∧ Par β (.Lam B2') q := by
    intro F F' B2' hszF hocc hF hB2
    cases hB2 with
    | @app _ Fa _ V' hFa hVa =>
      have hV : V' = .Var 0 := by
        cases hVa with
        | var => rfl
        | dref _ _ hsp _ _ => exact Term.noConfusion hsp
      subst hV
      have hocc2 : Term.occ 0 Fa = 0 := Par.occ_zero hβ hFa 0 hocc
      obtain ⟨F3, hF31, hF32⟩ := IH (t := F) (by omega) hF hFa
      exact ⟨Term.subst 0 .Typ F3,
        Par.subst hβ hF31 0 .typ,
        Par.eta hocc2 hF32⟩
    | @beta F0 F0' _ V' hf0 hv0 =>
      have hV : V' = .Var 0 := by
        cases hv0 with
        | var => rfl
        | dref _ _ hsp _ _ => exact Term.noConfusion hsp
      subst hV
      have hocc1 : Term.occ 1 F0 = 0 := hocc
      have hocc1' : Term.occ 1 F0' = 0 := Par.occ_zero hβ hf0 1 hocc1
      obtain ⟨Q, hQ1, hQ2⟩ := IH (t := .Lam F0) (by
        simp only [Term.size] at hszF ⊢
        omega) (Par.lam hf0) hF
      refine ⟨Term.subst 0 .Typ Q, Par.subst hβ hQ2 0 .typ, ?_⟩
      have hrw : Term.Lam (Term.subst 0 (.Var 0) F0')
          = Term.subst 0 .Typ (.Lam F0') := by
        show _ = Term.Lam (Term.subst 1 (Term.shift 0 .Typ) F0')
        rw [Term.subst_var_eq_subst_above F0' 0 (Term.shift 0 .Typ)
          hocc1']
      rw [hrw]
      exact Par.subst hβ hQ1 0 .typ
    | @dref k d b s2x args' hk hb hsp hlen' hpar =>
      have hspF : (Term.spine F).1 = .Ref k := hsp
      have hsF : F = Term.apps (.Ref k) (Term.spine F).2 := by
        rw [← hspF]
        exact (Term.apps_spine F).symm
      have hbc : b.Closed 0 := (hβ.defn hk).2 b hb
      have hsp2eq : (Term.spine (Term.App F (.Var 0))).2
          = (Term.spine F).2 ++ [Term.Var 0] := _root_.rfl
      rw [hsp2eq, List.length_append] at hlen'
      have hm1 : (Term.spine F).2.length + 1 = args'.length := by
        simp only [List.length_cons, List.length_nil] at hlen'
        omega
      have hoccas : ∀ i, i < (Term.spine F).2.length →
          Term.occ 0 ((Term.spine F).2.getD i .Typ) = 0 := by
        refine List.occ_getD_zero_of_sum 0 _ ?_
        have h0 : Term.occ 0 F = 0 := hocc
        rw [hsF, Term.occ_apps] at h0
        omega
      -- the fresh variable rides in the last argument slot
      have hlast : args'.getD (Term.spine F).2.length .Typ = .Var 0 := by
        have hp := hpar (Term.spine F).2.length (by
          rw [hsp2eq, List.length_append]
          simp only [List.length_cons, List.length_nil]
          omega)
        have hg : ((Term.spine F).2 ++ [Term.Var 0]).getD
            (Term.spine F).2.length .Typ = .Var 0 := by
          rw [show (Term.spine F).2.length
              = (Term.spine F).2.length + 0 from _root_.rfl,
            getD_append_right]
          rfl
        rw [hsp2eq, hg] at hp
        generalize hx : args'.getD (Term.spine F).2.length .Typ = X at hp ⊢
        cases hp with
        | var => rfl
        | dref _ _ hsp2 _ _ => exact Term.noConfusion hsp2
      have hsplit : args' = args'.take (Term.spine F).2.length
          ++ [.Var 0] := by
        rw [← hlast]
        exact (take_getD_self .Typ args' (Term.spine F).2.length
          (by omega)).symm
      have hpre : ∀ i, i < (Term.spine F).2.length →
          Par β ((Term.spine F).2.getD i .Typ) (args'.getD i .Typ) := by
        intro i hi
        have hp := hpar i (by
          rw [hsp2eq, List.length_append]
          simp only [List.length_cons, List.length_nil]
          omega)
        rw [hsp2eq, getD_append_left _ _ i hi] at hp
        exact hp
      have hoccpre : ∀ i, i < (Term.spine F).2.length →
          Term.occ 0 (args'.getD i .Typ) = 0 := fun i hi =>
        Par.occ_zero hβ (hpre i hi) 0 (hoccas i hi)
      rcases Par.ref_spine_cases hk hF hsF with
        ⟨bs, hFeq, hlb, hpb⟩ | ⟨b2, bs, hb2, hlb, hpb, hFeq⟩
      · -- the head survived on the eta side: unfold it after the cut
        subst hFeq
        obtain ⟨QS, hqlen, hqs⟩ := Par.pointwise_join
          ((Term.spine F).2.length)
          (fun i => args'.getD i .Typ) (fun i => bs.getD i .Typ)
          (fun i hi => by
            refine IH (t := (Term.spine F).2.getD i .Typ) ?_
              (hpre i hi) (hpb i hi)
            have h5 := Term.size_spine_arg F
              ((Term.spine F).2.getD i .Typ) (getD_mem _ i hi)
            omega)
        refine ⟨Term.apps b (QS.map (Term.subst 0 .Typ)), ?_, ?_⟩
        · -- subst kills the fresh slot, then the spine unfolds
          rw [Term.subst_apps,
            show Term.subst 0 .Typ (Term.Ref k) = .Ref k from _root_.rfl]
          refine Par.dref (s := Term.apps (.Ref k)
              (bs.map (Term.subst 0 .Typ))) hk hb
            (by rw [Term.spine_apps (by trivial)])
            (by
              rw [Term.spine_apps (by trivial)]
              simp only [List.length_map]
              omega) ?_
          rw [Term.spine_apps (by trivial)]
          intro i hi
          simp only [List.length_map] at hi
          rw [map_getD (Term.subst 0 .Typ) .Typ .Typ bs i (by omega),
            map_getD (Term.subst 0 .Typ) .Typ .Typ QS i (by omega)]
          exact Par.subst hβ ((hqs i (by omega)).2) 0 .typ
        · -- the wrapper contracts onto the unfolded spine
          rw [hsplit]
          have hhead : Par β
              (Term.apps b (args'.take (Term.spine F).2.length))
              (Term.apps b QS) := by
            refine Par.apps_congr (Par.refl b) (by
              simp only [List.length_take]
              omega) ?_
            intro i hi
            simp only [List.length_take] at hi
            rw [getD_take args' (Term.spine F).2.length i (by omega)]
            exact (hqs i (by omega)).1
          have hocch : Term.occ 0
              (Term.apps b (args'.take (Term.spine F).2.length)) = 0 := by
            rw [Term.occ_apps,
              Term.occ_closed b 0 0 hbc (Nat.le_refl 0)]
            have hz := List.occ_sum_zero_of_getD 0
              (args'.take (Term.spine F).2.length) (by
                intro i hi
                simp only [List.length_take] at hi
                rw [getD_take args' (Term.spine F).2.length i (by omega)]
                exact hoccpre i (by omega))
            omega
          have he := Par.eta hocch hhead
          rw [Term.subst_apps_closed 0 .Typ hbc QS] at he
          rw [Term.apps_snoc]
          exact he
      · -- both sides unfolded
        rw [hb] at hb2
        injection hb2 with hbb
        subst hbb
        subst hFeq
        obtain ⟨QS, hqlen, hqs⟩ := Par.pointwise_join
          ((Term.spine F).2.length)
          (fun i => args'.getD i .Typ) (fun i => bs.getD i .Typ)
          (fun i hi => by
            refine IH (t := (Term.spine F).2.getD i .Typ) ?_
              (hpre i hi) (hpb i hi)
            have h5 := Term.size_spine_arg F
              ((Term.spine F).2.getD i .Typ) (getD_mem _ i hi)
            omega)
        refine ⟨Term.apps b (QS.map (Term.subst 0 .Typ)), ?_, ?_⟩
        · rw [Term.subst_apps_closed 0 .Typ hbc bs]
          refine Par.apps_congr (Par.refl b) (by
            simp only [List.length_map]
            omega) ?_
          intro i hi
          simp only [List.length_map] at hi
          rw [map_getD (Term.subst 0 .Typ) .Typ .Typ bs i (by omega),
            map_getD (Term.subst 0 .Typ) .Typ .Typ QS i (by omega)]
          exact Par.subst hβ ((hqs i (by omega)).2) 0 .typ
        · rw [hsplit]
          have hhead : Par β
              (Term.apps b (args'.take (Term.spine F).2.length))
              (Term.apps b QS) := by
            refine Par.apps_congr (Par.refl b) (by
              simp only [List.length_take]
              omega) ?_
            intro i hi
            simp only [List.length_take] at hi
            rw [getD_take args' (Term.spine F).2.length i (by omega)]
            exact (hqs i (by omega)).1
          have hocch : Term.occ 0
              (Term.apps b (args'.take (Term.spine F).2.length)) = 0 := by
            rw [Term.occ_apps,
              Term.occ_closed b 0 0 hbc (Nat.le_refl 0)]
            have hz := List.occ_sum_zero_of_getD 0
              (args'.take (Term.spine F).2.length) (by
                intro i hi
                simp only [List.length_take] at hi
                rw [getD_take args' (Term.spine F).2.length i (by omega)]
                exact hoccpre i (by omega))
            omega
          have he := Par.eta hocch hhead
          rw [Term.subst_apps_closed 0 .Typ hbc QS] at he
          rw [Term.apps_snoc]
          exact he
    | matc _ _ hhead _ _ _ =>
      exact Term.noConfusion hhead
    | matm hhead _ _ _ =>
      exact Term.noConfusion hhead
  cases h1 with
  | @eta F F' hocc hF =>
    cases h2 with
    | eta hocc2 hF2 =>
      rename_i F2'
      obtain ⟨F3, hF31, hF32⟩ := IH (t := F) (by
        simp only [Term.size] at hsz
        omega) hF hF2
      exact ⟨Term.subst 0 .Typ F3, Par.subst hβ hF31 0 .typ,
        Par.subst hβ hF32 0 .typ⟩
    | lam hB2 =>
      exact hetalam (by simp only [Term.size] at hsz; omega) hocc hF hB2
    | dref _ _ hsp _ _ => exact Term.noConfusion hsp
  | var =>
    cases h2 with
    | var => exact ⟨_, .var, .var⟩
    | dref _ _ hsp _ _ => exact Term.noConfusion hsp
  | ref =>
    cases h2 with
    | ref => exact ⟨_, .ref, .ref⟩
    | dref hk2 hb2 hsp2 hlen2' hps2 =>
      exact ⟨_, Par.dref hk2 hb2 hsp2 hlen2' hps2, Par.refl _⟩
    | aref hk h0 => exact ⟨_, .aref hk h0, Par.refl _⟩
  | typ =>
    cases h2 with
    | typ => exact ⟨_, .typ, .typ⟩
    | dref _ _ hsp _ _ => exact Term.noConfusion hsp
  | adt =>
    cases h2 with
    | adt => exact ⟨_, .adt, .adt⟩
    | dref _ _ hsp _ _ => exact Term.noConfusion hsp
  | ctr =>
    cases h2 with
    | ctr => exact ⟨_, .ctr, .ctr⟩
    | dref _ _ hsp _ _ => exact Term.noConfusion hsp
  | efq =>
    cases h2 with
    | efq => exact ⟨_, .efq, .efq⟩
    | dref _ _ hsp _ _ => exact Term.noConfusion hsp
  | rfl =>
    cases h2 with
    | rfl => exact ⟨_, .rfl, .rfl⟩
    | dref _ _ hsp _ _ => exact Term.noConfusion hsp
  | @dref k d b s2 args' hk hb hsp hlen' hpar =>
    have hs : t = Term.apps (.Ref k) (Term.spine t).2 := by
      rw [← hsp]
      exact (Term.apps_spine t).symm
    have hjoins : ∀ (cs : List Term),
        (∀ i, i < (Term.spine t).2.length →
          Par β ((Term.spine t).2.getD i .Typ) (cs.getD i .Typ)) →
        ∀ i, i < (Term.spine t).2.length →
        ∃ q, Par β (args'.getD i .Typ) q ∧
          Par β (cs.getD i .Typ) q := by
      intro cs hcs i hi
      refine IH (t := (Term.spine t).2.getD i .Typ) ?_ (hpar i hi)
        (hcs i hi)
      have h5 := Term.size_spine_arg t ((Term.spine t).2.getD i .Typ)
        (getD_mem _ i hi)
      omega
    have hL2 : (Term.spine t).2.length = args'.length := hlen'
    rcases Par.ref_spine_cases hk h2 hs with
      ⟨bs, hp2eq, hlb, hpb⟩ | ⟨b2, bs, hb2, hlb, hpb, hp2eq⟩
    · subst hp2eq
      have hL3 : (Term.spine t).2.length = bs.length := hlb
      obtain ⟨qs, hqlen, hqs⟩ := Par.pointwise_join
        ((Term.spine t).2.length)
        (fun i => args'.getD i .Typ) (fun i => bs.getD i .Typ)
        (hjoins bs hpb)
      refine ⟨Term.apps b qs, ?_, ?_⟩
      · refine Par.apps_congr (Par.refl b) (by omega) ?_
        intro i hi
        exact (hqs i (by omega)).1
      · refine Par.dref (s := Term.apps (.Ref k) bs) hk hb
          (by rw [Term.spine_apps (by trivial)])
          (by
            rw [Term.spine_apps (by trivial)]
            show bs.length = qs.length
            omega) ?_
        rw [Term.spine_apps (by trivial)]
        intro i hi
        have hi2 : i < bs.length := hi
        exact (hqs i (by omega)).2
    · subst hp2eq
      have hL3 : (Term.spine t).2.length = bs.length := hlb
      rw [hb] at hb2
      injection hb2 with hbb
      subst hbb
      obtain ⟨qs, hqlen, hqs⟩ := Par.pointwise_join
        ((Term.spine t).2.length)
        (fun i => args'.getD i .Typ) (fun i => bs.getD i .Typ)
        (hjoins bs hpb)
      refine ⟨Term.apps b qs, ?_, ?_⟩
      · refine Par.apps_congr (Par.refl b) (by omega) ?_
        intro i hi
        exact (hqs i (by omega)).1
      · refine Par.apps_congr (Par.refl b) (by omega) ?_
        intro i hi
        have h6 : i < (Term.spine t).2.length := by omega
        exact (hqs i h6).2
  | aref hk h0 =>
    cases h2 with
    | ref => exact ⟨_, Par.refl _, .aref hk h0⟩
    | aref hk2 => exact ⟨_, Par.refl _, Par.refl _⟩
    | dref hk2 _ hsp2 _ _ =>
      injection hsp2 with hkk
      subst hkk
      exact absurd hk (fun hA => Book.defn_adt_clash hk2 hA)
  | all hA hB =>
    rename_i A A' B B' q
    have ihA : ∀ {p2 : Term}, Par β A p2 →
        ∃ q2, Par β A' q2 ∧ Par β p2 q2 := fun h2' =>
      IH (t := A) (by simp only [Term.size] at hsz; omega) hA h2'
    have ihB : ∀ {p2 : Term}, Par β B p2 →
        ∃ q2, Par β B' q2 ∧ Par β p2 q2 := fun h2' =>
      IH (t := B) (by simp only [Term.size] at hsz; omega) hB h2'
    cases h2 with
    | all hA2 hB2 =>
      obtain ⟨A3, hA31, hA32⟩ := ihA hA2
      obtain ⟨B3, hB31, hB32⟩ := ihB hB2
      exact ⟨.All _ A3 B3, .all hA31 hB31, .all hA32 hB32⟩
    | dref _ _ hsp _ _ => exact Term.noConfusion hsp
  | @lam f f' hf =>
    have ihf : ∀ {p2 : Term}, Par β f p2 →
        ∃ q2, Par β f' q2 ∧ Par β p2 q2 := fun h2' =>
      IH (t := f) (by simp only [Term.size] at hsz; omega) hf h2'
    cases h2 with
    | lam hf2 =>
      obtain ⟨f3, h31, h32⟩ := ihf hf2
      exact ⟨.Lam f3, .lam h31, .lam h32⟩
    | eta hocc2 hF2 =>
      obtain ⟨q, hq1, hq2⟩ := hetalam
        (by simp only [Term.size] at hsz; omega) hocc2 hF2 hf
      exact ⟨q, hq2, hq1⟩
    | dref _ _ hsp _ _ => exact Term.noConfusion hsp
  | @mat h0 h0' m0 m0' a c hh hm =>
    have ihh : ∀ {p2 : Term}, Par β h0 p2 →
        ∃ q2, Par β h0' q2 ∧ Par β p2 q2 := fun h2' =>
      IH (t := h0) (by simp only [Term.size] at hsz; omega) hh h2'
    have ihm : ∀ {p2 : Term}, Par β m0 p2 →
        ∃ q2, Par β m0' q2 ∧ Par β p2 q2 := fun h2' =>
      IH (t := m0) (by simp only [Term.size] at hsz; omega) hm h2'
    cases h2 with
    | mat hh2 hm2 =>
      obtain ⟨h3, hh31, hh32⟩ := ihh hh2
      obtain ⟨m3, hm31, hm32⟩ := ihm hm2
      exact ⟨.Mat _ _ h3 m3, .mat hh31 hm31, .mat hh32 hm32⟩
    | dref _ _ hsp _ _ => exact Term.noConfusion hsp
  | @eql x x' y y' T0 T0' hx hy hT =>
    have ihx : ∀ {p2 : Term}, Par β x p2 →
        ∃ q2, Par β x' q2 ∧ Par β p2 q2 := fun h2' =>
      IH (t := x) (by simp only [Term.size] at hsz; omega) hx h2'
    have ihy : ∀ {p2 : Term}, Par β y p2 →
        ∃ q2, Par β y' q2 ∧ Par β p2 q2 := fun h2' =>
      IH (t := y) (by simp only [Term.size] at hsz; omega) hy h2'
    have ihT : ∀ {p2 : Term}, Par β T0 p2 →
        ∃ q2, Par β T0' q2 ∧ Par β p2 q2 := fun h2' =>
      IH (t := T0) (by simp only [Term.size] at hsz; omega) hT h2'
    cases h2 with
    | eql hx2 hy2 hT2 =>
      obtain ⟨x3, hx31, hx32⟩ := ihx hx2
      obtain ⟨y3, hy31, hy32⟩ := ihy hy2
      obtain ⟨T3, hT31, hT32⟩ := ihT hT2
      exact ⟨.Eql x3 y3 T3, .eql hx31 hy31 hT31, .eql hx32 hy32 hT32⟩
    | dref _ _ hsp _ _ => exact Term.noConfusion hsp
  | @rwt e e' P P' f f' he hP hf =>
    have ihe : ∀ {p2 : Term}, Par β e p2 →
        ∃ q2, Par β e' q2 ∧ Par β p2 q2 := fun h2' =>
      IH (t := e) (by simp only [Term.size] at hsz; omega) he h2'
    have ihP : ∀ {p2 : Term}, Par β P p2 →
        ∃ q2, Par β P' q2 ∧ Par β p2 q2 := fun h2' =>
      IH (t := P) (by simp only [Term.size] at hsz; omega) hP h2'
    have ihf : ∀ {p2 : Term}, Par β f p2 →
        ∃ q2, Par β f' q2 ∧ Par β p2 q2 := fun h2' =>
      IH (t := f) (by simp only [Term.size] at hsz; omega) hf h2'
    cases h2 with
    | rwt he2 hP2 hf2 =>
      obtain ⟨e3, he31, he32⟩ := ihe he2
      obtain ⟨P3, hP31, hP32⟩ := ihP hP2
      obtain ⟨f3, hf31, hf32⟩ := ihf hf2
      exact ⟨.Rwt e3 P3 f3, .rwt he31 hP31 hf31, .rwt he32 hP32 hf32⟩
    | rwtr hf2 =>
      obtain ⟨f3, hf31, hf32⟩ := ihf hf2
      cases Par.rfl_inv he
      exact ⟨f3, .rwtr hf31, hf32⟩
    | dref _ _ hsp _ _ => exact Term.noConfusion hsp
  | rwtr hf =>
    rename_i f P
    have ihf : ∀ {p2x : Term}, Par β f p2x →
        ∃ q2, Par β p1 q2 ∧ Par β p2x q2 := fun h2' =>
      IH (t := f) (by simp only [Term.size] at hsz; omega) hf h2'
    cases h2 with
    | rwt he2 hP2 hf2 =>
      obtain ⟨f3, hf31, hf32⟩ := ihf hf2
      cases Par.rfl_inv he2
      exact ⟨f3, hf31, .rwtr hf32⟩
    | rwtr hf2 =>
      obtain ⟨f3, hf31, hf32⟩ := ihf hf2
      exact ⟨f3, hf31, hf32⟩
    | dref _ _ hsp _ _ => exact Term.noConfusion hsp
  | @let_ v v' b0 b0' q0 hv hb =>
    have ihv : ∀ {p2 : Term}, Par β v p2 →
        ∃ q2, Par β v' q2 ∧ Par β p2 q2 := fun h2' =>
      IH (t := v) (by simp only [Term.size] at hsz; omega) hv h2'
    have ihb : ∀ {p2 : Term}, Par β b0 p2 →
        ∃ q2, Par β b0' q2 ∧ Par β p2 q2 := fun h2' =>
      IH (t := b0) (by simp only [Term.size] at hsz; omega) hb h2'
    cases h2 with
    | let_ hv2 hb2 =>
      obtain ⟨v3, hv31, hv32⟩ := ihv hv2
      obtain ⟨b3, hb31, hb32⟩ := ihb hb2
      exact ⟨.Let _ v3 b3, .let_ hv31 hb31, .let_ hv32 hb32⟩
    | letr hv2 hb2 =>
      obtain ⟨v3, hv31, hv32⟩ := ihv hv2
      obtain ⟨b3, hb31, hb32⟩ := ihb hb2
      exact ⟨Term.subst 0 v3 b3, .letr hv31 hb31, Par.subst hβ hb32 0 hv32⟩
    | dref _ _ hsp _ _ => exact Term.noConfusion hsp
  | @letr v v' b0 b0' q0 hv hb =>
    have ihv : ∀ {p2 : Term}, Par β v p2 →
        ∃ q2, Par β v' q2 ∧ Par β p2 q2 := fun h2' =>
      IH (t := v) (by simp only [Term.size] at hsz; omega) hv h2'
    have ihb : ∀ {p2 : Term}, Par β b0 p2 →
        ∃ q2, Par β b0' q2 ∧ Par β p2 q2 := fun h2' =>
      IH (t := b0) (by simp only [Term.size] at hsz; omega) hb h2'
    cases h2 with
    | let_ hv2 hb2 =>
      obtain ⟨v3, hv31, hv32⟩ := ihv hv2
      obtain ⟨b3, hb31, hb32⟩ := ihb hb2
      exact ⟨Term.subst 0 v3 b3, Par.subst hβ hb31 0 hv31, .letr hv32 hb32⟩
    | letr hv2 hb2 =>
      obtain ⟨v3, hv31, hv32⟩ := ihv hv2
      obtain ⟨b3, hb31, hb32⟩ := ihb hb2
      exact ⟨Term.subst 0 v3 b3, Par.subst hβ hb31 0 hv31,
        Par.subst hβ hb32 0 hv32⟩
    | dref _ _ hsp _ _ => exact Term.noConfusion hsp
  | @beta f f' a a' hf ha =>
    have ihf : ∀ {p2 : Term}, Par β (.Lam f) p2 →
        ∃ q2, Par β (.Lam f') q2 ∧ Par β p2 q2 := fun h2' =>
      IH (t := Term.Lam f) (by simp only [Term.size] at hsz ⊢; omega)
        (Par.lam hf) h2'
    have iha : ∀ {p2 : Term}, Par β a p2 →
        ∃ q2, Par β a' q2 ∧ Par β p2 q2 := fun h2' =>
      IH (t := a) (by simp only [Term.size] at hsz; omega) ha h2'
    have ihfb : ∀ {p2 : Term}, Par β f p2 →
        ∃ q2, Par β f' q2 ∧ Par β p2 q2 := fun h2' =>
      IH (t := f) (by simp only [Term.size] at hsz; omega) hf h2'
    cases h2 with
    | app hf2 ha2 =>
      rename_i F2 a2
      obtain ⟨a3, ha31, ha32⟩ := iha ha2
      rcases Par.lam_inv hf2 with ⟨g2, hg2eq, hg2⟩ |
        ⟨G, G', hfeq, hoccG, hteq, hG⟩
      · subst hg2eq
        obtain ⟨f3, hf31, hf32⟩ := ihfb hg2
        exact ⟨Term.subst 0 a3 f3, Par.subst hβ hf31 0 ha31,
          .beta hf32 ha32⟩
      · subst hfeq
        subst hteq
        have hocc' : Term.occ 0 G' = 0 := Par.occ_zero hβ hG 0 hoccG
        obtain ⟨f3, hf31, hf32⟩ := ihfb (.app hG .var)
        refine ⟨Term.subst 0 a3 f3, Par.subst hβ hf31 0 ha31, ?_⟩
        have hrw : Term.subst 0 a2 (.App G' (.Var 0))
            = .App (Term.subst 0 .Typ G') a2 := by
          show Term.App (Term.subst 0 a2 G')
            (if 0 = 0 then a2 else _) = _
          rw [if_pos _root_.rfl,
            Term.occ_zero_subst_irrel G' 0 a2 .Typ hocc']
        rw [← hrw]
        exact Par.subst hβ hf32 0 ha32
    | beta hf2 ha2 =>
      obtain ⟨f3, hf31, hf32⟩ := ihfb hf2
      obtain ⟨a3, ha31, ha32⟩ := iha ha2
      exact ⟨Term.subst 0 a3 f3, Par.subst hβ hf31 0 ha31,
        Par.subst hβ hf32 0 ha32⟩
    | dref _ _ hsp _ _ => exact Term.noConfusion hsp
  | @app f f' a a' hf ha =>
    have ihf : ∀ {p2 : Term}, Par β f p2 →
        ∃ q2, Par β f' q2 ∧ Par β p2 q2 := fun h2' =>
      IH (t := f) (by simp only [Term.size] at hsz; omega) hf h2'
    have iha : ∀ {p2 : Term}, Par β a p2 →
        ∃ q2, Par β a' q2 ∧ Par β p2 q2 := fun h2' =>
      IH (t := a) (by simp only [Term.size] at hsz; omega) ha h2'
    cases h2 with
    | app hf2 ha2 =>
      obtain ⟨f3, hf31, hf32⟩ := ihf hf2
      obtain ⟨a3, ha31, ha32⟩ := iha ha2
      exact ⟨.App f3 a3, .app hf31 ha31, .app hf32 ha32⟩
    | beta hf2 ha2 =>
      rename_i f0 f02 a2
      obtain ⟨a3, ha31, ha32⟩ := iha ha2
      have ihf0 : ∀ {p2 : Term}, Par β f0 p2 →
          ∃ q2, Par β f02 q2 ∧ Par β p2 q2 := fun h2' =>
        IH (t := f0) (by simp only [Term.size] at hsz; omega) hf2 h2'
      rcases Par.lam_inv hf with ⟨g1, hg1eq, hg1⟩ |
        ⟨G, G', hfeq, hoccG, hteq, hG⟩
      · subst hg1eq
        obtain ⟨F3, hF31, hF32⟩ := ihf0 hg1
        exact ⟨Term.subst 0 a3 F3, .beta hF32 ha31,
          Par.subst hβ hF31 0 ha32⟩
      · subst hfeq
        subst hteq
        have hocc' : Term.occ 0 G' = 0 := Par.occ_zero hβ hG 0 hoccG
        obtain ⟨F3, hF31, hF32⟩ := ihf0 (.app hG .var)
        refine ⟨Term.subst 0 a3 F3, ?_, Par.subst hβ hF31 0 ha32⟩
        have hrw : Term.subst 0 a' (.App G' (.Var 0))
            = .App (Term.subst 0 .Typ G') a' := by
          show Term.App (Term.subst 0 a' G')
            (if 0 = 0 then a' else _) = _
          rw [if_pos _root_.rfl,
            Term.occ_zero_subst_irrel G' 0 a' .Typ hocc']
        rw [← hrw]
        exact Par.subst hβ hF32 0 ha31
    | matc hk1 hk2 hhead hlen hs2 hh2 =>
      obtain ⟨mh1, mm1, hmeq, hmh1, hmm1⟩ := Par.mat_inv hf
      subst hmeq
      obtain ⟨M3, hM31, hM32⟩ := ihf (Par.mat hh2 (Par.refl _))
      obtain ⟨h3t, m3t, hMeq, hh31, hm31⟩ := Par.mat_inv hM31
      subst hMeq
      obtain ⟨h3t', m3t', hMeq2, hh32, hm32⟩ := Par.mat_inv hM32
      cases hMeq2
      obtain ⟨s3, hs31, hs32⟩ := iha hs2
      have hstab1 := ha.spine_stable hhead
      have hstab2 := hs2.spine_stable hhead
      have hstab31 := hs31.spine_stable hstab1.1
      have hstab32 := hs32.spine_stable hstab2.1
      refine ⟨_, Par.matc hk1 hk2 hstab1.1 ?_ hs31 hh31, ?_⟩
      · rw [← hstab1.2.length]; exact hlen
      · exact Par.apps hh32 (Pars.drop hstab32.2 _)
    | matm hhead hne hs2 hm2 =>
      obtain ⟨mh1, mm1, hmeq, hmh1, hmm1⟩ := Par.mat_inv hf
      subst hmeq
      obtain ⟨M3, hM31, hM32⟩ := ihf (Par.mat (Par.refl _) hm2)
      obtain ⟨h3t, m3t, hMeq, hh31, hm31⟩ := Par.mat_inv hM31
      subst hMeq
      obtain ⟨h3t', m3t', hMeq2, hh32, hm32⟩ := Par.mat_inv hM32
      cases hMeq2
      obtain ⟨s3, hs31, hs32⟩ := iha hs2
      have hstab1 := ha.spine_stable hhead
      refine ⟨.App m3t s3, Par.matm hstab1.1 hne hs31 hm31, .app hm32 hs32⟩
    | @dref k2 d2 b2 s2x args2' hk2 hb2 hsp2 hlen2' hps2 =>
      have h1' : Par β (.App f a) (.App f' a') := .app hf ha
      have hs : Term.App f a
          = Term.apps (.Ref k2) (Term.spine (Term.App f a)).2 := by
        rw [← hsp2]
        exact (Term.apps_spine _).symm
      have hjoins : ∀ (cs : List Term),
          (∀ i, i < (Term.spine (Term.App f a)).2.length →
            Par β ((Term.spine (Term.App f a)).2.getD i .Typ)
              (cs.getD i .Typ)) →
          ∀ i, i < (Term.spine (Term.App f a)).2.length →
          ∃ q2, Par β (args2'.getD i .Typ) q2 ∧
            Par β (cs.getD i .Typ) q2 := by
        intro cs hcs i hi
        refine IH (t := (Term.spine (Term.App f a)).2.getD i .Typ) ?_
          (hps2 i hi) (hcs i hi)
        have h5 := Term.size_spine_arg (Term.App f a)
          ((Term.spine (Term.App f a)).2.getD i .Typ) (getD_mem _ i hi)
        omega
      have hL2 : (Term.spine (Term.App f a)).2.length = args2'.length :=
        hlen2'
      rcases Par.ref_spine_cases hk2 h1' hs with
        ⟨bs, hp1eq, hlb, hpb⟩ | ⟨b3, bs, hb3, hlb, hpb, hp1eq⟩
      · rw [hp1eq]
        have hL3 : (Term.spine (Term.App f a)).2.length = bs.length := hlb
        obtain ⟨qs, hqlen, hqs⟩ := Par.pointwise_join
          ((Term.spine (Term.App f a)).2.length)
          (fun i => args2'.getD i .Typ) (fun i => bs.getD i .Typ)
          (hjoins bs hpb)
        refine ⟨Term.apps b2 qs, ?_, ?_⟩
        · refine Par.dref (s := Term.apps (.Ref k2) bs) hk2 hb2
            (by rw [Term.spine_apps (by trivial)])
            (by
              rw [Term.spine_apps (by trivial)]
              show bs.length = qs.length
              omega) ?_
          rw [Term.spine_apps (by trivial)]
          intro i hi
          have hi2 : i < bs.length := hi
          exact (hqs i (by omega)).2
        · refine Par.apps_congr (Par.refl b2) (by omega) ?_
          intro i hi
          exact (hqs i (by omega)).1
      · rw [hp1eq]
        have hL3 : (Term.spine (Term.App f a)).2.length = bs.length := hlb
        rw [hb2] at hb3
        injection hb3 with hbb
        subst hbb
        obtain ⟨qs, hqlen, hqs⟩ := Par.pointwise_join
          ((Term.spine (Term.App f a)).2.length)
          (fun i => args2'.getD i .Typ) (fun i => bs.getD i .Typ)
          (hjoins bs hpb)
        refine ⟨Term.apps b2 qs, ?_, ?_⟩
        · refine Par.apps_congr (Par.refl b2) (by omega) ?_
          intro i hi
          have h6 : i < (Term.spine (Term.App f a)).2.length := by omega
          exact (hqs i h6).2
        · refine Par.apps_congr (Par.refl b2) (by omega) ?_
          intro i hi
          exact (hqs i (by omega)).1
  | @matc a A c C s2m s2m' h0 h0' m0 hk1 hk2 hhead hlen hs hh =>
    have ihs : ∀ {p2 : Term}, Par β s2m p2 →
        ∃ q2, Par β s2m' q2 ∧ Par β p2 q2 := fun h2' =>
      IH (t := s2m) (by simp only [Term.size] at hsz; omega) hs h2'
    have ihh : ∀ {p2 : Term}, Par β h0 p2 →
        ∃ q2, Par β h0' q2 ∧ Par β p2 q2 := fun h2' =>
      IH (t := h0) (by simp only [Term.size] at hsz; omega) hh h2'
    cases h2 with
    | app hf2 ha2 =>
      obtain ⟨mh2, mm2, hmeq, hmh2, hmm2⟩ := Par.mat_inv hf2
      subst hmeq
      obtain ⟨h3, hh31, hh32⟩ := ihh hmh2
      obtain ⟨s3, hs31, hs32⟩ := ihs ha2
      have hstab1 := hs.spine_stable hhead
      have hstab2 := ha2.spine_stable hhead
      have hstab31 := hs31.spine_stable hstab1.1
      refine ⟨_, Par.apps hh31 (Pars.drop hstab31.2 _),
        Par.matc hk1 hk2 hstab2.1 ?_ hs32 hh32⟩
      rw [← hstab2.2.length]; exact hlen
    | matc hk1' hk2' hhead' hlen' hs2 hh2 =>
      rw [hk1] at hk1'
      cases hk1'
      rw [hk2] at hk2'
      cases hk2'
      obtain ⟨h3, hh31, hh32⟩ := ihh hh2
      obtain ⟨s3, hs31, hs32⟩ := ihs hs2
      have hstab1 := hs.spine_stable hhead
      have hstab2 := hs2.spine_stable hhead
      have hstab31 := hs31.spine_stable hstab1.1
      have hstab32 := hs32.spine_stable hstab2.1
      exact ⟨_, Par.apps hh31 (Pars.drop hstab31.2 _),
        Par.apps hh32 (Pars.drop hstab32.2 _)⟩
    | matm hhead' hne hs2 hm2 =>
      exfalso
      rw [hhead] at hhead'
      cases hhead'
      exact hne _root_.rfl
    | dref _ _ hsp _ _ => exact Term.noConfusion hsp
  | @matm s2m a' c' a c s2m' m0 m0' h0 hhead hne hs hm =>
    have ihs : ∀ {p2 : Term}, Par β s2m p2 →
        ∃ q2, Par β s2m' q2 ∧ Par β p2 q2 := fun h2' =>
      IH (t := s2m) (by simp only [Term.size] at hsz; omega) hs h2'
    have ihm : ∀ {p2 : Term}, Par β m0 p2 →
        ∃ q2, Par β m0' q2 ∧ Par β p2 q2 := fun h2' =>
      IH (t := m0) (by simp only [Term.size] at hsz; omega) hm h2'
    cases h2 with
    | app hf2 ha2 =>
      obtain ⟨mh2, mm2, hmeq, hmh2, hmm2⟩ := Par.mat_inv hf2
      subst hmeq
      obtain ⟨m3, hm31, hm32⟩ := ihm hmm2
      obtain ⟨s3, hs31, hs32⟩ := ihs ha2
      have hstab2 := ha2.spine_stable hhead
      exact ⟨.App m3 s3, .app hm31 hs31,
        Par.matm hstab2.1 hne hs32 hm32⟩
    | matm hhead' hne' hs2 hm2 =>
      obtain ⟨m3, hm31, hm32⟩ := ihm hm2
      obtain ⟨s3, hs31, hs32⟩ := ihs hs2
      exact ⟨.App m3 s3, .app hm31 hs31, .app hm32 hs32⟩
    | matc hk1' hk2' hhead' hlen' hs2 hh2 =>
      exfalso
      rw [hhead] at hhead'
      cases hhead'
      exact hne _root_.rfl
    | dref _ _ hsp _ _ => exact Term.noConfusion hsp

-- chains of parallel steps (= strong runs, both directions)
inductive ParRed (β : Book) : Term → Term → Prop
  | refl : ParRed β t t
  | step : Par β a b → ParRed β b c → ParRed β a c

theorem ParRed.of_red (r : Red β .strong a b) : ParRed β a b := by
  induction r with
  | refl => exact .refl
  | step s _ ih => exact .step s.par ih

theorem ParRed.red (hβ : Book.Closed β) (r : ParRed β a b) :
    Red β .strong a b := by
  induction r with
  | refl => exact .refl
  | step p _ ih => exact (p.red hβ).trans ih

theorem ParRed.strip (hβ : Book.Closed β) (hp : Par β a b)
    (hr : ParRed β a c) : ∃ d, ParRed β b d ∧ Par β c d := by
  induction hr generalizing b with
  | refl => exact ⟨b, .refl, hp⟩
  | step p _ ih =>
    obtain ⟨e, hpe, hbe⟩ := Par.diamond hβ p hp
    obtain ⟨d, hd1, hd2⟩ := ih hpe
    exact ⟨d, .step hbe hd1, hd2⟩

theorem ParRed.confluent (hβ : Book.Closed β) (h1 : ParRed β a b)
    (h2 : ParRed β a c) : ∃ d, ParRed β b d ∧ ParRed β c d := by
  induction h1 generalizing c with
  | refl => exact ⟨c, h2, .refl⟩
  | step p _ ih =>
    obtain ⟨e, he1, he2⟩ := ParRed.strip hβ p h2
    obtain ⟨d, hd1, hd2⟩ := ih he1
    exact ⟨d, hd1, .step he2 hd2⟩

-- confluence over a closed book; Book.Ok closes the book in §D and
-- discharges the claim
theorem church_rosser_closed (hβ : Book.Closed β)
    (h1 : Red β .strong a b) (h2 : Red β .strong a c) :
    ∃ d, Red β .strong b d ∧ Red β .strong c d := by
  obtain ⟨d, hd1, hd2⟩ :=
    ParRed.confluent hβ (ParRed.of_red h1) (ParRed.of_red h2)
  exact ⟨d, hd1.red hβ, hd2.red hβ⟩


-- ============================================================================
-- METATHEORY §D0 — typed terms are closed; Book.Ok closes the book,
-- which discharges claim (1).
-- ============================================================================

theorem Ctx.get_lt : ∀ {Γ : Ctx} {i : Nat} {T : Term},
    Ctx.get Γ i = some T → i < Γ.length := by
  intro Γ
  induction Γ with
  | nil => intro i T h; cases h
  | cons A Γ ih =>
    intro i T h
    cases i with
    | zero => exact Nat.succ_pos _
    | succ i =>
      simp only [Ctx.get, Option.map_eq_some_iff] at h
      obtain ⟨T', hT', _⟩ := h
      exact Nat.succ_lt_succ (ih hT')

theorem Check.closed (h : Check β q Γ t T π) : t.Closed Γ.length := by
  induction h with
  | var hg => exact Ctx.get_lt hg
  | ref _ => trivial
  | refA _ _ => trivial
  | adt _ => trivial
  | ctr _ _ => trivial
  | typ => trivial
  | all _ _ _ ihA ihB => exact ⟨ihA, ihB⟩
  | lam _ _ ihf => exact ihf
  | app _ _ _ ihf ihx => exact ⟨ihf, ihx⟩
  | let_ _ _ _ _ ihv ihb => exact ⟨ihv, ihb⟩
  | eql _ _ _ ihT iha ihb => exact ⟨iha, ihb, ihT⟩
  | rfl _ => trivial
  | rwt _ _ _ ihe ihP ihf => exact ⟨ihe, ihP, ihf⟩
  | mat _ _ _ _ _ _ _ _ _ ihh ihm => exact ⟨ihh, ihm⟩
  | efq _ _ _ => trivial
  | cnv _ _ iht => exact iht

theorem Book.Ok.closed (hok : Book.Ok β) : Book.Closed β := by
  intro k t hk
  have h := hok k t hk
  cases t with
  | adt A =>
    refine ⟨?_, ?_⟩
    · obtain ⟨π, hs⟩ := h.1
      exact hs.closed
    · intro c C hc
      obtain ⟨π, hs⟩ := (h.2.2 c C hc).1
      exact hs.closed
  | defn d =>
    refine ⟨?_, ?_⟩
    · obtain ⟨π, hs⟩ := h.1
      exact hs.closed
    · intro b hb
      obtain ⟨π, hs⟩ := (h.2.2 b hb).1
      exact hs.closed

theorem church_rosser_holds : church_rosser := by
  intro β a b c hok h1 h2
  exact church_rosser_closed hok.closed h1 h2

-- ============================================================================
-- METATHEORY §C — conversion: an equivalence (transitivity is
-- confluence), congruent, with stable heads. The clash lemmas are what
-- generation and canonical forms consume: the four head classes — Typ,
-- All, Eql, and Adt-headed spines — never convert across classes, and
-- convert within a class only componentwise.
-- ============================================================================

theorem Conv.refl (t : Term) : Conv β t t := ⟨t, .refl, .refl⟩

theorem Conv.symm (h : Conv β a b) : Conv β b a := by
  obtain ⟨c, h1, h2⟩ := h
  exact ⟨c, h2, h1⟩

theorem Conv.trans (hβ : Book.Closed β) (h1 : Conv β a b) (h2 : Conv β b c) :
    Conv β a c := by
  obtain ⟨u, hu1, hu2⟩ := h1
  obtain ⟨v, hv1, hv2⟩ := h2
  obtain ⟨w, hw1, hw2⟩ := church_rosser_closed hβ hu2 hv1
  exact ⟨w, hu1.trans hw1, hv2.trans hw2⟩

theorem Conv.of_red (h : Red β .strong a b) : Conv β a b := ⟨b, h, .refl⟩

theorem Conv.of_red_rev (h : Red β .strong b a) : Conv β a b := ⟨a, .refl, h⟩

-- pointwise reduction and conversion on lists
inductive Reds (β : Book) (p : Strength) : List Term → List Term → Prop
  | nil  : Reds β p [] []
  | cons : Red β p x y → Reds β p xs ys → Reds β p (x :: xs) (y :: ys)

theorem Reds.refl : ∀ (xs : List Term), Reds β p xs xs := by
  intro xs
  induction xs with
  | nil => exact .nil
  | cons x xs ih => exact .cons .refl ih

theorem Reds.length (h : Reds β p xs ys) : xs.length = ys.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem Reds.trans (h1 : Reds β p xs ys) (h2 : Reds β p ys zs) :
    Reds β p xs zs := by
  induction h1 generalizing zs with
  | nil => cases h2; exact .nil
  | cons hr hrest ih =>
    cases h2 with
    | cons hr2 hrest2 => exact .cons (hr.trans hr2) (ih hrest2)

theorem Reds.append (h1 : Reds β p xs ys) (h2 : Reds β p as bs) :
    Reds β p (xs ++ as) (ys ++ bs) := by
  induction h1 with
  | nil => exact h2
  | cons hr _ ih => exact .cons hr ih

inductive Convs (β : Book) : List Term → List Term → Prop
  | nil  : Convs β [] []
  | cons : Conv β x y → Convs β xs ys → Convs β (x :: xs) (y :: ys)

theorem Convs.refl : ∀ (xs : List Term), Convs β xs xs := by
  intro xs
  induction xs with
  | nil => exact .nil
  | cons x xs ih => exact .cons (Conv.refl x) ih

theorem Convs.length (h : Convs β xs ys) : xs.length = ys.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem Reds.convs (h1 : Reds β .strong xs zs) (h2 : Reds β .strong ys zs) :
    Convs β xs ys := by
  induction h1 generalizing ys with
  | nil => cases h2; exact .nil
  | cons hr hrest ih =>
    cases h2 with
    | cons hr2 hrest2 =>
      exact .cons ⟨_, hr, hr2⟩ (ih hrest2)

-- head stability: no rule fires at a stable head, so a strong run out
-- of one keeps its shape

theorem Step.typ_inv (s : Step β p .Typ u) : False := by
  cases s with
  | drefS _ _ _ hsp => exact Term.noConfusion hsp
  | dref _ _ hsp _ => exact Term.noConfusion hsp

theorem Red.typ_inv (r : Red β .strong .Typ u) : u = .Typ := by
  cases r with
  | refl => rfl
  | step s _ => exact absurd s Step.typ_inv

theorem Step.all_inv (s : Step β p (.All q A B) u) :
    ∃ A' B', u = .All q A' B' ∧ Red β p A A' ∧ Red β p B B' := by
  cases s with
  | drefS _ _ _ hsp => exact Term.noConfusion hsp
  | all_a _ sA => exact ⟨_, _, rfl, Red.one sA, .refl⟩
  | all_b _ sB => exact ⟨_, _, rfl, .refl, Red.one sB⟩
  | dref _ _ hsp _ => exact Term.noConfusion hsp

theorem Red.all_inv (r : Red β .strong (.All q A B) u) :
    ∃ A' B', u = .All q A' B' ∧ Red β .strong A A' ∧ Red β .strong B B' := by
  generalize ht : Term.All q A B = t at r
  induction r generalizing A B with
  | refl => exact ⟨A, B, ht.symm, .refl, .refl⟩
  | step s _ ih =>
    subst ht
    obtain ⟨A1, B1, hu, hA1, hB1⟩ := Step.all_inv s
    obtain ⟨A2, B2, hu2, hA2, hB2⟩ := ih hu.symm
    exact ⟨A2, B2, hu2, hA1.trans hA2, hB1.trans hB2⟩

theorem Step.eql_inv (s : Step β p (.Eql a b T) u) :
    ∃ a' b' T', u = .Eql a' b' T' ∧
      Red β p a a' ∧ Red β p b b' ∧ Red β p T T' := by
  cases s with
  | drefS _ _ _ hsp => exact Term.noConfusion hsp
  | eql_a sa => exact ⟨_, _, _, rfl, Red.one sa, .refl, .refl⟩
  | eql_b sb => exact ⟨_, _, _, rfl, .refl, Red.one sb, .refl⟩
  | eql_t st => exact ⟨_, _, _, rfl, .refl, .refl, Red.one st⟩
  | dref _ _ hsp _ => exact Term.noConfusion hsp

theorem Red.eql_inv (r : Red β .strong (.Eql a b T) u) :
    ∃ a' b' T', u = .Eql a' b' T' ∧
      Red β .strong a a' ∧ Red β .strong b b' ∧ Red β .strong T T' := by
  generalize ht : Term.Eql a b T = t at r
  induction r generalizing a b T with
  | refl => exact ⟨a, b, T, ht.symm, .refl, .refl, .refl⟩
  | step s _ ih =>
    subst ht
    obtain ⟨a1, b1, T1, hu, h1, h2, h3⟩ := Step.eql_inv s
    obtain ⟨a2, b2, T2, hu2, g1, g2, g3⟩ := ih hu.symm
    exact ⟨a2, b2, T2, hu2, h1.trans g1, h2.trans g2, h3.trans g3⟩

theorem Step.rfl_inv (s : Step β p .Rfl u) : False := by
  cases s with
  | drefS _ _ _ hsp => exact Term.noConfusion hsp
  | dref _ _ hsp _ => exact Term.noConfusion hsp

theorem Red.rfl_inv (r : Red β .strong .Rfl u) : u = .Rfl := by
  cases r with
  | refl => rfl
  | step s _ => exact absurd s Step.rfl_inv

-- an Adt-headed spine steps only inside its arguments
theorem Step.adt_spine_inv (s : Step β p t u) :
    ∀ {a : Nat} {r : List Nat} {as : List Term},
    t = Term.apps (.Adt a r) as →
    ∃ bs, u = Term.apps (.Adt a r) bs ∧ Reds β p as bs := by
  induction s with
  | @eta F hp hocc =>
    intro a r as heq
    exact Term.noConfusion (Term.apps_head_inv
      (h := Term.Lam (.App F (.Var 0)))
      (h' := .Adt a r) (xs := []) trivial trivial heq).1
  | drefS _ _ _ hsp =>
    intro a r as heq
    rw [heq, Term.spine_apps (h := .Adt a r) trivial] at hsp
    exact Term.noConfusion hsp
  | app_f sf ihf =>
    intro a r as heq
    obtain ⟨ys, hys, hfy⟩ := Term.app_eq_apps (by trivial) heq
    obtain ⟨bs, hu, hred⟩ := ihf hfy
    subst hys hu
    exact ⟨bs ++ [_], (Term.apps_snoc _ _ _).symm,
      Reds.append hred (.cons .refl .nil)⟩
  | app_a sa =>
    intro a r as heq
    obtain ⟨ys, hys, hfy⟩ := Term.app_eq_apps (by trivial) heq
    subst hys hfy
    exact ⟨ys ++ [_], (Term.apps_snoc _ _ _).symm,
      Reds.append (Reds.refl ys) (.cons (Red.one sa) .nil)⟩
  | beta =>
    intro a r as heq
    obtain ⟨ys, _, hfy⟩ := Term.app_eq_apps (by trivial) heq
    exact absurd hfy.symm (Term.apps_adt_ne (by trivial) (fun h => nomatch h))
  | matc _ _ _ _ =>
    intro a r as heq
    obtain ⟨ys, _, hfy⟩ := Term.app_eq_apps (by trivial) heq
    exact absurd hfy.symm (Term.apps_adt_ne (by trivial) (fun h => nomatch h))
  | matm _ =>
    intro a r as heq
    obtain ⟨ys, _, hfy⟩ := Term.app_eq_apps (by trivial) heq
    exact absurd hfy.symm (Term.apps_adt_ne (by trivial) (fun h => nomatch h))
  | let_ =>
    intro a r as heq
    exact absurd heq.symm (Term.apps_adt_ne (by trivial) (fun h => nomatch h))
  | dref _ _ hsp _ =>
    intro a r as heq
    rw [heq, Term.spine_apps (by trivial)] at hsp
    exact Term.noConfusion hsp
  | aref _ =>
    intro a r as heq
    exact absurd heq.symm (Term.apps_adt_ne (by trivial) (fun h => nomatch h))
  | rwt =>
    intro a r as heq
    exact absurd heq.symm (Term.apps_adt_ne (by trivial) (fun h => nomatch h))
  | all_a _ _ =>
    intro a r as heq
    exact absurd heq.symm (Term.apps_adt_ne (by trivial) (fun h => nomatch h))
  | all_b _ _ =>
    intro a r as heq
    exact absurd heq.symm (Term.apps_adt_ne (by trivial) (fun h => nomatch h))
  | lam_f _ _ =>
    intro a r as heq
    exact absurd heq.symm (Term.apps_adt_ne (by trivial) (fun h => nomatch h))
  | mat_h _ =>
    intro a r as heq
    exact absurd heq.symm (Term.apps_adt_ne (by trivial) (fun h => nomatch h))
  | mat_m _ =>
    intro a r as heq
    exact absurd heq.symm (Term.apps_adt_ne (by trivial) (fun h => nomatch h))
  | eql_a _ =>
    intro a r as heq
    exact absurd heq.symm (Term.apps_adt_ne (by trivial) (fun h => nomatch h))
  | eql_b _ =>
    intro a r as heq
    exact absurd heq.symm (Term.apps_adt_ne (by trivial) (fun h => nomatch h))
  | eql_t _ =>
    intro a r as heq
    exact absurd heq.symm (Term.apps_adt_ne (by trivial) (fun h => nomatch h))
  | rwt_e _ =>
    intro a r as heq
    exact absurd heq.symm (Term.apps_adt_ne (by trivial) (fun h => nomatch h))
  | rwt_p _ =>
    intro a r as heq
    exact absurd heq.symm (Term.apps_adt_ne (by trivial) (fun h => nomatch h))
  | rwt_f _ =>
    intro a r as heq
    exact absurd heq.symm (Term.apps_adt_ne (by trivial) (fun h => nomatch h))
  | let_v _ =>
    intro a r as heq
    exact absurd heq.symm (Term.apps_adt_ne (by trivial) (fun h => nomatch h))
  | let_b _ _ =>
    intro a r as heq
    exact absurd heq.symm (Term.apps_adt_ne (by trivial) (fun h => nomatch h))

theorem Red.adt_spine_inv (r : Red β .strong t u) :
    ∀ {a : Nat} {rr : List Nat} {as : List Term},
    t = Term.apps (.Adt a rr) as →
    ∃ bs, u = Term.apps (.Adt a rr) bs ∧ Reds β .strong as bs := by
  induction r with
  | refl => intro a rr as heq; exact ⟨as, heq, Reds.refl as⟩
  | step s _ ih =>
    intro a rr as heq
    obtain ⟨bs, hu, hred⟩ := s.adt_spine_inv heq
    obtain ⟨cs, hu2, hred2⟩ := ih hu
    exact ⟨cs, hu2, hred.trans hred2⟩

-- the clash matrix: distinct head classes never convert

theorem Conv.typ_all (h : Conv β .Typ (.All q A B)) : False := by
  obtain ⟨c, h1, h2⟩ := h
  obtain ⟨A', B', hc, _, _⟩ := h2.all_inv
  rw [h1.typ_inv] at hc
  cases hc

theorem Conv.typ_eql (h : Conv β .Typ (.Eql a b T)) : False := by
  obtain ⟨c, h1, h2⟩ := h
  obtain ⟨a', b', T', hc, _, _, _⟩ := h2.eql_inv
  rw [h1.typ_inv] at hc
  cases hc

theorem Conv.typ_adt (h : Conv β .Typ (Term.apps (.Adt a r) ps)) : False := by
  obtain ⟨c, h1, h2⟩ := h
  obtain ⟨bs, hc, _⟩ := h2.adt_spine_inv (Eq.refl _)
  rw [h1.typ_inv] at hc
  exact Term.apps_adt_ne (t := .Typ) (by trivial) (fun h => nomatch h) hc.symm

theorem Conv.all_eql (h : Conv β (.All q A B) (.Eql x y T)) : False := by
  obtain ⟨c, h1, h2⟩ := h
  obtain ⟨A', B', hc, _, _⟩ := h1.all_inv
  obtain ⟨x', y', T', hc2, _, _, _⟩ := h2.eql_inv
  rw [hc] at hc2
  cases hc2

theorem Conv.all_adt (h : Conv β (.All q A B) (Term.apps (.Adt a r) ps)) :
    False := by
  obtain ⟨c, h1, h2⟩ := h
  obtain ⟨A', B', hc, _, _⟩ := h1.all_inv
  obtain ⟨bs, hc2, _⟩ := h2.adt_spine_inv (Eq.refl _)
  rw [hc] at hc2
  exact Term.apps_adt_ne (t := .All _ _ _) (by trivial)
    (fun h => nomatch h) hc2.symm

theorem Conv.eql_adt (h : Conv β (.Eql x y T) (Term.apps (.Adt a r) ps)) :
    False := by
  obtain ⟨c, h1, h2⟩ := h
  obtain ⟨x', y', T', hc, _, _, _⟩ := h1.eql_inv
  obtain ⟨bs, hc2, _⟩ := h2.adt_spine_inv (Eq.refl _)
  rw [hc] at hc2
  exact Term.apps_adt_ne (t := .Eql _ _ _) (by trivial)
    (fun h => nomatch h) hc2.symm

-- the injectivity lemmas: conversion within a class is componentwise

theorem Conv.all_inj (h : Conv β (.All q A B) (.All q' A' B')) :
    q = q' ∧ Conv β A A' ∧ Conv β B B' := by
  obtain ⟨c, h1, h2⟩ := h
  obtain ⟨A1, B1, hc1, hA1, hB1⟩ := h1.all_inv
  obtain ⟨A2, B2, hc2, hA2, hB2⟩ := h2.all_inv
  rw [hc1] at hc2
  cases hc2
  exact ⟨rfl, ⟨A1, hA1, hA2⟩, ⟨B1, hB1, hB2⟩⟩

theorem Conv.eql_inj (h : Conv β (.Eql a b T) (.Eql a' b' T')) :
    Conv β a a' ∧ Conv β b b' ∧ Conv β T T' := by
  obtain ⟨c, h1, h2⟩ := h
  obtain ⟨a1, b1, T1, hc1, g1, g2, g3⟩ := h1.eql_inv
  obtain ⟨a2, b2, T2, hc2, f1, f2, f3⟩ := h2.eql_inv
  rw [hc1] at hc2
  cases hc2
  exact ⟨⟨a1, g1, f1⟩, ⟨b1, g2, f2⟩, ⟨T1, g3, f3⟩⟩

theorem Conv.adt_inj
    (h : Conv β (Term.apps (.Adt a r) ps) (Term.apps (.Adt a' r') qs)) :
    a = a' ∧ r = r' ∧ Convs β ps qs := by
  obtain ⟨c, h1, h2⟩ := h
  obtain ⟨bs1, hc1, g1⟩ := h1.adt_spine_inv (Eq.refl _)
  obtain ⟨bs2, hc2, g2⟩ := h2.adt_spine_inv (Eq.refl _)
  rw [hc1] at hc2
  obtain ⟨hhead, hargs⟩ := Term.apps_head_inv (by trivial) (by trivial) hc2
  cases hhead
  cases hargs
  exact ⟨rfl, rfl, g1.convs g2⟩


-- ============================================================================
-- METATHEORY §A3 — the quantity order and the usage kit. Quant.mul is a
-- metatheory helper (the spec has no multiplication): it scales a
-- substituted value's measure by the substituted variable's measure.
-- All finite quantity identities are decided.
-- ============================================================================

def Quant.mul : Quant → Quant → Quant
  | .None, _     => .None
  | _,     .None => .None
  | .Lone, q     => q
  | .Many, _     => .Many

theorem Quant.add_comm : ∀ a b : Quant, Quant.add a b = Quant.add b a := by
  intro a b; cases a <;> cases b <;> rfl

theorem Quant.add_assoc : ∀ a b c : Quant,
    Quant.add (Quant.add a b) c = Quant.add a (Quant.add b c) := by
  intro a b c; cases a <;> cases b <;> cases c <;> rfl

theorem Quant.add_none : ∀ a : Quant, Quant.add a .None = a := by
  intro a; cases a <;> rfl


theorem Quant.none_mul : ∀ a : Quant, Quant.mul .None a = .None := by
  intro a; rfl


theorem Quant.lone_mul : ∀ a : Quant, Quant.mul .Lone a = a := by
  intro a; cases a <;> rfl

theorem Quant.le_refl : ∀ a : Quant, Quant.le a a := by
  intro a; cases a <;> trivial

theorem Quant.le_trans : ∀ {a b c : Quant},
    Quant.le a b → Quant.le b c → Quant.le a c := by
  intro a b c h1 h2
  cases a <;> cases b <;> cases c <;>
    first | trivial | exact h1.elim | exact h2.elim

theorem Quant.none_le : ∀ a : Quant, Quant.le .None a := by
  intro a; trivial

theorem Quant.le_none : ∀ {a : Quant}, Quant.le a .None → a = .None := by
  intro a h; cases a <;> first | rfl | exact h.elim


theorem Quant.le_add : ∀ {a a' b b' : Quant}, Quant.le a a' → Quant.le b b' →
    Quant.le (Quant.add a b) (Quant.add a' b') := by
  intro a a' b b' h1 h2
  cases a <;> cases a' <;> cases b <;> cases b' <;>
    first | trivial | exact h1.elim | exact h2.elim

theorem Quant.le_join : ∀ {a a' b b' : Quant}, Quant.le a a' → Quant.le b b' →
    Quant.le (Quant.join a b) (Quant.join a' b') := by
  intro a a' b b' h1 h2
  cases a <;> cases a' <;> cases b <;> cases b' <;>
    first | trivial | exact h1.elim | exact h2.elim

theorem Quant.le_mul : ∀ {a a' b b' : Quant}, Quant.le a a' → Quant.le b b' →
    Quant.le (Quant.mul a b) (Quant.mul a' b') := by
  intro a a' b b' h1 h2
  cases a <;> cases a' <;> cases b <;> cases b' <;>
    first | trivial | exact h1.elim | exact h2.elim

theorem Quant.le_add_left : ∀ a b : Quant, Quant.le a (Quant.add a b) := by
  intro a b; cases a <;> cases b <;> trivial

theorem Quant.le_add_right : ∀ a b : Quant, Quant.le b (Quant.add a b) := by
  intro a b; cases a <;> cases b <;> trivial

theorem Quant.le_join_left : ∀ a b : Quant, Quant.le a (Quant.join a b) := by
  intro a b; cases a <;> cases b <;> trivial

theorem Quant.le_join_right : ∀ a b : Quant, Quant.le b (Quant.join a b) := by
  intro a b; cases a <;> cases b <;> trivial

theorem Quant.join_le : ∀ {a b c : Quant},
    Quant.le a c → Quant.le b c → Quant.le (Quant.join a b) c := by
  intro a b c h1 h2
  cases a <;> cases b <;> cases c <;>
    first | trivial | exact h1.elim | exact h2.elim

theorem Quant.dem_none : ∀ q' : Quant, Quant.dem q' .None = .None := by
  intro q'; cases q' <;> rfl


theorem Quant.cut_add_point : ∀ a1 b1 a0 b0 v : Quant,
    Quant.add (Quant.add a1 b1) (Quant.mul (Quant.add a0 b0) v)
      = Quant.add (Quant.add a1 (Quant.mul a0 v))
          (Quant.add b1 (Quant.mul b0 v)) := by
  intro a1 b1 a0 b0 v
  cases a1 <;> cases b1 <;> cases a0 <;> cases b0 <;> cases v <;> rfl

theorem Quant.cut_join_point : ∀ a1 b1 a0 b0 v : Quant,
    Quant.le (Quant.join (Quant.add a1 (Quant.mul a0 v))
        (Quant.add b1 (Quant.mul b0 v)))
      (Quant.add (Quant.join a1 b1) (Quant.mul (Quant.join a0 b0) v)) := by
  intro a1 b1 a0 b0 v
  cases a1 <;> cases b1 <;> cases a0 <;> cases b0 <;> cases v <;> trivial

theorem Uses.le_refl (π : Uses) : Uses.le π π :=
  fun i => Quant.le_refl (π i)

theorem Uses.le_trans (h1 : Uses.le a b) (h2 : Uses.le b c) : Uses.le a c :=
  fun i => Quant.le_trans (h1 i) (h2 i)

theorem Uses.zero_le (π : Uses) : Uses.le Uses.zero π :=
  fun _ => Quant.none_le _

theorem Uses.le_zero_eq (h : Uses.le π Uses.zero) : π = Uses.zero := by
  funext i
  exact Quant.le_none (h i)

theorem Uses.le_add (h1 : Uses.le a a') (h2 : Uses.le b b') :
    Uses.le (Uses.add a b) (Uses.add a' b') :=
  fun i => Quant.le_add (h1 i) (h2 i)

theorem Uses.le_join (h1 : Uses.le a a') (h2 : Uses.le b b') :
    Uses.le (Uses.join a b) (Uses.join a' b') :=
  fun i => Quant.le_join (h1 i) (h2 i)

theorem Uses.le_tail (h : Uses.le a b) : Uses.le (Uses.tail a) (Uses.tail b) :=
  fun i => h (i + 1)

theorem Uses.add_zero (π : Uses) : Uses.add π Uses.zero = π := by
  funext i; exact Quant.add_none (π i)

theorem Uses.zero_add (π : Uses) : Uses.add Uses.zero π = π := by
  funext i; rfl

theorem Uses.add_assoc (a b c : Uses) :
    Uses.add (Uses.add a b) c = Uses.add a (Uses.add b c) := by
  funext i; exact Quant.add_assoc _ _ _

theorem Uses.le_add_left (a b : Uses) : Uses.le a (Uses.add a b) :=
  fun _ => Quant.le_add_left _ _

theorem Uses.le_add_right (a b : Uses) : Uses.le b (Uses.add a b) :=
  fun _ => Quant.le_add_right _ _

theorem Uses.le_join_left (a b : Uses) : Uses.le a (Uses.join a b) :=
  fun _ => Quant.le_join_left _ _

theorem Uses.le_join_right (a b : Uses) : Uses.le b (Uses.join a b) :=
  fun _ => Quant.le_join_right _ _

-- weakening reindex: open a fresh (unused) slot at depth n
def Uses.lift (n : Nat) (π : Uses) : Uses :=
  fun i => if i < n then π i else if i = n then .None else π (i - 1)

-- weakening by n fresh slots at the bottom
def Uses.liftN (n : Nat) (π : Uses) : Uses :=
  fun i => if i < n then .None else π (i - n)

-- substitution reindex: close slot n, charging the substituted value's
-- measure πv (shifted up by n) scaled by the closed slot's measure
def Uses.cut (n : Nat) (π : Uses) (πv : Uses) : Uses :=
  fun i => if i < n then π i
           else Quant.add (π (i + 1)) (Quant.mul (π n) (πv (i - n)))

theorem Uses.lift_zero (n : Nat) : Uses.lift n Uses.zero = Uses.zero := by
  funext i
  simp only [Uses.lift, Uses.zero]
  split
  · rfl
  · split <;> rfl

theorem Uses.lift_add (n : Nat) (a b : Uses) :
    Uses.lift n (Uses.add a b) = Uses.add (Uses.lift n a) (Uses.lift n b) := by
  funext i
  simp only [Uses.lift, Uses.add]
  split
  · rfl
  · split <;> rfl

theorem Uses.lift_join (n : Nat) (a b : Uses) :
    Uses.lift n (Uses.join a b) = Uses.join (Uses.lift n a) (Uses.lift n b) := by
  funext i
  simp only [Uses.lift, Uses.join]
  split
  · rfl
  · split <;> rfl

theorem Uses.lift_tail (n : Nat) (π : Uses) :
    Uses.lift n (Uses.tail π) = Uses.tail (Uses.lift (n + 1) π) := by
  funext i
  simp only [Uses.lift, Uses.tail]
  by_cases h1 : i < n
  · rw [if_pos h1, if_pos (by omega : i + 1 < n + 1)]
  · rw [if_neg h1]
    by_cases h2 : i = n
    · rw [if_pos h2, if_neg (by omega : ¬ i + 1 < n + 1),
        if_pos (by omega : i + 1 = n + 1)]
    · rw [if_neg h2, if_neg (by omega : ¬ i + 1 < n + 1),
        if_neg (by omega : ¬ i + 1 = n + 1)]
      congr 1
      omega

theorem Uses.lift_head (n : Nat) (π : Uses) : Uses.lift (n + 1) π 0 = π 0 := by
  simp [Uses.lift]

theorem Uses.lift_one_lt (n i : Nat) (q : Quant) (h : i < n) :
    Uses.lift n (Uses.one i q) = Uses.one i q := by
  funext j
  simp only [Uses.lift, Uses.one]
  by_cases h1 : j < n
  · rw [if_pos h1]
  · rw [if_neg h1]
    by_cases h2 : j = n
    · rw [if_pos h2, if_neg (by omega : ¬ j = i)]
    · rw [if_neg h2, if_neg (by omega : ¬ j - 1 = i),
        if_neg (by omega : ¬ j = i)]

theorem Uses.lift_one_ge (n i : Nat) (q : Quant) (h : n ≤ i) :
    Uses.lift n (Uses.one i q) = Uses.one (i + 1) q := by
  funext j
  simp only [Uses.lift, Uses.one]
  by_cases h1 : j < n
  · rw [if_pos h1, if_neg (by omega : ¬ j = i), if_neg (by omega : ¬ j = i + 1)]
  · rw [if_neg h1]
    by_cases h2 : j = n
    · rw [if_pos h2, if_neg (by omega : ¬ j = i + 1)]
    · rw [if_neg h2]
      by_cases h3 : j - 1 = i
      · rw [if_pos h3, if_pos (by omega : j = i + 1)]
      · rw [if_neg h3, if_neg (by omega : ¬ j = i + 1)]

theorem Uses.liftN_zero (πv : Uses) : Uses.liftN 0 πv = πv := by
  funext i; simp [Uses.liftN]

theorem Uses.lift0_liftN (n : Nat) (πv : Uses) :
    Uses.lift 0 (Uses.liftN n πv) = Uses.liftN (n + 1) πv := by
  funext i
  simp only [Uses.lift, Uses.liftN]
  by_cases h1 : i = 0
  · subst h1
    rw [if_neg (by omega : ¬ (0:Nat) < 0), if_pos rfl,
      if_pos (by omega : (0:Nat) < n + 1)]
  · rw [if_neg (by omega : ¬ i < 0), if_neg h1]
    by_cases h2 : i - 1 < n
    · rw [if_pos h2, if_pos (by omega : i < n + 1)]
    · rw [if_neg h2, if_neg (by omega : ¬ i < n + 1)]
      congr 1
      omega

theorem Uses.cut_zero_val (n : Nat) (πv : Uses) :
    Uses.cut n Uses.zero πv = Uses.zero := by
  funext i
  simp only [Uses.cut, Uses.zero]
  split <;> rfl

theorem Uses.cut_add (n : Nat) (a b πv : Uses) :
    Uses.cut n (Uses.add a b) πv
      = Uses.add (Uses.cut n a πv) (Uses.cut n b πv) := by
  funext i
  simp only [Uses.cut, Uses.add]
  split
  · rfl
  · exact Quant.cut_add_point _ _ _ _ _

theorem Uses.cut_join_le (n : Nat) (a b πv : Uses) :
    Uses.le (Uses.join (Uses.cut n a πv) (Uses.cut n b πv))
      (Uses.cut n (Uses.join a b) πv) := by
  intro i
  simp only [Uses.cut, Uses.join]
  split
  · exact Quant.le_refl _
  · exact Quant.cut_join_point _ _ _ _ _

theorem Uses.cut_tail (n : Nat) (π πv : Uses) :
    Uses.cut n (Uses.tail π) πv = Uses.tail (Uses.cut (n + 1) π πv) := by
  funext i
  simp only [Uses.cut, Uses.tail]
  by_cases h1 : i < n
  · rw [if_pos h1, if_pos (by omega : i + 1 < n + 1)]
  · rw [if_neg h1, if_neg (by omega : ¬ i + 1 < n + 1),
      (by omega : i + 1 - (n + 1) = i - n)]

theorem Uses.cut_head (n : Nat) (π πv : Uses) :
    Uses.cut (n + 1) π πv 0 = π 0 := by
  simp [Uses.cut]

theorem Uses.cut_one_lt (n i : Nat) (qo : Quant) (πv : Uses) (h : i < n) :
    Uses.cut n (Uses.one i qo) πv = Uses.one i qo := by
  funext j
  simp only [Uses.cut, Uses.one]
  by_cases h1 : j < n
  · rw [if_pos h1]
  · rw [if_neg h1, if_neg (by omega : ¬ j + 1 = i),
      if_neg (by omega : ¬ n = i), if_neg (by omega : ¬ j = i)]
    rfl

theorem Uses.cut_one_eq (n : Nat) (qo : Quant) (πv : Uses) :
    Uses.cut n (Uses.one n qo) πv
      = fun i => if i < n then .None else Quant.mul qo (πv (i - n)) := by
  funext j
  simp only [Uses.cut, Uses.one]
  by_cases h1 : j < n
  · rw [if_pos h1, if_pos h1, if_neg (by omega : ¬ j = n)]
  · rw [if_neg h1, if_neg h1, if_neg (by omega : ¬ j + 1 = n)]
    simp
    rfl

theorem Uses.cut_one_gt (n j0 : Nat) (qo : Quant) (πv : Uses) (h : n ≤ j0) :
    Uses.cut n (Uses.one (j0 + 1) qo) πv = Uses.one j0 qo := by
  funext j
  simp only [Uses.cut, Uses.one]
  by_cases h1 : j < n
  · rw [if_pos h1, if_neg (by omega : ¬ j = j0 + 1), if_neg (by omega : ¬ j = j0)]
  · rw [if_neg h1, if_neg (by omega : ¬ n = j0 + 1)]
    by_cases h2 : j + 1 = j0 + 1
    · rw [if_pos h2, if_pos (by omega : j = j0), Quant.none_mul,
        Quant.add_none]
    · rw [if_neg h2, if_neg (by omega : ¬ j = j0)]
      rfl


-- ============================================================================
-- METATHEORY §D1 — the dead fragment measures nothing; reduction and
-- conversion commute with shift and subst; closedness through spines.
-- ============================================================================

theorem Check.cast (h : Check β q Γ t T π) (e : π = π') :
    Check β q Γ t T π' :=
  e ▸ h

theorem Check.none_le_zero (h : Check β q Γ t T π) :
    q = .None → Uses.le π Uses.zero := by
  induction h with
  | var _ =>
    intro hq; subst hq
    intro i
    simp only [Uses.one, Uses.zero]
    split <;> trivial
  | ref _ => intro _; exact Uses.le_refl _
  | refA _ _ => intro _; exact Uses.le_refl _
  | adt _ => intro _; exact Uses.le_refl _
  | ctr _ _ _ => intro _; exact Uses.le_refl _
  | typ => intro _; exact Uses.le_refl _
  | all _ _ _ _ _ => intro _; exact Uses.le_refl _
  | lam _ _ ihf =>
    intro hq; subst hq
    exact Uses.le_tail (ihf _root_.rfl)
  | app _ _ _ ihf ihx =>
    intro hq; subst hq
    exact Uses.le_add (ihf _root_.rfl) (ihx (Quant.dem_none _))
  | let_ _ _ _ _ ihv ihb =>
    intro hq; subst hq
    exact Uses.le_add (ihv (Quant.dem_none _)) (Uses.le_tail (ihb _root_.rfl))
  | eql _ _ _ _ _ _ => intro _; exact Uses.le_refl _
  | rfl _ => intro _; exact Uses.le_refl _
  | rwt _ _ _ ihe _ ihf =>
    intro hq; subst hq
    exact Uses.le_add (ihe _root_.rfl) (ihf _root_.rfl)
  | mat _ _ _ _ _ _ _ _ _ ihh ihm =>
    intro hq; subst hq
    exact fun i => Quant.join_le (ihh _root_.rfl i) (ihm _root_.rfl i)
  | efq _ _ _ => intro _; exact Uses.le_refl _
  | cnv _ _ ih => exact ih

theorem Check.none_zero (h : Check β .None Γ t T π) :
    Check β .None Γ t T Uses.zero :=
  h.cast (Uses.le_zero_eq (h.none_le_zero _root_.rfl))

-- dead weakening: any judgment replays at the dead demand
theorem Check.at_none (h : Check β q Γ t T π) :
    ∃ π', Check β .None Γ t T π' := by
  induction h with
  | var hg => exact ⟨_, .var hg⟩
  | ref hk _ => exact ⟨_, .ref hk (fun hq => absurd _root_.rfl hq)⟩
  | refA hk h0 => exact ⟨_, .refA hk h0⟩
  | adt hk => exact ⟨_, .adt hk⟩
  | ctr hk hc hr => exact ⟨_, .ctr hk hc hr⟩
  | typ => exact ⟨_, .typ⟩
  | all hq hA hB _ _ => exact ⟨_, .all hq hA hB⟩
  | lam _ hle ihf =>
    obtain ⟨π', hf'⟩ := ihf
    exact ⟨_, .lam hf'.none_zero (by
      show Quant.le (Uses.zero 0) _
      exact Quant.none_le _)⟩
  | app hq hf hx ihf ihx =>
    obtain ⟨πf', hf'⟩ := ihf
    obtain ⟨πx', hx'⟩ := ihx
    exact ⟨_, .app hq hf' ((Quant.dem_none _).symm ▸ hx')⟩
  | let_ hq hv hb hle ihv ihb =>
    obtain ⟨πv', hv'⟩ := ihv
    obtain ⟨πb', hb'⟩ := ihb
    exact ⟨_, .let_ hq ((Quant.dem_none _).symm ▸ hv') hb'.none_zero (by
      show Quant.le (Uses.zero 0) _
      exact Quant.none_le _)⟩
  | eql hT ha hb _ _ _ => exact ⟨_, .eql hT ha hb⟩
  | rfl hc => exact ⟨_, .rfl hc⟩
  | rwt he hP hf ihe _ ihf =>
    obtain ⟨πe', he'⟩ := ihe
    obtain ⟨πf', hf'⟩ := ihf
    exact ⟨_, .rwt he' hP hf'⟩
  | mat hk hc hr hlen hlive hins hgoal hh hm ihh ihm =>
    obtain ⟨πh', hh'⟩ := ihh
    obtain ⟨πm', hm'⟩ := ihm
    exact ⟨_, .mat hk hc hr hlen (fun h => absurd _root_.rfl h) hins hgoal hh' hm'⟩
  | efq hk hall _ =>
    exact ⟨_, .efq hk hall (fun h => absurd _root_.rfl h)⟩
  | cnv _ hc iht =>
    obtain ⟨π', ht'⟩ := iht
    exact ⟨_, .cnv ht' hc⟩

-- reduction and conversion commute with shift and subst (closed book)
theorem Red.shiftS (hβ : Book.Closed β) (h : Red β .strong t t') (d : Nat) :
    Red β .strong (t.shift d) (t'.shift d) := by
  induction h with
  | refl => exact .refl
  | step s _ ih => exact (Par.red hβ ((Step.par s).shift hβ d)).trans ih

theorem Red.substS (hβ : Book.Closed β) (ht : Red β .strong t t')
    (hw : Red β .strong w w') (d : Nat) :
    Red β .strong (Term.subst d w t) (Term.subst d w' t') := by
  have h2 : Red β .strong (Term.subst d w t') (Term.subst d w' t') := by
    induction hw with
    | refl => exact .refl
    | step s _ ih =>
      exact (Par.red hβ ((Par.refl t').subst hβ d (Step.par s))).trans ih
  have h1 : Red β .strong (Term.subst d w t) (Term.subst d w t') := by
    clear h2
    induction ht with
    | refl => exact .refl
    | step s _ ih =>
      exact (Par.red hβ ((Step.par s).subst hβ d (Par.refl w))).trans ih
  exact h1.trans h2

theorem Conv.shift (hβ : Book.Closed β) (h : Conv β a b) (d : Nat) :
    Conv β (a.shift d) (b.shift d) := by
  obtain ⟨c, h1, h2⟩ := h
  exact ⟨c.shift d, h1.shiftS hβ d, h2.shiftS hβ d⟩

theorem Conv.subst (hβ : Book.Closed β) (ht : Conv β t t') (hw : Conv β w w')
    (d : Nat) : Conv β (Term.subst d w t) (Term.subst d w' t') := by
  obtain ⟨c, h1, h2⟩ := ht
  obtain ⟨e, g1, g2⟩ := hw
  exact ⟨Term.subst d e c, Red.substS hβ h1 g1 d, Red.substS hβ h2 g2 d⟩

theorem Conv.subst_w (hβ : Book.Closed β) (t : Term) (hw : Conv β w w')
    (d : Nat) : Conv β (Term.subst d w t) (Term.subst d w' t) :=
  Conv.subst hβ (Conv.refl t) hw d

-- closedness through spines and retip
theorem Term.closed_apps : ∀ (as : List Term) (h : Term) (m : Nat),
    (Term.apps h as).Closed m ↔ (h.Closed m ∧ ∀ x ∈ as, x.Closed m) := by
  intro as
  induction as with
  | nil =>
    intro h m
    exact ⟨fun hc => ⟨hc, fun x hx => nomatch hx⟩, fun hc => hc.1⟩
  | cons a as ih =>
    intro h m
    constructor
    · intro hc
      obtain ⟨⟨hh, ha⟩, hrest⟩ := (ih (.App h a) m).mp hc
      exact ⟨hh, fun x hx => by
        cases hx with
        | head => exact ha
        | tail _ hx => exact hrest x hx⟩
    · intro ⟨hh, hall⟩
      exact (ih (.App h a) m).mpr
        ⟨⟨hh, hall a (.head as)⟩, fun x hx => hall x (.tail a hx)⟩

theorem Term.spine_closed {t : Term} {m : Nat} (h : t.Closed m) :
    (Term.spine t).1.Closed m ∧ ∀ x ∈ (Term.spine t).2, x.Closed m := by
  have := (Term.closed_apps (Term.spine t).2 (Term.spine t).1 m).mp
  rw [Term.apps_spine t] at this
  exact this h

theorem Term.retip_closed (r : List Nat) :
    ∀ (n : Nat) (t : Term) (m : Nat), t.Closed m → (Term.retip r n t).Closed m := by
  intro n
  induction n with
  | zero =>
    intro t m hc
    simp only [Term.retip]
    split
    case _ a r' heq =>
      obtain ⟨_, hargs⟩ := Term.spine_closed hc
      exact (Term.closed_apps _ _ _).mpr ⟨trivial, hargs⟩
    case _ => exact hc
  | succ n ih =>
    intro t m hc
    cases t <;> simp only [Term.retip] <;> try exact hc
    case All q A B => exact ⟨hc.1, ih B (m + 1) hc.2⟩

-- shift transport for the mat premises
theorem Insts.shift (h : Insts T ps T') (d : Nat) :
    Insts (T.shift d) (ps.map (Term.shift d)) (T'.shift d) := by
  induction h generalizing d with
  | nil => exact .nil
  | cons hi ih =>
    refine Insts.cons ?_
    rw [← Term.shift_subst0]
    exact ih d

theorem MatGoal.shift (h : MatGoal q' n B s tel G) :
    ∀ d, MatGoal q' n (B.shift (d + 1)) (s.shift d) (tel.shift d)
      (G.shift d) := by
  induction h with
  | zero =>
    intro d
    rw [Term.shift_subst0]
    exact .zero
  | @succ n B s Bf G qf F hg ih =>
    intro d
    show MatGoal q' (n + 1) _ _ (.All qf (F.shift d) (Bf.shift (d + 1))) _
    have h2 := ih (d + 1)
    rw [← Term.shift_shift B 1 (d + 1) (by omega)] at h2
    have e : Term.shift (d + 1) (.App (Term.shift 0 s) (.Var 0))
        = .App (Term.shift 0 (s.shift d)) (.Var 0) := by
      show Term.App _ _ = _
      rw [Term.shift_shift0]
      rfl
    rw [e] at h2
    exact MatGoal.succ h2

-- context insertion: Γ' is Γ with U slotted in at depth n
inductive Ins (U : Term) : Nat → Ctx → Ctx → Prop
  | zero : Ins U 0 Γ (U :: Γ)
  | succ : Ins U n Γ Γ' → Ins U (n + 1) (A :: Γ) (Term.shift n A :: Γ')

theorem Ins.get_lt (h : Ins U n Γ Γ') : ∀ {i T}, i < n →
    Ctx.get Γ i = some T → Ctx.get Γ' i = some (Term.shift n T) := by
  induction h with
  | zero => intro i T hi; cases hi
  | @succ n Γ Γ' A hins ih =>
    intro i T hi hg
    cases i with
    | zero =>
      simp only [Ctx.get] at hg ⊢
      cases hg
      rw [Term.shift_shift0]
    | succ j =>
      simp only [Ctx.get] at hg ⊢
      cases hj : Ctx.get Γ j with
      | none => rw [hj] at hg; cases hg
      | some V =>
        rw [hj] at hg
        simp only [Option.map_some] at hg
        cases hg
        rw [ih (Nat.lt_of_succ_lt_succ hi) hj]
        simp only [Option.map_some]
        rw [Term.shift_shift0]

theorem Ins.get_ge (h : Ins U n Γ Γ') : ∀ {i T}, n ≤ i →
    Ctx.get Γ i = some T → Ctx.get Γ' (i + 1) = some (Term.shift n T) := by
  induction h with
  | zero =>
    intro i T _ hg
    simp only [Ctx.get, hg, Option.map_some]
  | @succ n Γ Γ' A hins ih =>
    intro i T hi hg
    cases i with
    | zero => cases hi
    | succ j =>
      simp only [Ctx.get] at hg ⊢
      cases hj : Ctx.get Γ j with
      | none => rw [hj] at hg; cases hg
      | some V =>
        rw [hj] at hg
        simp only [Option.map_some] at hg
        cases hg
        rw [ih (Nat.le_of_succ_le_succ hi) hj]
        simp only [Option.map_some]
        rw [Term.shift_shift0]

theorem Book.Closed.adtd (hβ : Book.Closed β) (h : Book.adt β a = some A) :
    A.sig.Closed 0 ∧ ∀ c C, AdtD.ctr A c = some C → C.ty.Closed 0 := by
  unfold Book.adt at h
  split at h
  case _ heq => cases h; exact hβ _ _ heq
  case _ => cases h

-- weakening: a judgment survives a context insertion, with its subject,
-- type and measure lifted
theorem Check.weaken (hβ : Book.Closed β) (h : Check β q Γ t T π) :
    ∀ {n : Nat} {U : Term} {Γ' : Ctx}, Ins U n Γ Γ' →
    Check β q Γ' (Term.shift n t) (Term.shift n T) (Uses.lift n π) := by
  induction h with
  | @var Γ i T q hg =>
    intro n U Γ' hins
    simp only [Term.shift]
    by_cases hi : i < n
    · rw [if_pos hi, Uses.lift_one_lt n i q hi]
      exact .var (hins.get_lt hi hg)
    · rw [if_neg hi, Uses.lift_one_ge n i q (by omega)]
      exact .var (hins.get_ge (by omega) hg)
  | @ref k d q Γ hk hlv =>
    intro n U Γ' hins
    rw [Term.shift_closed d.ty 0 n (hβ.defn hk).1 (Nat.zero_le n),
      Uses.lift_zero]
    exact .ref hk hlv
  | @refA k A q Γ hk h0 =>
    intro n U Γ' hins
    rw [Uses.lift_zero]
    exact .refA hk h0
  | @adt a A q Γ r hk =>
    intro n U Γ' hins
    rw [Term.shift_closed A.sig 0 n (hβ.adtd hk).1 (Nat.zero_le n),
      Uses.lift_zero]
    exact .adt hk
  | @ctr a A c C r q Γ hk hc hr =>
    intro n U Γ' hins
    rw [Term.shift_closed _ 0 n
      (Term.retip_closed r _ C.ty 0 ((hβ.adtd hk).2 c C hc)) (Nat.zero_le n),
      Uses.lift_zero]
    exact .ctr hk hc hr
  | typ =>
    intro n U Γ' hins
    rw [Uses.lift_zero]
    exact .typ
  | all hq hA hB ihA ihB =>
    intro n U Γ' hins
    rw [Uses.lift_zero]
    exact .all hq (ihA hins) (ihB (Ins.succ hins))
  | lam hf hle ihf =>
    intro n U Γ' hins
    rw [Uses.lift_tail]
    refine Check.lam (ihf (Ins.succ hins)) ?_
    rw [Uses.lift_head]
    exact hle
  | app hq hf hx ihf ihx =>
    intro n U Γ' hins
    rw [Uses.lift_add, Term.shift_subst0]
    exact .app hq (ihf hins) (ihx hins)
  | @let_ qb q Γ v A πv b T π hq hv hb hle ihv ihb =>
    intro n U Γ' hins
    rw [Uses.lift_add, Uses.lift_tail]
    refine Check.let_ hq (ihv hins) ?_ ?_
    · have := ihb (Ins.succ hins)
      rwa [Term.shift_shift0] at this
    · rw [Uses.lift_head]
      exact hle
  | eql hT ha hb ihT iha ihb =>
    intro n U Γ' hins
    rw [Uses.lift_zero]
    exact .eql (ihT hins) (iha hins) (ihb hins)
  | rfl hc =>
    intro n U Γ' hins
    rw [Uses.lift_zero]
    exact .rfl (hc.shift hβ n)
  | rwt he hP hf ihe ihP ihf =>
    intro n U Γ' hins
    rw [Uses.lift_add]
    have hP' := ihP hins
    rw [Term.shift_jmotive] at hP'
    exact .rwt (ihe hins) hP' (ihf hins)
  | @mat a A c C r q q' ps telF B G Γ h πh m πm hk hc hr hlen hlive hins
      hgoal hh hm ihh ihm =>
    intro n U Γ' hI
    rw [Uses.lift_join]
    simp only [Term.shift, Term.shift_apps]
    have hi' := hins.shift n
    rw [Term.shift_closed C.ty 0 n ((hβ.adtd hk).2 c C hc)
      (Nat.zero_le n)] at hi'
    have hg' := hgoal.shift n
    have e : Term.shift n (Term.apps (.Ctr a c) ps)
        = Term.apps (.Ctr a c) (ps.map (Term.shift n)) := by
      rw [Term.shift_apps]
      rfl
    rw [e] at hg'
    refine Check.mat hk hc hr (by simp [hlen]) hlive hi' hg' (ihh hI) ?_
    have := ihm hI
    simp only [Term.shift, Term.shift_apps] at this
    exact this
  | @efq a A r q q' Γ ps B hk hall hlive =>
    intro n U Γ' hins
    rw [Uses.lift_zero]
    have : Term.shift n (.All q' (Term.apps (.Adt a r) ps) B)
        = .All q' (Term.apps (.Adt a r) (ps.map (Term.shift n)))
            (B.shift (n + 1)) := by
      simp only [Term.shift, Term.shift_apps]
    rw [this]
    exact .efq hk hall hlive
  | cnv ht hc iht =>
    intro n U Γ' hins
    exact .cnv (iht hins) (hc.shift hβ n)


-- ============================================================================
-- METATHEORY §D2 — the substitution lemma, with the usage accounting.
-- Cut v T n Γb Γres Γtl: Γb splits as n entries over T :: Γtl; Γres is
-- the residue with v substituted through the prefix. The measure of the
-- result is bounded by Uses.cut: the closed slot's measure scales the
-- substituted value's measure.
-- ============================================================================

theorem Quant.add_eq_none : ∀ {a b : Quant},
    Quant.add a b = .None → a = .None ∧ b = .None := by
  intro a b h
  cases a <;> cases b <;> first
  | exact ⟨rfl, rfl⟩
  | exact absurd h (by intro hc; cases hc)

theorem Quant.join_eq_none : ∀ {a b : Quant},
    Quant.join a b = .None → a = .None ∧ b = .None := by
  intro a b h
  cases a <;> cases b <;> first
  | exact ⟨rfl, rfl⟩
  | exact absurd h (by intro hc; cases hc)

theorem Quant.dem_ne_many : ∀ {q' q : Quant},
    q ≠ .Many → Quant.dem q' q ≠ .Many := by
  intro q' q h
  cases q' <;> cases q <;> first
  | exact h
  | (intro hc; cases hc)

theorem Term.shiftN_succ' (n : Nat) (t : Term) :
    Term.shift 0 (Term.shiftN n t) = Term.shiftN (n + 1) t := rfl

theorem Term.shift_shiftN : ∀ (n d : Nat) (t : Term), d ≤ n →
    Term.shift d (Term.shiftN n t) = Term.shiftN (n + 1) t := by
  intro n
  induction n with
  | zero =>
    intro d t hd
    have h0 : d = 0 := by omega
    subst h0
    rfl
  | succ n ih =>
    intro d t hd
    cases d with
    | zero => rfl
    | succ d' =>
      show Term.shift (d' + 1) (Term.shift 0 (Term.shiftN n t)) = _
      rw [← Term.shift_shift (Term.shiftN n t) 0 d' (Nat.zero_le d'),
        ih d' t (by omega)]
      rfl

theorem Term.subst_shiftN (n : Nat) (w t : Term) :
    Term.subst n w (Term.shiftN (n + 1) t) = Term.shiftN n t := by
  rw [← Term.shift_shiftN n n t (Nat.le_refl n)]
  exact Term.subst_shift _ n w

theorem Check.erased (h : Check β q Γ t T π) :
    Check β .None Γ t T Uses.zero := by
  obtain ⟨π', h'⟩ := h.at_none
  exact h'.none_zero

-- subst transport for the mat premises
theorem Insts.subst (h : Insts T ps T') :
    ∀ (d : Nat) (w : Term),
    Insts (Term.subst d w T) (ps.map (Term.subst d w)) (Term.subst d w T') := by
  induction h with
  | nil => intro d w; exact .nil
  | cons hi ih =>
    intro d w
    refine Insts.cons ?_
    rw [← Term.subst_subst0]
    exact ih d w

theorem MatGoal.subst (h : MatGoal q' n B s tel G) :
    ∀ (d : Nat) (w : Term),
    MatGoal q' n (Term.subst (d + 1) (Term.shift 0 w) B) (Term.subst d w s)
      (Term.subst d w tel) (Term.subst d w G) := by
  induction h with
  | zero =>
    intro d w
    rw [Term.subst_subst0]
    exact .zero
  | @succ n B s Bf G qf F hg ih =>
    intro d w
    show MatGoal q' (n + 1) _ _
      (.All qf (Term.subst d w F) (Term.subst (d + 1) (Term.shift 0 w) Bf))
      (.All (Quant.dem qf q') (Term.subst d w F)
        (Term.subst (d + 1) (Term.shift 0 w) G))
    have h2 := ih (d + 1) (Term.shift 0 w)
    have eB : Term.subst (d + 1 + 1) (Term.shift 0 (Term.shift 0 w))
        (Term.shift 1 B)
        = Term.shift 1 (Term.subst (d + 1) (Term.shift 0 w) B) := by
      rw [Term.shift_subst_lt B 1 (d + 1) (Term.shift 0 w) (by omega),
        Term.shift_shift0]
    rw [eB] at h2
    have e1 : Term.subst (d + 1) (Term.shift 0 w)
        (.App (Term.shift 0 s) (.Var 0))
        = .App (Term.shift 0 (Term.subst d w s)) (.Var 0) := by
      show Term.App _ _ = _
      rw [← Term.shift_subst_lt s 0 d w (Nat.zero_le d)]
      simp only [Term.subst]
      rw [if_neg (by omega : ¬ (0 : Nat) = d + 1),
        if_neg (by omega : ¬ d + 1 < 0)]
    rw [e1] at h2
    exact MatGoal.succ h2

inductive Cut (v T : Term) : Nat → Ctx → Ctx → Ctx → Prop
  | zero : Cut v T 0 (T :: Γ) Γ Γ
  | succ : Cut v T n Γ Γres Γtl →
           Cut v T (n + 1) (A :: Γ)
             (Term.subst n (Term.shiftN n v) A :: Γres) Γtl

theorem Cut.get_lt (h : Cut v T n Γb Γres Γtl) : ∀ {i U}, i < n →
    Ctx.get Γb i = some U →
    Ctx.get Γres i = some (Term.subst n (Term.shiftN n v) U) := by
  induction h with
  | zero => intro i U hi; cases hi
  | @succ n Γ Γres Γtl A hcut ih =>
    intro i U hi hg
    cases i with
    | zero =>
      simp only [Ctx.get] at hg ⊢
      cases hg
      rw [Term.shift_subst_lt A 0 n (Term.shiftN n v) (Nat.zero_le n),
        Term.shiftN_succ']
    | succ j =>
      simp only [Ctx.get] at hg ⊢
      cases hj : Ctx.get Γ j with
      | none => rw [hj] at hg; cases hg
      | some V =>
        rw [hj] at hg
        simp only [Option.map_some] at hg
        cases hg
        rw [ih (Nat.lt_of_succ_lt_succ hi) hj]
        simp only [Option.map_some]
        rw [Term.shift_subst_lt V 0 n (Term.shiftN n v) (Nat.zero_le n),
          Term.shiftN_succ']

theorem Cut.get_eq (h : Cut v T n Γb Γres Γtl) :
    Ctx.get Γb n = some (Term.shiftN (n + 1) T) := by
  induction h with
  | zero => simp only [Ctx.get]; rfl
  | @succ n Γ Γres Γtl A hcut ih =>
    simp only [Ctx.get]
    rw [ih]
    simp only [Option.map_some]
    rw [Term.shiftN_succ']

theorem Cut.get_gt (h : Cut v T n Γb Γres Γtl) : ∀ {j U}, n ≤ j →
    Ctx.get Γb (j + 1) = some U →
    Ctx.get Γres j = some (Term.subst n (Term.shiftN n v) U) := by
  induction h with
  | @zero Γ =>
    intro j U _ hg
    simp only [Ctx.get] at hg
    cases hj : Ctx.get Γ j with
    | none => rw [hj] at hg; cases hg
    | some V =>
      rw [hj] at hg
      simp only [Option.map_some] at hg
      cases hg
      rw [Term.subst_shift V 0 (Term.shiftN 0 v)]
  | @succ n Γ Γres Γtl A hcut ih =>
    intro j U hj hg
    cases j with
    | zero => cases hj
    | succ i =>
      simp only [Ctx.get] at hg ⊢
      cases hgi : Ctx.get Γ (i + 1) with
      | none => rw [hgi] at hg; cases hg
      | some V =>
        rw [hgi] at hg
        simp only [Option.map_some] at hg
        cases hg
        rw [ih (Nat.le_of_succ_le_succ hj) hgi]
        simp only [Option.map_some]
        rw [Term.shift_subst_lt V 0 n (Term.shiftN n v) (Nat.zero_le n),
          Term.shiftN_succ']

theorem Cut.value (hβ : Book.Closed β) (h : Cut v T n Γb Γres Γtl) :
    ∀ {qv πv}, Check β qv Γtl v T πv →
    Check β qv Γres (Term.shiftN n v) (Term.shiftN n T)
      (Uses.liftN n πv) := by
  induction h with
  | zero =>
    intro qv πv hv
    exact hv.cast (Uses.liftN_zero πv).symm
  | @succ n Γ Γres Γtl A hcut ih =>
    intro qv πv hv
    have hw := (ih hv).weaken hβ
      (Ins.zero (U := Term.subst n (Term.shiftN n v) A))
    rw [Uses.lift0_liftN] at hw
    exact hw

theorem sub_none_zero
    (h : ∃ π', Uses.le π' X ∧ Check β .None Γres t T π') :
    Check β .None Γres t T Uses.zero := by
  obtain ⟨π', _, hc⟩ := h
  exact hc.none_zero

-- the substitution lemma: substituting a value checked once (or into a
-- dead slot) preserves the judgment, and the measure is bounded by the
-- cut of the original
theorem Check.sub (hβ : Book.Closed β) (h : Check β q Γb b B π) :
    ∀ {n : Nat} {v T : Term} {πv : Uses} {qv : Quant} {Γres Γtl : Ctx},
    q ≠ .Many →
    (qv = .Lone ∨ π n = .None) →
    Cut v T n Γb Γres Γtl →
    Check β qv Γtl v T πv →
    ∃ π', Uses.le π' (Uses.cut n π πv) ∧
      Check β q Γres (Term.subst n (Term.shiftN n v) b)
        (Term.subst n (Term.shiftN n v) B) π' := by
  induction h with
  | @var Γb i T0 qo hg =>
    intro n v T πv qv Γres Γtl hq hfit hcut hv
    by_cases h1 : i < n
    · refine ⟨Uses.one i qo, ?_, ?_⟩
      · rw [Uses.cut_one_lt n i qo πv h1]
        exact Uses.le_refl _
      · have hs : Term.subst n (Term.shiftN n v) (Term.Var i) = Term.Var i := by
          simp only [Term.subst]
          rw [if_neg (by omega : ¬ (i : Nat) = n), if_neg (by omega : ¬ n < i)]
        rw [hs]
        exact Check.var (hcut.get_lt h1 hg)
    · by_cases h2 : i = n
      · subst h2
        have hT0 : T0 = Term.shiftN (i + 1) T := by
          have hge := hcut.get_eq
          rw [hg] at hge
          exact Option.some_inj.mp hge
        subst hT0
        have hs : Term.subst i (Term.shiftN i v) (Term.Var i)
            = Term.shiftN i v := by
          simp [Term.subst]
        rw [hs, Term.subst_shiftN]
        cases qo with
        | None =>
          exact ⟨Uses.zero, Uses.zero_le _, (hcut.value hβ hv).erased⟩
        | Lone =>
          cases hfit with
          | inl hqv =>
            subst hqv
            refine ⟨Uses.liftN i πv, ?_, hcut.value hβ hv⟩
            rw [Uses.cut_one_eq]
            intro j
            simp only [Uses.liftN]
            split
            · exact Quant.none_le _
            · rw [Quant.lone_mul]
              exact Quant.le_refl _
          | inr hnone =>
            exfalso
            simp [Uses.one] at hnone
        | Many => exact absurd _root_.rfl hq
      · cases i with
        | zero => omega
        | succ j =>
          refine ⟨Uses.one j qo, ?_, ?_⟩
          · rw [Uses.cut_one_gt n j qo πv (by omega)]
            exact Uses.le_refl _
          · have hs : Term.subst n (Term.shiftN n v) (Term.Var (j + 1))
                = Term.Var j := by
              simp only [Term.subst]
              rw [if_neg (by omega : ¬ (j + 1 : Nat) = n),
                if_pos (by omega : n < j + 1)]
              rfl
            rw [hs]
            exact Check.var (hcut.get_gt (by omega) hg)
  | ref hk hlv =>
    intro n v T πv qv Γres Γtl hq hfit hcut hv
    refine ⟨Uses.zero, by rw [Uses.cut_zero_val]; exact Uses.le_refl _, ?_⟩
    rw [Term.subst_closed _ 0 n (Term.shiftN n v) (hβ.defn hk).1
      (Nat.zero_le n)]
    exact Check.ref hk hlv
  | refA hk h0 =>
    intro n v T πv qv Γres Γtl hq hfit hcut hv
    exact ⟨Uses.zero, by rw [Uses.cut_zero_val]; exact Uses.le_refl _,
      .refA hk h0⟩
  | adt hk =>
    intro n v T πv qv Γres Γtl hq hfit hcut hv
    refine ⟨Uses.zero, by rw [Uses.cut_zero_val]; exact Uses.le_refl _, ?_⟩
    rw [Term.subst_closed _ 0 n (Term.shiftN n v) (hβ.adtd hk).1
      (Nat.zero_le n)]
    exact Check.adt hk
  | @ctr a A c C r qo Γb hk hc hr =>
    intro n v T πv qv Γres Γtl hq hfit hcut hv
    refine ⟨Uses.zero, by rw [Uses.cut_zero_val]; exact Uses.le_refl _, ?_⟩
    rw [Term.subst_closed _ 0 n (Term.shiftN n v)
      (Term.retip_closed r _ C.ty 0 ((hβ.adtd hk).2 c C hc)) (Nat.zero_le n)]
    exact Check.ctr hk hc hr
  | typ =>
    intro n v T πv qv Γres Γtl hq hfit hcut hv
    exact ⟨Uses.zero, by rw [Uses.cut_zero_val]; exact Uses.le_refl _, .typ⟩
  | all hqne hA hB ihA ihB =>
    intro n v T πv qv Γres Γtl hq hfit hcut hv
    have hA' := sub_none_zero (ihA (fun h => Quant.noConfusion h)
      (Or.inr (Quant.le_none (hA.none_le_zero _root_.rfl n))) hcut hv)
    have hB' := sub_none_zero (ihB (fun h => Quant.noConfusion h)
      (Or.inr (Quant.le_none (hB.none_le_zero _root_.rfl (n + 1))))
      hcut.succ hv)
    rw [← Term.shiftN_succ'] at hB'
    exact ⟨Uses.zero, by rw [Uses.cut_zero_val]; exact Uses.le_refl _,
      .all hqne hA' hB'⟩
  | @lam qo A' Γ' f B' π' q'' hf hle ihf =>
    intro n v T πv qv Γres Γtl hq hfit hcut hv
    obtain ⟨π'b, hleb, ihf'⟩ := ihf hq hfit hcut.succ hv
    have h0 : Quant.le (π'b 0) (π' 0) := by
      have := hleb 0
      rwa [Uses.cut_head] at this
    rw [← Term.shiftN_succ'] at ihf'
    refine ⟨Uses.tail π'b, ?_, ?_⟩
    · have := Uses.le_tail hleb
      rwa [← Uses.cut_tail] at this
    · exact Check.lam ihf' (Quant.le_trans h0 hle)
  | @app q3 q'' Γ' f A' B' πf x πx hq3 hf hx ihf ihx =>
    intro n v T πv qv Γres Γtl hq hfit hcut hv
    obtain ⟨π'f, hlef, ihf'⟩ := ihf hq
      (hfit.imp id (fun h => (Quant.add_eq_none h).1)) hcut hv
    obtain ⟨π'x, hlex, ihx'⟩ := ihx (Quant.dem_ne_many hq)
      (hfit.imp id (fun h => (Quant.add_eq_none h).2)) hcut hv
    refine ⟨Uses.add π'f π'x, ?_, ?_⟩
    · rw [Uses.cut_add]
      exact Uses.le_add hlef hlex
    · rw [Term.subst_subst0]
      rw [Term.shiftN_succ']
      exact Check.app hq3 ihf' ihx'
  | @let_ qb q'' Γ' vv A' πvv bb T' π' hqb hvv hbb hle ihv ihb =>
    intro n v T πv qv Γres Γtl hq hfit hcut hv
    obtain ⟨π'v, hlev, ihv'⟩ := ihv (Quant.dem_ne_many hq)
      (hfit.imp id (fun h => (Quant.add_eq_none h).1)) hcut hv
    obtain ⟨π'b, hleb, ihb'⟩ := ihb hq
      (hfit.imp id (fun h => (Quant.add_eq_none h).2)) hcut.succ hv
    have h0 : Quant.le (π'b 0) (π' 0) := by
      have := hleb 0
      rwa [Uses.cut_head] at this
    rw [← Term.shiftN_succ'] at ihb'
    have e : Term.subst (n + 1) (Term.shift 0 (Term.shiftN n v))
        (Term.shift 0 T')
        = Term.shift 0 (Term.subst n (Term.shiftN n v) T') := by
      rw [← Term.shift_subst_lt T' 0 n (Term.shiftN n v) (Nat.zero_le n)]
    rw [e] at ihb'
    refine ⟨Uses.add π'v (Uses.tail π'b), ?_, ?_⟩
    · rw [Uses.cut_add]
      refine Uses.le_add hlev ?_
      have := Uses.le_tail hleb
      rwa [← Uses.cut_tail] at this
    · exact Check.let_ hqb ihv' ihb' (Quant.le_trans h0 hle)
  | eql hTd had hbd ihT iha ihb =>
    intro n v T πv qv Γres Γtl hq hfit hcut hv
    have hT' := sub_none_zero (ihT (fun h => Quant.noConfusion h)
      (Or.inr (Quant.le_none (hTd.none_le_zero _root_.rfl n))) hcut hv)
    have ha' := sub_none_zero (iha (fun h => Quant.noConfusion h)
      (Or.inr (Quant.le_none (had.none_le_zero _root_.rfl n))) hcut hv)
    have hb' := sub_none_zero (ihb (fun h => Quant.noConfusion h)
      (Or.inr (Quant.le_none (hbd.none_le_zero _root_.rfl n))) hcut hv)
    exact ⟨Uses.zero, by rw [Uses.cut_zero_val]; exact Uses.le_refl _,
      .eql hT' ha' hb'⟩
  | rfl hc =>
    intro n v T πv qv Γres Γtl hq hfit hcut hv
    exact ⟨Uses.zero, by rw [Uses.cut_zero_val]; exact Uses.le_refl _,
      .rfl (Conv.subst hβ hc (Conv.refl _) n)⟩
  | @rwt q'' Γ' e a' b' T' πe P πP f πf he hP hf ihe ihP ihf =>
    intro n v T πv qv Γres Γtl hq hfit hcut hv
    obtain ⟨π'e, hlee, ihe'⟩ := ihe hq
      (hfit.imp id (fun h => (Quant.add_eq_none h).1)) hcut hv
    obtain ⟨π'f, hlef, ihf'⟩ := ihf hq
      (hfit.imp id (fun h => (Quant.add_eq_none h).2)) hcut hv
    have hP' := sub_none_zero (ihP (fun h => Quant.noConfusion h)
      (Or.inr (Quant.le_none (hP.none_le_zero _root_.rfl n))) hcut hv)
    refine ⟨Uses.add π'e π'f, ?_, ?_⟩
    · rw [Uses.cut_add]
      exact Uses.le_add hlee hlef
    · rw [Term.subst_jmotive] at hP'
      exact Check.rwt ihe' hP' ihf'
  | @mat a A c C r q'' q3 ps telF B' G Γ' hh πh mm πm hk hc hr hlen hlive
      hins hgoal hharm hmarm ihh ihm =>
    intro n v T πv qv Γres Γtl hq hfit hcut hv
    obtain ⟨π'h, hleh, ihh'⟩ := ihh hq
      (hfit.imp id (fun h => (Quant.join_eq_none h).1)) hcut hv
    obtain ⟨π'm, hlem, ihm'⟩ := ihm hq
      (hfit.imp id (fun h => (Quant.join_eq_none h).2)) hcut hv
    have hins' := hins.subst n (Term.shiftN n v)
    rw [Term.subst_closed C.ty 0 n _ ((hβ.adtd hk).2 c C hc)
      (Nat.zero_le n)] at hins'
    have hg' := hgoal.subst n (Term.shiftN n v)
    have e : Term.subst n (Term.shiftN n v) (Term.apps (.Ctr a c) ps)
        = Term.apps (.Ctr a c) (ps.map (Term.subst n (Term.shiftN n v))) := by
      rw [Term.subst_apps]
      rfl
    rw [e] at hg'
    refine ⟨Uses.join π'h π'm, ?_, ?_⟩
    · exact Uses.le_trans (Uses.le_join hleh hlem) (Uses.cut_join_le _ _ _ _)
    · simp only [Term.subst, Term.subst_apps]
      refine Check.mat hk hc hr (by simp [hlen]) hlive hins' hg' ihh' ?_
      have hm2 := ihm'
      simp only [Term.subst, Term.subst_apps] at hm2
      exact hm2
  | @efq a A r q'' q3 Γ' ps B' hk hall hlive =>
    intro n v T πv qv Γres Γtl hq hfit hcut hv
    refine ⟨Uses.zero, by rw [Uses.cut_zero_val]; exact Uses.le_refl _, ?_⟩
    have e : Term.subst n (Term.shiftN n v)
        (.All q3 (Term.apps (.Adt a r) ps) B')
        = .All q3 (Term.apps (.Adt a r)
            (ps.map (Term.subst n (Term.shiftN n v))))
            (Term.subst (n + 1) (Term.shift 0 (Term.shiftN n v)) B') := by
      simp only [Term.subst, Term.subst_apps]
    rw [e]
    exact .efq hk hall hlive
  | cnv ht hc iht =>
    intro n v T πv qv Γres Γtl hq hfit hcut hv
    obtain ⟨π', hle, iht'⟩ := iht hq hfit hcut hv
    exact ⟨π', hle, .cnv iht' (Conv.subst hβ hc (Conv.refl _) n)⟩


-- ============================================================================
-- METATHEORY §E — the telescope walk: substitution transports the shaped
-- constructor and signature telescopes, retip re-tips them, and a spine
-- of checked applications walks them down to the family instance.
-- ============================================================================

theorem FTele.substW : ∀ {k : Nat} {ps : List Term} {B : Term},
    FTele a r ps k B → ∀ (d : Nat) (w : Term),
    FTele a r (ps.map (Term.subst d w)) k (Term.subst d w B) := by
  intro k
  induction k with
  | zero =>
    intro ps B h d w
    simp only [FTele] at h ⊢
    subst h
    rw [Term.subst_apps]
    rfl
  | succ k ih =>
    intro ps B h d w
    obtain ⟨qf, F, B0, hB, hrest⟩ := h
    subst hB
    refine ⟨qf, Term.subst d w F, Term.subst (d + 1) (Term.shift 0 w) B0,
      rfl, ?_⟩
    have h2 := ih hrest (d + 1) (Term.shift 0 w)
    have e : (ps.map (Term.shift 0)).map (Term.subst (d + 1) (Term.shift 0 w))
        = (ps.map (Term.subst d w)).map (Term.shift 0) := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro p _
      show Term.subst (d + 1) (Term.shift 0 w) (Term.shift 0 p)
        = Term.shift 0 (Term.subst d w p)
      rw [← Term.shift_subst_lt p 0 d w (Nat.zero_le d)]
    rwa [e] at h2

theorem WTele.substW : ∀ {pn : Nat} {ps : List Term} {B : Term},
    WTele a r ps pn fn B → ∀ (d : Nat) (w : Term),
    WTele a r (ps.map (Term.subst d w)) pn fn (Term.subst d w B) := by
  intro pn
  induction pn with
  | zero =>
    intro ps B h d w
    exact FTele.substW h d w
  | succ pn ih =>
    intro ps B h d w
    obtain ⟨K, B0, hB, hrest⟩ := h
    subst hB
    refine ⟨Term.subst d w K, Term.subst (d + 1) (Term.shift 0 w) B0, rfl, ?_⟩
    have h2 := ih hrest (d + 1) (Term.shift 0 w)
    have e1 : (ps.map (Term.shift 0)).map (Term.subst (d + 1) (Term.shift 0 w))
        = (ps.map (Term.subst d w)).map (Term.shift 0) := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro p _
      show Term.subst (d + 1) (Term.shift 0 w) (Term.shift 0 p)
        = Term.shift 0 (Term.subst d w p)
      rw [← Term.shift_subst_lt p 0 d w (Nat.zero_le d)]
    have e2 : [Term.Var 0].map (Term.subst (d + 1) (Term.shift 0 w))
        = [Term.Var 0] := by
      simp [Term.subst]
    rw [List.map_append, e1, e2] at h2
    exact h2

-- one parameter step: binding the next erased parameter to x
theorem WTele.param (h : WTele a r ps (pn + 1) fn T) :
    ∃ K B, T = .All .None K B ∧
      WTele a r (ps ++ [x]) pn fn (Term.subst 0 x B) := by
  obtain ⟨K, B, hT, hrest⟩ := h
  refine ⟨K, B, hT, ?_⟩
  have h2 := WTele.substW hrest 0 x
  have e1 : (ps.map (Term.shift 0)).map (Term.subst 0 x) = ps := by
    simp only [List.map_map]
    have hp : ∀ p ∈ ps, (Term.subst 0 x ∘ Term.shift 0) p = id p := by
      intro p _
      show Term.subst 0 x (Term.shift 0 p) = p
      exact Term.subst_shift p 0 x
    rw [List.map_congr_left hp, List.map_id]
  have e2 : [Term.Var 0].map (Term.subst 0 x) = [x] := by
    simp [Term.subst]
  rw [List.map_append, e1, e2] at h2
  exact h2

-- one field step: binding the next field to x
theorem FTele.field (h : FTele a r ps (k + 1) T) :
    ∃ qf F B, T = .All qf F B ∧ FTele a r ps k (Term.subst 0 x B) := by
  obtain ⟨qf, F, B, hT, hrest⟩ := h
  refine ⟨qf, F, B, hT, ?_⟩
  have h2 := FTele.substW hrest 0 x
  have e : (ps.map (Term.shift 0)).map (Term.subst 0 x) = ps := by
    simp only [List.map_map]
    have : ∀ p ∈ ps, (Term.subst 0 x ∘ Term.shift 0) p = id p := by
      intro p _
      show Term.subst 0 x (Term.shift 0 p) = p
      exact Term.subst_shift p 0 x
    rw [List.map_congr_left this, List.map_id]
  rwa [e] at h2

-- retip re-tips a walked telescope
theorem FTele.retip (r' : List Nat) : ∀ {k : Nat} {ps : List Term} {T : Term},
    FTele a r ps k T → FTele a r' ps k (Term.retip r' k T) := by
  intro k
  induction k with
  | zero =>
    intro ps T h
    simp only [FTele] at h ⊢
    subst h
    simp only [Term.retip]
    rw [Term.spine_apps (by trivial)]
  | succ k ih =>
    intro ps T h
    obtain ⟨qf, F, B, hT, hrest⟩ := h
    subst hT
    exact ⟨qf, F, Term.retip r' k B, rfl, ih hrest⟩

theorem WTele.retip (r' : List Nat) :
    ∀ {pn : Nat} {ps : List Term} {T : Term},
    WTele a r ps pn fn T →
    WTele a r' ps pn fn (Term.retip r' (pn + fn) T) := by
  intro pn
  induction pn with
  | zero =>
    intro ps T h
    rw [Nat.zero_add]
    exact FTele.retip r' h
  | succ pn ih =>
    intro ps T h
    obtain ⟨K, B, hT, hrest⟩ := h
    subst hT
    exact ⟨K, Term.retip r' (pn + fn) B, by rw [show pn + 1 + fn = (pn + fn) + 1 by omega]; rfl, ih hrest⟩


-- ============================================================================
-- METATHEORY §E2 — generation: every derivation of a given subject shape
-- factors through its rule, modulo conversion accumulated by cnv.
-- ============================================================================

theorem Check.typ_subj_inv (hβ : Book.Closed β) (h : Check β q Γ .Typ T π) :
    Conv β .Typ T ∧ π = Uses.zero := by
  generalize he : Term.Typ = t0 at h
  induction h <;> try exact Term.noConfusion he
  case typ => exact ⟨Conv.refl _, Eq.refl _⟩
  case cnv ht hc ih =>
    obtain ⟨hcv, hπ⟩ := ih he
    exact ⟨Conv.trans hβ hcv hc, hπ⟩

theorem Check.all_subj_inv (hβ : Book.Closed β)
    (h : Check β q Γ (.All q' A B) T π) :
    Conv β .Typ T ∧ π = Uses.zero := by
  generalize he : Term.All q' A B = t0 at h
  induction h <;> try exact Term.noConfusion he
  case all _ _ _ _ _ => exact ⟨Conv.refl _, Eq.refl _⟩
  case cnv ht hc ih =>
    obtain ⟨hcv, hπ⟩ := ih he
    exact ⟨Conv.trans hβ hcv hc, hπ⟩

theorem Check.eql_subj_inv (hβ : Book.Closed β)
    (h : Check β q Γ (.Eql x y T0) T π) :
    Conv β .Typ T ∧ π = Uses.zero := by
  generalize he : Term.Eql x y T0 = t0 at h
  induction h <;> try exact Term.noConfusion he
  case eql _ _ _ _ _ _ => exact ⟨Conv.refl _, Eq.refl _⟩
  case cnv ht hc ih =>
    obtain ⟨hcv, hπ⟩ := ih he
    exact ⟨Conv.trans hβ hcv hc, hπ⟩

theorem Check.lam_inv (hβ : Book.Closed β) (h : Check β q Γ (.Lam f) T π) :
    ∃ q' A B πf, Conv β (.All q' A B) T ∧ Check β q (A :: Γ) f B πf ∧
      Quant.le (πf 0) q' ∧ π = Uses.tail πf := by
  generalize he : Term.Lam f = t0 at h
  induction h <;> try exact Term.noConfusion he
  case lam hf hle _ =>
    cases he
    exact ⟨_, _, _, _, Conv.refl _, hf, hle, Eq.refl _⟩
  case cnv ht hc ih =>
    obtain ⟨q', A, B, πf, hcv, hf, hle, hπ⟩ := ih he
    exact ⟨q', A, B, πf, Conv.trans hβ hcv hc, hf, hle, hπ⟩

theorem Check.rfl_inv (hβ : Book.Closed β) (h : Check β q Γ .Rfl T π) :
    ∃ x y T0, Conv β x y ∧ Conv β (.Eql x y T0) T ∧ π = Uses.zero := by
  generalize he : Term.Rfl = t0 at h
  induction h <;> try exact Term.noConfusion he
  case rfl hc => exact ⟨_, _, _, hc, Conv.refl _, Eq.refl _⟩
  case cnv ht hc ih =>
    obtain ⟨x, y, T0, hxy, hcv, hπ⟩ := ih he
    exact ⟨x, y, T0, hxy, Conv.trans hβ hcv hc, hπ⟩

theorem Check.ref_inv (hβ : Book.Closed β) (h : Check β q Γ (.Ref k) T π) :
    (∃ d, Book.defn β k = some d ∧ (q ≠ .None → d.body ≠ none)
       ∧ Conv β d.ty T ∧ π = Uses.zero)
    ∨ (∃ A, Book.adt β k = some A ∧ A.pn = 0
       ∧ Conv β .Typ T ∧ π = Uses.zero) := by
  generalize he : Term.Ref k = t0 at h
  induction h <;> try exact Term.noConfusion he
  case ref hk hlv =>
    cases he
    exact Or.inl ⟨_, hk, hlv, Conv.refl _, Eq.refl _⟩
  case refA hk h0 =>
    cases he
    exact Or.inr ⟨_, hk, h0, Conv.refl _, Eq.refl _⟩
  case cnv ht hc ih =>
    rcases ih he with ⟨d, hk, hlv, hcv, hπ⟩ | ⟨A, hk, h0, hcv, hπ⟩
    · exact Or.inl ⟨d, hk, hlv, Conv.trans hβ hcv hc, hπ⟩
    · exact Or.inr ⟨A, hk, h0, Conv.trans hβ hcv hc, hπ⟩

theorem Check.adt_head_inv (hβ : Book.Closed β)
    (h : Check β q Γ (.Adt a r) T π) :
    ∃ A, Book.adt β a = some A ∧ Conv β A.sig T ∧ π = Uses.zero := by
  generalize he : Term.Adt a r = t0 at h
  induction h <;> try exact Term.noConfusion he
  case adt hk =>
    cases he
    exact ⟨_, hk, Conv.refl _, Eq.refl _⟩
  case cnv ht hc ih =>
    obtain ⟨A, hk, hcv, hπ⟩ := ih he
    exact ⟨A, hk, Conv.trans hβ hcv hc, hπ⟩

theorem Check.ctr_head_inv (hβ : Book.Closed β)
    (h : Check β q Γ (.Ctr a c) T π) :
    ∃ A C r0, Book.adt β a = some A ∧ AdtD.ctr A c = some C ∧ c ∉ r0 ∧
      Conv β (Term.retip r0 (A.pn + C.fn) C.ty) T ∧ π = Uses.zero := by
  generalize he : Term.Ctr a c = t0 at h
  induction h <;> try exact Term.noConfusion he
  case ctr hk hc0 hr =>
    cases he
    exact ⟨_, _, _, hk, hc0, hr, Conv.refl _, Eq.refl _⟩
  case cnv ht hc ih =>
    obtain ⟨A, C, r0, hk, hc0, hr, hcv, hπ⟩ := ih he
    exact ⟨A, C, r0, hk, hc0, hr, Conv.trans hβ hcv hc, hπ⟩

theorem Check.app_inv (hβ : Book.Closed β)
    (h : Check β q Γ (.App f x) T π) :
    ∃ q' A B πf πx, q' ≠ .Many ∧ Check β q Γ f (.All q' A B) πf ∧
      Check β (Quant.dem q' q) Γ x A πx ∧
      Conv β (Term.subst 0 x B) T ∧ π = Uses.add πf πx := by
  generalize he : Term.App f x = t0 at h
  induction h <;> try exact Term.noConfusion he
  case app hq3 hf hx _ _ =>
    cases he
    exact ⟨_, _, _, _, _, hq3, hf, hx, Conv.refl _, Eq.refl _⟩
  case cnv ht hc ih =>
    obtain ⟨q', A, B, πf, πx, hq3, hf, hx, hcv, hπ⟩ := ih he
    exact ⟨q', A, B, πf, πx, hq3, hf, hx, Conv.trans hβ hcv hc, hπ⟩

theorem Check.let_inv (hβ : Book.Closed β)
    (h : Check β q Γ (.Let qb v b) T π) :
    ∃ A T0 πv πb, qb ≠ .Many ∧ Check β (Quant.dem qb q) Γ v A πv ∧
      Check β q (A :: Γ) b (Term.shift 0 T0) πb ∧ Quant.le (πb 0) qb ∧
      Conv β T0 T ∧ π = Uses.add πv (Uses.tail πb) := by
  generalize he : Term.Let qb v b = t0 at h
  induction h <;> try exact Term.noConfusion he
  case let_ hqb hv hb hle _ _ =>
    cases he
    exact ⟨_, _, _, _, hqb, hv, hb, hle, Conv.refl _, Eq.refl _⟩
  case cnv ht hc ih =>
    obtain ⟨A, T0, πv, πb, hqb, hv, hb, hle, hcv, hπ⟩ := ih he
    exact ⟨A, T0, πv, πb, hqb, hv, hb, hle, Conv.trans hβ hcv hc, hπ⟩

theorem Check.rwt_inv (hβ : Book.Closed β)
    (h : Check β q Γ (.Rwt e P f) T π) :
    ∃ x y T0 πe πP πf, Check β q Γ e (.Eql x y T0) πe ∧
      Check β .None Γ P (Term.jmotive x T0) πP ∧
      Check β q Γ f (.App (.App P x) .Rfl) πf ∧
      Conv β (.App (.App P y) e) T ∧ π = Uses.add πe πf := by
  generalize he : Term.Rwt e P f = t0 at h
  induction h <;> try exact Term.noConfusion he
  case rwt he0 hP hf _ _ _ =>
    cases he
    exact ⟨_, _, _, _, _, _, he0, hP, hf, Conv.refl _, Eq.refl _⟩
  case cnv ht hc ih =>
    obtain ⟨x, y, T0, πe, πP, πf, he0, hP, hf, hcv, hπ⟩ := ih he
    exact ⟨x, y, T0, πe, πP, πf, he0, hP, hf, Conv.trans hβ hcv hc, hπ⟩

theorem Check.mat_ty_inv (hβ : Book.Closed β)
    (h : Check β q Γ (.Mat a c hh mm) T π) :
    ∃ A C r ps telF B G q' πh πm,
      Book.adt β a = some A ∧ AdtD.ctr A c = some C ∧ c ∉ r ∧
      ps.length = A.pn ∧ (q ≠ .None → q' ≠ .None) ∧
      Insts C.ty ps telF ∧
      MatGoal q' C.fn B (Term.apps (.Ctr a c) ps) telF G ∧
      Check β q Γ hh G πh ∧
      Check β q Γ mm (.All q' (Term.apps (.Adt a (c :: r)) ps) B) πm ∧
      Conv β (.All q' (Term.apps (.Adt a r) ps) B) T ∧
      π = Uses.join πh πm := by
  generalize he : Term.Mat a c hh mm = t0 at h
  induction h <;> try exact Term.noConfusion he
  case mat hk hc0 hr hlen hlive hins hgoal hharm hmarm _ _ =>
    cases he
    exact ⟨_, _, _, _, _, _, _, _, _, _, hk, hc0, hr, hlen, hlive, hins,
      hgoal, hharm, hmarm, Conv.refl _, Eq.refl _⟩
  case cnv ht hc ih =>
    obtain ⟨A, C, r, ps, telF, B, G, q', πh, πm, hk, hc0, hr, hlen, hlive,
      hins, hgoal, hharm, hmarm, hcv, hπ⟩ := ih he
    exact ⟨A, C, r, ps, telF, B, G, q', πh, πm, hk, hc0, hr, hlen, hlive,
      hins, hgoal, hharm, hmarm, Conv.trans hβ hcv hc, hπ⟩

theorem Check.efq_ty_inv (hβ : Book.Closed β) (h : Check β q Γ .Efq T π) :
    ∃ a A r q' ps B, Book.adt β a = some A ∧
      (∀ c, c < A.ctrs.length → c ∈ r) ∧ (q ≠ .None → q' ≠ .None) ∧
      Conv β (.All q' (Term.apps (.Adt a r) ps) B) T ∧ π = Uses.zero := by
  generalize he : Term.Efq = t0 at h
  induction h <;> try exact Term.noConfusion he
  case efq hk hall hlive =>
    exact ⟨_, _, _, _, _, _, hk, hall, hlive, Conv.refl _, Eq.refl _⟩
  case cnv ht hc ih =>
    obtain ⟨a, A, r, q', ps, B, hk, hall, hlive, hcv, hπ⟩ := ih he
    exact ⟨a, A, r, q', ps, B, hk, hall, hlive, Conv.trans hβ hcv hc, hπ⟩

-- ============================================================================
-- METATHEORY §E3 — spine typing: a checked application spine walks the
-- head's telescope, one Conv-linked All at a time.
-- ============================================================================

inductive ChkSpine (β : Book) (q : Quant) (Γ : Ctx) :
    Term → List Term → Term → Uses → Prop
  | nil  : ChkSpine β q Γ T [] T Uses.zero
  | cons : Conv β T0 (.All q' A B) → q' ≠ .Many →
           Check β (Quant.dem q' q) Γ x A πx →
           ChkSpine β q Γ (Term.subst 0 x B) as T' πs →
           ChkSpine β q Γ T0 (x :: as) T' (Uses.add πx πs)

theorem ChkSpine.snoc (hs : ChkSpine β q Γ T0 as T' πs)
    (hc : Conv β T' (.All q' A B)) (hq : q' ≠ .Many)
    (hx : Check β (Quant.dem q' q) Γ x A πx) :
    ChkSpine β q Γ T0 (as ++ [x]) (Term.subst 0 x B)
      (Uses.add πs πx) := by
  induction hs with
  | nil =>
    have := ChkSpine.cons hc hq hx (ChkSpine.nil)
    rw [show Uses.add Uses.zero πx = Uses.add πx Uses.zero from
      by rw [Uses.add_zero, Uses.zero_add]]
    exact this
  | @cons T1 q1 A1 B1 x1 πx1 as1 T1' πs1 hc1 hq1 hx1 hs1 ih =>
    have h2 := ih hc
    rw [show Uses.add (Uses.add πx1 πs1) πx
        = Uses.add πx1 (Uses.add πs1 πx) from Uses.add_assoc _ _ _]
    exact ChkSpine.cons hc1 hq1 hx1 h2

-- transport of a spine walk along conversion of its start
theorem ChkSpine.conv_start (hβ : Book.Closed β)
    (hs : ChkSpine β q Γ T0 as T' πs) (hc : Conv β T1 T0) :
    ∃ T'', ChkSpine β q Γ T1 as T'' πs ∧ Conv β T'' T' := by
  cases hs with
  | nil => exact ⟨T1, .nil, hc⟩
  | cons hc0 hq hx hrest =>
    exact ⟨_, .cons (Conv.trans hβ hc hc0) hq hx hrest, Conv.refl _⟩

-- inversion of a whole application spine
theorem Check.apps_inv (hβ : Book.Closed β) :
    ∀ {as : List Term} {f t T : Term} {π : Uses},
    t = Term.apps f as → Check β q Γ t T π →
    ∃ Tf T' πf πs, Check β q Γ f Tf πf ∧ ChkSpine β q Γ Tf as T' πs ∧
      Conv β T' T ∧ π = Uses.add πf πs := by
  intro as
  induction as with
  | nil =>
    intro f t T π he h
    subst he
    exact ⟨T, T, π, Uses.zero, h, .nil, Conv.refl _, (Uses.add_zero π).symm⟩
  | cons x rest ih =>
    intro f t T π he h
    obtain ⟨Tf, T', πf, πs, hfx, hsp, hcv, hπ⟩ := ih (f := .App f x) he h
    obtain ⟨q', A, B, πf0, πx, hq', hf, hx, hcv2, hπ2⟩ := Check.app_inv hβ hfx
    obtain ⟨T'', hsp', hcv3⟩ := hsp.conv_start hβ hcv2
    subst hπ2 hπ
    refine ⟨.All q' A B, T'', πf0, Uses.add πx πs, hf,
      .cons (Conv.refl _) hq' hx hsp', Conv.trans hβ hcv3 hcv, ?_⟩
    rw [Uses.add_assoc]


-- ============================================================================
-- METATHEORY §G — canonical forms and progress (claim 3). A spine walk
-- against a shaped telescope lands exactly on the family instance; a
-- closed value at a family type is a saturated constructor spine not in
-- the peeled set; a closed value at an equation is Rfl; and every
-- closed well-typed term is a value or weak-steps.
-- ============================================================================

theorem AdtD.ctr_lt {A : AdtD} (h : AdtD.ctr A c = some C) :
    c < A.ctrs.length := by
  unfold AdtD.ctr at h
  have aux : ∀ (cs : List CtrD) (c : Nat), AdtD.ctr.go cs c = some C →
      c < cs.length := by
    intro cs
    induction cs with
    | nil => intro c hc; cases hc
    | cons C0 cs ih =>
      intro c hc
      cases c with
      | zero => exact Nat.succ_pos _
      | succ c => exact Nat.succ_lt_succ (ih c hc)
  exact aux A.ctrs c h

theorem Book.Ok.adt_clauses (hok : Book.Ok β) (h : Book.adt β a = some A) :
    (∃ π, Check β .None [] A.sig .Typ π) ∧ A.Shape ∧
    ∀ c C, AdtD.ctr A c = some C →
      (∃ π, Check β .None [] C.ty .Typ π) ∧ CtrD.Shape a A.pn C := by
  unfold Book.adt at h
  split at h
  case _ heq =>
    cases h
    exact hok _ _ heq
  case _ => cases h

theorem Spinal.decompose (h : Spinal t) :
    (∃ a r as, t = Term.apps (.Adt a r) as) ∨
    (∃ a c as, t = Term.apps (.Ctr a c) as) := by
  induction h with
  | adt => exact .inl ⟨_, _, [], rfl⟩
  | ctr => exact .inr ⟨_, _, [], rfl⟩
  | @app f a hsp ih =>
    rcases ih with ⟨a0, r, as, he⟩ | ⟨a0, c, as, he⟩
    · exact .inl ⟨a0, r, as ++ [a], by rw [Term.apps_snoc, he]⟩
    · exact .inr ⟨a0, c, as ++ [a], by rw [Term.apps_snoc, he]⟩

-- the constructor-telescope walk: too few arguments leaves a function
-- type, exactly enough lands on the family instance, and too many is
-- impossible
theorem ChkSpine.wtele_walk (hβ : Book.Closed β)
    (hs : ChkSpine β q Γ T0 as T' πs) :
    ∀ {a : Nat} {r : List Nat} {pn fn : Nat} {ps : List Term} {Tw : Term},
    WTele a r ps pn fn Tw → Conv β Tw T0 →
    (as.length < pn + fn ∧ ∃ qA A B, Conv β (.All qA A B) T') ∨
    (as.length = pn + fn ∧
      Conv β (Term.apps (.Adt a r) (ps ++ as.take pn)) T') := by
  induction hs with
  | nil =>
    intro a r pn fn ps Tw hw hc
    cases pn with
    | zero =>
      cases fn with
      | zero =>
        right
        refine ⟨rfl, ?_⟩
        simp only [WTele, FTele] at hw
        subst hw
        simpa using hc
      | succ fk =>
        left
        refine ⟨by simp, ?_⟩
        simp only [WTele] at hw
        obtain ⟨qf, F, B, hTw, _⟩ := hw
        subst hTw
        exact ⟨_, _, _, hc⟩
    | succ pk =>
      left
      refine ⟨by simp; omega, ?_⟩
      obtain ⟨K, B, hTw, _⟩ := hw
      subst hTw
      exact ⟨_, _, _, hc⟩
  | @cons T1 q1 A1 B1 x1 πx1 as1 T1' πs1 hc0 hq1 hx1 hrest ih =>
    intro a r pn fn ps Tw hw hc
    cases pn with
    | succ pk =>
      obtain ⟨K, Bw, hTw, hw'⟩ := WTele.param (x := x1) hw
      subst hTw
      have hall := Conv.all_inj (Conv.trans hβ hc hc0)
      have hBw : Conv β (Term.subst 0 x1 Bw) (Term.subst 0 x1 B1) :=
        Conv.subst hβ hall.2.2 (Conv.refl x1) 0
      rcases ih hw' hBw with ⟨hlt, hex⟩ | ⟨hlen, hcv⟩
      · left
        exact ⟨by simp; omega, hex⟩
      · right
        refine ⟨by simp at hlen ⊢; omega, ?_⟩
        have e : ps ++ (x1 :: as1).take (pk + 1)
            = (ps ++ [x1]) ++ as1.take pk := by
          simp
        rwa [e]
    | zero =>
      cases fn with
      | zero =>
        exfalso
        simp only [WTele, FTele] at hw
        subst hw
        exact Conv.all_adt (Conv.symm (Conv.trans hβ hc hc0))
      | succ fk =>
        simp only [WTele] at hw
        obtain ⟨qf, F, Bw, hTw, hw'⟩ := FTele.field (x := x1) hw
        subst hTw
        have hall := Conv.all_inj (Conv.trans hβ hc hc0)
        have hBw : Conv β (Term.subst 0 x1 Bw) (Term.subst 0 x1 B1) :=
          Conv.subst hβ hall.2.2 (Conv.refl x1) 0
        rcases ih (show WTele a r ps 0 fk _ from hw') hBw with
          ⟨hlt, hex⟩ | ⟨hlen, hcv⟩
        · left
          exact ⟨by simp at hlt ⊢; omega, hex⟩
        · right
          refine ⟨by simp at hlen ⊢; omega, ?_⟩
          simpa using hcv

-- signature telescopes are stable under substitution
theorem STele.substW : ∀ {n : Nat} {T : Term}, STele n T →
    ∀ (d : Nat) (w : Term), STele n (Term.subst d w T) := by
  intro n
  induction n with
  | zero =>
    intro T h d w
    simp only [STele] at h ⊢
    subst h
    rfl
  | succ k ih =>
    intro T h d w
    obtain ⟨q0, K, B, hT, hr⟩ := h
    subst hT
    exact ⟨q0, _, _, rfl, ih hr (d + 1) (Term.shift 0 w)⟩

-- the signature walk: an Adt-headed spine has a function type or Type
theorem ChkSpine.stele_walk (hβ : Book.Closed β)
    (hs : ChkSpine β q Γ T0 as T' πs) :
    ∀ {n : Nat} {Tw : Term}, STele n Tw → Conv β Tw T0 →
    (as.length < n ∧ ∃ qA A B, Conv β (.All qA A B) T') ∨
    (as.length = n ∧ Conv β .Typ T') := by
  induction hs with
  | nil =>
    intro n Tw hw hc
    cases n with
    | zero =>
      right
      simp only [STele] at hw
      subst hw
      exact ⟨rfl, hc⟩
    | succ k =>
      left
      obtain ⟨q0, K, B, hTw, _⟩ := hw
      subst hTw
      exact ⟨by simp, ⟨_, _, _, hc⟩⟩
  | @cons T1 q1 A1 B1 x1 πx1 as1 T1' πs1 hc0 hq1 hx1 hrest ih =>
    intro n Tw hw hc
    cases n with
    | zero =>
      exfalso
      simp only [STele] at hw
      subst hw
      exact Conv.typ_all (Conv.trans hβ hc hc0)
    | succ k =>
      obtain ⟨q0, K, Bw, hTw, hw'⟩ := hw
      subst hTw
      have hall := Conv.all_inj (Conv.trans hβ hc hc0)
      have hBw : Conv β (Term.subst 0 x1 Bw) (Term.subst 0 x1 B1) :=
        Conv.subst hβ hall.2.2 (Conv.refl x1) 0
      rcases ih (STele.substW hw' 0 x1) hBw with ⟨hlt, hex⟩ | ⟨hlen, hcv⟩
      · left
        exact ⟨by simp; omega, hex⟩
      · right
        exact ⟨by simp; omega, hcv⟩


theorem Term.NAll.subst : ∀ {n : Nat} {T : Term}, T.NAll n →
    ∀ (d : Nat) (w : Term), (Term.subst d w T).NAll n := by
  intro n
  induction n with
  | zero => intro T _ d w; trivial
  | succ m ih =>
    intro T h d w
    obtain ⟨q, A, B, hqm, hT, hr⟩ := h
    subst hT
    exact ⟨q, _, _, hqm, _root_.rfl, ih hr (d + 1) (Term.shift 0 w)⟩

-- a reference kept below its arity checks at a function type: the
-- stuck spine can never inhabit a family or an equation
theorem Check.stuck_ref_all (hβ : Book.Closed β) {k : Nat} {d : DefD}
    (hk : Book.defn β k = some d) (hnall : d.ty.NAll d.n) :
    ∀ (n : Nat) (args : List Term) {q : Quant} {Γ : Ctx} {T : Term}
      {π : Uses},
    args.length ≤ n →
    args.length < d.n →
    Check β q Γ (Term.apps (.Ref k) args) T π →
    ∃ (U : Term), Term.NAll (d.n - args.length) U ∧ Conv β U T := by
  intro n
  induction n with
  | zero =>
    intro args q Γ T π hn hlt h
    have hargs : args = [] := by
      cases args with
      | nil => rfl
      | cons _ _ => simp at hn
    subst hargs
    rcases Check.ref_inv hβ h with ⟨d', hk', _, hcv, _⟩ | ⟨A', hk', _, _, _⟩
    rotate_left
    · exact (Book.defn_adt_clash hk hk').elim
    rw [hk] at hk'
    cases hk'
    exact ⟨d.ty, by simpa using hnall, hcv⟩
  | succ m ihn =>
    intro args q Γ T π hn hlt h
    rcases List.eq_nil_or_concat args with rfl | ⟨args0, a, rfl⟩
    · rcases Check.ref_inv hβ h with
        ⟨d', hk', _, hcv, _⟩ | ⟨A', hk', _, _, _⟩
      rotate_left
      · exact (Book.defn_adt_clash hk hk').elim
      rw [hk] at hk'
      cases hk'
      exact ⟨d.ty, by simpa using hnall, hcv⟩
    · rw [List.concat_eq_append, Term.apps_snoc] at h
      obtain ⟨q3, A, B, πf, πx, hq3, hf, hx, hcv, hπ⟩ :=
        Check.app_inv hβ h
      rw [List.concat_eq_append] at hn hlt ⊢
      simp only [List.length_append, List.length_cons,
        List.length_nil] at hn hlt
      obtain ⟨U, hnU, hcvU⟩ := ihn args0 (by omega) (by omega) hf
      have hge : 1 ≤ d.n - args0.length := by omega
      obtain ⟨q4, A4, B4, hUeq, hnB4⟩ : ∃ q4 A4 B4, U = Term.All q4 A4 B4
          ∧ Term.NAll (d.n - args0.length - 1) B4 := by
        rcases hnn : d.n - args0.length with _ | m2
        · omega
        · rw [hnn] at hnU
          obtain ⟨q4, A4, B4, hq4m, hUeq, hr⟩ := hnU
          refine ⟨q4, A4, B4, hUeq, ?_⟩
          simpa using hr
      subst hUeq
      obtain ⟨hq4, hcA, hcB⟩ := Conv.all_inj hcvU
      refine ⟨Term.subst 0 a B4, ?_, ?_⟩
      · simp only [List.length_append, List.length_cons, List.length_nil]
        rw [show d.n - (args0.length + 1) = d.n - args0.length - 1 from by
          omega]
        exact hnB4.subst 0 a
      · refine Conv.trans hβ ?_ hcv
        exact Conv.subst hβ hcB (Conv.refl a) 0

theorem Book.Ok.defn_clauses (hok : Book.Ok β) (h : Book.defn β k = some d) :
    (∃ π, Check β .None [] d.ty .Typ π) ∧
    d.ty.NAll d.n ∧
    (∀ b, d.body = some b →
      (∃ π, Check β .Lone [] b d.ty π) ∧
      Tree β k d.qs (.Ref k) d.n b) := by
  unfold Book.defn at h
  split at h
  case _ heq =>
    cases h
    exact hok _ _ heq
  case _ => cases h

-- liveness reaches the head of a checked spine: a live application of
-- an unfilled assert is already a type error
theorem Check.ref_head_body (hβ : Book.Closed β) :
    ∀ (n : Nat) (args : List Term) {k : Nat} {q : Quant} {Γ : Ctx}
      {T : Term} {π : Uses},
    args.length ≤ n →
    Check β q Γ (Term.apps (.Ref k) args) T π → q ≠ .None →
    ∀ {d : DefD}, Book.defn β k = some d → d.body ≠ none := by
  intro n
  induction n with
  | zero =>
    intro args k q Γ T π hn h hq d hk
    have hargs : args = [] := by
      cases args with
      | nil => rfl
      | cons _ _ => simp at hn
    subst hargs
    rcases Check.ref_inv hβ h with ⟨d', hk', hlv, _, _⟩ | ⟨A', hk', _, _, _⟩
    rotate_left
    · exact (Book.defn_adt_clash hk hk').elim
    rw [hk] at hk'
    cases hk'
    exact hlv hq
  | succ m ihn =>
    intro args k q Γ T π hn h hq d hk
    rcases List.eq_nil_or_concat args with rfl | ⟨args0, a, rfl⟩
    · rcases Check.ref_inv hβ h with
        ⟨d', hk', hlv, _, _⟩ | ⟨A', hk', _, _, _⟩
      rotate_left
      · exact (Book.defn_adt_clash hk hk').elim
      rw [hk] at hk'
      cases hk'
      exact hlv hq
    · rw [List.concat_eq_append, Term.apps_snoc] at h
      obtain ⟨q3, A, B, πf, πx, hq3, hf, hx, hcv, hπ⟩ :=
        Check.app_inv hβ h
      rw [List.concat_eq_append] at hn
      simp only [List.length_append, List.length_cons,
        List.length_nil] at hn
      exact ihn args0 (by omega) hf hq hk

-- ============================================================================
-- METATHEORY §F — subject reduction (claim 2): the kit. Demands
-- reassociate, a beta-cut is bounded by the affine budget, conversion is
-- congruent through applications, a spine walk rebuilds a checked
-- application, and closed judgments replay anywhere.
-- ============================================================================

theorem Quant.dem_assoc : ∀ qf q' q : Quant,
    Quant.dem (Quant.dem qf q') q = Quant.dem qf (Quant.dem q' q) := by
  intro qf q' q
  cases qf <;> cases q' <;> cases q <;> rfl

theorem Uses.cut0_le {πb πx : Uses} (h : Quant.le (πb 0) .Lone) :
    Uses.le (Uses.cut 0 πb πx) (Uses.add (Uses.tail πb) πx) := by
  intro i
  simp only [Uses.cut, Uses.tail, Uses.add]
  rw [if_neg (by omega : ¬ i < 0)]
  refine Quant.le_add (Quant.le_refl _) ?_
  have : Quant.le (Quant.mul (πb 0) (πx (i - 0))) (Quant.mul .Lone (πx (i - 0))) :=
    Quant.le_mul h (Quant.le_refl _)
  rw [Quant.lone_mul] at this
  rw [show i - 0 = i from rfl] at this
  exact this

theorem Conv.app_cong (_hβ : Book.Closed β) (hf : Conv β f f')
    (ha : Conv β a a') : Conv β (.App f a) (.App f' a') := by
  obtain ⟨cf, hf1, hf2⟩ := hf
  obtain ⟨ca, ha1, ha2⟩ := ha
  exact ⟨.App cf ca, (Red.app_f hf1).trans (Red.app_a ha1),
    (Red.app_f hf2).trans (Red.app_a ha2)⟩

theorem Conv.apps_cong (hβ : Book.Closed β) (hh : Conv β h h') :
    ∀ {as as' : List Term}, Convs β as as' →
    Conv β (Term.apps h as) (Term.apps h' as') := by
  intro as
  induction as generalizing h h' with
  | nil =>
    intro as' hc
    cases hc
    exact hh
  | cons x xs ih =>
    intro as' hc
    cases hc with
    | cons hx hxs => exact ih (Conv.app_cong hβ hh hx) hxs

-- rebuild a checked application from its spine walk
theorem ChkSpine.check (_hβ : Book.Closed β)
    (hs : ChkSpine β q Γ T0 as T' πs) :
    ∀ {f : Term} {πf : Uses}, Check β q Γ f T0 πf →
    Check β q Γ (Term.apps f as) T' (Uses.add πf πs) := by
  induction hs with
  | nil =>
    intro f πf hf
    exact hf.cast (Uses.add_zero πf).symm
  | @cons T1 q1 A1 B1 x1 πx1 as1 T1' πs1 hc0 hq1 hx1 hrest ih =>
    intro f πf hf
    have happ := Check.app hq1 (Check.cnv hf hc0) hx1
    have h2 := ih happ
    rw [show Uses.add (Uses.add πf πx1) πs1
        = Uses.add πf (Uses.add πx1 πs1) from Uses.add_assoc _ _ _] at h2
    exact h2

-- split a spine walk at a prefix
theorem ChkSpine.append_split (_hβ : Book.Closed β) :
    ∀ {ps : List Term} {T0 xs T' πs},
    ChkSpine β q Γ T0 (ps ++ xs) T' πs →
    ∃ Tm π1 π2, ChkSpine β q Γ T0 ps Tm π1 ∧ ChkSpine β q Γ Tm xs T' π2 ∧
      πs = Uses.add π1 π2 := by
  intro ps
  induction ps with
  | nil =>
    intro T0 xs T' πs h
    exact ⟨T0, Uses.zero, πs, .nil, h, (Uses.zero_add πs).symm⟩
  | cons p ps ih =>
    intro T0 xs T' πs h
    cases h with
    | cons hc0 hq1 hx1 hrest =>
      obtain ⟨Tm, π1, π2, h1, h2, hπ⟩ := ih hrest
      refine ⟨Tm, _, π2, .cons hc0 hq1 hx1 h1, h2, ?_⟩
      rw [hπ, Uses.add_assoc]

-- measures vanish beyond the context: a judgment in Γ charges no slot
-- at or past Γ.length
theorem Check.uses_bound (h : Check β q Γ t T π) :
    ∀ i, Γ.length ≤ i → π i = .None := by
  induction h with
  | @var Γ0 j T0 q0 hg =>
    intro i hi
    have hj := Ctx.get_lt hg
    simp only [Uses.one]
    rw [if_neg (by omega : ¬ i = j)]
  | ref _ => intro i _; rfl
  | refA _ _ => intro i _; rfl
  | adt _ => intro i _; rfl
  | ctr _ _ _ => intro i _; rfl
  | typ => intro i _; rfl
  | all _ _ _ _ _ => intro i _; rfl
  | lam _ _ ihf =>
    intro i hi
    exact ihf (i + 1) (by simp; omega)
  | app _ _ _ ihf ihx =>
    intro i hi
    show Quant.add _ _ = _
    rw [ihf i hi, ihx i hi]
    rfl
  | let_ _ _ _ _ ihv ihb =>
    intro i hi
    show Quant.add _ (Uses.tail _ i) = _
    rw [ihv i hi]
    show Quant.add .None _ = _
    have := ihb (i + 1) (by simp; omega)
    simp only [Uses.tail]
    rw [this]
    rfl
  | eql _ _ _ _ _ _ => intro i _; rfl
  | rfl _ => intro i _; rfl
  | rwt _ _ _ ihe _ ihf =>
    intro i hi
    show Quant.add _ _ = _
    rw [ihe i hi, ihf i hi]
    rfl
  | mat _ _ _ _ _ _ _ _ _ ihh ihm =>
    intro i hi
    show Quant.join _ _ = _
    rw [ihh i hi, ihm i hi]
    rfl
  | efq _ _ _ => intro i _; rfl
  | cnv _ _ ih => exact ih

theorem Check.empty_le_zero (h : Check β q [] t T π) :
    Uses.le π Uses.zero := by
  intro i
  rw [h.uses_bound i (by simp)]
  trivial

-- a closed empty-context judgment replays in any context, still
-- measuring nothing
theorem Check.weaken_closed (hβ : Book.Closed β) (h : Check β q [] t T π)
    (hct : t.Closed 0) (hcT : T.Closed 0) :
    ∀ Γ, ∃ π', Uses.le π' Uses.zero ∧ Check β q Γ t T π' := by
  intro Γ
  induction Γ with
  | nil => exact ⟨π, h.empty_le_zero, h⟩
  | cons A Γ ih =>
    obtain ⟨π', hle, h'⟩ := ih
    have hw := h'.weaken hβ (Ins.zero (U := A))
    rw [Term.shift_closed t 0 0 hct (Nat.le_refl 0),
      Term.shift_closed T 0 0 hcT (Nat.le_refl 0)] at hw
    refine ⟨_, ?_, hw⟩
    intro i
    simp only [Uses.lift]
    split
    · omega
    · split
      · trivial
      · exact hle _


-- ============================================================================
-- METATHEORY §F2 — retip transport: on a shaped telescope, retip
-- commutes with substitution and absorbs itself, and a checked spine
-- transports to any retipping of its telescope (what lets a mismatched
-- scrutinee re-check at the peeled domain of a match tail).
-- ============================================================================

theorem Term.retip_adt_apps (a : Nat) (r r' : List Nat) (ps : List Term) :
    Term.retip r' 0 (Term.apps (.Adt a r) ps) = Term.apps (.Adt a r') ps := by
  show (match (Term.spine (Term.apps (.Adt a r) ps)).1 with
        | .Adt a0 _ =>
          Term.apps (.Adt a0 r') (Term.spine (Term.apps (.Adt a r) ps)).2
        | _ => Term.apps (.Adt a r) ps) = _
  rw [Term.spine_apps (h := .Adt a r) trivial]

theorem FTele.retip_subst : ∀ {k : Nat} {ps : List Term} {B : Term},
    FTele a r ps k B → ∀ (r' : List Nat) (d : Nat) (w : Term),
    Term.subst d w (Term.retip r' k B) = Term.retip r' k (Term.subst d w B) := by
  intro k
  induction k with
  | zero =>
    intro ps B h r' d w
    simp only [FTele] at h
    subst h
    rw [Term.retip_adt_apps a r r' ps, Term.subst_apps, Term.subst_apps]
    rw [show Term.subst d w (.Adt a r') = (.Adt a r' : Term) from rfl,
      show Term.subst d w (.Adt a r) = (.Adt a r : Term) from rfl,
      Term.retip_adt_apps a r r' (ps.map (Term.subst d w))]
  | succ k ih =>
    intro ps B h r' d w
    obtain ⟨qf, F, B0, hB, hrest⟩ := h
    subst hB
    show Term.subst d w (.All qf F (Term.retip r' k B0))
        = .All qf (Term.subst d w F)
            (Term.retip r' k (Term.subst (d + 1) (Term.shift 0 w) B0))
    simp only [Term.subst]
    rw [ih hrest r' (d + 1) (Term.shift 0 w)]

theorem WTele.retip_subst : ∀ {pn : Nat} {ps : List Term} {B : Term},
    WTele a r ps pn fn B → ∀ (r' : List Nat) (d : Nat) (w : Term),
    Term.subst d w (Term.retip r' (pn + fn) B)
      = Term.retip r' (pn + fn) (Term.subst d w B) := by
  intro pn
  induction pn with
  | zero =>
    intro ps B h r' d w
    rw [Nat.zero_add]
    exact FTele.retip_subst h r' d w
  | succ pn ih =>
    intro ps B h r' d w
    obtain ⟨K, B0, hB, hrest⟩ := h
    subst hB
    rw [show pn + 1 + fn = (pn + fn) + 1 from by omega]
    show Term.subst d w (.All .None K (Term.retip r' (pn + fn) B0))
        = .All .None (Term.subst d w K)
            (Term.retip r' (pn + fn) (Term.subst (d + 1) (Term.shift 0 w) B0))
    simp only [Term.subst]
    rw [ih hrest r' (d + 1) (Term.shift 0 w)]

theorem FTele.retip_retip : ∀ {k : Nat} {ps : List Term} {B : Term},
    FTele a r ps k B → ∀ (r' r'' : List Nat),
    Term.retip r' k (Term.retip r'' k B) = Term.retip r' k B := by
  intro k
  induction k with
  | zero =>
    intro ps B h r' r''
    simp only [FTele] at h
    subst h
    rw [Term.retip_adt_apps a r r'' ps, Term.retip_adt_apps a r'' r' ps,
      Term.retip_adt_apps a r r' ps]
  | succ k ih =>
    intro ps B h r' r''
    obtain ⟨qf, F, B0, hB, hrest⟩ := h
    subst hB
    show Term.All qf F (Term.retip r' k (Term.retip r'' k B0))
        = .All qf F (Term.retip r' k B0)
    rw [ih hrest r' r'']

theorem WTele.retip_retip : ∀ {pn : Nat} {ps : List Term} {B : Term},
    WTele a r ps pn fn B → ∀ (r' r'' : List Nat),
    Term.retip r' (pn + fn) (Term.retip r'' (pn + fn) B)
      = Term.retip r' (pn + fn) B := by
  intro pn
  induction pn with
  | zero =>
    intro ps B h r' r''
    rw [Nat.zero_add]
    exact FTele.retip_retip h r' r''
  | succ pn ih =>
    intro ps B h r' r''
    obtain ⟨K, B0, hB, hrest⟩ := h
    subst hB
    rw [show pn + 1 + fn = (pn + fn) + 1 from by omega]
    show Term.All .None K
        (Term.retip r' (pn + fn) (Term.retip r'' (pn + fn) B0))
        = .All .None K (Term.retip r' (pn + fn) B0)
    rw [ih hrest r' r'']


-- a checked spine transports to any retipping of its (shaped) telescope
theorem ChkSpine.retipS (hβ : Book.Closed β)
    (hs : ChkSpine β q Γ T0 as T' πs) :
    ∀ {a : Nat} {r : List Nat} {pn fn : Nat} {ps : List Term} {Tw : Term},
    WTele a r ps pn fn Tw → Conv β Tw T0 →
    as.length = pn + fn → ∀ (r' : List Nat),
    ChkSpine β q Γ (Term.retip r' (pn + fn) Tw) as
      (Term.apps (.Adt a r') (ps ++ as.take pn)) πs := by
  induction hs with
  | nil =>
    intro a r pn fn ps Tw hw hc hlen r'
    have hpn : pn = 0 := by simp at hlen; omega
    have hfn : fn = 0 := by simp at hlen; omega
    subst hpn hfn
    simp only [WTele, FTele] at hw
    subst hw
    rw [show (0 : Nat) + 0 = 0 from rfl, Term.retip_adt_apps a r r' ps]
    rw [show ps ++ List.take 0 [] = ps from by simp]
    exact ChkSpine.nil
  | @cons T1 q1 A1 B1 x1 πx1 as1 T1' πs1 hc0 hq1 hx1 hrest ih =>
    intro a r pn fn ps Tw hw hc hlen r'
    cases pn with
    | succ pk =>
      obtain ⟨K, Bw, hTw, hwB⟩ := hw
      subst hTw
      obtain ⟨K', Bw', hTw2, hw'⟩ := WTele.param (x := x1)
        (show WTele a r ps (pk + 1) fn (.All .None K Bw) from ⟨K, Bw, rfl, hwB⟩)
      cases hTw2
      have hall := Conv.all_inj (Conv.trans hβ hc hc0)
      have hBw : Conv β (Term.subst 0 x1 Bw) (Term.subst 0 x1 B1) :=
        Conv.subst hβ hall.2.2 (Conv.refl x1) 0
      have hlen' : as1.length = pk + fn := by simp at hlen; omega
      have hstep := ih hw' hBw hlen' r'
      have hcomm : Term.subst 0 x1 (Term.retip r' (pk + fn) Bw)
          = Term.retip r' (pk + fn) (Term.subst 0 x1 Bw) :=
        WTele.retip_subst hwB r' 0 x1
      have harg : Check β (Quant.dem .None q) Γ x1 K πx1 := by
        rw [show Quant.dem .None q = Quant.dem q1 q from by rw [← hall.1]]
        exact Check.cnv hx1 (Conv.symm hall.2.1)
      rw [show pk + 1 + fn = (pk + fn) + 1 from by omega,
        show ps ++ (x1 :: as1).take (pk + 1) = (ps ++ [x1]) ++ as1.take pk
          from by simp]
      refine ChkSpine.cons (Conv.refl _) (by intro h; cases h) harg ?_
      show ChkSpine β q Γ (Term.subst 0 x1 (Term.retip r' (pk + fn) Bw))
        as1 _ πs1
      rw [hcomm]
      exact hstep
    | zero =>
      cases fn with
      | zero => simp at hlen
      | succ fk =>
        simp only [WTele] at hw
        obtain ⟨qf, F, Bw, hTw, hwB⟩ := hw
        subst hTw
        obtain ⟨qf', F', Bw', hTw2, hw'⟩ := FTele.field (x := x1)
          (show FTele a r ps (fk + 1) (.All qf F Bw) from ⟨qf, F, Bw, rfl, hwB⟩)
        cases hTw2
        have hall := Conv.all_inj (Conv.trans hβ hc hc0)
        have hBw : Conv β (Term.subst 0 x1 Bw) (Term.subst 0 x1 B1) :=
          Conv.subst hβ hall.2.2 (Conv.refl x1) 0
        have hlen' : as1.length = 0 + fk := by simp at hlen; omega
        have hstep := ih (show WTele a r ps 0 fk _ from hw') hBw hlen' r'
        rw [show (0 : Nat) + fk = fk from by omega,
          show ps ++ List.take 0 as1 = ps from by simp] at hstep
        have hcomm : Term.subst 0 x1 (Term.retip r' fk Bw)
            = Term.retip r' fk (Term.subst 0 x1 Bw) :=
          FTele.retip_subst hwB r' 0 x1
        have harg : Check β (Quant.dem qf q) Γ x1 F πx1 := by
          rw [show Quant.dem qf q = Quant.dem q1 q from by rw [hall.1]]
          exact Check.cnv hx1 (Conv.symm hall.2.1)
        have hqf : qf ≠ .Many := by
          rw [hall.1]
          exact hq1
        rw [show (0 : Nat) + (fk + 1) = fk + 1 from by omega,
          show ps ++ (x1 :: as1).take 0 = ps from by simp]
        refine ChkSpine.cons (Conv.refl _) hqf harg ?_
        show ChkSpine β q Γ (Term.subst 0 x1 (Term.retip r' fk Bw)) as1 _ πs1
        rw [hcomm]
        exact hstep


-- retip at the telescope's own peel is the identity
theorem FTele.retip_self : ∀ {k : Nat} {ps : List Term} {B : Term},
    FTele a r ps k B → Term.retip r k B = B := by
  intro k
  induction k with
  | zero =>
    intro ps B h
    simp only [FTele] at h
    subst h
    exact Term.retip_adt_apps a r r ps
  | succ k ih =>
    intro ps B h
    obtain ⟨qf, F, B0, hB, hrest⟩ := h
    subst hB
    show Term.All qf F (Term.retip r k B0) = _
    rw [ih hrest]

theorem WTele.retip_self : ∀ {pn : Nat} {ps : List Term} {B : Term},
    WTele a r ps pn fn B → Term.retip r (pn + fn) B = B := by
  intro pn
  induction pn with
  | zero =>
    intro ps B h
    rw [Nat.zero_add]
    exact FTele.retip_self h
  | succ pn ih =>
    intro ps B h
    obtain ⟨K, B0, hB, hrest⟩ := h
    subst hB
    rw [show pn + 1 + fn = (pn + fn) + 1 from by omega]
    show Term.All .None K (Term.retip r (pn + fn) B0) = _
    rw [ih hrest]

-- instantiating conversion-related telescopes at pointwise-convertible
-- arguments gives convertible results
theorem Insts.conv (hβ : Book.Closed β) :
    ∀ {ps : List Term} {T X : Term}, Insts T ps X →
    ∀ {T' Y : Term} {qs : List Term}, Insts T' qs Y →
    Conv β T T' → Convs β ps qs → Conv β X Y := by
  intro ps
  induction ps with
  | nil =>
    intro T X h T' Y qs h' hc hcs
    cases h
    cases hcs
    cases h'
    exact hc
  | cons p ps ih =>
    intro T X h T' Y qs h' hc hcs
    cases h with
    | cons hrest =>
      cases hcs with
      | cons hpq hrest2 =>
        cases h' with
        | cons hrest' =>
          have hall := Conv.all_inj hc
          exact ih hrest hrest' (Conv.subst hβ hall.2.2 hpq 0) hrest2

-- the parameter prefix of a spine walk is an instantiation of the
-- telescope, up to conversion, and leaves the field telescope shaped
theorem ChkSpine.insts_mid (hβ : Book.Closed β)
    (hs : ChkSpine β q Γ T0 ps Tm π1) :
    ∀ {a : Nat} {r : List Nat} {pn fn : Nat} {psw : List Term} {Tw : Term},
    WTele a r psw pn fn Tw → Conv β Tw T0 → ps.length = pn →
    ∃ Tinst, Insts Tw ps Tinst ∧ Conv β Tinst Tm ∧
      FTele a r (psw ++ ps) fn Tinst := by
  induction hs with
  | nil =>
    intro a r pn fn psw Tw hw hc hlen
    have hpn : pn = 0 := by simp at hlen; omega
    subst hpn
    refine ⟨Tw, .nil, hc, ?_⟩
    rw [show psw ++ ([] : List Term) = psw from by simp]
    exact hw
  | @cons T1 q1 A1 B1 x1 πx1 as1 T1' πs1 hc0 hq1 hx1 hrest ih =>
    intro a r pn fn psw Tw hw hc hlen
    cases pn with
    | zero => simp at hlen
    | succ pk =>
      obtain ⟨K, Bw, hTw, hwB⟩ := hw
      subst hTw
      obtain ⟨K', Bw', hTw2, hw'⟩ := WTele.param (x := x1)
        (show WTele a r psw (pk + 1) fn (.All .None K Bw)
          from ⟨K, Bw, rfl, hwB⟩)
      cases hTw2
      have hall := Conv.all_inj (Conv.trans hβ hc hc0)
      have hBw : Conv β (Term.subst 0 x1 Bw) (Term.subst 0 x1 B1) :=
        Conv.subst hβ hall.2.2 (Conv.refl x1) 0
      obtain ⟨Tinst, hi, hcv, hsh⟩ := ih hw' hBw (by simp at hlen; omega)
      refine ⟨Tinst, Insts.cons hi, hcv, ?_⟩
      rw [show psw ++ x1 :: as1 = (psw ++ [x1]) ++ as1 from by simp]
      exact hsh

-- the fired arm walks its goal against the scrutinee's field checks:
-- the field telescopes convert pointwise, the demands reassociate, and
-- the tip lands on the motive at the rebuilt constructor
theorem MatGoal.rebuild (hβ : Book.Closed β) :
    ∀ (fn : Nat) {B s telG G : Term} {q' : Quant},
    MatGoal q' fn B s telG G → q' ≠ .Many →
    ∀ {TS : Term} {xs : List Term} {T' : Term} {πs : Uses},
    ChkSpine β (Quant.dem q' q) Γ TS xs T' πs →
    Conv β telG TS →
    xs.length = fn →
    ChkSpine β q Γ G xs (Term.subst 0 (Term.apps s xs) B) πs := by
  intro fn
  induction fn with
  | zero =>
    intro B s telG G q' hg hq' TS xs T' πs hs hc hlen
    cases hg with
    | zero =>
      have hxs : xs = [] := by
        cases xs
        · rfl
        · simp at hlen
      subst hxs
      cases hs
      exact ChkSpine.nil
  | succ n ih =>
    intro B s telG G q' hg hq' TS xs T' πs hs hc hlen
    cases hg with
    | succ hgrest =>
      rename_i Bf G0 qf F
      cases xs with
      | nil => simp at hlen
      | cons x rest =>
        cases hs with
        | @cons _ q1 A1 B1 _ πx _ _ πs1 hc0 hq1 hx1 hrest =>
          have hall := Conv.all_inj (Conv.trans hβ hc hc0)
          have hsub := hgrest.subst 0 x
          rw [Term.subst_shift B 1 (Term.shift 0 x)] at hsub
          have es : Term.subst 0 x (.App (Term.shift 0 s) (.Var 0))
              = .App s x := by
            show Term.App _ _ = _
            rw [Term.subst_shift s 0 x]
            simp [Term.subst]
          rw [es] at hsub
          have harg : Check β (Quant.dem (Quant.dem qf q') q) Γ x F πx := by
            rw [Quant.dem_assoc, hall.1]
            exact Check.cnv hx1 (Conv.symm hall.2.1)
          have hrest' := ih hsub hq' hrest
            (Conv.subst hβ hall.2.2 (Conv.refl x) 0) (by simp at hlen; omega)
          have hdem : Quant.dem qf q' ≠ .Many := by
            cases qf
            · intro h; cases h
            · exact hq'
            · exact hq'
          exact ChkSpine.cons (Conv.refl _) hdem harg hrest'


-- ============================================================================
-- METATHEORY §F3 — subject reduction (claim 2). Weak steps preserve the
-- type, and the affine measure never grows: a beta-cut is bounded by the
-- binder's budget, a delta-unfold spends nothing, and a match arm spends
-- at most its branch of the join.
-- ============================================================================

theorem Uses.add_comm (a b : Uses) : Uses.add a b = Uses.add b a := by
  funext i
  exact Quant.add_comm _ _

theorem Quant.ne_many_le_lone : ∀ {a : Quant}, a ≠ .Many → Quant.le a .Lone := by
  intro a h
  cases a
  · trivial
  · trivial
  · exact absurd _root_.rfl h


theorem Check.eql_inv_full (hβ : Book.Closed β)
    (h : Check β q Γ (.Eql x y T0) T π) :
    ∃ πT πa πb, Check β .None Γ T0 .Typ πT ∧ Check β .None Γ x T0 πa ∧
      Check β .None Γ y T0 πb ∧ Conv β .Typ T ∧ π = Uses.zero := by
  generalize he : Term.Eql x y T0 = t0 at h
  induction h <;> try exact Term.noConfusion he
  case eql hT ha hb _ _ _ =>
    cases he
    exact ⟨_, _, _, hT, ha, hb, Conv.refl _, Eq.refl _⟩
  case cnv ht hc ih =>
    obtain ⟨πT, πa, πb, hT, ha, hb, hcv, hπ⟩ := ih he
    exact ⟨πT, πa, πb, hT, ha, hb, Conv.trans hβ hcv hc, hπ⟩

theorem take_append (xs ys : List Term) :
    (xs ++ ys).take xs.length = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem Convs.symm (h : Convs β as bs) : Convs β bs as := by
  induction h with
  | nil => exact .nil
  | cons hc _ ih => exact .cons (Conv.symm hc) ih

theorem Convs.append (h1 : Convs β as bs) (h2 : Convs β cs ds) :
    Convs β (as ++ cs) (bs ++ ds) := by
  induction h1 with
  | nil => exact h2
  | cons hc _ ih => exact .cons hc ih

-- replacing the head of a checked spine by a term that checks (with
-- smaller usage) at every type the head checks at — the transport that
-- carries a saturated dref redex's typing to its unfolding
theorem Check.head_replace (hβ : Book.Closed β) :
    ∀ (n : Nat) (args : List Term) {f g : Term} {q : Quant} {Γ : Ctx}
      {T : Term} {π : Uses},
    args.length ≤ n →
    Check β q Γ (Term.apps f args) T π →
    (∀ {T2 : Term} {π2 : Uses}, Check β q Γ f T2 π2 →
      ∃ π3, Uses.le π3 π2 ∧ Check β q Γ g T2 π3) →
    ∃ π', Uses.le π' π ∧ Check β q Γ (Term.apps g args) T π' := by
  intro n
  induction n with
  | zero =>
    intro args f g q Γ T π hn h hrep
    have hnil : args = [] := by
      cases args with
      | nil => rfl
      | cons a as => simp at hn
    subst hnil
    exact hrep h
  | succ n ih =>
    intro args f g q Γ T π hn h hrep
    rcases List.eq_nil_or_concat args with hnil | ⟨as, a, hsnoc⟩
    · subst hnil
      exact hrep h
    · subst hsnoc
      rw [List.concat_eq_append] at hn h ⊢
      rw [Term.apps_append] at h ⊢
      obtain ⟨q3, A, B, πf, πx, hq3, hf, hx, hcv, hπ⟩ := Check.app_inv hβ h
      obtain ⟨πf', hlef, hf'⟩ := ih as (by
        rw [List.length_append] at hn
        simp only [List.length_cons, List.length_nil] at hn
        omega) hf hrep
      refine ⟨Uses.add πf' πx, ?_, ?_⟩
      · subst hπ
        exact Uses.le_add hlef (Uses.le_refl _)
      · exact Check.cnv (Check.app hq3 hf' hx) hcv

theorem subject_reduction_holds : subject_reduction := by
  intro β q Γ t t' T π hok hq h hstep
  have hβ := hok.closed
  induction hstep generalizing q Γ T π with
  | @beta f a =>
    obtain ⟨q3, A, B, πf, πx, hq3, hf, hx, hcv, hπ⟩ := Check.app_inv hβ h
    obtain ⟨q4, A4, B4, πb, hcv4, hbody, hle4, hπ4⟩ := Check.lam_inv hβ hf
    obtain ⟨hq34, hcA, hcB⟩ := Conv.all_inj hcv4
    subst hq34
    have hfit : (Quant.dem q4 q) = .Lone ∨ πb 0 = .None := by
      cases hq4 : q4 with
      | None =>
        right
        rw [hq4] at hle4
        exact Quant.le_none hle4
      | Lone =>
        cases hq' : q with
        | None =>
          right
          subst hq'
          exact Quant.le_none (hbody.none_le_zero _root_.rfl 0)
        | Lone => exact .inl _root_.rfl
        | Many => exact absurd hq' hq
      | Many => exact absurd hq4 hq3
    obtain ⟨π', hle', hchk'⟩ := hbody.sub hβ hq hfit Cut.zero
      (Check.cnv hx (Conv.symm hcA))
    refine ⟨π', ?_, ?_⟩
    · subst hπ hπ4
      refine Uses.le_trans hle' ?_
      refine Uses.le_trans (Uses.cut0_le ?_) ?_
      · exact Quant.le_trans hle4 (Quant.ne_many_le_lone hq3)
      · exact Uses.le_refl _
    · refine Check.cnv hchk' (Conv.trans hβ ?_ hcv)
      exact Conv.subst hβ hcB (Conv.refl a) 0
  | @let_ qb v b =>
    obtain ⟨A, T0, πv, πb, hqb, hv, hb, hle, hcv, hπ⟩ := Check.let_inv hβ h
    have hfit : (Quant.dem qb q) = .Lone ∨ πb 0 = .None := by
      cases hqb' : qb with
      | None =>
        right
        rw [hqb'] at hle
        exact Quant.le_none hle
      | Lone =>
        cases hq' : q with
        | None =>
          right
          subst hq'
          exact Quant.le_none (hb.none_le_zero _root_.rfl 0)
        | Lone => exact .inl _root_.rfl
        | Many => exact absurd hq' hq
      | Many => exact absurd hqb' hqb
    obtain ⟨π', hle', hchk'⟩ := hb.sub hβ hq hfit Cut.zero hv
    rw [Term.subst_shift T0 0 (Term.shiftN 0 v)] at hchk'
    refine ⟨π', ?_, Check.cnv hchk' hcv⟩
    subst hπ
    refine Uses.le_trans hle' ?_
    refine Uses.le_trans (Uses.cut0_le
      (Quant.le_trans hle (Quant.ne_many_le_lone hqb))) ?_
    rw [Uses.add_comm]
    exact Uses.le_refl _
  | @dref k d b s2 hk hb hsp2 hlen =>
    have hs2 : s2 = Term.apps (.Ref k) (Term.spine s2).2 := by
      have h0 := Term.apps_spine s2
      rw [hsp2] at h0
      exact h0.symm
    rw [hs2] at h
    refine Check.head_replace hβ (Term.spine s2).2.length (Term.spine s2).2
      (Nat.le_refl _) h ?_
    intro T2 π2 h2
    rcases Check.ref_inv hβ h2 with
      ⟨d', hk', hlv', hcv, hπ⟩ | ⟨A', hk', _, _, _⟩
    rotate_left
    · exact (Book.defn_adt_clash hk hk').elim
    rw [hk] at hk'
    cases hk'
    obtain ⟨_, _, hcl⟩ := hok.defn_clauses hk
    obtain ⟨⟨π0, hbody⟩, _⟩ := hcl b hb
    have hct := (hβ.defn hk).2 b hb
    have hcT := (hβ.defn hk).1
    obtain ⟨π1, hle1, hchk1⟩ := (hbody.weaken_closed hβ hct hcT) Γ
    subst hπ
    cases hq' : q with
    | None =>
      exact ⟨Uses.zero, Uses.le_refl _, Check.cnv hchk1.erased hcv⟩
    | Lone =>
      exact ⟨π1, hle1, Check.cnv hchk1 hcv⟩
    | Many => exact absurd hq' hq
  | @eta F hp hocc =>
    exact absurd hp (by intro hc; cases hc)
  | @drefS k d b s2 hp hk hb hsp2 =>
    exact absurd hp (by intro hc; cases hc)
  | @aref k A hk h0 =>
    rcases Check.ref_inv hβ h with
      ⟨d', hk', _, _, _⟩ | ⟨A', hk', h0', hcv, hπ⟩
    · exact (Book.defn_adt_clash hk' hk).elim
    rw [hk] at hk'
    cases hk'
    subst hπ
    have hsig : STele A.pn A.sig := (hok.adt_clauses hk).2.1
    rw [h0] at hsig
    refine ⟨Uses.zero, Uses.le_refl _, ?_⟩
    refine Check.cnv (Check.adt hk) ?_
    rw [hsig]
    exact hcv
  | rwt =>
    obtain ⟨x, y, T0, πe, πP, πf, he0, hP, hf, hcv, hπ⟩ := Check.rwt_inv hβ h
    obtain ⟨x', y', T0', hxy', hcvE, hπe⟩ := Check.rfl_inv hβ he0
    obtain ⟨hcx, hcy, hcT⟩ := Conv.eql_inj hcvE
    have hxy : Conv β x y :=
      Conv.trans hβ (Conv.symm hcx) (Conv.trans hβ hxy' hcy)
    refine ⟨πf, ?_, ?_⟩
    · subst hπ
      exact Uses.le_add_right πe πf
    · refine Check.cnv hf (Conv.trans hβ ?_ hcv)
      exact Conv.app_cong hβ (Conv.app_cong hβ (Conv.refl _) hxy)
        (Conv.refl _)
  | @app_f f f' a hstep ih =>
    obtain ⟨q3, A, B, πf, πx, hq3, hf, hx, hcv, hπ⟩ := Check.app_inv hβ h
    obtain ⟨πf', hlef, hf'⟩ := ih _ _ _ _ hq hf
    refine ⟨Uses.add πf' πx, ?_, ?_⟩
    · subst hπ
      exact Uses.le_add hlef (Uses.le_refl _)
    · exact Check.cnv (Check.app hq3 hf' hx) hcv
  | @app_a a a' f hstep ih =>
    obtain ⟨q3, A, B, πf, πx, hq3, hf, hx, hcv, hπ⟩ := Check.app_inv hβ h
    obtain ⟨πx', hlex, hx'⟩ := ih _ _ _ _ (Quant.dem_ne_many hq) hx
    refine ⟨Uses.add πf πx', ?_, ?_⟩
    · subst hπ
      exact Uses.le_add (Uses.le_refl _) hlex
    · refine Check.cnv (Check.app hq3 hf hx') (Conv.trans hβ ?_ hcv)
      exact Conv.subst_w hβ B (Conv.symm (Conv.of_red (Red.one hstep.strong))) 0
  | @mat_h h0 h0' a c m hstep ih =>
    obtain ⟨A, C, r, ps, telF, B, G, q', πh, πm, hk, hc0, hr, hlen, hlive,
      hins, hgoal, hharm, hmarm, hcv, hπ⟩ := Check.mat_ty_inv hβ h
    obtain ⟨πh', hleh, hharm'⟩ := ih _ _ _ _ hq hharm
    refine ⟨Uses.join πh' πm, ?_, ?_⟩
    · subst hπ
      exact Uses.le_join hleh (Uses.le_refl _)
    · exact Check.cnv (Check.mat hk hc0 hr hlen hlive hins hgoal hharm' hmarm)
        hcv
  | @mat_m m m' a c h0 hstep ih =>
    obtain ⟨A, C, r, ps, telF, B, G, q', πh, πm, hk, hc0, hr, hlen, hlive,
      hins, hgoal, hharm, hmarm, hcv, hπ⟩ := Check.mat_ty_inv hβ h
    obtain ⟨πm', hlem, hmarm'⟩ := ih _ _ _ _ hq hmarm
    refine ⟨Uses.join πh πm', ?_, ?_⟩
    · subst hπ
      exact Uses.le_join (Uses.le_refl _) hlem
    · exact Check.cnv (Check.mat hk hc0 hr hlen hlive hins hgoal hharm hmarm')
        hcv
  | @eql_a x x' y T0 hstep ih =>
    obtain ⟨πT, πa, πb, hT, ha, hb, hcv, hπ⟩ := Check.eql_inv_full hβ h
    obtain ⟨πa', _, ha'⟩ := ih _ _ _ _ (by intro hc; cases hc) ha
    subst hπ
    exact ⟨Uses.zero, Uses.le_refl _, Check.cnv (Check.eql hT ha' hb) hcv⟩
  | @eql_b y y' x T0 hstep ih =>
    obtain ⟨πT, πa, πb, hT, ha, hb, hcv, hπ⟩ := Check.eql_inv_full hβ h
    obtain ⟨πb', _, hb'⟩ := ih _ _ _ _ (by intro hc; cases hc) hb
    subst hπ
    exact ⟨Uses.zero, Uses.le_refl _, Check.cnv (Check.eql hT ha hb') hcv⟩
  | @eql_t T0 T0' x y hstep ih =>
    obtain ⟨πT, πa, πb, hT, ha, hb, hcv, hπ⟩ := Check.eql_inv_full hβ h
    obtain ⟨πT', _, hT'⟩ := ih _ _ _ _ (by intro hc; cases hc) hT
    subst hπ
    have hcT : Conv β T0 T0' := Conv.of_red (Red.one hstep.strong)
    exact ⟨Uses.zero, Uses.le_refl _,
      Check.cnv (Check.eql hT' (Check.cnv ha hcT) (Check.cnv hb hcT)) hcv⟩
  | @rwt_e e e' P f hstep ih =>
    obtain ⟨x, y, T0, πe, πP, πf, he0, hP, hf, hcv, hπ⟩ := Check.rwt_inv hβ h
    obtain ⟨πe', hlee, he0'⟩ := ih _ _ _ _ hq he0
    refine ⟨Uses.add πe' πf, ?_, ?_⟩
    · subst hπ
      exact Uses.le_add hlee (Uses.le_refl _)
    · refine Check.cnv (Check.rwt he0' hP hf) (Conv.trans hβ ?_ hcv)
      exact Conv.app_cong hβ (Conv.refl _)
        (Conv.symm (Conv.of_red (Red.one hstep.strong)))
  | @rwt_p P P' e f hstep ih =>
    obtain ⟨x, y, T0, πe, πP, πf, he0, hP, hf, hcv, hπ⟩ := Check.rwt_inv hβ h
    obtain ⟨πP', _, hP'⟩ := ih _ _ _ _ (by intro hc; cases hc) hP
    have hcP : Conv β P P' := Conv.of_red (Red.one hstep.strong)
    refine ⟨Uses.add πe πf, ?_, ?_⟩
    · subst hπ
      exact Uses.le_refl _
    · refine Check.cnv (Check.rwt he0 hP'
        (Check.cnv hf (Conv.app_cong hβ
          (Conv.app_cong hβ hcP (Conv.refl x)) (Conv.refl _)))) ?_
      refine Conv.trans hβ ?_ hcv
      exact Conv.app_cong hβ
        (Conv.app_cong hβ (Conv.symm hcP) (Conv.refl y)) (Conv.refl e)
  | @rwt_f f f' e P hstep ih =>
    obtain ⟨x, y, T0, πe, πP, πf, he0, hP, hf, hcv, hπ⟩ := Check.rwt_inv hβ h
    obtain ⟨πf', hlef, hf'⟩ := ih _ _ _ _ hq hf
    refine ⟨Uses.add πe πf', ?_, ?_⟩
    · subst hπ
      exact Uses.le_add (Uses.le_refl _) hlef
    · exact Check.cnv (Check.rwt he0 hP hf') hcv
  | @let_v v v' qb b hstep ih =>
    obtain ⟨A, T0, πv, πb, hqb, hv, hb, hle, hcv, hπ⟩ := Check.let_inv hβ h
    obtain ⟨πv', hlev, hv'⟩ := ih _ _ _ _ (Quant.dem_ne_many hq) hv
    refine ⟨Uses.add πv' (Uses.tail πb), ?_, ?_⟩
    · subst hπ
      exact Uses.le_add hlev (Uses.le_refl _)
    · exact Check.cnv (Check.let_ hqb hv' hb hle) hcv
  | all_a hp _ _ => exact nomatch hp
  | all_b hp _ _ => exact nomatch hp
  | lam_f hp _ _ => exact nomatch hp
  | let_b hp _ _ => exact nomatch hp
  | @matm a' c' a c h0 m as hne =>
    obtain ⟨q3, A', B', πf, πx, hq3, hfMat, hxScrut, hcv, hπ⟩ :=
      Check.app_inv hβ h
    obtain ⟨A, C, r, ps0, telF, B0, G, q'0, πh, πm, hk, hc0, hr, hlen0,
      hlive, hins, hgoal, hharm, hmarm, hcvM, hπf⟩ := Check.mat_ty_inv hβ hfMat
    obtain ⟨hq30, hcA, hcB⟩ := Conv.all_inj hcvM
    subst hq30
    obtain ⟨Tf, T', πf0, πs, hhead, hspine, hcvT', hπx⟩ :=
      Check.apps_inv hβ (Eq.refl _) hxScrut
    obtain ⟨A1, C1, rr0, hA1, hC1, hrr0, hcty, hπf0⟩ :=
      Check.ctr_head_inv hβ hhead
    have hshape := ((hok.adt_clauses hA1).2.2 c' C1 hC1).2
    have hw := WTele.retip rr0 hshape
    rcases ChkSpine.wtele_walk hβ hspine hw hcty with
      ⟨_, qA, AA, BB, hcAll⟩ | ⟨hlenAs, hcadt⟩
    · exact absurd (Conv.trans hβ hcAll
        (Conv.trans hβ hcvT' (Conv.symm hcA))) Conv.all_adt
    · have hchainC : Conv β (Term.apps (.Adt a' rr0) ([] ++ as.take A1.pn))
          (Term.apps (.Adt a r) ps0) :=
        Conv.trans hβ hcadt (Conv.trans hβ hcvT' (Conv.symm hcA))
      obtain ⟨ha'a, hrr, hconvs⟩ := Conv.adt_inj hchainC
      subst ha'a
      subst hrr
      rw [hA1] at hk
      cases hk
      have hcc : c' ≠ c := by
        intro hcceq
        subst hcceq
        exact hne (Eq.refl _)
      have hchain2 := hspine.retipS hβ hw hcty hlenAs (c :: rr0)
      rw [WTele.retip_retip hshape (c :: rr0) rr0] at hchain2
      have hheadty : Check β (Quant.dem q'0 q) Γ (.Ctr a' c')
          (Term.retip (c :: rr0) (A.pn + C1.fn) C1.ty) Uses.zero := by
        refine Check.ctr hA1 hC1 ?_
        intro hmem
        rcases List.mem_cons.mp hmem with hc1 | hc1
        · exact hcc hc1
        · exact hrr0 hc1
      have hscrut2 := ChkSpine.check hβ hchain2 hheadty
      have hscrut3 : Check β (Quant.dem q'0 q) Γ
          (Term.apps (.Ctr a' c') as)
          (Term.apps (.Adt a' (c :: rr0)) ps0)
          (Uses.add Uses.zero πs) := by
        refine Check.cnv hscrut2 ?_
        refine Conv.apps_cong hβ (Conv.refl _) ?_
        simpa using hconvs
      have hred := Check.app hq3 hmarm hscrut3
      refine ⟨_, ?_, Check.cnv hred (Conv.trans hβ
        (Conv.subst hβ hcB (Conv.refl _) 0) hcv)⟩
      subst hπ hπf hπx hπf0
      refine Uses.le_add (Uses.le_join_right _ _) (Uses.le_refl _)
  | @matc a A0 c C0 h0 m ps xs hk hc0 hlenp hlenx =>
    obtain ⟨q3, A', B', πf, πx, hq3, hfMat, hxScrut, hcv, hπ⟩ :=
      Check.app_inv hβ h
    obtain ⟨A, C, r, ps0, telF, B0, G, q'0, πh, πm, hkM, hc0M, hr, hlen0,
      hlive, hins, hgoal, hharm, hmarm, hcvM, hπf⟩ := Check.mat_ty_inv hβ hfMat
    obtain ⟨hq30, hcA, hcB⟩ := Conv.all_inj hcvM
    subst hq30
    rw [hk] at hkM
    cases hkM
    rw [hc0] at hc0M
    cases hc0M
    obtain ⟨Tf, T', πf0, πs, hhead, hspine, hcvT', hπx⟩ :=
      Check.apps_inv hβ (Eq.refl _) hxScrut
    obtain ⟨A1, C1, rr0, hA1, hC1, hrr0, hcty, hπf0⟩ :=
      Check.ctr_head_inv hβ hhead
    rw [hk] at hA1
    cases hA1
    rw [hc0] at hC1
    cases hC1
    have hshape := ((hok.adt_clauses hk).2.2 c C0 hc0).2
    have hw := WTele.retip rr0 hshape
    rcases ChkSpine.wtele_walk hβ hspine hw hcty with
      ⟨_, qA, AA, BB, hcAll⟩ | ⟨hlenAs, hcadt⟩
    · exact absurd (Conv.trans hβ hcAll
        (Conv.trans hβ hcvT' (Conv.symm hcA))) Conv.all_adt
    · have hchainC : Conv β
          (Term.apps (.Adt a rr0) ([] ++ (ps ++ xs).take A0.pn))
          (Term.apps (.Adt a r) ps0) :=
        Conv.trans hβ hcadt (Conv.trans hβ hcvT' (Conv.symm hcA))
      obtain ⟨_, hrr, hconvs⟩ := Conv.adt_inj hchainC
      subst hrr
      have htake : (ps ++ xs).take A0.pn = ps := by
        rw [← hlenp]
        exact take_append ps xs
      rw [htake] at hconvs
      simp only [List.nil_append] at hconvs
      have hchain0 := hspine.retipS hβ hw hcty hlenAs []
      rw [WTele.retip_retip hshape [] rr0,
        WTele.retip_self hshape] at hchain0
      obtain ⟨Tmid0, π1', π2', hsp1, hsp2, hπsp⟩ :=
        ChkSpine.append_split hβ hchain0
      obtain ⟨Tinst, hinsts, hcvmid, hFsh⟩ :=
        ChkSpine.insts_mid hβ hsp1 hshape (Conv.refl _) hlenp
      have hcvTel : Conv β Tinst telF :=
        Insts.conv hβ hinsts hins (Conv.refl _) hconvs
      have hGchain := MatGoal.rebuild hβ C0.fn hgoal hq3 hsp2
        (Conv.trans hβ (Conv.symm hcvTel) hcvmid) hlenx
      have hred := ChkSpine.check hβ hGchain hharm
      refine ⟨_, ?_, Check.cnv hred (Conv.trans hβ ?_ hcv)⟩
      · subst hπ hπf hπx hπf0 hπsp
        refine Uses.le_add (Uses.le_join_left _ _) ?_
        exact fun i => Quant.le_add_right _ _
      · rw [← Term.apps_append]
        refine Conv.subst hβ hcB ?_ 0
        refine Conv.apps_cong hβ (Conv.refl _) ?_
        exact Convs.append (Convs.symm hconvs) (Convs.refl xs)


-- ============================================================================
-- METATHEORY §W2 — occurrences and weight: the syntactic half of the
-- normalization measure. Term.occ d u counts copies of Var d; match
-- arms count by MAX — only one arm ever runs, so an affine binder may
-- occur once per arm. Term.wgt prices references through pr and weighs
-- match nodes by their heavier arm; Term.wub bounds any erasure's
-- weight from the raw term. The engine lemma is wgt_subst: substitution
-- costs at most one copy of the substituend per counted occurrence.
-- ============================================================================

def Term.wgt (pr : Nat → Nat) : Term → Nat
  | .Var _         => 1
  | .Ref k         => pr k
  | .Typ           => 1
  | .All _ A B     => 1 + Term.wgt pr A + Term.wgt pr B
  | .Lam f         => 1 + Term.wgt pr f
  | .App f a       => 1 + Term.wgt pr f + Term.wgt pr a
  | .Adt _ _       => 1
  | .Ctr _ _       => 1
  | .Mat _ _ h m   => 1 + Nat.max (Term.wgt pr h) (Term.wgt pr m)
  | .Efq           => 1
  | .Eql a b T     => 1 + Term.wgt pr a + Term.wgt pr b + Term.wgt pr T
  | .Rfl           => 1
  | .Rwt e P f     => 1 + Term.wgt pr e + Term.wgt pr P + Term.wgt pr f
  | .Let _ v b     => 1 + Term.wgt pr v + Term.wgt pr b

theorem Term.wgt_pos (pr : Nat → Nat) (hpr : ∀ k, 1 ≤ pr k) :
    ∀ t : Term, 1 ≤ Term.wgt pr t := by
  intro t
  cases t <;> first
  | exact Nat.le_refl 1
  | exact hpr _
  | (simp only [Term.wgt]; omega)

def Term.wub (pr : Nat → Nat) : Term → Nat
  | .Var _         => 1
  | .Ref k         => pr k
  | .Typ           => 1
  | .All _ A B     => 1 + Term.wub pr A + Term.wub pr B
  | .Lam f         => 1 + Term.wub pr f
  | .App f a       => 1 + Term.wub pr f + Term.wub pr a
  | .Adt _ _       => 1
  | .Ctr _ _       => 1
  | .Mat _ _ h m   => 1 + Nat.max (Term.wub pr h) (Term.wub pr m)
  | .Efq           => 1
  | .Eql a b T     => 1 + Term.wub pr a + Term.wub pr b + Term.wub pr T
  | .Rfl           => 1
  | .Rwt e P f     => 1 + Term.wub pr e + Term.wub pr P + Term.wub pr f
  | .Let _ v b     => 1 + Term.wub pr v + Term.wub pr b

theorem Term.wgt_shift (pr : Nat → Nat) : ∀ (t : Term) (d : Nat),
    Term.wgt pr (Term.shift d t) = Term.wgt pr t := by
  intro t
  induction t <;> intro d
  case Var i =>
    simp only [Term.shift]
    split <;> rfl
  all_goals simp [Term.shift, Term.wgt, *]

theorem Term.wgt_subst (pr : Nat → Nat) :
    ∀ (t : Term) (d : Nat) (w : Term),
    Term.wgt pr (Term.subst d w t)
      ≤ Term.wgt pr t + Term.occ d t * Term.wgt pr w := by
  intro t
  induction t <;> intro d w <;> simp only [Term.subst, Term.occ, Term.wgt]
  case Var i =>
    by_cases h1 : i = d
    · rw [if_pos h1, if_pos h1]
      try simp only [Term.wgt]
      omega
    · rw [if_neg h1, if_neg h1]
      split <;> (try simp only [Term.wgt]) <;> omega
  case Ref k => omega
  case Typ => omega
  case All q A B ihA ihB =>
    have h1 := ihA d w
    have h2 := ihB (d + 1) (Term.shift 0 w)
    rw [Term.wgt_shift pr w 0] at h2
    have hd : (Term.occ d A + Term.occ (d + 1) B) * Term.wgt pr w
        = Term.occ d A * Term.wgt pr w
          + Term.occ (d + 1) B * Term.wgt pr w := Nat.add_mul _ _ _
    omega
  case Lam f ihf =>
    have h1 := ihf (d + 1) (Term.shift 0 w)
    rw [Term.wgt_shift pr w 0] at h1
    omega
  case App f a ihf iha =>
    have h1 := ihf d w
    have h2 := iha d w
    have hd : (Term.occ d f + Term.occ d a) * Term.wgt pr w
        = Term.occ d f * Term.wgt pr w + Term.occ d a * Term.wgt pr w :=
      Nat.add_mul _ _ _
    omega
  case Adt a r => omega
  case Ctr a c => omega
  case Mat a c h m ihh ihm =>
    have h1 := ihh d w
    have h2 := ihm d w
    have m1 : Term.occ d h * Term.wgt pr w
        ≤ Nat.max (Term.occ d h) (Term.occ d m) * Term.wgt pr w :=
      Nat.mul_le_mul_right _ (Nat.le_max_left _ _)
    have m2 : Term.occ d m * Term.wgt pr w
        ≤ Nat.max (Term.occ d h) (Term.occ d m) * Term.wgt pr w :=
      Nat.mul_le_mul_right _ (Nat.le_max_right _ _)
    have hmax : Nat.max (Term.wgt pr (Term.subst d w h))
        (Term.wgt pr (Term.subst d w m))
        ≤ Nat.max (Term.wgt pr h) (Term.wgt pr m)
          + Nat.max (Term.occ d h) (Term.occ d m) * Term.wgt pr w :=
      Nat.max_le.mpr
        ⟨Nat.le_trans h1 (Nat.add_le_add (Nat.le_max_left _ _) m1),
         Nat.le_trans h2 (Nat.add_le_add (Nat.le_max_right _ _) m2)⟩
    omega
  case Efq => omega
  case Eql a b T iha ihb ihT =>
    have h1 := iha d w
    have h2 := ihb d w
    have h3 := ihT d w
    have hd : (Term.occ d a + Term.occ d b + Term.occ d T) * Term.wgt pr w
        = Term.occ d a * Term.wgt pr w + Term.occ d b * Term.wgt pr w
          + Term.occ d T * Term.wgt pr w := by
      rw [Nat.add_mul, Nat.add_mul]
    omega
  case Rfl => omega
  case Rwt e P f ihe ihP ihf =>
    have h1 := ihe d w
    have h2 := ihP d w
    have h3 := ihf d w
    have hd : (Term.occ d e + Term.occ d P + Term.occ d f) * Term.wgt pr w
        = Term.occ d e * Term.wgt pr w + Term.occ d P * Term.wgt pr w
          + Term.occ d f * Term.wgt pr w := by
      rw [Nat.add_mul, Nat.add_mul]
    omega
  case Let q v b ihv ihb =>
    have h1 := ihv d w
    have h2 := ihb (d + 1) (Term.shift 0 w)
    rw [Term.wgt_shift pr w 0] at h2
    have hd : (Term.occ d v + Term.occ (d + 1) b) * Term.wgt pr w
        = Term.occ d v * Term.wgt pr w
          + Term.occ (d + 1) b * Term.wgt pr w := Nat.add_mul _ _ _
    omega

-- ============================================================================
-- METATHEORY §NE — the erasure: the runtime skeleton of a live typed
-- term. Era β Γ t T u pairs a live typing with an output u: what
-- remains of t once every position the head strategy never evaluates
-- is plugged by the token Typ — type formers, erased arguments, dead
-- let values, equation data, motives. The binder rules carry the
-- occurrence bounds the beta cases of the measure consume; the
-- Check → Era existence proves them from the usage vectors. References
-- are priced down the book: Book.price k exceeds any erasure of
-- definition k's body when the body's references stay below k (the
-- PLAIN fragment: no recursion).
-- ============================================================================

def Term.RefsBelow (n : Nat) : Term → Prop
  | .Var _         => True
  | .Ref k         => k < n
  | .Typ           => True
  | .All _ A B     => A.RefsBelow n ∧ B.RefsBelow n
  | .Lam f         => f.RefsBelow n
  | .App f a       => f.RefsBelow n ∧ a.RefsBelow n
  | .Adt _ _       => True
  | .Ctr _ _       => True
  | .Mat _ _ h m   => h.RefsBelow n ∧ m.RefsBelow n
  | .Efq           => True
  | .Eql a b T     => a.RefsBelow n ∧ b.RefsBelow n ∧ T.RefsBelow n
  | .Rfl           => True
  | .Rwt e P f     => e.RefsBelow n ∧ P.RefsBelow n ∧ f.RefsBelow n
  | .Let _ v b     => v.RefsBelow n ∧ b.RefsBelow n

-- the plain fragment: every definition's body references strictly
-- earlier definitions only — the book is recursion-free
def Book.Plain (β : Book) : Prop :=
  ∀ k d, Book.defn β k = some d → ∀ b, d.body = some b → b.RefsBelow k

def Book.price (β : Book) : Nat → Nat
  | k =>
    1 + (match Book.defn β k with
         | some d =>
           match d.body with
           | some b =>
             Term.wub (fun j => if _h : j < k then Book.price β j else 1) b
           | none => 1
         | none => 1)
  termination_by k => k
  decreasing_by exact _h

theorem Term.wub_ext : ∀ (t : Term) (p1 p2 : Nat → Nat) (n : Nat),
    t.RefsBelow n → (∀ j, j < n → p1 j = p2 j) →
    Term.wub p1 t = Term.wub p2 t := by
  intro t
  induction t <;> intro p1 p2 n hrb hag <;>
    simp only [Term.wub, Term.RefsBelow] at *
  case Ref k => exact hag k hrb
  case All ihA ihB => rw [ihA p1 p2 n hrb.1 hag, ihB p1 p2 n hrb.2 hag]
  case Lam ihf => rw [ihf p1 p2 n hrb hag]
  case App ihf iha => rw [ihf p1 p2 n hrb.1 hag, iha p1 p2 n hrb.2 hag]
  case Mat ihh ihm => rw [ihh p1 p2 n hrb.1 hag, ihm p1 p2 n hrb.2 hag]
  case Eql iha ihb ihT =>
    rw [iha p1 p2 n hrb.1 hag, ihb p1 p2 n hrb.2.1 hag,
      ihT p1 p2 n hrb.2.2 hag]
  case Rwt ihe ihP ihf =>
    rw [ihe p1 p2 n hrb.1 hag, ihP p1 p2 n hrb.2.1 hag,
      ihf p1 p2 n hrb.2.2 hag]
  case Let ihv ihb => rw [ihv p1 p2 n hrb.1 hag, ihb p1 p2 n hrb.2 hag]

theorem Term.wub_pos (pr : Nat → Nat) (hpr : ∀ k, 1 ≤ pr k) :
    ∀ t : Term, 1 ≤ Term.wub pr t := by
  intro t
  cases t <;> first
  | exact Nat.le_refl 1
  | exact hpr _
  | (simp only [Term.wub]; omega)

theorem Book.price_pos (β : Book) : ∀ k, 1 ≤ Book.price β k := by
  intro k
  rw [Book.price]
  omega


theorem Book.price_gt (β : Book) {k : Nat} {d : DefD} {b : Term}
    (hk : Book.defn β k = some d) (hb : d.body = some b)
    (hrb : b.RefsBelow k) :
    Term.wub (Book.price β) b < Book.price β k := by
  have he : Book.price β k
      = 1 + Term.wub (fun j => if _h : j < k then Book.price β j else 1)
          b := by
    rw [Book.price]
    simp only [hk, hb]
  rw [he, Term.wub_ext b (Book.price β)
    (fun j => if _h : j < k then Book.price β j else 1) k hrb
    (fun j hj => by rw [dif_pos hj])]
  omega

def Quant.occN : Quant → Nat
  | .None => 0
  | _     => 1

-- Era β Γ t T u : the live term t has type T and erases to the
-- skeleton u. Dead positions are Check premises and erase to the
-- token Typ; the binder rules carry their occurrence bounds.
inductive Era (β : Book) : Ctx → Term → Term → Term → Prop
  | var : Ctx.get Γ i = some T →
          Era β Γ (.Var i) T (.Var i)
  | ref : Book.defn β k = some d → d.body ≠ none →
          Era β Γ (.Ref k) d.ty (.Ref k)
  | refA : Book.adt β k = some A → A.pn = 0 →
           Era β Γ (.Ref k) .Typ (.Adt k [])
  | adt : Book.adt β a = some A →
          Era β Γ (.Adt a r) A.sig (.Adt a r)
  | ctr : Book.adt β a = some A → AdtD.ctr A c = some C → c ∉ r →
          Era β Γ (.Ctr a c) (Term.retip r (A.pn + C.fn) C.ty) (.Ctr a c)
  | typ : Era β Γ .Typ .Typ .Typ
  | all : q' ≠ .Many →
          Check β .None Γ A .Typ πA →
          Check β .None (A :: Γ) B .Typ πB →
          Era β Γ (.All q' A B) .Typ .Typ
  | lam : Era β (A :: Γ) f B uf →
          (q' ≠ .Many → Term.occ 0 uf ≤ Quant.occN q') →
          Era β Γ (.Lam f) (.All q' A B) (.Lam uf)
  | app_live : Era β Γ f (.All .Lone A B) uf →
               Era β Γ x A ux →
               Era β Γ (.App f x) (Term.subst 0 x B) (.App uf ux)
  | app_dead : Era β Γ f (.All .None A B) uf →
               Check β .None Γ x A πx →
               Era β Γ (.App f x) (Term.subst 0 x B) (.App uf .Typ)
  | let_live : Era β Γ v A uv →
               Era β (A :: Γ) b (Term.shift 0 T) ub →
               Term.occ 0 ub ≤ 1 →
               Era β Γ (.Let .Lone v b) T (.Let .Lone uv ub)
  | let_dead : Check β .None Γ v A πv →
               Era β (A :: Γ) b (Term.shift 0 T) ub →
               Term.occ 0 ub = 0 →
               Era β Γ (.Let .None v b) T (.Let .None .Typ ub)
  | eql : Check β .None Γ T .Typ πT →
          Check β .None Γ a T πa →
          Check β .None Γ b T πb →
          Era β Γ (.Eql a b T) .Typ .Typ
  | rfl : Conv β a b →
          Era β Γ .Rfl (.Eql a b T) .Rfl
  | rwt : Era β Γ e (.Eql x y T0) ue →
          Check β .None Γ P (Term.jmotive x T0) πP →
          Era β Γ f (.App (.App P x) .Rfl) uf →
          Era β Γ (.Rwt e P f) (.App (.App P y) e) (.Rwt ue .Typ uf)
  | mat : Book.adt β a = some A → AdtD.ctr A c = some C →
          c ∉ r → ps.length = A.pn → q' ≠ .None →
          Insts C.ty ps telF →
          MatGoal q' C.fn B (Term.apps (.Ctr a c) ps) telF G →
          Era β Γ h G uh →
          Era β Γ m (.All q' (Term.apps (.Adt a (c :: r)) ps) B) um →
          Era β Γ (.Mat a c h m) (.All q' (Term.apps (.Adt a r) ps) B)
            (.Mat a c uh um)
  | efq : Book.adt β a = some A →
          (∀ c, c < A.ctrs.length → c ∈ r) → q' ≠ .None →
          Era β Γ .Efq (.All q' (Term.apps (.Adt a r) ps) B) .Efq
  | cnv : Era β Γ t A u → Conv β A B →
          Era β Γ t B u

theorem Quant.add_eq_lone : ∀ {a b : Quant}, Quant.add a b = .Lone →
    (a = .None ∧ b = .Lone) ∨ (a = .Lone ∧ b = .None) := by
  intro a b h
  cases a <;> cases b <;> first
  | exact .inl ⟨rfl, rfl⟩
  | exact .inr ⟨rfl, rfl⟩
  | exact absurd h (by intro hc; cases hc)

theorem Quant.join_eq_lone : ∀ {a b : Quant}, Quant.join a b = .Lone →
    (a = .None ∨ a = .Lone) ∧ (b = .None ∨ b = .Lone) := by
  intro a b h
  cases a <;> cases b <;> first
  | exact ⟨.inl rfl, .inl rfl⟩
  | exact ⟨.inl rfl, .inr rfl⟩
  | exact ⟨.inr rfl, .inl rfl⟩
  | exact ⟨.inr rfl, .inr rfl⟩
  | exact absurd h (by intro hc; cases hc)



-- the erasure exists for every live judgment, with the usage vector
-- bounding the occurrences: a None-measured slot does not occur, a
-- Lone-measured slot occurs at most once
theorem Check.era (h : Check β q Γ t T π) : q = .Lone →
    ∃ u, Era β Γ t T u ∧
      (∀ i, π i = .None → Term.occ i u = 0) ∧
      (∀ i, π i = .Lone → Term.occ i u ≤ 1) := by
  induction h with
  | @var Γ0 i0 T0 q0 hg =>
    intro hq
    subst hq
    refine ⟨.Var i0, .var hg, ?_, ?_⟩
    · intro i hi
      simp only [Term.occ]
      rw [if_neg ?_]
      intro he
      subst he
      simp only [Uses.one, if_pos] at hi
      exact Quant.noConfusion hi
    · intro i _
      simp only [Term.occ]
      split <;> omega
  | ref hk hlv =>
    intro hq
    subst hq
    exact ⟨_, .ref hk (hlv (by intro hc; cases hc)), fun i _ => _root_.rfl,
      fun i _ => by simp [Term.occ]⟩
  | refA hk h0 =>
    intro _
    exact ⟨_, .refA hk h0, fun i _ => _root_.rfl,
      fun i _ => by simp [Term.occ]⟩
  | adt hk =>
    intro _
    exact ⟨_, .adt hk, fun i _ => _root_.rfl, fun i _ => by simp [Term.occ]⟩
  | ctr hk hc hr =>
    intro _
    exact ⟨_, .ctr hk hc hr, fun i _ => _root_.rfl,
      fun i _ => by simp [Term.occ]⟩
  | typ =>
    intro _
    exact ⟨_, .typ, fun i _ => _root_.rfl, fun i _ => by simp [Term.occ]⟩
  | all hq' hA hB _ _ =>
    intro _
    exact ⟨_, .all hq' hA hB, fun i _ => _root_.rfl,
      fun i _ => by simp [Term.occ]⟩
  | @lam q0 A0 Γ0 f0 B0 π0 q' hf hle ihf =>
    intro hq
    subst hq
    obtain ⟨uf, hera, h0, h1⟩ := ihf _root_.rfl
    refine ⟨.Lam uf, .lam hera ?_, ?_, ?_⟩
    · intro hq'
      cases hqe : q' with
      | None =>
        rw [hqe] at hle
        rw [h0 0 (Quant.le_none hle)]
        exact Nat.zero_le _
      | Lone =>
        rw [hqe] at hle
        cases hp0 : π0 0 with
        | None =>
          rw [h0 0 hp0]
          exact Nat.zero_le _
        | Lone => exact h1 0 hp0
        | Many =>
          rw [hp0] at hle
          exact absurd hle (by intro hc; cases hc)
      | Many => exact absurd hqe hq'
    · intro i hi
      exact h0 (i + 1) hi
    · intro i hi
      exact h1 (i + 1) hi
  | @app q3 q0 Γ0 f0 A0 B0 πf x0 πx hq3 hf hx ihf ihx =>
    intro hq
    cases hq3' : q3 with
    | None =>
      subst hq3'
      obtain ⟨uf, hera, h0, h1⟩ := ihf hq
      subst hq
      refine ⟨.App uf .Typ, .app_dead hera hx, ?_, ?_⟩
      · intro i hi
        obtain ⟨hif, _⟩ := Quant.add_eq_none hi
        simp only [Term.occ]
        rw [h0 i hif]
      · intro i hi
        simp only [Term.occ]
        cases Quant.add_eq_lone hi with
        | inl h2 =>
          rw [h0 i h2.1]
          omega
        | inr h2 =>
          have := h1 i h2.1
          omega
    | Lone =>
      subst hq3'
      obtain ⟨uf, heraf, hf0, hf1⟩ := ihf hq
      obtain ⟨ux, herax, hx0, hx1⟩ := ihx hq
      subst hq
      refine ⟨.App uf ux, .app_live heraf herax, ?_, ?_⟩
      · intro i hi
        obtain ⟨hif, hix⟩ := Quant.add_eq_none hi
        simp only [Term.occ]
        rw [hf0 i hif, hx0 i hix]
      · intro i hi
        simp only [Term.occ]
        cases Quant.add_eq_lone hi with
        | inl h2 =>
          rw [hf0 i h2.1]
          have := hx1 i h2.2
          omega
        | inr h2 =>
          rw [hx0 i h2.2]
          have := hf1 i h2.1
          omega
    | Many => exact absurd hq3' hq3
  | @let_ qb q0 Γ0 v0 A0 πv b0 T0 πb hqb hv hb hle ihv ihb =>
    intro hq
    cases hqb' : qb with
    | None =>
      subst hqb'
      obtain ⟨ub, herab, hb0, hb1⟩ := ihb hq
      subst hq
      refine ⟨.Let .None .Typ ub, .let_dead hv herab
        (hb0 0 (Quant.le_none hle)), ?_, ?_⟩
      · intro i hi
        obtain ⟨_, hib⟩ := Quant.add_eq_none hi
        simp only [Term.occ]
        rw [hb0 (i + 1) hib]
      · intro i hi
        simp only [Term.occ]
        cases Quant.add_eq_lone hi with
        | inl h2 =>
          have := hb1 (i + 1) h2.2
          omega
        | inr h2 =>
          have := hb0 (i + 1) h2.2
          omega
    | Lone =>
      subst hqb'
      obtain ⟨uv, herav, hv0, hv1⟩ := ihv hq
      obtain ⟨ub, herab, hb0, hb1⟩ := ihb hq
      have hocc : Term.occ 0 ub ≤ 1 := by
        cases hp0 : πb 0 with
        | None =>
          rw [hb0 0 hp0]
          exact Nat.zero_le _
        | Lone => exact hb1 0 hp0
        | Many =>
          rw [hp0] at hle
          exact absurd hle (by intro hc; cases hc)
      subst hq
      refine ⟨.Let .Lone uv ub, .let_live herav herab hocc, ?_, ?_⟩
      · intro i hi
        obtain ⟨hiv, hib⟩ := Quant.add_eq_none hi
        simp only [Term.occ]
        rw [hv0 i hiv, hb0 (i + 1) hib]
      · intro i hi
        simp only [Term.occ]
        cases Quant.add_eq_lone hi with
        | inl h2 =>
          rw [hv0 i h2.1]
          have := hb1 (i + 1) h2.2
          omega
        | inr h2 =>
          rw [hb0 (i + 1) h2.2]
          have := hv1 i h2.1
          omega
    | Many => exact absurd hqb' hqb
  | eql hT ha hb _ _ _ =>
    intro _
    exact ⟨_, .eql hT ha hb, fun i _ => _root_.rfl,
      fun i _ => by simp [Term.occ]⟩
  | rfl hc =>
    intro _
    exact ⟨_, .rfl hc, fun i _ => _root_.rfl, fun i _ => by simp [Term.occ]⟩
  | @rwt q0 Γ0 e0 x0 y0 T0 πe P0 πP f0 πf he hP hf ihe _ ihf =>
    intro hq
    obtain ⟨ue, herae, he0, he1⟩ := ihe hq
    obtain ⟨uf, heraf, hf0, hf1⟩ := ihf hq
    refine ⟨.Rwt ue .Typ uf, .rwt herae hP heraf, ?_, ?_⟩
    · intro i hi
      obtain ⟨hie, hif⟩ := Quant.add_eq_none hi
      simp only [Term.occ]
      rw [he0 i hie, hf0 i hif]
    · intro i hi
      simp only [Term.occ]
      cases Quant.add_eq_lone hi with
      | inl h2 =>
        rw [he0 i h2.1]
        have := hf1 i h2.2
        omega
      | inr h2 =>
        rw [hf0 i h2.2]
        have := he1 i h2.1
        omega
  | @mat a0 A0 c0 C0 r0 q0 q' ps0 telF B0 G0 Γ0 h0 πh m0 πm hk hc hr hlen
      hlive hins hgoal hharm hmarm ihh ihm =>
    intro hq
    obtain ⟨uh, herah, hh0, hh1⟩ := ihh hq
    obtain ⟨um, heram, hm0, hm1⟩ := ihm hq
    subst hq
    refine ⟨.Mat a0 c0 uh um, .mat hk hc hr hlen
      (hlive (fun hc2 => Quant.noConfusion hc2)) hins hgoal
      herah heram, ?_, ?_⟩
    · intro i hi
      obtain ⟨hih, him⟩ := Quant.join_eq_none hi
      simp only [Term.occ]
      rw [hh0 i hih, hm0 i him]
      rfl
    · intro i hi
      simp only [Term.occ]
      obtain ⟨hih, him⟩ := Quant.join_eq_lone hi
      have hhb : Term.occ i uh ≤ 1 := by
        rcases hih with hih | hih
        · rw [hh0 i hih]; exact Nat.zero_le _
        · exact hh1 i hih
      have hmb : Term.occ i um ≤ 1 := by
        rcases him with him | him
        · rw [hm0 i him]; exact Nat.zero_le _
        · exact hm1 i him
      exact Nat.max_le.mpr ⟨hhb, hmb⟩
  | efq hk hall hlive =>
    intro hq
    subst hq
    exact ⟨_, .efq hk hall (hlive (fun hc2 => Quant.noConfusion hc2)),
      fun i _ => _root_.rfl, fun i _ => by simp [Term.occ]⟩
  | cnv ht hc iht =>
    intro hq
    obtain ⟨u, hera, h0, h1⟩ := iht hq
    exact ⟨u, .cnv hera hc, h0, h1⟩


-- an erasure weighs no more than the raw term's bound
theorem Era.wub_le (pr : Nat → Nat) (hpr : ∀ k, 1 ≤ pr k)
    (h : Era β Γ t T u) : Term.wgt pr u ≤ Term.wub pr t := by
  induction h
  case var => exact Nat.le_refl _
  case ref => exact Nat.le_refl _
  case refA =>
    show Term.wgt pr (.Adt _ _) ≤ Term.wub pr (.Ref _)
    simp only [Term.wgt, Term.wub]
    exact hpr _
  case adt => exact Nat.le_refl _
  case ctr => exact Nat.le_refl _
  case typ => exact Nat.le_refl _
  case all =>
    simp only [Term.wgt, Term.wub]
    omega
  case lam ih =>
    simp only [Term.wgt, Term.wub]
    omega
  case app_live ihf ihx =>
    simp only [Term.wgt, Term.wub]
    omega
  case app_dead hx ihf =>
    simp only [Term.wgt, Term.wub]
    exact Nat.add_le_add (Nat.add_le_add_left ihf 1)
      (Term.wub_pos pr hpr _)
  case let_live ihv ihb =>
    simp only [Term.wgt, Term.wub]
    omega
  case let_dead ihb =>
    simp only [Term.wgt, Term.wub]
    exact Nat.add_le_add (Nat.add_le_add_left (Term.wub_pos pr hpr _) 1) ihb
  case eql =>
    simp only [Term.wgt, Term.wub]
    omega
  case rfl => exact Nat.le_refl _
  case rwt ihe ihf =>
    simp only [Term.wgt, Term.wub]
    exact Nat.add_le_add (Nat.add_le_add
      (Nat.add_le_add_left ihe 1) (Term.wub_pos pr hpr _)) ihf
  case mat ihh ihm =>
    simp only [Term.wgt, Term.wub]
    exact Nat.add_le_add_left (Nat.max_le.mpr
      ⟨Nat.le_trans ihh (Nat.le_max_left _ _),
       Nat.le_trans ihm (Nat.le_max_right _ _)⟩) 1
  case efq => exact Nat.le_refl _
  case cnv ih => exact ih


theorem Term.shiftN_closed (h : t.Closed 0) : ∀ n, Term.shiftN n t = t := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    show Term.shift 0 (Term.shiftN n t) = t
    rw [ih, Term.shift_closed t 0 0 h (Nat.le_refl 0)]

-- substituting a closed term preserves occurrence counts below the cut
-- erasure weakens along a context insertion
theorem Era.weaken (hβ : Book.Closed β) (h : Era β Γ t T u) :
    ∀ {n : Nat} {U : Term} {Γ' : Ctx}, Ins U n Γ Γ' →
    Era β Γ' (Term.shift n t) (Term.shift n T) (Term.shift n u) := by
  induction h with
  | @var Γ0 i T0 hg =>
    intro n U Γ' hins
    simp only [Term.shift]
    by_cases hi : i < n
    · rw [if_pos hi]
      exact .var (hins.get_lt hi hg)
    · rw [if_neg hi]
      exact .var (hins.get_ge (by omega) hg)
  | @ref k d Γ0 hk hbne =>
    intro n U Γ' hins
    rw [Term.shift_closed d.ty 0 n (hβ.defn hk).1 (Nat.zero_le n)]
    exact .ref hk hbne
  | @refA k A Γ0 hk h0 =>
    intro n U Γ' hins
    exact .refA hk h0
  | @adt a A Γ0 r hk =>
    intro n U Γ' hins
    rw [Term.shift_closed A.sig 0 n (hβ.adtd hk).1 (Nat.zero_le n)]
    exact .adt hk
  | @ctr a A c C r Γ0 hk hc hr =>
    intro n U Γ' hins
    rw [Term.shift_closed _ 0 n
      (Term.retip_closed r _ C.ty 0 ((hβ.adtd hk).2 c C hc)) (Nat.zero_le n)]
    exact .ctr hk hc hr
  | typ =>
    intro n U Γ' hins
    exact .typ
  | all hq hA hB =>
    intro n U Γ' hins
    exact .all hq (hA.weaken hβ hins) (hB.weaken hβ (Ins.succ hins))
  | lam hf hocc ihf =>
    intro n U Γ' hins
    refine Era.lam (ihf (Ins.succ hins)) ?_
    intro hq'
    rw [Term.occ_shift_lt _ 0 (n + 1) (by omega)]
    exact hocc hq'
  | app_live hf hx ihf ihx =>
    intro n U Γ' hins
    rw [Term.shift_subst0]
    exact .app_live (ihf hins) (ihx hins)
  | app_dead hf hx ihf =>
    intro n U Γ' hins
    rw [Term.shift_subst0]
    exact .app_dead (ihf hins) (hx.weaken hβ hins)
  | let_live hv hb hocc ihv ihb =>
    intro n U Γ' hins
    have hb' := ihb (Ins.succ hins)
    rw [Term.shift_shift0] at hb'
    refine Era.let_live (ihv hins) hb' ?_
    rw [Term.occ_shift_lt _ 0 (n + 1) (by omega)]
    exact hocc
  | let_dead hv hb hocc ihb =>
    intro n U Γ' hins
    have hb' := ihb (Ins.succ hins)
    rw [Term.shift_shift0] at hb'
    refine Era.let_dead (hv.weaken hβ hins) hb' ?_
    rw [Term.occ_shift_lt _ 0 (n + 1) (by omega)]
    exact hocc
  | eql hT ha hb =>
    intro n U Γ' hins
    exact .eql (hT.weaken hβ hins) (ha.weaken hβ hins) (hb.weaken hβ hins)
  | rfl hc =>
    intro n U Γ' hins
    exact .rfl (hc.shift hβ n)
  | rwt he hP hf ihe ihf =>
    intro n U Γ' hins
    have hP' := hP.weaken hβ hins
    rw [Term.shift_jmotive] at hP'
    exact .rwt (ihe hins) hP' (ihf hins)
  | @mat a A c C r q' ps telF B G Γ0 h0 uh m0 um hk hc hr hlen hlive hins0
      hgoal hh hm ihh ihm =>
    intro n U Γ' hI
    simp only [Term.shift, Term.shift_apps]
    have hi' := hins0.shift n
    rw [Term.shift_closed C.ty 0 n ((hβ.adtd hk).2 c C hc)
      (Nat.zero_le n)] at hi'
    have hg' := hgoal.shift n
    have e : Term.shift n (Term.apps (.Ctr a c) ps)
        = Term.apps (.Ctr a c) (ps.map (Term.shift n)) := by
      rw [Term.shift_apps]
      rfl
    rw [e] at hg'
    refine Era.mat hk hc hr (by simp [hlen]) hlive hi' hg' (ihh hI) ?_
    have hm2 := ihm hI
    simp only [Term.shift, Term.shift_apps] at hm2
    exact hm2
  | @efq a A r q' Γ0 ps B hk hall hlive =>
    intro n U Γ' hins
    have e : Term.shift n (.All q' (Term.apps (.Adt a r) ps) B)
        = .All q' (Term.apps (.Adt a r) (ps.map (Term.shift n)))
            (B.shift (n + 1)) := by
      simp only [Term.shift, Term.shift_apps]
    rw [e]
    exact .efq hk hall hlive
  | cnv ht hc iht =>
    intro n U Γ' hins
    exact .cnv (iht hins) (hc.shift hβ n)


-- the value's erasure travels into the residue context, shifted
theorem Cut.evalue (hβ : Book.Closed β) (h : Cut v T n Γb Γres Γtl)
    (hera : Era β Γtl v T uv) :
    Era β Γres (Term.shiftN n v) (Term.shiftN n T) (Term.shiftN n uv) := by
  induction h with
  | zero => exact hera
  | @succ n Γ Γres Γtl A hcut ih =>
    have hw := (ih hera).weaken hβ
      (Ins.zero (U := Term.subst n (Term.shiftN n v) A))
    rwa [Term.shiftN_succ', Term.shiftN_succ', Term.shiftN_succ'] at hw

-- the substitution lemma for the erasure: a closed live value, with its
-- own erasure, substitutes into a live judgment and its skeleton
theorem Era.sub (hβ : Book.Closed β) (h : Era β Γb b B ub) :
    ∀ {n : Nat} {v T uv : Term} {qv : Quant} {πv : Uses} {Γres Γtl : Ctx},
    Cut v T n Γb Γres Γtl →
    Check β qv Γtl v T πv → qv ≠ .Many →
    Era β Γtl v T uv →
    v.Closed 0 → uv.Closed 0 →
    Era β Γres (Term.subst n v b) (Term.subst n v B)
      (Term.subst n uv ub) := by
  induction h with
  | @var Γ0 i T0 hg =>
    intro n v T uv qv πv Γres Γtl hcut hvC hqv hera hv hu
    by_cases h1 : i < n
    · have hgl := hcut.get_lt h1 hg
      rw [Term.shiftN_closed hv n] at hgl
      have hs : ∀ w : Term, Term.subst n w (Term.Var i) = Term.Var i := by
        intro w
        simp only [Term.subst]
        rw [if_neg (by omega), if_neg (by omega)]
      rw [hs v, hs uv]
      exact .var hgl
    · by_cases h2 : i = n
      · subst h2
        have hT0 : T0 = Term.shiftN (i + 1) T := by
          have hge := hcut.get_eq
          rw [hg] at hge
          exact Option.some_inj.mp hge
        subst hT0
        have hs : ∀ w : Term, Term.subst i w (Term.Var i) = w := by
          intro w
          simp [Term.subst]
        rw [hs v, hs uv, Term.subst_shiftN]
        have hev := hcut.evalue hβ hera
        rw [Term.shiftN_closed hv i, Term.shiftN_closed hu i] at hev
        exact hev
      · cases i with
        | zero => omega
        | succ j =>
          have hgg := hcut.get_gt (by omega) hg
          rw [Term.shiftN_closed hv n] at hgg
          have hs : ∀ w : Term, Term.subst n w (Term.Var (j + 1))
              = Term.Var j := by
            intro w
            simp only [Term.subst]
            rw [if_neg (by omega), if_pos (by omega)]
            rfl
          rw [hs v, hs uv]
          exact .var hgg
  | @ref k d Γ0 hk hbne =>
    intro n v T uv qv πv Γres Γtl hcut hvC hqv hera hv hu
    rw [Term.subst_closed d.ty 0 n v (hβ.defn hk).1 (Nat.zero_le n)]
    exact .ref hk hbne
  | @refA k A Γ0 hk h0 =>
    intro n v T uv qv πv Γres Γtl hcut hvC hqv hera hv hu
    exact .refA hk h0
  | @adt a A Γ0 r hk =>
    intro n v T uv qv πv Γres Γtl hcut hvC hqv hera hv hu
    rw [Term.subst_closed A.sig 0 n v (hβ.adtd hk).1 (Nat.zero_le n)]
    exact .adt hk
  | @ctr a A c C r Γ0 hk hc hr =>
    intro n v T uv qv πv Γres Γtl hcut hvC hqv hera hv hu
    rw [Term.subst_closed _ 0 n v
      (Term.retip_closed r _ C.ty 0 ((hβ.adtd hk).2 c C hc)) (Nat.zero_le n)]
    exact .ctr hk hc hr
  | typ =>
    intro n v T uv qv πv Γres Γtl hcut hvC hqv hera hv hu
    exact .typ
  | all hq' hA hB =>
    intro n v T uv qv πv Γres Γtl hcut hvC hqv hera hv hu
    have hcv : Term.shift 0 v = v := Term.shift_closed v 0 0 hv (Nat.le_refl 0)
    obtain ⟨πA', _, hA'⟩ := hA.sub hβ (fun hc => Quant.noConfusion hc)
      (Or.inr (Quant.le_none (hA.none_le_zero _root_.rfl n))) hcut hvC
    obtain ⟨πB', _, hB'⟩ := hB.sub hβ (fun hc => Quant.noConfusion hc)
      (Or.inr (Quant.le_none (hB.none_le_zero _root_.rfl (n + 1))))
      hcut.succ hvC
    rw [Term.shiftN_closed hv n] at hA'
    rw [Term.shiftN_closed hv n, Term.shiftN_closed hv (n + 1)] at hB'
    show Era β Γres (.All _ _ _) (Term.subst n v .Typ) .Typ
    simp only [Term.subst]
    rw [hcv]
    exact .all hq' hA' hB'
  | @lam A0 Γ0 f0 B0 uf q' hf hocc ihf =>
    intro n v T uv qv πv Γres Γtl hcut hvC hqv hera hv hu
    have hcv : Term.shift 0 v = v := Term.shift_closed v 0 0 hv (Nat.le_refl 0)
    have hcu : Term.shift 0 uv = uv :=
      Term.shift_closed uv 0 0 hu (Nat.le_refl 0)
    have hb := ihf hcut.succ hvC hqv hera hv hu
    rw [Term.shiftN_closed hv n] at hb
    show Era β Γres (.Lam _) (.All _ _ _) (.Lam _)
    rw [hcv, hcu]
    refine Era.lam hb ?_
    intro hq'
    rw [Term.occ_subst_closed hu uf (n + 1) 0 (by omega)]
    exact hocc hq'
  | @app_live Γ0 f0 A0 B0 uf x0 ux hf hx ihf ihx =>
    intro n v T uv qv πv Γres Γtl hcut hvC hqv hera hv hu
    have hcv : Term.shift 0 v = v := Term.shift_closed v 0 0 hv (Nat.le_refl 0)
    have hfs := ihf hcut hvC hqv hera hv hu
    simp only [Term.subst] at hfs
    rw [hcv] at hfs
    rw [Term.subst_subst0, hcv]
    exact .app_live hfs (ihx hcut hvC hqv hera hv hu)
  | @app_dead Γ0 f0 A0 B0 uf x0 πx hf hx ihf =>
    intro n v T uv qv πv Γres Γtl hcut hvC hqv hera hv hu
    have hcv : Term.shift 0 v = v := Term.shift_closed v 0 0 hv (Nat.le_refl 0)
    have hfs := ihf hcut hvC hqv hera hv hu
    simp only [Term.subst] at hfs
    rw [hcv] at hfs
    obtain ⟨πx', _, hx'⟩ := hx.sub hβ (fun hc => Quant.noConfusion hc)
      (Or.inr (Quant.le_none (hx.none_le_zero _root_.rfl n))) hcut hvC
    rw [Term.shiftN_closed hv n] at hx'
    rw [Term.subst_subst0, hcv]
    exact .app_dead hfs hx'
  | @let_live Γ0 v0 A0 uv0 b0 T0 ub0 hv0 hb0 hocc ihv ihb =>
    intro n v T uv qv πv Γres Γtl hcut hvC hqv hera hv hu
    have hcv : Term.shift 0 v = v := Term.shift_closed v 0 0 hv (Nat.le_refl 0)
    have hcu : Term.shift 0 uv = uv :=
      Term.shift_closed uv 0 0 hu (Nat.le_refl 0)
    have hbs := ihb hcut.succ hvC hqv hera hv hu
    have eT : Term.subst (n + 1) v (Term.shift 0 T0)
        = Term.shift 0 (Term.subst n v T0) := by
      have h2 := Term.shift_subst_lt T0 0 n v (Nat.zero_le n)
      rw [hcv] at h2
      exact h2.symm
    rw [eT, Term.shiftN_closed hv n] at hbs
    show Era β Γres (.Let .Lone _ _) _ (.Let .Lone _ _)
    rw [hcv, hcu]
    refine Era.let_live (ihv hcut hvC hqv hera hv hu) hbs ?_
    rw [Term.occ_subst_closed hu ub0 (n + 1) 0 (by omega)]
    exact hocc
  | @let_dead Γ0 v0 A0 πv0 b0 T0 ub0 hv0 hb0 hocc ihb =>
    intro n v T uv qv πv Γres Γtl hcut hvC hqv hera hv hu
    have hcv : Term.shift 0 v = v := Term.shift_closed v 0 0 hv (Nat.le_refl 0)
    have hcu : Term.shift 0 uv = uv :=
      Term.shift_closed uv 0 0 hu (Nat.le_refl 0)
    have hbs := ihb hcut.succ hvC hqv hera hv hu
    have eT : Term.subst (n + 1) v (Term.shift 0 T0)
        = Term.shift 0 (Term.subst n v T0) := by
      have h2 := Term.shift_subst_lt T0 0 n v (Nat.zero_le n)
      rw [hcv] at h2
      exact h2.symm
    rw [eT, Term.shiftN_closed hv n] at hbs
    obtain ⟨πv', _, hv'⟩ := hv0.sub hβ (fun hc => Quant.noConfusion hc)
      (Or.inr (Quant.le_none (hv0.none_le_zero _root_.rfl n))) hcut hvC
    rw [Term.shiftN_closed hv n] at hv'
    show Era β Γres (.Let .None _ _) _ (.Let .None _ _)
    rw [hcv, hcu]
    refine Era.let_dead hv' hbs ?_
    rw [Term.occ_subst_closed hu ub0 (n + 1) 0 (by omega)]
    exact hocc
  | eql hT0 ha hb =>
    intro n v T uv qv πv Γres Γtl hcut hvC hqv hera hv hu
    obtain ⟨π1, _, h1⟩ := hT0.sub hβ (fun hc => Quant.noConfusion hc)
      (Or.inr (Quant.le_none (hT0.none_le_zero _root_.rfl n))) hcut hvC
    obtain ⟨π2, _, h2⟩ := ha.sub hβ (fun hc => Quant.noConfusion hc)
      (Or.inr (Quant.le_none (ha.none_le_zero _root_.rfl n))) hcut hvC
    obtain ⟨π3, _, h3⟩ := hb.sub hβ (fun hc => Quant.noConfusion hc)
      (Or.inr (Quant.le_none (hb.none_le_zero _root_.rfl n))) hcut hvC
    rw [Term.shiftN_closed hv n] at h1 h2 h3
    exact .eql h1 h2 h3
  | rfl hc =>
    intro n v T uv qv πv Γres Γtl hcut hvC hqv hera hv hu
    exact .rfl (Conv.subst hβ hc (Conv.refl v) n)
  | rwt he hP hf ihe ihf =>
    intro n v T uv qv πv Γres Γtl hcut hvC hqv hera hv hu
    obtain ⟨πP', _, hP'⟩ := hP.sub hβ (fun hc => Quant.noConfusion hc)
      (Or.inr (Quant.le_none (hP.none_le_zero _root_.rfl n))) hcut hvC
    rw [Term.shiftN_closed hv n, Term.subst_jmotive] at hP'
    exact .rwt (ihe hcut hvC hqv hera hv hu) hP'
      (ihf hcut hvC hqv hera hv hu)
  | @mat a A c C r q' ps telF B G Γ0 h0 uh m0 um hk hc hr hlen hlive hins0
      hgoal hh hm ihh ihm =>
    intro n v T uv qv πv Γres Γtl hcut hvC hqv hera hv hu
    have hcv : Term.shift 0 v = v := Term.shift_closed v 0 0 hv (Nat.le_refl 0)
    have hins' := hins0.subst n v
    rw [Term.subst_closed C.ty 0 n _ ((hβ.adtd hk).2 c C hc)
      (Nat.zero_le n)] at hins'
    have hg' := hgoal.subst n v
    have e : Term.subst n v (Term.apps (.Ctr a c) ps)
        = Term.apps (.Ctr a c) (ps.map (Term.subst n v)) := by
      rw [Term.subst_apps]
      rfl
    rw [e] at hg'
    rw [hcv] at hg'
    simp only [Term.subst, Term.subst_apps]
    rw [hcv]
    refine Era.mat hk hc hr (by simp [hlen]) hlive hins' hg'
      (ihh hcut hvC hqv hera hv hu) ?_
    have hm2 := ihm hcut hvC hqv hera hv hu
    simp only [Term.subst, Term.subst_apps] at hm2
    rw [hcv] at hm2
    exact hm2
  | @efq a A r q' Γ0 ps B hk hall hlive =>
    intro n v T uv qv πv Γres Γtl hcut hvC hqv hera hv hu
    have e : Term.subst n v (.All q' (Term.apps (.Adt a r) ps) B)
        = .All q' (Term.apps (.Adt a r) (ps.map (Term.subst n v)))
            (Term.subst (n + 1) (Term.shift 0 v) B) := by
      simp only [Term.subst, Term.subst_apps]
    rw [e]
    exact .efq hk hall hlive
  | cnv ht hc iht =>
    intro n v T uv qv πv Γres Γtl hcut hvC hqv hera hv hu
    exact .cnv (iht hcut hvC hqv hera hv hu)
      (Conv.subst hβ hc (Conv.refl v) n)


-- the skeleton of a closed term is closed
theorem Era.closed_out (h : Era β Γ t T u) : u.Closed Γ.length := by
  induction h with
  | var hg => exact Ctx.get_lt hg
  | ref _ => trivial
  | refA _ _ => trivial
  | adt _ => trivial
  | ctr _ _ _ => trivial
  | typ => trivial
  | all _ _ _ => trivial
  | lam _ _ ihf => exact ihf
  | app_live _ _ ihf ihx => exact ⟨ihf, ihx⟩
  | app_dead _ _ ihf => exact ⟨ihf, trivial⟩
  | let_live _ _ _ ihv ihb => exact ⟨ihv, ihb⟩
  | let_dead _ _ _ ihb => exact ⟨trivial, ihb⟩
  | eql _ _ _ => trivial
  | rfl _ => trivial
  | rwt _ _ _ ihe ihf => exact ⟨ihe, trivial, ihf⟩
  | mat _ _ _ _ _ _ _ _ _ ihh ihm => exact ⟨ihh, ihm⟩
  | efq _ _ _ => trivial
  | cnv _ _ iht => exact iht

-- generation for the erasure, modulo conversion accumulated by cnv
theorem Era.lam_inv (hβ : Book.Closed β) (h : Era β Γ (.Lam f) T u) :
    ∃ q' A B uf, Conv β (.All q' A B) T ∧ Era β (A :: Γ) f B uf ∧
      (q' ≠ .Many → Term.occ 0 uf ≤ Quant.occN q') ∧ u = .Lam uf := by
  generalize he : Term.Lam f = t0 at h
  induction h <;> try exact Term.noConfusion he
  case lam hf hocc _ =>
    cases he
    exact ⟨_, _, _, _, Conv.refl _, hf, hocc, Eq.refl _⟩
  case cnv ht hc ih =>
    obtain ⟨q', A, B, uf, hcv, hf, hocc, hu⟩ := ih he
    exact ⟨q', A, B, uf, Conv.trans hβ hcv hc, hf, hocc, hu⟩

theorem Era.var_inv (hβ : Book.Closed β) (h : Era β Γ (.Var i) T u) :
    ∃ T0, Ctx.get Γ i = some T0 ∧ Conv β T0 T ∧ u = .Var i := by
  generalize he : Term.Var i = t0 at h
  induction h <;> try exact Term.noConfusion he
  case var hg =>
    cases he
    exact ⟨_, hg, Conv.refl _, _root_.rfl⟩
  case cnv ht hc ih =>
    obtain ⟨T0, hg, hcv, hu⟩ := ih he
    exact ⟨T0, hg, Conv.trans hβ hcv hc, hu⟩

theorem Era.ref_inv (hβ : Book.Closed β) (h : Era β Γ (.Ref k) T u) :
    (∃ d, Book.defn β k = some d ∧ d.body ≠ none ∧ Conv β d.ty T
       ∧ u = .Ref k)
    ∨ (∃ A, Book.adt β k = some A ∧ A.pn = 0 ∧ Conv β .Typ T
       ∧ u = .Adt k []) := by
  generalize he : Term.Ref k = t0 at h
  induction h <;> try exact Term.noConfusion he
  case ref hk hbne =>
    cases he
    exact Or.inl ⟨_, hk, hbne, Conv.refl _, Eq.refl _⟩
  case refA hk h0 =>
    cases he
    exact Or.inr ⟨_, hk, h0, Conv.refl _, Eq.refl _⟩
  case cnv ht hc ih =>
    rcases ih he with ⟨d, hk, hbne, hcv, hu⟩ | ⟨A, hk, h0, hcv, hu⟩
    · exact Or.inl ⟨d, hk, hbne, Conv.trans hβ hcv hc, hu⟩
    · exact Or.inr ⟨A, hk, h0, Conv.trans hβ hcv hc, hu⟩

theorem Era.rfl_inv (_hβ : Book.Closed β) (h : Era β Γ .Rfl T u) :
    u = .Rfl := by
  generalize he : Term.Rfl = t0 at h
  induction h <;> try exact Term.noConfusion he
  case rfl hc => rfl
  case cnv ht hc ih => exact ih he

theorem Era.ctr_head_inv (hβ : Book.Closed β) (h : Era β Γ (.Ctr a c) T u) :
    ∃ A C r0, Book.adt β a = some A ∧ AdtD.ctr A c = some C ∧ c ∉ r0 ∧
      Conv β (Term.retip r0 (A.pn + C.fn) C.ty) T ∧ u = .Ctr a c := by
  generalize he : Term.Ctr a c = t0 at h
  induction h <;> try exact Term.noConfusion he
  case ctr hk hc0 hr =>
    cases he
    exact ⟨_, _, _, hk, hc0, hr, Conv.refl _, Eq.refl _⟩
  case cnv ht hc ih =>
    obtain ⟨A, C, r0, hk, hc0, hr, hcv, hu⟩ := ih he
    exact ⟨A, C, r0, hk, hc0, hr, Conv.trans hβ hcv hc, hu⟩

theorem Era.app_inv (hβ : Book.Closed β) (h : Era β Γ (.App f x) T u) :
    (∃ A B uf ux, Era β Γ f (.All .Lone A B) uf ∧ Era β Γ x A ux ∧
      Conv β (Term.subst 0 x B) T ∧ u = .App uf ux) ∨
    (∃ A B uf πx, Era β Γ f (.All .None A B) uf ∧
      Check β .None Γ x A πx ∧
      Conv β (Term.subst 0 x B) T ∧ u = .App uf .Typ) := by
  generalize he : Term.App f x = t0 at h
  induction h <;> try exact Term.noConfusion he
  case app_live hf hx _ _ =>
    cases he
    exact .inl ⟨_, _, _, _, hf, hx, Conv.refl _, Eq.refl _⟩
  case app_dead hf hx _ =>
    cases he
    exact .inr ⟨_, _, _, _, hf, hx, Conv.refl _, Eq.refl _⟩
  case cnv ht hc ih =>
    rcases ih he with ⟨A, B, uf, ux, hf, hx, hcv, hu⟩ |
      ⟨A, B, uf, πx, hf, hx, hcv, hu⟩
    · exact .inl ⟨A, B, uf, ux, hf, hx, Conv.trans hβ hcv hc, hu⟩
    · exact .inr ⟨A, B, uf, πx, hf, hx, Conv.trans hβ hcv hc, hu⟩

theorem Era.let_inv (hβ : Book.Closed β) (h : Era β Γ (.Let qb v b) T u) :
    (∃ A uv T0 ub, qb = .Lone ∧ Era β Γ v A uv ∧
      Era β (A :: Γ) b (Term.shift 0 T0) ub ∧ Term.occ 0 ub ≤ 1 ∧
      Conv β T0 T ∧ u = .Let .Lone uv ub) ∨
    (∃ A πv T0 ub, qb = .None ∧ Check β .None Γ v A πv ∧
      Era β (A :: Γ) b (Term.shift 0 T0) ub ∧ Term.occ 0 ub = 0 ∧
      Conv β T0 T ∧ u = .Let .None .Typ ub) := by
  generalize he : Term.Let qb v b = t0 at h
  induction h <;> try exact Term.noConfusion he
  case let_live hv hb hocc _ _ =>
    cases he
    exact .inl ⟨_, _, _, _, Eq.refl _, hv, hb, hocc, Conv.refl _, Eq.refl _⟩
  case let_dead hv hb hocc _ =>
    cases he
    exact .inr ⟨_, _, _, _, Eq.refl _, hv, hb, hocc, Conv.refl _, Eq.refl _⟩
  case cnv ht hc ih =>
    rcases ih he with ⟨A, uv, T0, ub, hq, hv, hb, hocc, hcv, hu⟩ |
      ⟨A, πv, T0, ub, hq, hv, hb, hocc, hcv, hu⟩
    · exact .inl ⟨A, uv, T0, ub, hq, hv, hb, hocc, Conv.trans hβ hcv hc, hu⟩
    · exact .inr ⟨A, πv, T0, ub, hq, hv, hb, hocc, Conv.trans hβ hcv hc, hu⟩

theorem Era.rwt_inv (hβ : Book.Closed β) (h : Era β Γ (.Rwt e P f) T u) :
    ∃ x y T0 ue uf, Era β Γ e (.Eql x y T0) ue ∧
      Era β Γ f (.App (.App P x) .Rfl) uf ∧
      Conv β (.App (.App P y) e) T ∧ u = .Rwt ue .Typ uf := by
  generalize he : Term.Rwt e P f = t0 at h
  induction h <;> try exact Term.noConfusion he
  case rwt he0 hP hf0 _ _ =>
    cases he
    exact ⟨_, _, _, _, _, he0, hf0, Conv.refl _, Eq.refl _⟩
  case cnv ht hc ih =>
    obtain ⟨x, y, T0, ue, uf, he0, hf0, hcv, hu⟩ := ih he
    exact ⟨x, y, T0, ue, uf, he0, hf0, Conv.trans hβ hcv hc, hu⟩

theorem Era.mat_inv (hβ : Book.Closed β) (h : Era β Γ (.Mat a c hh mm) T u) :
    ∃ A C r ps telF B G q' uh um,
      Book.adt β a = some A ∧ AdtD.ctr A c = some C ∧ c ∉ r ∧
      ps.length = A.pn ∧ q' ≠ .None ∧
      Insts C.ty ps telF ∧
      MatGoal q' C.fn B (Term.apps (.Ctr a c) ps) telF G ∧
      Era β Γ hh G uh ∧
      Era β Γ mm (.All q' (Term.apps (.Adt a (c :: r)) ps) B) um ∧
      Conv β (.All q' (Term.apps (.Adt a r) ps) B) T ∧
      u = .Mat a c uh um := by
  generalize he : Term.Mat a c hh mm = t0 at h
  induction h <;> try exact Term.noConfusion he
  case mat hk hc0 hr hlen hlive hins hgoal hh0 hm0 _ _ =>
    cases he
    exact ⟨_, _, _, _, _, _, _, _, _, _, hk, hc0, hr, hlen, hlive, hins,
      hgoal, hh0, hm0, Conv.refl _, Eq.refl _⟩
  case cnv ht hc ih =>
    obtain ⟨A, C, r, ps, telF, B, G, q', uh, um, hk, hc0, hr, hlen, hlive,
      hins, hgoal, hh0, hm0, hcv, hu⟩ := ih he
    exact ⟨A, C, r, ps, telF, B, G, q', uh, um, hk, hc0, hr, hlen, hlive,
      hins, hgoal, hh0, hm0, Conv.trans hβ hcv hc, hu⟩


-- an erasure judgment embeds a (dead) typing of its subject: at the
-- None demand every binder constraint is vacuous
theorem Era.check_none (h : Era β Γ t T u) :
    ∃ π, Check β .None Γ t T π := by
  induction h with
  | var hg => exact ⟨_, .var hg⟩
  | ref hk _ => exact ⟨_, .ref hk (fun hq => absurd _root_.rfl hq)⟩
  | refA hk h0 => exact ⟨_, .refA hk h0⟩
  | adt hk => exact ⟨_, .adt hk⟩
  | ctr hk hc hr => exact ⟨_, .ctr hk hc hr⟩
  | typ => exact ⟨_, .typ⟩
  | all hq hA hB => exact ⟨_, .all hq hA hB⟩
  | lam hf _ ihf =>
    obtain ⟨πf, hf'⟩ := ihf
    refine ⟨_, Check.lam hf'.none_zero ?_⟩
    show Quant.le (Uses.zero 0) _
    exact Quant.none_le _
  | app_live hf hx ihf ihx =>
    obtain ⟨πf, hf'⟩ := ihf
    obtain ⟨πx, hx'⟩ := ihx
    exact ⟨_, .app (by intro hc; cases hc) hf' hx'⟩
  | app_dead hf hx ihf =>
    obtain ⟨πf, hf'⟩ := ihf
    exact ⟨_, .app (by intro hc; cases hc) hf' hx⟩
  | let_live hv hb _ ihv ihb =>
    obtain ⟨πv, hv'⟩ := ihv
    obtain ⟨πb, hb'⟩ := ihb
    refine ⟨_, Check.let_ (by intro hc; cases hc) hv' hb'.none_zero ?_⟩
    show Quant.le (Uses.zero 0) _
    exact Quant.none_le _
  | let_dead hv hb _ ihb =>
    obtain ⟨πb, hb'⟩ := ihb
    refine ⟨_, Check.let_ (by intro hc; cases hc) hv hb'.none_zero ?_⟩
    show Quant.le (Uses.zero 0) _
    exact Quant.none_le _
  | eql hT ha hb => exact ⟨_, .eql hT ha hb⟩
  | rfl hc => exact ⟨_, .rfl hc⟩
  | rwt he hP hf ihe ihf =>
    obtain ⟨πe, he'⟩ := ihe
    obtain ⟨πf, hf'⟩ := ihf
    exact ⟨_, .rwt he' hP hf'⟩
  | mat hk hc hr hlen hlive hins hgoal hh hm ihh ihm =>
    obtain ⟨πh, hh'⟩ := ihh
    obtain ⟨πm, hm'⟩ := ihm
    exact ⟨_, .mat hk hc hr hlen (fun hc2 => absurd _root_.rfl hc2)
      hins hgoal hh' hm'⟩
  | efq hk hall hlive =>
    exact ⟨_, .efq hk hall (fun hc2 => absurd _root_.rfl hc2)⟩
  | cnv _ hc iht =>
    obtain ⟨π, ht'⟩ := iht
    exact ⟨_, .cnv ht' hc⟩


-- substituting a DEAD value: the slot does not occur in the erasure, so
-- the term side substitutes the None-checked value while the erasure
-- side plugs the token
theorem Era.sub_dead (hβ : Book.Closed β) (h : Era β Γb b B ub) :
    ∀ {n : Nat} {v T : Term} {πv : Uses} {Γres Γtl : Ctx},
    Cut v T n Γb Γres Γtl →
    Check β .None Γtl v T πv →
    v.Closed 0 →
    Term.occ n ub = 0 →
    Era β Γres (Term.subst n v b) (Term.subst n v B)
      (Term.subst n .Typ ub) := by
  have hut : (Term.Typ).Closed 0 := trivial
  induction h with
  | @var Γ0 i T0 hg =>
    intro n v T πv Γres Γtl hcut hvC hv hocc
    by_cases h1 : i < n
    · have hgl := hcut.get_lt h1 hg
      rw [Term.shiftN_closed hv n] at hgl
      have hs : ∀ w : Term, Term.subst n w (Term.Var i) = Term.Var i := by
        intro w
        simp only [Term.subst]
        rw [if_neg (by omega), if_neg (by omega)]
      rw [hs v, hs .Typ]
      exact .var hgl
    · by_cases h2 : i = n
      · exfalso
        subst h2
        simp only [Term.occ, if_pos] at hocc
        omega
      · cases i with
        | zero => omega
        | succ j =>
          have hgg := hcut.get_gt (by omega) hg
          rw [Term.shiftN_closed hv n] at hgg
          have hs : ∀ w : Term, Term.subst n w (Term.Var (j + 1))
              = Term.Var j := by
            intro w
            simp only [Term.subst]
            rw [if_neg (by omega), if_pos (by omega)]
            rfl
          rw [hs v, hs .Typ]
          exact .var hgg
  | @ref k d Γ0 hk hbne =>
    intro n v T πv Γres Γtl hcut hvC hv hocc
    rw [Term.subst_closed d.ty 0 n v (hβ.defn hk).1 (Nat.zero_le n)]
    exact .ref hk hbne
  | @refA k A Γ0 hk h0 =>
    intro n v T πv Γres Γtl hcut hvC hv hocc
    exact .refA hk h0
  | @adt a A Γ0 r hk =>
    intro n v T πv Γres Γtl hcut hvC hv hocc
    rw [Term.subst_closed A.sig 0 n v (hβ.adtd hk).1 (Nat.zero_le n)]
    exact .adt hk
  | @ctr a A c C r Γ0 hk hc hr =>
    intro n v T πv Γres Γtl hcut hvC hv hocc
    rw [Term.subst_closed _ 0 n v
      (Term.retip_closed r _ C.ty 0 ((hβ.adtd hk).2 c C hc)) (Nat.zero_le n)]
    exact .ctr hk hc hr
  | typ =>
    intro n v T πv Γres Γtl hcut hvC hv hocc
    exact .typ
  | all hq' hA hB =>
    intro n v T πv Γres Γtl hcut hvC hv hocc
    have hcv : Term.shift 0 v = v := Term.shift_closed v 0 0 hv (Nat.le_refl 0)
    obtain ⟨πA', _, hA'⟩ := hA.sub hβ (fun hc => Quant.noConfusion hc)
      (Or.inr (Quant.le_none (hA.none_le_zero _root_.rfl n))) hcut hvC
    obtain ⟨πB', _, hB'⟩ := hB.sub hβ (fun hc => Quant.noConfusion hc)
      (Or.inr (Quant.le_none (hB.none_le_zero _root_.rfl (n + 1))))
      hcut.succ hvC
    rw [Term.shiftN_closed hv n] at hA'
    rw [Term.shiftN_closed hv n, Term.shiftN_closed hv (n + 1)] at hB'
    show Era β Γres (.All _ _ _) (Term.subst n v .Typ) .Typ
    simp only [Term.subst]
    rw [hcv]
    exact .all hq' hA' hB'
  | @lam A0 Γ0 f0 B0 uf q' hf hocc0 ihf =>
    intro n v T πv Γres Γtl hcut hvC hv hocc
    have hcv : Term.shift 0 v = v := Term.shift_closed v 0 0 hv (Nat.le_refl 0)
    have hb := ihf hcut.succ hvC hv (by
      simp only [Term.occ] at hocc
      exact hocc)
    rw [Term.shiftN_closed hv n] at hb
    show Era β Γres (.Lam _) (.All _ _ _) (.Lam _)
    rw [hcv]
    refine Era.lam hb ?_
    intro hq'
    rw [show Term.shift 0 (Term.Typ) = Term.Typ from _root_.rfl,
      Term.occ_subst_closed hut uf (n + 1) 0 (by omega)]
    exact hocc0 hq'
  | @app_live Γ0 f0 A0 B0 uf x0 ux hf hx ihf ihx =>
    intro n v T πv Γres Γtl hcut hvC hv hocc
    have hcv : Term.shift 0 v = v := Term.shift_closed v 0 0 hv (Nat.le_refl 0)
    simp only [Term.occ] at hocc
    have hfs := ihf hcut hvC hv (by omega)
    simp only [Term.subst] at hfs
    rw [hcv] at hfs
    rw [Term.subst_subst0, hcv]
    exact .app_live hfs (ihx hcut hvC hv (by omega))
  | @app_dead Γ0 f0 A0 B0 uf x0 πx hf hx ihf =>
    intro n v T πv Γres Γtl hcut hvC hv hocc
    have hcv : Term.shift 0 v = v := Term.shift_closed v 0 0 hv (Nat.le_refl 0)
    simp only [Term.occ] at hocc
    have hfs := ihf hcut hvC hv (by omega)
    simp only [Term.subst] at hfs
    rw [hcv] at hfs
    obtain ⟨πx', _, hx'⟩ := hx.sub hβ (fun hc => Quant.noConfusion hc)
      (Or.inr (Quant.le_none (hx.none_le_zero _root_.rfl n))) hcut hvC
    rw [Term.shiftN_closed hv n] at hx'
    rw [Term.subst_subst0, hcv]
    exact .app_dead hfs hx'
  | @let_live Γ0 v0 A0 uv0 b0 T0 ub0 hv0 hb0 hocc0 ihv ihb =>
    intro n v T πv Γres Γtl hcut hvC hv hocc
    have hcv : Term.shift 0 v = v := Term.shift_closed v 0 0 hv (Nat.le_refl 0)
    simp only [Term.occ] at hocc
    have hbs := ihb hcut.succ hvC hv (by omega)
    have eT : Term.subst (n + 1) v (Term.shift 0 T0)
        = Term.shift 0 (Term.subst n v T0) := by
      have h2 := Term.shift_subst_lt T0 0 n v (Nat.zero_le n)
      rw [hcv] at h2
      exact h2.symm
    rw [eT, Term.shiftN_closed hv n] at hbs
    show Era β Γres (.Let .Lone _ _) _ (.Let .Lone _ _)
    rw [hcv]
    refine Era.let_live (ihv hcut hvC hv (by omega)) hbs ?_
    rw [show Term.shift 0 (Term.Typ) = Term.Typ from _root_.rfl,
      Term.occ_subst_closed hut ub0 (n + 1) 0 (by omega)]
    exact hocc0
  | @let_dead Γ0 v0 A0 πv0 b0 T0 ub0 hv0 hb0 hocc0 ihb =>
    intro n v T πv Γres Γtl hcut hvC hv hocc
    have hcv : Term.shift 0 v = v := Term.shift_closed v 0 0 hv (Nat.le_refl 0)
    simp only [Term.occ] at hocc
    have hbs := ihb hcut.succ hvC hv (by omega)
    have eT : Term.subst (n + 1) v (Term.shift 0 T0)
        = Term.shift 0 (Term.subst n v T0) := by
      have h2 := Term.shift_subst_lt T0 0 n v (Nat.zero_le n)
      rw [hcv] at h2
      exact h2.symm
    rw [eT, Term.shiftN_closed hv n] at hbs
    obtain ⟨πv', _, hv'⟩ := hv0.sub hβ (fun hc => Quant.noConfusion hc)
      (Or.inr (Quant.le_none (hv0.none_le_zero _root_.rfl n))) hcut hvC
    rw [Term.shiftN_closed hv n] at hv'
    show Era β Γres (.Let .None _ _) _ (.Let .None _ _)
    rw [hcv]
    refine Era.let_dead hv' hbs ?_
    rw [show Term.shift 0 (Term.Typ) = Term.Typ from _root_.rfl,
      Term.occ_subst_closed hut ub0 (n + 1) 0 (by omega)]
    exact hocc0
  | eql hT0 ha hb =>
    intro n v T πv Γres Γtl hcut hvC hv hocc
    obtain ⟨π1, _, h1⟩ := hT0.sub hβ (fun hc => Quant.noConfusion hc)
      (Or.inr (Quant.le_none (hT0.none_le_zero _root_.rfl n))) hcut hvC
    obtain ⟨π2, _, h2⟩ := ha.sub hβ (fun hc => Quant.noConfusion hc)
      (Or.inr (Quant.le_none (ha.none_le_zero _root_.rfl n))) hcut hvC
    obtain ⟨π3, _, h3⟩ := hb.sub hβ (fun hc => Quant.noConfusion hc)
      (Or.inr (Quant.le_none (hb.none_le_zero _root_.rfl n))) hcut hvC
    rw [Term.shiftN_closed hv n] at h1 h2 h3
    exact .eql h1 h2 h3
  | rfl hc =>
    intro n v T πv Γres Γtl hcut hvC hv hocc
    exact .rfl (Conv.subst hβ hc (Conv.refl v) n)
  | rwt he hP hf ihe ihf =>
    intro n v T πv Γres Γtl hcut hvC hv hocc
    simp only [Term.occ] at hocc
    obtain ⟨πP', _, hP'⟩ := hP.sub hβ (fun hc => Quant.noConfusion hc)
      (Or.inr (Quant.le_none (hP.none_le_zero _root_.rfl n))) hcut hvC
    rw [Term.shiftN_closed hv n, Term.subst_jmotive] at hP'
    exact .rwt (ihe hcut hvC hv (by omega)) hP'
      (ihf hcut hvC hv (by omega))
  | @mat a A c C r q' ps telF B G Γ0 h0 uh m0 um hk hc hr hlen hlive hins0
      hgoal hh hm ihh ihm =>
    intro n v T πv Γres Γtl hcut hvC hv hocc
    have hcv : Term.shift 0 v = v := Term.shift_closed v 0 0 hv (Nat.le_refl 0)
    simp only [Term.occ] at hocc
    have hoh : Term.occ n uh = 0 := by
      have h2 : Term.occ n uh ≤ Nat.max (Term.occ n uh) (Term.occ n um) :=
        Nat.le_max_left _ _
      rw [hocc] at h2
      omega
    have hom : Term.occ n um = 0 := by
      have h2 : Term.occ n um ≤ Nat.max (Term.occ n uh) (Term.occ n um) :=
        Nat.le_max_right _ _
      rw [hocc] at h2
      omega
    have hins' := hins0.subst n v
    rw [Term.subst_closed C.ty 0 n _ ((hβ.adtd hk).2 c C hc)
      (Nat.zero_le n)] at hins'
    have hg' := hgoal.subst n v
    have e : Term.subst n v (Term.apps (.Ctr a c) ps)
        = Term.apps (.Ctr a c) (ps.map (Term.subst n v)) := by
      rw [Term.subst_apps]
      rfl
    rw [e] at hg'
    rw [hcv] at hg'
    simp only [Term.subst, Term.subst_apps]
    rw [hcv]
    refine Era.mat hk hc hr (by simp [hlen]) hlive hins' hg'
      (ihh hcut hvC hv hoh) ?_
    have hm2 := ihm hcut hvC hv hom
    simp only [Term.subst, Term.subst_apps] at hm2
    rw [hcv] at hm2
    exact hm2
  | @efq a A r q' Γ0 ps B hk hall hlive =>
    intro n v T πv Γres Γtl hcut hvC hv hocc
    have e : Term.subst n v (.All q' (Term.apps (.Adt a r) ps) B)
        = .All q' (Term.apps (.Adt a r) (ps.map (Term.subst n v)))
            (Term.subst (n + 1) (Term.shift 0 v) B) := by
      simp only [Term.subst, Term.subst_apps]
    rw [e]
    exact .efq hk hall hlive
  | cnv ht hc iht =>
    intro n v T πv Γres Γtl hcut hvC hv hocc
    exact .cnv (iht hcut hvC hv hocc)
      (Conv.subst hβ hc (Conv.refl v) n)


-- subject reduction along a weak run
theorem Check.preservation_red (hok : Book.Ok β) (hq : q ≠ .Many)
    (h : Check β q Γ t T π) (hr : Red β .weak t t') :
    ∃ π', Uses.le π' π ∧ Check β q Γ t' T π' := by
  induction hr generalizing π with
  | refl => exact ⟨π, Uses.le_refl π, h⟩
  | step s _ ih =>
    obtain ⟨π1, hle1, h1⟩ := subject_reduction_holds β _ _ _ _ _ _ hok hq h s
    obtain ⟨π2, hle2, h2⟩ := ih h1
    exact ⟨π2, Uses.le_trans hle2 hle1, h2⟩

-- ============================================================================
-- METATHEORY §NP — the erased spine: an application spine's erasure,
-- one Conv-linked arm at a time, with its inversion, its rebuild, its
-- projection to a dead checked spine (which lets every Check-side walk
-- lemma serve the erasure), and the spine weight law.
-- ============================================================================

inductive EraSpine (β : Book) (Γ : Ctx) :
    Term → List Term → Term → List Term → Prop
  | nil  : EraSpine β Γ T [] T []
  | live : Conv β T0 (.All .Lone A B) → Era β Γ x A ux →
           EraSpine β Γ (Term.subst 0 x B) as T' us →
           EraSpine β Γ T0 (x :: as) T' (ux :: us)
  | dead : Conv β T0 (.All .None A B) → Check β .None Γ x A πx →
           EraSpine β Γ (Term.subst 0 x B) as T' us →
           EraSpine β Γ T0 (x :: as) T' (.Typ :: us)

theorem EraSpine.conv_start (hβ : Book.Closed β)
    (hs : EraSpine β Γ T0 as T' us) (hc : Conv β T1 T0) :
    ∃ T'', EraSpine β Γ T1 as T'' us ∧ Conv β T'' T' := by
  cases hs with
  | nil => exact ⟨T1, .nil, hc⟩
  | live hc0 hx hrest =>
    exact ⟨_, .live (Conv.trans hβ hc hc0) hx hrest, Conv.refl _⟩
  | dead hc0 hx hrest =>
    exact ⟨_, .dead (Conv.trans hβ hc hc0) hx hrest, Conv.refl _⟩

theorem Era.apps_inv (hβ : Book.Closed β) :
    ∀ {as : List Term} {f t T u : Term},
    t = Term.apps f as → Era β Γ t T u →
    ∃ Tf uf T' us, Era β Γ f Tf uf ∧ EraSpine β Γ Tf as T' us ∧
      Conv β T' T ∧ u = Term.apps uf us := by
  intro as
  induction as with
  | nil =>
    intro f t T u he h
    subst he
    exact ⟨T, u, T, [], h, .nil, Conv.refl _, _root_.rfl⟩
  | cons x rest ih =>
    intro f t T u he h
    obtain ⟨Tf, uf, T', us, hfx, hsp, hcv, hueq⟩ := ih (f := .App f x) he h
    rcases Era.app_inv hβ hfx with
      ⟨A, B, uf0, ux, hf0, hx0, hcv2, hueq2⟩ |
      ⟨A, B, uf0, πx, hf0, hx0, hcv2, hueq2⟩
    · obtain ⟨T'', hsp', hcv3⟩ := hsp.conv_start hβ hcv2
      subst hueq hueq2
      exact ⟨_, uf0, T'', ux :: us, hf0,
        .live (Conv.refl _) hx0 hsp', Conv.trans hβ hcv3 hcv, _root_.rfl⟩
    · obtain ⟨T'', hsp', hcv3⟩ := hsp.conv_start hβ hcv2
      subst hueq hueq2
      exact ⟨_, uf0, T'', .Typ :: us, hf0,
        .dead (Conv.refl _) hx0 hsp', Conv.trans hβ hcv3 hcv, _root_.rfl⟩

theorem Era.ref_head_body (hβ : Book.Closed β)
    (h : Era β Γ t T u) :
    ∀ {k : Nat} {args : List Term} {d : DefD},
    t = Term.apps (.Ref k) args → Book.defn β k = some d →
    d.body ≠ none := by
  intro k args d heq hk
  subst heq
  obtain ⟨Tf, uhead, T', us, hheadera, hspt, hcvT', hueq⟩ :=
    Era.apps_inv hβ (Eq.refl _) h
  rcases Era.ref_inv hβ hheadera with ⟨d', hk', hbne, _, _⟩ |
    ⟨A', hk', _, _, _⟩
  rotate_left
  · exact (Book.defn_adt_clash hk hk').elim
  rw [hk] at hk'
  cases hk'
  exact hbne

-- canonical forms at a family type: a value is a saturated constructor
-- spine of that family, not in the peeled set
theorem Check.canon_adt (hβ : Book.Closed β) (hok : Book.Ok β)
    (hv : Term.Value β v) (h : Check β q Γ v T π)
    (hbody : ∀ (k2 : Nat) (d2 : DefD) (args2 : List Term),
      v = Term.apps (.Ref k2) args2 → Book.defn β k2 = some d2 →
      d2.body ≠ none)
    (hA : Book.adt β a = some A)
    (hT : Conv β T (Term.apps (.Adt a r) ps)) :
    ∃ c C as, v = Term.apps (.Ctr a c) as ∧ AdtD.ctr A c = some C ∧
      c ∉ r ∧ as.length = A.pn + C.fn := by
  cases hv with
  | @stuck k2 d2 args2 hk2 hgate =>
    rcases hgate with hlt | hnone
    · obtain ⟨_, hnall2, _⟩ := hok.defn_clauses hk2
      obtain ⟨U, hnU, hcvU⟩ := Check.stuck_ref_all hβ hk2 hnall2
        args2.length args2 (Nat.le_refl _) hlt h
      have hge : 1 ≤ d2.n - args2.length := by omega
      obtain ⟨q4, A4, B4, hUeq, _⟩ : ∃ q4 A4 B4, U = Term.All q4 A4 B4
          ∧ Term.NAll (d2.n - args2.length - 1) B4 := by
        rcases hnn : d2.n - args2.length with _ | m2
        · omega
        · rw [hnn] at hnU
          obtain ⟨q4, A4, B4, hq4m, hUeq, hr⟩ := hnU
          refine ⟨q4, A4, B4, hUeq, ?_⟩
          simpa using hr
      subst hUeq
      exact absurd (Conv.trans hβ hcvU hT) Conv.all_adt
    · exact absurd hnone (hbody k2 d2 args2 _root_.rfl hk2)
  | typ =>
    exact absurd (Conv.trans hβ (Check.typ_subj_inv hβ h).1 hT) Conv.typ_adt
  | all =>
    exact absurd (Conv.trans hβ (Check.all_subj_inv hβ h).1 hT) Conv.typ_adt
  | eql =>
    exact absurd (Conv.trans hβ (Check.eql_subj_inv hβ h).1 hT) Conv.typ_adt
  | lam =>
    obtain ⟨q', A', B', πf, hcv, _, _, _⟩ := Check.lam_inv hβ h
    exact absurd (Conv.trans hβ hcv hT) Conv.all_adt
  | mat =>
    obtain ⟨A0, C0, r0, ps0, telF, B0, G, q', πh, πm, _, _, _, _, _, _, _,
      _, _, hcv, _⟩ := Check.mat_ty_inv hβ h
    exact absurd (Conv.trans hβ hcv hT) Conv.all_adt
  | efq =>
    obtain ⟨a0, A0, r0, q', ps0, B0, _, _, _, hcv, _⟩ := Check.efq_ty_inv hβ h
    exact absurd (Conv.trans hβ hcv hT) Conv.all_adt
  | rfl =>
    obtain ⟨x, y, T0, _, hcv, _⟩ := Check.rfl_inv hβ h
    exact absurd (Conv.trans hβ hcv hT) Conv.eql_adt
  | spine hsp =>
    rcases hsp.decompose with ⟨a0, r0, as, he⟩ | ⟨a0, c0, as, he⟩
    · subst he
      obtain ⟨Tf, T', πf, πs, hhead, hspine, hcvT, _⟩ :=
        Check.apps_inv hβ (Eq.refl _) h
      obtain ⟨A0, hA0, hcsig, _⟩ := Check.adt_head_inv hβ hhead
      have hshape := (hok.adt_clauses hA0).2.1
      rcases ChkSpine.stele_walk hβ hspine hshape hcsig with
        ⟨_, qA, A1, B1, hcAll⟩ | ⟨_, hcTyp⟩
      · exact absurd (Conv.trans hβ hcAll (Conv.trans hβ hcvT hT))
          Conv.all_adt
      · exact absurd (Conv.trans hβ hcTyp (Conv.trans hβ hcvT hT))
          Conv.typ_adt
    · subst he
      obtain ⟨Tf, T', πf, πs, hhead, hspine, hcvT, _⟩ :=
        Check.apps_inv hβ (Eq.refl _) h
      obtain ⟨A0, C0, rr0, hA0, hC0, hrr0, hcty, _⟩ :=
        Check.ctr_head_inv hβ hhead
      have hshape := ((hok.adt_clauses hA0).2.2 c0 C0 hC0).2
      have hw := WTele.retip rr0 hshape
      rcases ChkSpine.wtele_walk hβ hspine hw hcty with
        ⟨_, qA, A1, B1, hcAll⟩ | ⟨hlen, hcadt⟩
      · exact absurd (Conv.trans hβ hcAll (Conv.trans hβ hcvT hT))
          Conv.all_adt
      · have hconv : Conv β (Term.apps (.Adt a0 rr0) ([] ++ as.take A0.pn))
            (Term.apps (.Adt a r) ps) :=
          Conv.trans hβ hcadt (Conv.trans hβ hcvT hT)
        obtain ⟨ha_eq, hr_eq, _⟩ := Conv.adt_inj hconv
        subst ha_eq
        subst hr_eq
        rw [hA0] at hA
        cases hA
        exact ⟨c0, C0, as, Eq.refl _, hC0, hrr0, hlen⟩

-- canonical forms at an equation: a value is Rfl
theorem Check.canon_eql (hβ : Book.Closed β) (hok : Book.Ok β)
    (hv : Term.Value β v) (h : Check β q Γ v T π)
    (hbody : ∀ (k2 : Nat) (d2 : DefD) (args2 : List Term),
      v = Term.apps (.Ref k2) args2 → Book.defn β k2 = some d2 →
      d2.body ≠ none)
    (hT : Conv β T (.Eql x y T0)) : v = .Rfl := by
  cases hv with
  | @stuck k2 d2 args2 hk2 hgate =>
    rcases hgate with hlt | hnone
    · obtain ⟨_, hnall2, _⟩ := hok.defn_clauses hk2
      obtain ⟨U, hnU, hcvU⟩ := Check.stuck_ref_all hβ hk2 hnall2
        args2.length args2 (Nat.le_refl _) hlt h
      have hge : 1 ≤ d2.n - args2.length := by omega
      obtain ⟨q4, A4, B4, hUeq, _⟩ : ∃ q4 A4 B4, U = Term.All q4 A4 B4
          ∧ Term.NAll (d2.n - args2.length - 1) B4 := by
        rcases hnn : d2.n - args2.length with _ | m2
        · omega
        · rw [hnn] at hnU
          obtain ⟨q4, A4, B4, hq4m, hUeq, hr⟩ := hnU
          refine ⟨q4, A4, B4, hUeq, ?_⟩
          simpa using hr
      subst hUeq
      exact absurd (Conv.trans hβ hcvU hT) Conv.all_eql
    · exact absurd hnone (hbody k2 d2 args2 _root_.rfl hk2)
  | rfl => rfl
  | typ =>
    exact absurd (Conv.trans hβ (Check.typ_subj_inv hβ h).1 hT) Conv.typ_eql
  | all =>
    exact absurd (Conv.trans hβ (Check.all_subj_inv hβ h).1 hT) Conv.typ_eql
  | eql =>
    exact absurd (Conv.trans hβ (Check.eql_subj_inv hβ h).1 hT) Conv.typ_eql
  | lam =>
    obtain ⟨q', A', B', πf, hcv, _, _, _⟩ := Check.lam_inv hβ h
    exact absurd (Conv.trans hβ hcv hT) Conv.all_eql
  | mat =>
    obtain ⟨A0, C0, r0, ps0, telF, B0, G, q', πh, πm, _, _, _, _, _, _, _,
      _, _, hcv, _⟩ := Check.mat_ty_inv hβ h
    exact absurd (Conv.trans hβ hcv hT) Conv.all_eql
  | efq =>
    obtain ⟨a0, A0, r0, q', ps0, B0, _, _, _, hcv, _⟩ := Check.efq_ty_inv hβ h
    exact absurd (Conv.trans hβ hcv hT) Conv.all_eql
  | spine hsp =>
    rcases hsp.decompose with ⟨a0, r0, as, he⟩ | ⟨a0, c0, as, he⟩
    · subst he
      obtain ⟨Tf, T', πf, πs, hhead, hspine, hcvT, _⟩ :=
        Check.apps_inv hβ (Eq.refl _) h
      obtain ⟨A0, hA0, hcsig, _⟩ := Check.adt_head_inv hβ hhead
      have hshape := (hok.adt_clauses hA0).2.1
      rcases ChkSpine.stele_walk hβ hspine hshape hcsig with
        ⟨_, qA, A1, B1, hcAll⟩ | ⟨_, hcTyp⟩
      · exact absurd (Conv.trans hβ hcAll (Conv.trans hβ hcvT hT))
          Conv.all_eql
      · exact absurd (Conv.trans hβ hcTyp (Conv.trans hβ hcvT hT))
          Conv.typ_eql
    · subst he
      obtain ⟨Tf, T', πf, πs, hhead, hspine, hcvT, _⟩ :=
        Check.apps_inv hβ (Eq.refl _) h
      obtain ⟨A0, C0, rr0, hA0, hC0, hrr0, hcty, _⟩ :=
        Check.ctr_head_inv hβ hhead
      have hshape := ((hok.adt_clauses hA0).2.2 c0 C0 hC0).2
      have hw := WTele.retip rr0 hshape
      rcases ChkSpine.wtele_walk hβ hspine hw hcty with
        ⟨_, qA, A1, B1, hcAll⟩ | ⟨_, hcadt⟩
      · exact absurd (Conv.trans hβ hcAll (Conv.trans hβ hcvT hT))
          Conv.all_eql
      · exact absurd (Conv.trans hβ hcadt (Conv.trans hβ hcvT hT))
          (fun hc => Conv.eql_adt (Conv.symm hc))

-- claim (3): progress
theorem progress_holds : progress := by
  intro β q t T π hok hq h
  have hβ := hok.closed
  generalize hΓ : ([] : Ctx) = Γ0 at h
  revert hq
  induction h with
  | var hg =>
    intro hq
    subst hΓ
    simp [Ctx.get] at hg
  | @ref k d q' Γ' hk hlv =>
    intro hq
    cases hb : d.body with
    | some b =>
      by_cases hn0 : d.n = 0
      · exact .inr ⟨_, Step.dref (s := .Ref k) hk hb rfl (by rw [hn0]; rfl)⟩
      · exact .inl (Term.Value.stuck (args := []) hk
          (Or.inl (by simpa using Nat.pos_of_ne_zero hn0)))
    | none => exact absurd hb (hlv hq)
  | refA hk h0 => intro _; exact .inr ⟨_, Step.aref hk h0⟩
  | adt _ => intro _; exact .inl (.spine .adt)
  | ctr _ _ _ => intro _; exact .inl (.spine .ctr)
  | typ => intro _; exact .inl .typ
  | all _ _ _ _ _ => intro _; exact .inl .all
  | lam _ _ _ => intro _; exact .inl .lam
  | eql _ _ _ _ _ _ => intro _; exact .inl .eql
  | rfl _ => intro _; exact .inl .rfl
  | mat _ _ _ _ _ _ _ _ _ _ _ => intro _; exact .inl .mat
  | efq _ _ _ => intro _; exact .inl .efq
  | let_ _ _ _ _ _ _ => intro _; exact .inr ⟨_, .let_⟩
  | cnv _ _ ih => intro hq; exact ih hΓ hq
  | rwt he hP hf ihe _ ihf =>
    intro hq
    rcases ihe hΓ hq with hval | ⟨e', hstep⟩
    · have heq := Check.canon_eql hβ hok hval he
        (fun k2 d2 args2 hxeq hk2 =>
          Check.ref_head_body hβ args2.length args2 (Nat.le_refl _)
            (hxeq ▸ he) hq hk2)
        (Conv.refl _)
      subst heq
      exact .inr ⟨_, .rwt⟩
    · exact .inr ⟨_, .rwt_e hstep⟩
  | @app q3 q0 Γ1 f A' B' πf x πx hq3 hf hx ihf ihx =>
    intro hq
    rcases ihf hΓ hq with hvf | ⟨f', hstep⟩
    · cases hvf with
      | lam => exact .inr ⟨_, .beta⟩
      | spine hsp => exact .inl (.spine (.app hsp))
      | @stuck k2 d2 args2 hk2 hgate =>
        have happ : Term.App (Term.apps (.Ref k2) args2) x
            = Term.apps (.Ref k2) (args2 ++ [x]) :=
          (Term.apps_append (.Ref k2) args2 [x]).symm
        rw [happ]
        have hsp : Term.spine (Term.apps (.Ref k2) (args2 ++ [x]))
            = (.Ref k2, args2 ++ [x]) :=
          Term.spine_apps (h := .Ref k2) trivial (args2 ++ [x])
        rcases hgate with hlt | hnone
        · by_cases hsat : args2.length + 1 = d2.n
          · cases hb2 : d2.body with
            | some b2 =>
              refine .inr ⟨_, Step.dref hk2 hb2 (by rw [hsp]) ?_⟩
              rw [hsp]
              simpa using hsat
            | none => exact .inl (Term.Value.stuck hk2 (Or.inr hb2))
          · refine .inl (Term.Value.stuck hk2 (Or.inl ?_))
            simp only [List.length_append, List.length_cons, List.length_nil]
            omega
        · exact .inl (Term.Value.stuck hk2 (Or.inr hnone))
      | typ =>
        exact absurd (Check.typ_subj_inv hβ hf).1 Conv.typ_all
      | all =>
        exact absurd (Check.all_subj_inv hβ hf).1 Conv.typ_all
      | eql =>
        exact absurd (Check.eql_subj_inv hβ hf).1 Conv.typ_all
      | rfl =>
        obtain ⟨x0, y0, T0, _, hcv, _⟩ := Check.rfl_inv hβ hf
        exact absurd hcv (fun hc => Conv.all_eql (Conv.symm hc))
      | @mat a c mh mm =>
        obtain ⟨A0, C0, r0, ps0, telF, B0, G, q'0, πh, πm, hk, hc0, hr0,
          hlen0, hlq0, _, _, _, _, hcv, _⟩ := Check.mat_ty_inv hβ hf
        have hallinj := Conv.all_inj hcv
        have hdem : Quant.dem q3 q0 ≠ .None := by
          have hq3l : q3 ≠ .None := by
            rw [← hallinj.1]
            exact hlq0 hq
          cases q3 with
          | None => exact absurd _root_.rfl hq3l
          | Lone => exact hq
          | Many => exact hq
        rcases ihx hΓ hdem with hvx | ⟨x', hstep⟩
        · obtain ⟨c1, C1, as1, hxeq, hC1, hnotr, hlen1⟩ :=
            Check.canon_adt hβ hok hvx hx
              (fun k2 d2 args2 hxeq2 hk2 =>
                Check.ref_head_body hβ args2.length args2 (Nat.le_refl _)
                  (hxeq2 ▸ hx) hdem hk2)
              hk (Conv.symm hallinj.2.1)
          subst hxeq
          by_cases hcc : c1 = c
          · subst hcc
            right
            refine ⟨Term.apps mh (as1.drop A0.pn), ?_⟩
            have hsplit : Term.apps (.Ctr a c1) as1
                = Term.apps (.Ctr a c1)
                  (as1.take A0.pn ++ as1.drop A0.pn) := by
              rw [List.take_append_drop]
            rw [hsplit]
            exact Step.matc hk hC1
              (by simp [List.length_take]; omega)
              (by simp [List.length_drop]; omega)
          · exact .inr ⟨_, Step.matm (by simpa using hcc)⟩
        · exact .inr ⟨_, .app_a hstep⟩
      | efq =>
        obtain ⟨a0, A0, r0, q'0, ps0, B0, hk, hall, hlq0, hcv, _⟩ :=
          Check.efq_ty_inv hβ hf
        have hallinj := Conv.all_inj hcv
        have hdem : Quant.dem q3 q0 ≠ .None := by
          have hq3l : q3 ≠ .None := by
            rw [← hallinj.1]
            exact hlq0 hq
          cases q3 with
          | None => exact absurd _root_.rfl hq3l
          | Lone => exact hq
          | Many => exact hq
        rcases ihx hΓ hdem with hvx | ⟨x', hstep⟩
        · obtain ⟨c1, C1, as1, hxeq, hC1, hnotr, hlen1⟩ :=
            Check.canon_adt hβ hok hvx hx
              (fun k2 d2 args2 hxeq2 hk2 =>
                Check.ref_head_body hβ args2.length args2 (Nat.le_refl _)
                  (hxeq2 ▸ hx) hdem hk2)
              hk (Conv.symm hallinj.2.1)
          exact absurd (hall c1 (AdtD.ctr_lt hC1)) hnotr
        · exact .inr ⟨_, .app_a hstep⟩
    · exact .inr ⟨_, .app_f hstep⟩


-- ============================================================================
-- METATHEORY §N — the wall and its boundary. Dead code is specification,
-- not proof: over an Ok book with an empty family and a negative
-- recursive family — in source:
--
--   type Empty:
--   type W:
--     MkW{f: @g:W -> Empty}
--
-- the dead fragment types Curry's omega at Empty: the erased fragment is
-- the untyped lambda calculus, which is exactly why claim (5) demands
-- Lone. No positivity check excluded W; the wall is the usage discipline
-- of the LIVE fragment alone.
-- ============================================================================

def emptyA : AdtD := ⟨0, .Typ, []⟩

def emptyT : Term := .Adt 0 []

def wT : Term := .Adt 1 []

def wField : Term := .All .Lone wT emptyT

def mkwC : CtrD := ⟨1, .All .Lone wField wT⟩

def wA : AdtD := ⟨0, .Typ, [mkwC]⟩

def wBook : Book := [.adt emptyA, .adt wA]

def unwrapT : Term := .Mat 1 0 (.Lam (.Var 0)) .Efq

def deltaT : Term := .Lam (.App (.App unwrapT (.Var 0)) (.Var 0))

def omegaT : Term := .App deltaT (.App (.Ctr 1 0) deltaT)

theorem wbook_ok : Book.Ok wBook := by
  intro k t hk
  rcases k with _ | _ | k
  · injection hk with hk
    subst hk
    refine ⟨⟨Uses.zero, Check.typ⟩, by constructor, ?_⟩
    intro c C hc
    cases hc
  · injection hk with hk
    subst hk
    refine ⟨⟨Uses.zero, Check.typ⟩, by constructor, ?_⟩
    intro c C hc
    rcases c with _ | c
    · injection hc with hc
      subst hc
      refine ⟨⟨Uses.zero, ?_⟩, ?_⟩
      · exact Check.all (by intro h; cases h)
          (Check.all (by intro h; cases h)
            (Check.adt (A := wA) rfl) (Check.adt (A := emptyA) rfl))
          (Check.adt (A := wA) rfl)
      · exact ⟨.Lone, wField, wT, rfl, rfl⟩
    · cases hc
  · cases hk

theorem dead_omega_check : ∃ π, Check wBook .None [] omegaT emptyT π := by
  have hvar : Check wBook .None [wT] (.Var 0) wT (Uses.one 0 .None) :=
    Check.var rfl
  have hunwrap : Check wBook .None [wT] unwrapT (.All .Lone wT wField)
      (Uses.join (Uses.tail (Uses.one 0 .None)) Uses.zero) := by
    refine Check.mat (A := wA) (C := mkwC) (r := []) (ps := [])
      (B := wField) rfl rfl (by simp) rfl
      (fun h => absurd rfl h) Insts.nil (MatGoal.succ MatGoal.zero) ?_ ?_
    · exact Check.lam (Check.var rfl) (by trivial)
    · refine Check.efq (A := wA) (ps := []) rfl ?_ (fun h => absurd rfl h)
      intro c hc
      rcases c with _ | c
      · simp
      · exact absurd hc (by simp [wA])
  have happA : Check wBook .None [wT] (.App unwrapT (.Var 0)) wField
      (Uses.add (Uses.join (Uses.tail (Uses.one 0 .None)) Uses.zero)
        (Uses.one 0 .None)) :=
    Check.app (by intro h; cases h) hunwrap hvar
  have happB : Check wBook .None [wT]
      (.App (.App unwrapT (.Var 0)) (.Var 0)) emptyT
      (Uses.add (Uses.add (Uses.join (Uses.tail (Uses.one 0 .None))
        Uses.zero) (Uses.one 0 .None)) (Uses.one 0 .None)) :=
    Check.app (by intro h; cases h) happA hvar
  have hdelta : Check wBook .None [] deltaT (.All .Lone wT emptyT)
      (Uses.tail (Uses.add (Uses.add (Uses.join
        (Uses.tail (Uses.one 0 .None)) Uses.zero) (Uses.one 0 .None))
        (Uses.one 0 .None))) :=
    Check.lam happB (by trivial)
  have hmk : Check wBook .None [] (.App (.Ctr 1 0) deltaT) wT
      (Uses.add Uses.zero (Uses.tail (Uses.add (Uses.add (Uses.join
        (Uses.tail (Uses.one 0 .None)) Uses.zero) (Uses.one 0 .None))
        (Uses.one 0 .None)))) :=
    Check.app (by intro h; cases h)
      (Check.ctr (A := wA) (C := mkwC) (r := []) rfl rfl (by simp)) hdelta
  exact ⟨_, Check.app (by intro h; cases h) hdelta hmk⟩

-- claim (5)'s Lone demand is necessary: the boundary, as a theorem
theorem consistency_none_boundary :
    ∃ (β : Book) (a : Nat) (A : AdtD) (t : Term) (π : Uses),
      Book.Ok β ∧ Book.adt β a = some A ∧ A.ctrs = [] ∧
      Check β .None [] t (Term.apps (.Adt a []) []) π := by
  obtain ⟨π, h⟩ := dead_omega_check
  exact ⟨wBook, 0, emptyA, omegaT, π, wbook_ok, rfl, rfl, h⟩


theorem EraSpine.era (hs : EraSpine β Γ T0 as T' us) :
    ∀ {f uf : Term}, Era β Γ f T0 uf →
    Era β Γ (Term.apps f as) T' (Term.apps uf us) := by
  induction hs with
  | nil =>
    intro f uf hf
    exact hf
  | live hc0 hx hrest ih =>
    intro f uf hf
    exact ih (.app_live (Era.cnv hf hc0) hx)
  | dead hc0 hx hrest ih =>
    intro f uf hf
    exact ih (.app_dead (Era.cnv hf hc0) hx)

theorem EraSpine.append (h1 : EraSpine β Γ T0 as Tm us) :
    ∀ {bs T' vs}, EraSpine β Γ Tm bs T' vs →
    EraSpine β Γ T0 (as ++ bs) T' (us ++ vs) := by
  induction h1 with
  | nil => intro bs T' vs h2; exact h2
  | live hc0 hx hrest ih =>
    intro bs T' vs h2
    exact .live hc0 hx (ih h2)
  | dead hc0 hx hrest ih =>
    intro bs T' vs h2
    exact .dead hc0 hx (ih h2)

theorem EraSpine.chk (hs : EraSpine β Γ T0 as T' us) :
    ∃ πs, ChkSpine β .None Γ T0 as T' πs := by
  induction hs with
  | nil => exact ⟨_, .nil⟩
  | live hc0 hx hrest ih =>
    obtain ⟨πs, hc⟩ := ih
    obtain ⟨πx, hx'⟩ := hx.check_none
    exact ⟨_, .cons hc0 (by intro hc2; cases hc2) hx' hc⟩
  | dead hc0 hx hrest ih =>
    obtain ⟨πs, hc⟩ := ih
    exact ⟨_, .cons hc0 (by intro hc2; cases hc2) hx hc⟩

theorem EraSpine.append_split :
    ∀ {ps : List Term} {T0 xs T' us},
    EraSpine β Γ T0 (ps ++ xs) T' us →
    ∃ Tm us1 us2, EraSpine β Γ T0 ps Tm us1 ∧
      EraSpine β Γ Tm xs T' us2 ∧ us = us1 ++ us2 := by
  intro ps
  induction ps with
  | nil =>
    intro T0 xs T' us h
    exact ⟨T0, [], us, .nil, h, _root_.rfl⟩
  | cons p ps ih =>
    intro T0 xs T' us h
    cases h with
    | live hc0 hx hrest =>
      obtain ⟨Tm, us1, us2, h1, h2, he⟩ := ih hrest
      subst he
      exact ⟨Tm, _ :: us1, us2, .live hc0 hx h1, h2, _root_.rfl⟩
    | dead hc0 hx hrest =>
      obtain ⟨Tm, us1, us2, h1, h2, he⟩ := ih hrest
      subst he
      exact ⟨Tm, .Typ :: us1, us2, .dead hc0 hx h1, h2, _root_.rfl⟩

theorem Term.wgt_apps (pr : Nat → Nat) :
    ∀ (us : List Term) (h : Term),
    Term.wgt pr (Term.apps h us)
      = Term.wgt pr h + (us.map (Term.wgt pr)).sum + us.length := by
  intro us
  induction us with
  | nil => intro h; simp [Term.apps]
  | cons x xs ih =>
    intro h
    show Term.wgt pr (Term.apps (.App h x) xs) = _
    rw [ih (.App h x)]
    simp only [Term.wgt, List.map, List.sum_cons, List.length_cons]
    omega


-- the erased spine transports to any retipping of its shaped telescope,
-- with the SAME erased arguments (what re-checks a mismatched scrutinee
-- at the peeled domain without touching its skeleton)
theorem EraSpine.retipS (hβ : Book.Closed β)
    (hs : EraSpine β Γ T0 as T' us) :
    ∀ {a : Nat} {r : List Nat} {pn fn : Nat} {ps : List Term} {Tw : Term},
    WTele a r ps pn fn Tw → Conv β Tw T0 →
    as.length = pn + fn → ∀ (r' : List Nat),
    EraSpine β Γ (Term.retip r' (pn + fn) Tw) as
      (Term.apps (.Adt a r') (ps ++ as.take pn)) us := by
  induction hs with
  | nil =>
    intro a r pn fn ps Tw hw hc hlen r'
    have hpn : pn = 0 := by simp at hlen; omega
    have hfn : fn = 0 := by simp at hlen; omega
    subst hpn hfn
    simp only [WTele, FTele] at hw
    subst hw
    rw [show (0 : Nat) + 0 = 0 from rfl, Term.retip_adt_apps a r r' ps]
    rw [show ps ++ List.take 0 [] = ps from by simp]
    exact EraSpine.nil
  | @live T1 A1 B1 x1 ux1 as1 T1' us1 hc0 hx1 hrest ih =>
    intro a r pn fn ps Tw hw hc hlen r'
    cases pn with
    | succ pk =>
      obtain ⟨K, Bw, hTw, hwB⟩ := hw
      subst hTw
      have hall := Conv.all_inj (Conv.trans hβ hc hc0)
      exact absurd hall.1 (by intro hc2; cases hc2)
    | zero =>
      cases fn with
      | zero => simp at hlen
      | succ fk =>
        simp only [WTele] at hw
        obtain ⟨qf, F, Bw, hTw, hwB⟩ := hw
        subst hTw
        obtain ⟨qf', F', Bw', hTw2, hw'⟩ := FTele.field (x := x1)
          (show FTele a r ps (fk + 1) (.All qf F Bw)
            from ⟨qf, F, Bw, rfl, hwB⟩)
        cases hTw2
        have hall := Conv.all_inj (Conv.trans hβ hc hc0)
        have hBw : Conv β (Term.subst 0 x1 Bw) (Term.subst 0 x1 B1) :=
          Conv.subst hβ hall.2.2 (Conv.refl x1) 0
        have hlen' : as1.length = 0 + fk := by simp at hlen; omega
        have hstep := ih (show WTele a r ps 0 fk _ from hw') hBw hlen' r'
        rw [show (0 : Nat) + fk = fk from by omega,
          show ps ++ List.take 0 as1 = ps from by simp] at hstep
        have hcomm : Term.subst 0 x1 (Term.retip r' fk Bw)
            = Term.retip r' fk (Term.subst 0 x1 Bw) :=
          FTele.retip_subst hwB r' 0 x1
        have harg : Era β Γ x1 F ux1 := Era.cnv hx1 (Conv.symm hall.2.1)
        rw [show (0 : Nat) + (fk + 1) = fk + 1 from by omega,
          show ps ++ (x1 :: as1).take 0 = ps from by simp]
        rw [hall.1]
        refine EraSpine.live (Conv.refl _) harg ?_
        rw [hcomm]
        exact hstep
  | @dead T1 A1 B1 x1 πx1 as1 T1' us1 hc0 hx1 hrest ih =>
    intro a r pn fn ps Tw hw hc hlen r'
    cases pn with
    | succ pk =>
      obtain ⟨K, Bw, hTw, hwB⟩ := hw
      subst hTw
      obtain ⟨K', Bw', hTw2, hw'⟩ := WTele.param (x := x1)
        (show WTele a r ps (pk + 1) fn (.All .None K Bw)
          from ⟨K, Bw, rfl, hwB⟩)
      cases hTw2
      have hall := Conv.all_inj (Conv.trans hβ hc hc0)
      have hBw : Conv β (Term.subst 0 x1 Bw) (Term.subst 0 x1 B1) :=
        Conv.subst hβ hall.2.2 (Conv.refl x1) 0
      have hlen' : as1.length = pk + fn := by simp at hlen; omega
      have hstep := ih hw' hBw hlen' r'
      have hcomm : Term.subst 0 x1 (Term.retip r' (pk + fn) Bw)
          = Term.retip r' (pk + fn) (Term.subst 0 x1 Bw) :=
        WTele.retip_subst hwB r' 0 x1
      have harg : Check β .None Γ x1 K πx1 :=
        Check.cnv hx1 (Conv.symm hall.2.1)
      rw [show pk + 1 + fn = (pk + fn) + 1 from by omega,
        show ps ++ (x1 :: as1).take (pk + 1) = (ps ++ [x1]) ++ as1.take pk
          from by simp]
      refine EraSpine.dead (Conv.refl _) harg ?_
      show EraSpine β Γ (Term.subst 0 x1 (Term.retip r' (pk + fn) Bw))
        as1 _ us1
      rw [hcomm]
      exact hstep
    | zero =>
      cases fn with
      | zero => simp at hlen
      | succ fk =>
        simp only [WTele] at hw
        obtain ⟨qf, F, Bw, hTw, hwB⟩ := hw
        subst hTw
        obtain ⟨qf', F', Bw', hTw2, hw'⟩ := FTele.field (x := x1)
          (show FTele a r ps (fk + 1) (.All qf F Bw)
            from ⟨qf, F, Bw, rfl, hwB⟩)
        cases hTw2
        have hall := Conv.all_inj (Conv.trans hβ hc hc0)
        have hBw : Conv β (Term.subst 0 x1 Bw) (Term.subst 0 x1 B1) :=
          Conv.subst hβ hall.2.2 (Conv.refl x1) 0
        have hlen' : as1.length = 0 + fk := by simp at hlen; omega
        have hstep := ih (show WTele a r ps 0 fk _ from hw') hBw hlen' r'
        rw [show (0 : Nat) + fk = fk from by omega,
          show ps ++ List.take 0 as1 = ps from by simp] at hstep
        have hcomm : Term.subst 0 x1 (Term.retip r' fk Bw)
            = Term.retip r' fk (Term.subst 0 x1 Bw) :=
          FTele.retip_subst hwB r' 0 x1
        have harg : Check β .None Γ x1 F πx1 :=
          Check.cnv hx1 (Conv.symm hall.2.1)
        rw [show (0 : Nat) + (fk + 1) = fk + 1 from by omega,
          show ps ++ (x1 :: as1).take 0 = ps from by simp]
        rw [hall.1]
        refine EraSpine.dead (Conv.refl _) harg ?_
        rw [hcomm]
        exact hstep

-- the fired arm's erased spine: the goal telescope walks against the
-- scrutinee's erased fields, arm kinds preserved, tipping at the motive
-- on the rebuilt constructor
theorem MatGoal.erebuild (hβ : Book.Closed β) :
    ∀ (fn : Nat) {B s telG G : Term},
    MatGoal .Lone fn B s telG G →
    ∀ {TS : Term} {xs : List Term} {T' : Term} {us : List Term},
    EraSpine β Γ TS xs T' us →
    Conv β telG TS →
    xs.length = fn →
    EraSpine β Γ G xs (Term.subst 0 (Term.apps s xs) B) us := by
  intro fn
  induction fn with
  | zero =>
    intro B s telG G hg TS xs T' us hs hc hlen
    cases hg with
    | zero =>
      have hxs : xs = [] := by
        cases xs
        · rfl
        · simp at hlen
      subst hxs
      cases hs
      exact EraSpine.nil
  | succ n ih =>
    intro B s telG G hg TS xs T' us hs hc hlen
    cases hg with
    | succ hgrest =>
      rename_i Bf G0 qf F
      cases xs with
      | nil => simp at hlen
      | cons x rest =>
        have hsub := hgrest.subst 0 x
        rw [Term.subst_shift B 1 (Term.shift 0 x)] at hsub
        have es : Term.subst 0 x (.App (Term.shift 0 s) (.Var 0))
            = .App s x := by
          show Term.App _ _ = _
          rw [Term.subst_shift s 0 x]
          simp [Term.subst]
        rw [es] at hsub
        cases hs with
        | @live _ A1 B1 _ ux1 _ _ us1 hc0 hx1 hrest =>
          have hall := Conv.all_inj (Conv.trans hβ hc hc0)
          have harg : Era β Γ x F ux1 := Era.cnv hx1 (Conv.symm hall.2.1)
          have hrest' := ih hsub hrest
            (Conv.subst hβ hall.2.2 (Conv.refl x) 0) (by simp at hlen; omega)
          rw [hall.1]
          exact EraSpine.live (Conv.refl _) harg hrest'
        | @dead _ A1 B1 _ πx1 _ _ us1 hc0 hx1 hrest =>
          have hall := Conv.all_inj (Conv.trans hβ hc hc0)
          have harg : Check β .None Γ x F πx1 :=
            Check.cnv hx1 (Conv.symm hall.2.1)
          have hrest' := ih hsub hrest
            (Conv.subst hβ hall.2.2 (Conv.refl x) 0) (by simp at hlen; omega)
          rw [hall.1]
          exact EraSpine.dead (Conv.refl _) harg hrest'


-- weak congruence runs for the engine's frames
theorem Red.app_f_w (r : Red β .weak f f') :
    Red β .weak (.App f a) (.App f' a) := by
  induction r with
  | refl => exact .refl
  | step s _ ih => exact .step (.app_f s) ih

theorem Red.app_a_w (r : Red β .weak a a') :
    Red β .weak (.App f a) (.App f a') := by
  induction r with
  | refl => exact .refl
  | step s _ ih => exact .step (.app_a s) ih

theorem Red.rwt_e_w (r : Red β .weak e e') :
    Red β .weak (.Rwt e P f) (.Rwt e' P f) := by
  induction r with
  | refl => exact .refl
  | step s _ ih => exact .step (.rwt_e s) ih

-- a typed inversion for an erased Rfl: its equation converts
theorem Era.rfl_ty_inv (hβ : Book.Closed β) (h : Era β Γ .Rfl T u) :
    ∃ a b T0, Conv β a b ∧ Conv β (.Eql a b T0) T := by
  generalize he : Term.Rfl = t0 at h
  induction h <;> try exact Term.noConfusion he
  case rfl hc => exact ⟨_, _, _, hc, Conv.refl _⟩
  case cnv ht hc ih =>
    obtain ⟨a, b, T0, hab, hcv⟩ := ih he
    exact ⟨a, b, T0, hab, Conv.trans hβ hcv hc⟩


theorem Era.efq_ty_inv (hβ : Book.Closed β) (h : Era β Γ .Efq T u) :
    ∃ a A r q' ps B, Book.adt β a = some A ∧
      (∀ c, c < A.ctrs.length → c ∈ r) ∧ q' ≠ .None ∧
      Conv β (.All q' (Term.apps (.Adt a r) ps) B) T ∧ u = .Efq := by
  generalize he : Term.Efq = t0 at h
  induction h <;> try exact Term.noConfusion he
  case efq hk hall hlive =>
    exact ⟨_, _, _, _, _, _, hk, hall, hlive, Conv.refl _, _root_.rfl⟩
  case cnv ht hc ih =>
    obtain ⟨a, A, r, q', ps, B, hk, hall, hlive, hcv, hu⟩ := ih he
    exact ⟨a, A, r, q', ps, B, hk, hall, hlive, Conv.trans hβ hcv hc, hu⟩

-- ============================================================================
-- METATHEORY §NZ — the engine: over a plain (recursion-free) Ok book,
-- every closed live term runs to a weak-head value, by strong induction
-- on the weight of its erasure. Every interaction strictly drops the
-- weight; a δ-unfolding is paid by the reference's price.
-- ============================================================================

theorem engine (hok : Book.Ok β) (hplain : Book.Plain β) :
    ∀ (n : Nat) {t T u : Term},
    Era β [] t T u → t.Closed 0 →
    Term.wgt (Book.price β) u ≤ n →
    ∃ v uv, Red β .weak t v ∧ Term.Value β v ∧ v.Closed 0 ∧
      Era β [] v T uv ∧
      Term.wgt (Book.price β) uv ≤ Term.wgt (Book.price β) u := by
  have hβ := hok.closed
  have hpr : ∀ k, 1 ≤ Book.price β k := Book.price_pos β
  intro n
  induction n with
  | zero =>
    intro t T u hera hct hn
    have := Term.wgt_pos (Book.price β) hpr u
    omega
  | succ n ih =>
    intro t T u hera hct hn
    cases t with
    | Var i =>
      simp only [Term.Closed] at hct
      omega
    | Typ =>
      exact ⟨_, _, .refl, .typ, hct, hera, Nat.le_refl _⟩
    | All q' A B =>
      exact ⟨_, _, .refl, .all, hct, hera, Nat.le_refl _⟩
    | Lam f =>
      exact ⟨_, _, .refl, .lam, hct, hera, Nat.le_refl _⟩
    | Mat a c h m =>
      exact ⟨_, _, .refl, .mat, hct, hera, Nat.le_refl _⟩
    | Efq =>
      exact ⟨_, _, .refl, .efq, hct, hera, Nat.le_refl _⟩
    | Eql x y T0 =>
      exact ⟨_, _, .refl, .eql, hct, hera, Nat.le_refl _⟩
    | Rfl =>
      exact ⟨_, _, .refl, .rfl, hct, hera, Nat.le_refl _⟩
    | Adt a r =>
      exact ⟨_, _, .refl, .spine .adt, hct, hera, Nat.le_refl _⟩
    | Ctr a c =>
      exact ⟨_, _, .refl, .spine .ctr, hct, hera, Nat.le_refl _⟩
    | Ref k =>
      rcases Era.ref_inv hβ hera with ⟨d, hk, hbne, hcv, hueq⟩ |
        ⟨A, hk, h0, hcv, hueq⟩
      rotate_left
      · subst hueq
        have hsig : STele A.pn A.sig := (hok.adt_clauses hk).2.1
        rw [h0] at hsig
        refine ⟨.Adt k [], .Adt k [], .step (Step.aref hk h0) .refl,
          .spine .adt, trivial, ?_, Nat.le_refl _⟩
        refine Era.cnv (Era.adt hk) ?_
        rw [hsig]
        exact hcv
      subst hueq
      obtain ⟨b, hb⟩ : ∃ b, d.body = some b := by
        cases hbb : d.body with
        | some b2 => exact ⟨b2, _root_.rfl⟩
        | none => exact absurd hbb hbne
      by_cases hn0 : d.n = 0
      case neg =>
        exact ⟨_, _, .refl, Term.Value.stuck (args := []) hk
          (Or.inl (by simpa using Nat.pos_of_ne_zero hn0)), hct, hera,
          Nat.le_refl _⟩
      case pos =>
      obtain ⟨_, _, hcl⟩ := hok.defn_clauses hk
      obtain ⟨⟨πb, hbody⟩, _⟩ := hcl b hb
      obtain ⟨ub, hbera, _, _⟩ := hbody.era _root_.rfl
      have hwb : Term.wgt (Book.price β) ub
          ≤ Term.wub (Book.price β) b :=
        Era.wub_le (Book.price β) hpr hbera
      have hlt : Term.wub (Book.price β) b < Book.price β k :=
        Book.price_gt β hk hb (hplain k d hk b hb)
      have hbc := (hβ.defn hk).2 b hb
      have hwu : Term.wgt (Book.price β) (Term.Ref k) = Book.price β k :=
        _root_.rfl
      obtain ⟨v, uv, hred, hval, hvc, hvera, hwle⟩ :=
        ih (Era.cnv hbera hcv) hbc (by rw [hwu] at hn; omega)
      exact ⟨v, uv, .step (Step.dref (s := .Ref k) hk hb rfl
        (by rw [hn0]; rfl)) hred, hval, hvc, hvera, by
        rw [hwu]; omega⟩
    | Let qb v b =>
      rcases Era.let_inv hβ hera with
        ⟨A, uv0, T0, ub, hqb, hvera, hbera, hocc, hcv, hueq⟩ |
        ⟨A, πv, T0, ub, hqb, hvchk, hbera, hocc, hcv, hueq⟩
      · subst hqb hueq
        obtain ⟨πv0, hvchk0⟩ := hvera.check_none
        have huvc : uv0.Closed 0 := hvera.closed_out
        have hsub := hbera.sub hβ Cut.zero hvchk0
          (by intro hc; cases hc) hvera hct.1 huvc
        rw [Term.subst_shift T0 0 v] at hsub
        have hered := Era.cnv hsub hcv
        obtain ⟨πr, hrchk⟩ := hered.check_none
        have hrc := hrchk.closed
        have hocc1 : Term.occ 0 ub * Term.wgt (Book.price β) uv0
            ≤ Term.wgt (Book.price β) uv0 := by
          have := Nat.mul_le_mul_right (Term.wgt (Book.price β) uv0) hocc
          omega
        have hws := Term.wgt_subst (Book.price β) ub 0 uv0
        have hwlt : Term.wgt (Book.price β) (Term.subst 0 uv0 ub)
            ≤ n := by
          have hwu : Term.wgt (Book.price β) (.Let .Lone uv0 ub)
              = 1 + Term.wgt (Book.price β) uv0
                + Term.wgt (Book.price β) ub := _root_.rfl
          rw [hwu] at hn
          omega
        obtain ⟨w, uw, hred, hval, hwc, hwera, hwle⟩ :=
          ih hered hrc hwlt
        refine ⟨w, uw, .step .let_ hred, hval, hwc, hwera, ?_⟩
        have hwu : Term.wgt (Book.price β) (.Let .Lone uv0 ub)
            = 1 + Term.wgt (Book.price β) uv0
              + Term.wgt (Book.price β) ub := _root_.rfl
        rw [hwu]
        omega
      · subst hqb hueq
        have hsub := hbera.sub_dead hβ Cut.zero hvchk hct.1 hocc
        rw [Term.subst_shift T0 0 v] at hsub
        have hered := Era.cnv hsub hcv
        obtain ⟨πr, hrchk⟩ := hered.check_none
        have hrc := hrchk.closed
        have hws := Term.wgt_subst (Book.price β) ub 0 .Typ
        rw [hocc] at hws
        have hwlt : Term.wgt (Book.price β) (Term.subst 0 .Typ ub)
            ≤ n := by
          have hwu : Term.wgt (Book.price β) (.Let .None .Typ ub)
              = 1 + 1 + Term.wgt (Book.price β) ub := _root_.rfl
          rw [hwu] at hn
          omega
        obtain ⟨w, uw, hred, hval, hwc, hwera, hwle⟩ :=
          ih hered hrc hwlt
        refine ⟨w, uw, .step .let_ hred, hval, hwc, hwera, ?_⟩
        have hwu : Term.wgt (Book.price β) (.Let .None .Typ ub)
            = 1 + 1 + Term.wgt (Book.price β) ub := _root_.rfl
        rw [hwu]
        omega
    | Rwt e P f =>
      obtain ⟨x, y, T0, ue, uf, heera, hfera, hcv, hueq⟩ :=
        Era.rwt_inv hβ hera
      subst hueq
      have hwu : Term.wgt (Book.price β) (.Rwt ue .Typ uf)
          = 1 + Term.wgt (Book.price β) ue + 1
            + Term.wgt (Book.price β) uf := _root_.rfl
      obtain ⟨ve, uve, hrede, hvale, hvec, hveera, hwe⟩ :=
        ih heera hct.1 (by rw [hwu] at hn; omega)
      obtain ⟨πe0, hvechk⟩ := hveera.check_none
      have heq := Check.canon_eql hβ hok hvale hvechk
        (fun _ _ _ hxeq hk2 => Era.ref_head_body hβ hveera hxeq hk2)
        (Conv.refl _)
      subst heq
      obtain ⟨x', y', T0', hab, hcvE⟩ := Era.rfl_ty_inv hβ hveera
      obtain ⟨hcx, hcy, _⟩ := Conv.eql_inj hcvE
      have hxy : Conv β x y :=
        Conv.trans hβ (Conv.symm hcx) (Conv.trans hβ hab hcy)
      have hfera2 : Era β [] f T uf := by
        refine Era.cnv hfera (Conv.trans hβ ?_ hcv)
        exact Conv.app_cong hβ (Conv.app_cong hβ (Conv.refl _) hxy)
          (Conv.of_red_rev hrede.strong)
      obtain ⟨vf, uvf, hredf, hvalf, hvfc, hvfera, hwf⟩ :=
        ih hfera2 hct.2.2 (by rw [hwu] at hn; omega)
      refine ⟨vf, uvf, ?_, hvalf, hvfc, hvfera, ?_⟩
      · exact ((Red.rwt_e_w hrede).trans (.step .rwt .refl)).trans hredf
      · rw [hwu]
        omega
    | App f a =>
      rcases Era.app_inv hβ hera with
        ⟨A, B, uf, ua, hfera, haera, hcvT, hueq⟩ |
        ⟨A, B, uf, πa, hfera, hachk, hcvT, hueq⟩
      · -- live argument
        subst hueq
        have hwu : Term.wgt (Book.price β) (.App uf ua)
            = 1 + Term.wgt (Book.price β) uf
              + Term.wgt (Book.price β) ua := _root_.rfl
        obtain ⟨vf, uvf, hredf, hvalf, hvfc, hvfera, hwf⟩ :=
          ih hfera hct.1 (by rw [hwu] at hn; omega)
        cases hvalf with
        | @stuck k2 d2 args2 hk2 hgate =>
          have happ : Term.App (Term.apps (.Ref k2) args2) a
              = Term.apps (.Ref k2) (args2 ++ [a]) :=
            (Term.apps_append (.Ref k2) args2 [a]).symm
          obtain ⟨Tf, uhead, T'0, us, hheadera, hspE, hcvT', hueq3⟩ :=
            Era.apps_inv hβ (Eq.refl _) hvfera
          subst hueq3
          rcases Era.ref_inv hβ hheadera with
            ⟨d2', hk2', hbne2, hcvR, huh⟩ | ⟨A', hk2', _, _, _⟩
          rotate_left
          · exact (Book.defn_adt_clash hk2 hk2').elim
          subst huh
          rw [hk2] at hk2'
          injection hk2' with hd2eq
          subst hd2eq
          rcases hgate with hlt | hnone
          · by_cases hsat : args2.length + 1 = d2.n
            · -- the argument saturates the reference: unfold and recurse
              obtain ⟨b2, hb2⟩ : ∃ b2, d2.body = some b2 := by
                cases hbb : d2.body with
                | some b0 => exact ⟨b0, _root_.rfl⟩
                | none => exact absurd hbb hbne2
              obtain ⟨_, _, hcl⟩ := hok.defn_clauses hk2
              obtain ⟨⟨πb, hbody⟩, _⟩ := hcl b2 hb2
              obtain ⟨ub, hbera, _, _⟩ := hbody.era _root_.rfl
              have hwb : Term.wgt (Book.price β) ub
                  ≤ Term.wub (Book.price β) b2 :=
                Era.wub_le (Book.price β) hpr hbera
              have hltp : Term.wub (Book.price β) b2 < Book.price β k2 :=
                Book.price_gt β hk2 hb2 (hplain k2 d2 hk2 b2 hb2)
              have hspE2 : EraSpine β [] Tf (args2 ++ [a])
                  (Term.subst 0 a B) (us ++ [ua]) :=
                hspE.append (.live hcvT' haera .nil)
              have hredex : Era β [] (Term.apps b2 (args2 ++ [a])) T
                  (Term.apps ub (us ++ [ua])) :=
                Era.cnv (hspE2.era (Era.cnv hbera hcvR)) hcvT
              obtain ⟨πr, hrchk⟩ := hredex.check_none
              have hrc := hrchk.closed
              have hwr : Term.wgt (Book.price β) (Term.Ref k2)
                  = Book.price β k2 := _root_.rfl
              have hwvf := Term.wgt_apps (Book.price β) us (.Ref k2)
              rw [hwr] at hwvf
              have hwredex := Term.wgt_apps (Book.price β) (us ++ [ua]) ub
              rw [List.map_append, List.sum_append, List.length_append]
                at hwredex
              simp only [List.map_cons, List.map_nil, List.sum_cons,
                List.sum_nil, List.length_cons, List.length_nil] at hwredex
              obtain ⟨w, uw, hred, hval, hwc, hwera, hwle⟩ :=
                ih hredex hrc (by
                  rw [hwredex]
                  rw [hwu] at hn
                  rw [hwvf] at hwf
                  omega)
              have hsp2 : Term.spine (Term.apps (.Ref k2) (args2 ++ [a]))
                  = (.Ref k2, args2 ++ [a]) :=
                Term.spine_apps (h := .Ref k2) trivial (args2 ++ [a])
              have hstep : Step β .weak (Term.apps (.Ref k2) (args2 ++ [a]))
                  (Term.apps b2 (args2 ++ [a])) := by
                have h0 := Step.dref (β := β) (p := .weak)
                  (s := Term.apps (.Ref k2) (args2 ++ [a])) hk2 hb2
                  (by rw [hsp2]) (by rw [hsp2]; simpa using hsat)
                rwa [hsp2] at h0
              refine ⟨w, uw, ?_, hval, hwc, hwera, ?_⟩
              · refine (Red.app_f_w hredf).trans ?_
                rw [happ]
                exact .step hstep hred
              · rw [hwu]
                rw [hwvf] at hwf
                rw [hwredex] at hwle
                omega
            · -- still underapplied: the spine is a stuck weak value
              refine ⟨_, _, Red.app_f_w hredf, ?_,
                ⟨hvfc, hct.2⟩, Era.cnv (Era.app_live hvfera haera) hcvT, ?_⟩
              · rw [happ]
                refine Term.Value.stuck hk2 (Or.inl ?_)
                simp only [List.length_append, List.length_cons,
                  List.length_nil]
                omega
              · have hwuv : Term.wgt (Book.price β)
                    (Term.App (Term.apps (.Ref k2) us) ua)
                    = 1 + Term.wgt (Book.price β) (Term.apps (.Ref k2) us)
                      + Term.wgt (Book.price β) ua := _root_.rfl
                rw [hwu, hwuv]
                omega
          · exact absurd hnone hbne2
        | typ =>
          obtain ⟨π0, hc0⟩ := hvfera.check_none
          exact absurd (Check.typ_subj_inv hβ hc0).1 Conv.typ_all
        | all =>
          obtain ⟨π0, hc0⟩ := hvfera.check_none
          exact absurd (Check.all_subj_inv hβ hc0).1 Conv.typ_all
        | eql =>
          obtain ⟨π0, hc0⟩ := hvfera.check_none
          exact absurd (Check.eql_subj_inv hβ hc0).1 Conv.typ_all
        | rfl =>
          obtain ⟨π0, hc0⟩ := hvfera.check_none
          obtain ⟨x0, y0, T00, _, hcv0, _⟩ := Check.rfl_inv hβ hc0
          exact absurd hcv0 (fun hc2 => Conv.all_eql (Conv.symm hc2))
        | efq =>
          obtain ⟨π0, hc0⟩ := hvfera.check_none
          obtain ⟨a0, A0, r0, q'0, ps0, B0, hk0, hall0, _, hcv0, _⟩ :=
            Check.efq_ty_inv hβ hc0
          obtain ⟨_, hcA0, _⟩ := Conv.all_inj hcv0
          obtain ⟨va, uva, hreda, hvala, hvac, hvaera, hwa⟩ :=
            ih haera hct.2 (by rw [hwu] at hn; omega)
          obtain ⟨πa1, hvachk⟩ := hvaera.check_none
          obtain ⟨c1, C1, as1, hvaeq, hC1, hnr, hlen1⟩ :=
            Check.canon_adt hβ hok hvala hvachk
              (fun _ _ _ hxeq hk2 => Era.ref_head_body hβ hvaera hxeq hk2)
              hk0 (Conv.symm hcA0)
          exact absurd (hall0 c1 (AdtD.ctr_lt hC1)) hnr
        | lam =>
          rename_i g
          obtain ⟨q1, A1, B1, ug, hcvL, hbody, hocc, hueq2⟩ :=
            Era.lam_inv hβ hvfera
          obtain ⟨hq1, hcA, hcB⟩ := Conv.all_inj hcvL
          subst hq1
          subst hueq2
          have hocc1 := hocc (by intro hc; cases hc)
          obtain ⟨πa0, hachk0⟩ := haera.check_none
          have hsub := hbody.sub hβ Cut.zero
            (Check.cnv hachk0 (Conv.symm hcA)) (by intro hc; cases hc)
            (Era.cnv haera (Conv.symm hcA)) hct.2 haera.closed_out
          have hered := Era.cnv hsub (Conv.trans hβ
            (Conv.subst hβ hcB (Conv.refl a) 0) hcvT)
          obtain ⟨πr, hrchk⟩ := hered.check_none
          have hrc := hrchk.closed
          have hocc2 : Term.occ 0 ug * Term.wgt (Book.price β) ua
              ≤ Term.wgt (Book.price β) ua := by
            have := Nat.mul_le_mul_right (Term.wgt (Book.price β) ua) hocc1
            simp only [Quant.occN] at this
            omega
          have hws := Term.wgt_subst (Book.price β) ug 0 ua
          have hwlam : Term.wgt (Book.price β) (.Lam ug)
              = 1 + Term.wgt (Book.price β) ug := _root_.rfl
          rw [hwlam] at hwf
          obtain ⟨w, uw, hred, hval, hwc, hwera, hwle⟩ :=
            ih hered hrc (by rw [hwu] at hn; omega)
          refine ⟨w, uw, ?_, hval, hwc, hwera, ?_⟩
          · exact ((Red.app_f_w hredf).trans (.step .beta .refl)).trans hred
          · rw [hwu]
            omega
        | spine hsp =>
          have hframe : Era β [] (.App vf a) T (.App uvf ua) :=
            Era.cnv (.app_live hvfera haera) hcvT
          refine ⟨.App vf a, .App uvf ua, Red.app_f_w hredf,
            .spine (.app hsp), ⟨hvfc, hct.2⟩, hframe, ?_⟩
          show 1 + _ + _ ≤ _
          rw [hwu]
          omega
        | mat =>
          rename_i am cm hh mm
          obtain ⟨A0, C0, r0, ps0, telF, B0, G0, q'0, umh, umm, hk0, hc00,
            hr0, hlen0, hlive0, hins0, hgoal0, hmh, hmm2, hcvM, hueqM⟩ :=
            Era.mat_inv hβ hvfera
          obtain ⟨hq0, hcA2, hcB⟩ := Conv.all_inj hcvM
          subst hq0
          subst hueqM
          obtain ⟨va, uva, hreda, hvala, hvac, hvaera, hwa⟩ :=
            ih haera hct.2 (by rw [hwu] at hn; omega)
          obtain ⟨πa1, hvachk⟩ := hvaera.check_none
          obtain ⟨c1, C1, as1, hvaeq, hC1, hnr1, hlen1⟩ :=
            Check.canon_adt hβ hok hvala hvachk
              (fun _ _ _ hxeq hk2 => Era.ref_head_body hβ hvaera hxeq hk2)
              hk0 (Conv.symm hcA2)
          subst hvaeq
          obtain ⟨Tf, uhead, T', us, hheadera, hsp, hcvT', hueq3⟩ :=
            Era.apps_inv hβ (Eq.refl _) hvaera
          subst hueq3
          obtain ⟨A1, C1', rr0, hA1, hC1', hrr0, hcty, huhead⟩ :=
            Era.ctr_head_inv hβ hheadera
          subst huhead
          rw [hk0] at hA1
          cases hA1
          rw [hC1] at hC1'
          cases hC1'
          have hshape := ((hok.adt_clauses hk0).2.2 c1 C1 hC1).2
          have hw := WTele.retip rr0 hshape
          obtain ⟨πsp, hspc⟩ := hsp.chk
          rcases ChkSpine.wtele_walk hβ hspc hw hcty with
            ⟨_, qA, AA, BB, hcAll⟩ | ⟨hlenAs, hcadt⟩
          · exact absurd (Conv.trans hβ hcAll
              (Conv.trans hβ hcvT' (Conv.symm hcA2))) Conv.all_adt
          · have hchainC : Conv β
                (Term.apps (.Adt am rr0) ([] ++ as1.take A0.pn))
                (Term.apps (.Adt am r0) ps0) :=
              Conv.trans hβ hcadt (Conv.trans hβ hcvT' (Conv.symm hcA2))
            obtain ⟨_, hrr, hconvs⟩ := Conv.adt_inj hchainC
            subst hrr
            simp only [List.nil_append] at hconvs
            obtain ⟨ps1, xs1, hsplit, hlenp1, hlenx1⟩ :
                ∃ ps1 xs1, as1 = ps1 ++ xs1 ∧ ps1.length = A0.pn ∧
                  xs1.length = C1.fn := by
              refine ⟨as1.take A0.pn, as1.drop A0.pn,
                (List.take_append_drop _ _).symm, ?_, ?_⟩
              · rw [List.length_take]
                omega
              · rw [List.length_drop]
                omega
            subst hsplit
            have htake : (ps1 ++ xs1).take A0.pn = ps1 := by
              rw [← hlenp1]
              exact take_append ps1 xs1
            rw [htake] at hconvs
            have hwmat : Term.wgt (Book.price β) (.Mat am cm umh umm)
                = 1 + Nat.max (Term.wgt (Book.price β) umh)
                  (Term.wgt (Book.price β) umm) := _root_.rfl
            rw [hwmat] at hwf
            have hmaxl : Term.wgt (Book.price β) umh
                ≤ Nat.max (Term.wgt (Book.price β) umh)
                  (Term.wgt (Book.price β) umm) := Nat.le_max_left _ _
            have hmaxr : Term.wgt (Book.price β) umm
                ≤ Nat.max (Term.wgt (Book.price β) umh)
                  (Term.wgt (Book.price β) umm) := Nat.le_max_right _ _
            by_cases hcc : c1 = cm
            · -- matched constructor: fire the peel arm
              subst hcc
              rw [hc00] at hC1
              injection hC1 with hCC
              subst hCC
              have hchain0 := hsp.retipS hβ hw hcty hlenAs []
              rw [WTele.retip_retip hshape [] rr0,
                WTele.retip_self hshape] at hchain0
              obtain ⟨Tmid, us1, us2, hsp1, hsp2, husplit⟩ :=
                EraSpine.append_split hchain0
              subst husplit
              obtain ⟨π1c, hsp1c⟩ := hsp1.chk
              obtain ⟨Tinst, hinsts, hcvmid, hFsh⟩ :=
                ChkSpine.insts_mid hβ hsp1c hshape (Conv.refl _) hlenp1
              have hcvTel : Conv β Tinst telF :=
                Insts.conv hβ hinsts hins0 (Conv.refl _) hconvs
              have hGchain := MatGoal.erebuild hβ C0.fn hgoal0 hsp2
                (Conv.trans hβ (Conv.symm hcvTel) hcvmid) hlenx1
              have hredera := hGchain.era hmh
              have hscra : Conv β (Term.apps (.Ctr am c1) (ps0 ++ xs1)) a := by
                refine Conv.trans hβ ?_ (Conv.symm (Conv.of_red hreda.strong))
                exact Conv.apps_cong hβ (Conv.refl _)
                  (Convs.append (Convs.symm hconvs) (Convs.refl xs1))
              have herfin : Era β [] (Term.apps hh xs1) T
                  (Term.apps umh us2) := by
                refine Era.cnv hredera (Conv.trans hβ ?_ hcvT)
                rw [← Term.apps_append]
                exact Conv.subst hβ hcB hscra 0
              obtain ⟨πrr, hrchk⟩ := herfin.check_none
              have hrc := hrchk.closed
              have hwctr : Term.wgt (Book.price β) (Term.Ctr am c1) = 1 :=
                _root_.rfl
              rw [Term.wgt_apps (Book.price β) (us1 ++ us2) (.Ctr am c1),
                hwctr, List.map_append, List.sum_append,
                List.length_append] at hwa
              obtain ⟨w, uw, hred, hval, hwc, hwera, hwle⟩ :=
                ih herfin hrc (by
                  rw [hwu] at hn
                  rw [Term.wgt_apps (Book.price β) us2 umh]
                  omega)
              refine ⟨w, uw, ?_, hval, hwc, hwera, ?_⟩
              · exact (Red.app_f_w hredf).trans ((Red.app_a_w hreda).trans
                  ((Red.one (Step.matc hk0 hc00 hlenp1 hlenx1)).trans hred))
              · rw [hwu]
                rw [Term.wgt_apps (Book.price β) us2 umh] at hwle
                omega
            · -- mismatched constructor: peel and retry on the remainder arm
              have hchain2 := hsp.retipS hβ hw hcty hlenAs (cm :: rr0)
              rw [WTele.retip_retip hshape (cm :: rr0) rr0] at hchain2
              simp only [List.nil_append] at hchain2
              rw [htake] at hchain2
              have hheadty : Era β [] (.Ctr am c1)
                  (Term.retip (cm :: rr0) (A0.pn + C1.fn) C1.ty)
                  (.Ctr am c1) := by
                refine Era.ctr hk0 hC1 ?_
                intro hmem
                rcases List.mem_cons.mp hmem with h1 | h1
                · exact hcc h1
                · exact hrr0 h1
              have hscrut := hchain2.era hheadty
              have hscrut2 : Era β []
                  (Term.apps (.Ctr am c1) (ps1 ++ xs1))
                  (Term.apps (.Adt am (cm :: rr0)) ps0)
                  (Term.apps (.Ctr am c1) us) :=
                Era.cnv hscrut
                  (Conv.apps_cong hβ (Conv.refl _) hconvs)
              have hredera : Era β []
                  (.App mm (Term.apps (.Ctr am c1) (ps1 ++ xs1))) T
                  (.App umm (Term.apps (.Ctr am c1) us)) := by
                refine Era.cnv (Era.app_live hmm2 hscrut2)
                  (Conv.trans hβ ?_ hcvT)
                exact Conv.subst hβ hcB
                  (Conv.symm (Conv.of_red hreda.strong)) 0
              obtain ⟨πrr, hrchk⟩ := hredera.check_none
              have hrc := hrchk.closed
              have hwapp : Term.wgt (Book.price β)
                  (Term.App umm (Term.apps (.Ctr am c1) us))
                  = 1 + Term.wgt (Book.price β) umm
                    + Term.wgt (Book.price β)
                        (Term.apps (.Ctr am c1) us) := _root_.rfl
              obtain ⟨w, uw, hred, hval, hwc, hwera, hwle⟩ :=
                ih hredera hrc (by
                  rw [hwu] at hn
                  rw [hwapp]
                  omega)
              refine ⟨w, uw, ?_, hval, hwc, hwera, ?_⟩
              · refine (Red.app_f_w hredf).trans ((Red.app_a_w hreda).trans
                  ((Red.one (Step.matm ?_)).trans hred))
                exact fun hpair => hcc (congrArg Prod.snd hpair)
              · rw [hwu]
                rw [hwapp] at hwle
                omega
      · -- dead argument
        subst hueq
        have hwu : Term.wgt (Book.price β) (.App uf .Typ)
            = 1 + Term.wgt (Book.price β) uf + 1 := _root_.rfl
        obtain ⟨vf, uvf, hredf, hvalf, hvfc, hvfera, hwf⟩ :=
          ih hfera hct.1 (by rw [hwu] at hn; omega)
        cases hvalf with
        | @stuck k2 d2 args2 hk2 hgate =>
          have happ : Term.App (Term.apps (.Ref k2) args2) a
              = Term.apps (.Ref k2) (args2 ++ [a]) :=
            (Term.apps_append (.Ref k2) args2 [a]).symm
          obtain ⟨Tf, uhead, T'0, us, hheadera, hspE, hcvT', hueq3⟩ :=
            Era.apps_inv hβ (Eq.refl _) hvfera
          subst hueq3
          rcases Era.ref_inv hβ hheadera with
            ⟨d2', hk2', hbne2, hcvR, huh⟩ | ⟨A', hk2', _, _, _⟩
          rotate_left
          · exact (Book.defn_adt_clash hk2 hk2').elim
          subst huh
          rw [hk2] at hk2'
          injection hk2' with hd2eq
          subst hd2eq
          rcases hgate with hlt | hnone
          · by_cases hsat : args2.length + 1 = d2.n
            · -- the argument saturates the reference: unfold and recurse
              obtain ⟨b2, hb2⟩ : ∃ b2, d2.body = some b2 := by
                cases hbb : d2.body with
                | some b0 => exact ⟨b0, _root_.rfl⟩
                | none => exact absurd hbb hbne2
              obtain ⟨_, _, hcl⟩ := hok.defn_clauses hk2
              obtain ⟨⟨πb, hbody⟩, _⟩ := hcl b2 hb2
              obtain ⟨ub, hbera, _, _⟩ := hbody.era _root_.rfl
              have hwb : Term.wgt (Book.price β) ub
                  ≤ Term.wub (Book.price β) b2 :=
                Era.wub_le (Book.price β) hpr hbera
              have hltp : Term.wub (Book.price β) b2 < Book.price β k2 :=
                Book.price_gt β hk2 hb2 (hplain k2 d2 hk2 b2 hb2)
              have hspE2 : EraSpine β [] Tf (args2 ++ [a])
                  (Term.subst 0 a B) (us ++ [.Typ]) :=
                hspE.append (.dead hcvT' hachk .nil)
              have hredex : Era β [] (Term.apps b2 (args2 ++ [a])) T
                  (Term.apps ub (us ++ [.Typ])) :=
                Era.cnv (hspE2.era (Era.cnv hbera hcvR)) hcvT
              obtain ⟨πr, hrchk⟩ := hredex.check_none
              have hrc := hrchk.closed
              have hwr : Term.wgt (Book.price β) (Term.Ref k2)
                  = Book.price β k2 := _root_.rfl
              have hwvf := Term.wgt_apps (Book.price β) us (.Ref k2)
              rw [hwr] at hwvf
              have hwt : Term.wgt (Book.price β) Term.Typ = 1 :=
                _root_.rfl
              have hwredex := Term.wgt_apps (Book.price β) (us ++ [.Typ]) ub
              rw [List.map_append, List.sum_append, List.length_append]
                at hwredex
              simp only [List.map_cons, List.map_nil, List.sum_cons,
                List.sum_nil, List.length_cons, List.length_nil, hwt]
                at hwredex
              obtain ⟨w, uw, hred, hval, hwc, hwera, hwle⟩ :=
                ih hredex hrc (by
                  rw [hwredex]
                  rw [hwu] at hn
                  rw [hwvf] at hwf
                  omega)
              have hsp2 : Term.spine (Term.apps (.Ref k2) (args2 ++ [a]))
                  = (.Ref k2, args2 ++ [a]) :=
                Term.spine_apps (h := .Ref k2) trivial (args2 ++ [a])
              have hstep : Step β .weak (Term.apps (.Ref k2) (args2 ++ [a]))
                  (Term.apps b2 (args2 ++ [a])) := by
                have h0 := Step.dref (β := β) (p := .weak)
                  (s := Term.apps (.Ref k2) (args2 ++ [a])) hk2 hb2
                  (by rw [hsp2]) (by rw [hsp2]; simpa using hsat)
                rwa [hsp2] at h0
              refine ⟨w, uw, ?_, hval, hwc, hwera, ?_⟩
              · refine (Red.app_f_w hredf).trans ?_
                rw [happ]
                exact .step hstep hred
              · rw [hwu]
                rw [hwvf] at hwf
                rw [hwredex] at hwle
                omega
            · -- still underapplied: the spine is a stuck weak value
              refine ⟨_, _, Red.app_f_w hredf, ?_,
                ⟨hvfc, hct.2⟩, Era.cnv (Era.app_dead hvfera hachk) hcvT, ?_⟩
              · rw [happ]
                refine Term.Value.stuck hk2 (Or.inl ?_)
                simp only [List.length_append, List.length_cons,
                  List.length_nil]
                omega
              · have hwuv : Term.wgt (Book.price β)
                    (Term.App (Term.apps (.Ref k2) us) Term.Typ)
                    = 1 + Term.wgt (Book.price β) (Term.apps (.Ref k2) us)
                      + 1 := _root_.rfl
                rw [hwu, hwuv]
                omega
          · exact absurd hnone hbne2
        | typ =>
          obtain ⟨π0, hc0⟩ := hvfera.check_none
          exact absurd (Check.typ_subj_inv hβ hc0).1 Conv.typ_all
        | all =>
          obtain ⟨π0, hc0⟩ := hvfera.check_none
          exact absurd (Check.all_subj_inv hβ hc0).1 Conv.typ_all
        | eql =>
          obtain ⟨π0, hc0⟩ := hvfera.check_none
          exact absurd (Check.eql_subj_inv hβ hc0).1 Conv.typ_all
        | rfl =>
          obtain ⟨π0, hc0⟩ := hvfera.check_none
          obtain ⟨x0, y0, T00, _, hcv0, _⟩ := Check.rfl_inv hβ hc0
          exact absurd hcv0 (fun hc2 => Conv.all_eql (Conv.symm hc2))
        | efq =>
          obtain ⟨a0, A0, r0, q'0, ps0, B0, hk0, hall0, hlive0, hcv0, _⟩ :=
            Era.efq_ty_inv hβ hvfera
          obtain ⟨hq0, _, _⟩ := Conv.all_inj hcv0
          exact absurd hq0 hlive0
        | mat =>
          obtain ⟨A0, C0, r0, ps0, telF, B0, G0, q'0, umh, umm, hk0, hc00,
            hr0, hlen0, hlive0, hins0, hgoal0, hmh, hmm2, hcvM, hueqM⟩ :=
            Era.mat_inv hβ hvfera
          obtain ⟨hq0, _, _⟩ := Conv.all_inj hcvM
          exact absurd hq0 hlive0
        | lam =>
          rename_i g
          obtain ⟨q1, A1, B1, ug, hcvL, hbody, hocc, hueq2⟩ :=
            Era.lam_inv hβ hvfera
          obtain ⟨hq1, hcA, hcB⟩ := Conv.all_inj hcvL
          subst hq1
          subst hueq2
          have hocc0 : Term.occ 0 ug = 0 := by
            have := hocc (by intro hc; cases hc)
            simp only [Quant.occN] at this
            omega
          have hsub := hbody.sub_dead hβ Cut.zero
            (Check.cnv hachk (Conv.symm hcA)) hct.2 hocc0
          have hered := Era.cnv hsub (Conv.trans hβ
            (Conv.subst hβ hcB (Conv.refl a) 0) hcvT)
          obtain ⟨πr, hrchk⟩ := hered.check_none
          have hrc := hrchk.closed
          have hws := Term.wgt_subst (Book.price β) ug 0 .Typ
          rw [hocc0] at hws
          have hwlam : Term.wgt (Book.price β) (.Lam ug)
              = 1 + Term.wgt (Book.price β) ug := _root_.rfl
          rw [hwlam] at hwf
          obtain ⟨w, uw, hred, hval, hwc, hwera, hwle⟩ :=
            ih hered hrc (by rw [hwu] at hn; omega)
          refine ⟨w, uw, ?_, hval, hwc, hwera, ?_⟩
          · exact ((Red.app_f_w hredf).trans (.step .beta .refl)).trans hred
          · rw [hwu]
            omega
        | spine hsp =>
          have hframe : Era β [] (.App vf a) T (.App uvf .Typ) :=
            Era.cnv (.app_dead hvfera hachk) hcvT
          refine ⟨.App vf a, .App uvf .Typ, Red.app_f_w hredf,
            .spine (.app hsp), ⟨hvfc, hct.2⟩, hframe, ?_⟩
          show 1 + _ + 1 ≤ _
          rw [hwu]
          omega


-- METATHEORY §NO — the recursion budget's order, well-founded by hand.
--
-- A CHARGE prices one pending reference: the definition's book index,
-- a per-column size tuple — some for a column already pinned to a
-- size, none (⊤) for one still free — and a phase bit. Charges
-- compare by book index first (a definition may only call earlier
-- ones), then lexicographically on the tuple (a recursive call pins
-- or shrinks column sizes against the case-tree's descent, and
-- some < none, so any late pinning strictly drops), then by phase at
-- equal tuples (false < true: a bare δ-unfold reprices the body's
-- self-sites one phase down). The measure of a state is the MULTISET
-- of its charges; a δ-unfolding replaces one charge by finitely many
-- strictly smaller ones (Dershowitz–Manna, one step, permutation-
-- closed), and every other interaction leaves the charges alone and
-- pays with the erasure's weight — the lexicographic MMeas below.
-- ============================================================================


inductive LexR (r : α → α → Prop) : List α → List α → Prop
  | head : r a b → xs.length = ys.length → LexR r (a :: xs) (b :: ys)
  | tail : LexR r xs ys → LexR r (a :: xs) (a :: ys)

theorem LexR.length (h : LexR r xs ys) : xs.length = ys.length := by
  induction h with
  | head _ hl => simpa using hl
  | tail _ ih => simpa using ih

theorem LexR.acc_cons {r : α → α → Prop} (c : α) (l : List α)
    (hl : Acc (LexR r) l)
    (hsmall : ∀ a xs, r a c → xs.length = l.length → Acc (LexR r) (a :: xs)) :
    Acc (LexR r) (c :: l) := by
  induction hl with
  | intro z hz ihz =>
      constructor
      intro xs h
      cases h with
      | head hlt hlen => exact hsmall _ _ hlt hlen
      | tail htl =>
          exact ihz _ htl (fun a ys ha hy => hsmall a ys ha (hy.trans htl.length))

theorem LexR.acc_head {r : α → α → Prop} {n : Nat}
    (hn : ∀ l', l'.length = n → Acc (LexR r) l') :
    ∀ (c : α), Acc r c → ∀ l', l'.length = n → Acc (LexR r) (c :: l') := by
  intro c hc
  induction hc with
  | intro c _ ihc =>
      intro l' hl'
      exact LexR.acc_cons c l' (hn l' hl')
        (fun a xs ha hx => ihc a ha xs (hx.trans hl'))

theorem LexR.acc_len {r : α → α → Prop} (hwf : WellFounded r) :
    ∀ (n : Nat) (l : List α), l.length = n → Acc (LexR r) l := by
  intro n
  induction n with
  | zero =>
      intro l hl
      cases l with
      | nil =>
          constructor
          intro xs h
          cases h
      | cons c l' => simp at hl
  | succ n ihn =>
      intro l hl
      cases l with
      | nil => simp at hl
      | cons c l' =>
          have hl' : l'.length = n := by simpa using hl
          exact LexR.acc_head ihn c (hwf.apply c) l' hl'

theorem LexR.wf {r : α → α → Prop} (hwf : WellFounded r) :
    WellFounded (LexR r) :=
  ⟨fun l => LexR.acc_len hwf l.length l (Eq.refl _)⟩

def OLt : Option Nat → Option Nat → Prop
  | some a, some b => a < b
  | some _, none   => True
  | none,   _      => False

theorem OLt.acc_some : ∀ n, Acc OLt (some n) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
      constructor
      intro y hy
      cases y with
      | some m => exact ih m hy
      | none => exact absurd hy (fun h => h)

theorem OLt.wf : WellFounded OLt := by
  constructor
  intro a
  cases a with
  | some n => exact OLt.acc_some n
  | none =>
      constructor
      intro y hy
      cases y with
      | some m => exact OLt.acc_some m
      | none => exact absurd hy (fun h => h)

abbrev Charge := Nat × List (Option Nat) × Bool

abbrev TupLt : List (Option Nat) → List (Option Nat) → Prop := LexR OLt

theorem TupLt.wf : WellFounded TupLt := LexR.wf OLt.wf

def CLt (x y : Charge) : Prop :=
  x.1 < y.1 ∨ (x.1 = y.1 ∧ (TupLt x.2.1 y.2.1 ∨
    (x.2.1 = y.2.1 ∧ x.2.2 = false ∧ y.2.2 = true)))

theorem CLt.acc : ∀ (k : Nat) (t : List (Option Nat)) (p : Bool),
    Acc CLt (k, t, p) := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ihk =>
      intro t
      induction (TupLt.wf.apply t) with
      | intro t _ iht =>
          have hfalse : Acc CLt (k, t, false) := by
            constructor
            intro y hy
            rcases hy with hk | ⟨hk, ht | ⟨ht, hp, hq⟩⟩
            · exact ihk y.1 hk y.2.1 y.2.2
            · have h2 := iht y.2.1 ht y.2.2
              have he : y = (k, y.2.1, y.2.2) := by
                simp at hk
                rw [← hk]
              rw [he]
              exact h2
            · exact absurd hq (fun h => Bool.noConfusion h)
          intro p
          cases p with
          | false => exact hfalse
          | true =>
              constructor
              intro y hy
              rcases hy with hk | ⟨hk, ht | ⟨ht, hp, _⟩⟩
              · exact ihk y.1 hk y.2.1 y.2.2
              · have h2 := iht y.2.1 ht y.2.2
                have he : y = (k, y.2.1, y.2.2) := by
                  simp at hk
                  rw [← hk]
                rw [he]
                exact h2
              · have he : y = (k, t, false) := by
                  cases y with
                  | mk y1 y2 =>
                      cases y2 with
                      | mk y21 y22 =>
                          simp at hk ht hp
                          rw [hk, ht, hp]
                rw [he]
                exact hfalse

theorem CLt.wf : WellFounded CLt :=
  ⟨fun c => by
    have := CLt.acc c.1 c.2.1 c.2.2
    simpa using this⟩

inductive MStep : List Charge → List Charge → Prop
  | mk (c : Charge) (new rest : List Charge) :
      (∀ x, x ∈ new → CLt x c) →
      L.Perm (c :: rest) → L'.Perm (new ++ rest) →
      MStep L' L

theorem MStep.perm_right (h : MStep L' L) (hp : L.Perm K) : MStep L' K := by
  cases h with
  | mk c new rest hnew hL hL' =>
      exact .mk c new rest hnew (hp.symm.trans hL) hL'

theorem MStep.perm_left (h : MStep L' L) (hp : L'.Perm K') : MStep K' L := by
  cases h with
  | mk c new rest hnew hL hL' =>
      exact .mk c new rest hnew hL (hp.symm.trans hL')

theorem MStep.acc_perm (h : Acc MStep L) (hp : L.Perm K) : Acc MStep K := by
  constructor
  intro y hy
  exact h.inv (hy.perm_right hp.symm)

theorem MStep.acc_cons (hc : Acc CLt c) :
    ∀ M, Acc MStep M → Acc MStep (c :: M) := by
  induction hc with
  | intro c _ ihc =>
      intro M hM
      induction hM with
      | intro M hMpred ihM =>
          have hbatch : ∀ (new : List Charge), (∀ x, x ∈ new → CLt x c) →
              ∀ N, Acc MStep N → Acc MStep (new ++ N) := by
            intro new
            induction new with
            | nil => intro _ N hN; exact hN
            | cons x new' ihnew =>
                intro hnew N hN
                have h1 : Acc MStep (new' ++ N) :=
                  ihnew (fun z hz => hnew z (List.Mem.tail _ hz)) N hN
                exact ihc x (hnew x (List.Mem.head _)) _ h1
          constructor
          intro L' hL'
          cases hL' with
          | mk d new rest hnew hperm hperm' =>
              by_cases hdc : d = c
              · subst hdc
                have hMrest : M.Perm rest := (hperm.cons_inv)
                have hacc : Acc MStep (new ++ M) :=
                  hbatch new hnew M (Acc.intro M hMpred)
                exact MStep.acc_perm hacc
                  ((hperm'.trans (List.Perm.append_left new hMrest.symm)).symm)
              ·
                have hdM : d ∈ M := by
                  have hd1 : d ∈ c :: M := hperm.symm.mem_iff.mp (List.Mem.head _)
                  cases hd1 with
                  | head => exact absurd (Eq.refl _) hdc
                  | tail _ h => exact h
                have hMd : M.Perm (d :: M.erase d) := List.perm_cons_erase hdM
                have hswap : (c :: M).Perm (d :: c :: M.erase d) :=
                  (hMd.cons c).trans (List.Perm.swap d c (M.erase d))
                have hrest : rest.Perm (c :: M.erase d) :=
                  (hswap.symm.trans hperm).cons_inv.symm
                have hstep : MStep (new ++ M.erase d) M :=
                  .mk d new (M.erase d) hnew hMd (List.Perm.refl _)
                have hacc : Acc MStep (c :: (new ++ M.erase d)) :=
                  ihM _ hstep
                refine MStep.acc_perm hacc ?_
                exact (List.perm_middle.symm.trans
                  (List.Perm.append_left new hrest.symm)).trans hperm'.symm

theorem MStep.acc : ∀ (L : List Charge), Acc MStep L := by
  intro L
  induction L with
  | nil =>
      constructor
      intro y hy
      cases hy with
      | mk c new rest _ hperm _ =>
          have := hperm.length_eq
          simp at this
  | cons c L ih => exact MStep.acc_cons (CLt.wf.apply c) L ih

theorem MStep.wf : WellFounded MStep := ⟨MStep.acc⟩

inductive MPlus : List Charge → List Charge → Prop
  | one  : MStep L' L → MPlus L' L
  | snoc : MPlus L' K → MStep K L → MPlus L' L

theorem MPlus.perm_left (h : MPlus L' L) (hp : L'.Perm K') : MPlus K' L := by
  induction h with
  | one h1 => exact .one (h1.perm_left hp)
  | snoc _ h1 ih => exact .snoc ih h1

theorem MPlus.perm_right (h : MPlus L' L) (hp : L.Perm K) : MPlus L' K := by
  cases h with
  | one h1 => exact .one (h1.perm_right hp)
  | snoc h2 h1 => exact .snoc h2 (h1.perm_right hp)

theorem MPlus.head (h1 : MStep L' K) (h2 : MPlus K L) : MPlus L' L := by
  induction h2 with
  | one h => exact .snoc (.one h1) h
  | snoc _ h ih => exact .snoc ih h

theorem MPlus.trans (h1 : MPlus L' K) (h2 : MPlus K L) : MPlus L' L := by
  induction h2 with
  | one h => exact .snoc h1 h
  | snoc _ h ih => exact .snoc ih h

theorem MPlus.acc_self (L : List Charge) : Acc MPlus L := by
  induction MStep.acc L with
  | intro L _ ihL =>
      constructor
      intro L' h'
      cases h' with
      | one h1 => exact ihL _ h1
      | snoc h2 h1 => exact (ihL _ h1).inv h2

theorem MPlus.wf : WellFounded MPlus := ⟨MPlus.acc_self⟩

theorem MPlus.acc_perm (h : Acc MPlus L) (hp : L.Perm K) : Acc MPlus K := by
  constructor
  intro y hy
  exact h.inv (hy.perm_right hp.symm)

def MMeas (m' m : List Charge × Nat) : Prop :=
  MPlus m'.1 m.1 ∨ (m'.1.Perm m.1 ∧ m'.2 < m.2)

theorem MMeas.acc_aux (L : List Charge) :
    ∀ (n : Nat) (K : List Charge), K.Perm L → Acc MMeas (K, n) := by
  induction MPlus.acc_self L with
  | intro L _ ihL =>
      intro n
      induction n using Nat.strongRecOn with
      | _ n ihn =>
          intro K hKL
          constructor
          intro m' hm'
          cases hm' with
          | inl hp =>
              have hp' : MPlus m'.1 L := hp.perm_right hKL
              have := ihL m'.1 hp' m'.2 m'.1 (List.Perm.refl _)
              simpa using this
          | inr hpn =>
              have := ihn m'.2 hpn.2 m'.1 (hpn.1.trans hKL)
              simpa using this

theorem MMeas.wf : WellFounded MMeas := ⟨fun m => by
  have := MMeas.acc_aux m.1 m.2 m.1 (List.Perm.refl _)
  simpa using this⟩


-- ============================================================================
-- METATHEORY §L — the fold kernel. The spine and environment algebra


-- the sub-multiset order (pricing slack: a state may carry more
-- charges than its parts need), and the composite measure algebra:
-- MLe is the reflexive closure the sub-run contracts return; the
-- frame lemmas re-seat a sub-run's endpoint bound inside the
-- surrounding term's measure; MRed closes MPlus under permutation.

def Sub (A B : List Charge) : Prop := ∃ D, B.Perm (A ++ D)

theorem Sub.refl (A : List Charge) : Sub A A := ⟨[], by simp⟩

theorem Sub.perm_left (h : Sub A B) (hp : A.Perm A') : Sub A' B := by
  obtain ⟨D, hD⟩ := h
  exact ⟨D, hD.trans (hp.append_right D)⟩

theorem Sub.perm_right (h : Sub A B) (hp : B.Perm B') : Sub A B' := by
  obtain ⟨D, hD⟩ := h
  exact ⟨D, hp.symm.trans hD⟩

theorem Sub.append_right (A D : List Charge) : Sub A (A ++ D) :=
  ⟨D, List.Perm.refl _⟩

theorem Sub.append_left (A D : List Charge) : Sub A (D ++ A) :=
  ⟨D, List.perm_append_comm⟩

theorem List.perm_shuffle (A D1 A' D2 : List Charge) :
    ((A ++ D1) ++ (A' ++ D2)).Perm ((A ++ A') ++ (D1 ++ D2)) := by
  have h1 : ((A ++ D1) ++ (A' ++ D2)) = A ++ (D1 ++ (A' ++ D2)) := by
    simp [List.append_assoc]
  have h2 : ((A ++ A') ++ (D1 ++ D2)) = A ++ (A' ++ (D1 ++ D2)) := by
    simp [List.append_assoc]
  rw [h1, h2]
  refine List.Perm.append_left A ?_
  have h3 : D1 ++ (A' ++ D2) = (D1 ++ A') ++ D2 := by
    simp [List.append_assoc]
  have h4 : A' ++ (D1 ++ D2) = (A' ++ D1) ++ D2 := by
    simp [List.append_assoc]
  rw [h3, h4]
  exact (List.perm_append_comm).append_right D2

theorem Sub.trans (h1 : Sub A B) (h2 : Sub B C) : Sub A C := by
  obtain ⟨D1, hD1⟩ := h1
  obtain ⟨D2, hD2⟩ := h2
  refine ⟨D1 ++ D2, ?_⟩
  have h := hD2.trans (hD1.append_right D2)
  simpa [List.append_assoc] using h

theorem Sub.append (h1 : Sub A B) (h2 : Sub A' B') :
    Sub (A ++ A') (B ++ B') := by
  obtain ⟨D1, hD1⟩ := h1
  obtain ⟨D2, hD2⟩ := h2
  exact ⟨D1 ++ D2, (hD1.append hD2).trans (List.perm_shuffle A D1 A' D2)⟩

theorem Sub.mplus_or_perm (h : Sub A B) :
    MPlus A B ∨ A.Perm B := by
  obtain ⟨D, hD⟩ := h
  induction D generalizing B with
  | nil =>
      right
      exact (hD.trans (by simp)).symm
  | cons c D ih =>
      left
      have hstep : MStep (A ++ D) B := by
        refine MStep.mk c [] (A ++ D) (fun x hx => nomatch hx) ?_ ?_
        · exact hD.trans List.perm_middle
        · simp
      rcases ih (B := A ++ D) (List.Perm.refl _) with hmp | hperm
      · exact hmp.snoc hstep
      · exact .one (hstep.perm_left hperm.symm)

theorem MStep.append (h : MStep L' L) (D : List Charge) :
    MStep (L' ++ D) (L ++ D) := by
  cases h with
  | mk c new rest hnew hL hL' =>
      refine MStep.mk c new (rest ++ D) hnew ?_ ?_
      · exact hL.append_right D
      · have := hL'.append_right D
        rwa [List.append_assoc] at this

theorem MPlus.append (h : MPlus L' L) (D : List Charge) :
    MPlus (L' ++ D) (L ++ D) := by
  induction h with
  | one h1 => exact .one (h1.append D)
  | snoc _ h1 ih => exact ih.snoc (h1.append D)

def MLe (m' m : List Charge × Nat) : Prop :=
  MMeas m' m ∨ (m'.1.Perm m.1 ∧ m'.2 = m.2)

theorem MLe.refl (m : List Charge × Nat) : MLe m m :=
  Or.inr ⟨List.Perm.refl _, Eq.refl _⟩

theorem MMeas.perm_left (h : MMeas m' m) (hp : m'.1.Perm K) (hw : m'.2 = w) :
    MMeas (K, w) m := by
  cases h with
  | inl hplus => exact Or.inl (hplus.perm_left hp)
  | inr hpw => exact Or.inr ⟨hp.symm.trans hpw.1, hw ▸ hpw.2⟩

theorem MMeas.perm_right (h : MMeas m' m) (hp : m.1.Perm K) (hw : m.2 = w) :
    MMeas m' (K, w) := by
  cases h with
  | inl hplus => exact Or.inl (hplus.perm_right hp)
  | inr hpw => exact Or.inr ⟨hpw.1.trans hp, hw ▸ hpw.2⟩

theorem MMeas.trans_le (h1 : MMeas m2 m1) (h2 : MLe m3 m2) : MMeas m3 m1 := by
  cases h2 with
  | inl h3 =>
      cases h3 with
      | inl hp3 =>
          cases h1 with
          | inl hp1 => exact Or.inl (hp3.trans hp1)
          | inr hpw1 => exact Or.inl ((hp3.perm_right hpw1.1))
      | inr hpw3 =>
          cases h1 with
          | inl hp1 => exact Or.inl (hp1.perm_left hpw3.1.symm)
          | inr hpw1 => exact Or.inr ⟨hpw3.1.trans hpw1.1, by omega⟩
  | inr hpw3 =>
      cases h1 with
      | inl hp1 => exact Or.inl (hp1.perm_left hpw3.1.symm)
      | inr hpw1 => exact Or.inr ⟨hpw3.1.trans hpw1.1, by omega⟩

theorem MMeas.after_le (h1 : MLe m2 m1) (h2 : MMeas m3 m2) : MMeas m3 m1 := by
  cases h1 with
  | inl h1' =>
      cases h2 with
      | inl hp3 =>
          cases h1' with
          | inl hp1 => exact Or.inl (hp3.trans hp1)
          | inr hpw1 => exact Or.inl (hp3.perm_right hpw1.1)
      | inr hpw3 =>
          cases h1' with
          | inl hp1 => exact Or.inl (hp1.perm_left hpw3.1.symm)
          | inr hpw1 => exact Or.inr ⟨hpw3.1.trans hpw1.1, by omega⟩
  | inr hpw1 =>
      cases h2 with
      | inl hp3 => exact Or.inl (hp3.perm_right hpw1.1)
      | inr hpw3 => exact Or.inr ⟨hpw3.1.trans hpw1.1, by omega⟩

theorem MLe.trans_meas (h1 : MMeas m2 m1) (h2 : MLe m3 m2) : MLe m3 m1 :=
  Or.inl (h1.trans_le h2)

theorem MLe.trans (h1 : MLe m2 m1) (h2 : MLe m3 m2) : MLe m3 m1 := by
  cases h1 with
  | inl h1' => exact Or.inl (h1'.trans_le h2)
  | inr hpw1 =>
      cases h2 with
      | inl h2' =>
          exact Or.inl (h2'.perm_right hpw1.1 (by omega))
      | inr hpw2 =>
          exact Or.inr ⟨hpw2.1.trans hpw1.1, by omega⟩

theorem MLe.of_sub (h : Sub A B) (hw : w' ≤ w) : MLe (A, w') (B, w) := by
  rcases h.mplus_or_perm with hp | hperm
  · exact Or.inl (Or.inl hp)
  · by_cases he : w' = w
    · exact Or.inr ⟨hperm, he⟩
    · exact Or.inl (Or.inr ⟨hperm, by omega⟩)

theorem MLe.frame (D : List Charge) (K : Nat)
    (h : MLe (A', w') (A, w)) : MLe (D ++ A', K + w') (D ++ A, K + w) := by
  cases h with
  | inl hm =>
      cases hm with
      | inl hp =>
          refine Or.inl (Or.inl ?_)
          have := hp.append D
          have hc : ∀ X, D ++ X = ([] : List Charge) ++ (X ++ D) ∨ True := by
            intro X; exact Or.inr trivial
          exact ((this.perm_left List.perm_append_comm).perm_right
            List.perm_append_comm)
      | inr hpw =>
          exact Or.inl (Or.inr ⟨hpw.1.append_left D, by omega⟩)
  | inr hpw =>
      exact Or.inr ⟨hpw.1.append_left D, by omega⟩

theorem MMeas.frame (D : List Charge) (K : Nat)
    (h : MMeas (A', w') (A, w)) : MMeas (D ++ A', K + w') (D ++ A, K + w) := by
  cases h with
  | inl hp =>
      refine Or.inl ?_
      exact ((hp.append D).perm_left List.perm_append_comm).perm_right
        List.perm_append_comm
  | inr hpw =>
      exact Or.inr ⟨hpw.1.append_left D, by omega⟩

theorem MLe.frame_left (D : List Charge) (K : Nat)
    (h : MLe (A', w') (A, w)) : MLe (A' ++ D, w' + K) (A ++ D, w + K) := by
  have h1 := MLe.frame D K h
  cases h1 with
  | inl hm =>
      refine Or.inl ?_
      cases hm with
      | inl hp =>
          exact Or.inl ((hp.perm_left List.perm_append_comm).perm_right
            List.perm_append_comm)
      | inr hpw =>
          exact Or.inr ⟨(List.perm_append_comm.trans hpw.1).trans
            List.perm_append_comm, by omega⟩
  | inr hpw =>
      exact Or.inr ⟨(List.perm_append_comm.trans hpw.1).trans
        List.perm_append_comm, by omega⟩

def MRed (A B : List Charge) : Prop := MPlus A B ∨ A.Perm B

theorem MRed.refl (A : List Charge) : MRed A A := Or.inr (List.Perm.refl _)

theorem MRed.of_sub (h : Sub A B) : MRed A B := h.mplus_or_perm


theorem MRed.trans (h1 : MRed A B) (h2 : MRed B C) : MRed A C := by
  cases h1 with
  | inl hp1 =>
      cases h2 with
      | inl hp2 => exact Or.inl (hp1.trans hp2)
      | inr hq2 => exact Or.inl (hp1.perm_right hq2)
  | inr hq1 =>
      cases h2 with
      | inl hp2 => exact Or.inl (hp2.perm_left hq1.symm)
      | inr hq2 => exact Or.inr (hq1.trans hq2)

theorem MRed.append (h : MRed A B) (D : List Charge) :
    MRed (A ++ D) (B ++ D) := by
  cases h with
  | inl hp => exact Or.inl (hp.append D)
  | inr hq => exact Or.inr (hq.append_right D)

theorem MPlus.of_step_mred (h1 : MStep A B) (h2 : MRed B C) : MPlus A C := by
  cases h2 with
  | inl hp => exact MPlus.head h1 hp
  | inr hq => exact .one (h1.perm_right hq)


-- ============================================================================
-- METATHEORY §NS — the descent size. Term.csize counts the constructor
-- skeleton of a value along its declared FIELDS (the last C.fn spine
-- arguments — erased parameters are skipped, exactly as the §7
-- comparison skips them), so a column pattern (fields only) and a
-- runtime argument (parameters then fields) measure the same skeleton.
-- Closed values are shift/subst-transparent, so a pinned size never
-- moves. Term.msubst is the drive's environment: closed values
-- substituted for the binders one at a time, exactly as the betas fire.
-- ============================================================================



theorem mem_of_mem_drop : ∀ (n : Nat) (l : List α), ∀ x ∈ l.drop n, x ∈ l := by
  intro n
  induction n with
  | zero => intro l x hx; exact hx
  | succ n ih =>
    intro l x hx
    cases l with
    | nil => exact hx
    | cons y l => exact List.mem_cons_of_mem y (ih l x hx)

def Term.csize (β : Book) (t : Term) : Nat :=
  match (Term.spine t).1 with
  | .Ctr a c =>
    match Book.adt β a with
    | some A =>
      match AdtD.ctr A c with
      | some C =>
        let as := (Term.spine t).2
        1 + ((as.drop (as.length - C.fn)).attach.map
              (fun x => Term.csize β x.1)).sum
      | none => 0
    | none => 0
  | _ => 0
termination_by Term.size t
decreasing_by
  exact Term.size_spine_arg t x.1
    (mem_of_mem_drop _ _ x.1 x.2)

theorem attach_map_sum (l : List α) (f : α → Nat) :
    (l.attach.map (fun x => f x.1)).sum = (l.map f).sum := by
  rw [List.attach_map_val]

theorem Term.csize_ctr (hk : Book.adt β a = some A) (hc : AdtD.ctr A c = some C)
    (as : List Term) (hlen : as.length = A.pn + C.fn) :
    Term.csize β (Term.apps (.Ctr a c) as)
      = 1 + ((as.drop A.pn).map (Term.csize β)).sum := by
  rw [Term.csize]
  rw [Term.spine_apps (by trivial)]
  simp only [hk, hc]
  rw [show as.length - C.fn = A.pn from by omega]
  rw [attach_map_sum]

theorem Term.csize_fields (hk : Book.adt β a = some A)
    (hc : AdtD.ctr A c = some C) (ys : List Term) (hlen : ys.length = C.fn) :
    Term.csize β (Term.apps (.Ctr a c) ys)
      = 1 + (ys.map (Term.csize β)).sum := by
  rw [Term.csize]
  rw [Term.spine_apps (by trivial)]
  simp only [hk, hc]
  rw [show ys.length - C.fn = 0 from by omega]
  rw [attach_map_sum, List.drop_zero]

-- the drive environment: closed values consumed binder by binder
def Term.msubst : List Term → Term → Term
  | [],      t => t
  | v :: vs, t => Term.msubst vs (Term.subst 0 v t)




theorem Term.msubstAt_typ (d : Nat) : ∀ (vs : List Term),
    Term.msubstAt d vs .Typ = .Typ := by
  intro vs
  induction vs with
  | nil => rfl
  | cons v vs ih => exact ih

theorem Term.msubstAt_app (d : Nat) : ∀ (vs : List Term) (f a : Term),
    Term.msubstAt d vs (.App f a)
      = .App (Term.msubstAt d vs f) (Term.msubstAt d vs a) := by
  intro vs
  induction vs with
  | nil => intro f a; rfl
  | cons v vs ih => intro f a; exact ih _ _

theorem Term.msubstAt_apps (d : Nat) (vs : List Term) :
    ∀ (xs : List Term) (f : Term),
    Term.msubstAt d vs (Term.apps f xs)
      = Term.apps (Term.msubstAt d vs f) (xs.map (Term.msubstAt d vs)) := by
  intro xs
  induction xs with
  | nil => intro f; rfl
  | cons x xs ih =>
    intro f
    show Term.msubstAt d vs (Term.apps (.App f x) xs) = _
    rw [ih (.App f x), Term.msubstAt_app]
    rfl

theorem Term.msubstAt_ref (d : Nat) (k : Nat) : ∀ (vs : List Term),
    Term.msubstAt d vs (.Ref k) = .Ref k := by
  intro vs
  induction vs with
  | nil => rfl
  | cons v vs ih => exact ih

theorem Term.msubstAt_ctr (d : Nat) (a c : Nat) : ∀ (vs : List Term),
    Term.msubstAt d vs (.Ctr a c) = .Ctr a c := by
  intro vs
  induction vs with
  | nil => rfl
  | cons v vs ih => exact ih

theorem Term.msubstAt_lam (d : Nat) : ∀ (vs : List Term), (∀ v ∈ vs, v.Closed 0) →
    ∀ (f : Term), Term.msubstAt d vs (.Lam f)
      = .Lam (Term.msubstAt (d + 1) vs f) := by
  intro vs
  induction vs with
  | nil => intro _ f; rfl
  | cons v vs ih =>
    intro hcl f
    show Term.msubstAt d vs (Term.subst d v (.Lam f)) = _
    simp only [Term.subst]
    rw [Term.shift_closed v 0 0 (hcl v List.mem_cons_self) (Nat.le_refl 0)]
    exact ih (fun v' hv' => hcl v' (List.mem_cons_of_mem v hv')) _

theorem Term.msubstAt_rwt (d : Nat) : ∀ (vs : List Term) (e P f : Term),
    Term.msubstAt d vs (.Rwt e P f)
      = .Rwt (Term.msubstAt d vs e) (Term.msubstAt d vs P)
          (Term.msubstAt d vs f) := by
  intro vs
  induction vs with
  | nil => intro e P f; rfl
  | cons v vs ih => intro e P f; exact ih _ _ _

theorem Term.msubstAt_mat (d : Nat) : ∀ (vs : List Term) (a c : Nat)
    (h m : Term),
    Term.msubstAt d vs (.Mat a c h m)
      = .Mat a c (Term.msubstAt d vs h) (Term.msubstAt d vs m) := by
  intro vs
  induction vs with
  | nil => intro a c h m; rfl
  | cons v vs ih => intro a c h m; exact ih _ _ _ _

theorem Term.msubstAt_let (d : Nat) : ∀ (vs : List Term),
    (∀ v ∈ vs, v.Closed 0) → ∀ (q : Quant) (v0 b : Term),
    Term.msubstAt d vs (.Let q v0 b)
      = .Let q (Term.msubstAt d vs v0) (Term.msubstAt (d + 1) vs b) := by
  intro vs
  induction vs with
  | nil => intro _ q v0 b; rfl
  | cons v vs ih =>
    intro hcl q v0 b
    show Term.msubstAt d vs (Term.subst d v (.Let q v0 b)) = _
    simp only [Term.subst]
    rw [Term.shift_closed v 0 0 (hcl v List.mem_cons_self) (Nat.le_refl 0)]
    exact ih (fun v' hv' => hcl v' (List.mem_cons_of_mem v hv')) _ _ _

theorem Term.msubstAt_closed (d : Nat) : ∀ (vs : List Term) (t : Term),
    t.Closed 0 → Term.msubstAt d vs t = t := by
  intro vs
  induction vs with
  | nil => intro t _; rfl
  | cons v vs ih =>
    intro t ht
    show Term.msubstAt d vs (Term.subst d v t) = t
    rw [Term.subst_closed t 0 d v ht (Nat.zero_le d)]
    exact ih t ht

theorem Term.msubstAt_shift (d : Nat) : ∀ (vs : List Term),
    (∀ v ∈ vs, v.Closed 0) → ∀ (t : Term),
    Term.msubstAt (d + 1) vs (Term.shift 0 t)
      = Term.shift 0 (Term.msubstAt d vs t) := by
  intro vs
  induction vs with
  | nil => intro _ t; rfl
  | cons v vs ih =>
    intro hcl t
    show Term.msubstAt (d + 1) vs (Term.subst (d + 1) v (Term.shift 0 t)) = _
    have h := Term.shift_subst_lt t 0 d v (Nat.zero_le d)
    rw [Term.shift_closed v 0 0 (hcl v List.mem_cons_self) (Nat.le_refl 0)] at h
    rw [← h]
    exact ih (fun v' hv' => hcl v' (List.mem_cons_of_mem v hv')) _

theorem Term.msubstAt_var_lt (d : Nat) (i : Nat) (hi : i < d) :
    ∀ (vs : List Term), Term.msubstAt d vs (.Var i) = .Var i := by
  intro vs
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    show Term.msubstAt d vs (Term.subst d v (.Var i)) = _
    simp only [Term.subst]
    rw [if_neg (by omega), if_neg (by omega)]
    exact ih

theorem Term.msubstAt_var_hit (d : Nat) :
    ∀ (vs : List Term), (∀ v ∈ vs, v.Closed 0) →
    ∀ (j : Nat), j < vs.length →
    Term.msubstAt d vs (.Var (d + j)) = vs.getD j .Typ := by
  intro vs
  induction vs with
  | nil =>
    intro _ j hj
    exact absurd hj (by simp)
  | cons v vs ih =>
    intro hcl j hj
    cases j with
    | zero =>
      show Term.msubstAt d vs (Term.subst d v (.Var (d + 0))) = v
      rw [Nat.add_zero]
      simp only [Term.subst]
      simp only [if_true]
      exact Term.msubstAt_closed d vs v (hcl v List.mem_cons_self)
    | succ j =>
      show Term.msubstAt d vs (Term.subst d v (.Var (d + (j + 1)))) = _
      simp only [Term.subst]
      rw [if_neg (show ¬ (d + (j + 1) = d) from by omega),
        if_pos (show d < d + (j + 1) from by omega)]
      have h := ih (fun v' hv' => hcl v' (List.mem_cons_of_mem v hv')) j
        (by simp only [List.length_cons] at hj; omega)
      rw [show d + (j + 1) - 1 = d + j from by omega]
      exact h

theorem Term.msubstAt_var_ge (d : Nat) : ∀ (vs : List Term) (i : Nat),
    d + vs.length ≤ i →
    Term.msubstAt d vs (.Var i) = .Var (i - vs.length) := by
  intro vs
  induction vs with
  | nil =>
    intro i _
    simp only [List.length_nil, Nat.sub_zero]
    rfl
  | cons v vs ih =>
    intro i hi
    simp only [List.length_cons] at hi
    show Term.msubstAt d vs (Term.subst d v (.Var i)) = _
    simp only [Term.subst]
    rw [if_neg (show ¬ (i = d) from by omega),
      if_pos (show d < i from by omega)]
    rw [ih (i - 1) (by omega)]
    simp only [List.length_cons]
    congr 1
    omega

-- slot-wise sub-multisets flatten to a sub-multiset
theorem Term.msubstAt_cons (d : Nat) (v : Term) (hv : v.Closed 0) :
    ∀ (env : List Term), (∀ w ∈ env, w.Closed 0) → ∀ (f : Term),
    Term.msubstAt d (v :: env) f
      = Term.subst d v (Term.msubstAt (d + 1) env f) := by
  intro env
  induction env with
  | nil => intro _ f; rfl
  | cons w env ih =>
    intro hcl f
    show Term.msubstAt d env (Term.subst d w (Term.subst d v f)) = _
    have hcomm : Term.subst d w (Term.subst d v f)
        = Term.subst d v (Term.subst (d + 1) w f) := by
      have h := Term.subst_subst f d d w v (Nat.le_refl d)
      rw [Term.subst_closed v 0 d w hv (Nat.zero_le d)] at h
      rw [Term.shift_closed w 0 d (hcl w List.mem_cons_self)
        (Nat.zero_le d)] at h
      exact h
    rw [hcomm]
    show Term.msubstAt d (v :: env) (Term.subst (d + 1) w f) = _
    rw [ih (fun w' hw' => hcl w' (List.mem_cons_of_mem w hw')) _]
    rfl

theorem Term.subst_var_shift : ∀ (t : Term) (d : Nat),
    Term.subst d (.Var d) (Term.shift (d + 1) t) = t := by
  intro t
  induction t <;> intro d <;>
    simp only [Term.shift, Term.subst] <;>
    try rw [show Term.shift 0 (Term.Var d) = .Var (d + 1) from by
      simp [Term.shift]]
  case Var i =>
    by_cases h1 : i < d + 1
    · rw [if_pos h1]
      simp only [Term.subst]
      by_cases h2 : i = d
      · rw [if_pos h2, h2]
      · rw [if_neg h2, if_neg (by omega)]
    · rw [if_neg h1]
      simp only [Term.subst]
      rw [if_neg (by omega), if_pos (by omega)]
      simp
  case All q A B ihA ihB =>
    rw [if_neg (Nat.not_lt_zero d)]
    rw [ihA d, ihB (d + 1)]
  case Lam f ihf =>
    rw [if_neg (Nat.not_lt_zero d)]
    rw [ihf (d + 1)]
  case App f a ihf iha => rw [ihf d, iha d]
  case Mat a c h m ihh ihm => rw [ihh d, ihm d]
  case Eql x y T ihx ihy ihT => rw [ihx d, ihy d, ihT d]
  case Rwt e P f ihe ihP ihf => rw [ihe d, ihP d, ihf d]
  case Let q v b ihv ihb =>
    rw [if_neg (Nat.not_lt_zero d)]
    rw [ihv d, ihb (d + 1)]



-- the drive's application fold
def Term.applyBs : Term → List Term → Term
  | t, []      => t
  | t, v :: vs => Term.applyBs (Term.applyB t v) vs


-- instantiation tracks the lhs algebra: consuming a binder is applyB
-- of the consumed value on the instantiated side
theorem Term.applyB_not_lam (t v : Term) (h : ∀ L, t ≠ .Lam L) :
    Term.applyB t v = .App t v := by
  cases t <;> first
  | rfl
  | exact absurd _root_.rfl (h _)

theorem Term.shift_not_lam (t : Term) (d : Nat) (h : ∀ L, t ≠ .Lam L) :
    ∀ L, Term.shift d t ≠ .Lam L := by
  cases t <;> intro L hc <;> first
  | exact Term.noConfusion hc
  | exact absurd _root_.rfl (h _)
  | (simp only [Term.shift] at hc
     first
     | exact Term.noConfusion hc
     | (split at hc <;> exact Term.noConfusion hc))

theorem Term.msubstAt_applyB (v : Term) (hv : v.Closed 0)
    (env : List Term) (henv : ∀ w ∈ env, w.Closed 0) (lhs : Term)
    (hsh : (∃ L, lhs = .Lam L) ∨ ((∀ L, lhs ≠ .Lam L) ∧
      (∀ L, Term.msubstAt 0 env lhs ≠ .Lam L))) :
    Term.msubstAt 0 (v :: env) (Term.applyB (Term.shift 0 lhs) (.Var 0))
      = Term.applyB (Term.msubstAt 0 env lhs) v := by
  rcases hsh with ⟨L, rfl⟩ | ⟨h1, h2⟩
  · show Term.msubstAt 0 (v :: env)
      (Term.applyB (.Lam (Term.shift 1 L)) (.Var 0)) = _
    show Term.msubstAt 0 (v :: env) (Term.subst 0 (.Var 0) (Term.shift 1 L))
      = _
    rw [show Term.shift 1 L = Term.shift (0 + 1) L from _root_.rfl,
      Term.subst_var_shift L 0]
    rw [Term.msubstAt_lam 0 env henv]
    show _ = Term.subst 0 v (Term.msubstAt (0 + 1) env L)
    exact Term.msubstAt_cons 0 v hv env henv L
  · rw [Term.applyB_not_lam _ _ (Term.shift_not_lam lhs 0 h1)]
    rw [Term.msubstAt_app]
    rw [Term.applyB_not_lam _ _ h2]
    congr 1
    · show Term.msubstAt 0 env (Term.subst 0 v (Term.shift 0 lhs)) = _
      rw [Term.subst_shift lhs 0 v]
    · show Term.msubstAt 0 env (Term.subst 0 v (.Var 0)) = v
      simp only [Term.subst, if_true]
      exact Term.msubstAt_closed 0 env v hv



theorem Sub.flatten : ∀ {As Bs : List (List Charge)},
    As.length = Bs.length →
    (∀ i, i < As.length → Sub (As.getD i []) (Bs.getD i [])) →
    Sub As.flatten Bs.flatten := by
  intro As
  induction As with
  | nil =>
    intro Bs hlen _
    cases Bs with
    | nil => exact Sub.refl _
    | cons _ _ => exact absurd hlen (by simp)
  | cons A As ih =>
    intro Bs hlen hall
    cases Bs with
    | nil => exact absurd hlen (by simp)
    | cons B Bs =>
      show Sub (A ++ As.flatten) (B ++ Bs.flatten)
      refine Sub.append (hall 0 (by simp)) ?_
      refine ih (by simp only [List.length_cons] at hlen; omega) ?_
      intro i hi
      exact hall (i + 1) (by simp only [List.length_cons]; omega)

-- lifting a pointwise fact over a mapped zip of charge lists and pairs
theorem zip_zip_map_mem {R : List Charge → Term → Term → Prop}
    (F G : Term → Term) :
    ∀ (Css : List (List Charge)) (xs us : List Term),
    (∀ p ∈ (Css.zip xs).zip us, R p.1.1 (F p.1.2) (G p.2)) →
    ∀ p ∈ (Css.zip (xs.map F)).zip (us.map G), R p.1.1 p.1.2 p.2 := by
  intro Css
  induction Css with
  | nil => intro xs us _ p hp; exact nomatch hp
  | cons Cs Css ih =>
    intro xs us h p hp
    cases xs with
    | nil => exact nomatch hp
    | cons x xs =>
      cases us with
      | nil => exact nomatch hp
      | cons u us =>
        simp only [List.map, List.zip_cons_cons] at hp
        rcases List.mem_cons.mp hp with h1 | h2
        · subst h1
          exact h ((Cs, x), u) (List.mem_cons_self)
        · exact ih xs us
            (fun p' hp' => h p' (List.mem_cons_of_mem _ hp')) p h2

theorem map_closed_id : ∀ (l : List Term), (∀ v ∈ l, v.Closed 0) →
    ∀ (F : Term → Term), (∀ t : Term, t.Closed 0 → F t = t) →
    l.map F = l := by
  intro l
  induction l with
  | nil => intro _ F _; rfl
  | cons x xs ih =>
    intro hcl F hF
    simp only [List.map]
    rw [hF x (hcl x List.mem_cons_self),
      ih (fun v hv => hcl v (List.mem_cons_of_mem x hv)) F hF]




theorem mem_le_sum (f : α → Nat) : ∀ (l : List α) (x : α), x ∈ l →
    f x ≤ (l.map f).sum := by
  intro l
  induction l with
  | nil => intro x hx; exact nomatch hx
  | cons y l ih =>
    intro x hx
    rcases List.mem_cons.mp hx with h1 | h2
    · subst h1
      simp only [List.map, List.sum_cons]
      omega
    · have := ih x h2
      simp only [List.map, List.sum_cons]
      omega

-- the comparison is sound for the size: under ANY environment, a
-- PEq-matched argument measures exactly its pattern, and a PLt
-- argument measures strictly below it. The var case is free (both
-- sides are the SAME variable), so nothing is assumed of the
-- environment — higher-order values ride along untouched.
theorem PEqs.map_length : ∀ {xs ys : List Term}, PEqs β xs ys →
    xs.length = ys.length := by
  intro xs
  induction xs with
  | nil => intro ys h; cases h; rfl
  | cons x xs ih =>
    intro ys h
    cases h with
    | cons _ hrest => simpa using ih hrest

theorem PLes.map_length : ∀ {xs ys : List Term}, PLes β xs ys →
    xs.length = ys.length := by
  intro xs
  induction xs with
  | nil => intro ys h; cases h; rfl
  | cons x xs ih =>
    intro ys h
    cases h with
    | consEq _ hrest => simpa using ih hrest
    | consLt _ hrest => simpa using ih hrest

theorem PLts.map_length : ∀ {xs ys : List Term}, PLts β xs ys →
    xs.length = ys.length := by
  intro xs
  induction xs with
  | nil => intro ys h; cases h
  | cons x xs ih =>
    intro ys h
    cases h with
    | here _ hles => simpa using hles.map_length
    | there _ hrest => simpa using ih hrest

theorem PEqs.csize_sum : ∀ {xs ys : List Term}, PEqs β xs ys →
    (∀ y ∈ ys, ∀ t, PEq β t y → ∀ dd env,
      Term.csize β (Term.msubstAt dd env t) = Term.csize β (Term.msubstAt dd env y)) →
    ∀ (dd : Nat) (env : List Term), ((xs.map (Term.msubstAt dd env)).map (Term.csize β)).sum
      = ((ys.map (Term.msubstAt dd env)).map (Term.csize β)).sum := by
  intro xs
  induction xs with
  | nil =>
    intro ys h hIH dd env
    cases h
    rfl
  | cons x xs ih =>
    intro ys h hIH dd env
    cases h with
    | @cons _ y _ ys' hxy hrest =>
      have h1 := hIH y (List.mem_cons_self) x hxy dd env
      have h2 := ih hrest
        (fun y' hy' => hIH y' (List.mem_cons_of_mem y hy')) dd env
      simp only [List.map, List.sum_cons]
      omega

theorem PLes.csize_sum : ∀ {xs ys : List Term}, PLes β xs ys →
    (∀ y ∈ ys, ∀ t, PEq β t y → ∀ dd env,
      Term.csize β (Term.msubstAt dd env t) = Term.csize β (Term.msubstAt dd env y)) →
    (∀ y ∈ ys, ∀ t, PLt β t y → ∀ dd env,
      Term.csize β (Term.msubstAt dd env t) < Term.csize β (Term.msubstAt dd env y)) →
    ∀ (dd : Nat) (env : List Term), ((xs.map (Term.msubstAt dd env)).map (Term.csize β)).sum
      ≤ ((ys.map (Term.msubstAt dd env)).map (Term.csize β)).sum := by
  intro xs
  induction xs with
  | nil =>
    intro ys h hIHe hIHl dd env
    cases h
    exact Nat.le_refl _
  | cons x xs ih =>
    intro ys h hIHe hIHl dd env
    cases h with
    | @consEq _ y _ ys' hxy hrest =>
      have h1 := hIHe y (List.mem_cons_self) x hxy dd env
      have h2 := ih hrest
        (fun y' hy' => hIHe y' (List.mem_cons_of_mem y hy'))
        (fun y' hy' => hIHl y' (List.mem_cons_of_mem y hy')) dd env
      simp only [List.map, List.sum_cons]
      omega
    | @consLt _ y _ ys' hxy hrest =>
      have h1 := hIHl y (List.mem_cons_self) x hxy dd env
      have h2 := ih hrest
        (fun y' hy' => hIHe y' (List.mem_cons_of_mem y hy'))
        (fun y' hy' => hIHl y' (List.mem_cons_of_mem y hy')) dd env
      simp only [List.map, List.sum_cons]
      omega

theorem PLts.csize_sum : ∀ {xs ys : List Term}, PLts β xs ys →
    (∀ y ∈ ys, ∀ t, PEq β t y → ∀ dd env,
      Term.csize β (Term.msubstAt dd env t) = Term.csize β (Term.msubstAt dd env y)) →
    (∀ y ∈ ys, ∀ t, PLt β t y → ∀ dd env,
      Term.csize β (Term.msubstAt dd env t) < Term.csize β (Term.msubstAt dd env y)) →
    ∀ (dd : Nat) (env : List Term), ((xs.map (Term.msubstAt dd env)).map (Term.csize β)).sum
      < ((ys.map (Term.msubstAt dd env)).map (Term.csize β)).sum := by
  intro xs
  induction xs with
  | nil => intro ys h hIHe hIHl dd env; cases h
  | cons x xs ih =>
    intro ys h hIHe hIHl dd env
    cases h with
    | @here _ y _ ys' hxy hrest =>
      have h1 := hIHl y (List.mem_cons_self) x hxy dd env
      have h2 := hrest.csize_sum
        (fun y' hy' => hIHe y' (List.mem_cons_of_mem y hy'))
        (fun y' hy' => hIHl y' (List.mem_cons_of_mem y hy')) dd env
      simp only [List.map, List.sum_cons]
      omega
    | @there _ y _ ys' hxy hrest =>
      have h1 := hIHe y (List.mem_cons_self) x hxy dd env
      have h2 := ih hrest
        (fun y' hy' => hIHe y' (List.mem_cons_of_mem y hy'))
        (fun y' hy' => hIHl y' (List.mem_cons_of_mem y hy')) dd env
      simp only [List.map, List.sum_cons]
      omega

theorem descent_csize (β : Book) :
    ∀ (n : Nat) (p : Term), Term.size p ≤ n →
      (∀ t, PEq β t p → ∀ dd env,
        Term.csize β (Term.msubstAt dd env t) = Term.csize β (Term.msubstAt dd env p)) ∧
      (∀ t, PLt β t p → ∀ dd env,
        Term.csize β (Term.msubstAt dd env t) < Term.csize β (Term.msubstAt dd env p)) := by
  intro n
  induction n with
  | zero =>
    intro p hp
    have := Term.size_pos p
    omega
  | succ n ih =>
    intro p hp
    have helem : ∀ {a c : Nat} {ys : List Term},
        p = Term.apps (.Ctr a c) ys → ∀ y ∈ ys, Term.size y ≤ n := by
      intro a c ys hpe y hy
      have hsp : y ∈ (Term.spine p).2 := by
        rw [hpe, Term.spine_apps (by trivial)]
        exact hy
      have := Term.size_spine_arg p y hsp
      omega
    constructor
    · intro t hpe dd env
      cases hpe with
      | var => rfl
      | @ctr a A c C xs ys ps hk hc hlp hlx hpes =>
        have hIH : ∀ y ∈ ys, ∀ t', PEq β t' y → ∀ dd' env',
            Term.csize β (Term.msubstAt dd' env' t')
              = Term.csize β (Term.msubstAt dd' env' y) :=
          fun y hy t' ht' dd' env' =>
            ((ih y (helem (Eq.refl _) y hy)).1 t' ht') dd' env'
        rw [Term.msubstAt_apps, Term.msubstAt_apps, Term.msubstAt_ctr]
        rw [Term.csize_ctr hk hc _ (by
          simp only [List.length_map, List.length_append]
          omega)]
        rw [Term.csize_fields hk hc _ (by
          simp only [List.length_map]
          rw [← hpes.map_length]
          omega)]
        rw [List.map_append]
        rw [show A.pn = (ps.map (Term.msubstAt dd env)).length from by
          simp only [List.length_map]
          omega]
        rw [List.drop_left]
        rw [hpes.csize_sum hIH dd env]
    · intro t hpl dd env
      cases hpl with
      | @subEq a A c C ys y _t hk hc hly hy hpe =>
        have h1 := ((ih y (helem (Eq.refl _) y hy)).1 t hpe) dd env
        rw [Term.msubstAt_apps, Term.msubstAt_ctr]
        rw [Term.csize_fields hk hc _ (by
          simp only [List.length_map]
          omega)]
        have h2 : Term.csize β (Term.msubstAt dd env y)
            ≤ ((ys.map (Term.msubstAt dd env)).map (Term.csize β)).sum := by
          have := mem_le_sum (Term.csize β) (ys.map (Term.msubstAt dd env))
            (Term.msubstAt dd env y) (List.mem_map_of_mem hy)
          omega
        omega
      | @subLt a A c C ys y _t hk hc hly hy hpl2 =>
        have h1 := ((ih y (helem (Eq.refl _) y hy)).2 t hpl2) dd env
        rw [Term.msubstAt_apps, Term.msubstAt_ctr]
        rw [Term.csize_fields hk hc _ (by
          simp only [List.length_map]
          omega)]
        have h2 : Term.csize β (Term.msubstAt dd env y)
            ≤ ((ys.map (Term.msubstAt dd env)).map (Term.csize β)).sum := by
          have := mem_le_sum (Term.csize β) (ys.map (Term.msubstAt dd env))
            (Term.msubstAt dd env y) (List.mem_map_of_mem hy)
          omega
        omega
      | @ctr a A c C xs ys ps hk hc hlp hlx hplts =>
        have hIHe : ∀ y ∈ ys, ∀ t', PEq β t' y → ∀ dd' env',
            Term.csize β (Term.msubstAt dd' env' t')
              = Term.csize β (Term.msubstAt dd' env' y) :=
          fun y hy t' ht' dd' env' =>
            ((ih y (helem (Eq.refl _) y hy)).1 t' ht') dd' env'
        have hIHl : ∀ y ∈ ys, ∀ t', PLt β t' y → ∀ dd' env',
            Term.csize β (Term.msubstAt dd' env' t')
              < Term.csize β (Term.msubstAt dd' env' y) :=
          fun y hy t' ht' dd' env' =>
            ((ih y (helem (Eq.refl _) y hy)).2 t' ht') dd' env'
        rw [Term.msubstAt_apps, Term.msubstAt_apps, Term.msubstAt_ctr]
        rw [Term.csize_ctr hk hc _ (by
          simp only [List.length_map, List.length_append]
          omega)]
        rw [Term.csize_fields hk hc _ (by
          simp only [List.length_map]
          rw [← hplts.map_length]
          omega)]
        rw [List.map_append]
        rw [show A.pn = (ps.map (Term.msubstAt dd env)).length from by
          simp only [List.length_map]
          omega]
        rw [List.drop_left]
        have := hplts.csize_sum hIHe hIHl dd env
        omega

theorem PEq.csize (hpe : PEq β t p) (dd : Nat) (env : List Term) :
    Term.csize β (Term.msubstAt dd env t) = Term.csize β (Term.msubstAt dd env p) :=
  ((descent_csize β (Term.size p) p (Nat.le_refl _)).1 t hpe) dd env

theorem PLt.csize (hpl : PLt β t p) (dd : Nat) (env : List Term) :
    Term.csize β (Term.msubstAt dd env t) < Term.csize β (Term.msubstAt dd env p) :=
  ((descent_csize β (Term.size p) p (Nat.le_refl _)).2 t hpl) dd env


-- the descent's columns, instantiated, drop lexicographically: there
-- the pinned row of a compared prefix: per column, a live column pins
-- the argument's constructor size, an erased column rides free
def pinsRow (β : Book) (qs : List Quant) : Nat → List Term → Nat → List (Option Nat)
  | _, _, 0 => []
  | j, xs, m + 1 =>
    (if qs.getD j .Lone = .None then none
     else some (Term.csize β (xs.getD 0 .Typ)))
      :: pinsRow β qs (j + 1) (xs.drop 1) m

theorem pinsRow_length (β : Book) (qs : List Quant) :
    ∀ (m j : Nat) (xs : List Term), (pinsRow β qs j xs m).length = m := by
  intro m
  induction m with
  | zero => intro j xs; rfl
  | succ m ih =>
    intro j xs
    show ((if qs.getD j .Lone = .None then none
      else some (Term.csize β (xs.getD 0 .Typ))) :: pinsRow β qs (j + 1)
      (xs.drop 1) m).length = m + 1
    simp only [List.length_cons, ih]

theorem pinsRow_getD (β : Book) (qs : List Quant) :
    ∀ (m i j : Nat) (xs : List Term), i < m →
    (pinsRow β qs j xs m).getD i none
      = (if qs.getD (j + i) .Lone = .None then none
         else some (Term.csize β (xs.getD i .Typ))) := by
  intro m
  induction m with
  | zero => intro i j xs hi; omega
  | succ m ih =>
    intro i j xs hi
    cases i with
    | zero =>
      show (if qs.getD j .Lone = .None then none
        else some (Term.csize β (xs.getD 0 .Typ))) = _
      rw [Nat.add_zero]
    | succ i =>
      show (pinsRow β qs (j + 1) (xs.drop 1) m).getD i none = _
      rw [ih i (j + 1) (xs.drop 1) (by omega)]
      have h1 : (xs.drop 1).getD i .Typ = xs.getD (i + 1) .Typ := by
        cases xs with
        | nil => simp
        | cons x xs' => rfl
      rw [h1, show j + 1 + i = j + (i + 1) from by omega]

theorem pinsRow_congr (β : Book) (qs : List Quant) :
    ∀ (m j : Nat) (xs xs' : List Term),
    (∀ i, i < m → qs.getD (j + i) .Lone ≠ .None →
      Term.csize β (xs'.getD i .Typ) = Term.csize β (xs.getD i .Typ)) →
    pinsRow β qs j xs' m = pinsRow β qs j xs m := by
  intro m
  induction m with
  | zero => intro j xs xs' h; rfl
  | succ m ih =>
    intro j xs xs' h
    show (if qs.getD j .Lone = .None then none
        else some (Term.csize β (xs'.getD 0 .Typ)))
        :: pinsRow β qs (j + 1) (xs'.drop 1) m
      = (if qs.getD j .Lone = .None then none
        else some (Term.csize β (xs.getD 0 .Typ)))
        :: pinsRow β qs (j + 1) (xs.drop 1) m
    by_cases hq : qs.getD j .Lone = .None
    · rw [if_pos hq, if_pos hq]
      congr 1
      refine ih (j + 1) (xs.drop 1) (xs'.drop 1) ?_
      intro i hi hlv
      have e1 : ∀ (l : List Term), (l.drop 1).getD i .Typ
          = l.getD (i + 1) .Typ := by
        intro l
        cases l with
        | nil => simp
        | cons x l' => rfl
      rw [e1, e1]
      refine h (i + 1) (by omega) ?_
      rw [show j + (i + 1) = j + 1 + i from by omega]
      exact hlv
    · rw [if_neg hq, if_neg hq, h 0 (by omega) (by
        rw [Nat.add_zero]
        exact hq)]
      congr 1
      refine ih (j + 1) (xs.drop 1) (xs'.drop 1) ?_
      intro i hi hlv
      have e1 : ∀ (l : List Term), (l.drop 1).getD i .Typ
          = l.getD (i + 1) .Typ := by
        intro l
        cases l with
        | nil => simp
        | cons x l' => rfl
      rw [e1, e1]
      refine h (i + 1) (by omega) ?_
      rw [show j + (i + 1) = j + 1 + i from by omega]
      exact hlv

-- is a compared prefix (equal sizes, then one strict) below which any
-- padding of the two tuples compares — the spent charge's suffix may
-- be pinned or free, the leaf charge's suffix stays free
theorem SpineLt.tuplt {qs : List Quant} : ∀ {j0 : Nat}
    {cols args : List Term}, SpineLt β qs j0 cols args →
    ∀ (dd : Nat) (env : List Term),
    ∃ m, 0 < m ∧ m ≤ args.length ∧ m ≤ cols.length ∧
    (∀ (ra rc : List (Option Nat)), ra.length = rc.length →
      TupLt
        (pinsRow β qs j0 (args.map (Term.msubstAt dd env)) m ++ ra)
        (pinsRow β qs j0 (cols.map (Term.msubstAt dd env)) m ++ rc)) ∧
    (∀ i, i < m → qs.getD (j0 + i) .Lone ≠ .None →
      PEq β (args.getD i .Typ) (cols.getD i .Typ)
      ∨ PLt β (args.getD i .Typ) (cols.getD i .Typ)) ∧
    (∀ i, i < m - 1 → qs.getD (j0 + i) .Lone ≠ .None →
      PEq β (args.getD i .Typ) (cols.getD i .Typ)) ∧
    (qs.getD (j0 + (m - 1)) .Lone ≠ .None ∧
      PLt β (args.getD (m - 1) .Typ) (cols.getD (m - 1) .Typ)) := by
  intro j0 cols args hsl
  induction hsl with
  | @here j t c cs ts hlive hlt =>
    intro dd env
    refine ⟨1, Nat.one_pos, by simp, by simp, ?_, ?_, ?_, ?_⟩
    · intro ra rc hlen
      have e1 : pinsRow β qs j ((t :: ts).map (Term.msubstAt dd env)) 1
          = [if qs.getD j .Lone = .None then none
             else some (Term.csize β (Term.msubstAt dd env t))] := rfl
      have e2 : pinsRow β qs j ((c :: cs).map (Term.msubstAt dd env)) 1
          = [if qs.getD j .Lone = .None then none
             else some (Term.csize β (Term.msubstAt dd env c))] := rfl
      rw [e1, e2, if_neg hlive, if_neg hlive]
      refine LexR.head ?_ (by simp [hlen])
      show OLt _ _
      simp only [OLt]
      exact hlt.csize dd env
    · intro i hi hlv
      have hi0 : i = 0 := by omega
      subst hi0
      exact Or.inr hlt
    · intro i hi hlv
      omega
    · refine ⟨?_, hlt⟩
      rw [Nat.add_zero]
      exact hlive
  | @skip j cs ts c t hq hrest ih =>
    intro dd env
    obtain ⟨m, hm0, hma, hmc, htup, hrel, hpre, hstrict⟩ := ih dd env
    refine ⟨m + 1, Nat.succ_pos m, by simp; omega, by simp; omega,
      ?_, ?_, ?_, ?_⟩
    · intro ra rc hlen
      have e1 : pinsRow β qs j ((t :: ts).map (Term.msubstAt dd env))
          (m + 1)
          = (if qs.getD j .Lone = .None then none
             else some (Term.csize β (Term.msubstAt dd env t)))
            :: pinsRow β qs (j + 1) (ts.map (Term.msubstAt dd env)) m :=
        rfl
      have e2 : pinsRow β qs j ((c :: cs).map (Term.msubstAt dd env))
          (m + 1)
          = (if qs.getD j .Lone = .None then none
             else some (Term.csize β (Term.msubstAt dd env c)))
            :: pinsRow β qs (j + 1) (cs.map (Term.msubstAt dd env)) m :=
        rfl
      rw [e1, e2, if_pos hq, if_pos hq]
      exact LexR.tail (htup ra rc hlen)
    · intro i hi hlv
      cases i with
      | zero =>
        rw [Nat.add_zero] at hlv
        exact absurd hq hlv
      | succ i =>
        refine hrel i (by omega) ?_
        rw [show j + 1 + i = j + (i + 1) from by omega]
        exact hlv
    · intro i hi hlv
      cases i with
      | zero =>
        rw [Nat.add_zero] at hlv
        exact absurd hq hlv
      | succ i =>
        refine hpre i (by omega) ?_
        rw [show j + 1 + i = j + (i + 1) from by omega]
        exact hlv
    · obtain ⟨hsl1, hsl2⟩ := hstrict
      refine ⟨?_, ?_⟩
      · rw [show j + (m + 1 - 1) = j + 1 + (m - 1) from by omega]
        exact hsl1
      · show PLt β ((t :: ts).getD (m + 1 - 1) .Typ)
          ((c :: cs).getD (m + 1 - 1) .Typ)
        rw [show m + 1 - 1 = (m - 1) + 1 from by omega]
        exact hsl2
  | @there j t c cs ts hlive heq hrest ih =>
    intro dd env
    obtain ⟨m, hm0, hma, hmc, htup, hrel, hpre, hstrict⟩ := ih dd env
    refine ⟨m + 1, Nat.succ_pos m, by simp; omega, by simp; omega,
      ?_, ?_, ?_, ?_⟩
    · intro ra rc hlen
      have e1 : pinsRow β qs j ((t :: ts).map (Term.msubstAt dd env))
          (m + 1)
          = (if qs.getD j .Lone = .None then none
             else some (Term.csize β (Term.msubstAt dd env t)))
            :: pinsRow β qs (j + 1) (ts.map (Term.msubstAt dd env)) m :=
        rfl
      have e2 : pinsRow β qs j ((c :: cs).map (Term.msubstAt dd env))
          (m + 1)
          = (if qs.getD j .Lone = .None then none
             else some (Term.csize β (Term.msubstAt dd env c)))
            :: pinsRow β qs (j + 1) (cs.map (Term.msubstAt dd env)) m :=
        rfl
      rw [e1, e2, if_neg hlive, if_neg hlive, heq.csize dd env]
      exact LexR.tail (htup ra rc hlen)
    · intro i hi hlv
      cases i with
      | zero => exact Or.inl heq
      | succ i =>
        refine hrel i (by omega) ?_
        rw [show j + 1 + i = j + (i + 1) from by omega]
        exact hlv
    · intro i hi hlv
      cases i with
      | zero => exact heq
      | succ i =>
        refine hpre i (by omega) ?_
        rw [show j + 1 + i = j + (i + 1) from by omega]
        exact hlv
    · obtain ⟨hsl1, hsl2⟩ := hstrict
      refine ⟨?_, ?_⟩
      · rw [show j + (m + 1 - 1) = j + 1 + (m - 1) from by omega]
        exact hsl1
      · show PLt β ((t :: ts).getD (m + 1 - 1) .Typ)
          ((c :: cs).getD (m + 1 - 1) .Typ)
        rw [show m + 1 - 1 = (m - 1) + 1 from by omega]
        exact hsl2

-- ============================================================================
-- METATHEORY §NC — CG, the charged guard: pricing the pending
-- references of a SUBJECT-AND-ERASURE pair, in the erasure's live
-- structure. Every live reference carries a CHARGE. A bare reference
-- is ⊤-priced at its own book index; an applied reference may PIN a
-- prefix of its SUBJECT arguments that are already closed values —
-- sizes live on the subject side, where the §7 descent comparison
-- speaks, and closed values are transparent to shift, subst, and weak
-- reduction, so a pinned tuple never moves. Anything that erases to
-- the dead token .Typ costs nothing, whatever its subject: dead code
-- may duplicate, but its charges never enter the multiset. Mat is
-- priced by ANY multiset dominating both arms (Sub): an affine β may
-- land one copy of a value in each arm (occ is arm-max), and one copy
-- of its charges suffices — selecting an arm is then a drop. The pad
-- rule folds slack into the derivation.
-- ============================================================================


theorem mem_take_getD (d0 : α) : ∀ (l : List α) (m : Nat) (x : α),
    x ∈ l.take m → ∃ j, j < m ∧ j < l.length ∧ l.getD j d0 = x := by
  intro l
  induction l with
  | nil => intro m x hx; simp at hx
  | cons y ys ih =>
    intro m x hx
    cases m with
    | zero => simp at hx
    | succ m =>
      rcases List.mem_cons.mp hx with h1 | h2
      · exact ⟨0, by omega, by simp, h1.symm⟩
      · obtain ⟨j, hj1, hj2, hj3⟩ := ih m x h2
        exact ⟨j + 1, by omega, by simp only [List.length_cons]; omega, hj3⟩

-- era-paired deep values: a value whose live spine arguments (per the
-- erasure's tokens) are recursively deep; dead positions ride as junk
inductive DeepP (β : Book) : Term → Term → Prop
  | mk : Term.Value β v →
         (Term.spine u).2.length = (Term.spine v).2.length →
         (∀ p ∈ ((Term.spine v).2).zip ((Term.spine u).2),
           p.2 ≠ .Typ → DeepP β p.1 p.2) →
         DeepP β v u
  | stuck : Book.defn β k = some d →
            (Term.spine v).1 = .Ref k →
            (Term.spine v).2.length < d.n ∨ d.body = none →
            DeepP β v u

theorem DeepP.value (h : DeepP β v u) : Term.Value β v := by
  cases h with
  | mk hv _ _ => exact hv
  | @stuck k d _ _ hk hsp hgate =>
    have hv2 : v = Term.apps (.Ref k) (Term.spine v).2 := by
      have h0 := Term.apps_spine v
      rw [hsp] at h0
      exact h0.symm
    rw [hv2]
    exact Term.Value.stuck hk hgate

theorem DeepP.apps_pairs {h0 uh0 : Term} (hh : h0.IsHead)
    (huh : uh0.IsHead) (hnr : ∀ k : Nat, h0 ≠ .Ref k)
    (h : DeepP β (Term.apps h0 as) (Term.apps uh0 us)) :
    us.length = as.length ∧
    (∀ p ∈ as.zip us, p.2 ≠ .Typ → DeepP β p.1 p.2) := by
  cases h with
  | mk hv hlen hp =>
    rw [Term.spine_apps hh, Term.spine_apps huh] at hlen hp
    exact ⟨hlen, hp⟩
  | stuck hk hsp hgate =>
    rw [Term.spine_apps hh] at hsp
    exact absurd hsp (hnr _)

theorem DeepP.of_apps {h0 uh0 : Term} (hh : h0.IsHead)
    (huh : uh0.IsHead)
    (hv : Term.Value β (Term.apps h0 as)) (hlen : us.length = as.length)
    (hp : ∀ p ∈ as.zip us, p.2 ≠ .Typ → DeepP β p.1 p.2) :
    DeepP β (Term.apps h0 as) (Term.apps uh0 us) := by
  refine .mk hv ?_ ?_
  · rw [Term.spine_apps hh, Term.spine_apps huh]
    exact hlen
  · rw [Term.spine_apps hh, Term.spine_apps huh]
    exact hp

theorem Spinal.apps (hh : Spinal h) : ∀ (as : List Term),
    Spinal (Term.apps h as) := by
  intro as
  induction as generalizing h with
  | nil => exact hh
  | cons x xs ih => exact ih (.app hh)

theorem zip_append_of_len {α γ : Type} : ∀ (as : List α) (cs : List γ)
    (bs : List α) (ds : List γ), as.length = cs.length →
    (as ++ bs).zip (cs ++ ds) = as.zip cs ++ bs.zip ds := by
  intro as
  induction as with
  | nil =>
    intro cs bs ds h
    cases cs with
    | nil => rfl
    | cons _ _ => exact absurd h (by simp)
  | cons a as ih =>
    intro cs bs ds h
    cases cs with
    | nil => exact absurd h (by simp)
    | cons c cs =>
      simp only [List.cons_append, List.zip_cons_cons]
      rw [ih cs bs ds (by simp only [List.length_cons] at h; omega)]

theorem zip_getD_mem {d1 : α} {d2 : γ} : ∀ (l1 : List α) (l2 : List γ)
    (i : Nat), i < l1.length → i < l2.length →
    (l1.getD i d1, l2.getD i d2) ∈ l1.zip l2 := by
  intro l1
  induction l1 with
  | nil => intro l2 i h1 h2; exact absurd h1 (by simp)
  | cons x xs ih =>
    intro l2 i h1 h2
    cases l2 with
    | nil => exact absurd h2 (by simp)
    | cons y ys =>
      cases i with
      | zero => exact List.mem_cons_self
      | succ i =>
        simp only [List.length_cons] at h1 h2
        exact List.mem_cons_of_mem _ (ih ys i (by omega) (by omega))

theorem zip_map_both (f : α → α') (g : γ → γ') :
    ∀ (l1 : List α) (l2 : List γ),
    (l1.map f).zip (l2.map g) = (l1.zip l2).map (fun p => (f p.1, g p.2)) := by
  intro l1
  induction l1 with
  | nil => intro l2; rfl
  | cons x xs ih =>
    intro l2
    cases l2 with
    | nil => rfl
    | cons y ys => simp only [List.map, List.zip_cons_cons, ih]

-- a pinned argument paired with its erasure token: a dead-token leaf
-- (closed subject riding under .Typ), a settled closed pair, or a full
-- constructor whose parameters ride free under .Typ tokens and whose
-- fields recurse. Substitution-stable on both sides, csize-stable on
-- the subject, and convertible at spend time into the deepening's
-- dead-or-deep disjunct
inductive PinOk (β : Book) : Term → Term → Prop
  | cls : v.Closed 0 → PinOk β v .Typ
  | val : v.Closed 0 → u.Closed 0 → DeepP β v u → PinOk β v u
  | ctr : Book.adt β a = some A → AdtD.ctr A c = some C →
          as.length = A.pn + C.fn → us2.length = A.pn + C.fn →
          (∀ t ∈ us2.take A.pn, t = Term.Typ) →
          (∀ p ∈ (as.drop A.pn).zip (us2.drop A.pn), PinOk β p.1 p.2) →
          PinOk β (Term.apps (.Ctr a c) as) (Term.apps (.Ctr a c) us2)
  | ctrT : Book.adt β a = some A → AdtD.ctr A c = some C →
           as.length = A.pn + C.fn →
           (∀ x ∈ as.drop A.pn, PinOk β x .Typ) →
           PinOk β (Term.apps (.Ctr a c) as) .Typ

theorem PinOk.spend (h : PinOk β v u) :
    u = .Typ ∨ DeepP β v u := by
  induction h with
  | cls _ => exact Or.inl _root_.rfl
  | val _ _ hd => exact Or.inr hd
  | ctrT _ _ _ _ _ => exact Or.inl _root_.rfl
  | @ctr a A c C as us2 hk hc hlen hlen2 hpar hfld ih =>
    right
    refine DeepP.of_apps (by trivial) (by trivial)
      (.spine (Spinal.apps .ctr _)) (by omega) ?_
    intro p hp htok
    have hsplit : as.zip us2 = (as.take A.pn).zip (us2.take A.pn)
        ++ (as.drop A.pn).zip (us2.drop A.pn) := by
      rw [← zip_append_of_len (as.take A.pn) (us2.take A.pn)
        (as.drop A.pn) (us2.drop A.pn) (by
          simp only [List.length_take]
          omega)]
      rw [List.take_append_drop, List.take_append_drop]
    rw [hsplit] at hp
    rcases List.mem_append.mp hp with h1 | h2
    · exact absurd (hpar p.2 (List.of_mem_zip h1).2) htok
    · rcases ih p h2 with h3 | h4
      · exact absurd h3 htok
      · exact h4

theorem PinOk.subst : ∀ {v u : Term}, PinOk β v u →
    ∀ (d : Nat) (w : Term) (d' : Nat) (w' : Term),
    PinOk β (Term.subst d w v) (Term.subst d' w' u)
      ∧ Term.csize β (Term.subst d w v) = Term.csize β v := by
  intro v u h
  induction h with
  | cls hv =>
    intro d w d' w'
    rw [Term.subst_closed _ 0 d w hv (Nat.zero_le d)]
    exact ⟨.cls hv, _root_.rfl⟩
  | val hv hu hd =>
    intro d w d' w'
    rw [Term.subst_closed _ 0 d w hv (Nat.zero_le d),
      Term.subst_closed _ 0 d' w' hu (Nat.zero_le d')]
    exact ⟨.val hv hu hd, _root_.rfl⟩
  | @ctrT a A c C as hk hc hlen hfld ih =>
    intro d w d' w'
    rw [Term.subst_apps]
    simp only [Term.subst]
    have hlen' : (as.map (Term.subst d w)).length = A.pn + C.fn := by
      simp only [List.length_map]
      exact hlen
    have hdrop : (as.map (Term.subst d w)).drop A.pn
        = (as.drop A.pn).map (Term.subst d w) := List.map_drop.symm
    constructor
    · refine .ctrT hk hc hlen' ?_
      rw [hdrop]
      intro x hx
      obtain ⟨x0, hx0, hxe⟩ := List.mem_map.mp hx
      subst hxe
      exact (ih x0 hx0 d w d' w').1
    · rw [Term.csize_ctr hk hc _ hlen', Term.csize_ctr hk hc _ hlen]
      rw [hdrop]
      congr 1
      rw [List.map_map]
      refine congrArg List.sum (List.map_congr_left ?_)
      intro x0 hx0
      show Term.csize β (Term.subst d w x0) = Term.csize β x0
      exact (ih x0 hx0 d w d' w').2
  | @ctr a A c C as us2 hk hc hlen hlen2 hpar hfld ih =>
    intro d w d' w'
    rw [Term.subst_apps, Term.subst_apps]
    simp only [Term.subst]
    have hlen' : (as.map (Term.subst d w)).length = A.pn + C.fn := by
      simp only [List.length_map]
      exact hlen
    have hdrop : (as.map (Term.subst d w)).drop A.pn
        = (as.drop A.pn).map (Term.subst d w) := List.map_drop.symm
    have hdrop2 : (us2.map (Term.subst d' w')).drop A.pn
        = (us2.drop A.pn).map (Term.subst d' w') := List.map_drop.symm
    constructor
    · refine .ctr hk hc hlen' (by
        simp only [List.length_map]
        exact hlen2) ?_ ?_
      · rw [show (us2.map (Term.subst d' w')).take A.pn
            = (us2.take A.pn).map (Term.subst d' w') from
            List.map_take.symm]
        intro t ht
        obtain ⟨t0, ht0, hte⟩ := List.mem_map.mp ht
        subst hte
        rw [hpar t0 ht0]
        rfl
      · rw [hdrop, hdrop2, zip_map_both]
        intro p hp
        obtain ⟨q, hq, he⟩ := List.mem_map.mp hp
        subst he
        exact (ih q hq d w d' w').1
    · rw [Term.csize_ctr hk hc _ hlen', Term.csize_ctr hk hc _ hlen]
      rw [hdrop]
      congr 1
      have hlz : as.drop A.pn
          = ((as.drop A.pn).zip (us2.drop A.pn)).map Prod.fst := by
        rw [List.map_fst_zip]
        simp only [List.length_drop]
        omega
      rw [List.map_map, hlz, List.map_map, List.map_map]
      refine congrArg List.sum (List.map_congr_left ?_)
      intro p hp
      show Term.csize β (Term.subst d w p.1) = Term.csize β p.1
      exact (ih p hp d w d' w').2

-- csize-rigid arguments: a pinned size must never move, but only the
-- constructor skeleton and its fields are measured — erased parameters
-- ride free, so a full constructor application with rigid fields is
-- rigid whatever its parameters mention
inductive Term.CRigid (β : Book) : Term → Prop
  | cls : v.Closed 0 → Term.CRigid β v
  | ctr : Book.adt β a = some A → AdtD.ctr A c = some C →
          as.length = A.pn + C.fn →
          (∀ x ∈ as.drop A.pn, Term.CRigid β x) →
          Term.CRigid β (Term.apps (.Ctr a c) as)


-- rigidity survives substitution, and the measured size never moves
theorem Term.CRigid.subst : ∀ {v : Term}, Term.CRigid β v →
    ∀ (d : Nat) (w : Term),
    Term.CRigid β (Term.subst d w v)
      ∧ Term.csize β (Term.subst d w v) = Term.csize β v := by
  intro v h
  induction h with
  | cls hc =>
    intro d w
    rw [Term.subst_closed _ 0 d w hc (Nat.zero_le d)]
    exact ⟨.cls hc, _root_.rfl⟩
  | @ctr a A c C as hk hc0 hlen hall ih =>
    intro d w
    rw [Term.subst_apps]
    simp only [Term.subst]
    have hlen' : (as.map (Term.subst d w)).length = A.pn + C.fn := by
      simp only [List.length_map]
      exact hlen
    have hdrop : (as.map (Term.subst d w)).drop A.pn
        = (as.drop A.pn).map (Term.subst d w) := List.map_drop.symm
    constructor
    · refine .ctr hk hc0 hlen' ?_
      rw [hdrop]
      intro x hx
      obtain ⟨x0, hx0, hxe⟩ := List.mem_map.mp hx
      subst hxe
      exact (ih x0 hx0 d w).1
    · rw [Term.csize_ctr hk hc0 _ hlen', Term.csize_ctr hk hc0 _ hlen]
      rw [hdrop]
      congr 1
      rw [List.map_map]
      show (List.map (fun x0 => Term.csize β (Term.subst d w x0))
        (as.drop A.pn)).sum = _
      exact congrArg List.sum
        (List.map_congr_left (fun x0 hx0 => (ih x0 hx0 d w).2))

inductive CG (β : Book) : List Charge → Term → Term → Prop
  | typ_ : CG β [] t .Typ
  | var  : CG β [] (.Var i) (.Var i)
  | ref  : Book.defn β k = some d →
           CG β [(k, List.replicate d.n none ++ [some d.n], ph)]
             (.Ref k) (.Ref k)
  | site : ∀ {k : Nat} {d : DefD} {xs us : List Term} {m : Nat}
           {ts : List (Option Nat)} {Css : List (List Charge)} {ph : Bool},
           Book.defn β k = some d →
           ts = pinsRow β d.qs 0 xs m
             ++ List.replicate (d.n - m) none
             ++ [some (d.n - min xs.length d.n)] →
           m ≤ xs.length → m ≤ d.n →
           (∀ j, j < m → d.qs.getD j .Lone ≠ .None →
             PinOk β (xs.getD j .Typ) (us.getD j .Typ)) →
           xs.length = us.length →
           Css.length = us.length →
           (∀ p ∈ (Css.zip xs).zip us, CG β p.1.1 p.1.2 p.2) →
           CG β ((k, ts, ph) :: Css.flatten)
             (Term.apps (.Ref k) xs) (Term.apps (.Ref k) us)
  | adt  : CG β [] (.Adt a r) (.Adt a r)
  | refa : CG β [] (.Ref k) (.Adt k [])
  | ctr  : CG β [] (.Ctr a c) (.Ctr a c)
  | efq  : CG β [] .Efq .Efq
  | rfl  : CG β [] .Rfl .Rfl
  | lam  : CG β C f uf → CG β C (.Lam f) (.Lam uf)
  | app  : CG β Ca f uf → CG β Cb a ua →
           CG β (Ca ++ Cb) (.App f a) (.App uf ua)
  | mat  : CG β Ch h uh → CG β Cm m um → Sub Ch C → Sub Cm C →
           CG β C (.Mat a c h m) (.Mat a c uh um)
  | rwt  : CG β Ce e ue → CG β Cf f uf →
           CG β (Ce ++ Cf) (.Rwt e P f) (.Rwt ue .Typ uf)
  | let_ : CG β Ca v uv → CG β Cb b ub →
           CG β (Ca ++ Cb) (.Let q v b) (.Let q' uv ub)
  | pad  : CG β C t u → Sub C C' → CG β C' t u

theorem CG.perm (h : CG β C t u) (hp : C.Perm C') : CG β C' t u :=
  h.pad ((Sub.refl C).perm_right hp)

theorem CG.weaken (h : CG β C t u) (hs : Sub C C') : CG β C' t u :=
  h.pad hs

-- every erasure prices: bare references at ⊤, phase true
theorem Era.cg (he : Era β Γ t T u) : ∃ C, CG β C t u := by
  induction he with
  | var _ => exact ⟨[], .var⟩
  | ref hk => exact ⟨_, .ref (ph := true) hk⟩
  | refA _ _ => exact ⟨[], .refa⟩
  | adt _ => exact ⟨[], .adt⟩
  | ctr _ _ _ => exact ⟨[], .ctr⟩
  | typ => exact ⟨[], .typ_⟩
  | all _ _ _ => exact ⟨[], .typ_⟩
  | lam _ _ ihf =>
    obtain ⟨C, hC⟩ := ihf
    exact ⟨C, .lam hC⟩
  | app_live _ _ ihf ihx =>
    obtain ⟨Cf, hf⟩ := ihf
    obtain ⟨Cx, hx⟩ := ihx
    exact ⟨_, .app hf hx⟩
  | app_dead _ _ ihf =>
    obtain ⟨Cf, hf⟩ := ihf
    exact ⟨_, .app hf .typ_⟩
  | let_live _ _ _ ihv ihb =>
    obtain ⟨Cv, hv⟩ := ihv
    obtain ⟨Cb, hb⟩ := ihb
    exact ⟨_, .let_ hv hb⟩
  | let_dead _ _ _ ihb =>
    obtain ⟨Cb, hb⟩ := ihb
    exact ⟨_, .let_ .typ_ hb⟩
  | eql _ _ _ => exact ⟨[], .typ_⟩
  | rfl _ => exact ⟨[], .rfl⟩
  | rwt _ _ _ ihe ihf =>
    obtain ⟨Ce, hce⟩ := ihe
    obtain ⟨Cf, hcf⟩ := ihf
    exact ⟨_, .rwt hce hcf⟩
  | mat _ _ _ _ _ _ _ _ _ ihh ihm =>
    obtain ⟨Ch, hh⟩ := ihh
    obtain ⟨Cm, hm⟩ := ihm
    exact ⟨Ch ++ Cm, .mat hh hm (Sub.append_right _ _) (Sub.append_left _ _)⟩
  | efq _ _ _ => exact ⟨[], .efq⟩
  | cnv _ _ ih => exact ih





-- a zero-occurrence substitution leaves the charges exactly alone:
-- nothing live receives the value, and dead receivers cost nothing
theorem CG.subst_zero (h : CG β C t u) : ∀ (d : Nat) (v uv : Term),
    v.Closed 0 → uv.Closed 0 → Term.occ d u = 0 →
    CG β C (Term.subst d v t) (Term.subst d uv u) := by
  induction h with
  | typ_ => intro d v uv _ _ _; exact .typ_
  | refa => intro d v uv _ _ _; exact .refa
  | @var i =>
    intro d v uv _ _ hocc
    simp only [Term.occ] at hocc
    have hne : i ≠ d := by
      intro he
      rw [if_pos he] at hocc
      omega
    show CG β [] (Term.subst d v (.Var i)) (Term.subst d uv (.Var i))
    simp only [Term.subst]
    rw [if_neg hne]
    split <;> exact .var
  | ref hk => intro d v uv _ _ _; exact .ref hk
  | @site k dd xs us m ts Css ph hk hts hm hmn hvals hlen hclen hall ih =>
    intro d v uv hv huv hocc
    rw [Term.subst_apps, Term.subst_apps]
    have hocc' : ∀ u' ∈ us, Term.occ d u' = 0 := by
      intro u' hu'
      rw [Term.occ_apps] at hocc
      have := mem_le_sum (Term.occ d) us u' hu'
      omega
    have hpin : pinsRow β dd.qs 0 (xs.map (Term.subst d v)) m
        = pinsRow β dd.qs 0 xs m := by
      refine pinsRow_congr β dd.qs m 0 xs (xs.map (Term.subst d v)) ?_
      intro i hi hlv
      rw [map_getD (Term.subst d v) .Typ .Typ xs i (by omega),
        ((hvals i hi (by
          rw [Nat.zero_add] at hlv
          exact hlv)).subst d v 0 .Typ).2]
    have hpinvals : ∀ j, j < m → dd.qs.getD j .Lone ≠ .None →
        PinOk β ((xs.map (Term.subst d v)).getD j .Typ)
          ((us.map (Term.subst d uv)).getD j .Typ) := by
      intro j hj hlv
      rw [map_getD (Term.subst d v) .Typ .Typ xs j (by omega),
        map_getD (Term.subst d uv) .Typ .Typ us j (by omega)]
      exact ((hvals j hj hlv).subst d v d uv).1
    show CG β _ (Term.apps (Term.subst d v (.Ref k)) _)
      (Term.apps (Term.subst d uv (.Ref k)) _)
    simp only [Term.subst]
    refine CG.site hk ?_ ?_ hmn hpinvals ?_ ?_ ?_
    · rw [hpin]
      simp only [List.length_map]
      exact hts
    · simp only [List.length_map]
      exact hm
    · simp only [List.length_map]
      exact hlen
    · simp only [List.length_map]
      exact hclen
    · refine zip_zip_map_mem (Term.subst d v) (Term.subst d uv) Css xs us ?_
      intro p hp
      exact ih p hp d v uv hv huv (hocc' p.2 (List.of_mem_zip hp).2)
  | adt => intro d v uv _ _ _; exact .adt
  | ctr => intro d v uv _ _ _; exact .ctr
  | efq => intro d v uv _ _ _; exact .efq
  | rfl => intro d v uv _ _ _; exact .rfl
  | @lam C0 f uf hf ihf =>
    intro d v uv hv huv hocc
    simp only [Term.occ] at hocc
    show CG β C0 (Term.subst d v (.Lam f)) (Term.subst d uv (.Lam uf))
    simp only [Term.subst]
    rw [Term.shift_closed v 0 0 hv (Nat.le_refl 0),
      Term.shift_closed uv 0 0 huv (Nat.le_refl 0)]
    exact .lam (ihf (d + 1) v uv hv huv hocc)
  | @app Ca f uf Cb a ua hf ha ihf iha =>
    intro d v uv hv huv hocc
    simp only [Term.occ] at hocc
    exact .app (ihf d v uv hv huv (by omega)) (iha d v uv hv huv (by omega))
  | @mat Ch h0 uh Cm m0 um C0 a c hh hm hsh hsm ihh ihm =>
    intro d v uv hv huv hocc
    simp only [Term.occ] at hocc
    have h1 : Term.occ d uh = 0 := by
      have hx : Term.occ d uh ≤ Nat.max (Term.occ d uh) (Term.occ d um) :=
        Nat.le_max_left _ _
      omega
    have h2 : Term.occ d um = 0 := by
      have hx : Term.occ d um ≤ Nat.max (Term.occ d uh) (Term.occ d um) :=
        Nat.le_max_right _ _
      omega
    exact .mat (ihh d v uv hv huv h1) (ihm d v uv hv huv h2) hsh hsm
  | @rwt Ce e ue Cf f uf P he hf ihe ihf =>
    intro d v uv hv huv hocc
    simp only [Term.occ] at hocc
    exact .rwt (ihe d v uv hv huv (by omega)) (ihf d v uv hv huv (by omega))
  | @let_ Ca v0 uv0 Cb b ub q q' hv0 hb ihv ihb =>
    intro d v uv hv huv hocc
    simp only [Term.occ] at hocc
    show CG β _ (Term.subst d v (.Let q v0 b)) (Term.subst d uv (.Let q' uv0 ub))
    simp only [Term.subst]
    rw [Term.shift_closed v 0 0 hv (Nat.le_refl 0),
      Term.shift_closed uv 0 0 huv (Nat.le_refl 0)]
    exact .let_ (ihv d v uv hv huv (by omega))
      (ihb (d + 1) v uv hv huv (by omega))
  | pad h0 hs ih =>
    intro d v uv hv huv hocc
    exact (ih d v uv hv huv hocc).pad hs


theorem Sub.nil (X : List Charge) : Sub [] X := ⟨X, by simp⟩

theorem Sub.cons (c : Charge) (h : Sub A B) : Sub (c :: A) (c :: B) := by
  obtain ⟨D, hD⟩ := h
  exact ⟨D, hD.cons c⟩

theorem perm_interchange (A B C D : List Charge) :
    ((A ++ B) ++ (C ++ D)).Perm ((A ++ C) ++ (B ++ D)) := by
  have e1 : (A ++ B) ++ (C ++ D) = A ++ ((B ++ C) ++ D) := by
    simp [List.append_assoc]
  have e2 : (A ++ C) ++ (B ++ D) = A ++ ((C ++ B) ++ D) := by
    simp [List.append_assoc]
  rw [e1, e2]
  refine List.Perm.append_left A (List.Perm.append_right D ?_)
  exact List.perm_append_comm

theorem perm_rotate (A B C : List Charge) :
    ((A ++ B) ++ C).Perm ((A ++ C) ++ B) := by
  have h1 : (A ++ B) ++ C = A ++ (B ++ C) := by simp [List.append_assoc]
  have h2 : (A ++ C) ++ B = A ++ (C ++ B) := by simp [List.append_assoc]
  rw [h1, h2]
  exact List.Perm.append_left A List.perm_append_comm

-- an affine substitution: at most one live copy of the value lands, so
-- one copy of its charges suffices — the site walk spends it on the
-- single argument that has the occurrence
theorem CG.site_args (d : Nat) (v uv : Term) (Cv : List Charge)
    (hv : v.Closed 0) (huv : uv.Closed 0) :
    ∀ (Css : List (List Charge)) (xs us : List Term),
    (∀ p ∈ (Css.zip xs).zip us, CG β p.1.1 p.1.2 p.2) →
    (∀ p ∈ (Css.zip xs).zip us, Term.occ d p.2 ≤ 1 →
        ∃ C', CG β C' (Term.subst d v p.1.2) (Term.subst d uv p.2)
          ∧ Sub C' (p.1.1 ++ Cv)) →
    (us.map (Term.occ d)).sum ≤ 1 →
    Css.length = us.length → xs.length = us.length →
    ∃ Css' : List (List Charge), Css'.length = Css.length ∧
      (∀ p ∈ (Css'.zip (xs.map (Term.subst d v))).zip
          (us.map (Term.subst d uv)), CG β p.1.1 p.1.2 p.2) ∧
      Sub Css'.flatten (Css.flatten ++ Cv) := by
  intro Css
  induction Css with
  | nil =>
    intro xs us _ _ _ hcl hxl
    refine ⟨[], _root_.rfl, ?_, Sub.nil _⟩
    intro p hp
    exact nomatch hp
  | cons C0 Css ih =>
    intro xs us hall hone hsum hcl hxl
    cases us with
    | nil => exact nomatch hcl
    | cons u0 us =>
      cases xs with
      | nil => exact nomatch hxl
      | cons x0 xs =>
        simp only [List.length_cons] at hcl hxl
        simp only [List.map, List.sum_cons] at hsum
        have hhead : CG β C0 x0 u0 :=
          hall ((C0, x0), u0) (by simp [List.zip_cons_cons])
        have htail : ∀ p ∈ (Css.zip xs).zip us, CG β p.1.1 p.1.2 p.2 := by
          intro p hp
          exact hall p (by
            simp only [List.zip_cons_cons]
            exact List.mem_cons_of_mem _ hp)
        by_cases hz : Term.occ d u0 = 0
        · -- the head misses: exact charges; recurse on the tail
          have h0 := hhead.subst_zero d v uv hv huv hz
          obtain ⟨Css', hlen', hall', hsub'⟩ := ih xs us htail
            (fun p hp hpo => hone p (by
              simp only [List.zip_cons_cons]
              exact List.mem_cons_of_mem _ hp) hpo)
            (by omega) (by omega) (by omega)
          refine ⟨C0 :: Css', by simp [hlen'], ?_, ?_⟩
          · intro p hp
            simp only [List.map, List.zip_cons_cons] at hp
            rcases List.mem_cons.mp hp with h1 | h2
            · subst h1
              exact h0
            · exact hall' p h2
          · show Sub (C0 ++ Css'.flatten) _
            refine Sub.perm_right (Sub.append (Sub.refl C0) hsub') ?_
            simp [List.append_assoc]
        · -- the head takes the value; the tail misses everywhere
          have hone0 : Term.occ d u0 ≤ 1 := by omega
          obtain ⟨C0', h0, hsub0⟩ := hone ((C0, x0), u0)
            (by simp [List.zip_cons_cons]) hone0
          have hztail : ∀ u' ∈ us, Term.occ d u' = 0 := by
            intro u' hu'
            have := mem_le_sum (Term.occ d) us u' hu'
            omega
          have hall' : ∀ p ∈ (Css.zip (xs.map (Term.subst d v))).zip
              (us.map (Term.subst d uv)), CG β p.1.1 p.1.2 p.2 := by
            refine zip_zip_map_mem _ _ Css xs us ?_
            intro p hp
            exact (htail p hp).subst_zero d v uv hv huv
              (hztail p.2 (List.of_mem_zip hp).2)
          refine ⟨C0' :: Css, by simp, ?_, ?_⟩
          · intro p hp
            simp only [List.map, List.zip_cons_cons] at hp
            rcases List.mem_cons.mp hp with h1 | h2
            · subst h1
              exact h0
            · exact hall' p h2
          · exact Sub.perm_right (Sub.append hsub0 (Sub.refl Css.flatten))
              (perm_rotate C0 Cv Css.flatten)

theorem CG.subst_one (h : CG β C t u) : ∀ (d : Nat) (v uv : Term)
    (Cv : List Charge), v.Closed 0 → uv.Closed 0 → CG β Cv v uv →
    Term.occ d u ≤ 1 →
    ∃ C', CG β C' (Term.subst d v t) (Term.subst d uv u)
      ∧ Sub C' (C ++ Cv) := by
  induction h with
  | typ_ =>
    intro d v uv Cv _ _ _ _
    exact ⟨[], .typ_, Sub.nil _⟩
  | refa =>
    intro d v uv Cv _ _ _ _
    exact ⟨[], .refa, Sub.nil _⟩
  | @var i =>
    intro d v uv Cv hv huv hcv _
    by_cases he : i = d
    · subst he
      refine ⟨Cv, ?_, ?_⟩
      · show CG β Cv (Term.subst i v (.Var i)) (Term.subst i uv (.Var i))
        simp only [Term.subst, if_pos]
        exact hcv
      · exact (Sub.refl Cv).perm_right (by simp)
    · refine ⟨[], ?_, Sub.nil _⟩
      show CG β [] (Term.subst d v (.Var i)) (Term.subst d uv (.Var i))
      simp only [Term.subst]
      rw [if_neg he]
      split <;> exact .var
  | ref hk =>
    intro d v uv Cv _ _ _ _
    exact ⟨_, .ref hk, Sub.append_right _ _⟩
  | @site k dd xs us m ts Css ph hk hts hm hmn hvals hlen hclen hall ih =>
    intro d v uv Cv hv huv hcv hocc
    rw [Term.occ_apps] at hocc
    obtain ⟨Css', hlen', hall', hsub'⟩ := CG.site_args d v uv Cv hv huv
      Css xs us hall
      (fun p hp hpo => ih p hp d v uv Cv hv huv hcv hpo)
      (by omega) hclen (by omega)
    rw [Term.subst_apps, Term.subst_apps]
    have hpin : pinsRow β dd.qs 0 (xs.map (Term.subst d v)) m
        = pinsRow β dd.qs 0 xs m := by
      refine pinsRow_congr β dd.qs m 0 xs (xs.map (Term.subst d v)) ?_
      intro i hi hlv
      rw [map_getD (Term.subst d v) .Typ .Typ xs i (by omega),
        ((hvals i hi (by
          rw [Nat.zero_add] at hlv
          exact hlv)).subst d v 0 .Typ).2]
    have hpinvals : ∀ j, j < m → dd.qs.getD j .Lone ≠ .None →
        PinOk β ((xs.map (Term.subst d v)).getD j .Typ)
          ((us.map (Term.subst d uv)).getD j .Typ) := by
      intro j hj hlv
      rw [map_getD (Term.subst d v) .Typ .Typ xs j (by omega),
        map_getD (Term.subst d uv) .Typ .Typ us j (by omega)]
      exact ((hvals j hj hlv).subst d v d uv).1
    refine ⟨(k, ts, ph) :: Css'.flatten, ?_, ?_⟩
    · show CG β _ (Term.apps (Term.subst d v (.Ref k)) _)
        (Term.apps (Term.subst d uv (.Ref k)) _)
      simp only [Term.subst]
      refine CG.site hk ?_ ?_ hmn hpinvals ?_ ?_ hall'
      · rw [hpin]
        simp only [List.length_map]
        exact hts
      · simp only [List.length_map]
        exact hm
      · simp only [List.length_map]
        exact hlen
      · simp only [List.length_map]
        rw [hlen']
        exact hclen
    · exact (Sub.cons _ hsub').perm_right (by simp)
  | adt =>
    intro d v uv Cv _ _ _ _
    exact ⟨[], .adt, Sub.nil _⟩
  | ctr =>
    intro d v uv Cv _ _ _ _
    exact ⟨[], .ctr, Sub.nil _⟩
  | efq =>
    intro d v uv Cv _ _ _ _
    exact ⟨[], .efq, Sub.nil _⟩
  | rfl =>
    intro d v uv Cv _ _ _ _
    exact ⟨[], .rfl, Sub.nil _⟩
  | @lam C0 f uf hf ihf =>
    intro d v uv Cv hv huv hcv hocc
    simp only [Term.occ] at hocc
    obtain ⟨C', h', hsub⟩ := ihf (d + 1) v uv Cv hv huv hcv hocc
    refine ⟨C', ?_, hsub⟩
    show CG β C' (Term.subst d v (.Lam f)) (Term.subst d uv (.Lam uf))
    simp only [Term.subst]
    rw [Term.shift_closed v 0 0 hv (Nat.le_refl 0),
      Term.shift_closed uv 0 0 huv (Nat.le_refl 0)]
    exact .lam h'
  | @app Ca f uf Cb a ua hf ha ihf iha =>
    intro d v uv Cv hv huv hcv hocc
    simp only [Term.occ] at hocc
    by_cases hz : Term.occ d uf = 0
    · have h1 := hf.subst_zero d v uv hv huv hz
      obtain ⟨C'b, h2, hsub⟩ := iha d v uv Cv hv huv hcv (by omega)
      refine ⟨Ca ++ C'b, .app h1 h2, ?_⟩
      refine Sub.perm_right (Sub.append (Sub.refl Ca) hsub) ?_
      simp [List.append_assoc]
    · have hza : Term.occ d ua = 0 := by omega
      obtain ⟨C'a, h1, hsub⟩ := ihf d v uv Cv hv huv hcv (by omega)
      have h2 := ha.subst_zero d v uv hv huv hza
      refine ⟨C'a ++ Cb, .app h1 h2, ?_⟩
      exact Sub.perm_right (Sub.append hsub (Sub.refl Cb))
        (perm_rotate Ca Cv Cb)
  | @mat Ch h0 uh Cm m0 um C0 a c hh hm hsh hsm ihh ihm =>
    intro d v uv Cv hv huv hcv hocc
    simp only [Term.occ] at hocc
    have h1 : Term.occ d uh ≤ 1 := by
      have hx : Term.occ d uh ≤ Nat.max (Term.occ d uh) (Term.occ d um) :=
        Nat.le_max_left _ _
      omega
    have h2 : Term.occ d um ≤ 1 := by
      have hx : Term.occ d um ≤ Nat.max (Term.occ d uh) (Term.occ d um) :=
        Nat.le_max_right _ _
      omega
    obtain ⟨C'h, hh', hsubh⟩ := ihh d v uv Cv hv huv hcv h1
    obtain ⟨C'm, hm', hsubm⟩ := ihm d v uv Cv hv huv hcv h2
    refine ⟨C0 ++ Cv, ?_, Sub.refl _⟩
    exact .mat hh' hm'
      (hsubh.trans (Sub.append hsh (Sub.refl Cv)))
      (hsubm.trans (Sub.append hsm (Sub.refl Cv)))
  | @rwt Ce e ue Cf f uf P he hf ihe ihf =>
    intro d v uv Cv hv huv hcv hocc
    simp only [Term.occ] at hocc
    by_cases hz : Term.occ d ue = 0
    · have h1 := he.subst_zero d v uv hv huv hz
      obtain ⟨C'f, h2, hsub⟩ := ihf d v uv Cv hv huv hcv (by omega)
      refine ⟨Ce ++ C'f, .rwt h1 h2, ?_⟩
      refine Sub.perm_right (Sub.append (Sub.refl Ce) hsub) ?_
      simp [List.append_assoc]
    · have hzf : Term.occ d uf = 0 := by omega
      obtain ⟨C'e, h1, hsub⟩ := ihe d v uv Cv hv huv hcv (by omega)
      have h2 := hf.subst_zero d v uv hv huv hzf
      refine ⟨C'e ++ Cf, .rwt h1 h2, ?_⟩
      exact Sub.perm_right (Sub.append hsub (Sub.refl Cf))
        (perm_rotate Ce Cv Cf)
  | @let_ Ca v0 uv0 Cb b ub q q' hv0 hb ihv ihb =>
    intro d v uv Cv hv huv hcv hocc
    simp only [Term.occ] at hocc
    by_cases hz : Term.occ d uv0 = 0
    · have h1 := hv0.subst_zero d v uv hv huv hz
      obtain ⟨C'b, h2, hsub⟩ := ihb (d + 1) v uv Cv hv huv hcv (by omega)
      refine ⟨Ca ++ C'b, ?_, ?_⟩
      · show CG β _ (Term.subst d v (.Let q v0 b))
          (Term.subst d uv (.Let q' uv0 ub))
        simp only [Term.subst]
        rw [Term.shift_closed v 0 0 hv (Nat.le_refl 0),
          Term.shift_closed uv 0 0 huv (Nat.le_refl 0)]
        exact .let_ h1 h2
      · refine Sub.perm_right (Sub.append (Sub.refl Ca) hsub) ?_
        simp [List.append_assoc]
    · have hzb : Term.occ (d + 1) ub = 0 := by omega
      obtain ⟨C'a, h1, hsub⟩ := ihv d v uv Cv hv huv hcv (by omega)
      have h2 := hb.subst_zero (d + 1) v uv hv huv hzb
      refine ⟨C'a ++ Cb, ?_, ?_⟩
      · show CG β _ (Term.subst d v (.Let q v0 b))
          (Term.subst d uv (.Let q' uv0 ub))
        simp only [Term.subst]
        rw [Term.shift_closed v 0 0 hv (Nat.le_refl 0),
          Term.shift_closed uv 0 0 huv (Nat.le_refl 0)]
        exact .let_ h1 h2
      · exact Sub.perm_right (Sub.append hsub (Sub.refl Cb))
          (perm_rotate Ca Cv Cb)
  | pad h0 hs ih =>
    intro d v uv Cv hv huv hcv hocc
    obtain ⟨C', h', hsub⟩ := ih d v uv Cv hv huv hcv hocc
    exact ⟨C', h', hsub.trans (Sub.append hs (Sub.refl Cv))⟩


-- slot-wise charge bookkeeping: appending per-slot ledgers
theorem zipWith_append_getD : ∀ (As Bs : List (List Charge)) (i : Nat),
    As.length = Bs.length →
    (List.zipWith (· ++ ·) As Bs).getD i [] = As.getD i [] ++ Bs.getD i [] := by
  intro As
  induction As with
  | nil =>
    intro Bs i hlen
    cases Bs with
    | nil => cases i <;> rfl
    | cons _ _ => exact absurd hlen (by simp)
  | cons A As ih =>
    intro Bs i hlen
    cases Bs with
    | nil => exact absurd hlen (by simp)
    | cons B Bs =>
      cases i with
      | zero => rfl
      | succ i =>
        show (List.zipWith (· ++ ·) As Bs).getD i [] = _
        exact ih Bs i (by simp only [List.length_cons] at hlen; omega)

theorem zipWith_append_length : ∀ (As Bs : List (List Charge)),
    As.length = Bs.length →
    (List.zipWith (· ++ ·) As Bs).length = As.length := by
  intro As
  induction As with
  | nil => intro Bs _; rfl
  | cons A As ih =>
    intro Bs hlen
    cases Bs with
    | nil => exact absurd hlen (by simp)
    | cons B Bs =>
      show (List.zipWith (· ++ ·) As Bs).length + 1 = _
      rw [ih Bs (by simp only [List.length_cons] at hlen; omega)]
      rfl

theorem zipWith_append_flatten : ∀ (As Bs : List (List Charge)),
    As.length = Bs.length →
    (List.zipWith (· ++ ·) As Bs).flatten.Perm (As.flatten ++ Bs.flatten) := by
  intro As
  induction As with
  | nil =>
    intro Bs hlen
    cases Bs with
    | nil => exact List.Perm.refl _
    | cons _ _ => exact absurd hlen (by simp)
  | cons A As ih =>
    intro Bs hlen
    cases Bs with
    | nil => exact absurd hlen (by simp)
    | cons B Bs =>
      show ((A ++ B) ++ (List.zipWith (· ++ ·) As Bs).flatten).Perm
        ((A ++ As.flatten) ++ (B ++ Bs.flatten))
      have h1 := ih Bs (by simp only [List.length_cons] at hlen; omega)
      refine List.Perm.trans (List.Perm.append_left (A ++ B) h1) ?_
      have e1 : (A ++ B) ++ (As.flatten ++ Bs.flatten)
          = (A ++ (B ++ As.flatten)) ++ Bs.flatten := by
        simp [List.append_assoc]
      have e2 : (A ++ As.flatten) ++ (B ++ Bs.flatten)
          = (A ++ (As.flatten ++ B)) ++ Bs.flatten := by
        simp [List.append_assoc]
      rw [e1, e2]
      refine List.Perm.append_right Bs.flatten ?_
      exact List.Perm.append_left A List.perm_append_comm

theorem replicate_nil_getD (n i : Nat) :
    (List.replicate n ([] : List Charge)).getD i [] = [] := by
  induction n generalizing i with
  | zero => cases i <;> rfl
  | succ n ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

theorem replicate_nil_flatten (n : Nat) :
    (List.replicate n ([] : List Charge)).flatten = [] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show [] ++ (List.replicate n ([] : List Charge)).flatten = []
    rw [ih]
    rfl

-- a single occupied slot
theorem slot_single_getD_eq (Cv : List Charge) : ∀ (n j : Nat), j < n →
    ((List.replicate n ([] : List Charge)).set j Cv).getD j [] = Cv := by
  intro n
  induction n with
  | zero => intro j hj; omega
  | succ n ih =>
    intro j hj
    cases j with
    | zero => rfl
    | succ j =>
      show ((List.replicate n ([] : List Charge)).set j Cv).getD j [] = Cv
      exact ih j (by omega)

theorem slot_single_getD_ne (Cv : List Charge) : ∀ (n j i : Nat), i ≠ j →
    ((List.replicate n ([] : List Charge)).set j Cv).getD i [] = [] := by
  intro n
  induction n with
  | zero =>
    intro j i _
    cases j <;> cases i <;> rfl
  | succ n ih =>
    intro j i hne
    cases j with
    | zero =>
      cases i with
      | zero => exact absurd _root_.rfl hne
      | succ i =>
        show (List.replicate n ([] : List Charge)).getD i [] = []
        exact replicate_nil_getD n i
    | succ j =>
      cases i with
      | zero => rfl
      | succ i =>
        show ((List.replicate n ([] : List Charge)).set j Cv).getD i [] = []
        exact ih j i (by omega)

theorem slot_single_flatten (n j : Nat) (Cv : List Charge) (hj : j < n) :
    ((List.replicate n ([] : List Charge)).set j Cv).flatten.Perm Cv := by
  induction n generalizing j with
  | zero => omega
  | succ n ih =>
    cases j with
    | zero =>
      show (Cv ++ (List.replicate n ([] : List Charge)).flatten).Perm Cv
      rw [replicate_nil_flatten]
      simp
    | succ j =>
      show ([] ++ ((List.replicate n ([] : List Charge)).set j Cv).flatten).Perm Cv
      rw [List.nil_append]
      exact ih j (by omega)


theorem zip_zip_getD_mem : ∀ (Css : List (List Charge)) (env uenv : List Term),
    Css.length = uenv.length → env.length = uenv.length →
    ∀ (j : Nat), j < uenv.length →
    ((Css.getD j [], env.getD j .Typ), uenv.getD j .Typ)
      ∈ (Css.zip env).zip uenv := by
  intro Css
  induction Css with
  | nil =>
    intro env uenv hl1 _ j hj
    rw [← hl1] at hj
    exact absurd hj (by simp)
  | cons C0 Css ih =>
    intro env uenv hl1 hl2 j hj
    cases env with
    | nil =>
      rw [← hl2] at hj
      exact absurd hj (by simp)
    | cons v env =>
      cases uenv with
      | nil => exact absurd hj (by simp)
      | cons uv uenv =>
        simp only [List.zip_cons_cons]
        cases j with
        | zero => exact List.mem_cons_self
        | succ j =>
          refine List.mem_cons_of_mem _ ?_
          exact ih env uenv
            (by simp only [List.length_cons] at hl1; omega)
            (by simp only [List.length_cons] at hl2; omega)
            j (by simp only [List.length_cons] at hj; omega)

-- erasure output shapes by subject head (the cnv rule never edits terms)
theorem Era.typ_out (h : Era β Γ .Typ T u) : u = .Typ := by
  generalize he : Term.Typ = t0 at h
  induction h <;> first
  | exact Term.noConfusion he
  | exact _root_.rfl
  | (rename_i ih; exact ih he)

theorem Era.adt_out (h : Era β Γ (.Adt a r) T u) : u = .Adt a r := by
  generalize he : Term.Adt a r = t0 at h
  induction h <;> first
  | exact Term.noConfusion he
  | (cases he; exact _root_.rfl)
  | (rename_i ih; exact ih he)

theorem Era.ctr_out (h : Era β Γ (.Ctr a c) T u) : u = .Ctr a c := by
  generalize he : Term.Ctr a c = t0 at h
  induction h <;> first
  | exact Term.noConfusion he
  | (cases he; exact _root_.rfl)
  | (rename_i ih; exact ih he)

theorem Era.all_out (h : Era β Γ (.All q A B) T u) : u = .Typ := by
  generalize he : Term.All q A B = t0 at h
  induction h <;> first
  | exact Term.noConfusion he
  | exact _root_.rfl
  | (rename_i ih; exact ih he)

theorem Era.eql_out (h : Era β Γ (.Eql x y T0) T u) : u = .Typ := by
  generalize he : Term.Eql x y T0 = t0 at h
  induction h <;> first
  | exact Term.noConfusion he
  | exact _root_.rfl
  | (rename_i ih; exact ih he)

theorem Era.rfl_out (h : Era β Γ .Rfl T u) : u = .Rfl := by
  generalize he : Term.Rfl = t0 at h
  induction h <;> first
  | exact Term.noConfusion he
  | exact _root_.rfl
  | (rename_i ih; exact ih he)

theorem Era.efq_out (h : Era β Γ .Efq T u) : u = .Efq := by
  generalize he : Term.Efq = t0 at h
  induction h <;> first
  | exact Term.noConfusion he
  | exact _root_.rfl
  | (rename_i ih; exact ih he)

-- merging the two arms' slot ledgers under a Mat: a used slot is
-- dominated by the full input slot, an unused one stays empty
theorem mat_slots : ∀ (Ch Cm Css : List (List Charge)),
    Ch.length = Css.length → Cm.length = Css.length →
    (∀ i, i < Css.length → Sub (Ch.getD i []) (Css.getD i [])) →
    (∀ i, i < Css.length → Sub (Cm.getD i []) (Css.getD i [])) →
    ∃ Crs : List (List Charge), Crs.length = Css.length ∧
      (∀ i, i < Css.length → Sub (Ch.getD i []) (Crs.getD i []) ∧
        Sub (Cm.getD i []) (Crs.getD i [])) ∧
      (∀ i, i < Css.length → Sub (Crs.getD i []) (Css.getD i []) ∧
        (Ch.getD i [] = [] ∧ Cm.getD i [] = [] → Crs.getD i [] = [])) := by
  intro Ch
  induction Ch with
  | nil =>
    intro Cm Css hl1 _ _ _
    cases Css with
    | nil =>
      refine ⟨[], _root_.rfl, ?_, ?_⟩ <;> intro i hi <;> exact nomatch hi
    | cons _ _ => exact absurd hl1 (by simp)
  | cons c0 Ch ih =>
    intro Cm Css hl1 hl2 hsh hsm
    cases Css with
    | nil => exact absurd hl1 (by simp)
    | cons cs0 Css =>
      cases Cm with
      | nil => exact absurd hl2 (by simp)
      | cons m0 Cm =>
        obtain ⟨Crs, hlr, hdom, hsub⟩ := ih Cm Css
          (by simp only [List.length_cons] at hl1; omega)
          (by simp only [List.length_cons] at hl2; omega)
          (fun i hi => hsh (i + 1) (by simp only [List.length_cons]; omega))
          (fun i hi => hsm (i + 1) (by simp only [List.length_cons]; omega))
        by_cases hz : c0 = [] ∧ m0 = []
        · refine ⟨[] :: Crs, by simp [hlr], ?_, ?_⟩
          · intro i hi
            cases i with
            | zero => exact ⟨by rw [hz.1]; exact Sub.refl _,
                by rw [hz.2]; exact Sub.refl _⟩
            | succ i =>
              exact hdom i (by simp only [List.length_cons] at hi; omega)
          · intro i hi
            cases i with
            | zero => exact ⟨Sub.nil _, fun _ => _root_.rfl⟩
            | succ i =>
              exact hsub i (by simp only [List.length_cons] at hi; omega)
        · refine ⟨cs0 :: Crs, by simp [hlr], ?_, ?_⟩
          · intro i hi
            cases i with
            | zero =>
              exact ⟨hsh 0 (by simp), hsm 0 (by simp)⟩
            | succ i =>
              exact hdom i (by simp only [List.length_cons] at hi; omega)
          · intro i hi
            cases i with
            | zero =>
              refine ⟨Sub.refl _, ?_⟩
              intro hboth
              exact absurd hboth hz
            | succ i =>
              exact hsub i (by simp only [List.length_cons] at hi; omega)


-- the comparison's argument side instantiates RIGID: every leaf is an
-- environment value (closed), every node a full constructor whose
-- parameters ride free
theorem PEqs.crigid : ∀ {xs ys : List Term}, PEqs β xs ys →
    (∀ y ∈ ys, ∀ t, PEq β t y →
      (Term.msubstAt dd env y).Closed 0 →
      PinOk β (Term.msubstAt dd env t) .Typ) →
    (∀ y ∈ ys, (Term.msubstAt dd env y).Closed 0) →
    ∀ x ∈ xs, PinOk β (Term.msubstAt dd env x) .Typ := by
  intro xs
  induction xs with
  | nil => intro ys h _ _ x hx; exact nomatch hx
  | cons x0 xs ih =>
    intro ys h hIH hcl x hx
    cases h with
    | @cons _ y _ ys' hxy hrest =>
      rcases List.mem_cons.mp hx with h1 | h2
      · subst h1
        exact hIH y List.mem_cons_self x hxy (hcl y List.mem_cons_self)
      · exact ih hrest
          (fun y' hy' => hIH y' (List.mem_cons_of_mem y hy'))
          (fun y' hy' => hcl y' (List.mem_cons_of_mem y hy')) x h2

theorem PLes.crigid : ∀ {xs ys : List Term}, PLes β xs ys →
    (∀ y ∈ ys, ∀ t, PEq β t y →
      (Term.msubstAt dd env y).Closed 0 →
      PinOk β (Term.msubstAt dd env t) .Typ) →
    (∀ y ∈ ys, ∀ t, PLt β t y →
      (Term.msubstAt dd env y).Closed 0 →
      PinOk β (Term.msubstAt dd env t) .Typ) →
    (∀ y ∈ ys, (Term.msubstAt dd env y).Closed 0) →
    ∀ x ∈ xs, PinOk β (Term.msubstAt dd env x) .Typ := by
  intro xs
  induction xs with
  | nil => intro ys h _ _ _ x hx; exact nomatch hx
  | cons x0 xs ih =>
    intro ys h hIHe hIHl hcl x hx
    cases h with
    | @consEq _ y _ ys' hxy hrest =>
      rcases List.mem_cons.mp hx with h1 | h2
      · subst h1
        exact hIHe y List.mem_cons_self x hxy (hcl y List.mem_cons_self)
      · exact ih hrest
          (fun y' hy' => hIHe y' (List.mem_cons_of_mem y hy'))
          (fun y' hy' => hIHl y' (List.mem_cons_of_mem y hy'))
          (fun y' hy' => hcl y' (List.mem_cons_of_mem y hy')) x h2
    | @consLt _ y _ ys' hxy hrest =>
      rcases List.mem_cons.mp hx with h1 | h2
      · subst h1
        exact hIHl y List.mem_cons_self x hxy (hcl y List.mem_cons_self)
      · exact ih hrest
          (fun y' hy' => hIHe y' (List.mem_cons_of_mem y hy'))
          (fun y' hy' => hIHl y' (List.mem_cons_of_mem y hy'))
          (fun y' hy' => hcl y' (List.mem_cons_of_mem y hy')) x h2

theorem PLts.crigid : ∀ {xs ys : List Term}, PLts β xs ys →
    (∀ y ∈ ys, ∀ t, PEq β t y →
      (Term.msubstAt dd env y).Closed 0 →
      PinOk β (Term.msubstAt dd env t) .Typ) →
    (∀ y ∈ ys, ∀ t, PLt β t y →
      (Term.msubstAt dd env y).Closed 0 →
      PinOk β (Term.msubstAt dd env t) .Typ) →
    (∀ y ∈ ys, (Term.msubstAt dd env y).Closed 0) →
    ∀ x ∈ xs, PinOk β (Term.msubstAt dd env x) .Typ := by
  intro xs
  induction xs with
  | nil => intro ys h _ _ _ x hx; exact nomatch hx
  | cons x0 xs ih =>
    intro ys h hIHe hIHl hcl x hx
    cases h with
    | @here _ y _ ys' hxy hrest =>
      rcases List.mem_cons.mp hx with h1 | h2
      · subst h1
        exact hIHl y List.mem_cons_self x hxy (hcl y List.mem_cons_self)
      · exact hrest.crigid
          (fun y' hy' => hIHe y' (List.mem_cons_of_mem y hy'))
          (fun y' hy' => hIHl y' (List.mem_cons_of_mem y hy'))
          (fun y' hy' => hcl y' (List.mem_cons_of_mem y hy')) x h2
    | @there _ y _ ys' hxy hrest =>
      rcases List.mem_cons.mp hx with h1 | h2
      · subst h1
        exact hIHe y List.mem_cons_self x hxy (hcl y List.mem_cons_self)
      · exact ih hrest
          (fun y' hy' => hIHe y' (List.mem_cons_of_mem y hy'))
          (fun y' hy' => hIHl y' (List.mem_cons_of_mem y hy'))
          (fun y' hy' => hcl y' (List.mem_cons_of_mem y hy')) x h2

theorem descent_crigid (β : Book) (dd : Nat) (env : List Term)
    (henv : ∀ v ∈ env, v.Closed 0) :
    ∀ (n : Nat) (p : Term), Term.size p ≤ n →
      (∀ t, PEq β t p → (Term.msubstAt dd env p).Closed 0 →
        PinOk β (Term.msubstAt dd env t) .Typ) ∧
      (∀ t, PLt β t p → (Term.msubstAt dd env p).Closed 0 →
        PinOk β (Term.msubstAt dd env t) .Typ) := by
  intro n
  induction n with
  | zero =>
    intro p hp
    have := Term.size_pos p
    omega
  | succ n ih =>
    intro p hp
    have helem : ∀ {a c : Nat} {ys : List Term},
        p = Term.apps (.Ctr a c) ys → ∀ y ∈ ys, Term.size y ≤ n := by
      intro a c ys hpe y hy
      have hsp : y ∈ (Term.spine p).2 := by
        rw [hpe, Term.spine_apps (by trivial)]
        exact hy
      have := Term.size_spine_arg p y hsp
      omega
    have hfields : ∀ {a c : Nat} {ys : List Term},
        p = Term.apps (.Ctr a c) ys →
        (Term.msubstAt dd env p).Closed 0 →
        ∀ y ∈ ys, (Term.msubstAt dd env y).Closed 0 := by
      intro a c ys hpe hclp y hy
      subst hpe
      rw [Term.msubstAt_apps, Term.msubstAt_ctr] at hclp
      have := (Term.closed_apps _ _ _).mp hclp
      exact this.2 _ (List.mem_map_of_mem hy)
    have hvar : ∀ (i : Nat), (Term.msubstAt dd env (.Var i)).Closed 0 →
        PinOk β (Term.msubstAt dd env (.Var i)) .Typ := by
      intro i hcl
      by_cases h1 : i < dd
      · rw [Term.msubstAt_var_lt dd i h1] at hcl ⊢
        exact absurd hcl (by simp [Term.Closed])
      · by_cases h2 : i - dd < env.length
        · have hie : i = dd + (i - dd) := by omega
          rw [hie, Term.msubstAt_var_hit dd env
            henv (i - dd) h2] at hcl ⊢
          have hmem : env.getD (i - dd) .Typ ∈ env := getD_mem env (i - dd) h2
          exact .cls (henv _ hmem)
        · rw [Term.msubstAt_var_ge dd env i (by omega)] at hcl
          exact absurd hcl (by simp [Term.Closed])
    constructor
    · intro t hpe hclp
      cases hpe with
      | var => exact hvar _ hclp
      | @ctr a A c C xs ys ps hk hc hlp hlx hpes =>
        rw [Term.msubstAt_apps, Term.msubstAt_ctr]
        refine PinOk.ctrT hk hc ?_ ?_
        · simp only [List.length_map, List.length_append]
          omega
        · rw [List.map_append]
          rw [show A.pn = (ps.map (Term.msubstAt dd env)).length from by
            simp only [List.length_map]
            omega]
          rw [List.drop_left]
          intro x hx
          obtain ⟨x0, hx0, hxe⟩ := List.mem_map.mp hx
          subst hxe
          refine hpes.crigid ?_ (hfields (Eq.refl _) hclp) x0 hx0
          intro y hy t' ht' hcy
          exact ((ih y (helem (Eq.refl _) y hy)).1 t' ht') hcy
    · intro t hpl hclp
      cases hpl with
      | @subEq a A c C ys y _t hk hc hly hy hpe =>
        exact ((ih y (helem (Eq.refl _) y hy)).1 t hpe)
          (hfields (Eq.refl _) hclp y hy)
      | @subLt a A c C ys y _t hk hc hly hy hpl2 =>
        exact ((ih y (helem (Eq.refl _) y hy)).2 t hpl2)
          (hfields (Eq.refl _) hclp y hy)
      | @ctr a A c C xs ys ps hk hc hlp hlx hplts =>
        rw [Term.msubstAt_apps, Term.msubstAt_ctr]
        refine PinOk.ctrT hk hc ?_ ?_
        · simp only [List.length_map, List.length_append]
          omega
        · rw [List.map_append]
          rw [show A.pn = (ps.map (Term.msubstAt dd env)).length from by
            simp only [List.length_map]
            omega]
          rw [List.drop_left]
          intro x hx
          obtain ⟨x0, hx0, hxe⟩ := List.mem_map.mp hx
          subst hxe
          refine hplts.crigid ?_ ?_ (hfields (Eq.refl _) hclp) x0 hx0
          · intro y hy t' ht' hcy
            exact ((ih y (helem (Eq.refl _) y hy)).1 t' ht') hcy
          · intro y hy t' ht' hcy
            exact ((ih y (helem (Eq.refl _) y hy)).2 t' ht') hcy

theorem EraSpine.lengths (hs : EraSpine β Γ T0 as T' us) :
    as.length = us.length := by
  induction hs with
  | nil => rfl
  | live _ _ _ ih => simpa using ih
  | dead _ _ _ ih => simpa using ih



theorem Era.var_out_inv : ∀ {Γ : Ctx} {i : Nat} {T u : Term},
    Era β Γ (.Var i) T u → u = .Var i := by
  intro Γ i T u h
  generalize he : Term.Var i = t0 at h
  induction h <;> try exact Term.noConfusion he
  case var i2 _ =>
    cases he
    rfl
  case cnv ih =>
    exact ih he

-- the parameter region of a constructor-typed spine is dead: WTele's
-- parameter binders are None-quantified, and a live arm would force a
-- Lone/None quantifier clash through conversion
theorem EraSpine.wtele_dead (hβ : Book.Closed β) :
    ∀ {Γ : Ctx} {T0 T' : Term} {as us : List Term},
    EraSpine β Γ T0 as T' us →
    ∀ {a : Nat} {r : List Nat} {pn fn : Nat} {ps : List Term} {Tw : Term},
    WTele a r ps pn fn Tw → Conv β Tw T0 →
    ∀ j, j < pn → us.getD j .Typ = .Typ := by
  intro Γ T0 T' as us hs
  induction hs with
  | nil =>
    intro a r pn fn ps Tw hw hc j hj
    cases j <;> rfl
  | @live T0' A B x ux as' T'' us' hc0 hx hrest ih =>
    intro a r pn fn ps Tw hw hc j hj
    cases pn with
    | zero => omega
    | succ pk =>
      obtain ⟨K, Bw, hTw, hw'⟩ := WTele.param (x := x) hw
      subst hTw
      exact absurd (Conv.all_inj (Conv.trans hβ (Conv.symm hc0)
        (Conv.symm hc))).1 (by intro h; cases h)
  | @dead T0' A B x πx as' T'' us' hc0 hchk hrest ih =>
    intro a r pn fn ps Tw hw hc j hj
    cases pn with
    | zero => omega
    | succ pk =>
      cases j with
      | zero => rfl
      | succ j' =>
        obtain ⟨K, Bw, hTw, hw'⟩ := WTele.param (x := x) hw
        subst hTw
        have hall := Conv.all_inj (Conv.trans hβ hc hc0)
        exact ih hw' (Conv.subst hβ hall.2.2 (Conv.refl x) 0) j'
          (by omega)

-- the paired field walks: each compared field rides with its erasure
-- arm; live arms recurse through the paired verdict, dead arms fall
-- back to the token-free descent
theorem PEqs.deepp : ∀ {xs ys : List Term}, PEqs β xs ys →
    ∀ {Γ : Ctx} {T0 T' : Term} {toks : List Term},
    EraSpine β Γ T0 xs T' toks →
    (∀ y ∈ ys, ∀ t, PEq β t y →
      (Term.msubstAt dd env y).Closed 0 →
      ∀ {Γ' : Ctx} {A utok : Term}, Era β Γ' t A utok →
      PinOk β (Term.msubstAt dd env t) (Term.msubstAt dd uenv utok)) →
    (∀ y ∈ ys, ∀ t, PEq β t y →
      (Term.msubstAt dd env y).Closed 0 →
      PinOk β (Term.msubstAt dd env t) .Typ) →
    (∀ y ∈ ys, (Term.msubstAt dd env y).Closed 0) →
    ∀ p ∈ (xs.map (Term.msubstAt dd env)).zip
        (toks.map (Term.msubstAt dd uenv)), PinOk β p.1 p.2 := by
  intro xs
  induction xs with
  | nil =>
    intro ys h Γ T0 T' toks hsp hIHe hIHT hcl p hp
    exact nomatch hp
  | cons x0 xs ih =>
    intro ys h Γ T0 T' toks hsp hIHe hIHT hcl p hp
    cases h with
    | @cons _ y _ ys' hxy hrest =>
      cases hsp with
      | @live _ A B _ ux _ _ toks' hc0 hx hrest2 =>
        simp only [List.map, List.zip_cons_cons] at hp
        rcases List.mem_cons.mp hp with h1 | h2
        · subst h1
          exact hIHe y List.mem_cons_self x0 hxy
            (hcl y List.mem_cons_self) hx
        · exact ih hrest hrest2
            (fun y' hy' => hIHe y' (List.mem_cons_of_mem y hy'))
            (fun y' hy' => hIHT y' (List.mem_cons_of_mem y hy'))
            (fun y' hy' => hcl y' (List.mem_cons_of_mem y hy')) p h2
      | @dead _ A B _ πx _ _ toks' hc0 hchk hrest2 =>
        simp only [List.map, List.zip_cons_cons] at hp
        rcases List.mem_cons.mp hp with h1 | h2
        · subst h1
          show PinOk β (Term.msubstAt dd env x0) (Term.msubstAt dd uenv .Typ)
          rw [Term.msubstAt_typ]
          exact hIHT y List.mem_cons_self x0 hxy
            (hcl y List.mem_cons_self)
        · exact ih hrest hrest2
            (fun y' hy' => hIHe y' (List.mem_cons_of_mem y hy'))
            (fun y' hy' => hIHT y' (List.mem_cons_of_mem y hy'))
            (fun y' hy' => hcl y' (List.mem_cons_of_mem y hy')) p h2

theorem PLes.deepp : ∀ {xs ys : List Term}, PLes β xs ys →
    ∀ {Γ : Ctx} {T0 T' : Term} {toks : List Term},
    EraSpine β Γ T0 xs T' toks →
    (∀ y ∈ ys, ∀ t, PEq β t y →
      (Term.msubstAt dd env y).Closed 0 →
      ∀ {Γ' : Ctx} {A utok : Term}, Era β Γ' t A utok →
      PinOk β (Term.msubstAt dd env t) (Term.msubstAt dd uenv utok)) →
    (∀ y ∈ ys, ∀ t, PLt β t y →
      (Term.msubstAt dd env y).Closed 0 →
      ∀ {Γ' : Ctx} {A utok : Term}, Era β Γ' t A utok →
      PinOk β (Term.msubstAt dd env t) (Term.msubstAt dd uenv utok)) →
    (∀ y ∈ ys, ∀ t, PEq β t y →
      (Term.msubstAt dd env y).Closed 0 →
      PinOk β (Term.msubstAt dd env t) .Typ) →
    (∀ y ∈ ys, ∀ t, PLt β t y →
      (Term.msubstAt dd env y).Closed 0 →
      PinOk β (Term.msubstAt dd env t) .Typ) →
    (∀ y ∈ ys, (Term.msubstAt dd env y).Closed 0) →
    ∀ p ∈ (xs.map (Term.msubstAt dd env)).zip
        (toks.map (Term.msubstAt dd uenv)), PinOk β p.1 p.2 := by
  intro xs
  induction xs with
  | nil =>
    intro ys h Γ T0 T' toks hsp hIHe hIHl hIHTe hIHTl hcl p hp
    exact nomatch hp
  | cons x0 xs ih =>
    intro ys h Γ T0 T' toks hsp hIHe hIHl hIHTe hIHTl hcl p hp
    cases h with
    | @consEq _ y _ ys' hxy hrest =>
      cases hsp with
      | @live _ A B _ ux _ _ toks' hc0 hx hrest2 =>
        simp only [List.map, List.zip_cons_cons] at hp
        rcases List.mem_cons.mp hp with h1 | h2
        · subst h1
          exact hIHe y List.mem_cons_self x0 hxy
            (hcl y List.mem_cons_self) hx
        · exact ih hrest hrest2
            (fun y' hy' => hIHe y' (List.mem_cons_of_mem y hy'))
            (fun y' hy' => hIHl y' (List.mem_cons_of_mem y hy'))
            (fun y' hy' => hIHTe y' (List.mem_cons_of_mem y hy'))
            (fun y' hy' => hIHTl y' (List.mem_cons_of_mem y hy'))
            (fun y' hy' => hcl y' (List.mem_cons_of_mem y hy')) p h2
      | @dead _ A B _ πx _ _ toks' hc0 hchk hrest2 =>
        simp only [List.map, List.zip_cons_cons] at hp
        rcases List.mem_cons.mp hp with h1 | h2
        · subst h1
          show PinOk β (Term.msubstAt dd env x0) (Term.msubstAt dd uenv .Typ)
          rw [Term.msubstAt_typ]
          exact hIHTe y List.mem_cons_self x0 hxy
            (hcl y List.mem_cons_self)
        · exact ih hrest hrest2
            (fun y' hy' => hIHe y' (List.mem_cons_of_mem y hy'))
            (fun y' hy' => hIHl y' (List.mem_cons_of_mem y hy'))
            (fun y' hy' => hIHTe y' (List.mem_cons_of_mem y hy'))
            (fun y' hy' => hIHTl y' (List.mem_cons_of_mem y hy'))
            (fun y' hy' => hcl y' (List.mem_cons_of_mem y hy')) p h2
    | @consLt _ y _ ys' hxy hrest =>
      cases hsp with
      | @live _ A B _ ux _ _ toks' hc0 hx hrest2 =>
        simp only [List.map, List.zip_cons_cons] at hp
        rcases List.mem_cons.mp hp with h1 | h2
        · subst h1
          exact hIHl y List.mem_cons_self x0 hxy
            (hcl y List.mem_cons_self) hx
        · exact ih hrest hrest2
            (fun y' hy' => hIHe y' (List.mem_cons_of_mem y hy'))
            (fun y' hy' => hIHl y' (List.mem_cons_of_mem y hy'))
            (fun y' hy' => hIHTe y' (List.mem_cons_of_mem y hy'))
            (fun y' hy' => hIHTl y' (List.mem_cons_of_mem y hy'))
            (fun y' hy' => hcl y' (List.mem_cons_of_mem y hy')) p h2
      | @dead _ A B _ πx _ _ toks' hc0 hchk hrest2 =>
        simp only [List.map, List.zip_cons_cons] at hp
        rcases List.mem_cons.mp hp with h1 | h2
        · subst h1
          show PinOk β (Term.msubstAt dd env x0) (Term.msubstAt dd uenv .Typ)
          rw [Term.msubstAt_typ]
          exact hIHTl y List.mem_cons_self x0 hxy
            (hcl y List.mem_cons_self)
        · exact ih hrest hrest2
            (fun y' hy' => hIHe y' (List.mem_cons_of_mem y hy'))
            (fun y' hy' => hIHl y' (List.mem_cons_of_mem y hy'))
            (fun y' hy' => hIHTe y' (List.mem_cons_of_mem y hy'))
            (fun y' hy' => hIHTl y' (List.mem_cons_of_mem y hy'))
            (fun y' hy' => hcl y' (List.mem_cons_of_mem y hy')) p h2

theorem PLts.deepp : ∀ {xs ys : List Term}, PLts β xs ys →
    ∀ {Γ : Ctx} {T0 T' : Term} {toks : List Term},
    EraSpine β Γ T0 xs T' toks →
    (∀ y ∈ ys, ∀ t, PEq β t y →
      (Term.msubstAt dd env y).Closed 0 →
      ∀ {Γ' : Ctx} {A utok : Term}, Era β Γ' t A utok →
      PinOk β (Term.msubstAt dd env t) (Term.msubstAt dd uenv utok)) →
    (∀ y ∈ ys, ∀ t, PLt β t y →
      (Term.msubstAt dd env y).Closed 0 →
      ∀ {Γ' : Ctx} {A utok : Term}, Era β Γ' t A utok →
      PinOk β (Term.msubstAt dd env t) (Term.msubstAt dd uenv utok)) →
    (∀ y ∈ ys, ∀ t, PEq β t y →
      (Term.msubstAt dd env y).Closed 0 →
      PinOk β (Term.msubstAt dd env t) .Typ) →
    (∀ y ∈ ys, ∀ t, PLt β t y →
      (Term.msubstAt dd env y).Closed 0 →
      PinOk β (Term.msubstAt dd env t) .Typ) →
    (∀ y ∈ ys, (Term.msubstAt dd env y).Closed 0) →
    ∀ p ∈ (xs.map (Term.msubstAt dd env)).zip
        (toks.map (Term.msubstAt dd uenv)), PinOk β p.1 p.2 := by
  intro xs
  induction xs with
  | nil =>
    intro ys h Γ T0 T' toks hsp hIHe hIHl hIHTe hIHTl hcl p hp
    exact nomatch hp
  | cons x0 xs ih =>
    intro ys h Γ T0 T' toks hsp hIHe hIHl hIHTe hIHTl hcl p hp
    cases h with
    | @here _ y _ ys' hxy hrest =>
      cases hsp with
      | @live _ A B _ ux _ _ toks' hc0 hx hrest2 =>
        simp only [List.map, List.zip_cons_cons] at hp
        rcases List.mem_cons.mp hp with h1 | h2
        · subst h1
          exact hIHl y List.mem_cons_self x0 hxy
            (hcl y List.mem_cons_self) hx
        · exact hrest.deepp hrest2
            (fun y' hy' => hIHe y' (List.mem_cons_of_mem y hy'))
            (fun y' hy' => hIHl y' (List.mem_cons_of_mem y hy'))
            (fun y' hy' => hIHTe y' (List.mem_cons_of_mem y hy'))
            (fun y' hy' => hIHTl y' (List.mem_cons_of_mem y hy'))
            (fun y' hy' => hcl y' (List.mem_cons_of_mem y hy')) p h2
      | @dead _ A B _ πx _ _ toks' hc0 hchk hrest2 =>
        simp only [List.map, List.zip_cons_cons] at hp
        rcases List.mem_cons.mp hp with h1 | h2
        · subst h1
          show PinOk β (Term.msubstAt dd env x0) (Term.msubstAt dd uenv .Typ)
          rw [Term.msubstAt_typ]
          exact hIHTl y List.mem_cons_self x0 hxy
            (hcl y List.mem_cons_self)
        · exact hrest.deepp hrest2
            (fun y' hy' => hIHe y' (List.mem_cons_of_mem y hy'))
            (fun y' hy' => hIHl y' (List.mem_cons_of_mem y hy'))
            (fun y' hy' => hIHTe y' (List.mem_cons_of_mem y hy'))
            (fun y' hy' => hIHTl y' (List.mem_cons_of_mem y hy'))
            (fun y' hy' => hcl y' (List.mem_cons_of_mem y hy')) p h2
    | @there _ y _ ys' hxy hrest =>
      cases hsp with
      | @live _ A B _ ux _ _ toks' hc0 hx hrest2 =>
        simp only [List.map, List.zip_cons_cons] at hp
        rcases List.mem_cons.mp hp with h1 | h2
        · subst h1
          exact hIHe y List.mem_cons_self x0 hxy
            (hcl y List.mem_cons_self) hx
        · exact ih hrest hrest2
            (fun y' hy' => hIHe y' (List.mem_cons_of_mem y hy'))
            (fun y' hy' => hIHl y' (List.mem_cons_of_mem y hy'))
            (fun y' hy' => hIHTe y' (List.mem_cons_of_mem y hy'))
            (fun y' hy' => hIHTl y' (List.mem_cons_of_mem y hy'))
            (fun y' hy' => hcl y' (List.mem_cons_of_mem y hy')) p h2
      | @dead _ A B _ πx _ _ toks' hc0 hchk hrest2 =>
        simp only [List.map, List.zip_cons_cons] at hp
        rcases List.mem_cons.mp hp with h1 | h2
        · subst h1
          show PinOk β (Term.msubstAt dd env x0) (Term.msubstAt dd uenv .Typ)
          rw [Term.msubstAt_typ]
          exact hIHTe y List.mem_cons_self x0 hxy
            (hcl y List.mem_cons_self)
        · exact ih hrest hrest2
            (fun y' hy' => hIHe y' (List.mem_cons_of_mem y hy'))
            (fun y' hy' => hIHl y' (List.mem_cons_of_mem y hy'))
            (fun y' hy' => hIHTe y' (List.mem_cons_of_mem y hy'))
            (fun y' hy' => hIHTl y' (List.mem_cons_of_mem y hy'))
            (fun y' hy' => hcl y' (List.mem_cons_of_mem y hy')) p h2

-- the paired descent: a compared argument instantiates PinOk against
-- its erasure token — leaves land on the environment's settled pairs,
-- constructor nodes rebuild with dead parameter tokens
theorem descent_deepp (β : Book) (hβ : Book.Closed β) (hok : Book.Ok β)
    (dd : Nat) (env uenv : List Term)
    (henv : ∀ v ∈ env, v.Closed 0)
    (huenv : ∀ v ∈ uenv, v.Closed 0)
    (hl1 : env.length = uenv.length)
    (henvP : ∀ p ∈ env.zip uenv, p.2 = .Typ ∨ DeepP β p.1 p.2) :
    ∀ (n : Nat) (p : Term), Term.size p ≤ n →
      (∀ t, PEq β t p → (Term.msubstAt dd env p).Closed 0 →
        ∀ {Γ : Ctx} {A utok : Term}, Era β Γ t A utok →
        PinOk β (Term.msubstAt dd env t) (Term.msubstAt dd uenv utok)) ∧
      (∀ t, PLt β t p → (Term.msubstAt dd env p).Closed 0 →
        ∀ {Γ : Ctx} {A utok : Term}, Era β Γ t A utok →
        PinOk β (Term.msubstAt dd env t) (Term.msubstAt dd uenv utok)) := by
  intro n
  induction n with
  | zero =>
    intro p hp
    have := Term.size_pos p
    omega
  | succ n ih =>
    intro p hp
    have helem : ∀ {a c : Nat} {ys : List Term},
        p = Term.apps (.Ctr a c) ys → ∀ y ∈ ys, Term.size y ≤ n := by
      intro a c ys hpe y hy
      have hsp : y ∈ (Term.spine p).2 := by
        rw [hpe, Term.spine_apps (by trivial)]
        exact hy
      have := Term.size_spine_arg p y hsp
      omega
    have hfields : ∀ {a c : Nat} {ys : List Term},
        p = Term.apps (.Ctr a c) ys →
        (Term.msubstAt dd env p).Closed 0 →
        ∀ y ∈ ys, (Term.msubstAt dd env y).Closed 0 := by
      intro a c ys hpe hclp y hy
      subst hpe
      rw [Term.msubstAt_apps, Term.msubstAt_ctr] at hclp
      have := (Term.closed_apps _ _ _).mp hclp
      exact this.2 _ (List.mem_map_of_mem hy)
    have hvar : ∀ (i : Nat) {Γ : Ctx} {A utok : Term},
        Era β Γ (.Var i) A utok →
        (Term.msubstAt dd env (.Var i)).Closed 0 →
        PinOk β (Term.msubstAt dd env (.Var i))
          (Term.msubstAt dd uenv utok) := by
      intro i Γ A utok hera hcl
      have hueq := Era.var_out_inv hera
      subst hueq
      by_cases h1 : i < dd
      · rw [Term.msubstAt_var_lt dd i h1] at hcl
        exact absurd hcl (by simp [Term.Closed])
      · by_cases h2 : i - dd < env.length
        · have hie : i = dd + (i - dd) := by omega
          rw [hie, Term.msubstAt_var_hit dd env henv (i - dd) h2,
            Term.msubstAt_var_hit dd uenv huenv (i - dd) (by omega)]
          have hz := zip_getD_mem (d1 := Term.Typ) (d2 := Term.Typ)
            env uenv (i - dd) h2 (by omega)
          have hpr : uenv.getD (i - dd) .Typ = .Typ
              ∨ DeepP β (env.getD (i - dd) .Typ) (uenv.getD (i - dd) .Typ) :=
            henvP _ hz
          rcases hpr with hty | hdp
          · rw [hty]
            exact .cls (henv _ (getD_mem env (i - dd) h2))
          · exact .val (henv _ (getD_mem env (i - dd) h2))
              (huenv _ (getD_mem uenv (i - dd) (by omega))) hdp
        · rw [Term.msubstAt_var_ge dd env i (by omega)] at hcl
          exact absurd hcl (by simp [Term.Closed])
    constructor
    · intro t hpe hclp Γ A utok hera
      cases hpe with
      | var => exact hvar _ hera hclp
      | @ctr a A2 c C2 xs ys ps2 hk hc hlp hlx hpes =>
        obtain ⟨Tf, uhead, T', toks, hheadera, hspt, hcvT', hueq⟩ :=
          Era.apps_inv hβ (Eq.refl _) hera
        subst hueq
        obtain ⟨A3, C3, rr0, hA3, hC3, hrr0, hcty, huheq⟩ :=
          Era.ctr_head_inv hβ hheadera
        subst huheq
        rw [hk] at hA3
        cases hA3
        rw [hc] at hC3
        cases hC3
        have hshape := ((hok.adt_clauses hk).2.2 c C2 hc).2
        have hw := WTele.retip rr0 hshape
        have hdeadpar : ∀ j, j < A2.pn → toks.getD j .Typ = .Typ :=
          EraSpine.wtele_dead hβ hspt hw hcty
        have hlent := hspt.lengths
        obtain ⟨Tm, toks1, toks2, hsp1, hsp2, htsplit⟩ :=
          EraSpine.append_split hspt
        subst htsplit
        rw [Term.msubstAt_apps, Term.msubstAt_ctr,
          Term.msubstAt_apps, Term.msubstAt_ctr]
        refine PinOk.ctr hk hc ?_ ?_ ?_ ?_
        · simp only [List.length_map, List.length_append]
          omega
        · have e1 := hsp1.lengths
          have e2 := hsp2.lengths
          simp only [List.length_map, List.length_append] at *
          omega
        · intro t2 ht2
          obtain ⟨j, hj1, hj2, hj3⟩ := mem_take_getD .Typ _ _ t2 ht2
          rw [← hj3, map_getD (Term.msubstAt dd uenv) .Typ .Typ _ j (by
            simp only [List.length_map] at hj2
            exact hj2)]
          rw [hdeadpar j hj1]
          exact Term.msubstAt_typ dd uenv
        · have hdx : ((ps2 ++ xs).map (Term.msubstAt dd env)).drop A2.pn
              = xs.map (Term.msubstAt dd env) := by
            rw [List.map_append]
            rw [show A2.pn = (ps2.map (Term.msubstAt dd env)).length from by
              simp only [List.length_map]
              omega]
            exact List.drop_left
          have hdt : ((toks1 ++ toks2).map (Term.msubstAt dd uenv)).drop
              A2.pn = toks2.map (Term.msubstAt dd uenv) := by
            rw [List.map_append]
            rw [show A2.pn
                = (toks1.map (Term.msubstAt dd uenv)).length from by
              simp only [List.length_map]
              have e1 := hsp1.lengths
              omega]
            exact List.drop_left
          rw [hdx, hdt]
          refine hpes.deepp hsp2 ?_ ?_ (hfields (Eq.refl _) hclp)
          · intro y hy t' ht' hcy Γ' A' utok' hera'
            exact (ih y (helem (Eq.refl _) y hy)).1 t' ht' hcy hera'
          · intro y hy t' ht' hcy
            exact (descent_crigid β dd env henv (Term.size y) y
              (Nat.le_refl _)).1 t' ht' hcy
    · intro t hpl hclp Γ A utok hera
      cases hpl with
      | @subEq a A2 c C2 ys y _t hk hc hly hy hpe =>
        exact (ih y (helem (Eq.refl _) y hy)).1 t hpe
          (hfields (Eq.refl _) hclp y hy) hera
      | @subLt a A2 c C2 ys y _t hk hc hly hy hpl2 =>
        exact (ih y (helem (Eq.refl _) y hy)).2 t hpl2
          (hfields (Eq.refl _) hclp y hy) hera
      | @ctr a A2 c C2 xs ys ps2 hk hc hlp hlx hplts =>
        obtain ⟨Tf, uhead, T', toks, hheadera, hspt, hcvT', hueq⟩ :=
          Era.apps_inv hβ (Eq.refl _) hera
        subst hueq
        obtain ⟨A3, C3, rr0, hA3, hC3, hrr0, hcty, huheq⟩ :=
          Era.ctr_head_inv hβ hheadera
        subst huheq
        rw [hk] at hA3
        cases hA3
        rw [hc] at hC3
        cases hC3
        have hshape := ((hok.adt_clauses hk).2.2 c C2 hc).2
        have hw := WTele.retip rr0 hshape
        have hdeadpar : ∀ j, j < A2.pn → toks.getD j .Typ = .Typ :=
          EraSpine.wtele_dead hβ hspt hw hcty
        have hlent := hspt.lengths
        obtain ⟨Tm, toks1, toks2, hsp1, hsp2, htsplit⟩ :=
          EraSpine.append_split hspt
        subst htsplit
        rw [Term.msubstAt_apps, Term.msubstAt_ctr,
          Term.msubstAt_apps, Term.msubstAt_ctr]
        refine PinOk.ctr hk hc ?_ ?_ ?_ ?_
        · simp only [List.length_map, List.length_append]
          omega
        · have e1 := hsp1.lengths
          have e2 := hsp2.lengths
          simp only [List.length_map, List.length_append] at *
          omega
        · intro t2 ht2
          obtain ⟨j, hj1, hj2, hj3⟩ := mem_take_getD .Typ _ _ t2 ht2
          rw [← hj3, map_getD (Term.msubstAt dd uenv) .Typ .Typ _ j (by
            simp only [List.length_map] at hj2
            exact hj2)]
          rw [hdeadpar j hj1]
          exact Term.msubstAt_typ dd uenv
        · have hdx : ((ps2 ++ xs).map (Term.msubstAt dd env)).drop A2.pn
              = xs.map (Term.msubstAt dd env) := by
            rw [List.map_append]
            rw [show A2.pn = (ps2.map (Term.msubstAt dd env)).length from by
              simp only [List.length_map]
              omega]
            exact List.drop_left
          have hdt : ((toks1 ++ toks2).map (Term.msubstAt dd uenv)).drop
              A2.pn = toks2.map (Term.msubstAt dd uenv) := by
            rw [List.map_append]
            rw [show A2.pn
                = (toks1.map (Term.msubstAt dd uenv)).length from by
              simp only [List.length_map]
              have e1 := hsp1.lengths
              omega]
            exact List.drop_left
          rw [hdx, hdt]
          refine hplts.deepp hsp2 ?_ ?_ ?_ ?_ (hfields (Eq.refl _) hclp)
          · intro y hy t' ht' hcy Γ' A' utok' hera'
            exact (ih y (helem (Eq.refl _) y hy)).1 t' ht' hcy hera'
          · intro y hy t' ht' hcy Γ' A' utok' hera'
            exact (ih y (helem (Eq.refl _) y hy)).2 t' ht' hcy hera'
          · intro y hy t' ht' hcy
            exact (descent_crigid β dd env henv (Term.size y) y
              (Nat.le_refl _)).1 t' ht' hcy
          · intro y hy t' ht' hcy
            exact (descent_crigid β dd env henv (Term.size y) y
              (Nat.le_refl _)).2 t' ht' hcy

theorem Era.typ_out_inv (hβ : Book.Closed β) :
    ∀ {Γ : Ctx} {t T u : Term}, Era β Γ t T u →
    u = .Typ → Conv β .Typ T := by
  intro Γ t T u h
  induction h with
  | typ => intro _; exact Conv.refl _
  | refA _ _ => intro he; exact Term.noConfusion he
  | all _ _ _ => intro _; exact Conv.refl _
  | eql _ _ _ => intro _; exact Conv.refl _
  | cnv _ hc ih => intro he; exact Conv.trans hβ (ih he) hc
  | var _ => intro he; exact Term.noConfusion he
  | ref _ => intro he; exact Term.noConfusion he
  | adt _ => intro he; exact Term.noConfusion he
  | ctr _ _ _ => intro he; exact Term.noConfusion he
  | lam _ _ _ => intro he; exact Term.noConfusion he
  | app_live _ _ _ _ => intro he; exact Term.noConfusion he
  | app_dead _ _ _ => intro he; exact Term.noConfusion he
  | let_live _ _ _ _ _ => intro he; exact Term.noConfusion he
  | let_dead _ _ _ _ => intro he; exact Term.noConfusion he
  | rfl _ => intro he; exact Term.noConfusion he
  | rwt _ _ _ _ _ => intro he; exact Term.noConfusion he
  | mat _ _ _ _ _ _ _ _ _ _ _ => intro he; exact Term.noConfusion he
  | efq _ _ _ => intro he; exact Term.noConfusion he


-- walking a self-call's argument spine: each live argument prices by
-- the given contract, dead arguments are tokens; the ledgers append
-- slot-wise, the affine sum letting at most one argument use a slot
theorem call_walk (β : Book) (d : Nat) (env uenv : List Term)
    (Css : List (List Charge)) (sp : Charge) :
    ∀ {args : List Term} {Γ : Ctx} {T0 T' : Term} {us : List Term},
    EraSpine β Γ T0 args T' us →
    (∀ x ∈ args, ∀ (B' ub' : Term), Era β Γ x B' ub' →
      (∀ i, i < uenv.length → Term.occ (d + i) ub' ≤ 1) →
      ∃ (Cs : List Charge) (Crs : List (List Charge)),
        Crs.length = uenv.length ∧
        CG β (Cs ++ Crs.flatten) (Term.msubstAt d env x)
          (Term.msubstAt d uenv ub') ∧
        (∀ i, i < uenv.length → Sub (Crs.getD i []) (Css.getD i []) ∧
          (Term.occ (d + i) ub' = 0 → Crs.getD i [] = [])) ∧
        (∀ c ∈ Cs, CLt c sp)) →
    (∀ i, i < uenv.length → (us.map (Term.occ (d + i))).sum ≤ 1) →
    ∃ (Csw : List Charge) (Crsw Css_site : List (List Charge)),
      Crsw.length = uenv.length ∧
      Css_site.length = us.length ∧
      (∀ p ∈ (Css_site.zip (args.map (Term.msubstAt d env))).zip
          (us.map (Term.msubstAt d uenv)), CG β p.1.1 p.1.2 p.2) ∧
      Css_site.flatten.Perm (Csw ++ Crsw.flatten) ∧
      (∀ i, i < uenv.length → Sub (Crsw.getD i []) (Css.getD i []) ∧
        ((us.map (Term.occ (d + i))).sum = 0 → Crsw.getD i [] = [])) ∧
      (∀ c ∈ Csw, CLt c sp) := by
  intro args Γ T0 T' us hsp
  induction hsp with
  | nil =>
    intro _ _
    refine ⟨[], List.replicate uenv.length [], [], by simp, _root_.rfl,
      ?_, ?_, ?_, ?_⟩
    · intro p hp
      exact nomatch hp
    · rw [replicate_nil_flatten]
      exact List.Perm.refl _
    · intro i hi
      rw [replicate_nil_getD]
      exact ⟨Sub.nil _, fun _ => _root_.rfl⟩
    · intro c hc
      exact nomatch hc
  | @live T1 A1 B1 x1 ux1 as1 T1' us1 hc0 hx1 hrest ih =>
    intro hprice hsum
    obtain ⟨Csx, Crsx, hlenx, hcgx, hslotx, hbelowx⟩ :=
      hprice x1 List.mem_cons_self A1 ux1 hx1 (by
        intro i hi
        have := hsum i hi
        simp only [List.map, List.sum_cons] at this
        omega)
    obtain ⟨Csw, Crsw, Css_site, hlenw, hlens, hpairw, hpermw, hslotw,
        hbeloww⟩ :=
      ih (fun x hx => hprice x (List.mem_cons_of_mem x1 hx))
        (by
          intro i hi
          have := hsum i hi
          simp only [List.map, List.sum_cons] at this
          omega)
    have hll : Crsx.length = Crsw.length := by omega
    refine ⟨Csx ++ Csw, List.zipWith (· ++ ·) Crsx Crsw,
      (Csx ++ Crsx.flatten) :: Css_site, ?_, by simp [hlens], ?_, ?_, ?_, ?_⟩
    · rw [zipWith_append_length Crsx Crsw hll]
      exact hlenx
    · intro p hp
      simp only [List.map, List.zip_cons_cons] at hp
      rcases List.mem_cons.mp hp with h1 | h2
      · subst h1
        exact hcgx
      · exact hpairw p h2
    · show ((Csx ++ Crsx.flatten) ++ Css_site.flatten).Perm _
      refine List.Perm.trans
        (List.Perm.append_left _ hpermw) ?_
      refine List.Perm.trans
        (perm_interchange Csx Crsx.flatten Csw Crsw.flatten) ?_
      exact List.Perm.append_left _
        (zipWith_append_flatten Crsx Crsw hll).symm
    · intro i hi
      rw [zipWith_append_getD Crsx Crsw i hll]
      obtain ⟨hsx1, hsx2⟩ := hslotx i hi
      obtain ⟨hsw1, hsw2⟩ := hslotw i hi
      have hs := hsum i hi
      simp only [List.map, List.sum_cons] at hs
      constructor
      · by_cases hz : Term.occ (d + i) ux1 = 0
        · rw [hsx2 hz, List.nil_append]
          exact hsw1
        · have hzw : (us1.map (Term.occ (d + i))).sum = 0 := by omega
          rw [hsw2 hzw, List.append_nil]
          exact hsx1
      · intro h0
        simp only [List.map, List.sum_cons] at h0
        have hz1 : Term.occ (d + i) ux1 = 0 := by omega
        have hz2 : (us1.map (Term.occ (d + i))).sum = 0 := by omega
        rw [hsx2 hz1, hsw2 hz2]
        rfl
    · intro c hc
      rcases List.mem_append.mp hc with h1 | h2
      · exact hbelowx c h1
      · exact hbeloww c h2
  | @dead T1 A1 B1 x1 πx1 as1 T1' us1 hc0 hx1 hrest ih =>
    intro hprice hsum
    obtain ⟨Csw, Crsw, Css_site, hlenw, hlens, hpairw, hpermw, hslotw,
        hbeloww⟩ :=
      ih (fun x hx => hprice x (List.mem_cons_of_mem x1 hx))
        (by
          intro i hi
          have := hsum i hi
          simp only [List.map, List.sum_cons] at this
          omega)
    refine ⟨Csw, Crsw, [] :: Css_site, hlenw, by simp [hlens], ?_,
      by simpa using hpermw, ?_, hbeloww⟩
    · intro p hp
      simp only [List.map, List.zip_cons_cons] at hp
      rcases List.mem_cons.mp hp with h1 | h2
      · subst h1
        rw [Term.msubstAt_closed d uenv .Typ (by trivial)]
        exact .typ_
      · exact hpairw p h2
    · intro i hi
      obtain ⟨hsw1, hsw2⟩ := hslotw i hi
      refine ⟨hsw1, ?_⟩
      intro h0
      simp only [List.map, List.sum_cons] at h0
      refine hsw2 ?_
      have hz : Term.occ (d + i) Term.Typ = 0 := _root_.rfl
      omega



-- a constructor-headed spine's charges are exactly its arguments',
-- one list per argument (the head is free)
theorem CG.ctr_spine_inv : ∀ {C : List Charge} {t u : Term}, CG β C t u →
    ∀ {a c : Nat} {as us : List Term},
    t = Term.apps (.Ctr a c) as → u = Term.apps (.Ctr a c) us →
    as.length = us.length →
    ∃ Css : List (List Charge), Css.length = us.length ∧
      (∀ p ∈ (Css.zip as).zip us, CG β p.1.1 p.1.2 p.2) ∧
      Sub Css.flatten C := by
  intro C t u h
  induction h with
  | typ_ =>
    intro a c as us ht hu hlen
    rcases apps_shape us _ _ hu.symm with ⟨h1, h2⟩ | ⟨us0, ul, h1, h2⟩
    · exact Term.noConfusion h2
    · exact Term.noConfusion h2
  | var =>
    intro a c as us ht hu hlen
    rcases apps_shape us _ _ hu.symm with ⟨h1, h2⟩ | ⟨us0, ul, h1, h2⟩
    · exact Term.noConfusion h2
    · exact Term.noConfusion h2
  | refa =>
    intro a c as us ht hu hlen
    rcases apps_shape us _ _ hu.symm with ⟨h1, h2⟩ | ⟨us0, ul, h1, h2⟩
    · exact Term.noConfusion h2
    · exact Term.noConfusion h2
  | ref _ =>
    intro a c as us ht hu hlen
    rcases apps_shape us _ _ hu.symm with ⟨h1, h2⟩ | ⟨us0, ul, h1, h2⟩
    · exact Term.noConfusion h2
    · exact Term.noConfusion h2
  | @site k1 d1 xs1 us1 m1 ts1 Css1 ph1 _ _ _ _ _ _ _ _ =>
    intro a c as us ht hu hlen
    exfalso
    have h1 := Term.apps_head_inv (h := .Ref k1) (h' := .Ctr a c)
      (by trivial) (by trivial) ht
    exact Term.noConfusion h1.1
  | adt =>
    intro a c as us ht hu hlen
    rcases apps_shape us _ _ hu.symm with ⟨h1, h2⟩ | ⟨us0, ul, h1, h2⟩
    · exact Term.noConfusion h2
    · exact Term.noConfusion h2
  | ctr =>
    intro a c as us ht hu hlen
    rcases apps_shape as _ _ ht.symm with ⟨h1, h2⟩ | ⟨as0, al, h1, h2⟩
    · subst h1
      rcases apps_shape us _ _ hu.symm with ⟨h3, h4⟩ | ⟨us0, ul, h3, h4⟩
      · subst h3
        refine ⟨[], _root_.rfl, ?_, Sub.refl _⟩
        intro p hp
        exact nomatch hp
      · exact Term.noConfusion h4
    · exact Term.noConfusion h2
  | efq =>
    intro a c as us ht hu hlen
    rcases apps_shape us _ _ hu.symm with ⟨h1, h2⟩ | ⟨us0, ul, h1, h2⟩
    · exact Term.noConfusion h2
    · exact Term.noConfusion h2
  | rfl =>
    intro a c as us ht hu hlen
    rcases apps_shape us _ _ hu.symm with ⟨h1, h2⟩ | ⟨us0, ul, h1, h2⟩
    · exact Term.noConfusion h2
    · exact Term.noConfusion h2
  | lam _ _ =>
    intro a c as us ht hu hlen
    rcases apps_shape us _ _ hu.symm with ⟨h1, h2⟩ | ⟨us0, ul, h1, h2⟩
    · exact Term.noConfusion h2
    · exact Term.noConfusion h2
  | @app Ca f uf Cb x ux hf hx ihf _ =>
    intro a c as us ht hu hlen
    rcases apps_shape as _ _ ht.symm with ⟨h1, h2⟩ | ⟨as0, al, h1, h2⟩
    · exact Term.noConfusion h2
    · rcases apps_shape us _ _ hu.symm with ⟨h3, h4⟩ | ⟨us0, ul, h3, h4⟩
      · exact Term.noConfusion h4
      · subst h1
        subst h3
        cases h2
        cases h4
        obtain ⟨Css0, hlen0, hpair0, hsub0⟩ := ihf _root_.rfl _root_.rfl
          (by
            simp only [List.length_append, List.length_cons,
              List.length_nil] at hlen
            omega)
        have hlas : as0.length = us0.length := by
          simp only [List.length_append, List.length_cons,
            List.length_nil] at hlen
          omega
        refine ⟨Css0 ++ [Cb], ?_, ?_, ?_⟩
        · simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        · intro p hp
          rw [zip_append_of_len Css0 as0 [Cb] [x] (by omega),
            zip_append_of_len (Css0.zip as0) us0 ([Cb].zip [x]) [ux]
              (by simp only [List.length_zip]; omega)] at hp
          rcases List.mem_append.mp hp with h5 | h6
          · exact hpair0 p h5
          · simp only [List.zip_cons_cons, List.zip_nil_right,
              List.mem_singleton] at h6
            subst h6
            exact hx
        · rw [List.flatten_append]
          show Sub (Css0.flatten ++ (Cb ++ List.flatten [])) (Ca ++ Cb)
          rw [List.flatten_nil, List.append_nil]
          exact Sub.append hsub0 (Sub.refl Cb)
  | mat _ _ _ _ _ _ =>
    intro a c as us ht hu hlen
    rcases apps_shape us _ _ hu.symm with ⟨h1, h2⟩ | ⟨us0, ul, h1, h2⟩
    · exact Term.noConfusion h2
    · exact Term.noConfusion h2
  | rwt _ _ _ _ =>
    intro a c as us ht hu hlen
    rcases apps_shape us _ _ hu.symm with ⟨h1, h2⟩ | ⟨us0, ul, h1, h2⟩
    · exact Term.noConfusion h2
    · exact Term.noConfusion h2
  | let_ _ _ _ _ =>
    intro a c as us ht hu hlen
    rcases apps_shape us _ _ hu.symm with ⟨h1, h2⟩ | ⟨us0, ul, h1, h2⟩
    · exact Term.noConfusion h2
    · exact Term.noConfusion h2
  | pad _ hs ih =>
    intro a c as us ht hu hlen
    obtain ⟨Css0, hlen0, hpair0, hsub0⟩ := ih ht hu hlen
    exact ⟨Css0, hlen0, hpair0, hsub0.trans hs⟩

-- ============================================================================
-- METATHEORY §NL — the drive's pattern algebra. A match column is
-- rebuilt one peel at a time: the partially-built column is a PARTIAL
-- PATTERN — constructor nodes of declared arity whose leaves are
-- already-consumed closed values or HOLES, holes standing at field
-- positions in strict descending de Bruijn order (leftmost field,
-- highest var: the next value consumed always fills the highest
-- hole). Closedness and the size LEDGER (pattern size plus queued
-- sizes equals the finished column's size) ride through fills and
-- nested peels; a fill is a closed value (m = 0 holes) or a fresh
-- constructor pattern (m = fn new holes) uniformly.
-- ============================================================================

mutual
inductive PPat (β : Book) : Nat → Nat → Term → Prop
  | val  : v.Closed 0 → PPat β lo lo v
  | hole : PPat β lo (lo + 1) (.Var lo)
  | ctr  : Book.adt β a = some A → AdtD.ctr A c = some C →
           fields.length = C.fn →
           PPats β lo hi fields →
           PPat β lo hi (Term.apps (.Ctr a c) fields)
inductive PPats (β : Book) : Nat → Nat → List Term → Prop
  | nil  : PPats β lo lo []
  | cons : PPat β mid hi x → PPats β lo mid rest →
           PPats β lo hi (x :: rest)
end

theorem Term.csize_var (β : Book) (i : Nat) : Term.csize β (.Var i) = 0 := by
  rw [Term.csize]
  rfl

theorem PPats.closed_of : ∀ {xs : List Term} {lo hi : Nat}, PPats β lo hi xs →
    (∀ x ∈ xs, ∀ {lo' hi' : Nat}, PPat β lo' hi' x →
      lo' ≤ hi' ∧ x.Closed hi') →
    lo ≤ hi ∧ ∀ x ∈ xs, x.Closed hi := by
  intro xs
  induction xs with
  | nil =>
    intro lo hi h _
    cases h
    exact ⟨Nat.le_refl _, fun x hx => nomatch hx⟩
  | cons y ys ih =>
    intro lo hi h hIH
    cases h with
    | @cons mid _ _ _ _ hy hys =>
      obtain ⟨h1, h2⟩ := hIH y List.mem_cons_self hy
      obtain ⟨h3, h4⟩ := ih hys
        (fun x hx => hIH x (List.mem_cons_of_mem y hx))
      refine ⟨by omega, ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with h5 | h6
      · subst h5
        exact h2
      · exact Term.Closed.mono x mid hi (h4 x h6) (by omega)

theorem PPat.closed (β : Book) : ∀ (n : Nat) (T : Term), Term.size T ≤ n →
    ∀ {lo hi : Nat}, PPat β lo hi T → lo ≤ hi ∧ T.Closed hi := by
  intro n
  induction n with
  | zero =>
    intro T hT
    have := Term.size_pos T
    omega
  | succ n ih =>
    intro T hT lo hi hp
    cases hp with
    | val hv =>
      exact ⟨Nat.le_refl _, Term.Closed.mono _ 0 _ hv (Nat.zero_le _)⟩
    | hole =>
      refine ⟨by omega, ?_⟩
      show lo < lo + 1
      omega
    | @ctr a A c C _ _ fields hk hc hlen hps =>
      have helem : ∀ y ∈ fields, Term.size y ≤ n := by
        intro y hy
        have hsp : y ∈ (Term.spine (Term.apps (.Ctr a c) fields)).2 := by
          rw [Term.spine_apps (by trivial)]
          exact hy
        have := Term.size_spine_arg _ y hsp
        omega
      obtain ⟨h1, h2⟩ := hps.closed_of
        (fun x hx => ih x (helem x hx))
      refine ⟨h1, ?_⟩
      rw [Term.closed_apps]
      exact ⟨trivial, h2⟩

theorem PPat.le (hp : PPat β lo hi T) : lo ≤ hi :=
  (PPat.closed β (Term.size T) T (Nat.le_refl _) hp).1

theorem PPat.closed_out (hp : PPat β lo hi T) : T.Closed hi :=
  (PPat.closed β (Term.size T) T (Nat.le_refl _) hp).2

theorem PPats.zero_of : ∀ {xs : List Term} {lo : Nat}, PPats β lo lo xs →
    (∀ x ∈ xs, ∀ {lo' : Nat}, PPat β lo' lo' x → x.Closed 0) →
    ∀ x ∈ xs, x.Closed 0 := by
  intro xs
  induction xs with
  | nil => intro lo h _ x hx; exact nomatch hx
  | cons y ys ih =>
    intro lo h hIH x hx
    cases h with
    | @cons mid _ _ _ _ hy hys =>
      have hm1 : mid ≤ lo := hy.le
      have hm2 : lo ≤ mid := (hys.closed_of (fun x' hx' =>
        PPat.closed β (Term.size x') x' (Nat.le_refl _))).1
      have hme : mid = lo := by omega
      subst hme
      rcases List.mem_cons.mp hx with h5 | h6
      · subst h5
        exact hIH x List.mem_cons_self hy
      · exact ih hys (fun z hz => hIH z (List.mem_cons_of_mem y hz)) x h6

-- a hole-free pattern is a closed value skeleton
theorem PPat.closed_zero (β : Book) : ∀ (n : Nat) (T : Term),
    Term.size T ≤ n → ∀ {lo : Nat}, PPat β lo lo T → T.Closed 0 := by
  intro n
  induction n with
  | zero =>
    intro T hT
    have := Term.size_pos T
    omega
  | succ n ih =>
    intro T hT lo hp
    generalize he : lo = hi at hp
    cases hp with
    | val hv => exact hv
    | @ctr a A c C _ _ fields hk hc hlen hps =>
      have helem : ∀ y ∈ fields, Term.size y ≤ n := by
        intro y hy
        have hsp : y ∈ (Term.spine (Term.apps (.Ctr a c) fields)).2 := by
          rw [Term.spine_apps (by trivial)]
          exact hy
        have := Term.size_spine_arg _ y hsp
        omega
      subst he
      rw [Term.closed_apps]
      refine ⟨trivial, ?_⟩
      exact hps.zero_of (fun x hx {lo'} hp' => ih x (helem x hx) hp')


-- filling the highest hole — with a closed value (m = 0) or a fresh
-- fn-hole constructor pattern (m = fn) — moves the ceiling down and
-- opens the new holes in its place
theorem PPats.fill_of {m : Nat} {u : Term} :
    ∀ {xs : List Term} {lo hi : Nat}, PPats β lo hi xs → lo < hi →
    (∀ x ∈ xs, ∀ {lo' : Nat}, PPat β lo' hi x → lo' < hi →
      PPat β lo' (hi - 1 + m) (Term.subst (hi - 1) u x)) →
    PPats β lo (hi - 1 + m) (xs.map (Term.subst (hi - 1) u)) := by
  intro xs
  induction xs with
  | nil =>
    intro lo hi h hlt _
    cases h
    omega
  | cons y ys ih =>
    intro lo hi h hlt hIH
    cases h with
    | @cons mid _ _ _ _ hy hys =>
      by_cases hcm : mid < hi
      · -- the hole is in the head; the tail is below and untouched
        have hy' := hIH y List.mem_cons_self hy hcm
        have hrest : ys.map (Term.subst (hi - 1) u) = ys := by
          have hcl := (hys.closed_of (fun x hx =>
            PPat.closed β (Term.size x) x (Nat.le_refl _))).2
          refine List.map_congr_left ?_ |>.trans (List.map_id ys)
          intro z hz
          exact Term.subst_closed z mid (hi - 1) u (hcl z hz) (by omega)
        simp only [List.map]
        rw [hrest]
        exact PPats.cons hy' hys
      · -- head is hole-free; recurse into the tail
        have hme : mid = hi := by
          have := hy.le
          omega
        subst hme
        have hyc : y.Closed 0 :=
          PPat.closed_zero β (Term.size y) y (Nat.le_refl _) hy
        have hy' : Term.subst (mid - 1) u y = y :=
          Term.subst_closed y 0 (mid - 1) u hyc (Nat.zero_le _)
        simp only [List.map]
        rw [hy']
        exact PPats.cons (PPat.val (lo := mid - 1 + m) hyc)
          (ih hys hlt (fun x hx => hIH x (List.mem_cons_of_mem y hx)))

theorem PPat.fill (β : Book) : ∀ (n : Nat) (T : Term), Term.size T ≤ n →
    ∀ {lo hi : Nat}, PPat β lo hi T → lo < hi →
    ∀ {m : Nat} {u : Term}, PPat β (hi - 1) (hi - 1 + m) u →
    PPat β lo (hi - 1 + m) (Term.subst (hi - 1) u T) := by
  intro n
  induction n with
  | zero =>
    intro T hT
    have := Term.size_pos T
    omega
  | succ n ih =>
    intro T hT lo hi hp hlt m u hu
    cases hp with
    | val hv => omega
    | hole =>
      show PPat β lo (lo + 1 - 1 + m) (Term.subst (lo + 1 - 1) u (.Var lo))
      simp only [Nat.add_sub_cancel]
      simp only [Term.subst, if_true]
      simpa using hu
    | @ctr a A c C _ _ fields hk hc hlen hps =>
      have helem : ∀ y ∈ fields, Term.size y ≤ n := by
        intro y hy
        have hsp : y ∈ (Term.spine (Term.apps (.Ctr a c) fields)).2 := by
          rw [Term.spine_apps (by trivial)]
          exact hy
        have := Term.size_spine_arg _ y hsp
        omega
      rw [Term.subst_apps]
      show PPat β lo (hi - 1 + m)
        (Term.apps (Term.subst (hi - 1) u (.Ctr a c))
          (fields.map (Term.subst (hi - 1) u)))
      simp only [Term.subst]
      refine PPat.ctr hk hc ?_ ?_
      · simp only [List.length_map]
        exact hlen
      · exact hps.fill_of hlt
          (fun x hx {lo'} hp' hlt' => ih x (helem x hx) hp' hlt' hu)

theorem PPats.csize_of {u : Term} :
    ∀ {xs : List Term} {lo hi : Nat}, PPats β lo hi xs → lo < hi →
    (∀ x ∈ xs, ∀ {lo' : Nat}, PPat β lo' hi x → lo' < hi →
      Term.csize β (Term.subst (hi - 1) u x)
        = Term.csize β x + Term.csize β u) →
    ((xs.map (Term.subst (hi - 1) u)).map (Term.csize β)).sum
      = ((xs.map (Term.csize β)).sum) + Term.csize β u := by
  intro xs
  induction xs with
  | nil =>
    intro lo hi h hlt _
    cases h
    omega
  | cons y ys ih =>
    intro lo hi h hlt hIH
    cases h with
    | @cons mid _ _ _ _ hy hys =>
      by_cases hcm : mid < hi
      · have hy' := hIH y List.mem_cons_self hy hcm
        have hrest : ys.map (Term.subst (hi - 1) u) = ys := by
          have hcl := (hys.closed_of (fun x hx =>
            PPat.closed β (Term.size x) x (Nat.le_refl _))).2
          refine List.map_congr_left ?_ |>.trans (List.map_id ys)
          intro z hz
          exact Term.subst_closed z mid (hi - 1) u (hcl z hz) (by omega)
        simp only [List.map, List.sum_cons]
        rw [hrest, hy']
        omega
      · have hme : mid = hi := by
          have := hy.le
          omega
        subst hme
        have hyc : y.Closed 0 :=
          PPat.closed_zero β (Term.size y) y (Nat.le_refl _) hy
        have hy' : Term.subst (mid - 1) u y = y :=
          Term.subst_closed y 0 (mid - 1) u hyc (Nat.zero_le _)
        simp only [List.map, List.sum_cons]
        rw [hy']
        rw [ih hys hlt (fun x hx => hIH x (List.mem_cons_of_mem y hx))]
        omega

theorem PPat.csize_fill (β : Book) : ∀ (n : Nat) (T : Term),
    Term.size T ≤ n →
    ∀ {lo hi : Nat}, PPat β lo hi T → lo < hi → ∀ (u : Term),
    Term.csize β (Term.subst (hi - 1) u T)
      = Term.csize β T + Term.csize β u := by
  intro n
  induction n with
  | zero =>
    intro T hT
    have := Term.size_pos T
    omega
  | succ n ih =>
    intro T hT lo hi hp hlt u
    cases hp with
    | val hv => omega
    | hole =>
      show Term.csize β (Term.subst (lo + 1 - 1) u (.Var lo)) = _
      simp only [Nat.add_sub_cancel]
      simp only [Term.subst, if_true]
      rw [Term.csize_var]
      omega
    | @ctr a A c C _ _ fields hk hc hlen hps =>
      have helem : ∀ y ∈ fields, Term.size y ≤ n := by
        intro y hy
        have hsp : y ∈ (Term.spine (Term.apps (.Ctr a c) fields)).2 := by
          rw [Term.spine_apps (by trivial)]
          exact hy
        have := Term.size_spine_arg _ y hsp
        omega
      rw [Term.subst_apps]
      simp only [Term.subst]
      rw [Term.csize_fields hk hc _ (by simp only [List.length_map]; exact hlen)]
      rw [Term.csize_fields hk hc _ hlen]
      rw [hps.csize_of hlt
        (fun x hx {lo'} hp' hlt' => ih x (helem x hx) hp' hlt' u)]
      omega


-- the lams / shiftN / environment commutations: the lhs algebra's
-- binder blocks against the drive's closed-value environment
theorem Term.lams_append : ∀ (a b : Nat) (M : Term),
    Term.lams a (Term.lams b M) = Term.lams (a + b) M := by
  intro a
  induction a with
  | zero =>
    intro b M
    show Term.lams b M = Term.lams (0 + b) M
    rw [Nat.zero_add]
  | succ a ih =>
    intro b M
    show Term.Lam (Term.lams a (Term.lams b M)) = _
    rw [ih]
    show Term.lams (a + b + 1) M = Term.lams (a + 1 + b) M
    rw [show a + b + 1 = a + 1 + b from by omega]

theorem Term.lams_closed : ∀ (j n : Nat) (M : Term),
    M.Closed (n + j) → (Term.lams j M).Closed n := by
  intro j
  induction j with
  | zero =>
    intro n M h
    exact h
  | succ j ih =>
    intro n M h
    show (Term.lams j M).Closed (n + 1)
    exact ih (n + 1) M (by
      rw [show n + 1 + j = n + (j + 1) from by omega]
      exact h)

theorem Term.shiftN_shift : ∀ (n : Nat) (t : Term),
    Term.shiftN n (Term.shift 0 t) = Term.shift 0 (Term.shiftN n t) := by
  intro n
  induction n with
  | zero => intro t; rfl
  | succ n ih =>
    intro t
    show Term.shift 0 (Term.shiftN n (Term.shift 0 t)) = _
    rw [ih t]
    rfl

theorem Term.shift_lams : ∀ (j : Nat) (d : Nat) (M : Term),
    Term.shift d (Term.lams j M) = Term.lams j (Term.shift (d + j) M) := by
  intro j
  induction j with
  | zero => intro d M; rfl
  | succ j ih =>
    intro d M
    show Term.Lam (Term.shift (d + 1) (Term.lams j M)) = _
    rw [ih (d + 1) M]
    rw [show d + 1 + j = d + (j + 1) from by omega]
    rfl

theorem Term.subst_lams_open : ∀ (j : Nat) (d : Nat) (x M : Term),
    Term.subst d x (Term.lams j M)
      = Term.lams j (Term.subst (d + j) (Term.shiftN j x) M) := by
  intro j
  induction j with
  | zero => intro d x M; rfl
  | succ j ih =>
    intro d x M
    show Term.Lam (Term.subst (d + 1) (Term.shift 0 x) (Term.lams j M)) = _
    rw [ih (d + 1) (Term.shift 0 x) M]
    show Term.lams (j + 1) (Term.subst (d + 1 + j)
      (Term.shiftN j (Term.shift 0 x)) M) = _
    rw [Term.shiftN_shift j x]
    rw [show d + 1 + j = d + (j + 1) from by omega]
    rfl

theorem Term.subst_lams (j d : Nat) (x M : Term) (hx : x.Closed 0) :
    Term.subst d x (Term.lams j M)
      = Term.lams j (Term.subst (d + j) x M) := by
  rw [Term.subst_lams_open]
  rw [Term.shiftN_closed hx j]

theorem Term.msubstAt_lams (d : Nat) : ∀ (vs : List Term),
    (∀ v ∈ vs, v.Closed 0) → ∀ (j : Nat) (M : Term),
    Term.msubstAt d vs (Term.lams j M)
      = Term.lams j (Term.msubstAt (d + j) vs M) := by
  intro vs
  induction vs with
  | nil => intro _ j M; rfl
  | cons v vs ih =>
    intro hcl j M
    show Term.msubstAt d vs (Term.subst d v (Term.lams j M)) = _
    rw [Term.subst_lams j d v M (hcl v List.mem_cons_self)]
    exact ih (fun v' hv' => hcl v' (List.mem_cons_of_mem v hv')) j _

theorem Term.msubstAt_closed_at (d : Nat) : ∀ (vs : List Term) (t : Term),
    t.Closed d → Term.msubstAt d vs t = t := by
  intro vs
  induction vs with
  | nil => intro t _; rfl
  | cons v vs ih =>
    intro t ht
    show Term.msubstAt d vs (Term.subst d v t) = t
    rw [Term.subst_closed t d d v ht (Nat.le_refl d)]
    exact ih t ht

theorem Term.msubstAt_shiftN : ∀ (n d : Nat) (vs : List Term),
    (∀ v ∈ vs, v.Closed 0) → ∀ (t : Term),
    Term.msubstAt (d + n) vs (Term.shiftN n t)
      = Term.shiftN n (Term.msubstAt d vs t) := by
  intro n
  induction n with
  | zero => intro d vs _ t; rfl
  | succ n ih =>
    intro d vs hcl t
    show Term.msubstAt (d + n + 1) vs (Term.shift 0 (Term.shiftN n t)) = _
    rw [Term.msubstAt_shift (d + n) vs hcl (Term.shiftN n t)]
    rw [ih d vs hcl t]
    rfl

theorem Term.msubstAt_subst (e : Nat) : ∀ (d : Nat) (vs : List Term),
    (∀ v ∈ vs, v.Closed 0) → ∀ (x M : Term), x.Closed d → e ≤ d →
    Term.msubstAt d vs (Term.subst e x M)
      = Term.subst e x (Term.msubstAt (d + 1) vs M) := by
  intro d vs
  induction vs with
  | nil => intro _ x M _ _; rfl
  | cons w vs ih =>
    intro hcl x M hx hed
    show Term.msubstAt d vs (Term.subst d w (Term.subst e x M)) = _
    have hcomm : Term.subst d w (Term.subst e x M)
        = Term.subst e x (Term.subst (d + 1) w M) := by
      have h := Term.subst_subst M d e w x hed
      rw [Term.subst_closed x d d w hx (Nat.le_refl d)] at h
      rw [Term.shift_closed w 0 e (hcl w List.mem_cons_self)
        (Nat.zero_le e)] at h
      exact h
    rw [hcomm]
    show Term.msubstAt d vs (Term.subst e x (Term.subst (d + 1) w M)) = _
    rw [ih (fun v' hv' => hcl v' (List.mem_cons_of_mem w hv')) x _ hx hed]
    rfl

theorem Term.msubstAt_applyB_at (d : Nat) (vs : List Term)
    (hcl : ∀ v ∈ vs, v.Closed 0) (X Y : Term) (hY : Y.Closed d)
    (hsh : (∃ L, X = .Lam L) ∨ ((∀ L, X ≠ .Lam L) ∧
      (∀ L, Term.msubstAt d vs X ≠ .Lam L))) :
    Term.msubstAt d vs (Term.applyB X Y)
      = Term.applyB (Term.msubstAt d vs X) (Term.msubstAt d vs Y) := by
  rcases hsh with ⟨L, rfl⟩ | ⟨h1, h2⟩
  · show Term.msubstAt d vs (Term.subst 0 Y L) = _
    rw [Term.msubstAt_subst 0 d vs hcl Y L hY (Nat.zero_le d)]
    rw [Term.msubstAt_closed_at d vs Y hY]
    rw [Term.msubstAt_lam d vs hcl]
    rfl
  · rw [Term.applyB_not_lam X Y h1]
    rw [Term.msubstAt_app]
    rw [Term.applyB_not_lam _ _ h2]


theorem Term.shiftN_var : ∀ (d i : Nat),
    Term.shiftN d (.Var i) = .Var (i + d) := by
  intro d
  induction d with
  | zero => intro i; rfl
  | succ d ih =>
    intro i
    show Term.shift 0 (Term.shiftN d (.Var i)) = _
    rw [ih i]
    show Term.Var (i + d + 1) = _
    rfl

theorem Term.shiftN_apps : ∀ (d : Nat) (h : Term) (as : List Term),
    Term.shiftN d (Term.apps h as)
      = Term.apps (Term.shiftN d h) (as.map (Term.shiftN d)) := by
  intro d
  induction d with
  | zero =>
    intro h as
    show Term.apps h as = Term.apps h (as.map (fun t => t))
    rw [show as.map (fun t => t) = as from List.map_id as]
  | succ d ih =>
    intro h as
    show Term.shift 0 (Term.shiftN d (Term.apps h as)) = _
    rw [ih h as, Term.shift_apps]
    show Term.apps _ ((as.map (Term.shiftN d)).map (Term.shift 0)) = _
    rw [List.map_map]
    rfl

theorem Term.shiftN_ctr (d : Nat) (a c : Nat) :
    Term.shiftN d (.Ctr a c) = .Ctr a c := by
  induction d with
  | zero => rfl
  | succ d ih =>
    show Term.shift 0 (Term.shiftN d (.Ctr a c)) = _
    rw [ih]
    rfl

theorem Term.rvars_length : ∀ (n : Nat), (Term.rvars n).length = n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    show (Term.rvars n).length + 1 = n + 1
    rw [ih]

theorem Term.rvars_mem : ∀ (n : Nat), ∀ x ∈ Term.rvars n,
    ∃ i, i < n ∧ x = .Var i := by
  intro n
  induction n with
  | zero => intro x hx; exact nomatch hx
  | succ n ih =>
    intro x hx
    rcases List.mem_cons.mp hx with h1 | h2
    · exact ⟨n, by omega, h1⟩
    · obtain ⟨i, hi, he⟩ := ih x h2
      exact ⟨i, by omega, he⟩

-- the fresh pattern for a peel at depth d: holes d .. d + fn - 1
theorem rvars_ppats (β : Book) : ∀ (fn d : Nat),
    PPats β d (d + fn) ((Term.rvars fn).map (Term.shiftN d)) := by
  intro fn
  induction fn with
  | zero => intro d; exact .nil
  | succ fn ih =>
    intro d
    show PPats β d (d + (fn + 1))
      (Term.shiftN d (.Var fn) :: (Term.rvars fn).map (Term.shiftN d))
    rw [Term.shiftN_var d fn]
    refine PPats.cons ?_ (ih d)
    rw [show fn + d = d + fn from by omega,
      show d + (fn + 1) = (d + fn) + 1 from by omega]
    exact PPat.hole

theorem peel_pattern_ppat (β : Book) {a c : Nat} {A : AdtD} {C : CtrD}
    (hk : Book.adt β a = some A) (hc : AdtD.ctr A c = some C)
    (d : Nat) :
    PPat β d (d + C.fn)
      (Term.shiftN d (Term.apps (.Ctr a c) (Term.rvars C.fn))) := by
  rw [Term.shiftN_apps, Term.shiftN_ctr]
  refine PPat.ctr hk hc ?_ ?_
  · rw [List.length_map, Term.rvars_length]
  · exact rvars_ppats β C.fn d

theorem peel_pattern_csize (β : Book) {a c : Nat} {A : AdtD} {C : CtrD}
    (hk : Book.adt β a = some A) (hc : AdtD.ctr A c = some C)
    (d : Nat) :
    Term.csize β (Term.shiftN d (Term.apps (.Ctr a c) (Term.rvars C.fn)))
      = 1 := by
  rw [Term.shiftN_apps, Term.shiftN_ctr]
  rw [Term.csize_fields hk hc _ (by rw [List.length_map, Term.rvars_length])]
  have hz : ∀ x ∈ (Term.rvars C.fn).map (Term.shiftN d),
      Term.csize β x = 0 := by
    intro x hx
    obtain ⟨x0, hx0, hxe⟩ := List.mem_map.mp hx
    obtain ⟨i, _, he⟩ := Term.rvars_mem C.fn x0 hx0
    subst hxe
    subst he
    rw [Term.shiftN_var, Term.csize_var]
  have hgen : ∀ (l : List Term), (∀ x ∈ l, Term.csize β x = 0) →
      (l.map (Term.csize β)).sum = 0 := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons y ys ihy =>
      intro hz'
      simp only [List.map, List.sum_cons]
      rw [hz' y List.mem_cons_self,
        ihy (fun x hx => hz' x (List.mem_cons_of_mem y hx))]
  rw [hgen _ hz]

theorem peel_pattern_closed : ∀ (fn d : Nat) {a c : Nat},
    (Term.shiftN d (Term.apps (.Ctr a c) (Term.rvars fn))).Closed (d + fn) := by
  intro fn d a c
  rw [Term.shiftN_apps, Term.shiftN_ctr]
  rw [Term.closed_apps]
  refine ⟨trivial, ?_⟩
  intro x hx
  obtain ⟨x0, hx0, hxe⟩ := List.mem_map.mp hx
  obtain ⟨i, hi, he⟩ := Term.rvars_mem fn x0 hx0
  subst hxe
  subst he
  rw [Term.shiftN_var]
  show i + d < d + fn
  omega

theorem Term.shiftN_not_lam (t : Term) (d : Nat) (h : ∀ L, t ≠ .Lam L) :
    ∀ L, Term.shiftN d t ≠ .Lam L := by
  induction d with
  | zero => exact h
  | succ d ih =>
    show ∀ L, Term.shift 0 (Term.shiftN d t) ≠ .Lam L
    exact Term.shift_not_lam _ 0 ih

-- L-lam: a binder consumed on the instantiated side fills the pattern's
-- highest hole
theorem drive_lam_step (I₀ T x : Term) (j : Nat)
    (hI₀ : I₀.Closed 0) (hx : x.Closed 0) :
    Term.applyB (Term.lams (j + 1) (.App I₀ T)) x
      = Term.lams j (.App I₀ (Term.subst j x T)) := by
  show Term.subst 0 x (Term.lams j (.App I₀ T)) = _
  rw [Term.subst_lams j 0 x _ hx]
  show Term.lams j (.App (Term.subst (0 + j) x I₀)
    (Term.subst (0 + j) x T)) = _
  rw [Term.subst_closed I₀ 0 (0 + j) x hI₀ (Nat.zero_le _)]
  rw [Nat.zero_add]

-- L-peel: extending the lhs peels the highest hole into a fresh
-- constructor pattern
theorem drive_peel_step (I₀ T P : Term) (j fn : Nat)
    (hI₀ : I₀.Closed 0) (hT : T.Closed (j + 1)) :
    Term.lams fn (Term.applyB
      (Term.shiftN fn (Term.lams (j + 1) (.App I₀ T))) P)
      = Term.lams (fn + j) (.App I₀ (Term.subst j (Term.shiftN j P) T)) := by
  have hcl : (Term.lams (j + 1) (.App I₀ T)).Closed 0 := by
    refine Term.lams_closed (j + 1) 0 _ ?_
    rw [show 0 + (j + 1) = j + 1 from by omega]
    exact ⟨Term.Closed.mono I₀ 0 (j + 1) hI₀ (Nat.zero_le _), hT⟩
  rw [Term.shiftN_closed hcl fn]
  show Term.lams fn (Term.subst 0 P (Term.lams j (.App I₀ T))) = _
  rw [Term.subst_lams_open j 0 P _]
  rw [Nat.zero_add]
  show Term.lams fn (Term.lams j (.App
    (Term.subst j (Term.shiftN j P) I₀) (Term.subst j (Term.shiftN j P) T)))
    = _
  rw [Term.subst_closed I₀ 0 j _ hI₀ (Nat.zero_le _)]
  rw [Term.lams_append]

-- K2: instantiation commutes into lhsExt
theorem drive_ext_inst (dd : Nat) (env : List Term)
    (henv : ∀ v ∈ env, v.Closed 0) (lhs : Term) (a c fn : Nat)
    (hsh : (∃ L, lhs = .Lam L) ∨ ((∀ L, lhs ≠ .Lam L) ∧
      (∀ L, Term.msubstAt dd env lhs ≠ .Lam L))) :
    Term.msubstAt dd env (Term.lhsExt lhs a c fn)
      = Term.lams fn (Term.applyB
          (Term.shiftN fn (Term.msubstAt dd env lhs))
          (Term.apps (.Ctr a c) (Term.rvars fn))) := by
  show Term.msubstAt dd env (Term.lams fn (Term.applyB
    (Term.shiftN fn lhs) (Term.apps (.Ctr a c) (Term.rvars fn)))) = _
  rw [Term.msubstAt_lams dd env henv fn]
  have hP : (Term.apps (.Ctr a c) (Term.rvars fn)).Closed (dd + fn) := by
    have h := peel_pattern_closed fn 0 (a := a) (c := c)
    rw [Nat.zero_add] at h
    exact Term.Closed.mono _ fn (dd + fn) h (by omega)
  have hshiftc : Term.msubstAt (dd + fn) env (Term.shiftN fn lhs)
      = Term.shiftN fn (Term.msubstAt dd env lhs) :=
    Term.msubstAt_shiftN fn dd env henv lhs
  have hsh' : (∃ L, Term.shiftN fn lhs = .Lam L) ∨
      ((∀ L, Term.shiftN fn lhs ≠ .Lam L) ∧
       (∀ L, Term.msubstAt (dd + fn) env (Term.shiftN fn lhs)
          ≠ .Lam L)) := by
    rcases hsh with ⟨L, rfl⟩ | ⟨h1, h2⟩
    · left
      clear hP hshiftc
      induction fn with
      | zero => exact ⟨L, _root_.rfl⟩
      | succ fn ih =>
        obtain ⟨L', hL'⟩ := ih
        refine ⟨Term.shift 1 L', ?_⟩
        show Term.shift 0 (Term.shiftN fn (.Lam L)) = _
        rw [hL']
        rfl
    · right
      refine ⟨Term.shiftN_not_lam lhs fn h1, ?_⟩
      rw [hshiftc]
      exact Term.shiftN_not_lam _ fn h2
  rw [Term.msubstAt_applyB_at (dd + fn) env henv _ _ hP hsh']
  rw [Term.msubstAt_closed_at (dd + fn) env _ hP]
  rw [hshiftc]
theorem tup_below : ∀ (os : List (Option Nat)) (m : Nat)
    (tail sp : List (Option Nat)) (targets : Nat → Nat),
    os.length = m → 0 < m → sp.length = m + tail.length →
    (∀ j, j < m → sp.getD j none = none
      ∨ sp.getD j none = some (targets j)) →
    (∀ j, j < m → os.getD j none = none → sp.getD j none = none) →
    (∀ j, j < m - 1 → ∀ e, os.getD j none = some e → e = targets j) →
    (∃ e, os.getD (m - 1) none = some e ∧ e < targets (m - 1)) →
    TupLt (os ++ tail) sp := by
  intro os
  induction os with
  | nil => intro m tail sp targets hlen hm _ _ _ _ _; simp at hlen; omega
  | cons o os' ih =>
    intro m tail sp targets hlen hm hsp hcompat hmask hpre hstrict
    simp only [List.length_cons] at hlen
    cases sp with
    | nil =>
      exfalso
      simp only [List.length_nil] at hsp
      omega
    | cons s0 sp' =>
      simp only [List.length_cons] at hsp
      have hlens : (os' ++ tail).length = sp'.length := by
        simp only [List.length_append]
        omega
      cases o with
      | none =>
        have hs0 : s0 = none := hmask 0 (by omega) _root_.rfl
        subst hs0
        by_cases hm1 : m = 1
        · exfalso
          obtain ⟨e, he, _⟩ := hstrict
          rw [hm1] at he
          simp at he
        · show TupLt ((none : Option Nat) :: (os' ++ tail)) (none :: sp')
          refine LexR.tail ?_
          refine ih (m - 1) tail sp' (fun j => targets (j + 1))
            (by omega) (by omega) (by omega) ?_ ?_ ?_ ?_
          · intro j hj
            exact hcompat (j + 1) (by omega)
          · intro j hj
            exact hmask (j + 1) (by omega)
          · intro j hj
            exact hpre (j + 1) (by omega)
          · obtain ⟨e, he, hlt⟩ := hstrict
            refine ⟨e, ?_, ?_⟩
            · rw [show m - 1 - 1 = m - 2 from by omega]
              rw [show m - 1 = (m - 2) + 1 from by omega] at he
              exact he
            · show e < targets (m - 1 - 1 + 1)
              rw [show m - 1 - 1 + 1 = m - 1 from by omega]
              exact hlt
      | some e =>
        rcases hcompat 0 (by omega) with h0 | h0
        · have hs0 : s0 = none := h0
          subst hs0
          refine LexR.head ?_ hlens
          show OLt (some e) none
          trivial
        · have hs0 : s0 = some (targets 0) := h0
          subst hs0
          by_cases hm1 : m = 1
          · subst hm1
            refine LexR.head ?_ hlens
            obtain ⟨e2, he2, hlt2⟩ := hstrict
            have he2' : e = e2 := by
              injection he2
            subst he2'
            show OLt (some e) (some (targets 0))
            exact hlt2
          · have he : e = targets 0 := hpre 0 (by omega) e _root_.rfl
            rw [he]
            show TupLt (some (targets 0) :: (os' ++ tail))
              (some (targets 0) :: sp')
            refine LexR.tail ?_
            refine ih (m - 1) tail sp' (fun j => targets (j + 1))
              (by omega) (by omega) (by omega) ?_ ?_ ?_ ?_
            · intro j hj
              exact hcompat (j + 1) (by omega)
            · intro j hj
              exact hmask (j + 1) (by omega)
            · intro j hj
              exact hpre (j + 1) (by omega)
            · obtain ⟨e2, he2, hlt2⟩ := hstrict
              refine ⟨e2, ?_, ?_⟩
              · rw [show m - 1 - 1 = m - 2 from by omega]
                rw [show m - 1 = (m - 2) + 1 from by omega] at he2
                exact he2
              · show e2 < targets (m - 1 - 1 + 1)
                rw [show m - 1 - 1 + 1 = m - 1 from by omega]
                exact hlt2

-- the strict walk for suspended sites: below-or-equal on the pinned
-- prefix, free through the open region, strictly smaller at the
-- underapplication slack
theorem tup_below_slack : ∀ (os : List (Option Nat))
    (mm nfree ssite sspent : Nat)
    (sp : List (Option Nat)) (targets : Nat → Nat),
    os.length = mm →
    sp.length = mm + nfree + 1 →
    (∀ j, j < mm → sp.getD j none = none
      ∨ sp.getD j none = some (targets j)) →
    (∀ j, mm ≤ j → j < mm + nfree → sp.getD j none = none) →
    sp.getD (mm + nfree) none = some sspent →
    (∀ j, j < mm → os.getD j none = none → sp.getD j none = none) →
    (∀ j, j < mm → ∀ e, os.getD j none = some e → e ≤ targets j) →
    ssite < sspent →
    TupLt (os ++ (List.replicate nfree none ++ [some ssite]))
      sp := by
  intro os
  induction os with
  | nil =>
    intro mm nfree ssite sspent sp targets hlen hsp hcompat hfree hlast
      hmask hle hslt
    have hmm : mm = 0 := by simp at hlen; omega
    subst hmm
    clear hcompat hle hlen hmask
    induction nfree generalizing sp with
    | zero =>
      cases sp with
      | nil => simp at hsp
      | cons s0 sp' =>
        simp only [List.length_cons] at hsp
        have hsp' : sp' = [] := by
          cases sp' with
          | nil => rfl
          | cons _ _ => simp at hsp
        subst hsp'
        have hs0 : s0 = some sspent := hlast
        subst hs0
        refine LexR.head ?_ (by simp)
        show OLt (some ssite) (some sspent)
        exact hslt
    | succ nf ih2 =>
      cases sp with
      | nil => simp at hsp
      | cons s0 sp' =>
        simp only [List.length_cons] at hsp
        have hs0 : s0 = none := hfree 0 (by omega) (by omega)
        subst hs0
        show TupLt ((none : Option Nat) ::
          (List.replicate nf none ++ [some ssite])) (none :: sp')
        refine LexR.tail ?_
        refine ih2 sp' (by omega)
          (fun j h1 h2 => hfree (j + 1) (by omega) (by omega))
          ?_
        have h2 := hlast
        rw [show 0 + (nf + 1) = (0 + nf) + 1 from by omega] at h2
        exact h2
  | cons o os' ih =>
    intro mm nfree ssite sspent sp targets hlen hsp hcompat hfree hlast
      hmask hle hslt
    simp only [List.length_cons] at hlen
    cases sp with
    | nil =>
      exfalso
      simp only [List.length_nil] at hsp
      omega
    | cons s0 sp' =>
      simp only [List.length_cons] at hsp
      have hlens : (os' ++ (List.replicate nfree none
          ++ [some ssite])).length = sp'.length := by
        simp only [List.length_append,
          List.length_replicate, List.length_cons, List.length_nil]
        omega
      have hihargs : TupLt (os' ++ (List.replicate nfree none
          ++ [some ssite])) sp' :=
        ih (mm - 1) nfree ssite sspent sp'
          (fun j => targets (j + 1))
          (by omega) (by omega)
          (fun j hj => hcompat (j + 1) (by omega))
          (fun j h1 h2 => hfree (j + 1) (by omega) (by omega))
          (by
            have h2 := hlast
            rw [show mm + nfree = (mm - 1 + nfree) + 1 from by omega]
              at h2
            exact h2)
          (fun j hj => hmask (j + 1) (by omega))
          (fun j hj => hle (j + 1) (by omega))
          hslt
      cases o with
      | none =>
        have hs0 : s0 = none := hmask 0 (by omega) _root_.rfl
        subst hs0
        show TupLt ((none : Option Nat) :: (os' ++ (List.replicate
          nfree none ++ [some ssite]))) (none :: sp')
        exact LexR.tail hihargs
      | some e =>
        rcases hcompat 0 (by omega) with h0 | h0
        · have hs0 : s0 = none := h0
          subst hs0
          refine LexR.head ?_ hlens
          show OLt (some e) none
          trivial
        · have hs0 : s0 = some (targets 0) := h0
          subst hs0
          have he0 : e ≤ targets 0 := hle 0 (by omega) e _root_.rfl
          by_cases heq : e = targets 0
          · subst heq
            show TupLt (some (targets 0) :: (os'
              ++ (List.replicate nfree none ++ [some ssite])))
              (some (targets 0) :: sp')
            exact LexR.tail hihargs
          · refine LexR.head ?_ hlens
            show OLt (some e) (some (targets 0))
            show e < targets 0
            omega


-- pricing the remaining spine frames: each live argument carries its
-- supplied charges, dead arguments are tokens
theorem CG.frames : ∀ {queue : List Term} {Γ : Ctx} {T0 T' : Term} {uq : List Term},
    EraSpine β Γ T0 queue T' uq →
    ∀ {Cssq : List (List Charge)}, Cssq.length = queue.length →
    (∀ p ∈ (Cssq.zip queue).zip uq, CG β p.1.1 p.1.2 p.2) →
    ∀ {C : List Charge} {f uf : Term}, CG β C f uf →
    CG β (C ++ Cssq.flatten) (Term.apps f queue) (Term.apps uf uq) := by
  intro queue
  induction queue with
  | nil =>
    intro Γ T0 T' uq hsp Cssq hlen hpairs C f uf hcg
    cases hsp
    cases Cssq with
    | nil =>
      show CG β (C ++ []) f uf
      exact hcg.perm (by simp)
    | cons _ _ => exact absurd hlen (by simp)
  | cons x rest ih =>
    intro Γ T0 T' uq hsp Cssq hlen hpairs C f uf hcg
    cases Cssq with
    | nil => exact absurd hlen (by simp)
    | cons Cx Cssq =>
      simp only [List.length_cons] at hlen
      cases hsp with
      | @live _ A1 B1 _ ux1 _ _ us1 hc0 hx1 hrest =>
        have h2 := ih hrest (Cssq := Cssq) (by omega)
          (fun p hp => hpairs p (by
            simp only [List.zip_cons_cons]
            exact List.mem_cons_of_mem _ hp))
          (C := C ++ Cx) (f := .App f x) (uf := .App uf ux1)
          (.app hcg (hpairs ((Cx, x), ux1) (by
            simp only [List.zip_cons_cons]
            exact List.mem_cons_self)))
        show CG β (C ++ (Cx ++ Cssq.flatten)) _ _
        refine h2.perm ?_
        simp [List.append_assoc]
      | @dead _ A1 B1 _ πx1 _ _ us1 hc0 hx1 hrest =>
        have h2 := ih hrest (Cssq := Cssq) (by omega)
          (fun p hp => hpairs p (by
            simp only [List.zip_cons_cons]
            exact List.mem_cons_of_mem _ hp))
          (C := C ++ Cx) (f := .App f x) (uf := .App uf .Typ)
          (.app hcg ?_)
        · show CG β (C ++ (Cx ++ Cssq.flatten)) _ _
          refine h2.perm ?_
          simp [List.append_assoc]
        · exact CG.typ_.weaken (Sub.nil Cx)
-- ============================================================================
-- METATHEORY §NG — the leaf pricing: a Guard-ed body, instantiated by
-- the drive's environment of closed values, prices with every skeleton
-- charge strictly below the spent call's pinned charge, while the
-- environment's own charges ride slot by slot (each live slot at most
-- once — the era is affine). This is the heart of claims (4) and (5):
-- the descent comparison (§7), instantiated (§NS), meets the charged
-- guard (§NC) at every self-call site.
-- ============================================================================

theorem EraSpine.arm : ∀ {Γ : Ctx} {T0 T' : Term} {as us : List Term},
    EraSpine β Γ T0 as T' us → ∀ j, j < as.length →
    us.getD j .Typ = .Typ
    ∨ ∃ A, Era β Γ (as.getD j .Typ) A (us.getD j .Typ) := by
  intro Γ T0 T' as us hs
  induction hs with
  | nil => intro j hj; exact absurd hj (by simp)
  | @live _ A B x ux as' _ us' hc0 hx hrest ih =>
    intro j hj
    cases j with
    | zero => exact Or.inr ⟨A, hx⟩
    | succ j' =>
      simp only [List.length_cons] at hj
      exact ih j' (by omega)
  | @dead _ A B x πx as' _ us' hc0 hchk hrest ih =>
    intro j hj
    cases j with
    | zero => exact Or.inl _root_.rfl
    | succ j' =>
      simp only [List.length_cons] at hj
      exact ih j' (by omega)

theorem Guard.era_cg (hβ : Book.Closed β) (hok : Book.Ok β) {k : Nat} {dk : DefD}
    (hd : Book.defn β k = some dk) (vs : List Term)
    (hvsc : ∀ v ∈ vs, v.Closed 0)
    (sp : List (Option Nat)) (hspl : sp.length = dk.n + 1)
    (hspc : ∀ j, j < vs.length → sp.getD j none = none
      ∨ sp.getD j none = some (Term.csize β (vs.getD j .Typ)))
    (hspmask : ∀ j, j < dk.n → dk.qs.getD j .Lone = .None →
      sp.getD j none = none)
    (ph0 : Bool) :
    ∀ {cols : List Term} {b : Term}, Guard β k dk.qs cols b →
    ∀ {Γ : Ctx} {B ub : Term}, Era β Γ b B ub →
    ∀ (d : Nat) (env uenv : List Term) (Css : List (List Charge)),
    Γ.length = d + env.length →
    env.length = uenv.length →
    Css.length = uenv.length →
    (∀ v ∈ env, v.Closed 0) →
    (∀ v ∈ uenv, v.Closed 0) →
    (∀ p ∈ (Css.zip env).zip uenv, CG β p.1.1 p.1.2 p.2) →
    (∀ p ∈ env.zip uenv, p.2 = .Typ ∨ DeepP β p.1 p.2) →
    (∀ i, i < uenv.length → Term.occ (d + i) ub ≤ 1) →
    cols.map (Term.msubstAt d env) = vs →
    cols.length ≤ dk.n →
    ∃ (Cs : List Charge) (Crs : List (List Charge)),
      Crs.length = uenv.length ∧
      CG β (Cs ++ Crs.flatten) (Term.msubstAt d env b)
        (Term.msubstAt d uenv ub) ∧
      (∀ i, i < uenv.length → Sub (Crs.getD i []) (Css.getD i []) ∧
        (Term.occ (d + i) ub = 0 → Crs.getD i [] = [])) ∧
      (∀ c ∈ Cs, CLt c (k, sp, ph0)) := by
  intro cols b hg
  induction hg with
  | @call cols0 args hsl hargs ih =>
    intro Γ B ub he d env uenv Css hΓ hl1 hl2 henv huenv hpair henvP hocc hcols hcl
    obtain ⟨Tf, uhead, T', us, hheadera, hsp, hcvT', hueq⟩ :=
      Era.apps_inv hβ (Eq.refl _) he
    subst hueq
    rcases Era.ref_inv hβ hheadera with ⟨dj, hkj, hbnej, hcvj, huheq⟩ |
      ⟨A', hkj, _, _, _⟩
    rotate_left
    · exact (Book.defn_adt_clash hd hkj).elim
    subst huheq
    rw [hd] at hkj
    cases hkj
    have hvslen : vs.length = cols0.length := by
      rw [← hcols]
      simp
    have hsum : ∀ i, i < uenv.length →
        (us.map (Term.occ (d + i))).sum ≤ 1 := by
      intro i hi
      have h1 := hocc i hi
      rw [Term.occ_apps] at h1
      have h0 : Term.occ (d + i) (Term.Ref k) = 0 := _root_.rfl
      omega
    obtain ⟨Csw, Crsw, Css_site, hlenw, hlens, hpairw, hpermw, hslotw,
        hbeloww⟩ :=
      call_walk β d env uenv Css (k, sp, ph0)
        hsp
        (fun x hx B' ub' hera' hocc' =>
          ih x hx hera' d env uenv Css hΓ hl1 hl2 henv huenv hpair henvP hocc'
            hcols hcl)
        hsum
    obtain ⟨m, hm0, hma, hmc, htup, hrel, hpre, hstrict⟩ := hsl.tuplt d env
    have hclosj : ∀ j, j < m →
        (Term.msubstAt d env (cols0.getD j .Typ)).Closed 0 := by
      intro j hj
      have hgd := map_getD (Term.msubstAt d env) .Typ .Typ cols0 j (by omega)
      rw [hcols] at hgd
      rw [← hgd]
      exact hvsc _ (getD_mem vs j (by omega))
    have hpin : ∀ j, j < m → dk.qs.getD j .Lone ≠ .None →
        PinOk β ((args.map (Term.msubstAt d env)).getD j .Typ)
          ((us.map (Term.msubstAt d uenv)).getD j .Typ) := by
      intro j hj hlv
      have hlv0 : dk.qs.getD (0 + j) .Lone ≠ .None := by
        rw [Nat.zero_add]
        exact hlv
      have hja : j < args.length := by omega
      have hju : j < us.length := by
        have := hsp.lengths
        omega
      rw [map_getD (Term.msubstAt d env) .Typ .Typ args j hja,
        map_getD (Term.msubstAt d uenv) .Typ .Typ us j hju]
      rcases EraSpine.arm hsp j hja with htok | ⟨Aj, herax⟩
      · rw [htok, Term.msubstAt_typ]
        rcases hrel j (by omega) hlv0 with hpe | hpl
        · exact (descent_crigid β d env henv
            (Term.size (cols0.getD j .Typ)) (cols0.getD j .Typ)
            (Nat.le_refl _)).1 _ hpe (hclosj j (by omega))
        · exact (descent_crigid β d env henv
            (Term.size (cols0.getD j .Typ)) (cols0.getD j .Typ)
            (Nat.le_refl _)).2 _ hpl (hclosj j (by omega))
      · rcases hrel j (by omega) hlv0 with hpe | hpl
        · exact (descent_deepp β hβ hok d env uenv henv huenv hl1 henvP
            (Term.size (cols0.getD j .Typ)) (cols0.getD j .Typ)
            (Nat.le_refl _)).1 _ hpe (hclosj j (by omega)) herax
        · exact (descent_deepp β hβ hok d env uenv henv huenv hl1 henvP
            (Term.size (cols0.getD j .Typ)) (cols0.getD j .Typ)
            (Nat.le_refl _)).2 _ hpl (hclosj j (by omega)) herax
    rw [Term.msubstAt_apps, Term.msubstAt_apps, Term.msubstAt_ref,
      Term.msubstAt_ref]
    refine ⟨(k, pinsRow β dk.qs 0 (args.map (Term.msubstAt d env)) m
        ++ List.replicate (dk.n - m) none
        ++ [some (dk.n - min (args.map (Term.msubstAt d env)).length
            dk.n)], true) :: Csw, Crsw, hlenw,
      ?_, ?_, ?_⟩
    · refine CG.perm (CG.site (ph := true) hd (Eq.refl _)
        (by simp only [List.length_map]; exact hma)
        (by omega) hpin
        (by
          simp only [List.length_map]
          exact hsp.lengths)
        (by
          simp only [List.length_map]
          exact hlens)
        hpairw) ?_
      show ((k, _, true) :: Css_site.flatten).Perm
        (((k, _, true) :: Csw) ++ Crsw.flatten)
      exact hpermw.cons _
    · intro i hi
      obtain ⟨h1, h2⟩ := hslotw i hi
      refine ⟨h1, ?_⟩
      intro h0
      refine h2 ?_
      rw [Term.occ_apps] at h0
      have hr0 : Term.occ (d + i) (Term.Ref k) = 0 := _root_.rfl
      omega
    · intro c hc
      rcases List.mem_cons.mp hc with h1 | h2
      · subst h1
        refine Or.inr ⟨_root_.rfl, Or.inl ?_⟩
        have hmvs : m ≤ vs.length := by omega
        have hmdk : m ≤ dk.n := by omega
        have hlvs : vs.length = cols0.length := by
          rw [← hcols]
          simp
        show TupLt (pinsRow β dk.qs 0 (args.map (Term.msubstAt d env)) m
          ++ List.replicate (dk.n - m) none
          ++ [some (dk.n - min (args.map (Term.msubstAt d env)).length
              dk.n)]) sp
        rw [List.append_assoc]
        have htgt : ∀ j, j < m →
            Term.csize β (Term.msubstAt d env (cols0.getD j .Typ))
              = Term.csize β (vs.getD j .Typ) := by
          intro j hj
          have h2 := map_getD (Term.msubstAt d env) .Typ .Typ cols0 j
            (by omega)
          rw [hcols] at h2
          rw [← h2]
        have hargj : ∀ j, j < m →
            (args.map (Term.msubstAt d env)).getD j .Typ
              = Term.msubstAt d env (args.getD j .Typ) := by
          intro j hj
          exact map_getD (Term.msubstAt d env) .Typ .Typ args j (by omega)
        refine tup_below _ m (List.replicate (dk.n - m) none
            ++ [some (dk.n - min (args.map (Term.msubstAt d env)).length
              dk.n)]) sp
          (fun j => Term.csize β (Term.msubstAt d env (cols0.getD j .Typ)))
          (pinsRow_length β dk.qs m 0 _)
          hm0
          (by
            simp only [List.length_append, List.length_replicate,
              List.length_cons, List.length_nil]
            omega)
          ?_ ?_ ?_ ?_
        · intro j hj
          rcases hspc j (by omega) with h2 | h4
          · exact Or.inl h2
          · right
            rw [h4, htgt j hj]
        · intro j hj hnone
          rw [pinsRow_getD β dk.qs m j 0 _ hj] at hnone
          by_cases hq : dk.qs.getD (0 + j) .Lone = .None
          · refine hspmask j (by omega) ?_
            rw [Nat.zero_add] at hq
            exact hq
          · rw [if_neg hq] at hnone
            simp at hnone
        · intro j hj e he
          rw [pinsRow_getD β dk.qs m j 0 _ (by omega)] at he
          by_cases hq : dk.qs.getD (0 + j) .Lone = .None
          · rw [if_pos hq] at he
            simp at he
          · rw [if_neg hq] at he
            injection he with he2
            rw [← he2, hargj j (by omega)]
            exact (hpre j hj hq).csize d env
        · obtain ⟨hlvs, hstr⟩ := hstrict
          refine ⟨Term.csize β (Term.msubstAt d env
            (args.getD (m - 1) .Typ)), ?_, ?_⟩
          · rw [pinsRow_getD β dk.qs m (m - 1) 0 _ (by omega),
              if_neg hlvs, hargj (m - 1) (by omega)]
          · exact hstr.csize d env
      · exact hbeloww c h2
  | @var cols0 i =>
    intro Γ B ub he d env uenv Css hΓ hl1 hl2 henv huenv hpair henvP hocc hcols hcl
    obtain ⟨T0, hget, _, hueq⟩ := Era.var_inv hβ he
    subst hueq
    by_cases hid : i < d
    · rw [Term.msubstAt_var_lt d i hid, Term.msubstAt_var_lt d i hid]
      refine ⟨[], List.replicate uenv.length [], by simp, ?_, ?_, ?_⟩
      · rw [replicate_nil_flatten]
        exact .var
      · intro j hj
        rw [replicate_nil_getD]
        exact ⟨Sub.nil _, fun _ => _root_.rfl⟩
      · intro c hc
        exact nomatch hc
    · have hilt : i < Γ.length := Ctx.get_lt hget
      have hj : i - d < uenv.length := by omega
      have hie : i = d + (i - d) := by omega
      rw [hie, Term.msubstAt_var_hit d env
          henv (i - d) (by omega),
        Term.msubstAt_var_hit d uenv huenv (i - d) hj]
      refine ⟨[], (List.replicate uenv.length ([] : List Charge)).set (i - d)
        (Css.getD (i - d) []), ?_, ?_, ?_, ?_⟩
      · simp
      · rw [List.nil_append]
        refine CG.perm ?_ (slot_single_flatten uenv.length (i - d) _ hj).symm
        exact hpair _ (zip_zip_getD_mem Css env uenv hl2 hl1 (i - d) hj)
      · intro j' hj'
        by_cases hje : j' = i - d
        · subst hje
          rw [slot_single_getD_eq _ _ _ hj]
          refine ⟨Sub.refl _, ?_⟩
          intro h0
          rw [← hie] at h0
          simp only [Term.occ] at h0
          simp only [if_true] at h0
          exact absurd h0 Nat.one_ne_zero
        · rw [slot_single_getD_ne _ _ _ _ hje]
          exact ⟨Sub.nil _, fun _ => _root_.rfl⟩
      · intro c hc
        exact nomatch hc
  | @ref j cols0 hjk =>
    intro Γ B ub he d env uenv Css hΓ hl1 hl2 henv huenv hpair henvP hocc hcols hcl
    rcases Era.ref_inv hβ he with ⟨dj, hkj, _, _, hueq⟩ |
      ⟨A', hkj, h0', _, hueq⟩
    rotate_left
    · subst hueq
      rw [Term.msubstAt_ref]
      rw [Term.msubstAt_closed d uenv _ (by trivial)]
      refine ⟨[], List.replicate uenv.length [], by simp, ?_, ?_, ?_⟩
      · rw [replicate_nil_flatten]
        exact .refa
      · intro j' hj'
        rw [replicate_nil_getD]
        exact ⟨Sub.nil _, fun _ => _root_.rfl⟩
      · intro c hc
        exact nomatch hc
    subst hueq
    rw [Term.msubstAt_ref, Term.msubstAt_ref]
    refine ⟨[(j, List.replicate dj.n none ++ [some dj.n], true)],
      List.replicate uenv.length [], by simp, ?_, ?_, ?_⟩
    · rw [replicate_nil_flatten]
      exact (CG.ref (ph := true) hkj).perm (by simp)
    · intro j' hj'
      rw [replicate_nil_getD]
      exact ⟨Sub.nil _, fun _ => _root_.rfl⟩
    · intro c hc
      rw [List.mem_singleton.mp hc]
      exact Or.inl hjk
  | @typ cols0 =>
    intro Γ B ub he d env uenv Css hΓ hl1 hl2 henv huenv hpair henvP hocc hcols hcl
    have hueq := Era.typ_out he
    subst hueq
    rw [Term.msubstAt_closed d uenv _ (by trivial)]
    rw [Term.msubstAt_closed d env _ (by trivial)]
    refine ⟨[], List.replicate uenv.length [], by simp, ?_, ?_, ?_⟩
    · rw [replicate_nil_flatten]
      exact .typ_
    · intro j hj
      rw [replicate_nil_getD]
      exact ⟨Sub.nil _, fun _ => _root_.rfl⟩
    · intro c hc
      exact nomatch hc
  | @all A cols0 B0 q hgA hgB ihA ihB =>
    intro Γ B ub he d env uenv Css hΓ hl1 hl2 henv huenv hpair henvP hocc hcols hcl
    have hueq := Era.all_out he
    subst hueq
    rw [Term.msubstAt_closed d uenv _ (by trivial)]
    refine ⟨[], List.replicate uenv.length [], by simp, ?_, ?_, ?_⟩
    · rw [replicate_nil_flatten]
      exact .typ_
    · intro j hj
      rw [replicate_nil_getD]
      exact ⟨Sub.nil _, fun _ => _root_.rfl⟩
    · intro c hc
      exact nomatch hc
  | @lam f cols0 hgf ihf =>
    intro Γ B ub he d env uenv Css hΓ hl1 hl2 henv huenv hpair henvP hocc hcols hcl
    obtain ⟨q1, A1, B1, uf, hcv, hbody, hoccf, hueq⟩ := Era.lam_inv hβ he
    subst hueq
    rw [Term.msubstAt_lam d env henv,
      Term.msubstAt_lam d uenv huenv]
    have hcols' : (cols0.map (Term.shift 0)).map
        (Term.msubstAt (d + 1) env) = vs := by
      rw [List.map_map]
      have h1 : cols0.map (Term.msubstAt (d + 1) env ∘ Term.shift 0)
          = cols0.map (fun c0 => Term.shift 0 (Term.msubstAt d env c0)) :=
        List.map_congr_left (fun c0 _ =>
          Term.msubstAt_shift d env henv c0)
      rw [h1]
      rw [show (fun c0 => Term.shift 0 (Term.msubstAt d env c0))
        = (Term.shift 0 ∘ Term.msubstAt d env) from _root_.rfl]
      rw [← List.map_map]
      rw [hcols]
      exact map_closed_id vs hvsc _
        (fun t ht => Term.shift_closed t 0 0 ht (Nat.le_refl 0))
    obtain ⟨Cs, Crs, hlenr, hcg, hslots, hbelow⟩ :=
      ihf hbody (d + 1) env uenv Css (by simp only [List.length_cons]; omega)
        hl1 hl2 henv huenv hpair henvP
        (by
          intro i hi
          have := hocc i hi
          simp only [Term.occ] at this
          rw [show d + 1 + i = d + i + 1 from by omega]
          exact this)
        hcols' (by simpa using hcl)
    refine ⟨Cs, Crs, hlenr, .lam hcg, ?_, hbelow⟩
    intro i hi
    obtain ⟨hs1, hs2⟩ := hslots i hi
    refine ⟨hs1, ?_⟩
    intro h0
    refine hs2 ?_
    simp only [Term.occ] at h0
    rw [show d + 1 + i = d + i + 1 from by omega]
    exact h0
  | @app cols0 f a hgf hga ihf iha =>
    intro Γ B ub he d env uenv Css hΓ hl1 hl2 henv huenv hpair henvP hocc hcols hcl
    rcases Era.app_inv hβ he with
      ⟨A1, B1, uf, ua, hf, ha, hcv, hueq⟩ |
      ⟨A1, B1, uf, πa, hf, ha, hcv, hueq⟩
    · -- live argument: both sides recurse; slots split by occurrence
      subst hueq
      obtain ⟨Csf, Crsf, hlenf, hcgf, hslotf, hbelowf⟩ :=
        ihf hf d env uenv Css hΓ hl1 hl2 henv huenv hpair henvP
          (by
            intro i hi
            have := hocc i hi
            simp only [Term.occ] at this
            omega)
          hcols hcl
      obtain ⟨Csa, Crsa, hlena, hcga, hslota, hbelowa⟩ :=
        iha ha d env uenv Css hΓ hl1 hl2 henv huenv hpair henvP
          (by
            intro i hi
            have := hocc i hi
            simp only [Term.occ] at this
            omega)
          hcols hcl
      rw [Term.msubstAt_app, Term.msubstAt_app]
      have hll : Crsf.length = Crsa.length := by rw [hlenf, hlena]
      refine ⟨Csf ++ Csa, List.zipWith (· ++ ·) Crsf Crsa, ?_, ?_, ?_, ?_⟩
      · rw [zipWith_append_length Crsf Crsa hll]
        exact hlenf
      · refine CG.perm (.app hcgf hcga) ?_
        have hp := zipWith_append_flatten Crsf Crsa hll
        exact List.Perm.trans
          (perm_interchange Csf Crsf.flatten Csa Crsa.flatten)
          (List.Perm.append_left _ hp.symm)
      · intro i hi
        rw [zipWith_append_getD Crsf Crsa i hll]
        obtain ⟨hsf1, hsf2⟩ := hslotf i hi
        obtain ⟨hsa1, hsa2⟩ := hslota i hi
        have := hocc i hi
        simp only [Term.occ] at this
        constructor
        · by_cases hz : Term.occ (d + i) uf = 0
          · rw [hsf2 hz, List.nil_append]
            exact hsa1
          · have hza : Term.occ (d + i) ua = 0 := by omega
            rw [hsa2 hza, List.append_nil]
            exact hsf1
        · intro h0
          simp only [Term.occ] at h0
          have h1 : Term.occ (d + i) uf = 0 := by omega
          have h2 : Term.occ (d + i) ua = 0 := by omega
          rw [hsf2 h1, hsa2 h2]
          rfl
      · intro c hc
        rcases List.mem_append.mp hc with h1 | h2
        · exact hbelowf c h1
        · exact hbelowa c h2
    · -- dead argument: the token is free
      subst hueq
      obtain ⟨Csf, Crsf, hlenf, hcgf, hslotf, hbelowf⟩ :=
        ihf hf d env uenv Css hΓ hl1 hl2 henv huenv hpair henvP
          (by
            intro i hi
            have := hocc i hi
            simp only [Term.occ] at this
            omega)
          hcols hcl
      rw [Term.msubstAt_app, Term.msubstAt_app]
      rw [Term.msubstAt_closed d uenv .Typ (by trivial)]
      refine ⟨Csf, Crsf, hlenf, ?_, ?_, hbelowf⟩
      · refine CG.perm (.app hcgf .typ_) ?_
        simp
      · intro i hi
        obtain ⟨hs1, hs2⟩ := hslotf i hi
        refine ⟨hs1, ?_⟩
        intro h0
        refine hs2 ?_
        simp only [Term.occ] at h0
        omega
  | @adt cols0 a r =>
    intro Γ B ub he d env uenv Css hΓ hl1 hl2 henv huenv hpair henvP hocc hcols hcl
    have hueq := Era.adt_out he
    subst hueq
    rw [Term.msubstAt_closed d uenv _ (by trivial)]
    rw [Term.msubstAt_closed d env _ (by trivial)]
    refine ⟨[], List.replicate uenv.length [], by simp, ?_, ?_, ?_⟩
    · rw [replicate_nil_flatten]
      exact .adt
    · intro j hj
      rw [replicate_nil_getD]
      exact ⟨Sub.nil _, fun _ => _root_.rfl⟩
    · intro c hc
      exact nomatch hc
  | @ctr cols0 a c =>
    intro Γ B ub he d env uenv Css hΓ hl1 hl2 henv huenv hpair henvP hocc hcols hcl
    have hueq := Era.ctr_out he
    subst hueq
    rw [Term.msubstAt_closed d uenv _ (by trivial)]
    rw [Term.msubstAt_closed d env _ (by trivial)]
    refine ⟨[], List.replicate uenv.length [], by simp, ?_, ?_, ?_⟩
    · rw [replicate_nil_flatten]
      exact .ctr
    · intro j hj
      rw [replicate_nil_getD]
      exact ⟨Sub.nil _, fun _ => _root_.rfl⟩
    · intro c hc
      exact nomatch hc
  | @mat cols0 h0 m0 a c hgh hgm ihh ihm =>
    intro Γ B ub he d env uenv Css hΓ hl1 hl2 henv huenv hpair henvP hocc hcols hcl
    obtain ⟨A0, C0, r0, ps0, telF, B0, G0, q'0, uh, um, hk0, hc00, hr0,
      hlen0, hlive0, hins0, hgoal0, hh, hm, hcv, hueq⟩ := Era.mat_inv hβ he
    subst hueq
    rw [Term.msubstAt_mat, Term.msubstAt_mat]
    obtain ⟨Csh, Crsh, hlenh, hcgh, hsloth, hbelowh⟩ :=
      ihh hh d env uenv Css hΓ hl1 hl2 henv huenv hpair henvP
        (by
          intro i hi
          have h1 := hocc i hi
          simp only [Term.occ] at h1
          have hx : Term.occ (d + i) uh
              ≤ Nat.max (Term.occ (d + i) uh) (Term.occ (d + i) um) :=
            Nat.le_max_left _ _
          omega)
        hcols hcl
    obtain ⟨Csm, Crsm, hlenm, hcgm, hslotm, hbelowm⟩ :=
      ihm hm d env uenv Css hΓ hl1 hl2 henv huenv hpair henvP
        (by
          intro i hi
          have h1 := hocc i hi
          simp only [Term.occ] at h1
          have hx : Term.occ (d + i) um
              ≤ Nat.max (Term.occ (d + i) uh) (Term.occ (d + i) um) :=
            Nat.le_max_right _ _
          omega)
        hcols hcl
    obtain ⟨Crs, hlenr, hdom, hsubz⟩ := mat_slots Crsh Crsm Css
      (by omega) (by omega)
      (fun i hi => (hsloth i (by omega)).1)
      (fun i hi => (hslotm i (by omega)).1)
    refine ⟨Csh ++ Csm, Crs, by omega, ?_, ?_, ?_⟩
    · refine CG.mat hcgh hcgm ?_ ?_
      · refine Sub.append (Sub.append_right _ _) ?_
        refine Sub.flatten (by omega) ?_
        intro i hi
        exact (hdom i (by omega)).1
      · refine Sub.append (Sub.append_left _ _) ?_
        refine Sub.flatten (by omega) ?_
        intro i hi
        exact (hdom i (by omega)).2
    · intro i hi
      obtain ⟨hs1, hs2⟩ := hsubz i (by omega)
      refine ⟨hs1, ?_⟩
      intro h0
      simp only [Term.occ] at h0
      have hzh : Term.occ (d + i) uh = 0 := by
        have hx : Term.occ (d + i) uh
            ≤ Nat.max (Term.occ (d + i) uh) (Term.occ (d + i) um) :=
          Nat.le_max_left _ _
        omega
      have hzm : Term.occ (d + i) um = 0 := by
        have hx : Term.occ (d + i) um
            ≤ Nat.max (Term.occ (d + i) uh) (Term.occ (d + i) um) :=
          Nat.le_max_right _ _
        omega
      exact hs2 ⟨(hsloth i hi).2 hzh, (hslotm i hi).2 hzm⟩
    · intro c1 hc1
      rcases List.mem_append.mp hc1 with h1 | h2
      · exact hbelowh c1 h1
      · exact hbelowm c1 h2
  | @efq cols0 =>
    intro Γ B ub he d env uenv Css hΓ hl1 hl2 henv huenv hpair henvP hocc hcols hcl
    have hueq := Era.efq_out he
    subst hueq
    rw [Term.msubstAt_closed d uenv _ (by trivial)]
    rw [Term.msubstAt_closed d env _ (by trivial)]
    refine ⟨[], List.replicate uenv.length [], by simp, ?_, ?_, ?_⟩
    · rw [replicate_nil_flatten]
      exact .efq
    · intro j hj
      rw [replicate_nil_getD]
      exact ⟨Sub.nil _, fun _ => _root_.rfl⟩
    · intro c hc
      exact nomatch hc
  | @eql cols0 x y T hgx hgy hgT ihx ihy ihT =>
    intro Γ B ub he d env uenv Css hΓ hl1 hl2 henv huenv hpair henvP hocc hcols hcl
    have hueq := Era.eql_out he
    subst hueq
    rw [Term.msubstAt_closed d uenv _ (by trivial)]
    refine ⟨[], List.replicate uenv.length [], by simp, ?_, ?_, ?_⟩
    · rw [replicate_nil_flatten]
      exact .typ_
    · intro j hj
      rw [replicate_nil_getD]
      exact ⟨Sub.nil _, fun _ => _root_.rfl⟩
    · intro c hc
      exact nomatch hc
  | @rfl cols0 =>
    intro Γ B ub he d env uenv Css hΓ hl1 hl2 henv huenv hpair henvP hocc hcols hcl
    have hueq := Era.rfl_out he
    subst hueq
    rw [Term.msubstAt_closed d uenv _ (by trivial)]
    rw [Term.msubstAt_closed d env _ (by trivial)]
    refine ⟨[], List.replicate uenv.length [], by simp, ?_, ?_, ?_⟩
    · rw [replicate_nil_flatten]
      exact .rfl
    · intro j hj
      rw [replicate_nil_getD]
      exact ⟨Sub.nil _, fun _ => _root_.rfl⟩
    · intro c hc
      exact nomatch hc
  | @rwt cols0 e P f hge hgP hgf ihe ihP ihf =>
    intro Γ B ub he d env uenv Css hΓ hl1 hl2 henv huenv hpair henvP hocc hcols hcl
    obtain ⟨x, y, T0, ue, uf, hee, hfe, hcv, hueq⟩ := Era.rwt_inv hβ he
    subst hueq
    rw [Term.msubstAt_rwt, Term.msubstAt_rwt]
    rw [Term.msubstAt_closed d uenv .Typ (by trivial)]
    obtain ⟨Cse, Crse, hlene, hcge, hslote, hbelowe⟩ :=
      ihe hee d env uenv Css hΓ hl1 hl2 henv huenv hpair henvP
        (by
          intro i hi
          have h1 := hocc i hi
          simp only [Term.occ] at h1
          omega)
        hcols hcl
    obtain ⟨Csf, Crsf, hlenf, hcgf, hslotf, hbelowf⟩ :=
      ihf hfe d env uenv Css hΓ hl1 hl2 henv huenv hpair henvP
        (by
          intro i hi
          have h1 := hocc i hi
          simp only [Term.occ] at h1
          omega)
        hcols hcl
    have hll : Crse.length = Crsf.length := by omega
    refine ⟨Cse ++ Csf, List.zipWith (· ++ ·) Crse Crsf, ?_, ?_, ?_, ?_⟩
    · rw [zipWith_append_length Crse Crsf hll]
      exact hlene
    · refine CG.perm (.rwt hcge hcgf) ?_
      have hp := zipWith_append_flatten Crse Crsf hll
      exact List.Perm.trans
        (perm_interchange Cse Crse.flatten Csf Crsf.flatten)
        (List.Perm.append_left _ hp.symm)
    · intro i hi
      rw [zipWith_append_getD Crse Crsf i hll]
      obtain ⟨hse1, hse2⟩ := hslote i hi
      obtain ⟨hsf1, hsf2⟩ := hslotf i hi
      have h1 := hocc i hi
      simp only [Term.occ] at h1
      constructor
      · by_cases hz : Term.occ (d + i) ue = 0
        · rw [hse2 hz, List.nil_append]
          exact hsf1
        · have hzf : Term.occ (d + i) uf = 0 := by omega
          rw [hsf2 hzf, List.append_nil]
          exact hse1
      · intro h0
        simp only [Term.occ] at h0
        have hz1 : Term.occ (d + i) ue = 0 := by omega
        have hz2 : Term.occ (d + i) uf = 0 := by omega
        rw [hse2 hz1, hsf2 hz2]
        rfl
    · intro c1 hc1
      rcases List.mem_append.mp hc1 with h1 | h2
      · exact hbelowe c1 h1
      · exact hbelowf c1 h2
  | @let_ cols0 v b0 q hgv hgb ihv ihb =>
    intro Γ B ub he d env uenv Css hΓ hl1 hl2 henv huenv hpair henvP hocc hcols hcl
    have hcols' : (cols0.map (Term.shift 0)).map
        (Term.msubstAt (d + 1) env) = vs := by
      rw [List.map_map]
      have h1 : cols0.map (Term.msubstAt (d + 1) env ∘ Term.shift 0)
          = cols0.map (fun c0 => Term.shift 0 (Term.msubstAt d env c0)) :=
        List.map_congr_left (fun c0 _ =>
          Term.msubstAt_shift d env henv c0)
      rw [h1]
      rw [show (fun c0 => Term.shift 0 (Term.msubstAt d env c0))
        = (Term.shift 0 ∘ Term.msubstAt d env) from _root_.rfl]
      rw [← List.map_map]
      rw [hcols]
      exact map_closed_id vs hvsc _
        (fun t ht => Term.shift_closed t 0 0 ht (Nat.le_refl 0))
    rcases Era.let_inv hβ he with
      ⟨A1, uv0, T0, ubb, hqb, hve, hbe, hocc0, hcv, hueq⟩ |
      ⟨A1, πv, T0, ubb, hqb, hvchk, hbe, hocc0, hcv, hueq⟩
    · subst hqb
      subst hueq
      rw [Term.msubstAt_let d env henv,
        Term.msubstAt_let d uenv huenv]
      obtain ⟨Csv, Crsv, hlenv, hcgv, hslotv, hbelowv⟩ :=
        ihv hve d env uenv Css hΓ hl1 hl2 henv huenv hpair henvP
          (by
            intro i hi
            have h1 := hocc i hi
            simp only [Term.occ] at h1
            omega)
          hcols hcl
      obtain ⟨Csb, Crsb, hlenb, hcgb, hslotb, hbelowb⟩ :=
        ihb hbe (d + 1) env uenv Css
          (by simp only [List.length_cons]; omega)
          hl1 hl2 henv huenv hpair henvP
          (by
            intro i hi
            have h1 := hocc i hi
            simp only [Term.occ] at h1
            rw [show d + 1 + i = d + i + 1 from by omega]
            omega)
          hcols' (by simpa using hcl)
      have hll : Crsv.length = Crsb.length := by omega
      refine ⟨Csv ++ Csb, List.zipWith (· ++ ·) Crsv Crsb, ?_, ?_, ?_, ?_⟩
      · rw [zipWith_append_length Crsv Crsb hll]
        exact hlenv
      · refine CG.perm (.let_ hcgv hcgb) ?_
        have hp := zipWith_append_flatten Crsv Crsb hll
        exact List.Perm.trans
          (perm_interchange Csv Crsv.flatten Csb Crsb.flatten)
          (List.Perm.append_left _ hp.symm)
      · intro i hi
        rw [zipWith_append_getD Crsv Crsb i hll]
        obtain ⟨hsv1, hsv2⟩ := hslotv i hi
        obtain ⟨hsb1, hsb2⟩ := hslotb i hi
        have h1 := hocc i hi
        simp only [Term.occ] at h1
        constructor
        · by_cases hz : Term.occ (d + i) uv0 = 0
          · rw [hsv2 hz, List.nil_append]
            exact hsb1
          · have hzb : Term.occ (d + i + 1) ubb = 0 := by omega
            have hzb' := hsb2 (by
              rw [show d + 1 + i = d + i + 1 from by omega]
              exact hzb)
            rw [hzb', List.append_nil]
            exact hsv1
        · intro h0
          simp only [Term.occ] at h0
          have hz1 : Term.occ (d + i) uv0 = 0 := by omega
          have hz2 : Term.occ (d + i + 1) ubb = 0 := by omega
          have hz2' := hsb2 (by
            rw [show d + 1 + i = d + i + 1 from by omega]
            exact hz2)
          rw [hsv2 hz1, hz2']
          rfl
      · intro c1 hc1
        rcases List.mem_append.mp hc1 with h1 | h2
        · exact hbelowv c1 h1
        · exact hbelowb c1 h2
    · subst hqb
      subst hueq
      rw [Term.msubstAt_let d env henv,
        Term.msubstAt_let d uenv huenv]
      rw [Term.msubstAt_closed d uenv .Typ (by trivial)]
      obtain ⟨Csb, Crsb, hlenb, hcgb, hslotb, hbelowb⟩ :=
        ihb hbe (d + 1) env uenv Css
          (by simp only [List.length_cons]; omega)
          hl1 hl2 henv huenv hpair henvP
          (by
            intro i hi
            have h1 := hocc i hi
            simp only [Term.occ] at h1
            rw [show d + 1 + i = d + i + 1 from by omega]
            omega)
          hcols' (by simpa using hcl)
      refine ⟨Csb, Crsb, hlenb, ?_, ?_, hbelowb⟩
      · refine CG.perm (.let_ .typ_ hcgb) ?_
        simp
      · intro i hi
        obtain ⟨hs1, hs2⟩ := hslotb i hi
        refine ⟨hs1, ?_⟩
        intro h0
        simp only [Term.occ] at h0
        refine hs2 ?_
        rw [show d + 1 + i = d + i + 1 from by omega]
        omega


theorem Guard.era_cg_susp (hβ : Book.Closed β) (hok : Book.Ok β) {k : Nat} {dk : DefD}
    (hd : Book.defn β k = some dk) (vs : List Term)
    (hvsc : ∀ v ∈ vs, v.Closed 0)
    (hmWd : vs.length < dk.n)
    (sp : List (Option Nat)) (hspl : sp.length = dk.n + 1)
    (hspc : ∀ j, j < vs.length → sp.getD j none = none
      ∨ sp.getD j none = some (Term.csize β (vs.getD j .Typ)))
    (hspfree : ∀ j, vs.length ≤ j → j < dk.n → sp.getD j none = none)
    (hslack : ∃ ss, sp.getD dk.n none = some ss
      ∧ dk.n - vs.length ≤ ss)
    (hspmask : ∀ j, j < dk.n → dk.qs.getD j .Lone = .None →
      sp.getD j none = none)
    (ph0 : Bool) :
    ∀ {cols : List Term} {b : Term}, Guard β k dk.qs cols b →
    ∀ {Γ : Ctx} {B ub : Term}, Era β Γ b B ub →
    ∀ (d : Nat) (env uenv : List Term) (Css : List (List Charge)),
    Γ.length = d + env.length →
    env.length = uenv.length →
    Css.length = uenv.length →
    (∀ v ∈ env, v.Closed 0) →
    (∀ v ∈ uenv, v.Closed 0) →
    (∀ p ∈ (Css.zip env).zip uenv, CG β p.1.1 p.1.2 p.2) →
    (∀ p ∈ env.zip uenv, p.2 = .Typ ∨ DeepP β p.1 p.2) →
    (∀ i, i < uenv.length → Term.occ (d + i) ub ≤ 1) →
    (∃ colsW tl, colsW ++ tl = cols ∧
      colsW.map (Term.msubstAt d env) = vs) →
    True →
    ∃ (Cs : List Charge) (Crs : List (List Charge)),
      Crs.length = uenv.length ∧
      CG β (Cs ++ Crs.flatten) (Term.msubstAt d env b)
        (Term.msubstAt d uenv ub) ∧
      (∀ i, i < uenv.length → Sub (Crs.getD i []) (Css.getD i []) ∧
        (Term.occ (d + i) ub = 0 → Crs.getD i [] = [])) ∧
      (∀ c ∈ Cs, CLt c (k, sp, ph0)) := by
  intro cols b hg
  induction hg with
  | @call cols0 args hsl hargs ih =>
    intro Γ B ub he d env uenv Css hΓ hl1 hl2 henv huenv hpair henvP hocc hcols hcl
    obtain ⟨Tf, uhead, T', us, hheadera, hsp, hcvT', hueq⟩ :=
      Era.apps_inv hβ (Eq.refl _) he
    subst hueq
    rcases Era.ref_inv hβ hheadera with ⟨dj, hkj, hbnej, hcvj, huheq⟩ |
      ⟨A', hkj, _, _, _⟩
    rotate_left
    · exact (Book.defn_adt_clash hd hkj).elim
    subst huheq
    rw [hd] at hkj
    cases hkj
    obtain ⟨colsW, tlW, happW, hmapW⟩ := hcols
    have hvslen : vs.length = colsW.length := by
      rw [← hmapW]
      simp
    have hgetW : ∀ j, j < vs.length →
        cols0.getD j .Typ = colsW.getD j .Typ := by
      intro j hj
      rw [← happW]
      exact getD_append_left colsW tlW j (by omega)
    have hsum : ∀ i, i < uenv.length →
        (us.map (Term.occ (d + i))).sum ≤ 1 := by
      intro i hi
      have h1 := hocc i hi
      rw [Term.occ_apps] at h1
      have h0 : Term.occ (d + i) (Term.Ref k) = 0 := _root_.rfl
      omega
    obtain ⟨Csw, Crsw, Css_site, hlenw, hlens, hpairw, hpermw, hslotw,
        hbeloww⟩ :=
      call_walk β d env uenv Css (k, sp, ph0)
        hsp
        (fun x hx B' ub' hera' hocc' =>
          ih x hx hera' d env uenv Css hΓ hl1 hl2 henv huenv hpair henvP hocc'
            ⟨colsW, tlW, happW, hmapW⟩ hcl)
        hsum
    obtain ⟨m, hm0, hma, hmc, htup, hrel, hpre, hstrict⟩ := hsl.tuplt d env
    have hclosj : ∀ j, j < vs.length →
        (Term.msubstAt d env (cols0.getD j .Typ)).Closed 0 := by
      intro j hj
      rw [hgetW j hj]
      have hgd := map_getD (Term.msubstAt d env) .Typ .Typ colsW j (by omega)
      rw [hmapW] at hgd
      rw [← hgd]
      exact hvsc _ (getD_mem vs j (by omega))
    have htgt : ∀ j, j < vs.length →
        Term.csize β (Term.msubstAt d env (cols0.getD j .Typ))
          = Term.csize β (vs.getD j .Typ) := by
      intro j hj
      rw [hgetW j hj]
      have h2 := map_getD (Term.msubstAt d env) .Typ .Typ colsW j (by omega)
      rw [hmapW] at h2
      rw [← h2]
    rw [Term.msubstAt_apps, Term.msubstAt_apps, Term.msubstAt_ref,
      Term.msubstAt_ref]
    by_cases hsm : m ≤ vs.length
    · -- the descent column is within the consumed region: strict pin
      have hpin : ∀ j, j < m → dk.qs.getD j .Lone ≠ .None →
          PinOk β ((args.map (Term.msubstAt d env)).getD j .Typ)
            ((us.map (Term.msubstAt d uenv)).getD j .Typ) := by
        intro j hj hlv
        have hlv0 : dk.qs.getD (0 + j) .Lone ≠ .None := by
          rw [Nat.zero_add]
          exact hlv
        have hja : j < args.length := by omega
        have hju : j < us.length := by
          have := hsp.lengths
          omega
        rw [map_getD (Term.msubstAt d env) .Typ .Typ args j hja,
          map_getD (Term.msubstAt d uenv) .Typ .Typ us j hju]
        rcases EraSpine.arm hsp j hja with htok | ⟨Aj, herax⟩
        · rw [htok, Term.msubstAt_typ]
          rcases hrel j (by omega) hlv0 with hpe | hpl
          · exact (descent_crigid β d env henv
              (Term.size (cols0.getD j .Typ)) (cols0.getD j .Typ)
              (Nat.le_refl _)).1 _ hpe (hclosj j (by omega))
          · exact (descent_crigid β d env henv
              (Term.size (cols0.getD j .Typ)) (cols0.getD j .Typ)
              (Nat.le_refl _)).2 _ hpl (hclosj j (by omega))
        · rcases hrel j (by omega) hlv0 with hpe | hpl
          · exact (descent_deepp β hβ hok d env uenv henv huenv hl1 henvP
              (Term.size (cols0.getD j .Typ)) (cols0.getD j .Typ)
              (Nat.le_refl _)).1 _ hpe (hclosj j (by omega)) herax
          · exact (descent_deepp β hβ hok d env uenv henv huenv hl1 henvP
              (Term.size (cols0.getD j .Typ)) (cols0.getD j .Typ)
              (Nat.le_refl _)).2 _ hpl (hclosj j (by omega)) herax
      refine ⟨(k, pinsRow β dk.qs 0 (args.map (Term.msubstAt d env)) m
          ++ List.replicate (dk.n - m) none
          ++ [some (dk.n - min (args.map (Term.msubstAt d env)).length
              dk.n)], true) :: Csw, Crsw, hlenw,
        ?_, ?_, ?_⟩
      · refine CG.perm (CG.site (ph := true) hd (Eq.refl _)
          (by simp only [List.length_map]; exact hma)
          (by omega) hpin
          (by
            simp only [List.length_map]
            exact hsp.lengths)
          (by
            simp only [List.length_map]
            exact hlens)
          hpairw) ?_
        show ((k, _, true) :: Css_site.flatten).Perm
          (((k, _, true) :: Csw) ++ Crsw.flatten)
        exact hpermw.cons _
      · intro i hi
        obtain ⟨h1, h2⟩ := hslotw i hi
        refine ⟨h1, ?_⟩
        intro h0
        refine h2 ?_
        rw [Term.occ_apps] at h0
        have hr0 : Term.occ (d + i) (Term.Ref k) = 0 := _root_.rfl
        omega
      · intro c hc
        rcases List.mem_cons.mp hc with h1 | h2
        · subst h1
          refine Or.inr ⟨_root_.rfl, Or.inl ?_⟩
          show TupLt (pinsRow β dk.qs 0
            (args.map (Term.msubstAt d env)) m
            ++ List.replicate (dk.n - m) none
            ++ [some (dk.n - min (args.map (Term.msubstAt d env)).length
                dk.n)]) sp
          rw [List.append_assoc]
          have hargj : ∀ j, j < m →
              (args.map (Term.msubstAt d env)).getD j .Typ
                = Term.msubstAt d env (args.getD j .Typ) := by
            intro j hj
            exact map_getD (Term.msubstAt d env) .Typ .Typ args j
              (by omega)
          refine tup_below _ m (List.replicate (dk.n - m) none
              ++ [some (dk.n - min (args.map (Term.msubstAt d env)).length
                dk.n)]) sp
            (fun j => Term.csize β (Term.msubstAt d env
              (cols0.getD j .Typ)))
            (pinsRow_length β dk.qs m 0 _)
            hm0
            (by
              simp only [List.length_append, List.length_replicate,
                List.length_cons, List.length_nil]
              omega)
            ?_ ?_ ?_ ?_
          · intro j hj
            rcases hspc j (by omega) with h2 | h4
            · exact Or.inl h2
            · right
              rw [h4, htgt j (by omega)]
          · intro j hj hnone
            rw [pinsRow_getD β dk.qs m j 0 _ hj] at hnone
            by_cases hq : dk.qs.getD (0 + j) .Lone = .None
            · refine hspmask j (by omega) ?_
              rw [Nat.zero_add] at hq
              exact hq
            · rw [if_neg hq] at hnone
              simp at hnone
          · intro j hj e he
            rw [pinsRow_getD β dk.qs m j 0 _ (by omega)] at he
            by_cases hq : dk.qs.getD (0 + j) .Lone = .None
            · rw [if_pos hq] at he
              simp at he
            · rw [if_neg hq] at he
              injection he with he2
              rw [← he2, hargj j (by omega)]
              exact (hpre j hj hq).csize d env
          · obtain ⟨hlvs, hstr⟩ := hstrict
            refine ⟨Term.csize β (Term.msubstAt d env
              (args.getD (m - 1) .Typ)), ?_, ?_⟩
            · rw [pinsRow_getD β dk.qs m (m - 1) 0 _ (by omega),
                if_neg hlvs, hargj (m - 1) (by omega)]
            · exact hstr.csize d env
        · exact hbeloww c h2
    · -- the descent column is hidden: pin the consumed region, the
      -- slack slot pays
      have hpin : ∀ j, j < vs.length → dk.qs.getD j .Lone ≠ .None →
          PinOk β ((args.map (Term.msubstAt d env)).getD j .Typ)
            ((us.map (Term.msubstAt d uenv)).getD j .Typ) := by
        intro j hj hlv
        have hlv0 : dk.qs.getD (0 + j) .Lone ≠ .None := by
          rw [Nat.zero_add]
          exact hlv
        have hja : j < args.length := by omega
        have hju : j < us.length := by
          have := hsp.lengths
          omega
        rw [map_getD (Term.msubstAt d env) .Typ .Typ args j hja,
          map_getD (Term.msubstAt d uenv) .Typ .Typ us j hju]
        rcases EraSpine.arm hsp j hja with htok | ⟨Aj, herax⟩
        · rw [htok, Term.msubstAt_typ]
          rcases hrel j (by omega) hlv0 with hpe | hpl
          · exact (descent_crigid β d env henv
              (Term.size (cols0.getD j .Typ)) (cols0.getD j .Typ)
              (Nat.le_refl _)).1 _ hpe (hclosj j (by omega))
          · exact (descent_crigid β d env henv
              (Term.size (cols0.getD j .Typ)) (cols0.getD j .Typ)
              (Nat.le_refl _)).2 _ hpl (hclosj j (by omega))
        · rcases hrel j (by omega) hlv0 with hpe | hpl
          · exact (descent_deepp β hβ hok d env uenv henv huenv hl1 henvP
              (Term.size (cols0.getD j .Typ)) (cols0.getD j .Typ)
              (Nat.le_refl _)).1 _ hpe (hclosj j (by omega)) herax
          · exact (descent_deepp β hβ hok d env uenv henv huenv hl1 henvP
              (Term.size (cols0.getD j .Typ)) (cols0.getD j .Typ)
              (Nat.le_refl _)).2 _ hpl (hclosj j (by omega)) herax
      refine ⟨(k, pinsRow β dk.qs 0 (args.map (Term.msubstAt d env)) vs.length
          ++ List.replicate (dk.n - vs.length) none
          ++ [some (dk.n - min (args.map (Term.msubstAt d env)).length
              dk.n)], true) :: Csw, Crsw, hlenw,
        ?_, ?_, ?_⟩
      · refine CG.perm (CG.site (ph := true) hd (Eq.refl _)
          (by simp only [List.length_map]; omega)
          (by omega) hpin
          (by
            simp only [List.length_map]
            exact hsp.lengths)
          (by
            simp only [List.length_map]
            exact hlens)
          hpairw) ?_
        show ((k, _, true) :: Css_site.flatten).Perm
          (((k, _, true) :: Csw) ++ Crsw.flatten)
        exact hpermw.cons _
      · intro i hi
        obtain ⟨h1, h2⟩ := hslotw i hi
        refine ⟨h1, ?_⟩
        intro h0
        refine h2 ?_
        rw [Term.occ_apps] at h0
        have hr0 : Term.occ (d + i) (Term.Ref k) = 0 := _root_.rfl
        omega
      · intro c hc
        rcases List.mem_cons.mp hc with h1 | h2
        · subst h1
          refine Or.inr ⟨_root_.rfl, Or.inl ?_⟩
          show TupLt (pinsRow β dk.qs 0
            (args.map (Term.msubstAt d env)) vs.length
            ++ List.replicate (dk.n - vs.length) none
            ++ [some (dk.n - min (args.map (Term.msubstAt d env)).length
                dk.n)]) sp
          rw [List.append_assoc]
          have hargj : ∀ j, j < vs.length →
              (args.map (Term.msubstAt d env)).getD j .Typ
                = Term.msubstAt d env (args.getD j .Typ) := by
            intro j hj
            exact map_getD (Term.msubstAt d env) .Typ .Typ args j
              (by omega)
          obtain ⟨ss, hs1, hs2⟩ := hslack
          have hslt : dk.n - min (args.map (Term.msubstAt d env)).length
              dk.n < ss := by
            simp only [List.length_map]
            omega
          refine tup_below_slack
            (pinsRow β dk.qs 0 (args.map (Term.msubstAt d env))
              vs.length)
            vs.length (dk.n - vs.length)
            (dk.n - min (args.map (Term.msubstAt d env)).length dk.n)
            ss sp
            (fun j => Term.csize β (Term.msubstAt d env
              (cols0.getD j .Typ)))
            (pinsRow_length β dk.qs vs.length 0 _)
            (by omega)
            ?_ ?_ ?_ ?_ ?_ hslt
          · intro j hj
            rcases hspc j hj with h2 | h4
            · exact Or.inl h2
            · right
              rw [h4, htgt j hj]
          · intro j hj1 hj2
            exact hspfree j (by omega) (by omega)
          · rw [show vs.length + (dk.n - vs.length) = dk.n from by omega]
            exact hs1
          · intro j hj hnone
            rw [pinsRow_getD β dk.qs vs.length j 0 _ hj] at hnone
            by_cases hq : dk.qs.getD (0 + j) .Lone = .None
            · refine hspmask j (by omega) ?_
              rw [Nat.zero_add] at hq
              exact hq
            · rw [if_neg hq] at hnone
              simp at hnone
          · intro j hj e he
            rw [pinsRow_getD β dk.qs vs.length j 0 _ hj] at he
            by_cases hq : dk.qs.getD (0 + j) .Lone = .None
            · rw [if_pos hq] at he
              simp at he
            · rw [if_neg hq] at he
              injection he with he2
              rw [← he2, hargj j hj]
              rcases hrel j (by omega) hq with hpe | hpl
              · exact Nat.le_of_eq (hpe.csize d env)
              · exact Nat.le_of_lt (hpl.csize d env)
        · exact hbeloww c h2
  | @var cols0 i =>
    intro Γ B ub he d env uenv Css hΓ hl1 hl2 henv huenv hpair henvP hocc hcols hcl
    obtain ⟨T0, hget, _, hueq⟩ := Era.var_inv hβ he
    subst hueq
    by_cases hid : i < d
    · rw [Term.msubstAt_var_lt d i hid, Term.msubstAt_var_lt d i hid]
      refine ⟨[], List.replicate uenv.length [], by simp, ?_, ?_, ?_⟩
      · rw [replicate_nil_flatten]
        exact .var
      · intro j hj
        rw [replicate_nil_getD]
        exact ⟨Sub.nil _, fun _ => _root_.rfl⟩
      · intro c hc
        exact nomatch hc
    · have hilt : i < Γ.length := Ctx.get_lt hget
      have hj : i - d < uenv.length := by omega
      have hie : i = d + (i - d) := by omega
      rw [hie, Term.msubstAt_var_hit d env
          henv (i - d) (by omega),
        Term.msubstAt_var_hit d uenv huenv (i - d) hj]
      refine ⟨[], (List.replicate uenv.length ([] : List Charge)).set (i - d)
        (Css.getD (i - d) []), ?_, ?_, ?_, ?_⟩
      · simp
      · rw [List.nil_append]
        refine CG.perm ?_ (slot_single_flatten uenv.length (i - d) _ hj).symm
        exact hpair _ (zip_zip_getD_mem Css env uenv hl2 hl1 (i - d) hj)
      · intro j' hj'
        by_cases hje : j' = i - d
        · subst hje
          rw [slot_single_getD_eq _ _ _ hj]
          refine ⟨Sub.refl _, ?_⟩
          intro h0
          rw [← hie] at h0
          simp only [Term.occ] at h0
          simp only [if_true] at h0
          exact absurd h0 Nat.one_ne_zero
        · rw [slot_single_getD_ne _ _ _ _ hje]
          exact ⟨Sub.nil _, fun _ => _root_.rfl⟩
      · intro c hc
        exact nomatch hc
  | @ref j cols0 hjk =>
    intro Γ B ub he d env uenv Css hΓ hl1 hl2 henv huenv hpair henvP hocc hcols hcl
    rcases Era.ref_inv hβ he with ⟨dj, hkj, _, _, hueq⟩ |
      ⟨A', hkj, h0', _, hueq⟩
    rotate_left
    · subst hueq
      rw [Term.msubstAt_ref]
      rw [Term.msubstAt_closed d uenv _ (by trivial)]
      refine ⟨[], List.replicate uenv.length [], by simp, ?_, ?_, ?_⟩
      · rw [replicate_nil_flatten]
        exact .refa
      · intro j' hj'
        rw [replicate_nil_getD]
        exact ⟨Sub.nil _, fun _ => _root_.rfl⟩
      · intro c hc
        exact nomatch hc
    subst hueq
    rw [Term.msubstAt_ref, Term.msubstAt_ref]
    refine ⟨[(j, List.replicate dj.n none ++ [some dj.n], true)],
      List.replicate uenv.length [], by simp, ?_, ?_, ?_⟩
    · rw [replicate_nil_flatten]
      exact (CG.ref (ph := true) hkj).perm (by simp)
    · intro j' hj'
      rw [replicate_nil_getD]
      exact ⟨Sub.nil _, fun _ => _root_.rfl⟩
    · intro c hc
      rw [List.mem_singleton.mp hc]
      exact Or.inl hjk
  | @typ cols0 =>
    intro Γ B ub he d env uenv Css hΓ hl1 hl2 henv huenv hpair henvP hocc hcols hcl
    have hueq := Era.typ_out he
    subst hueq
    rw [Term.msubstAt_closed d uenv _ (by trivial)]
    rw [Term.msubstAt_closed d env _ (by trivial)]
    refine ⟨[], List.replicate uenv.length [], by simp, ?_, ?_, ?_⟩
    · rw [replicate_nil_flatten]
      exact .typ_
    · intro j hj
      rw [replicate_nil_getD]
      exact ⟨Sub.nil _, fun _ => _root_.rfl⟩
    · intro c hc
      exact nomatch hc
  | @all A cols0 B0 q hgA hgB ihA ihB =>
    intro Γ B ub he d env uenv Css hΓ hl1 hl2 henv huenv hpair henvP hocc hcols hcl
    have hueq := Era.all_out he
    subst hueq
    rw [Term.msubstAt_closed d uenv _ (by trivial)]
    refine ⟨[], List.replicate uenv.length [], by simp, ?_, ?_, ?_⟩
    · rw [replicate_nil_flatten]
      exact .typ_
    · intro j hj
      rw [replicate_nil_getD]
      exact ⟨Sub.nil _, fun _ => _root_.rfl⟩
    · intro c hc
      exact nomatch hc
  | @lam f cols0 hgf ihf =>
    intro Γ B ub he d env uenv Css hΓ hl1 hl2 henv huenv hpair henvP hocc hcols hcl
    obtain ⟨q1, A1, B1, uf, hcv, hbody, hoccf, hueq⟩ := Era.lam_inv hβ he
    subst hueq
    rw [Term.msubstAt_lam d env henv,
      Term.msubstAt_lam d uenv huenv]
    obtain ⟨colsW, tlW, happW, hmapW⟩ := hcols
    have hcols' : ∃ colsW' tl', colsW' ++ tl' = cols0.map (Term.shift 0) ∧
        colsW'.map (Term.msubstAt (d + 1) env) = vs := by
      refine ⟨colsW.map (Term.shift 0), tlW.map (Term.shift 0), ?_, ?_⟩
      · rw [← List.map_append, happW]
      · rw [List.map_map]
        have h1 : colsW.map (Term.msubstAt (d + 1) env ∘ Term.shift 0)
            = colsW.map (fun c0 => Term.shift 0 (Term.msubstAt d env c0)) :=
          List.map_congr_left (fun c0 _ =>
            Term.msubstAt_shift d env henv c0)
        rw [h1]
        rw [show (fun c0 => Term.shift 0 (Term.msubstAt d env c0))
          = (Term.shift 0 ∘ Term.msubstAt d env) from _root_.rfl]
        rw [← List.map_map]
        rw [hmapW]
        exact map_closed_id vs hvsc _
          (fun t ht => Term.shift_closed t 0 0 ht (Nat.le_refl 0))
    obtain ⟨Cs, Crs, hlenr, hcg, hslots, hbelow⟩ :=
      ihf hbody (d + 1) env uenv Css (by simp only [List.length_cons]; omega)
        hl1 hl2 henv huenv hpair henvP
        (by
          intro i hi
          have := hocc i hi
          simp only [Term.occ] at this
          rw [show d + 1 + i = d + i + 1 from by omega]
          exact this)
        hcols' trivial
    refine ⟨Cs, Crs, hlenr, .lam hcg, ?_, hbelow⟩
    intro i hi
    obtain ⟨hs1, hs2⟩ := hslots i hi
    refine ⟨hs1, ?_⟩
    intro h0
    refine hs2 ?_
    simp only [Term.occ] at h0
    rw [show d + 1 + i = d + i + 1 from by omega]
    exact h0
  | @app cols0 f a hgf hga ihf iha =>
    intro Γ B ub he d env uenv Css hΓ hl1 hl2 henv huenv hpair henvP hocc hcols hcl
    rcases Era.app_inv hβ he with
      ⟨A1, B1, uf, ua, hf, ha, hcv, hueq⟩ |
      ⟨A1, B1, uf, πa, hf, ha, hcv, hueq⟩
    · -- live argument: both sides recurse; slots split by occurrence
      subst hueq
      obtain ⟨Csf, Crsf, hlenf, hcgf, hslotf, hbelowf⟩ :=
        ihf hf d env uenv Css hΓ hl1 hl2 henv huenv hpair henvP
          (by
            intro i hi
            have := hocc i hi
            simp only [Term.occ] at this
            omega)
          hcols hcl
      obtain ⟨Csa, Crsa, hlena, hcga, hslota, hbelowa⟩ :=
        iha ha d env uenv Css hΓ hl1 hl2 henv huenv hpair henvP
          (by
            intro i hi
            have := hocc i hi
            simp only [Term.occ] at this
            omega)
          hcols hcl
      rw [Term.msubstAt_app, Term.msubstAt_app]
      have hll : Crsf.length = Crsa.length := by rw [hlenf, hlena]
      refine ⟨Csf ++ Csa, List.zipWith (· ++ ·) Crsf Crsa, ?_, ?_, ?_, ?_⟩
      · rw [zipWith_append_length Crsf Crsa hll]
        exact hlenf
      · refine CG.perm (.app hcgf hcga) ?_
        have hp := zipWith_append_flatten Crsf Crsa hll
        exact List.Perm.trans
          (perm_interchange Csf Crsf.flatten Csa Crsa.flatten)
          (List.Perm.append_left _ hp.symm)
      · intro i hi
        rw [zipWith_append_getD Crsf Crsa i hll]
        obtain ⟨hsf1, hsf2⟩ := hslotf i hi
        obtain ⟨hsa1, hsa2⟩ := hslota i hi
        have := hocc i hi
        simp only [Term.occ] at this
        constructor
        · by_cases hz : Term.occ (d + i) uf = 0
          · rw [hsf2 hz, List.nil_append]
            exact hsa1
          · have hza : Term.occ (d + i) ua = 0 := by omega
            rw [hsa2 hza, List.append_nil]
            exact hsf1
        · intro h0
          simp only [Term.occ] at h0
          have h1 : Term.occ (d + i) uf = 0 := by omega
          have h2 : Term.occ (d + i) ua = 0 := by omega
          rw [hsf2 h1, hsa2 h2]
          rfl
      · intro c hc
        rcases List.mem_append.mp hc with h1 | h2
        · exact hbelowf c h1
        · exact hbelowa c h2
    · -- dead argument: the token is free
      subst hueq
      obtain ⟨Csf, Crsf, hlenf, hcgf, hslotf, hbelowf⟩ :=
        ihf hf d env uenv Css hΓ hl1 hl2 henv huenv hpair henvP
          (by
            intro i hi
            have := hocc i hi
            simp only [Term.occ] at this
            omega)
          hcols hcl
      rw [Term.msubstAt_app, Term.msubstAt_app]
      rw [Term.msubstAt_closed d uenv .Typ (by trivial)]
      refine ⟨Csf, Crsf, hlenf, ?_, ?_, hbelowf⟩
      · refine CG.perm (.app hcgf .typ_) ?_
        simp
      · intro i hi
        obtain ⟨hs1, hs2⟩ := hslotf i hi
        refine ⟨hs1, ?_⟩
        intro h0
        refine hs2 ?_
        simp only [Term.occ] at h0
        omega
  | @adt cols0 a r =>
    intro Γ B ub he d env uenv Css hΓ hl1 hl2 henv huenv hpair henvP hocc hcols hcl
    have hueq := Era.adt_out he
    subst hueq
    rw [Term.msubstAt_closed d uenv _ (by trivial)]
    rw [Term.msubstAt_closed d env _ (by trivial)]
    refine ⟨[], List.replicate uenv.length [], by simp, ?_, ?_, ?_⟩
    · rw [replicate_nil_flatten]
      exact .adt
    · intro j hj
      rw [replicate_nil_getD]
      exact ⟨Sub.nil _, fun _ => _root_.rfl⟩
    · intro c hc
      exact nomatch hc
  | @ctr cols0 a c =>
    intro Γ B ub he d env uenv Css hΓ hl1 hl2 henv huenv hpair henvP hocc hcols hcl
    have hueq := Era.ctr_out he
    subst hueq
    rw [Term.msubstAt_closed d uenv _ (by trivial)]
    rw [Term.msubstAt_closed d env _ (by trivial)]
    refine ⟨[], List.replicate uenv.length [], by simp, ?_, ?_, ?_⟩
    · rw [replicate_nil_flatten]
      exact .ctr
    · intro j hj
      rw [replicate_nil_getD]
      exact ⟨Sub.nil _, fun _ => _root_.rfl⟩
    · intro c hc
      exact nomatch hc
  | @mat cols0 h0 m0 a c hgh hgm ihh ihm =>
    intro Γ B ub he d env uenv Css hΓ hl1 hl2 henv huenv hpair henvP hocc hcols hcl
    obtain ⟨A0, C0, r0, ps0, telF, B0, G0, q'0, uh, um, hk0, hc00, hr0,
      hlen0, hlive0, hins0, hgoal0, hh, hm, hcv, hueq⟩ := Era.mat_inv hβ he
    subst hueq
    rw [Term.msubstAt_mat, Term.msubstAt_mat]
    obtain ⟨Csh, Crsh, hlenh, hcgh, hsloth, hbelowh⟩ :=
      ihh hh d env uenv Css hΓ hl1 hl2 henv huenv hpair henvP
        (by
          intro i hi
          have h1 := hocc i hi
          simp only [Term.occ] at h1
          have hx : Term.occ (d + i) uh
              ≤ Nat.max (Term.occ (d + i) uh) (Term.occ (d + i) um) :=
            Nat.le_max_left _ _
          omega)
        hcols hcl
    obtain ⟨Csm, Crsm, hlenm, hcgm, hslotm, hbelowm⟩ :=
      ihm hm d env uenv Css hΓ hl1 hl2 henv huenv hpair henvP
        (by
          intro i hi
          have h1 := hocc i hi
          simp only [Term.occ] at h1
          have hx : Term.occ (d + i) um
              ≤ Nat.max (Term.occ (d + i) uh) (Term.occ (d + i) um) :=
            Nat.le_max_right _ _
          omega)
        hcols hcl
    obtain ⟨Crs, hlenr, hdom, hsubz⟩ := mat_slots Crsh Crsm Css
      (by omega) (by omega)
      (fun i hi => (hsloth i (by omega)).1)
      (fun i hi => (hslotm i (by omega)).1)
    refine ⟨Csh ++ Csm, Crs, by omega, ?_, ?_, ?_⟩
    · refine CG.mat hcgh hcgm ?_ ?_
      · refine Sub.append (Sub.append_right _ _) ?_
        refine Sub.flatten (by omega) ?_
        intro i hi
        exact (hdom i (by omega)).1
      · refine Sub.append (Sub.append_left _ _) ?_
        refine Sub.flatten (by omega) ?_
        intro i hi
        exact (hdom i (by omega)).2
    · intro i hi
      obtain ⟨hs1, hs2⟩ := hsubz i (by omega)
      refine ⟨hs1, ?_⟩
      intro h0
      simp only [Term.occ] at h0
      have hzh : Term.occ (d + i) uh = 0 := by
        have hx : Term.occ (d + i) uh
            ≤ Nat.max (Term.occ (d + i) uh) (Term.occ (d + i) um) :=
          Nat.le_max_left _ _
        omega
      have hzm : Term.occ (d + i) um = 0 := by
        have hx : Term.occ (d + i) um
            ≤ Nat.max (Term.occ (d + i) uh) (Term.occ (d + i) um) :=
          Nat.le_max_right _ _
        omega
      exact hs2 ⟨(hsloth i hi).2 hzh, (hslotm i hi).2 hzm⟩
    · intro c1 hc1
      rcases List.mem_append.mp hc1 with h1 | h2
      · exact hbelowh c1 h1
      · exact hbelowm c1 h2
  | @efq cols0 =>
    intro Γ B ub he d env uenv Css hΓ hl1 hl2 henv huenv hpair henvP hocc hcols hcl
    have hueq := Era.efq_out he
    subst hueq
    rw [Term.msubstAt_closed d uenv _ (by trivial)]
    rw [Term.msubstAt_closed d env _ (by trivial)]
    refine ⟨[], List.replicate uenv.length [], by simp, ?_, ?_, ?_⟩
    · rw [replicate_nil_flatten]
      exact .efq
    · intro j hj
      rw [replicate_nil_getD]
      exact ⟨Sub.nil _, fun _ => _root_.rfl⟩
    · intro c hc
      exact nomatch hc
  | @eql cols0 x y T hgx hgy hgT ihx ihy ihT =>
    intro Γ B ub he d env uenv Css hΓ hl1 hl2 henv huenv hpair henvP hocc hcols hcl
    have hueq := Era.eql_out he
    subst hueq
    rw [Term.msubstAt_closed d uenv _ (by trivial)]
    refine ⟨[], List.replicate uenv.length [], by simp, ?_, ?_, ?_⟩
    · rw [replicate_nil_flatten]
      exact .typ_
    · intro j hj
      rw [replicate_nil_getD]
      exact ⟨Sub.nil _, fun _ => _root_.rfl⟩
    · intro c hc
      exact nomatch hc
  | @rfl cols0 =>
    intro Γ B ub he d env uenv Css hΓ hl1 hl2 henv huenv hpair henvP hocc hcols hcl
    have hueq := Era.rfl_out he
    subst hueq
    rw [Term.msubstAt_closed d uenv _ (by trivial)]
    rw [Term.msubstAt_closed d env _ (by trivial)]
    refine ⟨[], List.replicate uenv.length [], by simp, ?_, ?_, ?_⟩
    · rw [replicate_nil_flatten]
      exact .rfl
    · intro j hj
      rw [replicate_nil_getD]
      exact ⟨Sub.nil _, fun _ => _root_.rfl⟩
    · intro c hc
      exact nomatch hc
  | @rwt cols0 e P f hge hgP hgf ihe ihP ihf =>
    intro Γ B ub he d env uenv Css hΓ hl1 hl2 henv huenv hpair henvP hocc hcols hcl
    obtain ⟨x, y, T0, ue, uf, hee, hfe, hcv, hueq⟩ := Era.rwt_inv hβ he
    subst hueq
    rw [Term.msubstAt_rwt, Term.msubstAt_rwt]
    rw [Term.msubstAt_closed d uenv .Typ (by trivial)]
    obtain ⟨Cse, Crse, hlene, hcge, hslote, hbelowe⟩ :=
      ihe hee d env uenv Css hΓ hl1 hl2 henv huenv hpair henvP
        (by
          intro i hi
          have h1 := hocc i hi
          simp only [Term.occ] at h1
          omega)
        hcols hcl
    obtain ⟨Csf, Crsf, hlenf, hcgf, hslotf, hbelowf⟩ :=
      ihf hfe d env uenv Css hΓ hl1 hl2 henv huenv hpair henvP
        (by
          intro i hi
          have h1 := hocc i hi
          simp only [Term.occ] at h1
          omega)
        hcols hcl
    have hll : Crse.length = Crsf.length := by omega
    refine ⟨Cse ++ Csf, List.zipWith (· ++ ·) Crse Crsf, ?_, ?_, ?_, ?_⟩
    · rw [zipWith_append_length Crse Crsf hll]
      exact hlene
    · refine CG.perm (.rwt hcge hcgf) ?_
      have hp := zipWith_append_flatten Crse Crsf hll
      exact List.Perm.trans
        (perm_interchange Cse Crse.flatten Csf Crsf.flatten)
        (List.Perm.append_left _ hp.symm)
    · intro i hi
      rw [zipWith_append_getD Crse Crsf i hll]
      obtain ⟨hse1, hse2⟩ := hslote i hi
      obtain ⟨hsf1, hsf2⟩ := hslotf i hi
      have h1 := hocc i hi
      simp only [Term.occ] at h1
      constructor
      · by_cases hz : Term.occ (d + i) ue = 0
        · rw [hse2 hz, List.nil_append]
          exact hsf1
        · have hzf : Term.occ (d + i) uf = 0 := by omega
          rw [hsf2 hzf, List.append_nil]
          exact hse1
      · intro h0
        simp only [Term.occ] at h0
        have hz1 : Term.occ (d + i) ue = 0 := by omega
        have hz2 : Term.occ (d + i) uf = 0 := by omega
        rw [hse2 hz1, hsf2 hz2]
        rfl
    · intro c1 hc1
      rcases List.mem_append.mp hc1 with h1 | h2
      · exact hbelowe c1 h1
      · exact hbelowf c1 h2
  | @let_ cols0 v b0 q hgv hgb ihv ihb =>
    intro Γ B ub he d env uenv Css hΓ hl1 hl2 henv huenv hpair henvP hocc hcols hcl
    obtain ⟨colsW, tlW, happW, hmapW⟩ := hcols
    have hcols' : ∃ colsW' tl', colsW' ++ tl' = cols0.map (Term.shift 0) ∧
        colsW'.map (Term.msubstAt (d + 1) env) = vs := by
      refine ⟨colsW.map (Term.shift 0), tlW.map (Term.shift 0), ?_, ?_⟩
      · rw [← List.map_append, happW]
      · rw [List.map_map]
        have h1 : colsW.map (Term.msubstAt (d + 1) env ∘ Term.shift 0)
            = colsW.map (fun c0 => Term.shift 0 (Term.msubstAt d env c0)) :=
          List.map_congr_left (fun c0 _ =>
            Term.msubstAt_shift d env henv c0)
        rw [h1]
        rw [show (fun c0 => Term.shift 0 (Term.msubstAt d env c0))
          = (Term.shift 0 ∘ Term.msubstAt d env) from _root_.rfl]
        rw [← List.map_map]
        rw [hmapW]
        exact map_closed_id vs hvsc _
          (fun t ht => Term.shift_closed t 0 0 ht (Nat.le_refl 0))
    rcases Era.let_inv hβ he with
      ⟨A1, uv0, T0, ubb, hqb, hve, hbe, hocc0, hcv, hueq⟩ |
      ⟨A1, πv, T0, ubb, hqb, hvchk, hbe, hocc0, hcv, hueq⟩
    · subst hqb
      subst hueq
      rw [Term.msubstAt_let d env henv,
        Term.msubstAt_let d uenv huenv]
      obtain ⟨Csv, Crsv, hlenv, hcgv, hslotv, hbelowv⟩ :=
        ihv hve d env uenv Css hΓ hl1 hl2 henv huenv hpair henvP
          (by
            intro i hi
            have h1 := hocc i hi
            simp only [Term.occ] at h1
            omega)
          ⟨colsW, tlW, happW, hmapW⟩ hcl
      obtain ⟨Csb, Crsb, hlenb, hcgb, hslotb, hbelowb⟩ :=
        ihb hbe (d + 1) env uenv Css
          (by simp only [List.length_cons]; omega)
          hl1 hl2 henv huenv hpair henvP
          (by
            intro i hi
            have h1 := hocc i hi
            simp only [Term.occ] at h1
            rw [show d + 1 + i = d + i + 1 from by omega]
            omega)
          hcols' trivial
      have hll : Crsv.length = Crsb.length := by omega
      refine ⟨Csv ++ Csb, List.zipWith (· ++ ·) Crsv Crsb, ?_, ?_, ?_, ?_⟩
      · rw [zipWith_append_length Crsv Crsb hll]
        exact hlenv
      · refine CG.perm (.let_ hcgv hcgb) ?_
        have hp := zipWith_append_flatten Crsv Crsb hll
        exact List.Perm.trans
          (perm_interchange Csv Crsv.flatten Csb Crsb.flatten)
          (List.Perm.append_left _ hp.symm)
      · intro i hi
        rw [zipWith_append_getD Crsv Crsb i hll]
        obtain ⟨hsv1, hsv2⟩ := hslotv i hi
        obtain ⟨hsb1, hsb2⟩ := hslotb i hi
        have h1 := hocc i hi
        simp only [Term.occ] at h1
        constructor
        · by_cases hz : Term.occ (d + i) uv0 = 0
          · rw [hsv2 hz, List.nil_append]
            exact hsb1
          · have hzb : Term.occ (d + i + 1) ubb = 0 := by omega
            have hzb' := hsb2 (by
              rw [show d + 1 + i = d + i + 1 from by omega]
              exact hzb)
            rw [hzb', List.append_nil]
            exact hsv1
        · intro h0
          simp only [Term.occ] at h0
          have hz1 : Term.occ (d + i) uv0 = 0 := by omega
          have hz2 : Term.occ (d + i + 1) ubb = 0 := by omega
          have hz2' := hsb2 (by
            rw [show d + 1 + i = d + i + 1 from by omega]
            exact hz2)
          rw [hsv2 hz1, hz2']
          rfl
      · intro c1 hc1
        rcases List.mem_append.mp hc1 with h1 | h2
        · exact hbelowv c1 h1
        · exact hbelowb c1 h2
    · subst hqb
      subst hueq
      rw [Term.msubstAt_let d env henv,
        Term.msubstAt_let d uenv huenv]
      rw [Term.msubstAt_closed d uenv .Typ (by trivial)]
      obtain ⟨Csb, Crsb, hlenb, hcgb, hslotb, hbelowb⟩ :=
        ihb hbe (d + 1) env uenv Css
          (by simp only [List.length_cons]; omega)
          hl1 hl2 henv huenv hpair henvP
          (by
            intro i hi
            have h1 := hocc i hi
            simp only [Term.occ] at h1
            rw [show d + 1 + i = d + i + 1 from by omega]
            omega)
          hcols' trivial
      refine ⟨Csb, Crsb, hlenb, ?_, ?_, hbelowb⟩
      · refine CG.perm (.let_ .typ_ hcgb) ?_
        simp
      · intro i hi
        obtain ⟨hs1, hs2⟩ := hslotb i hi
        refine ⟨hs1, ?_⟩
        intro h0
        simp only [Term.occ] at h0
        refine hs2 ?_
        rw [show d + 1 + i = d + i + 1 from by omega]
        omega



-- the lhs algebra's terms always keep a Ref at the heart of their
-- lam-body spine — never a bare variable — so instantiation preserves
-- their head shape
def Term.lhsOk : Term → Prop
  | .Lam L   => Term.lhsOk L
  | .App f _ => Term.lhsOk f
  | .Ref _   => True
  | _        => False


theorem Term.lhsOk.subst : ∀ (t : Term), Term.lhsOk t →
    ∀ (d : Nat) (w : Term), Term.lhsOk (Term.subst d w t) := by
  intro t
  induction t with
  | Lam L ihL =>
    intro h d w
    exact ihL h (d + 1) (Term.shift 0 w)
  | App f a ihf _ =>
    intro h d w
    exact ihf h d w
  | Ref k =>
    intro _ d w
    trivial
  | _ =>
    intro h
    exact absurd h (by trivial)

theorem Term.lhsOk.shift : ∀ (t : Term), Term.lhsOk t →
    ∀ (d : Nat), Term.lhsOk (Term.shift d t) := by
  intro t
  induction t with
  | Lam L ihL =>
    intro h d
    exact ihL h (d + 1)
  | App f a ihf _ =>
    intro h d
    exact ihf h d
  | Ref k =>
    intro _ d
    trivial
  | _ =>
    intro h
    exact absurd h (by trivial)

theorem Term.lhsOk.shiftN (h : Term.lhsOk t) : ∀ (n : Nat),
    Term.lhsOk (Term.shiftN n t) := by
  intro n
  induction n with
  | zero => exact h
  | succ n ih => exact Term.lhsOk.shift _ ih 0

theorem Term.lhsOk.applyB (h : Term.lhsOk t) (a : Term) :
    Term.lhsOk (Term.applyB t a) := by
  cases t with
  | Lam L => exact Term.lhsOk.subst L h 0 a
  | Ref k => trivial
  | App f x => exact h
  | _ => exact absurd h (by trivial)

theorem Term.lhsOk.lams (h : Term.lhsOk t) : ∀ (n : Nat),
    Term.lhsOk (Term.lams n t) := by
  intro n
  induction n with
  | zero => exact h
  | succ n ih => exact ih

theorem Term.lhsOk.lhsExt (h : Term.lhsOk t) (a c fn : Nat) :
    Term.lhsOk (Term.lhsExt t a c fn) := by
  refine Term.lhsOk.lams ?_ fn
  exact Term.lhsOk.applyB (Term.lhsOk.shiftN h fn) _

theorem Term.lhsOk.msubstAt (h : Term.lhsOk t) : ∀ (d : Nat)
    (vs : List Term), Term.lhsOk (Term.msubstAt d vs t) := by
  intro d vs
  induction vs generalizing t h with
  | nil => exact h
  | cons v vs ih =>
    exact ih (Term.lhsOk.subst t h d v)


-- ============================================================================
-- METATHEORY §ND — the drive: a δ-unfolded definition's case tree runs
-- against its argument queue. Betas consume columns and pattern
-- fields, matches peel constructor values, and the run ends either at
-- a Guard leaf (priced by §NG strictly below the spent charge) or,
-- underapplied, at a suspended Lam/Mat value. The three-layer era
-- invariant — raw era in the binder context, instantiated era, and
-- their syntactic connection — rides on constructor injectivity.
-- ============================================================================

theorem Term.occ_msubstAt (d i : Nat) (hid : i < d) :
    ∀ (vs : List Term), (∀ v ∈ vs, v.Closed 0) → ∀ (u : Term),
    Term.occ i (Term.msubstAt d vs u) = Term.occ i u := by
  intro vs
  induction vs with
  | nil => intro _ u; rfl
  | cons v vs ih =>
    intro hcl u
    show Term.occ i (Term.msubstAt d vs (Term.subst d v u)) = _
    rw [ih (fun w hw => hcl w (List.mem_cons_of_mem v hw)) _]
    exact Term.occ_subst_closed (hcl v List.mem_cons_self) u d i hid

theorem apps_ref_not_lam (k : Nat) (ws : List Term) :
    ∀ L, Term.apps (.Ref k) ws ≠ .Lam L := by
  intro L he
  rcases apps_shape ws (.Ref k) _ he with ⟨h1, h2⟩ | ⟨as0, al, h1, h2⟩
  · exact Term.noConfusion h2
  · exact Term.noConfusion h2

theorem getD_last {d0 : α} : ∀ (l : List α) (x : α),
    (l ++ [x]).getD l.length d0 = x := by
  intro l
  induction l with
  | nil => intro x; rfl
  | cons y ys ih => intro x; exact ih x

theorem Term.shiftN_ref (d k : Nat) :
    Term.shiftN d (.Ref k) = .Ref k := by
  induction d with
  | zero => rfl
  | succ d ih =>
    show Term.shift 0 (Term.shiftN d (.Ref k)) = _
    rw [ih]
    rfl

-- the suspension shapes are stable under shifting and substitution:
-- the closed consumed prefix rides untouched, the open tail is junk
theorem susp_shape_shift (k : Nat) (vs : List Term)
    (hvsc : ∀ v ∈ vs, v.Closed 0) (dsh : Nat) :
    ∀ (o1 : List Term) (T1 : Term),
    ∃ (o2 : List Term) (T2 : Term),
      Term.shift dsh (.App (Term.apps (.Ref k) (vs ++ o1)) T1)
        = .App (Term.apps (.Ref k) (vs ++ o2)) T2 := by
  intro o1 T1
  refine ⟨o1.map (Term.shift dsh), Term.shift dsh T1, ?_⟩
  show Term.App (Term.shift dsh (Term.apps (.Ref k) (vs ++ o1))) _ = _
  rw [Term.shift_apps, List.map_append]
  rw [show Term.shift dsh (.Ref k) = .Ref k from by
    cases dsh <;> rfl]
  rw [map_closed_id vs hvsc _
    (fun t ht => Term.shift_closed t 0 dsh ht (Nat.zero_le dsh))]

theorem susp_shape_subst (k : Nat) (vs : List Term)
    (hvsc : ∀ v ∈ vs, v.Closed 0) (dsu : Nat) (w : Term) :
    ∀ (o1 : List Term) (T1 : Term),
    ∃ (o2 : List Term) (T2 : Term),
      Term.subst dsu w (.App (Term.apps (.Ref k) (vs ++ o1)) T1)
        = .App (Term.apps (.Ref k) (vs ++ o2)) T2 := by
  intro o1 T1
  refine ⟨o1.map (Term.subst dsu w), Term.subst dsu w T1, ?_⟩
  show Term.App (Term.subst dsu w (Term.apps (.Ref k) (vs ++ o1))) _ = _
  rw [Term.subst_apps, List.map_append]
  show Term.App (Term.apps (Term.subst dsu w (.Ref k)) _) _ = _
  simp only [Term.subst]
  rw [map_closed_id vs hvsc _
    (fun t ht => Term.subst_closed t 0 dsu w ht (Nat.zero_le dsu))]

theorem susp_shape_shiftN (k : Nat) (vs : List Term)
    (hvsc : ∀ v ∈ vs, v.Closed 0) :
    ∀ (fn j : Nat) (o1 : List Term) (T1 : Term),
    ∃ (o2 : List Term) (T2 : Term),
      Term.shiftN fn (Term.lams j
          (.App (Term.apps (.Ref k) (vs ++ o1)) T1))
        = Term.lams j (.App (Term.apps (.Ref k) (vs ++ o2)) T2) := by
  intro fn
  induction fn with
  | zero => intro j o1 T1; exact ⟨o1, T1, _root_.rfl⟩
  | succ fn ih =>
    intro j o1 T1
    obtain ⟨o2, T2, h2⟩ := ih j o1 T1
    obtain ⟨o3, T3, h3⟩ := susp_shape_shift k vs hvsc (0 + j) o2 T2
    refine ⟨o3, T3, ?_⟩
    show Term.shift 0 (Term.shiftN fn
      (Term.lams j (.App (Term.apps (.Ref k) (vs ++ o1)) T1))) = _
    rw [h2, Term.shift_lams, h3]

theorem getD_replicate_none : ∀ (n j : Nat),
    (List.replicate n (none : Option Nat)).getD j none = none := by
  intro n
  induction n with
  | zero => intro j; cases j <;> rfl
  | succ n ih =>
    intro j
    cases j with
    | zero => rfl
    | succ j => exact ih j

-- extracting the spendable charge of a reference-headed call from any
-- pricing: a bare head or a pinned site, through frames and slack —
-- either way the stored tuple is compatible with the true argument
-- sizes and its slack covers the call's
theorem CG.ref_spine_inv : ∀ {C : List Charge} {t u : Term}, CG β C t u →
    ∀ {k : Nat} {xs us : List Term},
    t = Term.apps (.Ref k) xs → u = Term.apps (.Ref k) us →
    xs.length = us.length →
    ∃ (dk : DefD) (ts : List (Option Nat)) (ph : Bool)
      (Css : List (List Charge)),
      Book.defn β k = some dk ∧
      Css.length = us.length ∧
      (∀ p ∈ (Css.zip xs).zip us, CG β p.1.1 p.1.2 p.2) ∧
      Sub ((k, ts, ph) :: Css.flatten) C ∧
      ts.length = dk.n + 1 ∧
      (∀ j, j < dk.n → ts.getD j none = none
        ∨ (j < xs.length ∧ ts.getD j none
            = some (Term.csize β (xs.getD j .Typ)))) ∧
      (∃ ss, ts.getD dk.n none = some ss
        ∧ dk.n - min xs.length dk.n ≤ ss) ∧
      (∀ j, j < dk.n → ts.getD j none ≠ none →
        j < xs.length ∧ j < us.length
        ∧ PinOk β (xs.getD j .Typ) (us.getD j .Typ)) ∧
      (∀ j, j < dk.n → dk.qs.getD j .Lone = .None →
        ts.getD j none = none) := by
  intro C t u h
  induction h with
  | typ_ =>
    intro k xs us ht hu hlen
    rcases apps_shape us _ _ hu.symm with ⟨h1, h2⟩ | ⟨us0, ul, h1, h2⟩
    · exact Term.noConfusion h2
    · exact Term.noConfusion h2
  | refa =>
    intro k xs us ht hu hlen
    rcases apps_shape us _ _ hu.symm with ⟨h1, h2⟩ | ⟨us0, ul, h1, h2⟩
    · exact Term.noConfusion h2
    · exact Term.noConfusion h2
  | var =>
    intro k xs us ht hu hlen
    rcases apps_shape us _ _ hu.symm with ⟨h1, h2⟩ | ⟨us0, ul, h1, h2⟩
    · exact Term.noConfusion h2
    · exact Term.noConfusion h2
  | @ref k1 d1 ph1 hk1 =>
    intro k xs us ht hu hlen
    rcases apps_shape xs _ _ ht.symm with ⟨h1, h2⟩ | ⟨xs0, xl, h1, h2⟩
    · subst h1
      rcases apps_shape us _ _ hu.symm with ⟨h3, h4⟩ | ⟨us0, ul, h3, h4⟩
      · subst h3
        injection h2 with hk2
        subst hk2
        refine ⟨d1, List.replicate d1.n none ++ [some d1.n], ph1, [],
          hk1, _root_.rfl, ?_, Sub.refl _, ?_, ?_, ?_⟩
        · intro p hp
          exact nomatch hp
        · simp only [List.length_append, List.length_replicate,
            List.length_cons, List.length_nil]
        · intro j hj
          left
          rw [getD_append_left _ _ j (by
            simp only [List.length_replicate]
            omega)]
          exact getD_replicate_none d1.n j
        · refine ⟨⟨d1.n, ?_, by omega⟩, ?_, ?_⟩
          · have h := getD_last (d0 := (none : Option Nat))
              (List.replicate d1.n none) (some d1.n)
            rw [show (List.replicate d1.n (none : Option Nat)).length
              = d1.n from by simp] at h
            exact h
          · intro j hj hne
            exfalso
            refine hne ?_
            rw [getD_append_left _ _ j (by
              simp only [List.length_replicate]
              omega)]
            exact getD_replicate_none _ _
          · intro j hj _
            rw [getD_append_left _ _ j (by
              simp only [List.length_replicate]
              omega)]
            exact getD_replicate_none _ _
      · exact Term.noConfusion h4
    · exact Term.noConfusion h2
  | @site k1 d1 xs1 us1 m1 ts1 Css1 ph1 hk1 hts1 hm1 hmn1 hpins1 hlxu1
      hlc1 hall1 =>
    intro k xs us ht hu hlen
    obtain ⟨hheq, hargs⟩ := Term.apps_head_inv (h := Term.Ref k1)
      (h' := Term.Ref k) (by trivial) (by trivial) ht
    injection hheq with hk2
    subst hk2
    subst hargs
    obtain ⟨_, hargs2⟩ := Term.apps_head_inv (h := Term.Ref k1)
      (h' := Term.Ref k1) (by trivial) (by trivial) hu
    subst hargs2
    have hrowlen : (pinsRow β d1.qs 0 xs1 m1).length = m1 :=
      pinsRow_length β d1.qs m1 0 xs1
    have hbeyond : ∀ j, m1 ≤ j → j < d1.n →
        ts1.getD j none = none := by
      intro j hj1 hj2
      rw [hts1, List.append_assoc]
      rw [show j = (pinsRow β d1.qs 0 xs1 m1).length + (j - m1) from by
        omega]
      rw [getD_append_right]
      rw [getD_append_left _ _ (j - m1) (by
        simp only [List.length_replicate]
        omega)]
      exact getD_replicate_none _ _
    refine ⟨d1, ts1, ph1, Css1, hk1, hlc1, hall1, Sub.refl _, ?_, ?_, ?_,
      ?_, ?_⟩
    · rw [hts1]
      simp only [List.length_append, List.length_replicate,
        List.length_cons, List.length_nil, hrowlen]
      omega
    · intro j hj
      by_cases hjm : j < m1
      · rw [hts1, List.append_assoc]
        rw [getD_append_left _ _ j (by omega)]
        rw [pinsRow_getD β d1.qs m1 j 0 xs1 hjm]
        by_cases hq : d1.qs.getD (0 + j) .Lone = .None
        · rw [if_pos hq]
          exact Or.inl _root_.rfl
        · rw [if_neg hq]
          exact Or.inr ⟨by omega, _root_.rfl⟩
      · exact Or.inl (hbeyond j (by omega) hj)
    · rw [hts1, List.append_assoc]
      refine ⟨d1.n - min xs1.length d1.n, ?_, by omega⟩
      have h := getD_last (d0 := (none : Option Nat))
        (List.replicate (d1.n - m1) none)
        (some (d1.n - min xs1.length d1.n))
      rw [show (List.replicate (d1.n - m1) (none : Option Nat)).length
        = d1.n - m1 from by simp] at h
      have h2 := getD_append_right (d0 := (none : Option Nat))
        (pinsRow β d1.qs 0 xs1 m1)
        (List.replicate (d1.n - m1) none
          ++ [some (d1.n - min xs1.length d1.n)])
        (d1.n - m1)
      rw [hrowlen] at h2
      rw [show m1 + (d1.n - m1) = d1.n from by omega] at h2
      rw [h2]
      exact h
    · intro j hj hne
      by_cases hjm : j < m1
      · have hlive : d1.qs.getD j .Lone ≠ .None := by
          intro hq
          refine hne ?_
          rw [hts1, List.append_assoc]
          rw [getD_append_left _ _ j (by omega)]
          rw [pinsRow_getD β d1.qs m1 j 0 xs1 hjm]
          rw [if_pos (by rw [Nat.zero_add]; exact hq)]
        exact ⟨by omega, by omega, hpins1 j hjm hlive⟩
      · exact absurd (hbeyond j (by omega) hj) hne
    · intro j hj hq
      by_cases hjm : j < m1
      · rw [hts1, List.append_assoc]
        rw [getD_append_left _ _ j (by omega)]
        rw [pinsRow_getD β d1.qs m1 j 0 xs1 hjm]
        rw [if_pos (by rw [Nat.zero_add]; exact hq)]
      · exact hbeyond j (by omega) hj
  | @app Ca f uf Cb x ux hf hx ihf _ =>
    intro k xs us ht hu hlen
    rcases apps_shape xs _ _ ht.symm with ⟨h1, h2⟩ | ⟨xs0, xl, h1, h2⟩
    · exact Term.noConfusion h2
    · rcases apps_shape us _ _ hu.symm with ⟨h3, h4⟩ | ⟨us0, ul, h3, h4⟩
      · exact Term.noConfusion h4
      · subst h1
        subst h3
        cases h2
        cases h4
        obtain ⟨dk, ts, ph, Css0, hk1, hlc0, hall0, hsub0, hlts,
          hcompat0, hslack0, hpin0, hmask0⟩ := ihf _root_.rfl _root_.rfl (by
            simp only [List.length_append, List.length_cons,
              List.length_nil] at hlen
            omega)
        have hlas : xs0.length = us0.length := by
          simp only [List.length_append, List.length_cons,
            List.length_nil] at hlen
          omega
        refine ⟨dk, ts, ph, Css0 ++ [Cb], hk1, by
          simp only [List.length_append, List.length_cons,
            List.length_nil]
          omega, ?_, ?_, hlts, ?_, ?_, ?_, hmask0⟩
        · intro p hp
          rw [zip_append_of_len Css0 xs0 [Cb] [x] (by omega),
            zip_append_of_len (Css0.zip xs0) us0 ([Cb].zip [x]) [ux]
              (by simp only [List.length_zip]; omega)] at hp
          rcases List.mem_append.mp hp with h5 | h6
          · exact hall0 p h5
          · simp only [List.zip_cons_cons, List.zip_nil_right,
              List.mem_singleton] at h6
            subst h6
            exact hx
        · rw [List.flatten_append]
          show Sub (((k, ts, ph) :: Css0.flatten) ++ (Cb ++ []))
            (Ca ++ Cb)
          refine Sub.append hsub0 ?_
          exact (Sub.refl Cb).perm_left (by simp)
        · intro j hj
          rcases hcompat0 j hj with h5 | ⟨h6, h7⟩
          · exact Or.inl h5
          · right
            refine ⟨by
              simp only [List.length_append, List.length_cons,
                List.length_nil]
              omega, ?_⟩
            rw [h7]
            congr 2
            exact (getD_append_left xs0 [x] j h6).symm
        · obtain ⟨ss, hs1, hs2⟩ := hslack0
          refine ⟨ss, hs1, ?_⟩
          simp only [List.length_append, List.length_cons,
            List.length_nil]
          omega
        · intro j hj hne
          obtain ⟨h6, h7, h8⟩ := hpin0 j hj hne
          refine ⟨by
            simp only [List.length_append, List.length_cons,
              List.length_nil]
            omega, by
            simp only [List.length_append, List.length_cons,
              List.length_nil]
            omega, ?_⟩
          rw [getD_append_left xs0 [x] j h6, getD_append_left us0 [ux] j h7]
          exact h8
  | adt =>
    intro k xs us ht hu hlen
    rcases apps_shape us _ _ hu.symm with ⟨h1, h2⟩ | ⟨us0, ul, h1, h2⟩
    · exact Term.noConfusion h2
    · exact Term.noConfusion h2
  | ctr =>
    intro k xs us ht hu hlen
    rcases apps_shape us _ _ hu.symm with ⟨h1, h2⟩ | ⟨us0, ul, h1, h2⟩
    · rcases apps_shape xs _ _ ht.symm with ⟨h3, h4⟩ | ⟨xs0, xl, h3, h4⟩
      · exact Term.noConfusion h4
      · exact Term.noConfusion h4
    · exact Term.noConfusion h2
  | efq =>
    intro k xs us ht hu hlen
    rcases apps_shape us _ _ hu.symm with ⟨h1, h2⟩ | ⟨us0, ul, h1, h2⟩
    · exact Term.noConfusion h2
    · exact Term.noConfusion h2
  | rfl =>
    intro k xs us ht hu hlen
    rcases apps_shape us _ _ hu.symm with ⟨h1, h2⟩ | ⟨us0, ul, h1, h2⟩
    · exact Term.noConfusion h2
    · exact Term.noConfusion h2
  | lam _ _ =>
    intro k xs us ht hu hlen
    rcases apps_shape us _ _ hu.symm with ⟨h1, h2⟩ | ⟨us0, ul, h1, h2⟩
    · exact Term.noConfusion h2
    · exact Term.noConfusion h2
  | mat _ _ _ _ _ _ =>
    intro k xs us ht hu hlen
    rcases apps_shape us _ _ hu.symm with ⟨h1, h2⟩ | ⟨us0, ul, h1, h2⟩
    · exact Term.noConfusion h2
    · exact Term.noConfusion h2
  | rwt _ _ _ _ =>
    intro k xs us ht hu hlen
    rcases apps_shape us _ _ hu.symm with ⟨h1, h2⟩ | ⟨us0, ul, h1, h2⟩
    · exact Term.noConfusion h2
    · exact Term.noConfusion h2
  | let_ _ _ _ _ =>
    intro k xs us ht hu hlen
    rcases apps_shape us _ _ hu.symm with ⟨h1, h2⟩ | ⟨us0, ul, h1, h2⟩
    · exact Term.noConfusion h2
    · exact Term.noConfusion h2
  | pad _ hs ih =>
    intro k xs us ht hu hlen
    obtain ⟨dk, ts, ph, Css, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
      ih ht hu hlen
    exact ⟨dk, ts, ph, Css, h1, h2, h3, h4.trans hs, h5, h6, h7, h8, h9⟩

theorem MMeas_of_sub_wgt (h : Sub C' C) {w' w : Nat} (hw : w' < w) :
    MMeas (C', w') (C, w) := by
  rcases h.mplus_or_perm with h1 | h1
  · exact Or.inl h1
  · exact Or.inr ⟨h1, hw⟩

theorem MLe_of_sub_wgt (h : Sub C' C) {w' w : Nat} (hw : w' ≤ w) :
    MLe (C', w') (C, w) := by
  rcases h.mplus_or_perm with h1 | h1
  · exact Or.inl (Or.inl h1)
  · by_cases hw2 : w' = w
    · subst hw2
      exact Or.inr ⟨h1, _root_.rfl⟩
    · exact Or.inl (Or.inr ⟨h1, by omega⟩)

-- the pair-pricing inversions, with Sub slack
theorem CG.pair_lam_inv : ∀ {C : List Charge} {t u : Term}, CG β C t u →
    ∀ {f uf : Term}, t = .Lam f → u = .Lam uf →
    ∃ C0, CG β C0 f uf ∧ Sub C0 C := by
  intro C t u h
  induction h with
  | lam hf _ =>
    intro f uf ht hu
    cases ht
    cases hu
    exact ⟨_, hf, Sub.refl _⟩
  | refa =>
    intro f uf ht hu
    exact Term.noConfusion ht
  | pad _ hs ih =>
    intro f uf ht hu
    obtain ⟨C0, h0, hsub⟩ := ih ht hu
    exact ⟨C0, h0, hsub.trans hs⟩
  | site _ _ _ _ _ _ _ _ =>
    intro f uf ht hu
    rcases apps_shape _ _ _ hu with ⟨h1, h2⟩ | ⟨us0, ul, h1, h2⟩
    · exact Term.noConfusion h2.symm
    · exact Term.noConfusion h2.symm
  | typ_ => intro f uf ht hu; exact Term.noConfusion hu
  | var => intro f uf ht hu; exact Term.noConfusion hu
  | ref _ => intro f uf ht hu; exact Term.noConfusion hu
  | adt => intro f uf ht hu; exact Term.noConfusion hu
  | ctr => intro f uf ht hu; exact Term.noConfusion hu
  | efq => intro f uf ht hu; exact Term.noConfusion hu
  | rfl => intro f uf ht hu; exact Term.noConfusion hu
  | app _ _ _ _ => intro f uf ht hu; exact Term.noConfusion hu
  | mat _ _ _ _ _ _ => intro f uf ht hu; exact Term.noConfusion hu
  | rwt _ _ _ _ => intro f uf ht hu; exact Term.noConfusion hu
  | let_ _ _ _ _ => intro f uf ht hu; exact Term.noConfusion hu

theorem CG.pair_app_inv : ∀ {C : List Charge} {t u : Term}, CG β C t u →
    ∀ {f a uf ua : Term}, t = .App f a → u = .App uf ua →
    (∀ j (xs : List Term), t ≠ Term.apps (.Ref j) xs) →
    ∃ Ca Cb, CG β Ca f uf ∧ CG β Cb a ua ∧ Sub (Ca ++ Cb) C := by
  intro C t u h
  induction h with
  | app hf ha _ _ =>
    intro f a uf ua ht hu _
    cases ht
    cases hu
    exact ⟨_, _, hf, ha, Sub.refl _⟩
  | refa =>
    intro f a uf ua ht hu _
    exact Term.noConfusion ht
  | pad _ hs ih =>
    intro f a uf ua ht hu hnr
    obtain ⟨Ca, Cb, h1, h2, hsub⟩ := ih ht hu hnr
    exact ⟨Ca, Cb, h1, h2, hsub.trans hs⟩
  | @site k1 d1 xs1 us1 m1 ts1 Css1 ph1 _ _ _ _ _ _ _ _ =>
    intro f a uf ua ht hu hnr
    exact absurd _root_.rfl (hnr k1 xs1)
  | typ_ => intro f a uf ua ht hu _; exact Term.noConfusion hu
  | var => intro f a uf ua ht hu _; exact Term.noConfusion hu
  | ref _ => intro f a uf ua ht hu _; exact Term.noConfusion hu
  | adt => intro f a uf ua ht hu _; exact Term.noConfusion hu
  | ctr => intro f a uf ua ht hu _; exact Term.noConfusion hu
  | efq => intro f a uf ua ht hu _; exact Term.noConfusion hu
  | rfl => intro f a uf ua ht hu _; exact Term.noConfusion hu
  | lam _ _ => intro f a uf ua ht hu _; exact Term.noConfusion hu
  | mat _ _ _ _ _ _ => intro f a uf ua ht hu _; exact Term.noConfusion hu
  | rwt _ _ _ _ => intro f a uf ua ht hu _; exact Term.noConfusion hu
  | let_ _ _ _ _ => intro f a uf ua ht hu _; exact Term.noConfusion hu

theorem CG.pair_let_inv : ∀ {C : List Charge} {t u : Term}, CG β C t u →
    ∀ {qq qq' : Quant} {v0 b0 uv ub : Term},
    t = .Let qq v0 b0 → u = .Let qq' uv ub →
    ∃ Ca Cb, CG β Ca v0 uv ∧ CG β Cb b0 ub ∧ Sub (Ca ++ Cb) C := by
  intro C t u h
  induction h with
  | let_ hv hb _ _ =>
    intro qq qq' v0 b0 uv ub ht hu
    cases ht
    cases hu
    exact ⟨_, _, hv, hb, Sub.refl _⟩
  | refa =>
    intro qq qq' v0 b0 uv ub ht hu
    exact Term.noConfusion ht
  | pad _ hs ih =>
    intro qq qq' v0 b0 uv ub ht hu
    obtain ⟨Ca, Cb, h1, h2, hsub⟩ := ih ht hu
    exact ⟨Ca, Cb, h1, h2, hsub.trans hs⟩
  | site _ _ _ _ _ _ _ _ =>
    intro qq qq' v0 b0 uv ub ht hu
    rcases apps_shape _ _ _ hu with ⟨h1, h2⟩ | ⟨us0, ul, h1, h2⟩
    · exact Term.noConfusion h2.symm
    · exact Term.noConfusion h2.symm
  | typ_ => intro qq qq' v0 b0 uv ub ht hu; exact Term.noConfusion hu
  | var => intro qq qq' v0 b0 uv ub ht hu; exact Term.noConfusion hu
  | ref _ => intro qq qq' v0 b0 uv ub ht hu; exact Term.noConfusion hu
  | adt => intro qq qq' v0 b0 uv ub ht hu; exact Term.noConfusion hu
  | ctr => intro qq qq' v0 b0 uv ub ht hu; exact Term.noConfusion hu
  | efq => intro qq qq' v0 b0 uv ub ht hu; exact Term.noConfusion hu
  | rfl => intro qq qq' v0 b0 uv ub ht hu; exact Term.noConfusion hu
  | lam _ _ => intro qq qq' v0 b0 uv ub ht hu; exact Term.noConfusion hu
  | app _ _ _ _ => intro qq qq' v0 b0 uv ub ht hu; exact Term.noConfusion hu
  | mat _ _ _ _ _ _ => intro qq qq' v0 b0 uv ub ht hu; exact Term.noConfusion hu
  | rwt _ _ _ _ => intro qq qq' v0 b0 uv ub ht hu; exact Term.noConfusion hu

theorem CG.pair_rwt_inv : ∀ {C : List Charge} {t u : Term}, CG β C t u →
    ∀ {e P f ue um uf : Term},
    t = .Rwt e P f → u = .Rwt ue um uf →
    ∃ Ca Cb, CG β Ca e ue ∧ CG β Cb f uf ∧ Sub (Ca ++ Cb) C := by
  intro C t u h
  induction h with
  | rwt he hf _ _ =>
    intro e P f ue um uf ht hu
    cases ht
    cases hu
    exact ⟨_, _, he, hf, Sub.refl _⟩
  | refa =>
    intro e P f ue um uf ht hu
    exact Term.noConfusion ht
  | pad _ hs ih =>
    intro e P f ue um uf ht hu
    obtain ⟨Ca, Cb, h1, h2, hsub⟩ := ih ht hu
    exact ⟨Ca, Cb, h1, h2, hsub.trans hs⟩
  | site _ _ _ _ _ _ _ _ =>
    intro e P f ue um uf ht hu
    rcases apps_shape _ _ _ hu with ⟨h1, h2⟩ | ⟨us0, ul, h1, h2⟩
    · exact Term.noConfusion h2.symm
    · exact Term.noConfusion h2.symm
  | typ_ => intro e P f ue um uf ht hu; exact Term.noConfusion hu
  | var => intro e P f ue um uf ht hu; exact Term.noConfusion hu
  | ref _ => intro e P f ue um uf ht hu; exact Term.noConfusion hu
  | adt => intro e P f ue um uf ht hu; exact Term.noConfusion hu
  | ctr => intro e P f ue um uf ht hu; exact Term.noConfusion hu
  | efq => intro e P f ue um uf ht hu; exact Term.noConfusion hu
  | rfl => intro e P f ue um uf ht hu; exact Term.noConfusion hu
  | lam _ _ => intro e P f ue um uf ht hu; exact Term.noConfusion hu
  | app _ _ _ _ => intro e P f ue um uf ht hu; exact Term.noConfusion hu
  | mat _ _ _ _ _ _ =>
    intro e P f ue um uf ht hu
    exact Term.noConfusion hu
  | let_ _ _ _ _ => intro e P f ue um uf ht hu; exact Term.noConfusion hu

theorem CG.pair_mat_inv : ∀ {C : List Charge} {t u : Term}, CG β C t u →
    ∀ {a c : Nat} {h0 m0 uh um : Term},
    t = .Mat a c h0 m0 → u = .Mat a c uh um →
    ∃ Ch Cm, CG β Ch h0 uh ∧ CG β Cm m0 um ∧ Sub Ch C ∧ Sub Cm C := by
  intro C t u h
  induction h with
  | mat hh hm hsh hsm _ _ =>
    intro a c h0 m0 uh um ht hu
    cases ht
    cases hu
    exact ⟨_, _, hh, hm, hsh, hsm⟩
  | refa =>
    intro a c h0 m0 uh um ht hu
    exact Term.noConfusion ht
  | pad _ hs ih =>
    intro a c h0 m0 uh um ht hu
    obtain ⟨Ch, Cm, h1, h2, hs1, hs2⟩ := ih ht hu
    exact ⟨Ch, Cm, h1, h2, hs1.trans hs, hs2.trans hs⟩
  | site _ _ _ _ _ _ _ _ =>
    intro a c h0 m0 uh um ht hu
    rcases apps_shape _ _ _ hu with ⟨h1, h2⟩ | ⟨us0, ul, h1, h2⟩
    · exact Term.noConfusion h2.symm
    · exact Term.noConfusion h2.symm
  | typ_ => intro a c h0 m0 uh um ht hu; exact Term.noConfusion hu
  | var => intro a c h0 m0 uh um ht hu; exact Term.noConfusion hu
  | ref _ => intro a c h0 m0 uh um ht hu; exact Term.noConfusion hu
  | adt => intro a c h0 m0 uh um ht hu; exact Term.noConfusion hu
  | ctr => intro a c h0 m0 uh um ht hu; exact Term.noConfusion hu
  | efq => intro a c h0 m0 uh um ht hu; exact Term.noConfusion hu
  | rfl => intro a c h0 m0 uh um ht hu; exact Term.noConfusion hu
  | lam _ _ => intro a c h0 m0 uh um ht hu; exact Term.noConfusion hu
  | app _ _ _ _ => intro a c h0 m0 uh um ht hu; exact Term.noConfusion hu
  | rwt _ _ _ _ => intro a c h0 m0 uh um ht hu; exact Term.noConfusion hu
  | let_ _ _ _ _ => intro a c h0 m0 uh um ht hu; exact Term.noConfusion hu

-- a data-headed spine's charges are its arguments', one list each
theorem CG.adt_spine_inv : ∀ {C : List Charge} {t u : Term}, CG β C t u →
    ∀ {a : Nat} {r : List Nat} {as us : List Term},
    t = Term.apps (.Adt a r) as → u = Term.apps (.Adt a r) us →
    as.length = us.length →
    ∃ Css : List (List Charge), Css.length = us.length ∧
      (∀ p ∈ (Css.zip as).zip us, CG β p.1.1 p.1.2 p.2) ∧
      Sub Css.flatten C := by
  intro C t u h
  induction h with
  | typ_ =>
    intro a r as us ht hu hlen
    rcases apps_shape us _ _ hu.symm with ⟨h1, h2⟩ | ⟨us0, ul, h1, h2⟩
    · exact Term.noConfusion h2
    · exact Term.noConfusion h2
  | refa =>
    intro a r as us ht hu hlen
    rcases apps_shape as _ _ ht.symm with ⟨h1, h2⟩ | ⟨as0, al, h1, h2⟩
    · exact Term.noConfusion h2
    · exact Term.noConfusion h2
  | var =>
    intro a r as us ht hu hlen
    rcases apps_shape us _ _ hu.symm with ⟨h1, h2⟩ | ⟨us0, ul, h1, h2⟩
    · exact Term.noConfusion h2
    · exact Term.noConfusion h2
  | ref _ =>
    intro a r as us ht hu hlen
    rcases apps_shape us _ _ hu.symm with ⟨h1, h2⟩ | ⟨us0, ul, h1, h2⟩
    · exact Term.noConfusion h2
    · exact Term.noConfusion h2
  | @site k1 d1 xs1 us1 m1 ts1 Css1 ph1 _ _ _ _ _ _ _ _ =>
    intro a r as us ht hu hlen
    exfalso
    have h1 := Term.apps_head_inv (h := .Ref k1) (h' := .Adt a r)
      (by trivial) (by trivial) ht
    exact Term.noConfusion h1.1
  | adt =>
    intro a r as us ht hu hlen
    rcases apps_shape as _ _ ht.symm with ⟨h1, h2⟩ | ⟨as0, al, h1, h2⟩
    · subst h1
      rcases apps_shape us _ _ hu.symm with ⟨h3, h4⟩ | ⟨us0, ul, h3, h4⟩
      · subst h3
        refine ⟨[], _root_.rfl, ?_, Sub.refl _⟩
        intro p hp
        exact nomatch hp
      · exact Term.noConfusion h4
    · exact Term.noConfusion h2
  | ctr =>
    intro a r as us ht hu hlen
    rcases apps_shape as _ _ ht.symm with ⟨h1, h2⟩ | ⟨as0, al, h1, h2⟩
    · exact Term.noConfusion h2
    · exact Term.noConfusion h2
  | efq =>
    intro a r as us ht hu hlen
    rcases apps_shape us _ _ hu.symm with ⟨h1, h2⟩ | ⟨us0, ul, h1, h2⟩
    · exact Term.noConfusion h2
    · exact Term.noConfusion h2
  | rfl =>
    intro a r as us ht hu hlen
    rcases apps_shape us _ _ hu.symm with ⟨h1, h2⟩ | ⟨us0, ul, h1, h2⟩
    · exact Term.noConfusion h2
    · exact Term.noConfusion h2
  | lam _ _ =>
    intro a r as us ht hu hlen
    rcases apps_shape us _ _ hu.symm with ⟨h1, h2⟩ | ⟨us0, ul, h1, h2⟩
    · exact Term.noConfusion h2
    · exact Term.noConfusion h2
  | @app Ca f uf Cb x ux hf hx ihf _ =>
    intro a r as us ht hu hlen
    rcases apps_shape as _ _ ht.symm with ⟨h1, h2⟩ | ⟨as0, al, h1, h2⟩
    · exact Term.noConfusion h2
    · rcases apps_shape us _ _ hu.symm with ⟨h3, h4⟩ | ⟨us0, ul, h3, h4⟩
      · exact Term.noConfusion h4
      · subst h1
        subst h3
        cases h2
        cases h4
        obtain ⟨Css0, hlen0, hpair0, hsub0⟩ := ihf _root_.rfl _root_.rfl
          (by
            simp only [List.length_append, List.length_cons,
              List.length_nil] at hlen
            omega)
        refine ⟨Css0 ++ [Cb], ?_, ?_, ?_⟩
        · simp only [List.length_append, List.length_cons,
            List.length_nil]
          omega
        · intro p hp
          rw [zip_append_of_len Css0 as0 [Cb] [x] (by
              simp only [List.length_append, List.length_cons,
                List.length_nil] at hlen
              omega),
            zip_append_of_len (Css0.zip as0) us0 ([Cb].zip [x]) [ux]
              (by
                simp only [List.length_zip, List.length_append,
                  List.length_cons, List.length_nil] at hlen ⊢
                omega)] at hp
          rcases List.mem_append.mp hp with h5 | h6
          · exact hpair0 p h5
          · simp only [List.zip_cons_cons, List.zip_nil_right,
              List.mem_singleton] at h6
            subst h6
            exact hx
        · rw [List.flatten_append]
          show Sub (Css0.flatten ++ (Cb ++ List.flatten [])) (Ca ++ Cb)
          rw [List.flatten_nil, List.append_nil]
          exact Sub.append hsub0 (Sub.refl Cb)
  | mat _ _ _ _ _ _ =>
    intro a r as us ht hu hlen
    rcases apps_shape us _ _ hu.symm with ⟨h1, h2⟩ | ⟨us0, ul, h1, h2⟩
    · exact Term.noConfusion h2
    · exact Term.noConfusion h2
  | rwt _ _ _ _ =>
    intro a r as us ht hu hlen
    rcases apps_shape us _ _ hu.symm with ⟨h1, h2⟩ | ⟨us0, ul, h1, h2⟩
    · exact Term.noConfusion h2
    · exact Term.noConfusion h2
  | let_ _ _ _ _ =>
    intro a r as us ht hu hlen
    rcases apps_shape us _ _ hu.symm with ⟨h1, h2⟩ | ⟨us0, ul, h1, h2⟩
    · exact Term.noConfusion h2
    · exact Term.noConfusion h2
  | pad _ hs ih =>
    intro a r as us ht hu hlen
    obtain ⟨Css0, hlen0, hpair0, hsub0⟩ := ih ht hu hlen
    exact ⟨Css0, hlen0, hpair0, hsub0.trans hs⟩

-- the deepening walk: evaluate a spine's live arms to era-paired deep
-- values through a caller-supplied evaluation contract; dead arms ride
theorem deepen_spine (hβ : Book.Closed β) :
    ∀ (as : List Term) {T0 T' : Term} {us : List Term},
    EraSpine β [] T0 as T' us →
    (∀ x ∈ as, x.Closed 0) →
    ∀ (Css : List (List Charge)),
    Css.length = us.length →
    (∀ p ∈ (Css.zip as).zip us, CG β p.1.1 p.1.2 p.2) →
    ∀ (C0 : List Charge) (W0 : Nat),
    Sub Css.flatten C0 →
    (us.map (Term.wgt (fun _ => 1))).sum < W0 →
    (∀ x ∈ as, ∀ (B' ub' : Term) (Cx : List Charge),
      Era β [] x B' ub' → x.Closed 0 → CG β Cx x ub' →
      Sub Cx C0 → Term.wgt (fun _ => 1) ub' < W0 →
      ∃ v uv Cv, Red β .weak x v ∧ v.Closed 0 ∧
        Era β [] v B' uv ∧ DeepP β v uv ∧ CG β Cv v uv ∧
        MLe (Cv, Term.wgt (fun _ => 1) uv)
          (Cx, Term.wgt (fun _ => 1) ub') ∧
        (ub' = .Typ → v = x) ∧ (DeepP β x ub' → v = x)) →
    ∃ (vs uvs : List Term) (Css2 : List (List Charge)) (T2 : Term),
      (∀ h : Term, Red β .weak (Term.apps h as) (Term.apps h vs)) ∧
      vs.length = as.length ∧
      (∀ x ∈ vs, x.Closed 0) ∧
      (∀ p ∈ vs.zip uvs, p.2 = .Typ ∨ DeepP β p.1 p.2) ∧
      EraSpine β [] T0 vs T2 uvs ∧ Conv β T2 T' ∧
      Css2.length = uvs.length ∧
      (∀ p ∈ (Css2.zip vs).zip uvs, CG β p.1.1 p.1.2 p.2) ∧
      MLe (Css2.flatten, (uvs.map (Term.wgt (fun _ => 1))).sum)
        (Css.flatten, (us.map (Term.wgt (fun _ => 1))).sum) ∧
      (∀ j, j < as.length →
        (us.getD j .Typ = .Typ
          ∨ DeepP β (as.getD j .Typ) (us.getD j .Typ)) →
        vs.getD j .Typ = as.getD j .Typ) := by
  intro as
  induction as with
  | nil =>
    intro T0 T' us hsp hcl Css hlenc hpair C0 W0 hsubC hwlt hrun
    cases hsp with
    | nil =>
      cases Css with
      | cons _ _ => exact absurd hlenc (by simp)
      | nil =>
        refine ⟨[], [], [], T0, fun h => Red.refl, _root_.rfl,
          (by intro x hx; exact nomatch hx),
          (by intro p hp; exact nomatch hp),
          .nil, Conv.refl _, _root_.rfl,
          (by intro p hp; exact nomatch hp), MLe.refl _,
          (by intro j hj _; exact absurd hj (by simp))⟩
  | cons x as' ih =>
    intro T0 T' us hsp hcl Css hlenc hpair C0 W0 hsubC hwlt hrun
    cases hsp with
    | @live _ A B _ ux _ _ us' hc0 hx hrest =>
      cases Css with
      | nil => exact absurd hlenc (by simp)
      | cons Cx Css' =>
        have hwcons : (List.map (Term.wgt (fun _ => 1)) (ux :: us')).sum
            = Term.wgt (fun _ => 1) ux
              + (us'.map (Term.wgt (fun _ => 1))).sum := by
          simp
        rw [hwcons] at hwlt
        have hfl : (Cx :: Css').flatten = Cx ++ Css'.flatten := _root_.rfl
        rw [hfl] at hsubC
        obtain ⟨v, uv, Cv, hred, hvcl, herav, hdeep, hcgv, hmle,
            hclau1, hclau2⟩ :=
          hrun x List.mem_cons_self A ux Cx hx (hcl x List.mem_cons_self)
            (hpair ((Cx, x), ux) (by
              simp only [List.zip_cons_cons]
              exact List.mem_cons_self))
            ((Sub.append_right Cx Css'.flatten).trans hsubC)
            (by omega)
        obtain ⟨T2s, hrest2, hcseat⟩ := hrest.conv_start hβ
          (Conv.subst hβ (Conv.refl B) (Conv.of_red_rev hred.strong) 0)
        obtain ⟨vs', uvs', Css2', T2, hredt, hlenv, hclv, hpairv,
            hsp2, hcv2, hlenc2, hpair2, hmle2, hposu⟩ :=
          ih hrest2 (fun y hy => hcl y (List.mem_cons_of_mem x hy)) Css'
            (by
              simp only [List.length_cons] at hlenc
              omega)
            (fun p hp => hpair p (by
              simp only [List.zip_cons_cons]
              exact List.mem_cons_of_mem _ hp))
            C0 W0
            ((Sub.append_left Css'.flatten Cx).trans hsubC)
            (by omega)
            (fun y hy => hrun y (List.mem_cons_of_mem x hy))
        refine ⟨v :: vs', uv :: uvs', Cv :: Css2', T2, ?_, ?_, ?_, ?_,
          .live hc0 herav hsp2, Conv.trans hβ hcv2 hcseat, ?_, ?_, ?_,
          ?_⟩
        · intro h
          refine Red.trans ?_ (hredt (.App h v))
          show Red β .weak (Term.apps (.App h x) as')
            (Term.apps (.App h v) as')
          exact Red.apps (Red.app_a_w hred) as'
        · simp only [List.length_cons]
          omega
        · intro y hy
          rcases List.mem_cons.mp hy with h1 | h2
          · subst h1
            exact hvcl
          · exact hclv y h2
        · intro p hp
          simp only [List.zip_cons_cons] at hp
          rcases List.mem_cons.mp hp with h1 | h2
          · subst h1
            exact Or.inr hdeep
          · exact hpairv p h2
        · simp only [List.length_cons]
          omega
        · intro p hp
          simp only [List.zip_cons_cons] at hp
          rcases List.mem_cons.mp hp with h1 | h2
          · subst h1
            exact hcgv
          · exact hpair2 p h2
        · show MLe (Cv ++ Css2'.flatten, Term.wgt (fun _ => 1) uv
              + (uvs'.map (Term.wgt (fun _ => 1))).sum)
            (Cx ++ Css'.flatten, Term.wgt (fun _ => 1) ux
              + (us'.map (Term.wgt (fun _ => 1))).sum)
          exact MLe.trans
            (MLe.frame Cx (Term.wgt (fun _ => 1) ux) hmle2)
            (MLe.frame_left Css2'.flatten
              ((uvs'.map (Term.wgt (fun _ => 1))).sum) hmle)
        · intro j hj hdisj
          cases j with
          | zero =>
            rcases hdisj with h1 | h2
            · exact hclau1 h1
            · exact hclau2 h2
          | succ j' =>
            simp only [List.length_cons] at hj
            exact hposu j' (by omega) hdisj
    | @dead _ A B _ πx _ _ us' hc0 hchk hrest =>
      cases Css with
      | nil => exact absurd hlenc (by simp)
      | cons Cx Css' =>
        have hwcons : (List.map (Term.wgt (fun _ => 1))
            (Term.Typ :: us')).sum
            = Term.wgt (fun _ => 1) .Typ
              + (us'.map (Term.wgt (fun _ => 1))).sum := by
          simp
        rw [hwcons] at hwlt
        have hfl : (Cx :: Css').flatten = Cx ++ Css'.flatten := _root_.rfl
        rw [hfl] at hsubC
        obtain ⟨vs', uvs', Css2', T2, hredt, hlenv, hclv, hpairv,
            hsp2, hcv2, hlenc2, hpair2, hmle2, hposu⟩ :=
          ih hrest (fun y hy => hcl y (List.mem_cons_of_mem x hy)) Css'
            (by
              simp only [List.length_cons] at hlenc
              omega)
            (fun p hp => hpair p (by
              simp only [List.zip_cons_cons]
              exact List.mem_cons_of_mem _ hp))
            C0 W0
            ((Sub.append_left Css'.flatten Cx).trans hsubC)
            (by omega)
            (fun y hy => hrun y (List.mem_cons_of_mem x hy))
        refine ⟨x :: vs', .Typ :: uvs', Cx :: Css2', T2, ?_, ?_, ?_, ?_,
          .dead hc0 hchk hsp2, hcv2, ?_, ?_, ?_, ?_⟩
        · intro h
          exact hredt (.App h x)
        · simp only [List.length_cons]
          omega
        · intro y hy
          rcases List.mem_cons.mp hy with h1 | h2
          · subst h1
            exact hcl _ List.mem_cons_self
          · exact hclv y h2
        · intro p hp
          simp only [List.zip_cons_cons] at hp
          rcases List.mem_cons.mp hp with h1 | h2
          · subst h1
            exact Or.inl _root_.rfl
          · exact hpairv p h2
        · simp only [List.length_cons]
          omega
        · intro p hp
          simp only [List.zip_cons_cons] at hp
          rcases List.mem_cons.mp hp with h1 | h2
          · subst h1
            exact hpair ((Cx, x), .Typ) (by
              simp only [List.zip_cons_cons]
              exact List.mem_cons_self)
          · exact hpair2 p h2
        · show MLe (Cx ++ Css2'.flatten, Term.wgt (fun _ => 1) .Typ
              + (uvs'.map (Term.wgt (fun _ => 1))).sum)
            (Cx ++ Css'.flatten, Term.wgt (fun _ => 1) .Typ
              + (us'.map (Term.wgt (fun _ => 1))).sum)
          exact MLe.frame Cx (Term.wgt (fun _ => 1) .Typ) hmle2
        · intro j hj hdisj
          cases j with
          | zero => rfl
          | succ j' =>
            simp only [List.length_cons] at hj
            exact hposu j' (by omega) hdisj

-- pricing the suspension: an underapplied call's remaining tree.
-- Every leaf below prices with its pins capped at the consumed
-- region, strictly under the spent charge via the slack slot.
theorem Tree.suspend (hβ : Book.Closed β) (hok : Book.Ok β)
    {k : Nat} {dk : DefD} (hd : Book.defn β k = some dk)
    (vs : List Term) (hvsc : ∀ v ∈ vs, v.Closed 0)
    (hmWd : vs.length < dk.n)
    (sp : List (Option Nat)) (hspl : sp.length = dk.n + 1)
    (hspc : ∀ j, j < vs.length → sp.getD j none = none
      ∨ sp.getD j none = some (Term.csize β (vs.getD j .Typ)))
    (hspfree : ∀ j, vs.length ≤ j → j < dk.n → sp.getD j none = none)
    (hslack : ∃ ss, sp.getD dk.n none = some ss
      ∧ dk.n - vs.length ≤ ss)
    (hspmask : ∀ j, j < dk.n → dk.qs.getD j .Lone = .None →
      sp.getD j none = none)
    (ph0 : Bool)
    (env uenv : List Term) (Css : List (List Charge))
    (hl1 : env.length = uenv.length) (hl2 : Css.length = uenv.length)
    (henv : ∀ v ∈ env, v.Closed 0)
    (huenv : ∀ v ∈ uenv, v.Closed 0)
    (hpair : ∀ p ∈ (Css.zip env).zip uenv, CG β p.1.1 p.1.2 p.2)
    (henvP : ∀ p ∈ env.zip uenv, p.2 = .Typ ∨ DeepP β p.1 p.2) :
    ∀ {lhs : Term} {n : Nat} {node : Term}, Tree β k dk.qs lhs n node →
    ∀ (Γ : Ctx) (Braw ubraw : Term), Era β Γ node Braw ubraw →
    ∀ (d : Nat), Γ.length = d + env.length →
    (∀ i, i < uenv.length → Term.occ (d + i) ubraw ≤ 1) →
    Term.lhsOk lhs →
    ((∃ opencols : List Term, (∀ L, lhs ≠ .Lam L) ∧
        Term.msubstAt d env lhs = Term.apps (.Ref k) (vs ++ opencols))
     ∨ (∃ (L T : Term) (j : Nat) (opencols : List Term), lhs = .Lam L ∧
        Term.msubstAt d env lhs = Term.lams (j + 1)
          (.App (Term.apps (.Ref k) (vs ++ opencols)) T))) →
    ∃ (Cs : List Charge) (Crs : List (List Charge)),
      Crs.length = uenv.length ∧
      CG β (Cs ++ Crs.flatten) (Term.msubstAt d env node)
        (Term.msubstAt d uenv ubraw) ∧
      (∀ i, i < uenv.length → Sub (Crs.getD i []) (Css.getD i []) ∧
        (Term.occ (d + i) ubraw = 0 → Crs.getD i [] = [])) ∧
      (∀ c ∈ Cs, CLt c (k, sp, ph0)) := by
  intro lhs n node htree
  induction htree with
  | @bod cols0 t0 n0 hguard =>
    intro Γ Braw ubraw hraw d hΓl hocc hlok hstate
    rcases hstate with
      ⟨opencols, hnl, hinst⟩ | ⟨L, T, j, opencols, hlhsL, _⟩
    · rw [Term.msubstAt_apps, Term.msubstAt_ref] at hinst
      obtain ⟨_, hargs⟩ := Term.apps_head_inv (h := Term.Ref k)
        (h' := Term.Ref k) (by trivial) (by trivial) hinst
      have hsplit : (cols0.take vs.length).map (Term.msubstAt d env)
          = vs := by
        rw [List.map_take, hargs]
        rw [show vs.length = vs.length from _root_.rfl]
        exact take_append vs opencols
      exact Guard.era_cg_susp hβ hok hd vs hvsc hmWd sp hspl hspc hspfree
        hslack hspmask ph0 hguard hraw d env uenv Css hΓl hl1 hl2 henv huenv hpair henvP
        hocc ⟨cols0.take vs.length, cols0.drop vs.length,
          List.take_append_drop _ _, hsplit⟩ trivial
    · exfalso
      rcases apps_shape cols0 (.Ref k) _ _root_.rfl.symm with
        ⟨h1, h2⟩ | ⟨as0, al, h1, h2⟩
      · rw [hlhsL] at h2
        exact Term.noConfusion h2
      · rw [hlhsL] at h2
        exact Term.noConfusion h2
  | @lam n0 lhs0 f0 hn htree0 ih =>
    intro Γ Braw ubraw hraw d hΓl hocc hlok hstate
    obtain ⟨q1, A1, B1, ufr, hcvL, hbraw, hoccf, hueqr⟩ :=
      Era.lam_inv hβ hraw
    subst hueqr
    have henvc : ∀ w ∈ env, Term.Closed 0 w := henv
    have hocc' : ∀ i, i < uenv.length →
        Term.occ (d + 1 + i) ufr ≤ 1 := by
      intro i hi
      have h1 := hocc i hi
      simp only [Term.occ] at h1
      rw [show d + 1 + i = d + i + 1 from by omega]
      exact h1
    have hlok' : Term.lhsOk (Term.applyB (Term.shift 0 lhs0) (.Var 0)) :=
      Term.lhsOk.applyB (Term.lhsOk.shift lhs0 hlok 0) _
    have hstate' :
        (∃ opencols : List Term,
          (∀ L, Term.applyB (Term.shift 0 lhs0) (.Var 0) ≠ .Lam L) ∧
          Term.msubstAt (d + 1) env
            (Term.applyB (Term.shift 0 lhs0) (.Var 0))
            = Term.apps (.Ref k) (vs ++ opencols))
        ∨ (∃ (L T : Term) (j : Nat) (opencols : List Term),
          Term.applyB (Term.shift 0 lhs0) (.Var 0) = .Lam L ∧
          Term.msubstAt (d + 1) env
            (Term.applyB (Term.shift 0 lhs0) (.Var 0))
            = Term.lams (j + 1)
              (.App (Term.apps (.Ref k) (vs ++ opencols)) T)) := by
      rcases hstate with ⟨open0, hnl, hinst⟩ |
        ⟨L, T, j, open0, hlhsL, hinst⟩
      · left
        refine ⟨open0.map (Term.shift 0) ++ [.Var 0], ?_, ?_⟩
        · intro L he
          rw [Term.applyB_not_lam _ _ (Term.shift_not_lam lhs0 0 hnl)]
            at he
          exact Term.noConfusion he
        · rw [Term.applyB_not_lam _ _ (Term.shift_not_lam lhs0 0 hnl)]
          rw [Term.msubstAt_app]
          rw [Term.msubstAt_shift d env henvc lhs0]
          rw [hinst, Term.shift_apps]
          rw [show Term.shift 0 (.Ref k) = (.Ref k : Term) from
            _root_.rfl]
          rw [List.map_append]
          rw [map_closed_id vs hvsc _
            (fun t ht => Term.shift_closed t 0 0 ht (Nat.le_refl 0))]
          rw [Term.msubstAt_var_lt (d + 1) 0 (by omega)]
          rw [show vs ++ (open0.map (Term.shift 0) ++ [Term.Var 0])
            = (vs ++ open0.map (Term.shift 0)) ++ [Term.Var 0] from by
              simp [List.append_assoc]]
          exact (Term.apps_snoc _ _ _).symm
      · subst hlhsL
        have hlhs' : Term.applyB (Term.shift 0 (.Lam L)) (.Var 0) = L := by
          show Term.subst 0 (.Var 0) (Term.shift 1 L) = L
          exact Term.subst_var_shift L 0
        rw [Term.msubstAt_lam d env henvc] at hinst
        have hinner : Term.msubstAt (d + 1) env L
            = Term.lams j (.App (Term.apps (.Ref k) (vs ++ open0)) T) := by
          injection hinst
        cases j with
        | zero =>
          left
          refine ⟨open0 ++ [T], ?_, ?_⟩
          · intro L2 he
            rw [hlhs'] at he
            subst he
            rw [Term.msubstAt_lam (d + 1) env henvc] at hinner
            exact Term.noConfusion hinner
          · rw [hlhs', hinner]
            show Term.App _ _ = _
            rw [show vs ++ (open0 ++ [T]) = (vs ++ open0) ++ [T] from by
              simp [List.append_assoc]]
            exact (Term.apps_snoc _ _ _).symm
        | succ jq =>
          right
          have hlokL : Term.lhsOk L := hlok
          have hex : ∃ L2, L = .Lam L2 := by
            cases hLc : L with
            | Lam L2 => exact ⟨L2, _root_.rfl⟩
            | Var i =>
              rw [hLc] at hlokL
              exact hlokL.elim
            | Ref j2 =>
              rw [hLc, Term.msubstAt_ref] at hinner
              exact Term.noConfusion hinner
            | App f a =>
              rw [hLc, Term.msubstAt_app] at hinner
              exact Term.noConfusion hinner
            | _ =>
              rw [hLc] at hlokL
              exact hlokL.elim
          obtain ⟨L2, hL2⟩ := hex
          refine ⟨L2, T, jq, open0, by rw [hlhs']; exact hL2, ?_⟩
          rw [hlhs']
          exact hinner
    obtain ⟨Cs, Crs, hlenr, hcg, hslots, hbelow⟩ :=
      ih (A1 :: Γ) B1 ufr hbraw (d + 1)
        (by simp only [List.length_cons]; omega) hocc' hlok' hstate'
    refine ⟨Cs, Crs, hlenr, ?_, ?_, hbelow⟩
    · rw [Term.msubstAt_lam d env henvc, Term.msubstAt_lam d uenv huenv]
      exact .lam hcg
    · intro i hi
      obtain ⟨h1, h2⟩ := hslots i hi
      refine ⟨h1, ?_⟩
      intro h0
      refine h2 ?_
      simp only [Term.occ] at h0
      rw [show d + 1 + i = d + i + 1 from by omega]
      exact h0
  | @mat n0 a0 A0 c0 C0 lhs0 h0 m0 hn hk0 hc0 htreeh htreem ihh ihm =>
    intro Γ Braw ubraw hraw d hΓl hocc hlok hstate
    have henvc : ∀ w ∈ env, Term.Closed 0 w := henv
    obtain ⟨A0', C0', r0, ps0, telF, B0, G0, q'0, uhr, umr, hk0r, hc00r,
      hr0, hlen0, hlive0, hins0, hgoal0, hmhr, hmmr, hcvM, hueqr⟩ :=
      Era.mat_inv hβ hraw
    subst hueqr
    have hocch : ∀ i, i < uenv.length → Term.occ (d + i) uhr ≤ 1 := by
      intro i hi
      have h1 := hocc i hi
      simp only [Term.occ] at h1
      have hx : Term.occ (d + i) uhr
          ≤ Nat.max (Term.occ (d + i) uhr) (Term.occ (d + i) umr) :=
        Nat.le_max_left _ _
      omega
    have hoccm : ∀ i, i < uenv.length → Term.occ (d + i) umr ≤ 1 := by
      intro i hi
      have h1 := hocc i hi
      simp only [Term.occ] at h1
      have hx : Term.occ (d + i) umr
          ≤ Nat.max (Term.occ (d + i) uhr) (Term.occ (d + i) umr) :=
        Nat.le_max_right _ _
      omega
    have hlokh : Term.lhsOk (Term.lhsExt lhs0 a0 c0 C0.fn) :=
      Term.lhsOk.lhsExt hlok a0 c0 C0.fn
    have hstateh :
        (∃ opencols : List Term,
          (∀ L, Term.lhsExt lhs0 a0 c0 C0.fn ≠ .Lam L) ∧
          Term.msubstAt d env (Term.lhsExt lhs0 a0 c0 C0.fn)
            = Term.apps (.Ref k) (vs ++ opencols))
        ∨ (∃ (L T : Term) (j : Nat) (opencols : List Term),
          Term.lhsExt lhs0 a0 c0 C0.fn = .Lam L ∧
          Term.msubstAt d env (Term.lhsExt lhs0 a0 c0 C0.fn)
            = Term.lams (j + 1)
              (.App (Term.apps (.Ref k) (vs ++ opencols)) T)) := by
      rcases hstate with ⟨open0, hnl, hinst⟩ |
        ⟨L, T, j, open0, hlhsL, hinst⟩
      · have hinstx := drive_ext_inst d env henvc lhs0 a0 c0 C0.fn
          (Or.inr ⟨hnl, by
            rw [hinst]
            exact apps_ref_not_lam k (vs ++ open0)⟩)
        rw [hinst] at hinstx
        have hsh : Term.shiftN C0.fn
            (Term.apps (.Ref k) (vs ++ open0))
            = Term.apps (.Ref k)
                (vs ++ open0.map (Term.shiftN C0.fn)) := by
          rw [Term.shiftN_apps, Term.shiftN_ref, List.map_append]
          rw [map_closed_id vs hvsc _
            (fun t ht => Term.shiftN_closed ht C0.fn)]
        rw [hsh] at hinstx
        rw [Term.applyB_not_lam _ _
          (apps_ref_not_lam k (vs ++ open0.map (Term.shiftN C0.fn)))]
          at hinstx
        cases hfn : C0.fn with
        | zero =>
          left
          rw [hfn] at hinstx
          refine ⟨open0.map (Term.shiftN 0)
            ++ [Term.apps (.Ctr a0 c0) (Term.rvars 0)], ?_, ?_⟩
          · intro L2 he
            have hz : Term.lhsExt lhs0 a0 c0 0
                = .App lhs0 (Term.apps (.Ctr a0 c0) (Term.rvars 0)) :=
              Term.applyB_not_lam _ _ hnl
            rw [hz] at he
            exact Term.noConfusion he
          · rw [hinstx]
            show Term.App _ _ = _
            rw [show vs ++ (open0.map (Term.shiftN 0)
              ++ [Term.apps (.Ctr a0 c0) (Term.rvars 0)])
              = (vs ++ open0.map (Term.shiftN 0))
                ++ [Term.apps (.Ctr a0 c0) (Term.rvars 0)] from by
                simp [List.append_assoc]]
            exact (Term.apps_snoc _ _ _).symm
        | succ fnm =>
          right
          rw [hfn] at hinstx
          exact ⟨Term.lams fnm (Term.applyB
              (Term.shiftN (fnm + 1) lhs0)
              (Term.apps (.Ctr a0 c0) (Term.rvars (fnm + 1)))),
            Term.apps (.Ctr a0 c0) (Term.rvars (fnm + 1)), fnm,
            open0.map (Term.shiftN (fnm + 1)), _root_.rfl, hinstx⟩
      · subst hlhsL
        have hinstx := drive_ext_inst d env henvc (.Lam L) a0 c0 C0.fn
          (Or.inl ⟨L, _root_.rfl⟩)
        rw [hinst] at hinstx
        obtain ⟨o2, T2, hsh⟩ := susp_shape_shiftN k vs hvsc C0.fn (j + 1)
          open0 T
        rw [hsh] at hinstx
        have happB : Term.applyB (Term.lams (j + 1)
            (.App (Term.apps (.Ref k) (vs ++ o2)) T2))
            (Term.apps (.Ctr a0 c0) (Term.rvars C0.fn))
            = Term.lams j (Term.subst j
                (Term.shiftN j (Term.apps (.Ctr a0 c0) (Term.rvars C0.fn)))
                (.App (Term.apps (.Ref k) (vs ++ o2)) T2)) := by
          show Term.subst 0 _ (Term.lams j _) = _
          rw [Term.subst_lams_open j 0 _ _]
          rw [Nat.zero_add]
        rw [happB] at hinstx
        obtain ⟨o3, T3, hsub⟩ := susp_shape_subst k vs hvsc j
          (Term.shiftN j (Term.apps (.Ctr a0 c0) (Term.rvars C0.fn)))
          o2 T2
        rw [hsub] at hinstx
        rw [Term.lams_append] at hinstx
        cases hfj : C0.fn + j with
        | zero =>
          left
          rw [hfj] at hinstx
          refine ⟨o3 ++ [T3], ?_, ?_⟩
          · intro L2 he
            rw [he, Term.msubstAt_lam d env henvc] at hinstx
            exact Term.noConfusion hinstx
          · rw [hinstx]
            show Term.App _ _ = _
            rw [show vs ++ (o3 ++ [T3]) = (vs ++ o3) ++ [T3] from by
              simp [List.append_assoc]]
            exact (Term.apps_snoc _ _ _).symm
        | succ jj =>
          right
          rw [hfj] at hinstx
          have hex : ∃ L2, Term.lhsExt (.Lam L) a0 c0 C0.fn = .Lam L2 := by
            cases hLc : Term.lhsExt (.Lam L) a0 c0 C0.fn with
            | Lam L2 => exact ⟨L2, _root_.rfl⟩
            | Var i =>
              rw [hLc] at hlokh
              exact hlokh.elim
            | Ref j2 =>
              rw [hLc, Term.msubstAt_ref] at hinstx
              exact Term.noConfusion hinstx
            | App f a =>
              rw [hLc, Term.msubstAt_app] at hinstx
              exact Term.noConfusion hinstx
            | _ =>
              rw [hLc] at hlokh
              exact hlokh.elim
          obtain ⟨L2, hL2⟩ := hex
          exact ⟨L2, T3, jj, o3, hL2, hinstx⟩
    obtain ⟨Csh, Crsh, hlenh, hcgh, hsloth, hbelowh⟩ :=
      ihh Γ G0 uhr hmhr d hΓl hocch hlokh hstateh
    obtain ⟨Csm, Crsm, hlenm, hcgm, hslotm, hbelowm⟩ :=
      ihm Γ (.All q'0 (Term.apps (.Adt a0 (c0 :: r0)) ps0) B0) umr hmmr
        d hΓl hoccm hlok hstate
    obtain ⟨Crs, hlenr, hdom, hsubz⟩ := mat_slots Crsh Crsm Css
      (by omega) (by omega)
      (fun i hi => (hsloth i (by omega)).1)
      (fun i hi => (hslotm i (by omega)).1)
    refine ⟨Csh ++ Csm, Crs, by omega, ?_, ?_, ?_⟩
    · rw [Term.msubstAt_mat, Term.msubstAt_mat]
      refine CG.mat hcgh hcgm ?_ ?_
      · refine Sub.append (Sub.append_right _ _) ?_
        refine Sub.flatten (by omega) ?_
        intro i hi
        exact (hdom i (by omega)).1
      · refine Sub.append (Sub.append_left _ _) ?_
        refine Sub.flatten (by omega) ?_
        intro i hi
        exact (hdom i (by omega)).2
    · intro i hi
      obtain ⟨hs1, hs2⟩ := hsubz i (by omega)
      refine ⟨hs1, ?_⟩
      intro h0
      simp only [Term.occ] at h0
      have hzh : Term.occ (d + i) uhr = 0 := by
        have hx : Term.occ (d + i) uhr
            ≤ Nat.max (Term.occ (d + i) uhr) (Term.occ (d + i) umr) :=
          Nat.le_max_left _ _
        omega
      have hzm : Term.occ (d + i) umr = 0 := by
        have hx : Term.occ (d + i) umr
            ≤ Nat.max (Term.occ (d + i) uhr) (Term.occ (d + i) umr) :=
          Nat.le_max_right _ _
        omega
      exact hs2 ⟨(hsloth i hi).2 hzh, (hslotm i hi).2 hzm⟩
    · intro c1 hc1
      rcases List.mem_append.mp hc1 with h1 | h2
      · exact hbelowh c1 h1
      · exact hbelowm c1 h2

-- the drive's state: either between columns (the instantiated lhs is
-- a whole call spine, sizes matching the consumed arguments) or
-- mid-pattern (a lams-wrapped partial pattern with its size ledger)
def DriveSt (β : Book) (k : Nat) (lhs : Term) (env W queue : List Term)
    (jp : Nat) : Prop :=
  (∃ ws : List Term, (∀ L, lhs ≠ .Lam L) ∧
    Term.msubstAt 0 env lhs = Term.apps (.Ref k) ws ∧
    jp = 0 ∧ ws.length = W.length ∧
    (∀ j, j < W.length → (ws.getD j .Typ).Closed 0 ∧
      Term.csize β (ws.getD j .Typ) = Term.csize β (W.getD j .Typ)))
  ∨ (∃ (L : Term) (ws : List Term) (T : Term) (jpm : Nat),
    lhs = .Lam L ∧ jp = jpm + 1 ∧
    Term.msubstAt 0 env lhs
      = Term.lams (jpm + 1) (.App (Term.apps (.Ref k) ws) T) ∧
    (∀ w' ∈ ws, w'.Closed 0) ∧
    PPat β 0 (jpm + 1) T ∧
    ws.length + 1 = W.length ∧
    (∀ j, j < ws.length → (ws.getD j .Typ).Closed 0 ∧
      Term.csize β (ws.getD j .Typ) = Term.csize β (W.getD j .Typ)) ∧
    Term.csize β T
      + ((queue.take (jpm + 1)).map (Term.csize β)).sum
      = Term.csize β (W.getD ws.length .Typ))

theorem take_append_more : ∀ (xs rest : List α) (j : Nat),
    (xs ++ rest).take (xs.length + j) = xs ++ rest.take j := by
  intro xs
  induction xs with
  | nil =>
    intro rest j
    simp only [List.length_nil, Nat.zero_add, List.nil_append]
  | cons x xs ih =>
    intro rest j
    simp only [List.length_cons, List.cons_append]
    rw [show xs.length + 1 + j = (xs.length + j) + 1 from by omega]
    show x :: (xs ++ rest).take (xs.length + j) = _
    rw [ih rest j]

theorem drop_append_more : ∀ (xs rest : List α) (j : Nat),
    (xs ++ rest).drop (xs.length + j) = rest.drop j := by
  intro xs
  induction xs with
  | nil =>
    intro rest j
    simp only [List.length_nil, Nat.zero_add, List.nil_append]
  | cons x xs ih =>
    intro rest j
    simp only [List.length_cons, List.cons_append]
    rw [show xs.length + 1 + j = (xs.length + j) + 1 from by omega]
    show (xs ++ rest).drop (xs.length + j) = _
    exact ih rest j

-- peeling the next queue value into a fresh constructor pattern: the
-- state opens the pattern's field holes
theorem DriveSt.peel (β : Book) (k : Nat) (lhs : Term)
    (env W : List Term) (w : Term) (rest : List Term) (jp : Nat)
    (henv : ∀ x ∈ env, x.Closed 0)
    (hw : Term.Value β w ∧ w.Closed 0)
    (hlok : Term.lhsOk lhs)
    {a c : Nat} {A : AdtD} {C : CtrD} (hk : Book.adt β a = some A)
    (hc : AdtD.ctr A c = some C)
    (pps xs : List Term) (hweq : w = Term.apps (.Ctr a c) (pps ++ xs))
    (hlp : pps.length = A.pn) (hlx : xs.length = C.fn)
    (hst : DriveSt β k lhs env W (w :: rest) jp) :
    ∃ (W' : List Term) (jp' : Nat),
      ((jp = 0 ∧ jp' = C.fn ∧ W' = W ++ [w]) ∨
       (0 < jp ∧ jp' = jp - 1 + C.fn ∧ W' = W)) ∧
      W' ++ (xs ++ rest).drop jp' = W ++ (w :: rest).drop jp ∧
      DriveSt β k (Term.lhsExt lhs a c C.fn) env W' (xs ++ rest) jp' := by
  have henvc : ∀ x ∈ env, x.Closed 0 := henv
  have hxsc : ∀ x ∈ xs, x.Closed 0 := by
    intro x hx
    have h1 := hw.2
    rw [hweq, Term.closed_apps] at h1
    exact h1.2 x (List.mem_append.mpr (Or.inr hx))
  have hcw : Term.csize β w
      = 1 + (xs.map (Term.csize β)).sum := by
    rw [hweq]
    rw [Term.csize_ctr hk hc _ (by
      simp only [List.length_append]
      omega)]
    congr 2
    rw [show A.pn = pps.length from hlp.symm]
    rw [List.drop_left]
  have hlokx : Term.lhsOk (Term.lhsExt lhs a c C.fn) :=
    Term.lhsOk.lhsExt hlok a c C.fn
  rcases hst with
    ⟨ws, hnl, hinst, hjp0, hlenw, hfacts⟩ |
    ⟨L, ws, T, jpm, hlhsL, hjpe, hinst, hwsc, hppat, hlenw, hfacts, hledger⟩
  · -- between columns: open the pattern as the next column
    subst hjp0
    have hI0c : (Term.apps (.Ref k) ws).Closed 0 := by
      rw [Term.closed_apps]
      refine ⟨trivial, ?_⟩
      intro x hx
      have := mem_take_getD .Typ ws ws.length x (by
        rw [List.take_length]
        exact hx)
      obtain ⟨j, hj1, hj2, hj3⟩ := this
      rw [← hj3]
      exact (hfacts j (by omega)).1
    have hinst' : Term.msubstAt 0 env (Term.lhsExt lhs a c C.fn)
        = Term.lams C.fn (.App (Term.apps (.Ref k) ws)
            (Term.apps (.Ctr a c) (Term.rvars C.fn))) := by
      rw [drive_ext_inst 0 env henvc lhs a c C.fn
        (Or.inr ⟨hnl, by
          rw [hinst]
          exact apps_ref_not_lam k ws⟩)]
      rw [hinst]
      rw [Term.shiftN_closed hI0c C.fn]
      rw [Term.applyB_not_lam _ _ (apps_ref_not_lam k ws)]
    refine ⟨W ++ [w], C.fn, Or.inl ⟨_root_.rfl, _root_.rfl, _root_.rfl⟩,
      ?_, ?_⟩
    · rw [show C.fn = xs.length + 0 from by omega, drop_append_more,
        List.drop_zero, List.drop_zero]
      simp [List.append_assoc]
    · cases hfn : C.fn with
      | zero =>
        left
        rw [hfn] at hinst'
        have hxse : xs = [] := by
          cases xs with
          | nil => rfl
          | cons _ _ =>
            exfalso
            rw [hfn] at hlx
            simp at hlx
        subst hxse
        have hlhs0 : Term.lhsExt lhs a c 0
            = .App lhs (Term.apps (.Ctr a c) (Term.rvars 0)) :=
          Term.applyB_not_lam _ _ hnl
        refine ⟨ws ++ [Term.apps (.Ctr a c) (Term.rvars 0)], ?_,
          ?_, _root_.rfl, by
            simp only [List.length_append, List.length_cons,
              List.length_nil]
            omega, ?_⟩
        · intro L he
          rw [hlhs0] at he
          exact Term.noConfusion he
        · rw [hinst']
          show Term.App _ _ = _
          exact (Term.apps_snoc _ _ _).symm
        · intro j hj
          simp only [List.length_append, List.length_cons,
            List.length_nil] at hj
          by_cases hje : j < W.length
          · have e1 : (ws ++ [Term.apps (.Ctr a c) (Term.rvars 0)]).getD
                j .Typ = ws.getD j .Typ :=
              getD_append_left ws _ j (by omega)
            have e2 : (W ++ [w]).getD j .Typ = W.getD j .Typ :=
              getD_append_left W [w] j hje
            rw [e1, e2]
            exact hfacts j hje
          · have hj2 : j = W.length := by omega
            subst hj2
            have e1 : (ws ++ [Term.apps (.Ctr a c) (Term.rvars 0)]).getD
                W.length .Typ = Term.apps (.Ctr a c) (Term.rvars 0) := by
              rw [show W.length = ws.length from hlenw.symm]
              exact getD_last ws _
            have e2 : (W ++ [w]).getD W.length .Typ = w := getD_last W w
            rw [e1, e2]
            constructor
            · show (Term.Ctr a c).Closed 0
              trivial
            · show Term.csize β (Term.Ctr a c) = _
              have h1 : Term.csize β (Term.apps (.Ctr a c) ([] : List Term))
                  = 1 + (([] : List Term).map (Term.csize β)).sum :=
                Term.csize_fields hk hc [] (by rw [hfn]; rfl)
              rw [hcw]
              exact h1
      | succ fnm =>
        right
        rw [hfn] at hinst'
        have hppat0 : PPat β 0 (fnm + 1)
            (Term.apps (.Ctr a c) (Term.rvars (fnm + 1))) := by
          have h := peel_pattern_ppat β hk hc 0
          rw [hfn] at h
          rw [Nat.zero_add] at h
          exact h
        have hcsz0 : Term.csize β
            (Term.apps (.Ctr a c) (Term.rvars (fnm + 1))) = 1 := by
          have h := peel_pattern_csize β hk hc 0
          rw [hfn] at h
          exact h
        refine ⟨Term.lams fnm (Term.applyB
            (Term.shiftN (fnm + 1) lhs)
            (Term.apps (.Ctr a c) (Term.rvars (fnm + 1)))), ws,
          Term.apps (.Ctr a c) (Term.rvars (fnm + 1)), fnm,
          _root_.rfl, _root_.rfl, hinst', ?_, hppat0, by
            simp only [List.length_append, List.length_cons,
              List.length_nil]
            omega, ?_, ?_⟩
        · intro w' hw'
          have := mem_take_getD .Typ ws ws.length w' (by
            rw [List.take_length]
            exact hw')
          obtain ⟨j, hj1, hj2, hj3⟩ := this
          rw [← hj3]
          exact (hfacts j (by omega)).1
        · intro j hj
          have e2 : (W ++ [w]).getD j .Typ = W.getD j .Typ :=
            getD_append_left W [w] j (by omega)
          rw [e2]
          exact hfacts j (by omega)
        · have e2 : (W ++ [w]).getD ws.length .Typ = w := by
            rw [show ws.length = W.length from hlenw]
            exact getD_last W w
          rw [e2, hcsz0]
          have e3 : (xs ++ rest).take (fnm + 1) = xs := by
            rw [show fnm + 1 = xs.length from by omega]
            exact take_append xs rest
          rw [e3]
          omega
  · -- mid-pattern: a nested peel fills the hole with a fresh pattern
    subst hjpe
    subst hlhsL
    have hI0c : (Term.apps (.Ref k) ws).Closed 0 := by
      rw [Term.closed_apps]
      exact ⟨trivial, hwsc⟩
    have hTc : T.Closed (jpm + 1) := hppat.closed_out
    have hinst' : Term.msubstAt 0 env (Term.lhsExt (.Lam L) a c C.fn)
        = Term.lams (C.fn + jpm) (.App (Term.apps (.Ref k) ws)
            (Term.subst jpm (Term.shiftN jpm
              (Term.apps (.Ctr a c) (Term.rvars C.fn))) T)) := by
      rw [drive_ext_inst 0 env henvc (.Lam L) a c C.fn
        (Or.inl ⟨L, _root_.rfl⟩)]
      rw [hinst]
      exact drive_peel_step _ T _ jpm C.fn hI0c hTc
    have hfill : PPat β 0 (jpm + C.fn)
        (Term.subst jpm (Term.shiftN jpm
          (Term.apps (.Ctr a c) (Term.rvars C.fn))) T) := by
      have h := PPat.fill β (Term.size T) T (Nat.le_refl _) hppat
        (by omega) (m := C.fn) (u := Term.shiftN jpm
          (Term.apps (.Ctr a c) (Term.rvars C.fn)))
        (by
          have h2 := peel_pattern_ppat β hk hc jpm
          simpa using h2)
      simpa using h
    have hcsz : Term.csize β (Term.subst jpm (Term.shiftN jpm
        (Term.apps (.Ctr a c) (Term.rvars C.fn))) T)
        = Term.csize β T + 1 := by
      have h := PPat.csize_fill β (Term.size T) T (Nat.le_refl _) hppat
        (by omega) (Term.shiftN jpm (Term.apps (.Ctr a c)
          (Term.rvars C.fn)))
      rw [peel_pattern_csize β hk hc jpm] at h
      simpa using h
    refine ⟨W, jpm + C.fn, Or.inr ⟨by omega, by omega, _root_.rfl⟩,
      ?_, ?_⟩
    · rw [show jpm + C.fn = xs.length + jpm from by omega,
        drop_append_more]
      rfl
    · cases hfj : jpm + C.fn with
      | zero =>
        left
        have hfn0 : C.fn = 0 := by omega
        have hjm0 : jpm = 0 := by omega
        subst hjm0
        have hxse : xs = [] := by
          cases xs with
          | nil => rfl
          | cons _ _ =>
            exfalso
            rw [hfn0] at hlx
            simp at hlx
        subst hxse
        have hinst2 : Term.msubstAt 0 env (Term.lhsExt (.Lam L) a c C.fn)
            = .App (Term.apps (.Ref k) ws)
                (Term.subst 0 (Term.shiftN 0
                  (Term.apps (.Ctr a c) (Term.rvars C.fn))) T) := by
          rw [hinst']
          rw [show C.fn + 0 = 0 from by omega]
          rfl
        refine ⟨ws ++ [Term.subst 0 (Term.shiftN 0
            (Term.apps (.Ctr a c) (Term.rvars C.fn))) T], ?_, ?_,
          _root_.rfl, by
            simp only [List.length_append, List.length_cons,
              List.length_nil]
            omega, ?_⟩
        · intro L2 he
          rw [he, Term.msubstAt_lam 0 env henvc] at hinst2
          exact Term.noConfusion hinst2
        · rw [hinst2]
          show Term.App _ _ = _
          exact (Term.apps_snoc _ _ _).symm
        · intro j hj
          by_cases hje : j < ws.length
          · have e1 := getD_append_left (d0 := Term.Typ) ws
              [Term.subst 0 (Term.shiftN 0
                (Term.apps (.Ctr a c) (Term.rvars C.fn))) T] j hje
            rw [e1]
            exact hfacts j hje
          · have hj2 : j = ws.length := by omega
            subst hj2
            have e1 := getD_last (d0 := Term.Typ) ws
              (Term.subst 0 (Term.shiftN 0
                (Term.apps (.Ctr a c) (Term.rvars C.fn))) T)
            rw [e1]
            have hfill0 : PPat β 0 0 (Term.subst 0 (Term.shiftN 0
                (Term.apps (.Ctr a c) (Term.rvars C.fn))) T) := by
              have h := hfill
              rw [hfn0] at h ⊢
              exact h
            refine ⟨PPat.closed_zero β (Term.size _) _ (Nat.le_refl _)
              hfill0, ?_⟩
            have hl2 := hledger
            have hsum1 : (((w :: rest).take (0 + 1)).map
                (Term.csize β)).sum = Term.csize β w := by
              show Term.csize β w + (([] : List Term).map
                (Term.csize β)).sum = _
              simp
            rw [hsum1] at hl2
            have hcw1 : Term.csize β w = 1 := by
              rw [hcw]
              rfl
            omega
      | succ jj =>
        right
        have hinst2 := hinst'
        rw [show C.fn + jpm = jj + 1 from by omega] at hinst2
        have hex : ∃ L2, Term.lhsExt (.Lam L) a c C.fn = .Lam L2 := by
          cases hLc : Term.lhsExt (.Lam L) a c C.fn with
          | Lam L2 => exact ⟨L2, _root_.rfl⟩
          | Var i =>
            rw [hLc] at hlokx
            exact hlokx.elim
          | Ref j2 =>
            rw [hLc, Term.msubstAt_ref] at hinst2
            exact Term.noConfusion hinst2
          | App f a2 =>
            rw [hLc, Term.msubstAt_app] at hinst2
            exact Term.noConfusion hinst2
          | _ =>
            rw [hLc] at hlokx
            exact hlokx.elim
        obtain ⟨L2, hL2⟩ := hex
        refine ⟨L2, ws, Term.subst jpm (Term.shiftN jpm
            (Term.apps (.Ctr a c) (Term.rvars C.fn))) T, jj,
          hL2, _root_.rfl, hinst2, hwsc, ?_, hlenw, hfacts, ?_⟩
        · have h := hfill
          rw [show jpm + C.fn = jj + 1 from by omega] at h
          exact h
        · have e3 : (xs ++ rest).take (jj + 1)
              = xs ++ rest.take jpm := by
            rw [show jj + 1 = xs.length + jpm from by omega]
            exact take_append_more xs rest jpm
          rw [e3, hcsz]
          rw [List.map_append, List.sum_append]
          have hl2 := hledger
          have hsum1 : (((w :: rest).take (jpm + 1)).map
              (Term.csize β)).sum = Term.csize β w
                + ((rest.take jpm).map (Term.csize β)).sum := _root_.rfl
          rw [hsum1] at hl2
          omega
-- consuming one queue value through a binder: the state advances
theorem DriveSt.step (β : Book) (k : Nat) (lhs : Term)
    (env W : List Term) (v : Term) (rest : List Term) (jp : Nat)
    (henv : ∀ w ∈ env, w.Closed 0)
    (hv : v.Closed 0)
    (hlok : Term.lhsOk lhs)
    (hst : DriveSt β k lhs env W (v :: rest) jp) :
    ∃ (W' : List Term) (jp' : Nat),
      ((jp = 0 ∧ jp' = 0 ∧ W' = W ++ [v]) ∨
       (0 < jp ∧ jp' = jp - 1 ∧ W' = W)) ∧
      W' ++ rest.drop jp' = W ++ (v :: rest).drop jp ∧
      DriveSt β k (Term.applyB (Term.shift 0 lhs) (.Var 0)) (v :: env)
        W' rest jp' := by
  rcases hst with
    ⟨ws, hnl, hinst, hjp0, hlenw, hfacts⟩ |
    ⟨L, ws, T, jpm, hlhsL, hjpe, hinst, hwsc, hppat, hlenw, hfacts, hledger⟩
  · -- between columns: the value becomes the next column
    subst hjp0
    refine ⟨W ++ [v], 0, Or.inl ⟨_root_.rfl, _root_.rfl, _root_.rfl⟩, ?_, ?_⟩
    · rw [List.drop_zero, List.drop_zero]
      simp [List.append_assoc]
    · left
      have hinst' : Term.msubstAt 0 (v :: env)
          (Term.applyB (Term.shift 0 lhs) (.Var 0))
          = Term.apps (.Ref k) (ws ++ [v]) := by
        rw [Term.msubstAt_applyB v hv env henv lhs
          (Or.inr ⟨hnl, by
            rw [hinst]
            exact apps_ref_not_lam k ws⟩)]
        rw [hinst]
        rw [Term.applyB_not_lam _ _ (apps_ref_not_lam k ws)]
        exact (Term.apps_snoc _ _ _).symm
      refine ⟨ws ++ [v], ?_, hinst', _root_.rfl, by simp [hlenw], ?_⟩
      · intro L he
        rw [Term.applyB_not_lam _ _ (Term.shift_not_lam lhs 0 hnl)] at he
        exact Term.noConfusion he
      · intro j hj
        simp only [List.length_append, List.length_cons,
          List.length_nil] at hj
        by_cases hje : j < W.length
        · have e1 : (ws ++ [v]).getD j .Typ = ws.getD j .Typ :=
            getD_append_left ws [v] j (by omega)
          have e2 : (W ++ [v]).getD j .Typ = W.getD j .Typ :=
            getD_append_left W [v] j hje
          rw [e1, e2]
          exact hfacts j hje
        · have hj2 : j = W.length := by omega
          subst hj2
          have e1 : (ws ++ [v]).getD W.length .Typ = v := by
            rw [show W.length = ws.length from hlenw.symm]
            exact getD_last ws v
          have e2 : (W ++ [v]).getD W.length .Typ = v := getD_last W v
          rw [e1, e2]
          exact ⟨hv, _root_.rfl⟩
  · -- mid-pattern: the value fills the highest hole
    subst hjpe
    subst hlhsL
    have hlhs' : Term.applyB (Term.shift 0 (.Lam L)) (.Var 0) = L := by
      show Term.subst 0 (.Var 0) (Term.shift 1 L) = L
      exact Term.subst_var_shift L 0
    have hI0c : (Term.apps (.Ref k) ws).Closed 0 := by
      rw [Term.closed_apps]
      exact ⟨trivial, hwsc⟩
    have hinst' : Term.msubstAt 0 (v :: env)
        (Term.applyB (Term.shift 0 (.Lam L)) (.Var 0))
        = Term.lams jpm (.App (Term.apps (.Ref k) ws)
            (Term.subst jpm v T)) := by
      rw [Term.msubstAt_applyB v hv env henv
        (.Lam L) (Or.inl ⟨L, _root_.rfl⟩)]
      rw [hinst]
      exact drive_lam_step _ T v jpm hI0c hv
    have hfill : PPat β 0 (jpm + 0) (Term.subst jpm v T) := by
      have h := PPat.fill β (Term.size T) T (Nat.le_refl _) hppat
        (by omega) (m := 0) (u := v) (PPat.val hv)
      simpa using h
    have hcsz : Term.csize β (Term.subst jpm v T)
        = Term.csize β T + Term.csize β v := by
      have h := PPat.csize_fill β (Term.size T) T (Nat.le_refl _) hppat
        (by omega) v
      simpa using h
    have hlsum : (((v :: rest).take (jpm + 1)).map (Term.csize β)).sum
        = Term.csize β v + ((rest.take jpm).map (Term.csize β)).sum := by
      rfl
    cases jpm with
    | zero =>
      refine ⟨W, 0, Or.inr ⟨by omega, _root_.rfl, _root_.rfl⟩, ?_, ?_⟩
      · rw [List.drop_zero]
        rfl
      · left
        rw [hlhs'] at hinst' ⊢
        have hLnl : ∀ L2, L ≠ .Lam L2 := by
          intro L2 he
          subst he
          rw [Term.msubstAt_lam 0 (v :: env) (by
            intro w hw
            rcases List.mem_cons.mp hw with h1 | h2
            · subst h1
              exact hv
            · exact henv w h2)] at hinst'
          exact Term.noConfusion hinst'
        refine ⟨ws ++ [Term.subst 0 v T], hLnl, ?_, _root_.rfl,
          by simp only [List.length_append, List.length_cons,
            List.length_nil]; omega, ?_⟩
        · rw [hinst']
          show Term.App _ _ = _
          exact (Term.apps_snoc _ _ _).symm
        · intro j hj
          by_cases hje : j < ws.length
          · have e1 : (ws ++ [Term.subst 0 v T]).getD j .Typ
                = ws.getD j .Typ := getD_append_left _ _ j hje
            rw [e1]
            exact hfacts j hje
          · have hj2 : j = ws.length := by omega
            subst hj2
            have e1 : (ws ++ [Term.subst 0 v T]).getD ws.length .Typ
                = Term.subst 0 v T := getD_last _ _
            rw [e1]
            refine ⟨PPat.closed_zero β (Term.size _) _ (Nat.le_refl _)
              (by simpa using hfill), ?_⟩
            have hl2 := hledger
            rw [hlsum] at hl2
            have hz : ((rest.take 0).map (Term.csize β)).sum = 0 := _root_.rfl
            omega
    | succ jq =>
      refine ⟨W, jq + 1, Or.inr ⟨by omega, _root_.rfl, _root_.rfl⟩, ?_, ?_⟩
      · rfl
      · right
        rw [hlhs'] at hinst' ⊢
        have hlokL : Term.lhsOk L := hlok
        have hex : ∃ L2, L = .Lam L2 := by
          cases hLc : L with
          | Lam L2 => exact ⟨L2, _root_.rfl⟩
          | Var i =>
            rw [hLc] at hlokL
            exact hlokL.elim
          | Ref j =>
            rw [hLc, Term.msubstAt_ref] at hinst'
            exact Term.noConfusion hinst'
          | App f a =>
            rw [hLc, Term.msubstAt_app] at hinst'
            exact Term.noConfusion hinst'
          | _ =>
            rw [hLc] at hlokL
            exact hlokL.elim
        obtain ⟨L2, hL2⟩ := hex
        refine ⟨L2, ws, Term.subst (jq + 1) v T, jq, hL2, _root_.rfl,
          ?_, hwsc, (by simpa using hfill), hlenw, hfacts, ?_⟩
        · exact hinst'
        · have hl2 := hledger
          rw [hlsum] at hl2
          omega

theorem Tree.drive (hβ : Book.Closed β) (hok : Book.Ok β)
    {k : Nat} {dk : DefD} (hd : Book.defn β k = some dk)
    (args0 : List Term) (sp : List (Option Nat))
    (hspl : sp.length = dk.n + 1)
    (hspc0 : ∀ j, j < dk.n → sp.getD j none = none
      ∨ (j < args0.length ∧ sp.getD j none
          = some (Term.csize β (args0.getD j .Typ))))
    (hsp_slack : ∃ ss, sp.getD dk.n none = some ss
      ∧ dk.n - min args0.length dk.n ≤ ss)
    (hspmask : ∀ j, j < dk.n → dk.qs.getD j .Lone = .None →
      sp.getD j none = none)
    (ph0 : Bool) :
    ∀ {lhs : Term} {n : Nat} {node : Term}, Tree β k dk.qs lhs n node →
    ∀ (Γ : Ctx) (Braw ubraw : Term), Era β Γ node Braw ubraw →
    ∀ (env uenv W queue : List Term) (Css Cssq : List (List Charge))
      (TN Tf' : Term) (uN : Term) (uq : List Term) (jp : Nat),
    Γ.length = env.length →
    env.length = uenv.length →
    Css.length = uenv.length →
    (∀ v ∈ env, v.Closed 0) →
    (∀ v ∈ uenv, v.Closed 0) →
    (∀ p ∈ (Css.zip env).zip uenv, CG β p.1.1 p.1.2 p.2) →
    (∀ p ∈ env.zip uenv, p.2 = .Typ ∨ DeepP β p.1 p.2) →
    (∀ i, i < uenv.length → Term.occ i ubraw ≤ 1) →
    Era β [] (Term.msubstAt 0 env node) TN uN →
    uN = Term.msubstAt 0 uenv ubraw →
    (∀ p ∈ queue.zip uq, p.1.Closed 0 ∧ (p.2 = .Typ ∨ DeepP β p.1 p.2)) →
    EraSpine β [] TN queue Tf' uq →
    Cssq.length = queue.length →
    (∀ p ∈ (Cssq.zip queue).zip uq, CG β p.1.1 p.1.2 p.2) →
    jp ≤ queue.length →
    W ++ queue.drop jp = args0 →
    n + W.length = dk.n + jp →
    Term.lhsOk lhs →
    DriveSt β k lhs env W queue jp →
    ∃ (t_r u_r : Term) (C_r Cs : List Charge),
      Red β .weak (Term.apps (Term.msubstAt 0 env node) queue) t_r ∧
      (∃ Tr, Era β [] t_r Tr u_r ∧ Conv β Tr Tf') ∧
      CG β C_r t_r u_r ∧
      Sub C_r (Cs ++ (Css.flatten ++ Cssq.flatten)) ∧
      (∀ c ∈ Cs, CLt c (k, sp, ph0)) := by
  intro lhs n node htree
  induction htree with
  | @bod cols0 t0 n0 hguard =>
    intro Γ Braw ubraw hraw env uenv W queue Css Cssq TN Tf' uN uq jp
      hΓl hl1 hl2 henv huenv hpair henvP hocc hera hconn hqv hsp hlq hpairq
      hjp horig harity hlok hstate
    rcases hstate with
      ⟨ws, hnl, hinst, hjp0, hlenw, hfacts⟩ |
      ⟨L, ws, T, jpm, hlhsL, _, _, _, _, _, _, _⟩
    · -- the leaf: price it and frame the leftover queue
      subst hjp0
      rw [Term.msubstAt_apps, Term.msubstAt_ref] at hinst
      obtain ⟨hheq, hargs⟩ := Term.apps_head_inv (h := Term.Ref k)
        (h' := Term.Ref k) (by trivial) (by trivial) hinst
      have hlencw : cols0.length = W.length := by
        rw [← hlenw, ← hargs]
        simp
      have hmemws : ∀ v ∈ ws, ∃ j, j < ws.length ∧ ws.getD j .Typ = v := by
        intro v hv
        have := mem_take_getD .Typ ws ws.length v (by
          rw [List.take_length]
          exact hv)
        obtain ⟨j, hj1, hj2, hj3⟩ := this
        exact ⟨j, hj1, hj3⟩
      obtain ⟨Cs, Crs, hlenr, hcg, hslots, hbelow⟩ :=
        Guard.era_cg hβ hok hd ws
          (by
            intro v hv
            obtain ⟨j, hj1, hj2⟩ := hmemws v hv
            rw [← hj2]
            exact (hfacts j (by omega)).1)
          sp hspl
          (by
            intro j hj
            rw [hlenw] at hj
            rcases hspc0 j (by omega) with h2 | ⟨h3, h4⟩
            · exact Or.inl h2
            · right
              rw [h4]
              congr 1
              have hW : args0.getD j .Typ = W.getD j .Typ := by
                rw [← horig, List.drop_zero]
                exact getD_append_left W queue j (by omega)
              rw [hW]
              exact ((hfacts j (by omega)).2).symm)
          (by
            intro j hj hq
            exact hspmask j hj hq)
          ph0 hguard hraw 0 env uenv Css
          (by omega) hl1 hl2 henv huenv hpair henvP
          (by
            intro i hi
            have := hocc i hi
            rw [Nat.zero_add]
            exact this)
          hargs
          (by omega)
      refine ⟨Term.apps (Term.msubstAt 0 env t0) queue,
        Term.apps uN uq, (Cs ++ Crs.flatten) ++ Cssq.flatten, Cs,
        .refl, ⟨Tf', hsp.era hera, Conv.refl _⟩, ?_, ?_, hbelow⟩
      · rw [hconn]
        exact CG.frames hsp hlq hpairq hcg
      · have h1 : Sub Crs.flatten Css.flatten :=
          Sub.flatten (by omega) (fun i hi => (hslots i (by omega)).1)
        exact Sub.perm_right
          (Sub.append (Sub.append (Sub.refl Cs) h1) (Sub.refl _))
          (by simp [List.append_assoc])
    · -- bod's lhs is an application spine, never a lambda
      exfalso
      rcases apps_shape cols0 (.Ref k) _ _root_.rfl.symm with
        ⟨h1, h2⟩ | ⟨as0, al, h1, h2⟩
      · rw [hlhsL] at h2
        exact Term.noConfusion h2
      · rw [hlhsL] at h2
        exact Term.noConfusion h2
  | @lam n0 lhs0 f0 hn htree0 ih =>
    intro Γ Braw ubraw hraw env uenv W queue Css Cssq TN Tf' uN uq jp
      hΓl hl1 hl2 henv huenv hpair henvP hocc hera hconn hqv hsp hlq hpairq
      hjp horig harity hlok hstate
    obtain ⟨q1, A1, B1, ufr, hcvL, hbraw, hoccf, hueqr⟩ := Era.lam_inv hβ hraw
    subst hueqr
    rw [Term.msubstAt_lam 0 uenv huenv] at hconn
    have henvc : ∀ w ∈ env, Term.Closed 0 w := henv
    have hinstf : Term.msubstAt 0 env (.Lam f0)
        = .Lam (Term.msubstAt 1 env f0) := Term.msubstAt_lam 0 env henvc f0
    cases queue with
    | nil =>
      -- underapplied: the suspended value prices below the spent charge
      cases hsp
      have hjp0 : jp = 0 := by
        simp only [List.length_nil] at hjp
        omega
      subst hjp0
      have hW : W = args0 := by
        rw [← horig]
        simp
      rcases hstate with ⟨ws, hnl, hinst, _, hlenw, hfacts⟩ |
        ⟨L, ws, T, jpm, _, hjpe, _⟩
      · have hwlt : ws.length < dk.n := by omega
        have hwsc : ∀ v ∈ ws, v.Closed 0 := by
          intro v hv
          obtain ⟨j, hj1, hj2, hj3⟩ := mem_take_getD .Typ ws ws.length v
            (by
              rw [List.take_length]
              exact hv)
          rw [← hj3]
          exact (hfacts j (by omega)).1
        obtain ⟨Cs, Crs, hlenr, hcg, hslots, hbelow⟩ :=
          Tree.suspend hβ hok hd ws hwsc hwlt sp hspl
            (by
              intro j hj
              rcases hspc0 j (by omega) with h2 | ⟨h3, h4⟩
              · exact Or.inl h2
              · right
                rw [h4]
                congr 1
                rw [← hW]
                exact ((hfacts j (by omega)).2).symm
            )
            (by
              intro j hj1 hj2
              rcases hspc0 j (by omega) with h2 | ⟨h3, h4⟩
              · exact h2
              · exfalso
                rw [← hW] at h3
                omega)
            (by
              obtain ⟨ss, hs1, hs2⟩ := hsp_slack
              refine ⟨ss, hs1, ?_⟩
              rw [hW] at hlenw
              omega)
            (by
              intro j hj hq
              exact hspmask j hj hq)
            ph0 env uenv Css hl1 hl2 henv huenv hpair henvP
            (Tree.lam hn htree0) Γ Braw (.Lam ufr) hraw 0
            (by omega)
            (by
              intro i hi
              rw [Nat.zero_add]
              exact hocc i hi)
            hlok
            (Or.inl ⟨[], hnl, by
              rw [hinst]
              simp⟩)
        refine ⟨Term.msubstAt 0 env (.Lam f0), uN, Cs ++ Crs.flatten, Cs,
          .refl, ⟨TN, hera, Conv.refl _⟩, ?_, ?_, hbelow⟩
        · rw [show uN = Term.msubstAt 0 uenv (.Lam ufr) from by
            rw [Term.msubstAt_lam 0 uenv huenv]
            exact hconn]
          exact hcg
        · cases Cssq with
          | cons _ _ => exact absurd hlq (by simp)
          | nil =>
            refine Sub.perm_right (Sub.append (Sub.refl Cs)
              (Sub.flatten (by omega)
                (fun i hi => (hslots i (by omega)).1))) ?_
            simp
      · omega
    | cons v rest =>
      obtain ⟨u0, uqrest0, huqeq⟩ : ∃ u0 uqrest0, uq = u0 :: uqrest0 := by
        cases hsp with
        | live _ _ _ => exact ⟨_, _, _root_.rfl⟩
        | dead _ _ _ => exact ⟨_, _, _root_.rfl⟩
      subst huqeq
      have hp0 : v.Closed 0 ∧ (u0 = .Typ ∨ DeepP β v u0) := hqv (v, u0) (by
        simp only [List.zip_cons_cons]
        exact List.mem_cons_self)
      have hvcl : v.Closed 0 := hp0.1
      have hrestv : ∀ p ∈ rest.zip uqrest0,
          p.1.Closed 0 ∧ (p.2 = .Typ ∨ DeepP β p.1 p.2) :=
        fun p hp => hqv p (by
          simp only [List.zip_cons_cons]
          exact List.mem_cons_of_mem _ hp)
      obtain ⟨W', jp', hcase, horig', hst'⟩ := DriveSt.step β k lhs0 env W
        v rest jp henv hvcl hlok hstate
      have hlok' : Term.lhsOk (Term.applyB (Term.shift 0 lhs0) (.Var 0)) :=
        Term.lhsOk.applyB (Term.lhsOk.shift lhs0 hlok 0) _
      cases Cssq with
      | nil => exact absurd hlq (by simp)
      | cons Cq0 Cssq' =>
        simp only [List.length_cons] at hlq
        cases hsp with
        | @live _ A B _ uvarm _ _ uqrest hc0 hva hrest =>
          obtain ⟨q2, A2, B2, ubody, hcv2, hbody, hocc2, hueq2⟩ :=
            Era.lam_inv hβ (Era.cnv (hinstf ▸ hera) hc0)
          rw [hconn] at hueq2
          injection hueq2 with hub
          obtain ⟨hq2, hcA2, hcB2⟩ := Conv.all_inj hcv2
          subst hq2
          obtain ⟨πv0, hvchk0⟩ := hva.check_none
          have hsub := hbody.sub hβ Cut.zero
            (Check.cnv hvchk0 (Conv.symm hcA2)) (by intro hc; cases hc)
            (Era.cnv hva (Conv.symm hcA2)) hvcl
            hva.closed_out
          rw [← hub] at hsub
          rw [show Term.subst 0 v (Term.msubstAt 1 env f0)
            = Term.msubstAt 0 (v :: env) f0 from
              (Term.msubstAt_cons 0 v hvcl env henvc f0).symm] at hsub
          rw [show Term.subst 0 u0 (Term.msubstAt 1 uenv ufr)
            = Term.msubstAt 0 (u0 :: uenv) ufr from
              (Term.msubstAt_cons 0 u0 hva.closed_out uenv huenv
                ufr).symm] at hsub
          obtain ⟨T'', hrest', hcvend⟩ := hrest.conv_start hβ
            (Conv.subst hβ hcB2 (Conv.refl v) 0)
          have hocc0 : Term.occ 0 ufr ≤ 1 := by
            have h1 := hocc2 (by intro hc; cases hc)
            rw [← hub] at h1
            rw [Term.occ_msubstAt 1 0 (by omega) uenv huenv ufr] at h1
            exact h1
          obtain ⟨t_r, u_r, C_r, Cs, hred, ⟨Tr, herar, hcvr⟩, hcgr,
              hsubr, hbelowr⟩ :=
            ih (A1 :: Γ) B1 ufr hbraw (v :: env) (u0 :: uenv) W' rest
              (Cq0 :: Css) Cssq'
              (Term.subst 0 v B2) T'' (Term.msubstAt 0 (u0 :: uenv) ufr)
              uqrest0 jp'
              (by simp only [List.length_cons]; omega)
              (by simp only [List.length_cons]; omega)
              (by simp only [List.length_cons]; omega)
              (by
                intro w hw
                rcases List.mem_cons.mp hw with h1 | h2
                · subst h1
                  exact hvcl
                · exact henv w h2)
              (by
                intro w hw
                rcases List.mem_cons.mp hw with h1 | h2
                · subst h1
                  exact hva.closed_out
                · exact huenv w h2)
              (by
                intro p hp
                simp only [List.zip_cons_cons] at hp
                rcases List.mem_cons.mp hp with h1 | h2
                · subst h1
                  exact hpairq ((Cq0, v), u0) (by
                    simp only [List.zip_cons_cons]
                    exact List.mem_cons_self)
                · exact hpair p h2)
              (by
                intro p hp
                simp only [List.zip_cons_cons] at hp
                rcases List.mem_cons.mp hp with h1 | h2
                · subst h1
                  exact hp0.2
                · exact henvP p h2)
              (by
                intro i hi
                cases i with
                | zero => exact hocc0
                | succ i =>
                  have h1 := hocc i (by
                    simp only [List.length_cons] at hi
                    omega)
                  simp only [Term.occ] at h1
                  exact h1)
              hsub _root_.rfl
              hrestv hrest'
              (by omega)
              (fun p hp => hpairq p (by
                simp only [List.zip_cons_cons]
                exact List.mem_cons_of_mem _ hp))
              (by
                simp only [List.length_cons] at hjp
                rcases hcase with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> omega)
              (by
                rw [horig']
                exact horig)
              (by
                rcases hcase with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;>
                  subst h3 <;>
                  first
                  | (simp only [List.length_append, List.length_cons,
                      List.length_nil]
                     omega)
                  | omega)
              hlok' hst'
          refine ⟨t_r, u_r, C_r, Cs, ?_, ⟨Tr, herar,
            Conv.trans hβ hcvr hcvend⟩, hcgr, ?_, hbelowr⟩
          · rw [hinstf]
            refine Red.trans ?_ hred
            show Red β .weak (Term.apps
              (.App (.Lam (Term.msubstAt 1 env f0)) v) rest) _
            refine Red.trans (Red.apps (Red.one Step.beta) rest) ?_
            rw [show Term.subst 0 v (Term.msubstAt 1 env f0)
              = Term.msubstAt 0 (v :: env) f0 from
                (Term.msubstAt_cons 0 v hvcl env henvc f0).symm]
            exact Red.refl
          · refine Sub.perm_right hsubr ?_
            show (Cs ++ ((Cq0 ++ Css.flatten) ++ Cssq'.flatten)).Perm
              (Cs ++ (Css.flatten ++ (Cq0 ++ Cssq'.flatten)))
            refine List.Perm.append_left Cs ?_
            exact List.Perm.trans (perm_rotate Cq0 Css.flatten Cssq'.flatten)
              List.perm_append_comm
        | @dead _ A B _ πva _ _ uqrest hc0 hvchk hrest =>
          obtain ⟨q2, A2, B2, ubody, hcv2, hbody, hocc2, hueq2⟩ :=
            Era.lam_inv hβ (Era.cnv (hinstf ▸ hera) hc0)
          rw [hconn] at hueq2
          injection hueq2 with hub
          obtain ⟨hq2, hcA2, hcB2⟩ := Conv.all_inj hcv2
          subst hq2
          have hocc20 : Term.occ 0 ubody = 0 := by
            have h1 := hocc2 (by intro hc; cases hc)
            simp only [Quant.occN] at h1
            omega
          have hsub := hbody.sub_dead hβ Cut.zero
            (Check.cnv hvchk (Conv.symm hcA2)) hvcl hocc20
          rw [← hub] at hsub
          rw [show Term.subst 0 v (Term.msubstAt 1 env f0)
            = Term.msubstAt 0 (v :: env) f0 from
              (Term.msubstAt_cons 0 v hvcl env henvc f0).symm] at hsub
          rw [show Term.subst 0 Term.Typ (Term.msubstAt 1 uenv ufr)
            = Term.msubstAt 0 (.Typ :: uenv) ufr from
              (Term.msubstAt_cons 0 .Typ (by trivial) uenv huenv
                ufr).symm] at hsub
          obtain ⟨T'', hrest', hcvend⟩ := hrest.conv_start hβ
            (Conv.subst hβ hcB2 (Conv.refl v) 0)
          have hocc0 : Term.occ 0 ufr ≤ 1 := by
            have h1 : Term.occ 0 ubody = Term.occ 0 ufr := by
              rw [← hub]
              exact Term.occ_msubstAt 1 0 (by omega) uenv huenv ufr
            omega
          obtain ⟨t_r, u_r, C_r, Cs, hred, ⟨Tr, herar, hcvr⟩, hcgr,
              hsubr, hbelowr⟩ :=
            ih (A1 :: Γ) B1 ufr hbraw (v :: env) (.Typ :: uenv) W' rest
              (Cq0 :: Css) Cssq'
              (Term.subst 0 v B2) T'' (Term.msubstAt 0 (.Typ :: uenv) ufr)
              uqrest0 jp'
              (by simp only [List.length_cons]; omega)
              (by simp only [List.length_cons]; omega)
              (by simp only [List.length_cons]; omega)
              (by
                intro w hw
                rcases List.mem_cons.mp hw with h1 | h2
                · subst h1
                  exact hvcl
                · exact henv w h2)
              (by
                intro w hw
                rcases List.mem_cons.mp hw with h1 | h2
                · subst h1
                  trivial
                · exact huenv w h2)
              (by
                intro p hp
                simp only [List.zip_cons_cons] at hp
                rcases List.mem_cons.mp hp with h1 | h2
                · subst h1
                  exact hpairq ((Cq0, v), .Typ) (by
                    simp only [List.zip_cons_cons]
                    exact List.mem_cons_self)
                · exact hpair p h2)
              (by
                intro p hp
                simp only [List.zip_cons_cons] at hp
                rcases List.mem_cons.mp hp with h1 | h2
                · subst h1
                  exact Or.inl _root_.rfl
                · exact henvP p h2)
              (by
                intro i hi
                cases i with
                | zero => exact hocc0
                | succ i =>
                  have h1 := hocc i (by
                    simp only [List.length_cons] at hi
                    omega)
                  simp only [Term.occ] at h1
                  exact h1)
              hsub _root_.rfl
              hrestv hrest'
              (by omega)
              (fun p hp => hpairq p (by
                simp only [List.zip_cons_cons]
                exact List.mem_cons_of_mem _ hp))
              (by
                simp only [List.length_cons] at hjp
                rcases hcase with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> omega)
              (by
                rw [horig']
                exact horig)
              (by
                rcases hcase with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;>
                  subst h3 <;>
                  first
                  | (simp only [List.length_append, List.length_cons,
                      List.length_nil]
                     omega)
                  | omega)
              hlok' hst'
          refine ⟨t_r, u_r, C_r, Cs, ?_, ⟨Tr, herar,
            Conv.trans hβ hcvr hcvend⟩, hcgr, ?_, hbelowr⟩
          · rw [hinstf]
            refine Red.trans ?_ hred
            show Red β .weak (Term.apps
              (.App (.Lam (Term.msubstAt 1 env f0)) v) rest) _
            refine Red.trans (Red.apps (Red.one Step.beta) rest) ?_
            rw [show Term.subst 0 v (Term.msubstAt 1 env f0)
              = Term.msubstAt 0 (v :: env) f0 from
                (Term.msubstAt_cons 0 v hvcl env henvc f0).symm]
            exact Red.refl
          · refine Sub.perm_right hsubr ?_
            show (Cs ++ ((Cq0 ++ Css.flatten) ++ Cssq'.flatten)).Perm
              (Cs ++ (Css.flatten ++ (Cq0 ++ Cssq'.flatten)))
            refine List.Perm.append_left Cs ?_
            exact List.Perm.trans (perm_rotate Cq0 Css.flatten Cssq'.flatten)
              List.perm_append_comm
  | @mat n0 a0 A0 c0 C0 lhs0 h0 m0 hn hk0 hc0 htreeh htreem ihh ihm =>
    intro Γ Braw ubraw hraw env uenv W queue Css Cssq TN Tf' uN uq jp
      hΓl hl1 hl2 henv huenv hpair henvP hocc hera hconn hqv hsp hlq hpairq
      hjp horig harity hlok hstate
    have henvc : ∀ x ∈ env, Term.Closed 0 x := henv
    obtain ⟨A0', C0', r0, ps0, telF, B0, G0, q'0, uhr, umr, hk0r, hc00r,
      hr0, hlen0, hlive0, hins0, hgoal0, hmhr, hmmr, hcvM, hueqr⟩ :=
      Era.mat_inv hβ hraw
    subst hueqr
    rw [hk0] at hk0r
    cases hk0r
    rw [hc0] at hc00r
    cases hc00r
    rw [Term.msubstAt_mat] at hconn
    have hinstm : Term.msubstAt 0 env (.Mat a0 c0 h0 m0)
        = .Mat a0 c0 (Term.msubstAt 0 env h0) (Term.msubstAt 0 env m0) :=
      Term.msubstAt_mat 0 env a0 c0 h0 m0
    cases queue with
    | nil =>
      -- underapplied: the suspended Mat prices below the spent charge
      cases hsp
      have hjp0 : jp = 0 := by
        simp only [List.length_nil] at hjp
        omega
      subst hjp0
      have hW : W = args0 := by
        rw [← horig]
        simp
      rcases hstate with ⟨ws, hnl, hinst, _, hlenw, hfacts⟩ |
        ⟨L, ws, T, jpm, _, hjpe, _⟩
      · have hwlt : ws.length < dk.n := by omega
        have hwsc : ∀ v ∈ ws, v.Closed 0 := by
          intro v hv
          obtain ⟨j, hj1, hj2, hj3⟩ := mem_take_getD .Typ ws ws.length v
            (by
              rw [List.take_length]
              exact hv)
          rw [← hj3]
          exact (hfacts j (by omega)).1
        obtain ⟨Cs, Crs, hlenr, hcg, hslots, hbelow⟩ :=
          Tree.suspend hβ hok hd ws hwsc hwlt sp hspl
            (by
              intro j hj
              rcases hspc0 j (by omega) with h2 | ⟨h3, h4⟩
              · exact Or.inl h2
              · right
                rw [h4]
                congr 1
                rw [← hW]
                exact ((hfacts j (by omega)).2).symm
            )
            (by
              intro j hj1 hj2
              rcases hspc0 j (by omega) with h2 | ⟨h3, h4⟩
              · exact h2
              · exfalso
                rw [← hW] at h3
                omega)
            (by
              obtain ⟨ss, hs1, hs2⟩ := hsp_slack
              refine ⟨ss, hs1, ?_⟩
              rw [hW] at hlenw
              omega)
            (by
              intro j hj hq
              exact hspmask j hj hq)
            ph0 env uenv Css hl1 hl2 henv huenv hpair henvP
            (Tree.mat hn hk0 hc0 htreeh htreem) Γ Braw
            (.Mat a0 c0 uhr umr) hraw 0
            (by omega)
            (by
              intro i hi
              rw [Nat.zero_add]
              exact hocc i hi)
            hlok
            (Or.inl ⟨[], hnl, by
              rw [hinst]
              simp⟩)
        refine ⟨Term.msubstAt 0 env (.Mat a0 c0 h0 m0), uN,
          Cs ++ Crs.flatten, Cs,
          .refl, ⟨TN, hera, Conv.refl _⟩, ?_, ?_, hbelow⟩
        · rw [show uN = Term.msubstAt 0 uenv (.Mat a0 c0 uhr umr) from by
            rw [Term.msubstAt_mat]
            exact hconn]
          exact hcg
        · cases Cssq with
          | cons _ _ => exact absurd hlq (by simp)
          | nil =>
            refine Sub.perm_right (Sub.append (Sub.refl Cs)
              (Sub.flatten (by omega)
                (fun i hi => (hslots i (by omega)).1))) ?_
            simp
      · omega
    | cons w rest =>
      obtain ⟨u0m, uqrest0m, huqeqm⟩ : ∃ u0 uqrest0, uq = u0 :: uqrest0 := by
        cases hsp with
        | live _ _ _ => exact ⟨_, _, _root_.rfl⟩
        | dead _ _ _ => exact ⟨_, _, _root_.rfl⟩
      subst huqeqm
      have hpw : w.Closed 0 ∧ (u0m = .Typ ∨ DeepP β w u0m) := hqv (w, u0m) (by
        simp only [List.zip_cons_cons]
        exact List.mem_cons_self)
      have hwcl : w.Closed 0 := hpw.1
      have hrestv : ∀ p ∈ rest.zip uqrest0m,
          p.1.Closed 0 ∧ (p.2 = .Typ ∨ DeepP β p.1 p.2) :=
        fun p hp => hqv p (by
          simp only [List.zip_cons_cons]
          exact List.mem_cons_of_mem _ hp)
      cases Cssq with
      | nil => exact absurd hlq (by simp)
      | cons Cq0 Cssq' =>
        simp only [List.length_cons] at hlq
        -- the instantiated mat's own inversion
        obtain ⟨Ai, Ci, ri, psi, telFi, Bi, Gi, q'i, uhi, umi, hk0i, hc0i,
          hri, hleni, hlivei, hinsi, hgoali, hmhi, hmmi, hcvMi, hueqi⟩ :=
          Era.mat_inv hβ (hinstm ▸ hera)
        rw [hk0] at hk0i
        cases hk0i
        rw [hc0] at hc0i
        cases hc0i
        rw [hconn] at hueqi
        injection hueqi with hueqa hueqc hueq1 hueq2
        cases hsp with
        | @dead _ A B _ πva _ _ uqrest hc0d hvchk hrest =>
          exfalso
          have hall := Conv.all_inj (Conv.trans hβ hcvMi hc0d)
          exact hlivei hall.1
        | @live _ A B _ uva _ _ uqrest hc0l hva hrest =>
          have hall := Conv.all_inj (Conv.trans hβ hcvMi hc0l)
          obtain ⟨hq'i, hcAi, hcBi⟩ := hall
          subst hq'i
          have hwvd : DeepP β w u0m := by
            rcases hpw.2 with htypv | hdeepw
            · exfalso
              rw [htypv] at hva
              exact Conv.typ_adt (Conv.trans hβ
                (Era.typ_out_inv hβ hva _root_.rfl) (Conv.symm hcAi))
            · exact hdeepw
          have hwv : Term.Value β w ∧ w.Closed 0 := ⟨hwvd.value, hwcl⟩
          obtain ⟨πa1, hvachk⟩ := hva.check_none
          obtain ⟨c1, C1, as1, hweq, hC1, hnr1, hlen1⟩ :=
            Check.canon_adt hβ hok hwv.1 hvachk
              (fun _ _ _ hxeq hk2 => Era.ref_head_body hβ hva hxeq hk2)
              hk0 (Conv.symm hcAi)
          subst hweq
          obtain ⟨Tfh, uhead, T', us, hheadera, hspw, hcvT', hueq3⟩ :=
            Era.apps_inv hβ (Eq.refl _) hva
          subst hueq3
          obtain ⟨A1, C1', rr0, hA1, hC1', hrr0, hcty, huhead⟩ :=
            Era.ctr_head_inv hβ hheadera
          subst huhead
          rw [hk0] at hA1
          cases hA1
          rw [hC1] at hC1'
          cases hC1'
          have hshape := ((hok.adt_clauses hk0).2.2 c1 C1 hC1).2
          have hw := WTele.retip rr0 hshape
          obtain ⟨πsp, hspc⟩ := hspw.chk
          rcases ChkSpine.wtele_walk hβ hspc hw hcty with
            ⟨_, qA, AA, BB, hcAll⟩ | ⟨hlenAs, hcadt⟩
          · exact absurd (Conv.trans hβ hcAll
              (Conv.trans hβ hcvT' (Conv.symm hcAi))) Conv.all_adt
          · have hchainC : Conv β
                (Term.apps (.Adt a0 rr0) ([] ++ as1.take A0.pn))
                (Term.apps (.Adt a0 ri) psi) :=
              Conv.trans hβ hcadt (Conv.trans hβ hcvT' (Conv.symm hcAi))
            obtain ⟨_, hrr, hconvs⟩ := Conv.adt_inj hchainC
            subst hrr
            simp only [List.nil_append] at hconvs
            obtain ⟨pps, xs, hsplit, hlenp1, hlenx1⟩ :
                ∃ pps xs, as1 = pps ++ xs ∧ pps.length = A0.pn ∧
                  xs.length = C1.fn := by
              refine ⟨as1.take A0.pn, as1.drop A0.pn,
                (List.take_append_drop _ _).symm, ?_, ?_⟩
              · rw [List.length_take]
                omega
              · rw [List.length_drop]
                omega
            subst hsplit
            have htake : (pps ++ xs).take A0.pn = pps := by
              rw [← hlenp1]
              exact take_append pps xs
            rw [htake] at hconvs
            by_cases hcc : c1 = c0
            · -- matc: fire the arm
              subst hcc
              rw [hc0] at hC1
              injection hC1 with hCC
              subst hCC
              have hchain0 := hspw.retipS hβ hw hcty hlenAs []
              rw [WTele.retip_retip hshape [] rr0,
                WTele.retip_self hshape] at hchain0
              obtain ⟨Tmid, us1, us2, hsp1, hsp2, husplit⟩ :=
                EraSpine.append_split hchain0
              subst husplit
              obtain ⟨π1c, hsp1c⟩ := hsp1.chk
              obtain ⟨Tinst, hinsts, hcvmid, hFsh⟩ :=
                ChkSpine.insts_mid hβ hsp1c hshape (Conv.refl _) hlenp1
              have hcvTel : Conv β Tinst telFi :=
                Insts.conv hβ hinsts hinsi (Conv.refl _) hconvs
              have hGchain := MatGoal.erebuild hβ C0.fn hgoali hsp2
                (Conv.trans hβ (Conv.symm hcvTel) hcvmid) hlenx1
              have hglue : Conv β
                  (Term.subst 0 (Term.apps (Term.apps (.Ctr a0 c1) psi) xs)
                    Bi) (Term.subst 0 (Term.apps (.Ctr a0 c1) (pps ++ xs))
                      B) := by
                refine Conv.subst hβ hcBi ?_ 0
                rw [← Term.apps_append]
                refine Conv.apps_cong hβ (Conv.refl _) ?_
                exact Convs.append (Convs.symm hconvs) (Convs.refl xs)
              obtain ⟨T'', hrest', hcvend⟩ := hrest.conv_start hβ hglue
              have hspine' := hGchain.append hrest'
              -- split the scrutinee's charges into its fields'
              have hpairw := hpairq ((Cq0, Term.apps (.Ctr a0 c1)
                (pps ++ xs)), Term.apps (.Ctr a0 c1) (us1 ++ us2)) (by
                simp only [List.zip_cons_cons]
                exact List.mem_cons_self)
              have hlenus : (pps ++ xs).length = (us1 ++ us2).length :=
                hspw.lengths
              obtain ⟨CssW, hlenW, hpairW, hsubW⟩ :=
                hpairw.ctr_spine_inv _root_.rfl _root_.rfl hlenus
              have hlenus1 : us1.length = A0.pn := by
                have h1 := hsp1.lengths
                omega
              have hlenW2 : CssW.length = (pps ++ xs).length := by
                rw [hlenW, ← hlenus]
              have hCssWsplit : CssW = CssW.take A0.pn ++ CssW.drop A0.pn :=
                (List.take_append_drop _ _).symm
              have hpairxs : ∀ p ∈ ((CssW.drop A0.pn).zip xs).zip us2,
                  CG β p.1.1 p.1.2 p.2 := by
                intro p hp
                refine hpairW p ?_
                rw [hCssWsplit]
                have hz1 : ((CssW.take A0.pn ++ CssW.drop A0.pn).zip
                    (pps ++ xs)) = (CssW.take A0.pn).zip pps
                      ++ (CssW.drop A0.pn).zip xs := by
                  refine zip_append_of_len _ _ _ _ ?_
                  simp only [List.length_take]
                  omega
                rw [hz1]
                have hz2 : (((CssW.take A0.pn).zip pps
                    ++ (CssW.drop A0.pn).zip xs).zip (us1 ++ us2))
                    = ((CssW.take A0.pn).zip pps).zip us1
                      ++ ((CssW.drop A0.pn).zip xs).zip us2 := by
                  refine zip_append_of_len _ _ _ _ ?_
                  simp only [List.length_zip, List.length_take]
                  omega
                rw [hz2]
                exact List.mem_append.mpr (Or.inr hp)
              obtain ⟨W', jp', hcase, horig', hst'⟩ := DriveSt.peel β k
                lhs0 env W (Term.apps (.Ctr a0 c1) (pps ++ xs)) rest jp
                henv hwv hlok hk0 hc0 pps xs _root_.rfl hlenp1 hlenx1
                hstate
              have hocch : ∀ i, i < uenv.length → Term.occ i uhr ≤ 1 := by
                intro i hi
                have h1 := hocc i hi
                simp only [Term.occ] at h1
                have hx : Term.occ i uhr
                    ≤ Nat.max (Term.occ i uhr) (Term.occ i umr) :=
                  Nat.le_max_left _ _
                omega
              have hxscl : ∀ x ∈ xs, x.Closed 0 := by
                intro x hx
                have h1 := hwv.2
                rw [Term.closed_apps] at h1
                exact h1.2 x (List.mem_append.mpr (Or.inr hx))
              have hfieldp : ∀ p ∈ xs.zip us2,
                  p.2 = Term.Typ ∨ DeepP β p.1 p.2 := by
                intro p hp
                by_cases htok : p.2 = Term.Typ
                · exact Or.inl htok
                · refine Or.inr ((DeepP.apps_pairs (by trivial)
                    (by trivial) (fun _ he => Term.noConfusion he)
                    hwvd).2 p ?_ htok)
                  rw [zip_append_of_len pps us1 xs us2 (by
                    have h5 := hsp1.lengths
                    omega)]
                  exact List.mem_append.mpr (Or.inr hp)
              obtain ⟨t_r, u_r, C_r, Cs, hred, ⟨Tr, herar, hcvr⟩, hcgr,
                  hsubr, hbelowr⟩ :=
                ihh Γ G0 uhr hmhr env uenv W' (xs ++ rest) Css
                  ((CssW.drop A0.pn) ++ Cssq') Gi T''
                  uhi (us2 ++ uqrest0m) jp'
                  hΓl hl1 hl2 henv huenv hpair henvP hocch
                  (hueq1 ▸ hmhi) hueq1.symm
                  (by
                    intro p hp
                    obtain ⟨p1, p2⟩ := p
                    rw [zip_append_of_len xs us2 rest uqrest0m (by
                      have h5 := hsp2.lengths
                      omega)] at hp
                    rcases List.mem_append.mp hp with h1 | h2
                    · exact ⟨hxscl p1 (List.of_mem_zip h1).1,
                        hfieldp (p1, p2) h1⟩
                    · exact hrestv (p1, p2) h2)
                  hspine'
                  (by
                    simp only [List.length_append, List.length_drop]
                    omega)
                  (by
                    intro p hp
                    have hz3 : (((CssW.drop A0.pn) ++ Cssq').zip
                        (xs ++ rest)) = (CssW.drop A0.pn).zip xs
                          ++ Cssq'.zip rest := by
                      refine zip_append_of_len _ _ _ _ ?_
                      simp only [List.length_drop]
                      omega
                    rw [hz3] at hp
                    have hz4 : (((CssW.drop A0.pn).zip xs
                        ++ Cssq'.zip rest).zip (us2 ++ uqrest0m))
                        = ((CssW.drop A0.pn).zip xs).zip us2
                          ++ (Cssq'.zip rest).zip uqrest0m := by
                      refine zip_append_of_len _ _ _ _ ?_
                      simp only [List.length_zip, List.length_drop]
                      have h5 := hsp2.lengths
                      have h6 := hrest.lengths
                      omega
                    rw [hz4] at hp
                    rcases List.mem_append.mp hp with h1 | h2
                    · exact hpairxs p h1
                    · exact hpairq p (by
                        simp only [List.zip_cons_cons]
                        exact List.mem_cons_of_mem _ h2))
                  (by
                    simp only [List.length_cons] at hjp
                    rcases hcase with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;>
                      simp only [List.length_append] <;> omega)
                  (by
                    rw [horig']
                    exact horig)
                  (by
                    rcases hcase with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;>
                      subst h3 <;>
                      first
                      | (simp only [List.length_append, List.length_cons,
                          List.length_nil]
                         omega)
                      | omega)
                  (Term.lhsOk.lhsExt hlok a0 c1 C0.fn) hst'
              refine ⟨t_r, u_r, C_r, Cs, ?_, ⟨Tr, herar,
                Conv.trans hβ hcvr hcvend⟩, hcgr, ?_, hbelowr⟩
              · rw [hinstm]
                refine Red.trans ?_ hred
                show Red β .weak (Term.apps
                  (.App (.Mat a0 c1 (Term.msubstAt 0 env h0)
                    (Term.msubstAt 0 env m0))
                    (Term.apps (.Ctr a0 c1) (pps ++ xs))) rest) _
                refine Red.trans
                  (Red.apps (Red.one (Step.matc hk0 hc0 hlenp1 hlenx1))
                    rest) ?_
                rw [← Term.apps_append]
                exact Red.refl
              · refine Sub.trans hsubr ?_
                refine Sub.append (Sub.refl Cs) ?_
                refine Sub.append (Sub.refl Css.flatten) ?_
                show Sub ((CssW.drop A0.pn) ++ Cssq').flatten
                  (Cq0 ++ Cssq'.flatten)
                rw [List.flatten_append]
                refine Sub.append ?_ (Sub.refl _)
                refine Sub.trans ?_ hsubW
                have hfl : CssW.flatten = (CssW.take A0.pn).flatten
                    ++ (CssW.drop A0.pn).flatten := by
                  rw [← List.flatten_append, List.take_append_drop]
                rw [hfl]
                exact Sub.append_left _ _
            · -- matm: same state, remainder arm
              have hchain2 := hspw.retipS hβ hw hcty hlenAs (c0 :: rr0)
              rw [WTele.retip_retip hshape (c0 :: rr0) rr0] at hchain2
              simp only [List.nil_append] at hchain2
              rw [htake] at hchain2
              have hheadty : Era β [] (.Ctr a0 c1)
                  (Term.retip (c0 :: rr0) (A0.pn + C1.fn) C1.ty)
                  (.Ctr a0 c1) := by
                refine Era.ctr hk0 hC1 ?_
                intro hmem
                rcases List.mem_cons.mp hmem with h1 | h1
                · exact hcc h1
                · exact hrr0 h1
              have hscrut := hchain2.era hheadty
              have hscrut2 : Era β []
                  (Term.apps (.Ctr a0 c1) (pps ++ xs))
                  (Term.apps (.Adt a0 (c0 :: rr0)) psi)
                  (Term.apps (.Ctr a0 c1) us) :=
                Era.cnv hscrut
                  (Conv.apps_cong hβ (Conv.refl _) hconvs)
              obtain ⟨T'', hrest', hcvend⟩ := hrest.conv_start hβ
                (Conv.subst hβ hcBi (Conv.refl _) 0)
              have hspine' : EraSpine β []
                  (.All .Lone (Term.apps (.Adt a0 (c0 :: rr0)) psi) Bi)
                  (Term.apps (.Ctr a0 c1) (pps ++ xs) :: rest) T''
                  (Term.apps (.Ctr a0 c1) us :: uqrest0m) :=
                .live (Conv.refl _) hscrut2 hrest'
              have hoccm : ∀ i, i < uenv.length → Term.occ i umr ≤ 1 := by
                intro i hi
                have h1 := hocc i hi
                simp only [Term.occ] at h1
                have hx : Term.occ i umr
                    ≤ Nat.max (Term.occ i uhr) (Term.occ i umr) :=
                  Nat.le_max_right _ _
                omega
              obtain ⟨t_r, u_r, C_r, Cs, hred, ⟨Tr, herar, hcvr⟩, hcgr,
                  hsubr, hbelowr⟩ :=
                ihm Γ (.All q'0 (Term.apps (.Adt a0 (c0 :: r0)) ps0) B0)
                  umr hmmr env uenv W
                  (Term.apps (.Ctr a0 c1) (pps ++ xs) :: rest) Css
                  (Cq0 :: Cssq')
                  (.All .Lone (Term.apps (.Adt a0 (c0 :: rr0)) psi) Bi)
                  T'' umi (Term.apps (.Ctr a0 c1) us :: uqrest0m) jp
                  hΓl hl1 hl2 henv huenv hpair henvP hoccm
                  (hueq2 ▸ hmmi) hueq2.symm
                  hqv hspine' (by simp only [List.length_cons]; omega)
                  hpairq hjp horig harity hlok hstate
              refine ⟨t_r, u_r, C_r, Cs, ?_, ⟨Tr, herar,
                Conv.trans hβ hcvr hcvend⟩, hcgr, hsubr, hbelowr⟩
              rw [hinstm]
              refine Red.trans ?_ hred
              show Red β .weak (Term.apps
                (.App (.Mat a0 c0 (Term.msubstAt 0 env h0)
                  (Term.msubstAt 0 env m0))
                  (Term.apps (.Ctr a0 c1) (pps ++ xs))) rest) _
              refine Red.apps (Red.one (Step.matm ?_)) rest
              exact fun hpair2 => hcc (congrArg Prod.snd hpair2)


-- ============================================================================
-- METATHEORY §NF — claims (4) and (5) for plain (recursion-free) books.
-- every era rule except the application rules outputs a non-App
-- erasure, so non-application subjects have atomic-spined erasures
theorem Term.spine_non_app (h : ∀ f a : Term, u ≠ .App f a) :
    Term.spine u = (u, []) := by
  cases u <;> first
  | rfl
  | exact absurd _root_.rfl (h _ _)

theorem Era.u_non_app (h : Era β Γ t T u)
    (ht : ∀ f a : Term, t ≠ .App f a) : ∀ f a : Term, u ≠ .App f a := by
  induction h with
  | var _ => exact fun f a he => Term.noConfusion he
  | ref _ => exact fun f a he => Term.noConfusion he
  | refA _ _ => exact fun f a he => Term.noConfusion he
  | adt _ => exact fun f a he => Term.noConfusion he
  | ctr _ _ _ => exact fun f a he => Term.noConfusion he
  | typ => exact fun f a he => Term.noConfusion he
  | all _ _ _ => exact fun f a he => Term.noConfusion he
  | lam _ _ _ => exact fun f a he => Term.noConfusion he
  | app_live _ _ _ _ => exact absurd _root_.rfl (ht _ _)
  | app_dead _ _ _ => exact absurd _root_.rfl (ht _ _)
  | let_live _ _ _ _ _ => exact fun f a he => Term.noConfusion he
  | let_dead _ _ _ _ => exact fun f a he => Term.noConfusion he
  | eql _ _ _ => exact fun f a he => Term.noConfusion he
  | rfl _ => exact fun f a he => Term.noConfusion he
  | rwt _ _ _ _ _ => exact fun f a he => Term.noConfusion he
  | mat _ _ _ _ _ _ _ _ _ _ _ => exact fun f a he => Term.noConfusion he
  | efq _ _ _ => exact fun f a he => Term.noConfusion he
  | cnv _ _ ih => exact ih ht

theorem DeepP.of_non_app (hv : Term.Value β t)
    (ht : ∀ f a : Term, t ≠ .App f a)
    (hu : ∀ f a : Term, u ≠ .App f a) : DeepP β t u := by
  refine .mk hv ?_ ?_
  · rw [Term.spine_non_app ht, Term.spine_non_app hu]
  · rw [Term.spine_non_app ht, Term.spine_non_app hu]
    intro p hp
    exact nomatch hp

theorem Spinal.head_not_ref (h : Spinal t) :
    ∀ j : Nat, (Term.spine t).1 ≠ .Ref j := by
  induction h with
  | adt => exact fun j he => Term.noConfusion he
  | ctr => exact fun j he => Term.noConfusion he
  | app _ ih => exact ih

-- rebuild a charged application spine from a head and paired arms
theorem CG.apps_build : ∀ {xs : List Term} {us : List Term}
    {Css : List (List Charge)} {h uh : Term} {Ch : List Charge},
    CG β Ch h uh → Css.length = us.length →
    (∀ p ∈ (Css.zip xs).zip us, CG β p.1.1 p.1.2 p.2) →
    xs.length = us.length →
    CG β (Ch ++ Css.flatten) (Term.apps h xs) (Term.apps uh us) := by
  intro xs
  induction xs with
  | nil =>
    intro us Css h uh Ch hh hlc hp hl
    cases us with
    | cons _ _ => exact absurd hl (by simp)
    | nil =>
      cases Css with
      | cons _ _ => exact absurd hlc (by simp)
      | nil => exact hh.pad (Sub.perm_left (Sub.refl _) (by simp))
  | cons x xs' ih =>
    intro us Css h uh Ch hh hlc hp hl
    cases us with
    | nil => exact absurd hl (by simp)
    | cons ux us' =>
      cases Css with
      | nil => exact absurd hlc (by simp)
      | cons Cx Css' =>
        have hhead : CG β (Ch ++ Cx) (.App h x) (.App uh ux) :=
          .app hh (hp ((Cx, x), ux) (by
            simp only [List.zip_cons_cons]
            exact List.mem_cons_self))
        have h2 := ih (us := us') (Css := Css') hhead (by
            simp only [List.length_cons] at hlc
            omega)
          (fun p hp2 => hp p (by
            simp only [List.zip_cons_cons]
            exact List.mem_cons_of_mem _ hp2))
          (by
            simp only [List.length_cons] at hl
            omega)
        refine h2.perm ?_
        show ((Ch ++ Cx) ++ Css'.flatten).Perm (Ch ++ (Cx ++ Css'.flatten))
        simp [List.append_assoc]

-- a nonempty erased spine starts at a function type; and a family
-- reference is never era-paired deep (its erasure is the stepped node)
theorem EraSpine.nonempty_all (hs : EraSpine β Γ T0 as T' us)
    (hne : as ≠ []) : ∃ qx A B, Conv β T0 (.All qx A B) := by
  cases hs with
  | nil => exact absurd _root_.rfl hne
  | live hc0 hx hrest => exact ⟨_, _, _, hc0⟩
  | dead hc0 hx hrest => exact ⟨_, _, _, hc0⟩

theorem Value.not_family_ref (hk : Book.adt β k = some A)
    (hv : Term.Value β (.Ref k)) : False := by
  generalize he : (Term.Ref k : Term) = t0 at hv
  cases hv with
  | typ => exact Term.noConfusion he
  | all => exact Term.noConfusion he
  | lam => exact Term.noConfusion he
  | mat => exact Term.noConfusion he
  | efq => exact Term.noConfusion he
  | eql => exact Term.noConfusion he
  | rfl => exact Term.noConfusion he
  | spine hsp =>
    subst he
    cases hsp
  | stuck hk2 hgate =>
    rcases apps_shape _ _ _ he.symm with ⟨h1, h2⟩ | ⟨as0, al, h1, h2⟩
    · injection h2 with hkk
      subst hkk
      exact Book.defn_adt_clash hk2 hk
    · exact Term.noConfusion h2

theorem DeepP.not_family_ref (hk : Book.adt β k = some A)
    (h : DeepP β (.Ref k) u) : False := by
  cases h with
  | mk hv _ _ => exact Value.not_family_ref hk hv
  | stuck hk2 hsp hgate =>
    rename_i k2 d2
    have hsp2 : (Term.spine (.Ref k)).1 = .Ref k2 := hsp
    injection hsp2 with hkk
    subst hkk
    exact Book.defn_adt_clash hk2 hk

-- ============================================================================
-- METATHEORY §NM — the master engine: over any Ok book, every closed
-- live term runs to an era-paired deep value. The measure is the
-- charge multiset paired with the unit erasure weight: interactions
-- pay with weight, reference spends replace one charge by strictly
-- smaller ones through the drive.
-- ============================================================================

theorem master (hβ : Book.Closed β) (hok : Book.Ok β) :
    ∀ (mw : List Charge × Nat), Acc MMeas mw →
    ∀ {t T u : Term} {C : List Charge},
    Era β [] t T u → t.Closed 0 → CG β C t u →
    mw = (C, Term.wgt (fun _ => 1) u) →
    ∃ (v uv : Term) (Cv : List Charge), Red β .weak t v ∧ v.Closed 0 ∧
      Era β [] v T uv ∧ DeepP β v uv ∧ CG β Cv v uv ∧
      MLe (Cv, Term.wgt (fun _ => 1) uv) (C, Term.wgt (fun _ => 1) u) ∧
      (u = .Typ → v = t) ∧ (DeepP β t u → v = t) := by
  intro mw hacc
  induction hacc with
  | intro mw0 hstep ihacc =>
    intro t T u C hera hct hcg hmw
    subst hmw
    have hdrive : ∀ (j : Nat) (xs : List Term) {t0 T0 u0 : Term}
        {C0 : List Charge},
        t0 = Term.apps (.Ref j) xs →
        Era β [] t0 T0 u0 → t0.Closed 0 → CG β C0 t0 u0 →
        MLe (C0, Term.wgt (fun _ => 1) u0)
          (C, Term.wgt (fun _ => 1) u) →
        (∀ {d0 : DefD}, Book.defn β j = some d0 → d0.n ≤ xs.length) →
        ∃ (v uv : Term) (Cv : List Charge), Red β .weak t0 v ∧
          v.Closed 0 ∧ Era β [] v T0 uv ∧ DeepP β v uv ∧ CG β Cv v uv ∧
          MLe (Cv, Term.wgt (fun _ => 1) uv)
            (C, Term.wgt (fun _ => 1) u) := by
      intro j xs t0 T0 u0 C0 hteq0 hera0 hct0 hcg0 hmleC hns0
      subst hteq0
      obtain ⟨Tf, uhead, T', us, hheadera, hspt, hcvT', hueq0⟩ :=
        Era.apps_inv hβ (Eq.refl _) hera0
      rcases Era.ref_inv hβ hheadera with ⟨d, hk, hbne, hcvd, huheq⟩ |
        ⟨A', hk, h0', hcvd, huheq⟩
      rotate_left
      · subst huheq
        subst hueq0
        cases hspt with
        | live hc0 hx hrest =>
          exact absurd (Conv.trans hβ hcvd hc0) Conv.typ_all
        | dead hc0 hx hrest =>
          exact absurd (Conv.trans hβ hcvd hc0) Conv.typ_all
        | nil =>
          have hsig : STele A'.pn A'.sig := (hok.adt_clauses hk).2.1
          rw [h0'] at hsig
          have hera2 : Era β [] (.Adt j []) T0 (.Adt j []) := by
            refine Era.cnv (Era.adt hk) ?_
            rw [hsig]
            exact Conv.trans hβ hcvd hcvT'
          have hunapp2 : ∀ f0 a0 : Term,
              (Term.Adt j [] : Term) ≠ .App f0 a0 :=
            fun f0 a0 he => Term.noConfusion he
          refine ⟨.Adt j [], .Adt j [], [],
            .step (Step.aref hk h0') .refl, trivial, hera2,
            DeepP.of_non_app (.spine .adt) hunapp2 hunapp2, .adt, ?_⟩
          exact MLe.trans hmleC (MLe_of_sub_wgt (Sub.nil _) (Nat.le_refl _))
      subst huheq
      subst hueq0
      have hlas : xs.length = us.length := hspt.lengths
      obtain ⟨dk, ts, ph, Css, hkd, hlcss, hpaircg, hsubinv, hlts,
          hcompat, hslack, hpin, hmaskx⟩ :=
        hcg0.ref_spine_inv (Eq.refl _) _root_.rfl hlas
      rw [hk] at hkd
      cases hkd
      have hns : d.n ≤ xs.length := hns0 hk
      have hctapps :
          (Term.apps (.Ref j) (xs)).Closed 0 :=
        hct0
      have hclas : ∀ x ∈ xs, x.Closed 0 := by
        rw [Term.closed_apps] at hctapps
        exact fun x hx => hctapps.2 x hx
      obtain ⟨vs, uvs, Css2, T2, hredd, hlenv, hclv, hpairv, hsp2,
          hcv2, hlenc2, hpair2, hmle2, hpos⟩ :=
        deepen_spine hβ (xs) hspt hclas Css hlcss
          hpaircg C0 (Term.wgt (fun _ => 1) (Term.apps (.Ref j) us))
          (by
            refine Sub.trans ?_ hsubinv
            exact ⟨[(j, ts, ph)], List.perm_append_comm
              (l₁ := [(j, ts, ph)]) (l₂ := Css.flatten)⟩)
          (by
            rw [Term.wgt_apps]
            have hr1 : Term.wgt (fun _ => 1) (Term.Ref j) = 1 :=
              _root_.rfl
            rw [hr1]
            omega)
          (fun x hx B' ub' Cx herax hclx hcgx hsubx hwx =>
            ihacc (Cx, Term.wgt (fun _ => 1) ub')
              (MMeas.after_le hmleC (MMeas_of_sub_wgt hsubx hwx))
              herax hclx hcgx _root_.rfl)
      have hspc0 : ∀ j2, j2 < d.n → ts.getD j2 none = none
          ∨ (j2 < vs.length ∧ ts.getD j2 none
              = some (Term.csize β (vs.getD j2 .Typ))) := by
        intro j2 hj2
        rcases hcompat j2 hj2 with h1 | ⟨h2, h3⟩
        · exact Or.inl h1
        · right
          refine ⟨by omega, ?_⟩
          rw [h3]
          have hne : ts.getD j2 none ≠ none := by
            rw [h3]
            simp
          obtain ⟨h4, h5, hpinj⟩ := hpin j2 hj2 hne
          rcases hpinj.spend with htok | hdp
          · rw [hpos j2 (by omega) (Or.inl htok)]
          · rw [hpos j2 (by omega) (Or.inr hdp)]
      have hslack2 : ∃ ss, ts.getD d.n none = some ss
          ∧ d.n - min vs.length d.n ≤ ss := by
        obtain ⟨ss, h1, h2⟩ := hslack
        refine ⟨ss, h1, ?_⟩
        rw [hlenv]
        omega
      obtain ⟨b, hb⟩ : ∃ b, d.body = some b := by
        cases hbb : d.body with
        | some b2 => exact ⟨b2, _root_.rfl⟩
        | none => exact absurd hbb hbne
      obtain ⟨_, _, hcl⟩ := hok.defn_clauses hk
      obtain ⟨⟨πb, hbody⟩, htree⟩ := hcl b hb
      obtain ⟨ub2, hbera, _, _⟩ := hbody.era _root_.rfl
      obtain ⟨T3, hsp3, hcv3⟩ := hsp2.conv_start hβ hcvd
      obtain ⟨t_r, u_r, C_r, Cs, hredr, ⟨Tr, herar, hcvr⟩, hcgr, hsubr,
          hbelow⟩ :=
        Tree.drive hβ hok hk vs ts hlts hspc0 hslack2 hmaskx ph
          htree []
          d.ty ub2 hbera [] [] [] vs [] Css2 d.ty T3 ub2 uvs 0
          _root_.rfl _root_.rfl _root_.rfl
          (fun v hv => nomatch hv) (fun v hv => nomatch hv)
          (fun p hp => nomatch hp) (fun p hp => nomatch hp)
          (by intro i hi; exact absurd hi (by simp))
          hbera _root_.rfl
          (by
            intro p hp
            exact ⟨hclv p.1 (List.of_mem_zip hp).1, hpairv p hp⟩)
          hsp3
          (by
            have h1 := hsp2.lengths
            omega)
          hpair2 (Nat.zero_le _)
          _root_.rfl _root_.rfl trivial
          (Or.inl ⟨[], (fun L he => Term.noConfusion he), _root_.rfl,
            _root_.rfl, _root_.rfl,
            (by intro j2 hj2; exact absurd hj2 (by simp))⟩)
      obtain ⟨D, hpermD⟩ := hsubinv
      have hmred : MRed Css2.flatten Css.flatten := by
        rcases hmle2 with h1 | h1
        · rcases h1 with h2 | h2
          · exact Or.inl h2
          · exact Or.inr h2.1
        · exact Or.inr h1.1
      have hstep1 : MStep (Cs ++ (Css2.flatten ++ D))
          ((j, ts, ph) :: (Css2.flatten ++ D)) :=
        MStep.mk (j, ts, ph) Cs (Css2.flatten ++ D) hbelow
          (List.Perm.refl _) (List.Perm.refl _)
      have hmred2 : MRed ((j, ts, ph) :: (Css2.flatten ++ D))
          ((j, ts, ph) :: (Css.flatten ++ D)) := by
        rcases hmred with h1 | h1
        · left
          have h2 := MPlus.append h1 D
          have h3 := MPlus.append h2 [(j, ts, ph)]
          refine (h3.perm_left ?_).perm_right ?_
          · simpa using (List.perm_append_comm
              (l₁ := Css2.flatten ++ D) (l₂ := [(j, ts, ph)]))
          · simpa using (List.perm_append_comm
              (l₁ := Css.flatten ++ D) (l₂ := [(j, ts, ph)]))
        · right
          exact (h1.append_right D).cons _
      have hmredBC : MRed ((j, ts, ph) :: (Css2.flatten ++ D)) C0 := by
        rcases hmred2 with h1 | h1
        · exact Or.inl (h1.perm_right hpermD.symm)
        · exact Or.inr (h1.trans hpermD.symm)
      have hmp : MPlus C_r C0 := by
        have hsubred : Sub C_r (Cs ++ (Css2.flatten ++ D)) := by
          refine hsubr.trans ?_
          exact ⟨D, by simp [List.append_assoc]⟩
        have hplusA : MPlus (Cs ++ (Css2.flatten ++ D)) C0 :=
          MPlus.of_step_mred hstep1 hmredBC
        rcases hsubred.mplus_or_perm with h1 | h1
        · exact MPlus.trans h1 hplusA
        · exact hplusA.perm_left h1.symm
      obtain ⟨πr, hrchk⟩ := herar.check_none
      have hrc := hrchk.closed
      have hmpC : MPlus C_r C := by
        rcases hmleC with hmm | ⟨hperm, _⟩
        · rcases hmm with hplus | ⟨hperm2, _⟩
          · exact hmp.trans hplus
          · exact hmp.perm_right hperm2
        · exact hmp.perm_right hperm
      obtain ⟨w, uw, Cw, hred, hwc, hwera, hwdeep, hwcg, hwle, _, _⟩ :=
        ihacc (C_r, Term.wgt (fun _ => 1) u_r)
          (Or.inl hmpC) herar hrc hcgr _root_.rfl
      refine ⟨w, uw, Cw, ?_, hwc,
        Era.cnv hwera (Conv.trans hβ hcvr (Conv.trans hβ hcv3
          (Conv.trans hβ hcv2 hcvT'))), hwdeep, hwcg, ?_⟩
      · refine (hredd (.Ref j)).trans ?_
        have hnsv : d.n ≤ vs.length := by
          rw [hlenv]
          omega
        have hsp4 : Term.spine (Term.apps (.Ref j) (vs.take d.n))
            = (.Ref j, vs.take d.n) :=
          Term.spine_apps (h := .Ref j) trivial _
        have htk : (vs.take d.n).length = d.n := by
          rw [List.length_take]
          omega
        have hstepd : Step β .weak (Term.apps (.Ref j) (vs.take d.n))
            (Term.apps b (vs.take d.n)) := by
          have h0 := Step.dref (β := β) (p := .weak)
            (s := Term.apps (.Ref j) (vs.take d.n)) hk hb
            (by rw [hsp4]) (by rw [hsp4]; exact htk)
          rwa [hsp4] at h0
        have hdstep : Red β .weak (Term.apps (.Ref j) vs)
            (Term.apps b vs) := by
          have he1 : Term.apps (.Ref j) vs
              = Term.apps (Term.apps (.Ref j) (vs.take d.n))
                (vs.drop d.n) := by
            rw [← Term.apps_append, List.take_append_drop]
          have he2 : Term.apps b vs
              = Term.apps (Term.apps b (vs.take d.n)) (vs.drop d.n) := by
            rw [← Term.apps_append, List.take_append_drop]
          rw [he1, he2]
          exact Red.apps (Red.step hstepd .refl) (vs.drop d.n)
        exact hdstep.trans (hredr.trans hred)
      · exact MLe.trans (Or.inl (Or.inl hmpC)) hwle
    cases t with
    | Var i =>
      simp only [Term.Closed] at hct
      omega
    | Typ =>
      have hunapp := Era.u_non_app hera (by intro f0 a0 he; cases he)
      exact ⟨_, u, C, .refl, hct, hera,
        DeepP.of_non_app .typ (by intro f0 a0 he; cases he) hunapp,
        hcg, MLe.refl _, fun _ => _root_.rfl, fun _ => _root_.rfl⟩
    | All q' A B =>
      have hunapp := Era.u_non_app hera (by intro f0 a0 he; cases he)
      exact ⟨_, u, C, .refl, hct, hera,
        DeepP.of_non_app .all (by intro f0 a0 he; cases he) hunapp,
        hcg, MLe.refl _, fun _ => _root_.rfl, fun _ => _root_.rfl⟩
    | Lam f =>
      have hunapp := Era.u_non_app hera (by intro f0 a0 he; cases he)
      exact ⟨_, u, C, .refl, hct, hera,
        DeepP.of_non_app .lam (by intro f0 a0 he; cases he) hunapp,
        hcg, MLe.refl _, fun _ => _root_.rfl, fun _ => _root_.rfl⟩
    | Mat a c h m =>
      have hunapp := Era.u_non_app hera (by intro f0 a0 he; cases he)
      exact ⟨_, u, C, .refl, hct, hera,
        DeepP.of_non_app .mat (by intro f0 a0 he; cases he) hunapp,
        hcg, MLe.refl _, fun _ => _root_.rfl, fun _ => _root_.rfl⟩
    | Efq =>
      have hunapp := Era.u_non_app hera (by intro f0 a0 he; cases he)
      exact ⟨_, u, C, .refl, hct, hera,
        DeepP.of_non_app .efq (by intro f0 a0 he; cases he) hunapp,
        hcg, MLe.refl _, fun _ => _root_.rfl, fun _ => _root_.rfl⟩
    | Eql x y T0 =>
      have hunapp := Era.u_non_app hera (by intro f0 a0 he; cases he)
      exact ⟨_, u, C, .refl, hct, hera,
        DeepP.of_non_app .eql (by intro f0 a0 he; cases he) hunapp,
        hcg, MLe.refl _, fun _ => _root_.rfl, fun _ => _root_.rfl⟩
    | Rfl =>
      have hunapp := Era.u_non_app hera (by intro f0 a0 he; cases he)
      exact ⟨_, u, C, .refl, hct, hera,
        DeepP.of_non_app .rfl (by intro f0 a0 he; cases he) hunapp,
        hcg, MLe.refl _, fun _ => _root_.rfl, fun _ => _root_.rfl⟩
    | Adt a r =>
      have hunapp := Era.u_non_app hera (by intro f0 a0 he; cases he)
      exact ⟨_, u, C, .refl, hct, hera,
        DeepP.of_non_app (.spine .adt) (by intro f0 a0 he; cases he) hunapp,
        hcg, MLe.refl _, fun _ => _root_.rfl, fun _ => _root_.rfl⟩
    | Ctr a c =>
      have hunapp := Era.u_non_app hera (by intro f0 a0 he; cases he)
      exact ⟨_, u, C, .refl, hct, hera,
        DeepP.of_non_app (.spine .ctr) (by intro f0 a0 he; cases he) hunapp,
        hcg, MLe.refl _, fun _ => _root_.rfl, fun _ => _root_.rfl⟩
    | Ref k =>
      rcases Era.ref_inv hβ hera with ⟨d, hk, hbne, hcv, hueq⟩ |
        ⟨A, hk, h0, hcv, hueq⟩
      rotate_left
      · subst hueq
        have hsig : STele A.pn A.sig := (hok.adt_clauses hk).2.1
        rw [h0] at hsig
        have hera2 : Era β [] (.Adt k []) T (.Adt k []) := by
          refine Era.cnv (Era.adt hk) ?_
          rw [hsig]
          exact hcv
        have hunapp2 : ∀ f0 a0 : Term,
            (Term.Adt k [] : Term) ≠ .App f0 a0 :=
          fun f0 a0 he => Term.noConfusion he
        refine ⟨.Adt k [], .Adt k [], [],
          .step (Step.aref hk h0) .refl, trivial, hera2,
          DeepP.of_non_app (.spine .adt) hunapp2 hunapp2, .adt, ?_, ?_, ?_⟩
        · exact MLe_of_sub_wgt (Sub.nil _) (Nat.le_refl _)
        · intro he
          exact Term.noConfusion he
        · intro hdp
          exact (DeepP.not_family_ref hk hdp).elim
      subst hueq
      by_cases hn0 : d.n = 0
      case neg =>
        exact ⟨_, _, C, .refl, hct, hera,
          DeepP.of_non_app (Term.Value.stuck (args := []) hk
            (Or.inl (by simpa using Nat.pos_of_ne_zero hn0)))
            (by intro f0 a0 he; cases he) (by intro f0 a0 he; cases he),
          hcg, MLe.refl _, fun _ => _root_.rfl, fun _ => _root_.rfl⟩
      case pos =>
      obtain ⟨dk, ts, ph, Css, hkd, hlcss, _, hsubinv, hlts, hcompat,
          hslack, _, hmaskx⟩ :=
        hcg.ref_spine_inv (k := k) (xs := []) (us := [])
          _root_.rfl _root_.rfl _root_.rfl
      rw [hk] at hkd
      cases hkd
      have hcssnil : Css = [] := by
        cases Css with
        | nil => rfl
        | cons _ _ => exact absurd hlcss (by simp)
      subst hcssnil
      obtain ⟨b, hb⟩ : ∃ b, d.body = some b := by
        cases hbb : d.body with
        | some b2 => exact ⟨b2, _root_.rfl⟩
        | none => exact absurd hbb hbne
      obtain ⟨_, _, hcl⟩ := hok.defn_clauses hk
      obtain ⟨⟨πb, hbody⟩, htree⟩ := hcl b hb
      obtain ⟨ub, hbera, _, _⟩ := hbody.era _root_.rfl
      obtain ⟨t_r, u_r, C_r, Cs, hredr, ⟨Tr, herar, hcvr⟩, hcgr, hsubr,
          hbelow⟩ :=
        Tree.drive hβ hok hk [] ts hlts
          (by
            intro j hj
            rcases hcompat j hj with h1 | ⟨h2, _⟩
            · exact Or.inl h1
            · exact absurd h2 (by simp))
          (by
            obtain ⟨ss, h1, h2⟩ := hslack
            exact ⟨ss, h1, by omega⟩)
          hmaskx
          ph htree [] d.ty ub hbera [] [] [] [] [] [] d.ty d.ty ub [] 0
          _root_.rfl _root_.rfl _root_.rfl
          (fun v hv => nomatch hv) (fun v hv => nomatch hv)
          (fun p hp => nomatch hp) (fun p hp => nomatch hp)
          (by intro i hi; exact absurd hi (by simp))
          hbera _root_.rfl
          (fun p hp => nomatch hp) .nil _root_.rfl
          (fun p hp => nomatch hp) (Nat.le_refl 0) _root_.rfl
          _root_.rfl trivial
          (Or.inl ⟨[], (fun L he => Term.noConfusion he), _root_.rfl,
            _root_.rfl, _root_.rfl,
            (by intro j hj; exact absurd hj (by simp))⟩)
      obtain ⟨D, hpermD⟩ := hsubinv
      have hstepC : MStep (Cs ++ D) C := by
        refine MStep.mk (k, ts, ph) Cs D hbelow ?_ ?_
        · exact hpermD
        · exact List.Perm.refl _
      have hsubred : Sub C_r (Cs ++ D) := by
        refine hsubr.trans ?_
        refine Sub.perm_left (Sub.append_right Cs D) ?_
        simp
      have hmp : MPlus C_r C := by
        rcases hsubred.mplus_or_perm with h1 | h1
        · exact MPlus.trans h1 (.one hstepC)
        · exact .one (hstepC.perm_left h1.symm)
      obtain ⟨πr, hrchk⟩ := herar.check_none
      have hrc := hrchk.closed
      obtain ⟨w, uw, Cw, hred, hwc, hwera, hwdeep, hwcg, hwle, _, _⟩ :=
        ihacc (C_r, Term.wgt (fun _ => 1) u_r)
          (Or.inl hmp) herar hrc hcgr _root_.rfl
      refine ⟨w, uw, Cw, ?_, hwc,
        Era.cnv hwera (Conv.trans hβ hcvr hcv), hwdeep, hwcg, ?_,
        fun he => Term.noConfusion he,
        fun hd => absurd (hd.value.ref_cases hk) (by
          intro h
          rcases h with h | h
          · omega
          · rw [hb] at h; simp at h)⟩
      · exact (Red.step (Step.dref (s := .Ref k) hk hb rfl
          (by rw [hn0]; rfl)) hredr).trans hred
      · exact MLe.trans (Or.inl (Or.inl hmp)) hwle
    | Let qb v b =>
      rcases Era.let_inv hβ hera with
        ⟨A, uv0, T0, ub, hqb, hvera, hbera, hocc, hcv, hueq⟩ |
        ⟨A, πv, T0, ub, hqb, hvchk, hbera, hocc, hcv, hueq⟩
      · subst hqb hueq
        obtain ⟨Ca, Cb, hcgv, hcgb, hsubab⟩ :=
          hcg.pair_let_inv _root_.rfl _root_.rfl
        obtain ⟨πv0, hvchk0⟩ := hvera.check_none
        have huvc : uv0.Closed 0 := hvera.closed_out
        have hsub := hbera.sub hβ Cut.zero hvchk0
          (by intro hc; cases hc) hvera hct.1 huvc
        rw [Term.subst_shift T0 0 v] at hsub
        have hered := Era.cnv hsub hcv
        obtain ⟨πr, hrchk⟩ := hered.check_none
        have hrc := hrchk.closed
        obtain ⟨C', hcgsub, hsubc'⟩ := hcgb.subst_one 0 v uv0 Ca
          hct.1 huvc hcgv hocc
        have hsubC : Sub C' C := by
          refine (hsubc'.perm_right List.perm_append_comm).trans hsubab
        have hocc1 : Term.occ 0 ub * Term.wgt (fun _ => 1) uv0
            ≤ Term.wgt (fun _ => 1) uv0 := by
          have := Nat.mul_le_mul_right (Term.wgt (fun _ => 1) uv0) hocc
          omega
        have hws := Term.wgt_subst (fun _ => 1) ub 0 uv0
        have hwu : Term.wgt (fun _ => 1) (Term.Let .Lone uv0 ub)
            = 1 + Term.wgt (fun _ => 1) uv0
              + Term.wgt (fun _ => 1) ub := _root_.rfl
        have hwlt : Term.wgt (fun _ => 1) (Term.subst 0 uv0 ub)
            < Term.wgt (fun _ => 1) (Term.Let .Lone uv0 ub) := by
          rw [hwu]
          omega
        obtain ⟨w, uw, Cw, hred, hwc, hwera, hwdeep, hwcg, hwle, _, _⟩ :=
          ihacc (C', Term.wgt (fun _ => 1) (Term.subst 0 uv0 ub))
            (MMeas_of_sub_wgt hsubC hwlt) hered hrc hcgsub _root_.rfl
        refine ⟨w, uw, Cw, .step .let_ hred, hwc, hwera, hwdeep, hwcg,
          ?_, fun he => Term.noConfusion he,
          fun hd => hd.value.let_absurd.elim⟩
        exact MLe.trans (MLe_of_sub_wgt hsubC (Nat.le_of_lt hwlt)) hwle
      · subst hqb hueq
        obtain ⟨Ca, Cb, hcgv, hcgb, hsubab⟩ :=
          hcg.pair_let_inv _root_.rfl _root_.rfl
        have hsub := hbera.sub_dead hβ Cut.zero hvchk hct.1 hocc
        rw [Term.subst_shift T0 0 v] at hsub
        have hered := Era.cnv hsub hcv
        obtain ⟨πr, hrchk⟩ := hered.check_none
        have hrc := hrchk.closed
        have hcgsub := hcgb.subst_zero 0 v .Typ hct.1 (by trivial) hocc
        have hsubC : Sub Cb C :=
          (Sub.append_left Cb Ca).trans hsubab
        have hws := Term.wgt_subst (fun _ => 1) ub 0 .Typ
        rw [hocc] at hws
        have hwu : Term.wgt (fun _ => 1) (Term.Let .None .Typ ub)
            = 1 + 1 + Term.wgt (fun _ => 1) ub := _root_.rfl
        have hwlt : Term.wgt (fun _ => 1) (Term.subst 0 .Typ ub)
            < Term.wgt (fun _ => 1) (Term.Let .None .Typ ub) := by
          rw [hwu]
          omega
        obtain ⟨w, uw, Cw, hred, hwc, hwera, hwdeep, hwcg, hwle, _, _⟩ :=
          ihacc (Cb, Term.wgt (fun _ => 1) (Term.subst 0 .Typ ub))
            (MMeas_of_sub_wgt hsubC hwlt) hered hrc hcgsub _root_.rfl
        refine ⟨w, uw, Cw, .step .let_ hred, hwc, hwera, hwdeep, hwcg,
          ?_, fun he => Term.noConfusion he,
          fun hd => hd.value.let_absurd.elim⟩
        exact MLe.trans (MLe_of_sub_wgt hsubC (Nat.le_of_lt hwlt)) hwle
    | Rwt e P f =>
      obtain ⟨x, y, T0, ue, uf, heera, hfera, hcv, hueq⟩ :=
        Era.rwt_inv hβ hera
      subst hueq
      obtain ⟨Ce, Cf, hcge, hcgf, hsubef⟩ :=
        hcg.pair_rwt_inv _root_.rfl _root_.rfl
      have hwu : Term.wgt (fun _ => 1) (Term.Rwt ue .Typ uf)
          = 1 + Term.wgt (fun _ => 1) ue + 1
            + Term.wgt (fun _ => 1) uf := _root_.rfl
      have hsubCe : Sub Ce C :=
        (Sub.append_right Ce Cf).trans hsubef
      have hsubCf : Sub Cf C :=
        (Sub.append_left Cf Ce).trans hsubef
      obtain ⟨ve, uve, Cve, hrede, hvec, hveera, hvedeep, _, _, _, _⟩ :=
        ihacc (Ce, Term.wgt (fun _ => 1) ue)
          (MMeas_of_sub_wgt hsubCe (by rw [hwu]; omega))
          heera hct.1 hcge _root_.rfl
      obtain ⟨πe0, hvechk⟩ := hveera.check_none
      have heq := Check.canon_eql hβ hok hvedeep.value hvechk
        (fun _ _ _ hxeq hk2 => Era.ref_head_body hβ hveera hxeq hk2)
        (Conv.refl _)
      subst heq
      obtain ⟨x', y', T0', hab, hcvE⟩ := Era.rfl_ty_inv hβ hveera
      obtain ⟨hcx, hcy, _⟩ := Conv.eql_inj hcvE
      have hxy : Conv β x y :=
        Conv.trans hβ (Conv.symm hcx) (Conv.trans hβ hab hcy)
      have hfera2 : Era β [] f T uf := by
        refine Era.cnv hfera (Conv.trans hβ ?_ hcv)
        exact Conv.app_cong hβ (Conv.app_cong hβ (Conv.refl _) hxy)
          (Conv.of_red_rev hrede.strong)
      obtain ⟨vf, uvf, Cvf, hredf, hvfc, hvfera, hvfdeep, hvfcg,
          hwlef, _, _⟩ :=
        ihacc (Cf, Term.wgt (fun _ => 1) uf)
          (MMeas_of_sub_wgt hsubCf (by rw [hwu]; omega))
          hfera2 hct.2.2 hcgf _root_.rfl
      refine ⟨vf, uvf, Cvf, ?_, hvfc, hvfera, hvfdeep, hvfcg, ?_,
        fun he => Term.noConfusion he,
        fun hd => hd.value.rwt_absurd.elim⟩
      · exact ((Red.rwt_e_w hrede).trans (.step .rwt .refl)).trans hredf
      · exact MLe.trans
          (MLe_of_sub_wgt hsubCf (by rw [hwu]; omega)) hwlef
    | App f a =>
      by_cases hrefh : ∃ j : Nat, (Term.spine f).1 = .Ref j
      · -- a reference-headed spine: the composite spend
        obtain ⟨j, hj⟩ := hrefh
        have hteq : Term.App f a
            = Term.apps (.Ref j) ((Term.spine f).2 ++ [a]) := by
          rw [Term.apps_snoc, ← hj, Term.apps_spine]
        obtain ⟨Tf, uhead, T', us, hheadera, hspt, hcvT', hueq⟩ :=
          Era.apps_inv hβ hteq hera
        rcases Era.ref_inv hβ hheadera with ⟨d, hk, hbne, hcvd, huheq⟩ |
          ⟨A', hk, h0', hcvd, huheq⟩
        rotate_left
        · obtain ⟨qx, A1, B1, hcall⟩ := hspt.nonempty_all (by simp)
          exact absurd (Conv.trans hβ hcvd hcall) Conv.typ_all
        subst huheq
        subst hueq
        by_cases hns : d.n ≤ ((Term.spine f).2 ++ [a]).length
        case neg =>
          -- underapplied reference spine: a stuck weak value, settled
          -- as-is — the master returns it unchanged
          exact ⟨Term.App f a, Term.apps (.Ref j) us, C, .refl, hct, hera,
            DeepP.stuck hk hj (Or.inl (show
              ((Term.spine f).2 ++ [a]).length < d.n by omega)),
            hcg, MLe.refl _, fun _ => _root_.rfl, fun _ => _root_.rfl⟩
        case pos =>
        obtain ⟨w, uw, Cw, hredw, hwc, hwera, hwdeep, hwcg, hwle⟩ :=
          hdrive j ((Term.spine f).2 ++ [a]) hteq hera hct hcg
            (MLe.refl _) (by
              intro d0 hk0
              rw [hk] at hk0
              injection hk0 with hd0
              rw [← hd0]
              exact hns)
        refine ⟨w, uw, Cw, ?_, hwc, hwera, hwdeep, hwcg, hwle, ?_, ?_⟩
        · exact hredw
        · intro he
          rcases apps_shape us _ _ he with ⟨h1, h2⟩ | ⟨us0, ul, h1, h2⟩
          · exact Term.noConfusion h2.symm
          · exact Term.noConfusion h2.symm
        · intro hd
          exfalso
          cases hd with
          | mk hv _ _ =>
            rcases hv.app_inv with hsf | ⟨k2, d2, hsp2, hk2, hgate⟩
            · exact hsf.head_not_ref j hj
            · have hsp3 : (Term.spine f).1 = .Ref k2 := hsp2
              rw [hj] at hsp3
              injection hsp3 with hjk
              subst hjk
              rw [hk] at hk2
              injection hk2 with hd2
              subst hd2
              rcases hgate with h1 | h1
              · have h2 : ((Term.spine f).2 ++ [a]).length < d.n := h1
                omega
              · exact absurd h1 hbne
          | stuck hk2 hsp2 hgate =>
            rename_i k2 d2
            have hsp3 : (Term.spine f).1 = .Ref k2 := hsp2
            rw [hj] at hsp3
            injection hsp3 with hjk
            subst hjk
            rw [hk] at hk2
            injection hk2 with hd2
            subst hd2
            rcases hgate with h1 | h1
            · have h2 : ((Term.spine f).2 ++ [a]).length < d.n := h1
              omega
            · exact absurd h1 hbne
      · -- an ordinary application: run the function, then interact
        have hnr : ∀ (j : Nat) (xs : List Term),
            Term.App f a ≠ Term.apps (.Ref j) xs := by
          intro j xs he
          have h1 : (Term.spine (Term.App f a)).1 = .Ref j := by
            rw [he, Term.spine_apps (by trivial)]
          exact hrefh ⟨j, h1⟩
        rcases Era.app_inv hβ hera with
          ⟨A, B, uf, ua, hfera, haera, hcvT, hueq⟩ |
          ⟨A, B, uf, πa, hfera, hachk, hcvT, hueq⟩
        · -- live argument
          subst hueq
          obtain ⟨Ca, Cb, hcgf, hcga, hsubab⟩ :=
            hcg.pair_app_inv _root_.rfl _root_.rfl hnr
          have hwu : Term.wgt (fun _ => 1) (Term.App uf ua)
              = 1 + Term.wgt (fun _ => 1) uf
                + Term.wgt (fun _ => 1) ua := _root_.rfl
          have hsubCa : Sub Ca C :=
            (Sub.append_right Ca Cb).trans hsubab
          have hsubCb : Sub Cb C :=
            (Sub.append_left Cb Ca).trans hsubab
          obtain ⟨vf, uvf, Cvf, hredf, hvfc, hvfera, hvfdeep, hvfcg,
              hwlef, hvfcl1, hvfcl2⟩ :=
            ihacc (Ca, Term.wgt (fun _ => 1) uf)
              (MMeas_of_sub_wgt hsubCa (by rw [hwu]; omega))
              hfera hct.1 hcgf _root_.rfl
          have hvalf := hvfdeep.value
          cases hvalf with
          | @stuck k2 d2 args2 hk2 hgate =>
            have happ : Term.App (Term.apps (.Ref k2) args2) a
                = Term.apps (.Ref k2) (args2 ++ [a]) :=
              (Term.apps_append (.Ref k2) args2 [a]).symm
            obtain ⟨Tf2, uhead2, T'2, us2, hheadera2, hspE2, hcvT'2,
                hueq3⟩ :=
              Era.apps_inv hβ (Eq.refl _) hvfera
            subst hueq3
            rcases Era.ref_inv hβ hheadera2 with
              ⟨d2', hk2', hbne2, hcvR2, huh2⟩ | ⟨A', hk2', _, _, _⟩
            rotate_left
            · exact (Book.defn_adt_clash hk2 hk2').elim
            subst huh2
            rw [hk2] at hk2'
            injection hk2' with hd2eq
            subst hd2eq
            have hmleC2 : MLe (Cvf ++ Cb,
                Term.wgt (fun _ => 1)
                  (Term.App (Term.apps (.Ref k2) us2) ua))
                (C, Term.wgt (fun _ => 1) (Term.App uf ua)) := by
              have hfr := MLe.frame_left Cb
                (1 + Term.wgt (fun _ => 1) ua) hwlef
              have he1 : Term.wgt (fun _ => 1) (Term.apps (.Ref k2) us2)
                  + (1 + Term.wgt (fun _ => 1) ua)
                  = Term.wgt (fun _ => 1)
                    (Term.App (Term.apps (.Ref k2) us2) ua) := by
                have hwa : Term.wgt (fun _ => 1)
                    (Term.App (Term.apps (.Ref k2) us2) ua)
                    = 1 + Term.wgt (fun _ => 1) (Term.apps (.Ref k2) us2)
                      + Term.wgt (fun _ => 1) ua := _root_.rfl
                rw [hwa]
                omega
              have he2 : Term.wgt (fun _ => 1) uf
                  + (1 + Term.wgt (fun _ => 1) ua)
                  = 1 + Term.wgt (fun _ => 1) uf
                    + Term.wgt (fun _ => 1) ua := by
                omega
              rw [he1, he2] at hfr
              have hm3' : MLe (Ca ++ Cb, 1 + Term.wgt (fun _ => 1) uf
                  + Term.wgt (fun _ => 1) ua)
                  (C, Term.wgt (fun _ => 1) (Term.App uf ua)) := by
                refine MLe_of_sub_wgt hsubab ?_
                rw [hwu]
                omega
              exact MLe.trans hm3' hfr
            have hdabs : ¬ DeepP β (Term.App f a) (Term.App uf ua) := by
              intro hd
              cases hd with
              | stuck _ hsp9 _ => exact absurd ⟨_, hsp9⟩ hrefh
              | mk hv hlen hp =>
                rcases hv.app_inv with hsf | ⟨k9, _, hsp9, _, _⟩
                · have hdf : DeepP β f uf := by
                    refine .mk (.spine hsf) ?_ ?_
                    · have h3 : ((Term.spine uf).2 ++ [ua]).length
                          = ((Term.spine f).2 ++ [a]).length := hlen
                      simp only [List.length_append, List.length_cons,
                        List.length_nil] at h3
                      omega
                    · intro p hp2 htok
                      refine hp p ?_ htok
                      show p ∈ ((Term.spine f).2 ++ [a]).zip
                        ((Term.spine uf).2 ++ [ua])
                      rw [zip_append_of_len _ _ _ _ (by
                        have h3 : ((Term.spine uf).2 ++ [ua]).length
                            = ((Term.spine f).2 ++ [a]).length := hlen
                        simp only [List.length_append, List.length_cons,
                          List.length_nil] at h3
                        omega)]
                      exact List.mem_append.mpr (Or.inl hp2)
                  have hfeq := hvfcl2 hdf
                  have hfref : (Term.spine f).1 = .Ref k2 := by
                    rw [← hfeq, Term.spine_apps (h := .Ref k2) trivial]
                  exact absurd ⟨k2, hfref⟩ hrefh
                · exact absurd ⟨k9, hsp9⟩ hrefh
            rcases hgate with hlt | hnone
            · by_cases hsat : d2.n ≤ args2.length + 1
              · -- the argument saturates the head: replay the spend
                obtain ⟨w, uw, Cw, hredw, hwc, hwera, hwdeep, hwcg,
                    hwle⟩ :=
                  hdrive k2 (args2 ++ [a]) happ
                    (Era.cnv (Era.app_live hvfera haera) hcvT)
                    ⟨hvfc, hct.2⟩ (CG.app hvfcg hcga) hmleC2 (by
                      intro d0 hk0
                      rw [hk2] at hk0
                      injection hk0 with hd0
                      rw [← hd0]
                      simp only [List.length_append, List.length_cons,
                        List.length_nil]
                      omega)
                refine ⟨w, uw, Cw, ?_, hwc, hwera, hwdeep, hwcg, hwle,
                  fun he => Term.noConfusion he,
                  fun hd => absurd hd hdabs⟩
                exact (Red.app_f_w hredf).trans hredw
              · -- still underapplied: a stuck weak value
                refine ⟨Term.App (Term.apps (.Ref k2) args2) a,
                  Term.App (Term.apps (.Ref k2) us2) ua, Cvf ++ Cb,
                  Red.app_f_w hredf, ⟨hvfc, hct.2⟩,
                  Era.cnv (Era.app_live hvfera haera) hcvT, ?_,
                  CG.app hvfcg hcga, hmleC2,
                  fun he => Term.noConfusion he,
                  fun hd => absurd hd hdabs⟩
                refine DeepP.stuck hk2 ?_ ?_
                · show (Term.spine
                    (Term.App (Term.apps (.Ref k2) args2) a)).1 = .Ref k2
                  rw [happ, Term.spine_apps (h := .Ref k2) trivial]
                · left
                  show (Term.spine
                    (Term.App (Term.apps (.Ref k2) args2) a)).2.length
                      < d2.n
                  rw [happ, Term.spine_apps (h := .Ref k2) trivial]
                  simp only [List.length_append, List.length_cons,
                    List.length_nil]
                  omega
            · exact absurd hnone hbne2
          | typ =>
            obtain ⟨π0, hc0⟩ := hvfera.check_none
            exact absurd (Check.typ_subj_inv hβ hc0).1 Conv.typ_all
          | all =>
            obtain ⟨π0, hc0⟩ := hvfera.check_none
            exact absurd (Check.all_subj_inv hβ hc0).1 Conv.typ_all
          | eql =>
            obtain ⟨π0, hc0⟩ := hvfera.check_none
            exact absurd (Check.eql_subj_inv hβ hc0).1 Conv.typ_all
          | rfl =>
            obtain ⟨π0, hc0⟩ := hvfera.check_none
            obtain ⟨x0, y0, T00, _, hcv0, _⟩ := Check.rfl_inv hβ hc0
            exact absurd hcv0 (fun hc2 => Conv.all_eql (Conv.symm hc2))
          | efq =>
            obtain ⟨π0, hc0⟩ := hvfera.check_none
            obtain ⟨a0, A0, r0, q'0, ps0, B0, hk0, hall0, _, hcv0, _⟩ :=
              Check.efq_ty_inv hβ hc0
            obtain ⟨_, hcA0, _⟩ := Conv.all_inj hcv0
            obtain ⟨va, uva, Cva, hreda, hvac, hvaera, hvadeep, _, _,
                _, _⟩ :=
              ihacc (Cb, Term.wgt (fun _ => 1) ua)
                (MMeas_of_sub_wgt hsubCb (by rw [hwu]; omega))
                haera hct.2 hcga _root_.rfl
            obtain ⟨πa1, hvachk⟩ := hvaera.check_none
            obtain ⟨c1, C1, as1, hvaeq, hC1, hnr2, hlen1⟩ :=
              Check.canon_adt hβ hok hvadeep.value hvachk
                (fun _ _ _ hxeq hk2 => Era.ref_head_body hβ hvaera hxeq hk2)
                hk0 (Conv.symm hcA0)
            exact absurd (hall0 c1 (AdtD.ctr_lt hC1)) hnr2
          | lam =>
            rename_i g
            obtain ⟨q1, A1, B1, ug, hcvL, hbody, hocc, hueq2⟩ :=
              Era.lam_inv hβ hvfera
            obtain ⟨hq1, hcA, hcB⟩ := Conv.all_inj hcvL
            subst hq1
            subst hueq2
            have hocc1 := hocc (by intro hc; cases hc)
            obtain ⟨πa0, hachk0⟩ := haera.check_none
            have hsub := hbody.sub hβ Cut.zero
              (Check.cnv hachk0 (Conv.symm hcA)) (by intro hc; cases hc)
              (Era.cnv haera (Conv.symm hcA)) hct.2 haera.closed_out
            have hered := Era.cnv hsub (Conv.trans hβ
              (Conv.subst hβ hcB (Conv.refl a) 0) hcvT)
            obtain ⟨πr, hrchk⟩ := hered.check_none
            have hrc := hrchk.closed
            obtain ⟨C0, hcg0, hsubC0⟩ :=
              hvfcg.pair_lam_inv _root_.rfl _root_.rfl
            obtain ⟨C', hcgsub, hsubc'⟩ := hcg0.subst_one 0 a ua Cb
              hct.2 haera.closed_out hcga (by
                simp only [Quant.occN] at hocc1
                omega)
            have hocc2 : Term.occ 0 ug * Term.wgt (fun _ => 1) ua
                ≤ Term.wgt (fun _ => 1) ua := by
              have := Nat.mul_le_mul_right
                (Term.wgt (fun _ => 1) ua) hocc1
              simp only [Quant.occN] at this
              omega
            have hws := Term.wgt_subst (fun _ => 1) ug 0 ua
            have hwlam : Term.wgt (fun _ => 1) (Term.Lam ug)
                = 1 + Term.wgt (fun _ => 1) ug := _root_.rfl
            have hm1 : MMeas
                (C', Term.wgt (fun _ => 1) (Term.subst 0 ua ug))
                (Cvf ++ Cb, Term.wgt (fun _ => 1) (Term.Lam ug)
                  + Term.wgt (fun _ => 1) ua) := by
              refine MMeas_of_sub_wgt ?_ ?_
              · exact hsubc'.trans (Sub.append hsubC0 (Sub.refl Cb))
              · rw [hwlam]
                omega
            have hm2 : MLe (Cvf ++ Cb, Term.wgt (fun _ => 1) (Term.Lam ug)
                  + Term.wgt (fun _ => 1) ua)
                (Ca ++ Cb, Term.wgt (fun _ => 1) uf
                  + Term.wgt (fun _ => 1) ua) :=
              MLe.frame_left Cb (Term.wgt (fun _ => 1) ua) hwlef
            have hm3 : MLe (Ca ++ Cb, Term.wgt (fun _ => 1) uf
                  + Term.wgt (fun _ => 1) ua)
                (C, Term.wgt (fun _ => 1) (Term.App uf ua)) := by
              refine MLe_of_sub_wgt hsubab ?_
              rw [hwu]
              omega
            have hmeas : MMeas
                (C', Term.wgt (fun _ => 1) (Term.subst 0 ua ug))
                (C, Term.wgt (fun _ => 1) (Term.App uf ua)) :=
              MMeas.after_le hm3 (MMeas.after_le hm2 hm1)
            obtain ⟨w, uw, Cw, hred, hwc, hwera, hwdeep, hwcg, hwle,
                _, _⟩ :=
              ihacc (C', Term.wgt (fun _ => 1) (Term.subst 0 ua ug))
                hmeas hered hrc hcgsub _root_.rfl
            refine ⟨w, uw, Cw, ?_, hwc, hwera, hwdeep, hwcg, ?_,
              fun he => Term.noConfusion he, ?_⟩
            · exact ((Red.app_f_w hredf).trans
                (.step .beta .refl)).trans hred
            · exact MLe.trans_meas hmeas hwle
            · intro hd
              exfalso
              have hsf : Spinal f := by
                rcases hd.value.app_inv with h1 | ⟨k9, _, hsp9, _, _⟩
                · exact h1
                · exact absurd ⟨k9, hsp9⟩ hrefh
              have hdf : DeepP β f uf := by
                cases hd with
                | stuck _ hsp9 _ => exact absurd ⟨_, hsp9⟩ hrefh
                | mk hv hlen hp =>
                  refine .mk (.spine hsf) ?_ ?_
                  · have h3 : ((Term.spine uf).2 ++ [ua]).length
                        = ((Term.spine f).2 ++ [a]).length := hlen
                    simp only [List.length_append, List.length_cons,
                      List.length_nil] at h3
                    omega
                  · intro p hp2 htok
                    refine hp p ?_ htok
                    show p ∈ ((Term.spine f).2 ++ [a]).zip
                      ((Term.spine uf).2 ++ [ua])
                    rw [zip_append_of_len _ _ _ _ (by
                      have h3 : ((Term.spine uf).2 ++ [ua]).length
                          = ((Term.spine f).2 ++ [a]).length := hlen
                      simp only [List.length_append, List.length_cons,
                        List.length_nil] at h3
                      omega)]
                    exact List.mem_append.mpr (Or.inl hp2)
              have hvfeq := hvfcl2 hdf
              rw [← hvfeq] at hsf
              cases hsf
          | spine hsp =>
            obtain ⟨va, uva, Cva, hreda, hvac, hvaera, hvadeep, hvacg,
                hwlea, hvacl1, hvacl2⟩ :=
              ihacc (Cb, Term.wgt (fun _ => 1) ua)
                (MMeas_of_sub_wgt hsubCb (by rw [hwu]; omega))
                haera hct.2 hcga _root_.rfl
            have hframe : Era β [] (.App vf va) T (.App uvf uva) := by
              refine Era.cnv (.app_live hvfera hvaera) ?_
              refine Conv.trans hβ ?_ hcvT
              exact Conv.subst hβ (Conv.refl B)
                (Conv.of_red_rev hreda.strong) 0
            have hdeepA : DeepP β (.App vf va) (.App uvf uva) := by
              cases hvfdeep with
              | stuck _ hsp9 _ => exact absurd hsp9 (hsp.head_not_ref _)
              | mk _ hlen2 hp2 =>
                refine .mk (.spine (.app hsp)) ?_ ?_
                · show ((Term.spine uvf).2 ++ [uva]).length
                    = ((Term.spine vf).2 ++ [va]).length
                  simp only [List.length_append, List.length_cons,
                    List.length_nil]
                  omega
                · show ∀ p ∈ ((Term.spine vf).2 ++ [va]).zip
                      ((Term.spine uvf).2 ++ [uva]),
                    p.2 ≠ .Typ → DeepP β p.1 p.2
                  intro p hp3 htok
                  rw [zip_append_of_len _ _ _ _ (by omega)] at hp3
                  rcases List.mem_append.mp hp3 with h5 | h6
                  · exact hp2 p h5 htok
                  · simp only [List.zip_cons_cons, List.zip_nil_right,
                      List.mem_singleton] at h6
                    subst h6
                    exact hvadeep
            have hchain1 : MLe
                (Cvf ++ Cva, Term.wgt (fun _ => 1) uvf
                  + Term.wgt (fun _ => 1) uva)
                (Ca ++ Cb, Term.wgt (fun _ => 1) uf
                  + Term.wgt (fun _ => 1) ua) :=
              MLe.trans
                (MLe.frame_left Cb (Term.wgt (fun _ => 1) ua) hwlef)
                (MLe.frame Cvf (Term.wgt (fun _ => 1) uvf) hwlea)
            have hchain2 := MLe.frame [] 1 hchain1
            rw [show 1 + (Term.wgt (fun _ => 1) uvf
                + Term.wgt (fun _ => 1) uva)
              = 1 + Term.wgt (fun _ => 1) uvf
                + Term.wgt (fun _ => 1) uva from by omega,
              show 1 + (Term.wgt (fun _ => 1) uf
                + Term.wgt (fun _ => 1) ua)
              = 1 + Term.wgt (fun _ => 1) uf
                + Term.wgt (fun _ => 1) ua from by omega] at hchain2
            refine ⟨.App vf va, .App uvf uva, Cvf ++ Cva, ?_,
              ⟨hvfc, hvac⟩, hframe, hdeepA, .app hvfcg hvacg, ?_,
              fun he => Term.noConfusion he, ?_⟩
            · exact (Red.app_f_w hredf).trans (Red.app_a_w hreda)
            · exact MLe.trans (MLe_of_sub_wgt hsubab (by
                rw [hwu]
                omega)) hchain2
            · intro hd
              have hsf : Spinal f := by
                rcases hd.value.app_inv with h1 | ⟨k9, _, hsp9, _, _⟩
                · exact h1
                · exact absurd ⟨k9, hsp9⟩ hrefh
              have hlen0 : (Term.spine uf).2.length
                  = (Term.spine f).2.length := by
                cases hd with
                | stuck _ hsp9 _ => exact absurd ⟨_, hsp9⟩ hrefh
                | mk _ hlen hp =>
                  have h3 : ((Term.spine uf).2 ++ [ua]).length
                      = ((Term.spine f).2 ++ [a]).length := hlen
                  simp only [List.length_append, List.length_cons,
                    List.length_nil] at h3
                  omega
              have hdf : DeepP β f uf := by
                cases hd with
                | stuck _ hsp9 _ => exact absurd ⟨_, hsp9⟩ hrefh
                | mk hv hlen hp =>
                  refine .mk (.spine hsf) hlen0 ?_
                  intro p hp2 htok
                  refine hp p ?_ htok
                  show p ∈ ((Term.spine f).2 ++ [a]).zip
                    ((Term.spine uf).2 ++ [ua])
                  rw [zip_append_of_len _ _ _ _ (by omega)]
                  exact List.mem_append.mpr (Or.inl hp2)
              have hpa : ua ≠ .Typ → DeepP β a ua := by
                cases hd with
                | stuck _ hsp9 _ => exact absurd ⟨_, hsp9⟩ hrefh
                | mk hv hlen hp =>
                  intro htok
                  refine hp (a, ua) ?_ htok
                  show (a, ua) ∈ ((Term.spine f).2 ++ [a]).zip
                    ((Term.spine uf).2 ++ [ua])
                  rw [zip_append_of_len _ _ _ _ (by omega)]
                  refine List.mem_append.mpr (Or.inr ?_)
                  simp
              have hvfeq := hvfcl2 hdf
              have hvaeq : va = a := by
                by_cases htok : ua = .Typ
                · exact hvacl1 htok
                · exact hvacl2 (hpa htok)
              rw [hvfeq, hvaeq]
          | mat =>
            rename_i am cm hh mm
            obtain ⟨A0, C0, r0, ps0, telF, B0, G0, q'0, umh, umm, hk0,
              hc00, hr0, hlen0, hlive0, hins0, hgoal0, hmh, hmm2, hcvM,
              hueqM⟩ := Era.mat_inv hβ hvfera
            obtain ⟨hq0, hcA2, hcB2⟩ := Conv.all_inj hcvM
            subst hq0
            subst hueqM
            obtain ⟨Ch, Cm, hcgh, hcgm, hsubh, hsubm⟩ :=
              hvfcg.pair_mat_inv _root_.rfl _root_.rfl
            obtain ⟨va, uva, Cva, hreda, hvac, hvaera, hvadeep, hvacg,
                hwlea, hvacl1, hvacl2⟩ :=
              ihacc (Cb, Term.wgt (fun _ => 1) ua)
                (MMeas_of_sub_wgt hsubCb (by rw [hwu]; omega))
                haera hct.2 hcga _root_.rfl
            obtain ⟨πa1, hvachk⟩ := hvaera.check_none
            obtain ⟨c1, C1, as1, hvaeq, hC1, hnr1, hlen1⟩ :=
              Check.canon_adt hβ hok hvadeep.value hvachk
                (fun _ _ _ hxeq hk2 => Era.ref_head_body hβ hvaera hxeq hk2)
                hk0 (Conv.symm hcA2)
            subst hvaeq
            obtain ⟨Tf, uhead, T', us, hheadera, hsp0, hcvT', hueq3⟩ :=
              Era.apps_inv hβ (Eq.refl _) hvaera
            subst hueq3
            obtain ⟨A1, C1', rr0, hA1, hC1', hrr0, hcty, huhead⟩ :=
              Era.ctr_head_inv hβ hheadera
            subst huhead
            rw [hk0] at hA1
            cases hA1
            rw [hC1] at hC1'
            cases hC1'
            have hshape := ((hok.adt_clauses hk0).2.2 c1 C1 hC1).2
            have hw := WTele.retip rr0 hshape
            obtain ⟨πsp, hspc⟩ := hsp0.chk
            rcases ChkSpine.wtele_walk hβ hspc hw hcty with
              ⟨_, qA, AA, BB, hcAll⟩ | ⟨hlenAs, hcadt⟩
            · exact absurd (Conv.trans hβ hcAll
                (Conv.trans hβ hcvT' (Conv.symm hcA2))) Conv.all_adt
            · have hchainC : Conv β
                  (Term.apps (.Adt am rr0) ([] ++ as1.take A0.pn))
                  (Term.apps (.Adt am r0) ps0) :=
                Conv.trans hβ hcadt (Conv.trans hβ hcvT' (Conv.symm hcA2))
              obtain ⟨_, hrr, hconvs⟩ := Conv.adt_inj hchainC
              subst hrr
              simp only [List.nil_append] at hconvs
              obtain ⟨ps1, xs1, hsplit, hlenp1, hlenx1⟩ :
                  ∃ ps1 xs1, as1 = ps1 ++ xs1 ∧ ps1.length = A0.pn ∧
                    xs1.length = C1.fn := by
                refine ⟨as1.take A0.pn, as1.drop A0.pn,
                  (List.take_append_drop _ _).symm, ?_, ?_⟩
                · rw [List.length_take]
                  omega
                · rw [List.length_drop]
                  omega
              subst hsplit
              have htake : (ps1 ++ xs1).take A0.pn = ps1 := by
                rw [← hlenp1]
                exact take_append ps1 xs1
              rw [htake] at hconvs
              have hwmat : Term.wgt (fun _ => 1) (Term.Mat am cm umh umm)
                  = 1 + Nat.max (Term.wgt (fun _ => 1) umh)
                    (Term.wgt (fun _ => 1) umm) := _root_.rfl
              have hmaxl : Term.wgt (fun _ => 1) umh
                  ≤ Nat.max (Term.wgt (fun _ => 1) umh)
                    (Term.wgt (fun _ => 1) umm) := Nat.le_max_left _ _
              have hmaxr : Term.wgt (fun _ => 1) umm
                  ≤ Nat.max (Term.wgt (fun _ => 1) umh)
                    (Term.wgt (fun _ => 1) umm) := Nat.le_max_right _ _
              have hdclause : DeepP β (Term.App f a) (.App uf ua) →
                  False := by
                intro hd
                have hsf : Spinal f := by
                  rcases hd.value.app_inv with h1 | ⟨k9, _, hsp9, _, _⟩
                  · exact h1
                  · exact absurd ⟨k9, hsp9⟩ hrefh
                have hlen00 : (Term.spine uf).2.length
                    = (Term.spine f).2.length := by
                  cases hd with
                  | stuck _ hsp9 _ => exact absurd ⟨_, hsp9⟩ hrefh
                  | mk _ hlen hp =>
                    have h3 : ((Term.spine uf).2 ++ [ua]).length
                        = ((Term.spine f).2 ++ [a]).length := hlen
                    simp only [List.length_append, List.length_cons,
                      List.length_nil] at h3
                    omega
                have hdf : DeepP β f uf := by
                  cases hd with
                  | stuck _ hsp9 _ => exact absurd ⟨_, hsp9⟩ hrefh
                  | mk hv hlen hp =>
                    refine .mk (.spine hsf) hlen00 ?_
                    intro p hp2 htok
                    refine hp p ?_ htok
                    show p ∈ ((Term.spine f).2 ++ [a]).zip
                      ((Term.spine uf).2 ++ [ua])
                    rw [zip_append_of_len _ _ _ _ (by omega)]
                    exact List.mem_append.mpr (Or.inl hp2)
                have hvfeq := hvfcl2 hdf
                rw [← hvfeq] at hsf
                cases hsf
              by_cases hcc : c1 = cm
              · subst hcc
                rw [hc00] at hC1
                injection hC1 with hCC
                subst hCC
                have hchain0 := hsp0.retipS hβ hw hcty hlenAs []
                rw [WTele.retip_retip hshape [] rr0,
                  WTele.retip_self hshape] at hchain0
                obtain ⟨Tmid, us1, us2, hsp1, hsp2, husplit⟩ :=
                  EraSpine.append_split hchain0
                subst husplit
                obtain ⟨π1c, hsp1c⟩ := hsp1.chk
                obtain ⟨Tinst, hinsts, hcvmid, hFsh⟩ :=
                  ChkSpine.insts_mid hβ hsp1c hshape (Conv.refl _) hlenp1
                have hcvTel : Conv β Tinst telF :=
                  Insts.conv hβ hinsts hins0 (Conv.refl _) hconvs
                have hGchain := MatGoal.erebuild hβ C0.fn hgoal0 hsp2
                  (Conv.trans hβ (Conv.symm hcvTel) hcvmid) hlenx1
                have hredera := hGchain.era hmh
                have hscra : Conv β
                    (Term.apps (.Ctr am c1) (ps0 ++ xs1)) a := by
                  refine Conv.trans hβ ?_
                    (Conv.symm (Conv.of_red hreda.strong))
                  exact Conv.apps_cong hβ (Conv.refl _)
                    (Convs.append (Convs.symm hconvs) (Convs.refl xs1))
                have herfin : Era β [] (Term.apps hh xs1) T
                    (Term.apps umh us2) := by
                  refine Era.cnv hredera (Conv.trans hβ ?_ hcvT)
                  rw [← Term.apps_append]
                  exact Conv.subst hβ hcB2 hscra 0
                obtain ⟨πrr, hrchk⟩ := herfin.check_none
                have hrc := hrchk.closed
                obtain ⟨Css1, hlenc1, hpair1, hsubc1⟩ :=
                  hvacg.ctr_spine_inv _root_.rfl _root_.rfl
                    (by
                      have := hsp0.lengths
                      simp only [List.length_append] at this ⊢
                      omega)
                have hl1s := hsp1.lengths
                have hl2s := hsp2.lengths
                have hpairxs : ∀ p ∈ ((Css1.drop A0.pn).zip xs1).zip us2,
                    CG β p.1.1 p.1.2 p.2 := by
                  intro p hp2
                  refine hpair1 p ?_
                  have hz1 : Css1.zip (ps1 ++ xs1)
                      = (Css1.take A0.pn).zip ps1
                        ++ (Css1.drop A0.pn).zip xs1 := by
                    rw [← zip_append_of_len (Css1.take A0.pn) ps1
                      (Css1.drop A0.pn) xs1 (by
                        simp only [List.length_take, List.length_append]
                          at hlenc1 ⊢
                        omega)]
                    rw [List.take_append_drop]
                  rw [hz1, zip_append_of_len _ us1 _ us2 (by
                    simp only [List.length_zip, List.length_take,
                      List.length_append] at hlenc1 ⊢
                    omega)]
                  exact List.mem_append.mpr (Or.inr hp2)
                have hcgfired : CG β (Ch ++ (Css1.drop A0.pn).flatten)
                    (Term.apps hh xs1) (Term.apps umh us2) :=
                  CG.apps_build hcgh (by
                    simp only [List.length_drop, List.length_append]
                      at hlenc1 ⊢
                    omega) hpairxs (by omega)
                have hsubfired : Sub (Ch ++ (Css1.drop A0.pn).flatten)
                    (Cvf ++ Cva) := by
                  refine Sub.append (hsubh) ?_
                  refine Sub.trans ?_ hsubc1
                  refine Sub.perm_right (Sub.append_left _
                    (Css1.take A0.pn).flatten) ?_
                  rw [← List.flatten_append, List.take_append_drop]
                have hwae : Term.wgt (fun _ => 1) (Term.apps
                    (.Ctr am c1) (us1 ++ us2))
                    = 1 + ((us1 ++ us2).map (Term.wgt (fun _ => 1))).sum
                      + (us1 ++ us2).length := by
                  rw [Term.wgt_apps]
                  rfl
                have hwfe : Term.wgt (fun _ => 1) (Term.apps umh us2)
                    = Term.wgt (fun _ => 1) umh
                      + (us2.map (Term.wgt (fun _ => 1))).sum
                      + us2.length := Term.wgt_apps _ us2 umh
                have hm1 : MMeas
                    (Ch ++ (Css1.drop A0.pn).flatten,
                      Term.wgt (fun _ => 1) (Term.apps umh us2))
                    (Cvf ++ Cva,
                      Term.wgt (fun _ => 1) (Term.Mat am c1 umh umm)
                        + Term.wgt (fun _ => 1)
                            (Term.apps (.Ctr am c1) (us1 ++ us2))) := by
                  refine MMeas_of_sub_wgt hsubfired ?_
                  rw [hwfe, hwmat, hwae]
                  simp only [List.map_append, List.sum_append,
                    List.length_append]
                  omega
                have hm2 : MLe
                    (Cvf ++ Cva,
                      Term.wgt (fun _ => 1) (Term.Mat am c1 umh umm)
                        + Term.wgt (fun _ => 1)
                            (Term.apps (.Ctr am c1) (us1 ++ us2)))
                    (Ca ++ Cb, Term.wgt (fun _ => 1) uf
                      + Term.wgt (fun _ => 1) ua) :=
                  MLe.trans
                    (MLe.frame_left Cb (Term.wgt (fun _ => 1) ua) hwlef)
                    (MLe.frame Cvf
                      (Term.wgt (fun _ => 1) (Term.Mat am c1 umh umm))
                      hwlea)
                have hm3 : MLe
                    (Ca ++ Cb, Term.wgt (fun _ => 1) uf
                      + Term.wgt (fun _ => 1) ua)
                    (C, Term.wgt (fun _ => 1) (Term.App uf ua)) := by
                  refine MLe_of_sub_wgt hsubab ?_
                  rw [hwu]
                  omega
                have hmeasBig : MMeas
                    (Ch ++ (Css1.drop A0.pn).flatten,
                      Term.wgt (fun _ => 1) (Term.apps umh us2))
                    (C, Term.wgt (fun _ => 1) (Term.App uf ua)) :=
                  MMeas.after_le hm3 (MMeas.after_le hm2 hm1)
                obtain ⟨w, uw, Cw, hred, hwc, hwera, hwdeep, hwcg,
                    hwle, _, _⟩ :=
                  ihacc (Ch ++ (Css1.drop A0.pn).flatten,
                      Term.wgt (fun _ => 1) (Term.apps umh us2))
                    hmeasBig herfin hrc hcgfired _root_.rfl
                refine ⟨w, uw, Cw, ?_, hwc, hwera, hwdeep, hwcg, ?_,
                  fun he => Term.noConfusion he,
                  fun hd => absurd hd hdclause⟩
                · exact (Red.app_f_w hredf).trans
                    ((Red.app_a_w hreda).trans
                      ((Red.one (Step.matc hk0 hc00 hlenp1 hlenx1)).trans
                        hred))
                · exact MLe.trans_meas hmeasBig hwle
              · have hchain2 := hsp0.retipS hβ hw hcty hlenAs (cm :: rr0)
                rw [WTele.retip_retip hshape (cm :: rr0) rr0] at hchain2
                simp only [List.nil_append] at hchain2
                rw [htake] at hchain2
                have hheadty : Era β [] (.Ctr am c1)
                    (Term.retip (cm :: rr0) (A0.pn + C1.fn) C1.ty)
                    (.Ctr am c1) := by
                  refine Era.ctr hk0 hC1 ?_
                  intro hmem
                  rcases List.mem_cons.mp hmem with h1 | h1
                  · exact hcc h1
                  · exact hrr0 h1
                have hscrut := hchain2.era hheadty
                have hscrut2 : Era β []
                    (Term.apps (.Ctr am c1) (ps1 ++ xs1))
                    (Term.apps (.Adt am (cm :: rr0)) ps0)
                    (Term.apps (.Ctr am c1) us) :=
                  Era.cnv hscrut
                    (Conv.apps_cong hβ (Conv.refl _) hconvs)
                have hredera : Era β []
                    (.App mm (Term.apps (.Ctr am c1) (ps1 ++ xs1))) T
                    (.App umm (Term.apps (.Ctr am c1) us)) := by
                  refine Era.cnv (Era.app_live hmm2 hscrut2)
                    (Conv.trans hβ ?_ hcvT)
                  exact Conv.subst hβ hcB2
                    (Conv.symm (Conv.of_red hreda.strong)) 0
                obtain ⟨πrr, hrchk⟩ := hredera.check_none
                have hrc := hrchk.closed
                have hcgnext : CG β (Cm ++ Cva)
                    (.App mm (Term.apps (.Ctr am c1) (ps1 ++ xs1)))
                    (.App umm (Term.apps (.Ctr am c1) us)) :=
                  .app hcgm hvacg
                have hwapp : Term.wgt (fun _ => 1)
                    (Term.App umm (Term.apps (.Ctr am c1) us))
                    = 1 + Term.wgt (fun _ => 1) umm
                      + Term.wgt (fun _ => 1)
                          (Term.apps (.Ctr am c1) us) := _root_.rfl
                have hm1 : MMeas
                    (Cm ++ Cva, Term.wgt (fun _ => 1)
                      (Term.App umm (Term.apps (.Ctr am c1) us)))
                    (Cvf ++ Cva,
                      1 + (Term.wgt (fun _ => 1) (Term.Mat am cm umh umm)
                        + Term.wgt (fun _ => 1)
                            (Term.apps (.Ctr am c1) us))) := by
                  refine MMeas_of_sub_wgt
                    (Sub.append hsubm (Sub.refl Cva)) ?_
                  show Term.wgt (fun _ => 1)
                      (Term.App umm (Term.apps (.Ctr am c1) us))
                    < 1 + (Term.wgt (fun _ => 1) (Term.Mat am cm umh umm)
                      + Term.wgt (fun _ => 1) (Term.apps (.Ctr am c1) us))
                  rw [hwapp, hwmat]
                  omega
                have hm2 : MLe
                    (Cvf ++ Cva,
                      1 + (Term.wgt (fun _ => 1) (Term.Mat am cm umh umm)
                        + Term.wgt (fun _ => 1)
                            (Term.apps (.Ctr am c1) us)))
                    (Ca ++ Cb, 1 + (Term.wgt (fun _ => 1) uf
                      + Term.wgt (fun _ => 1) ua)) :=
                  MLe.frame [] 1 (MLe.trans
                    (MLe.frame_left Cb (Term.wgt (fun _ => 1) ua) hwlef)
                    (MLe.frame Cvf
                      (Term.wgt (fun _ => 1) (Term.Mat am cm umh umm))
                      hwlea))
                have hm3 : MLe
                    (Ca ++ Cb, 1 + (Term.wgt (fun _ => 1) uf
                      + Term.wgt (fun _ => 1) ua))
                    (C, Term.wgt (fun _ => 1) (Term.App uf ua)) := by
                  refine MLe_of_sub_wgt hsubab ?_
                  rw [hwu]
                  omega
                have hmeasBig : MMeas
                    (Cm ++ Cva, Term.wgt (fun _ => 1)
                      (Term.App umm (Term.apps (.Ctr am c1) us)))
                    (C, Term.wgt (fun _ => 1) (Term.App uf ua)) :=
                  MMeas.after_le hm3 (MMeas.after_le hm2 hm1)
                obtain ⟨w, uw, Cw, hred, hwc, hwera, hwdeep, hwcg,
                    hwle, _, _⟩ :=
                  ihacc (Cm ++ Cva, Term.wgt (fun _ => 1)
                      (Term.App umm (Term.apps (.Ctr am c1) us)))
                    hmeasBig hredera hrc hcgnext _root_.rfl
                refine ⟨w, uw, Cw, ?_, hwc, hwera, hwdeep, hwcg, ?_,
                  fun he => Term.noConfusion he,
                  fun hd => absurd hd hdclause⟩
                · refine (Red.app_f_w hredf).trans
                    ((Red.app_a_w hreda).trans
                      ((Red.one (Step.matm ?_)).trans hred))
                  exact fun hpair => hcc (congrArg Prod.snd hpair)
                · exact MLe.trans_meas hmeasBig hwle
        · -- dead argument
          subst hueq
          obtain ⟨Ca, Cb, hcgf, hcga, hsubab⟩ :=
            hcg.pair_app_inv _root_.rfl _root_.rfl hnr
          have hwu : Term.wgt (fun _ => 1) (Term.App uf .Typ)
              = 1 + Term.wgt (fun _ => 1) uf + 1 := _root_.rfl
          have hsubCa : Sub Ca C :=
            (Sub.append_right Ca Cb).trans hsubab
          obtain ⟨vf, uvf, Cvf, hredf, hvfc, hvfera, hvfdeep, hvfcg,
              hwlef, hvfcl1, hvfcl2⟩ :=
            ihacc (Ca, Term.wgt (fun _ => 1) uf)
              (MMeas_of_sub_wgt hsubCa (by rw [hwu]; omega))
              hfera hct.1 hcgf _root_.rfl
          have hdclause : DeepP β (Term.App f a) (.App uf .Typ) →
              vf = f := by
            intro hd
            have hsf : Spinal f := by
              rcases hd.value.app_inv with h1 | ⟨k9, _, hsp9, _, _⟩
              · exact h1
              · exact absurd ⟨k9, hsp9⟩ hrefh
            have hlen00 : (Term.spine uf).2.length
                = (Term.spine f).2.length := by
              cases hd with
              | stuck _ hsp9 _ => exact absurd ⟨_, hsp9⟩ hrefh
              | mk _ hlen hp =>
                have h3 : ((Term.spine uf).2 ++ [Term.Typ]).length
                    = ((Term.spine f).2 ++ [a]).length := hlen
                simp only [List.length_append, List.length_cons,
                  List.length_nil] at h3
                omega
            have hdf : DeepP β f uf := by
              cases hd with
              | stuck _ hsp9 _ => exact absurd ⟨_, hsp9⟩ hrefh
              | mk hv hlen hp =>
                refine .mk (.spine hsf) hlen00 ?_
                intro p hp2 htok
                refine hp p ?_ htok
                show p ∈ ((Term.spine f).2 ++ [a]).zip
                  ((Term.spine uf).2 ++ [Term.Typ])
                rw [zip_append_of_len _ _ _ _ (by omega)]
                exact List.mem_append.mpr (Or.inl hp2)
            exact hvfcl2 hdf
          have hvalf := hvfdeep.value
          cases hvalf with
          | @stuck k2 d2 args2 hk2 hgate =>
            have happ : Term.App (Term.apps (.Ref k2) args2) a
                = Term.apps (.Ref k2) (args2 ++ [a]) :=
              (Term.apps_append (.Ref k2) args2 [a]).symm
            obtain ⟨Tf2, uhead2, T'2, us2, hheadera2, hspE2, hcvT'2,
                hueq3⟩ :=
              Era.apps_inv hβ (Eq.refl _) hvfera
            subst hueq3
            rcases Era.ref_inv hβ hheadera2 with
              ⟨d2', hk2', hbne2, hcvR2, huh2⟩ | ⟨A', hk2', _, _, _⟩
            rotate_left
            · exact (Book.defn_adt_clash hk2 hk2').elim
            subst huh2
            rw [hk2] at hk2'
            injection hk2' with hd2eq
            subst hd2eq
            have hmleC2 : MLe (Cvf ++ Cb,
                Term.wgt (fun _ => 1)
                  (Term.App (Term.apps (.Ref k2) us2) Term.Typ))
                (C, Term.wgt (fun _ => 1) (Term.App uf Term.Typ)) := by
              have hfr := MLe.frame_left Cb (1 + 1) hwlef
              have he1 : Term.wgt (fun _ => 1) (Term.apps (.Ref k2) us2)
                  + (1 + 1)
                  = Term.wgt (fun _ => 1)
                    (Term.App (Term.apps (.Ref k2) us2) Term.Typ) := by
                have hwa : Term.wgt (fun _ => 1)
                    (Term.App (Term.apps (.Ref k2) us2) Term.Typ)
                    = 1 + Term.wgt (fun _ => 1) (Term.apps (.Ref k2) us2)
                      + 1 := _root_.rfl
                rw [hwa]
                omega
              have he2 : Term.wgt (fun _ => 1) uf + (1 + 1)
                  = 1 + Term.wgt (fun _ => 1) uf + 1 := by
                omega
              rw [he1, he2] at hfr
              have hm3' : MLe (Ca ++ Cb,
                  1 + Term.wgt (fun _ => 1) uf + 1)
                  (C, Term.wgt (fun _ => 1) (Term.App uf Term.Typ)) := by
                refine MLe_of_sub_wgt hsubab ?_
                rw [hwu]
                omega
              exact MLe.trans hm3' hfr
            have hdabs : ¬ DeepP β (Term.App f a)
                (Term.App uf Term.Typ) := by
              intro hd
              have hfeq := hdclause hd
              have hfref : (Term.spine f).1 = .Ref k2 := by
                rw [← hfeq, Term.spine_apps (h := .Ref k2) trivial]
              exact absurd ⟨k2, hfref⟩ hrefh
            rcases hgate with hlt | hnone
            · by_cases hsat : d2.n ≤ args2.length + 1
              · -- the argument saturates the head: replay the spend
                obtain ⟨w, uw, Cw, hredw, hwc, hwera, hwdeep, hwcg,
                    hwle⟩ :=
                  hdrive k2 (args2 ++ [a]) happ
                    (Era.cnv (Era.app_dead hvfera hachk) hcvT)
                    ⟨hvfc, hct.2⟩ (CG.app hvfcg hcga) hmleC2 (by
                      intro d0 hk0
                      rw [hk2] at hk0
                      injection hk0 with hd0
                      rw [← hd0]
                      simp only [List.length_append, List.length_cons,
                        List.length_nil]
                      omega)
                refine ⟨w, uw, Cw, ?_, hwc, hwera, hwdeep, hwcg, hwle,
                  fun he => Term.noConfusion he,
                  fun hd => absurd hd hdabs⟩
                exact (Red.app_f_w hredf).trans hredw
              · -- still underapplied: a stuck weak value
                refine ⟨Term.App (Term.apps (.Ref k2) args2) a,
                  Term.App (Term.apps (.Ref k2) us2) Term.Typ, Cvf ++ Cb,
                  Red.app_f_w hredf, ⟨hvfc, hct.2⟩,
                  Era.cnv (Era.app_dead hvfera hachk) hcvT, ?_,
                  CG.app hvfcg hcga, hmleC2,
                  fun he => Term.noConfusion he,
                  fun hd => absurd hd hdabs⟩
                refine DeepP.stuck hk2 ?_ ?_
                · show (Term.spine
                    (Term.App (Term.apps (.Ref k2) args2) a)).1 = .Ref k2
                  rw [happ, Term.spine_apps (h := .Ref k2) trivial]
                · left
                  show (Term.spine
                    (Term.App (Term.apps (.Ref k2) args2) a)).2.length
                      < d2.n
                  rw [happ, Term.spine_apps (h := .Ref k2) trivial]
                  simp only [List.length_append, List.length_cons,
                    List.length_nil]
                  omega
            · exact absurd hnone hbne2
          | typ =>
            obtain ⟨π0, hc0⟩ := hvfera.check_none
            exact absurd (Check.typ_subj_inv hβ hc0).1 Conv.typ_all
          | all =>
            obtain ⟨π0, hc0⟩ := hvfera.check_none
            exact absurd (Check.all_subj_inv hβ hc0).1 Conv.typ_all
          | eql =>
            obtain ⟨π0, hc0⟩ := hvfera.check_none
            exact absurd (Check.eql_subj_inv hβ hc0).1 Conv.typ_all
          | rfl =>
            obtain ⟨π0, hc0⟩ := hvfera.check_none
            obtain ⟨x0, y0, T00, _, hcv0, _⟩ := Check.rfl_inv hβ hc0
            exact absurd hcv0 (fun hc2 => Conv.all_eql (Conv.symm hc2))
          | efq =>
            obtain ⟨a0, A0, r0, q'0, ps0, B0, hk0, hall0, hlive0,
              hcv0, _⟩ := Era.efq_ty_inv hβ hvfera
            obtain ⟨hq0, _, _⟩ := Conv.all_inj hcv0
            exact absurd hq0 hlive0
          | mat =>
            obtain ⟨A0, C0, r0, ps0, telF, B0, G0, q'0, umh, umm, hk0,
              hc00, hr0, hlen0, hlive0, hins0, hgoal0, hmh, hmm2, hcvM,
              hueqM⟩ := Era.mat_inv hβ hvfera
            obtain ⟨hq0, _, _⟩ := Conv.all_inj hcvM
            exact absurd hq0 hlive0
          | lam =>
            rename_i g
            obtain ⟨q1, A1, B1, ug, hcvL, hbody, hocc, hueq2⟩ :=
              Era.lam_inv hβ hvfera
            obtain ⟨hq1, hcA, hcB⟩ := Conv.all_inj hcvL
            subst hq1
            subst hueq2
            have hocc0 : Term.occ 0 ug = 0 := by
              have := hocc (by intro hc; cases hc)
              simp only [Quant.occN] at this
              omega
            have hsub := hbody.sub_dead hβ Cut.zero
              (Check.cnv hachk (Conv.symm hcA)) hct.2 hocc0
            have hered := Era.cnv hsub (Conv.trans hβ
              (Conv.subst hβ hcB (Conv.refl a) 0) hcvT)
            obtain ⟨πr, hrchk⟩ := hered.check_none
            have hrc := hrchk.closed
            obtain ⟨C0, hcg0, hsubC0⟩ :=
              hvfcg.pair_lam_inv _root_.rfl _root_.rfl
            have hcgsub := hcg0.subst_zero 0 a .Typ hct.2
              (by trivial) hocc0
            have hws := Term.wgt_subst (fun _ => 1) ug 0 .Typ
            rw [hocc0] at hws
            have hwlam : Term.wgt (fun _ => 1) (Term.Lam ug)
                = 1 + Term.wgt (fun _ => 1) ug := _root_.rfl
            have hm1 : MMeas
                (C0, Term.wgt (fun _ => 1) (Term.subst 0 .Typ ug))
                (Cvf ++ Cb, Term.wgt (fun _ => 1) (Term.Lam ug) + 1) := by
              refine MMeas_of_sub_wgt ?_ ?_
              · exact (Sub.append_right C0 Cb).trans
                  (Sub.append hsubC0 (Sub.refl Cb))
              · rw [hwlam]
                omega
            have hm2 : MLe
                (Cvf ++ Cb, Term.wgt (fun _ => 1) (Term.Lam ug) + 1)
                (Ca ++ Cb, Term.wgt (fun _ => 1) uf + 1) :=
              MLe.frame_left Cb 1 hwlef
            have hm3 : MLe (Ca ++ Cb, Term.wgt (fun _ => 1) uf + 1)
                (C, Term.wgt (fun _ => 1) (Term.App uf .Typ)) := by
              refine MLe_of_sub_wgt hsubab ?_
              rw [hwu]
              omega
            have hmeas : MMeas
                (C0, Term.wgt (fun _ => 1) (Term.subst 0 .Typ ug))
                (C, Term.wgt (fun _ => 1) (Term.App uf .Typ)) :=
              MMeas.after_le hm3 (MMeas.after_le hm2 hm1)
            obtain ⟨w, uw, Cw, hred, hwc, hwera, hwdeep, hwcg, hwle,
                _, _⟩ :=
              ihacc (C0, Term.wgt (fun _ => 1) (Term.subst 0 .Typ ug))
                hmeas hered hrc hcgsub _root_.rfl
            refine ⟨w, uw, Cw, ?_, hwc, hwera, hwdeep, hwcg, ?_,
              fun he => Term.noConfusion he, ?_⟩
            · exact ((Red.app_f_w hredf).trans
                (.step .beta .refl)).trans hred
            · exact MLe.trans_meas hmeas hwle
            · intro hd
              have := hdclause hd
              exfalso
              have hsf : Spinal f := by
                rcases hd.value.app_inv with h1 | ⟨k9, _, hsp9, _, _⟩
                · exact h1
                · exact absurd ⟨k9, hsp9⟩ hrefh
              rw [← this] at hsf
              cases hsf
          | spine hsp =>
            have hframe : Era β [] (.App vf a) T (.App uvf .Typ) :=
              Era.cnv (.app_dead hvfera hachk) hcvT
            have hdeepA : DeepP β (.App vf a) (.App uvf .Typ) := by
              cases hvfdeep with
              | stuck _ hsp9 _ => exact absurd hsp9 (hsp.head_not_ref _)
              | mk _ hlen2 hp2 =>
                refine .mk (.spine (.app hsp)) ?_ ?_
                · show ((Term.spine uvf).2 ++ [Term.Typ]).length
                    = ((Term.spine vf).2 ++ [a]).length
                  simp only [List.length_append, List.length_cons,
                    List.length_nil]
                  omega
                · show ∀ p ∈ ((Term.spine vf).2 ++ [a]).zip
                      ((Term.spine uvf).2 ++ [Term.Typ]),
                    p.2 ≠ .Typ → DeepP β p.1 p.2
                  intro p hp3 htok
                  rw [zip_append_of_len _ _ _ _ (by omega)] at hp3
                  rcases List.mem_append.mp hp3 with h5 | h6
                  · exact hp2 p h5 htok
                  · simp only [List.zip_cons_cons, List.zip_nil_right,
                      List.mem_singleton] at h6
                    subst h6
                    exact absurd _root_.rfl htok
            have hchain1 : MLe
                (Cvf ++ Cb, Term.wgt (fun _ => 1) uvf + 1)
                (Ca ++ Cb, Term.wgt (fun _ => 1) uf + 1) :=
              MLe.frame_left Cb 1 hwlef
            have hchain2 := MLe.frame [] 1 hchain1
            rw [show 1 + (Term.wgt (fun _ => 1) uvf + 1)
              = 1 + Term.wgt (fun _ => 1) uvf + 1 from by omega,
              show 1 + (Term.wgt (fun _ => 1) uf + 1)
              = 1 + Term.wgt (fun _ => 1) uf + 1 from by omega] at hchain2
            refine ⟨.App vf a, .App uvf .Typ, Cvf ++ Cb, ?_,
              ⟨hvfc, hct.2⟩, hframe, hdeepA, .app hvfcg hcga, ?_,
              fun he => Term.noConfusion he, ?_⟩
            · exact Red.app_f_w hredf
            · exact MLe.trans (MLe_of_sub_wgt hsubab (by
                rw [hwu]
                omega)) hchain2
            · intro hd
              rw [hdclause hd]

-- The engine runs any live-checked closed term to a value inside the
-- erased-weight budget; preservation carries the typing to the value;
-- canonical forms then forbid any value of an empty family. The full
-- recursive claims need the descent charge on top of this engine.
-- ============================================================================

theorem normalization_plain (β : Book) (t T : Term) (π : Uses)
    (hok : Book.Ok β) (hplain : Book.Plain β)
    (h : Check β .Lone [] t T π) :
    ∃ v π', Red β .weak t v ∧ Term.Value β v ∧ Check β .Lone [] v T π' := by
  obtain ⟨u, hera, _, _⟩ := h.era _root_.rfl
  obtain ⟨v, uv, hred, hval, hvc, hvera, _⟩ :=
    engine hok hplain (Term.wgt (Book.price β) u) hera h.closed
      (Nat.le_refl _)
  obtain ⟨π', hle, hv⟩ :=
    Check.preservation_red hok (by intro hc; cases hc) h hred
  exact ⟨v, π', hred, hval, hv⟩

theorem consistency_plain (β : Book) (a : Nat) (A : AdtD) (r : List Nat)
    (ps : List Term) (t : Term) (π : Uses)
    (hok : Book.Ok β) (hplain : Book.Plain β)
    (hA : Book.adt β a = some A) (hctrs : A.ctrs = []) :
    ¬ Check β .Lone [] t (Term.apps (.Adt a r) ps) π := by
  intro h
  obtain ⟨v, π', hred, hval, hv⟩ :=
    normalization_plain β t (Term.apps (.Adt a r) ps) π hok hplain h
  obtain ⟨c, C, as, hveq, hC, _, _⟩ :=
    Check.canon_adt hok.closed hok hval hv
      (fun _ _ args2 hxeq hk2 =>
        Check.ref_head_body hok.closed args2.length args2 (Nat.le_refl _)
          (hxeq ▸ hv) (fun hq0 => Quant.noConfusion hq0) hk2)
      hA (Conv.refl _)
  have := AdtD.ctr_lt hC
  rw [hctrs] at this
  simp at this


-- ============================================================================
-- CLAIMS 4 and 5 — over ANY Ok book, recursive definitions included:
-- every live-checked closed term runs weakly to a value, and an empty
-- family has no closed inhabitant. The master engine pays interactions
-- with the erasure weight and reference spends with the charge
-- multiset, well-founded by Dershowitz-Manna over the descent order.
-- ============================================================================

theorem normalization_holds : normalization := by
  intro β t T π hok h
  obtain ⟨u, hera, _, _⟩ := h.era _root_.rfl
  obtain ⟨C, hcg⟩ := hera.cg
  obtain ⟨v, uv, Cv, hred, hvc, hvera, hvdeep, _, _, _, _⟩ :=
    master hok.closed hok (C, Term.wgt (fun _ => 1) u)
      (MMeas.wf.apply _) hera h.closed hcg _root_.rfl
  obtain ⟨π', hle, hv⟩ :=
    Check.preservation_red hok (by intro hc; cases hc) h hred
  exact ⟨v, π', hred, hvdeep.value, hv⟩

theorem consistency_holds : consistency := by
  intro β a A r ps t π hok hA hctrs h
  obtain ⟨v, π', hred, hval, hv⟩ :=
    normalization_holds β t (Term.apps (.Adt a r) ps) π hok h
  obtain ⟨c, C, as, hveq, hC, _, _⟩ :=
    Check.canon_adt hok.closed hok hval hv
      (fun _ _ args2 hxeq hk2 =>
        Check.ref_head_body hok.closed args2.length args2 (Nat.le_refl _)
          (hxeq ▸ hv) (fun hq0 => Quant.noConfusion hq0) hk2)
      hA (Conv.refl _)
  have := AdtD.ctr_lt hC
  rw [hctrs] at this
  simp at this

end BendCore
