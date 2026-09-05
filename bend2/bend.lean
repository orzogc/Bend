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
-- BEND-CORE — the bend2 calculus, as bend.ts implements it
-- ============================================================================
--
-- A model of the Bend core: the language (bend.ts's Types through Valid),
-- its reduction, typing, descent and validation, and the five claims the
-- bend.ts header trusts. PART I is the SPEC — the part a human must read.
-- PART II is the metatheory proving the claims.
--
-- THE HEADLINE. A dependent calculus with Type : Type, impredicativity and
-- negative recursive types, made consistent not by a universe hierarchy or a
-- positivity check but by a usage wall. Two checking demands, None (dead)
-- and Lone (live); binders graded None, Lone or Many; a Many binder forms
-- only at a Data type, and no function type is Data. So a live function
-- value is consumed at most once: self-replicating lambdas (omega, Curry,
-- Hurkens) contract a live function-valued binding and do not type. The
-- other way to loop is recursion, and every live self-call descends on a
-- strict subterm of the definition's own case-tree columns. Dead code is
-- specification, not proof: it may diverge and may inhabit Empty, and the
-- claims are stated for the live fragment only.
--
-- THE MAP. Part I mirrors bend.ts's core, section by section:
--
--   bend.ts section    | here          | contents
--   -------------------|---------------|------------------------------------
--   Types              | §1 Types      | Quant, Uses, Term, Bind, Ctx, DefD,
--                      |               | CtrD, AdtD, TLD, Book, LHS
--   Quant              | §2 Quant      | add, join, mul, le, dem
--   Uses               | §3 Uses       | zero, one, add, join, tail
--   Term, LHS          | §4 Term       | apps/spine, shift, subst, Closed,
--                      |               | the J motive, the lhs algebra
--   Ctx, Ctrs, Book    | §5 Ctx/Book   | get, δ (let expansion), tld, adt,
--                      |               | defn, ctr, LHS walks
--   Compare (descend)  | §6 Descent    | PEq/PLt (EQ/LT verdicts), SpineLt
--   Tele               | §7 Tele       | telescope shapes and openings
--   WNF, SNF, Compare  | §8 Equal      | Step/Red (wnf/snf), Value, Conv
--                      |               | (compare EQ), Le (compare LE)
--   Check              | §9 Check      | the one judgment: infer and check,
--                      |               | with the descent test at infer-ref
--   Valid              | §10 Valid     | Book.Ok (book_valid)
--   (header claims)    | §11 Claims    | the five claims as Props
--
-- THE ENCODING. Terms are de Bruijn and first-order; bend.ts's binder ids
-- and HOAS bodies are its way of being capture-free, and a de Bruijn index
-- is the same fact. Its Ann is inference's only help and has no rule here:
-- {x : T} is x checked at T, which the declarative judgment can always do
-- (cnv). Its Hol is ?TODO, which marks a book incomplete, and its Sub is a
-- flattener node: neither reaches a checked book. Its n-ary ADT and Ctr
-- nodes are application spines headed by Adt a r and Ctr a c, always full
-- in a parsed book; a constructor spine carries the family's parameters
-- as erased leading arguments (check-ctr reads them off the goal, and the
-- elaborated node records them in its Ann). Its parallel let x y = a b; f
-- is nested Lets, each value checked in the outer scope. The surface
-- syntax (match, case, do, the sugars) desugars and flattens into this
-- core at parse time; the flattener's output is a tree of Lam, Mat and
-- Efq over the definition's columns, in binder order (Tree, §10), and
-- check-mat's column peel is sound only for such a body, so Book.Ok
-- states the shape def_valid trusts.
--
-- LETS ARE TRANSPARENT. A let binds x with its value: the checker types x
-- from the context and counts its uses, while reduction, conversion and
-- descent step through x to the value (bend.ts's Var carries v). Here a
-- Bind carries the optional value, and Ctx.δ expands every let-bound
-- variable in a term (§5); every comparison the judgment makes (cnv, rfl,
-- the descent test) compares δ-expanded terms. Reduction itself is
-- context-free: a closed let fires by substitution.
--
-- THE MODEL ACCEPTS EVERY BOOK bend.ts ACCEPTS with a clean verdict, and
-- some more. The extra permissions are harmless for the claims, which are
-- negative, and are listed here so nobody reads the model as the checker:
--   (a) the judgment is declarative: a term may be checked at any type
--       that its inferred type fits (cnv anywhere), where bend.ts converts
--       only at check-any, rfl and rwt, and normalizes goals by wnf;
--   (b) a family or constructor head may be applied to fewer arguments
--       than its arity, where bend.ts spells only full nodes;
--   (c) a residual family Adt a r may be written anywhere, where bend.ts
--       mints residuals only in match goals;
--   (d) an unused let value is not charged (its variable is never used,
--       so its measure is dropped by the rule), where bend.ts adds it;
--   (e) (x => f)(a) types by the app rule too when the lambda is typed,
--       where bend.ts takes one beta step first (both are here);
--   (f) check-efq reads a binding's type up to conversion, where bend.ts
--       reads its weak head normal form (the same verdict on every type
--       bend.ts normalizes; conversion is what a let value's reduction
--       preserves, which subject reduction under a let needs).
-- Two premises the declarative form needs that bend.ts gets for free from
-- its pipeline: check-lam kinds the binder's domain at the binder's
-- quantity (bend.ts kinded it when the arrow was formed, and every goal
-- it meets was formed), and a constructor head's parameter binders are
-- erased (a bend.ts value never carries them). Each keeps a Many binder
-- from ever copying a function: what the Data layer's soundness rests on.
-- THE MODEL REFUSES one thing bend.ts accepts: a book with an @unsafe
-- def or a surviving ?TODO. bend.ts reports both in its verdict, and the
-- claims are for clean verdicts. Every other bend.ts permission is a
-- rule below.
-- TWO HYPOTHESES beyond Book.Ok enter claims (2), (4) and (5):
--   Wall: no live call runs ahead in fill order. A user def cannot make
--       one (a live reference needs a filled or native target), but a
--       base def may live-call a base law filled later — the b flag —
--       and base.bend does, in seventeen helper pairs (a helper calls
--       the pending law that calls it back). The checker tests descent
--       on self-calls only, so those cycles are trusted by inspection,
--       like the natives; the model says so by naming the hypothesis.
--   Filled: no definition is bodiless. A stuck native is a value the
--       machine never opens, so a native of an emptied type would void
--       the dead arm of a match (preservation fails there), and a native
--       at Void{e: Empty} is an inconsistency outright. So the claims
--       speak of the book with its natives filled; Book.Native (every
--       native admits a filling that validates: a constant does for
--       base's F32, U32, Bool, String, Maybe and IO natives) carries
--       consistency back to the shipped book (consistency_natives),
--       since a filling only grows typing.
--
-- NOT MODELED. Char, PMap, the number sections, Show, Parse, Flatten,
-- imports and the error window are pipeline and presentation concerns.
-- Literals are base.bend constructors, not calculus.
--
-- QUANTITIES. None | Lone | Many, spelled -x, x, +x.
--   add  (sequential): None + q = q; two live uses saturate to Many
--   join (branches):   pointwise max
--   mul  (fields):     a match field binds at field times scrutinee
--   dem  (arguments):  an erased binder kills the demand, else the
--                      ambient demand passes, unscaled (certify-once)
-- A demand is None or Lone, never Many. An argument to a q binder checks
-- at dem q qt and its measure adds once: a Lone Data value may enter a
-- Many binder, let or field, and the callee copies it. A binder's
-- measured use must not exceed its declared quantity on close.
--
-- KINDS. Every type has a kind Kind(g) over a quantity term g: Type is
-- Kind(&1), Data is Kind(&2); a function type is Type, an equation is
-- Data, a family declares Kind(G) over its parameters. A binder q x: A
-- checks A against Kind(q). Le orders kinds by the quantity: Kind(g) fits
-- Kind(h) when h <= g, &0 and &1 one rung, so Data fits every kind, every
-- kind fits Type, a meet fits a kind under both sides, a kind fits a meet
-- under either, and a stuck quantity licenses nothing. The meet a <&> b is
-- the minimum, reduced only when forced (§8).
--
-- REDUCTION (§8), one rule set read at two strengths: STRONG may enter
-- any subterm (conversion's reach), WEAK never enters a binder (the
-- machine's reach: Lam body, Let body, All codomain, Kind argument).
--   beta  ((λ f) a)                      → f[0 := a]
--   let   (let q v; b)                   → b[0 := v]
--   dref  @k·as, |as| = arity, filled    → book[k].body·as      (== wnf)
--   drefS @k·as, STRONG only             → book[k].body·as      (any arity)
--   eta   λ(F 0), STRONG, 0 ∉ F          → F                    (functions)
--   aref  @a, a nullary family           → Adt a []
--   matc  (Mat a c h m) (Ctr a c)·ps·xs  → h·xs                 (|xs| = fn)
--   matm  (Mat a c h m) (Ctr a' c')·as   → m ((Ctr a' c')·as)   (c' ≠ c)
--   rwt   (Rwt {==} P f)                 → f
--   min   &2 <&> b → b, &0 <&> b → &0, a <&> &2 → a, a <&> &0 → &0,
--         &1 <&> &1 → &1; a stuck side keeps the meet stuck
-- Values are weak-head: type formers, quantities, function values, stuck
-- meets and rewrites, Adt/Ctr-headed spines, and stuck reference spines
-- (a parameterized family head, an underapplied or bodiless definition).
-- Conv is joinability of strong runs (compare EQ); Le is Conv made
-- directional at kinds, at ADT residuals (peeling more fits peeling
-- fewer) and at function domains, which compare swapped (compare LE).
--
-- TYPING (§9). One judgment, Check β Φ L sp q Γ t T π u: under the
-- equation L and the pending spine sp, at demand q, t has type T
-- consuming π and elaborates to u, the certified term with its dead
-- parts erased to the token Quant (bend.ts answers the elaborated term;
-- comp.ts erases exactly these parts). Φ names the judgment's two tests,
-- conversion (Le) and ex-falso (CtxDead): Pol.std, bend.ts's; PART II
-- also reads the rules under a coarser pair for dead code. Every rule is
-- bend.ts's rule of the same name, spelled as its derivation comment.
-- The var rule charges the ambient demand; a type position, an erased
-- argument, a kind's quantity, an equality endpoint and a motive check
-- dead; no rule coerces dead to live. A live reference to a
-- definition with no body needs the native flag; a live self-reference
-- must head a call whose pending spine descends against the equation's
-- columns (infer-ref), the equation being the def's own left-hand side
-- rebuilt as the walk binds a Lam column or peels a Mat column into a
-- constructor of fresh fields (check-lam, check-mat). Dead code carries
-- no descent obligation at all, which is what lets a negative recursive
-- type be defined. A live match consumes a live scrutinee; the empty
-- match accepts when no constructor remains or a LIVE binding in scope
-- has an emptied type (check-efq).
--
-- THE CLAIMS (§11), over any Ok book:
-- (1) confluence of strong reduction; (3) progress at live demand; and,
-- with the wall up and the natives filled, (2) subject reduction along
-- weak steps of closed live terms (dead code preserves nothing: a dead
-- arm may inhabit Empty); (4) weak normalization of closed live terms;
-- (5) consistency: no closed live term inhabits an emptied family.
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
  | Ref : Nat → Term                          -- @k (a definition or a family)
  | Typ : Term → Term                         -- Kind(g); Type = Typ (Qua Lone)
  | Qnt : Term                                -- Quant
  | Qua : Quant → Term                        -- &0 &1 &2
  | Min : Term → Term → Term                  -- a <&> b
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

-- a definition: n case-tree columns, their quantities, a closed type, an
-- optional closed body, and the native flag (base's b flag, or a foreign
-- fill): a native is live-usable without a body
structure DefD : Type where
  n    : Nat
  qs   : List Quant
  ty   : Term
  body : Option Term
  b    : Bool
deriving DecidableEq

-- a constructor: field count and closed telescope type (the family's pn
-- parameters, then fn fields, tipped at the family applied to its own
-- parameters — parse_adt builds exactly this shape)
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

-- the book, in fill order: a law sits at its fill, a native that is never
-- filled at its declaration
abbrev Book := List TLD

-- a context binding: quantity, type, and the value of a let binder
structure Bind : Type where
  q : Quant
  T : Term
  v : Option Term
deriving DecidableEq

abbrev Ctx := List Bind

-- the equation of the definition under check (bend.ts LHS): the def's
-- index, its left-hand side rebuilt as the walk binds columns, the
-- columns still to bind, the parameter quantities, and the wall flag:
-- whether a live call to a pending native must also point backward
-- (bend.ts never demands it; the claims that need termination do)
structure LHS : Type where
  k  : Nat
  t  : Term
  n  : Nat
  qs : List Quant
  w  : Bool
deriving DecidableEq

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

-- a match field binds at field times scrutinee: a + field under a Lone
-- holder is Many (bend.ts quant_mul)
def Quant.mul : Quant → Quant → Quant
  | .None, _ => .None
  | .Lone, x => x
  | .Many, x => Quant.add x x

def Quant.le : Quant → Quant → Prop
  | .None, _     => True
  | .Lone, .None => False
  | .Lone, _     => True
  | .Many, .Many => True
  | .Many, _     => False

-- the demand on an argument: an erased binder kills the demand, any other
-- binder passes the ambient demand through (bend.ts quant_dem)
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

-- ============================================================================
-- §4 Term (== bend.ts Term: apply/unapply, shift, subst, the lhs algebra)
-- ============================================================================

def Term.apps : Term → List Term → Term
  | f, []      => f
  | f, a :: as => Term.apps (.App f a) as

-- a term is a head (never an App) — spine decompositions are unique
def Term.IsHead : Term → Prop
  | .App _ _ => False
  | _        => True

-- the spine decomposition: t = apps (spine t).1 (spine t).2 with a
-- non-App head (bend.ts term_unapply)
def Term.spine : Term → Term × List Term
  | .App f a => ((Term.spine f).1, (Term.spine f).2 ++ [a])
  | t        => (t, [])

def Term.shift (d : Nat) : Term → Term
  | .Var i         => if i < d then .Var i else .Var (i + 1)
  | .Ref k         => .Ref k
  | .Typ g         => .Typ (Term.shift d g)
  | .Qnt           => .Qnt
  | .Qua q         => .Qua q
  | .Min a b       => .Min (Term.shift d a) (Term.shift d b)
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
  | .Typ g         => .Typ (Term.subst d w g)
  | .Qnt           => .Qnt
  | .Qua q         => .Qua q
  | .Min a b       => .Min (Term.subst d w a) (Term.subst d w b)
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
  | n, .Typ g         => g.Closed n
  | _, .Qnt           => True
  | _, .Qua _         => True
  | n, .Min a b       => a.Closed n ∧ b.Closed n
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

def Term.shiftN : Nat → Term → Term
  | 0,     t => t
  | n + 1, t => Term.shift 0 (Term.shiftN n t)

-- the J motive's type: over an equation {a == b : T}, the motive binds
-- the second endpoint and the equation itself (bend.ts check-rwt's p_typ)
def Term.jmotive (a T : Term) : Term :=
  .All .Lone T (.All .Lone (.Eql (Term.shift 0 a) (.Var 0) (Term.shift 0 T))
    (.Typ (.Qua .Lone)))

-- the left-hand-side algebra (bend.ts term_apply and lhs_ext): applying
-- a lambda equation beta-reduces it, and a peeled column becomes the
-- constructor of fn fresh fields, bound by fn lambdas
def Term.applyB : Term → Term → Term
  | .Lam f, a => Term.subst 0 a f
  | f,      a => .App f a

def Term.occ (d : Nat) : Term → Nat
  | .Var i         => if i = d then 1 else 0
  | .Ref _         => 0
  | .Typ g         => Term.occ d g
  | .Qnt           => 0
  | .Qua _         => 0
  | .Min a b       => Term.occ d a + Term.occ d b
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

-- the erasure wrapper: a dead check leaves the token, a live one its term
def Term.era : Quant → Term → Term
  | .None, _ => .Qnt
  | _,     u => u

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
-- §5 Ctx and Book (== bend.ts Ctx, Ctrs, Book, LHS)
-- ============================================================================

def Bind.shift (b : Bind) : Bind :=
  { b with T := Term.shift 0 b.T, v := b.v.map (Term.shift 0) }

def Ctx.get : Ctx → Nat → Option Bind
  | [], _         => none
  | b :: _, 0     => some b.shift
  | _ :: Γ, i + 1 => (Ctx.get Γ i).map Bind.shift

-- the let expansion of a context (bend.ts's Var.v, followed by wnf,
-- compare and descend): every let-bound variable is replaced by its
-- value, innermost binder first. d counts the term's own binders above
-- the context; a binder without a value joins them and stays rigid, so
-- the result mentions rigid binders only, renumbered alike on every term
-- the judgment compares
def Ctx.δ : Ctx → Nat → Term → Term
  | [], _, t => t
  | b :: Γ, d, t =>
    match b.v with
    | some v => Ctx.δ Γ d (Term.subst d (Term.shiftN d v) t)
    | none   => Ctx.δ Γ (d + 1) t

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

-- a family with the peeled set r has no constructor left (bend.ts
-- book_adt's filtered list is empty)
def Book.empty (β : Book) (a : Nat) (r : List Nat) : Prop :=
  ∃ A, Book.adt β a = some A ∧ ∀ c, c < A.ctrs.length → c ∈ r

-- the equation's walks: entering any binder shifts it; a Lam binds the
-- next column while one remains (check-lam); a Mat peels the next column
-- into a constructor of fn fresh fields (check-mat); the columns are the
-- arguments of its spine (lhs_descend)
def LHS.shift (L : LHS) : LHS := { L with t := Term.shift 0 L.t }

def LHS.lam (L : LHS) : LHS :=
  if L.n = 0 then L.shift
  else { L with t := Term.applyB (Term.shift 0 L.t) (.Var 0), n := L.n - 1 }

def LHS.mat (L : LHS) (a c fn : Nat) : LHS :=
  if L.n = 0 then L
  else { L with t := Term.lhsExt L.t a c fn, n := L.n - 1 + fn }

def LHS.cols (L : LHS) : List Term := (Term.spine L.t).2

-- the equation of no definition: the index past the book, so no reference
-- is a self-reference and every backward reference is allowed (the claims
-- are stated under it; a def body checks under its own)
def LHS.void (β : Book) : LHS := ⟨β.length, .Ref β.length, 0, [], false⟩

-- ============================================================================
-- §6 Descent (== bend.ts term_descend and lhs_descend: EQ columns then
-- one strict subterm, erased columns skipped)
-- ============================================================================

-- PEq β t p: argument t matches column pattern p exactly. A pattern is a
-- variable or a constructor of patterns (fields only, built by the walk);
-- a constructor argument carries its erased parameters, which the
-- comparison skips. Both pin their field-list arity to the declared C.fn:
-- bend.ts constructor nodes are n-ary and always full.
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
-- constructor with pointwise <= fields, at least one strict, or <= some
-- field of p (bend.ts term_descend's LT verdicts)
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

-- SpineLt β qs j cols args: from column j on, live columns compare EQ left
-- to right until one is a strict subterm; an erased column is skipped
-- (lhs_descend; a missing quantity counts live)
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

-- WTele a r ps pn fn T: T is a telescope of pn more parameter binders,
-- each of its own quantity, then fn field binders, tipped at the family
-- applied to the parameters (those already instantiated in ps, then the
-- pn to come) — parse_adt's one telescope per constructor
def WTele (a : Nat) (r : List Nat) : List Term → Nat → Nat → Term → Prop
  | ps, 0,      fn, T => FTele a r ps fn T
  | ps, pn + 1, fn, T => ∃ q K B, T = .All q K B ∧
      WTele a r (ps.map (Term.shift 0) ++ [.Var 0]) pn fn B

-- the constructor telescope shape
def CtrD.Shape (a pn : Nat) (C : CtrD) : Prop :=
  WTele a [] [] pn C.fn C.ty

-- Insts T ps T': T' is the telescope T with its first |ps| binders
-- instantiated at ps (bend.ts tele_fill of a constructor's parameters
-- with the goal's)
inductive Insts : Term → List Term → Term → Prop
  | nil  : Insts T [] T
  | cons : Insts (Term.subst 0 p B) ps T' →
           Insts (.All q A B) (p :: ps) T'

-- ============================================================================
-- §8 Equal (== bend.ts WNF/SNF/Compare: reduction at two strengths;
-- conversion is joinability of strong runs, eta included; Le adds the
-- directional cases of compare LE)
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
  | minLM : Step β p (.Min (.Qua .Many) b) b
  | minLN : Step β p (.Min (.Qua .None) b) (.Qua .None)
  | minRM : Step β p (.Min a (.Qua .Many)) a
  | minRN : Step β p (.Min a (.Qua .None)) (.Qua .None)
  | minLL : Step β p (.Min (.Qua .Lone) (.Qua .Lone)) (.Qua .Lone)
  | eta   : p = .strong → Term.occ 0 F = 0 →
            Step β p (.Lam (.App F (.Var 0))) (Term.subst 0 .Qnt F)
  | typ_g : p = .strong → Step β p g g' → Step β p (.Typ g) (.Typ g')
  | min_a : Step β p a a' → Step β p (.Min a b) (.Min a' b)
  | min_b : Step β p b b' → Step β p (.Min a b) (.Min a b')
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

-- compare EQ: joinability of strong runs
def Conv (β : Book) (a b : Term) : Prop :=
  ∃ c, Red β .strong a c ∧ Red β .strong b c

-- the kind order (compare LE at Typ): Kind(g) fits Kind(h) when g is &2,
-- or h is a literal under &2, or a meet on the left fits under both
-- sides, or a meet on the right fits under either, or the quantities
-- convert; a stuck quantity fits only itself
inductive KLe (β : Book) : Term → Term → Prop
  | many : Red β .strong g (.Qua .Many) → KLe β g h
  | lone : Red β .strong h (.Qua q) → q ≠ .Many → KLe β g h
  | minL : Red β .strong g (.Min g1 g2) → KLe β g1 h → KLe β g2 h → KLe β g h
  | minR1 : Red β .strong h (.Min h1 h2) → KLe β g h1 → KLe β g h
  | minR2 : Red β .strong h (.Min h1 h2) → KLe β g h2 → KLe β g h
  | conv : Conv β g h → KLe β g h

-- compare LE: a fits b. Conv everywhere, except that a kind is ordered by
-- KLe, a family with more constructors peeled fits one with fewer, and a
-- function type compares its domains swapped and its codomains along;
-- every part that flows both ways compares EQ
inductive Le (β : Book) : Term → Term → Prop
  | conv : Conv β a b → Le β a b
  | red  : Red β .strong a a' → Red β .strong b b' → Le β a' b' → Le β a b
  | typ  : KLe β g h → Le β (.Typ g) (.Typ h)
  | all  : Le β A' A → Le β B B' → Le β (.All q A B) (.All q A' B')
  | adt  : (∀ c, c ∈ r' → c ∈ r) → ps.length = ps'.length →
           (∀ (i : Nat) p p', ps[i]? = some p → ps'[i]? = some p' → Conv β p p') →
           Le β (Term.apps (.Adt a r) ps) (Term.apps (.Adt a r') ps')

-- weak-head values (bend.ts term_wnf's break-focus forms): a head that
-- no weak rule fires on, applied to any spine. A reference is stuck
-- when it is a parameterized family, or a definition kept closed by its
-- arity gate or by a missing body; a match is stuck on a scrutinee that
-- is a value but no constructor
inductive Term.Value (β : Book) : Term → Prop
  | var  : Term.Value β (Term.apps (.Var i) as)
  | typ  : Term.Value β (Term.apps (.Typ g) as)
  | qnt  : Term.Value β (Term.apps .Qnt as)
  | qua  : Term.Value β (Term.apps (.Qua q) as)
  | all  : Term.Value β (Term.apps (.All q A B) as)
  | lam  : Term.Value β (.Lam f)
  | mat  : Term.Value β (.Mat a c h m)
  | efq  : Term.Value β (Term.apps .Efq as)
  | eql  : Term.Value β (Term.apps (.Eql a b T) as)
  | rfl  : Term.Value β (Term.apps .Rfl as)
  | adt  : Term.Value β (Term.apps (.Adt a r) as)
  | ctr  : Term.Value β (Term.apps (.Ctr a c) as)
  | fam  : Book.adt β k = some A → 0 < A.pn →
           Term.Value β (Term.apps (.Ref k) as)
  | ref  : Book.defn β k = some d →
           as.length < d.n ∨ d.body = none →
           Term.Value β (Term.apps (.Ref k) as)
  | min  : Term.Value β a → a ≠ .Qua .Many → a ≠ .Qua .None →
           Term.Value β b → b ≠ .Qua .Many → b ≠ .Qua .None →
           ¬ (a = .Qua .Lone ∧ b = .Qua .Lone) →
           Term.Value β (Term.apps (.Min a b) as)
  | rwt  : Term.Value β e → e ≠ .Rfl →
           Term.Value β (Term.apps (.Rwt e P f) as)
  | matS : Term.Value β x → (∀ a' c' xs, x ≠ Term.apps (.Ctr a' c') xs) →
           Term.Value β (Term.apps (.Mat a c h m) (x :: as))

-- ============================================================================
-- §9 Check (== bend.ts Check: one bidirectional judgment, with the
-- descent test of infer-ref and the lhs threading of check-lam/check-mat)
-- ============================================================================

-- MatGoal q' n B s tel G: G is the goal for a match arm handling a
-- constructor with n fields — the instantiated field telescope tel, each
-- field's quantity multiplied by the scrutinee's q', tipped at the motive
-- B applied to the constructor spine s rebuilt from the fields
-- (bend.ts term_check_mat_goal)
inductive MatGoal (q' : Quant) : Nat → Term → Term → Term → Term → Prop
  | zero : MatGoal q' 0 B s tel (Term.subst 0 s B)
  | succ : MatGoal q' n (Term.shift 1 B) (.App (Term.shift 0 s) (.Var 0)) Bf G →
           MatGoal q' (n + 1) B s (.All qf F Bf) (.All (Quant.mul qf q') F G)

-- retip r pn n ty: the type of a constructor head, from its declared
-- telescope of pn parameters and n - pn fields: the parameter binders
-- are erased (a value never carries its family's parameters — bend.ts
-- check-ctr reads them off the goal and checks only the fields), and the
-- Adt at the tip is reannotated with the peeled set r. A constructor
-- checks against the REMAINDER of its family (ctrs_find over book_adt's
-- filtered constructors): its head type here carries any peeled set that
-- does not contain it, which is what lets a mismatched scrutinee re-check
-- at the peeled domain of a match's tail
def Term.retip (r : List Nat) : Nat → Nat → Term → Term
  | 0, 0, t =>
    match (Term.spine t).1 with
    | .Adt a _ => Term.apps (.Adt a r) (Term.spine t).2
    | _        => t
  | pn + 1, n + 1, .All _ A B => .All .None A (Term.retip r pn n B)
  | 0, n + 1, .All q A B => .All q A (Term.retip r 0 n B)
  | _, _, t => t

-- CtxDead β Γ: some LIVE binding in scope has an emptied datatype, so the
-- region is unreachable (bend.ts ctx_dead, up to conversion: permission
-- (f); an erased binding proves nothing, since dead code inhabits Empty)
def CtxDead (β : Book) (Γ : Ctx) : Prop :=
  ∃ i b a r ps, Ctx.get Γ i = some b ∧ b.q ≠ .None ∧
    Conv β (Ctx.δ Γ 0 b.T) (Term.apps (.Adt a r) ps) ∧ Book.empty β a r

-- the judgment's two tests, as parameters: its conversion (compare LE)
-- and its ex-falso test (ctx_dead). bend.ts's are Le and CtxDead; the
-- metatheory also reads the same rules under a coarser conversion when it
-- reasons about dead code (PART II §K), where quantities are moot
structure Pol : Type where
  conv : Term → Term → Prop
  efq  : Ctx → Prop

def Pol.std (β : Book) : Pol := ⟨Le β, CtxDead β⟩

-- Check β Φ L sp q Γ t T π u: under the equation L and the pending spine
-- sp (the arguments above t, infer-app's sp), at demand q, t has type T
-- consuming π, and elaborates to u: the certified term with every part
-- checked dead replaced by the token Quant (what the compiler runs;
-- bend.ts's Infer/Check answer tm, the same term with its dead parts kept
-- for printing). Demands are None and Lone only in any derivation rooted
-- at Book.Ok; Many is a measure value. A None-demand derivation measures
-- only None and elaborates to the token, and the rule that checks a
-- premise dead drops its measure from the conclusion, as in bend.ts.
inductive Check (β : Book) (Φ : Pol) : LHS → List Term → Quant → Ctx → Term → Term → Uses → Term → Prop
  -- Γ[i] = q' A
  -- ------------------------- infer-var
  -- Γ ⊢ x_i : A ~ {i : q}
  | var : Ctx.get Γ i = some b →
          Check β Φ L sp q Γ (.Var i) b.T (Uses.one i q) (Term.era q (.Var i))
  -- β[j] = def(T, v)
  -- where a live j is filled or native; a filled one precedes the def
  --       under check in fill order (it was filled when the body was
  --       checked), a native may be pending — base's one way to build a
  --       live cycle — unless the wall flag is up
  --       a live self-reference (j = L.k) descends: its pending spine sp
  --       compares against L's columns, both let-expanded (lhs_descend)
  -- --------------------------------------------------------- infer-ref
  -- Γ ⊢ @j : T ~ {}
  | ref : Book.defn β j = some d →
          (q ≠ .None → d.body ≠ none ∨ d.b = true) →
          (q ≠ .None → L.w = true ∨ d.b = false → j ≤ L.k) →
          (q ≠ .None → j = L.k →
            SpineLt β L.qs 0 (L.cols.map (Ctx.δ Γ 0)) (sp.map (Ctx.δ Γ 0))) →
          Check β Φ L sp q Γ (.Ref j) d.ty Uses.zero (Term.era q (.Ref j))
  -- β[k] = adt(sig, cs), nullary: the one bare-head spelling (a
  -- parameterized family head is an error: D<..> is the one spelling)
  -- --------------------------------------------------------- infer-ref (adt)
  -- Γ ⊢ @k : sig ~ {}
  | refA : Book.adt β k = some A → A.pn = 0 →
           Check β Φ L sp q Γ (.Ref k) A.sig Uses.zero (Term.era q (.Ref k))
  -- β[a] = adt(sig, cs)
  -- ------------------------- infer-adt (head; the parameters apply)
  -- Γ ⊢ Adt a r : sig ~ {}
  | adt : Book.adt β a = some A →
          Check β Φ L sp q Γ (.Adt a r) A.sig Uses.zero (Term.era q (.Adt a r))
  -- β[a].cs[c] = ctr(T)    c not peeled by r
  -- ----------------------------------------- check-ctr (head; the erased
  -- Γ ⊢ Ctr a c : retip r T ~ {}                parameters and the fields apply)
  | ctr : Book.adt β a = some A → AdtD.ctr A c = some C → c ∉ r →
          Check β Φ L sp q Γ (.Ctr a c) (Term.retip r A.pn (A.pn + C.fn) C.ty) Uses.zero
            (Term.era q (.Ctr a c))
  -- Γ ⊢ g : Quant    (dead)
  -- ------------------------- infer-typ
  -- Γ ⊢ Kind(g) : Type ~ {}
  | typ : Check β Φ L [] .None Γ g .Qnt πg .Qnt →
          Check β Φ L sp q Γ (.Typ g) (.Typ (.Qua .Lone)) Uses.zero
            (Term.era q (.Typ .Qnt))
  -- ------------------------- infer-qnt
  -- Γ ⊢ Quant : Type ~ {}      Γ ⊢ &q : Quant ~ {}
  | qnt : Check β Φ L sp q Γ .Qnt (.Typ (.Qua .Lone)) Uses.zero .Qnt
  | qua : Check β Φ L sp q Γ (.Qua q') .Qnt Uses.zero (Term.era q (.Qua q'))
  -- Γ ⊢ a : Quant ~ πa    Γ ⊢ b : Quant ~ πb    (both at the ambient demand)
  -- ------------------------------------------------ infer-min
  -- Γ ⊢ a <&> b : Quant ~ πa + πb
  | min : Check β Φ L [] q Γ a .Qnt πa ua →
          Check β Φ L [] q Γ b .Qnt πb ub →
          Check β Φ L sp q Γ (.Min a b) .Qnt (Uses.add πa πb) (Term.era q (.Min ua ub))
  -- Γ ⊢ A : Kind(q')    Γ, q' A ⊢ B : Type    (both dead)
  -- ------------------------------------------------ infer-all
  -- Γ ⊢ @q' A -> B : Type ~ {}
  | all : Check β Φ L [] .None Γ A (.Typ (.Qua q')) πA .Qnt →
          Check β Φ L.shift [] .None (⟨q', A, none⟩ :: Γ) B (.Typ (.Qua .Lone)) πB .Qnt →
          Check β Φ L sp q Γ (.All q' A B) (.Typ (.Qua .Lone)) Uses.zero
            (Term.era q (.All q' .Qnt .Qnt))
  -- Γ ⊢ A : Kind(q')    (dead: the goal's arrow was formed under infer-all)
  -- Γ, q' A ⊢ f : B ~ π    π[0] <= q'
  -- where L binds the next column by x while one remains
  -- ------------------------------------------------ check-lam
  -- Γ ⊢ λ f : @q' A -> B ~ tail π
  | lam : Check β Φ L [] .None Γ A (.Typ (.Qua q')) πA .Qnt →
          Check β Φ L.lam [] q (⟨q', A, none⟩ :: Γ) f B π uf →
          Quant.le (π 0) q' →
          Check β Φ L sp q Γ (.Lam f) (.All q' A B) (Uses.tail π) (Term.era q (.Lam uf))
  -- Γ ⊢ f : @q' A -> B ~ πf (with x pending)    Γ ⊢ x : A ~ πx at dem q' q
  -- where x is dead if q' is -, and consumed once otherwise: its measure
  --       adds unscaled (certify-once), a + callee copies it
  -- --------------------------------------------------------------- infer-app
  -- Γ ⊢ f(x) : B[0 := x] ~ πf + πx
  | app : Check β Φ L (x :: sp) q Γ f (.All q' A B) πf uf →
          Check β Φ L [] (Quant.dem q' q) Γ x A πx ux →
          Check β Φ L sp q Γ (.App f x) (Term.subst 0 x B) (Uses.add πf πx)
            (Term.era q (.App uf ux))
  -- Γ ⊢ f[0 := a] : T ~ π    (a in scope: bend.ts terms are always well-scoped)
  -- ------------------------------ infer-app (a lambda head: one beta step)
  -- Γ ⊢ (λ f)(a) : T ~ π
  | appLam : Term.Closed Γ.length a →
             Check β Φ L sp q Γ (Term.subst 0 a f) T π u →
             Check β Φ L sp q Γ (.App (.Lam f) a) T π u
  -- Γ ⊢ v : A ~ πv at dem qb q    Γ ⊢ A : Kind(qb)    (dead)
  -- Γ, qb A = v ⊢ b : T↑ ~ π    π[0] <= qb
  -- ------------------------------------------------------------------- check-let
  -- Γ ⊢ qb x = v; b : T ~ πv + tail π
  | let_ : Check β Φ L [] (Quant.dem qb q) Γ v A πv uv →
           Check β Φ L [] .None Γ A (.Typ (.Qua qb)) πA .Qnt →
           Check β Φ L.shift [] q (⟨qb, A, some v⟩ :: Γ) b (Term.shift 0 T) π ub →
           Quant.le (π 0) qb →
           Check β Φ L sp q Γ (.Let qb v b) T (Uses.add πv (Uses.tail π))
             (Term.era q (.Let qb uv ub))
  -- Γ ⊢ T : Type    Γ ⊢ a : T    Γ ⊢ b : T    (all dead; evidence is erased)
  -- --------------------------------------------------- infer-eql
  -- Γ ⊢ {a == b : T} : Data ~ {}
  | eql : Check β Φ L [] .None Γ T (.Typ (.Qua .Lone)) πT .Qnt →
          Check β Φ L [] .None Γ a T πa .Qnt →
          Check β Φ L [] .None Γ b T πb .Qnt →
          Check β Φ L sp q Γ (.Eql a b T) (.Typ (.Qua .Many)) Uses.zero
            (Term.era q (.Eql .Qnt .Qnt .Qnt))
  -- a == b    (let-expanded, compare EQ)
  -- ------------------------------ check-rfl
  -- Γ ⊢ {==} : {a == b : T} ~ {}
  | rfl : Conv β (Ctx.δ Γ 0 a) (Ctx.δ Γ 0 b) →
          Check β Φ L sp q Γ .Rfl (.Eql a b T) Uses.zero (Term.era q .Rfl)
  -- Γ ⊢ e : {a == b : T} ~ πe
  -- Γ ⊢ P : @x:T -> @_:{a == x : T} -> Type    (dead; the J motive)
  -- Γ ⊢ f : P(a, {==}) ~ πf
  -- ------------------------------------------ check-rwt
  -- Γ ⊢ %e : P; f : P(b, e) ~ πe + πf
  | rwt : Check β Φ L [] q Γ e (.Eql a b T) πe ue →
          Check β Φ L [] .None Γ P (Term.jmotive a T) πP .Qnt →
          Check β Φ L [] q Γ f (.App (.App P a) .Rfl) πf uf →
          Check β Φ L sp q Γ (.Rwt e P f) (.App (.App P b) e) (Uses.add πe πf)
            (Term.era q (.Rwt ue .Qnt uf))
  -- β[a].cs[c] : telescope, params instantiated at ps leaving telF
  -- Γ ⊢ h : fields of telF at field times q', tipped at B[Ctr a c · ps · fields] ~ πh
  -- Γ ⊢ m : @q' (Adt a (c :: r)) · ps -> B ~ πm
  -- where c is not already peeled, q' is live in a live region, and
  --       L peels the next column into c's fields for h
  -- --------------------------------------------------------------------- check-mat
  -- Γ ⊢ \{c: h; m} : @q' (Adt a r) · ps -> B ~ πh | πm
  | mat : Book.adt β a = some A → AdtD.ctr A c = some C →
          c ∉ r → ps.length = A.pn →
          (q ≠ .None → q' ≠ .None) →
          Insts C.ty ps telF →
          MatGoal q' C.fn B (Term.apps (.Ctr a c) ps) telF G →
          Check β Φ (L.mat a c C.fn) [] q Γ h G πh uh →
          Check β Φ L [] q Γ m (.All q' (Term.apps (.Adt a (c :: r)) ps) B) πm um →
          Check β Φ L sp q Γ (.Mat a c h m) (.All q' (Term.apps (.Adt a r) ps) B)
            (Uses.join πh πm) (Term.era q (.Mat a c uh um))
  -- every constructor of β[a] is peeled, or a LIVE binding in scope has an
  -- emptied type (ctx_dead, the policy's efq); q' is live in a live region
  -- --------------------------------------------------------------------- check-efq
  -- Γ ⊢ \{} : @q' (Adt a r) · ps -> B ~ {}
  | efq : Book.adt β a = some A →
          (q ≠ .None → q' ≠ .None) →
          (Book.empty β a r ∨ Φ.efq Γ) →
          Check β Φ L sp q Γ .Efq (.All q' (Term.apps (.Adt a r) ps) B) Uses.zero
            (Term.era q .Efq)
  -- Γ ⊢ t : A ~ π    A <= B    (let-expanded, the policy's conversion)
  -- ------------------------ check-any
  -- Γ ⊢ t : B ~ π
  | cnv : Check β Φ L sp q Γ t A π u → Φ.conv (Ctx.δ Γ 0 A) (Ctx.δ Γ 0 B) →
          Check β Φ L sp q Γ t B π u

-- ============================================================================
-- §10 Valid (== bend.ts Valid: book_valid, adt_valid, def_valid)
-- ============================================================================

-- STele n T G: the family signature, pn parameter binders tipped at a
-- term that weak-reduces to the kind Kind(G) (tele_unbind then the Typ
-- test of adt_valid; the declared kind may be an alias)
def STele (β : Book) : Nat → Term → Term → Prop
  | 0,     T, G => Red β .weak T (.Typ G)
  | n + 1, T, G => ∃ q K B, T = .All q K B ∧ STele β n B G

-- TeleQs β T n qs: the quantities of the first n binders of a def's type,
-- each layer opened by wnf (tele_unbind; def_valid's qs)
inductive TeleQs (β : Book) : Term → Nat → List Quant → Prop
  | nil  : TeleQs β T 0 []
  | cons : Red β .weak T (.All q A B) → TeleQs β B n qs →
           TeleQs β T (n + 1) (q :: qs)

-- CtrOk β k pn G Γ i T: adt_valid's constructor walk. Binder i's domain
-- checks dead against Kind(q) for a parameter or a non-Lone field, and
-- against the family's kind G (shifted to the binder's depth) for a live
-- field, in the real constructor context
def CtrOk (β : Book) (k pn : Nat) (G : Term) : Ctx → Nat → Term → Prop
  | Γ, i, .All q A B =>
      (∃ π, Check β (Pol.std β) ⟨k, .Ref k, 0, [], false⟩ [] .None Γ A
        (if pn ≤ i ∧ q = .Lone then Term.shiftN (i - pn) G else .Typ (.Qua q)) π .Qnt) ∧
      CtrOk β k pn G (⟨q, A, none⟩ :: Γ) (i + 1) B
  | _, _, _ => True

-- Tree β n t: the flattener's output shape, a case tree over n columns
-- in binder order (match_flatten): a Lam binds a variable column, a Mat
-- peels a constructor column into fn field columns for its arm and keeps
-- the column for its tail, an Efq closes it, and below the columns any
-- term is a leaf. def_valid trusts this shape (parse_def_body builds it),
-- and check-mat's peel is sound only under it
inductive Tree (β : Book) : Nat → Term → Prop
  | leaf : Tree β 0 t
  | lam  : Tree β n f → Tree β (n + 1) (.Lam f)
  | mat  : Book.adt β a = some A → AdtD.ctr A c = some C →
           Tree β (n + C.fn) h → Tree β (n + 1) m → Tree β (n + 1) (.Mat a c h m)
  | efq  : Tree β (n + 1) .Efq

-- Book.Ok (book_valid): each family's signature checks dead against Type
-- and tips at a kind; each constructor has parse_adt's shape and passes
-- adt_valid's walk. Each definition's type checks dead against Type, its
-- column quantities are read off it, a bodiless definition is native
-- (a complete book: no surviving law), and a body is a case tree over
-- the columns that checks LIVE against the type under the def's own
-- equation, so every live self-call descends
def Book.Ok (β : Book) : Prop :=
  ∀ k t, Book.tld β k = some t →
    match t with
    | .adt A =>
        (∃ π, Check β (Pol.std β) ⟨k, .Ref k, 0, [], false⟩ [] .None [] A.sig (.Typ (.Qua .Lone)) π .Qnt) ∧
        ∃ G, STele β A.pn A.sig G ∧
        ∀ c C, AdtD.ctr A c = some C →
          CtrD.Shape k A.pn C ∧ CtrOk β k A.pn G [] 0 C.ty
    | .defn d =>
        (∃ π, Check β (Pol.std β) ⟨k, .Ref k, 0, [], false⟩ [] .None [] d.ty (.Typ (.Qua .Lone)) π .Qnt) ∧
        TeleQs β d.ty d.n d.qs ∧
        (d.body = none → d.b = true) ∧
        (∀ b, d.body = some b → Tree β d.n b ∧
          ∃ π u, Check β (Pol.std β) ⟨k, .Ref k, d.n, d.qs, false⟩ [] .Lone [] b d.ty π u)

-- Book.Wall: every body also checks with the wall up, so no live call
-- runs ahead in fill order and the live reference graph is well-founded.
-- A book without natives has it for free (only base.bend mints the b
-- flag); base.bend itself breaks it in seventeen helper pairs
-- (Map.seek.bit calls the pending law Map.seek, which calls it back),
-- each a structural recursion by inspection that the checker does not
-- test. Claims (4) and (5) assume it
def Book.Wall (β : Book) : Prop :=
  ∀ k d b, Book.defn β k = some d → d.body = some b →
    ∃ π u, Check β (Pol.std β) ⟨k, .Ref k, d.n, d.qs, true⟩ [] .Lone [] b d.ty π u

-- Book.Filled β: no definition is bodiless. Book.Native β: every bodiless
-- native could be filled — a case tree of its arity checks live against
-- its type under its own equation with the wall up. A constant fills each
-- of base.bend's natives (they answer F32, U32, Bool, String, Maybe or
-- IO). The termination claims are stated for filled books: a stuck
-- native of an emptied type would void the dead arm of a match, and an
-- axiom at Void{e: Empty} is an inconsistency. Book.fill carries them
-- over: typing only grows when a native gains a body (Check.fill, PART II)
def Book.Filled (β : Book) : Prop :=
  ∀ k d, Book.defn β k = some d → d.body ≠ none

def Book.Native (β : Book) : Prop :=
  ∀ k d, Book.defn β k = some d → d.body = none →
    ∃ w π u, Tree β d.n w ∧ Check β (Pol.std β) ⟨k, .Ref k, d.n, d.qs, true⟩ [] .Lone [] w d.ty π u

-- β' fills β: the same book, except that a bodiless definition may have
-- gained a body
def Book.fill (β β' : Book) : Prop :=
  β.length = β'.length ∧
  ∀ k, (∀ A, Book.adt β k = some A ↔ Book.adt β' k = some A) ∧
    ∀ d, Book.defn β k = some d →
      ∃ d', Book.defn β' k = some d' ∧ d'.n = d.n ∧ d'.qs = d.qs ∧ d'.ty = d.ty ∧
        d'.b = d.b ∧ (d.body ≠ none → d'.body = d.body)

-- ============================================================================
-- §11 Claims (bend.ts states these in prose; PART II proves them)
-- ============================================================================

def church_rosser : Prop :=
  ∀ (β : Book) (a b c : Term),
    Book.Ok β → Red β .strong a b → Red β .strong a c →
    ∃ d, Red β .strong b d ∧ Red β .strong c d

def subject_reduction : Prop :=
  ∀ (β : Book) (t t' T : Term) (π : Uses) (u : Term),
    Book.Ok β → Book.Wall β → Book.Filled β →
    Check β (Pol.std β) (LHS.void β) [] .Lone [] t T π u → Step β .weak t t' →
    ∃ π' u', Check β (Pol.std β) (LHS.void β) [] .Lone [] t' T π' u'

def progress : Prop :=
  ∀ (β : Book) (q : Quant) (t T : Term) (π : Uses) (u : Term),
    Book.Ok β → q ≠ .None → Check β (Pol.std β) (LHS.void β) [] q [] t T π u →
    Term.Value β t ∨ ∃ t', Step β .weak t t'

def normalization : Prop :=
  ∀ (β : Book) (t T : Term) (π : Uses) (u : Term),
    Book.Ok β → Book.Wall β → Book.Filled β →
    Check β (Pol.std β) (LHS.void β) [] .Lone [] t T π u →
    ∃ v π' u', Red β .weak t v ∧ Term.Value β v ∧
      Check β (Pol.std β) (LHS.void β) [] .Lone [] v T π' u'

-- no closed live term inhabits an emptied family: one with no
-- constructor, or one with every constructor peeled
def consistency : Prop :=
  ∀ (β : Book) (a : Nat) (r : List Nat) (ps : List Term)
    (t : Term) (π : Uses) (u : Term),
    Book.Ok β → Book.Wall β → Book.Filled β → Book.empty β a r →
    ¬ Check β (Pol.std β) (LHS.void β) [] .Lone [] t (Term.apps (.Adt a r) ps) π u

-- and for a book with natives: through any filling of them
def consistency_natives : Prop :=
  ∀ (β : Book) (a : Nat) (r : List Nat) (ps : List Term)
    (t : Term) (π : Uses) (u : Term),
    Book.Ok β → Book.Wall β → Book.Native β → Book.empty β a r →
    ¬ Check β (Pol.std β) (LHS.void β) [] .Lone [] t (Term.apps (.Adt a r) ps) π u











-- ============================================================================
-- ============================================================================
--
-- PART II — THE METATHEORY
--
-- Everything below proves the claims of §11, and the
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
  simp [Term.jmotive, Term.shift, Term.shift_shift0]

theorem Term.subst_jmotive (a T : Term) (d : Nat) (w : Term) :
    Term.subst d w (Term.jmotive a T)
      = Term.jmotive (Term.subst d w a) (Term.subst d w T) := by
  simp [Term.jmotive, Term.subst, Term.shift_subst_lt _ 0 d w (Nat.zero_le d)]

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
  case Typ ih => exact ih n m hc h
  case Min iha ihb => exact ⟨iha n m hc.1 h, ihb n m hc.2 h⟩
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
  case Typ ih => rw [ih n d hc h]
  case Min iha ihb => rw [iha n d hc.1 h, ihb n d hc.2 h]
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
  case Typ ih => exact ih n d hc hle
  case Min iha ihb => rw [iha n d hc.1 hle, ihb n d hc.2 hle]
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
  case Typ ih => exact ih d i hid
  case Min iha ihb => rw [iha d i hid, ihb d i hid]
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
  case Typ ih => exact ih e i w hie ht hw
  case Min iha ihb =>
    rw [iha e i w hie (by omega) hw, ihb e i w hie (by omega) hw]
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
  case Typ ih => exact ih e i w hei ht hw
  case Min iha ihb =>
    rw [iha e i w hei (by omega) hw, ihb e i w hei (by omega) hw]
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
  case Typ ih => rw [ih e w w' ht]
  case Min iha ihb => rw [iha e w w' (by omega), ihb e w w' (by omega)]
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
  case Typ ih => rw [ih d w ht]
  case Min iha ihb => rw [iha d w (by omega), ihb d w (by omega)]
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
  case Typ ih => rw [ih n d w hc h]
  case Min iha ihb => rw [iha n d w hc.1 h, ihb n d w hc.2 h]
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

-- substituting an absent variable is a renaming that shift undoes
theorem Term.shift_subst_occ : ∀ (t : Term) (d : Nat) (w : Term),
    Term.occ d t = 0 → Term.shift d (Term.subst d w t) = t := by
  intro t
  induction t <;> intro d w ht <;> simp only [Term.subst, Term.occ] at ht ⊢
  case Var i =>
    have hne : i ≠ d := by intro h; rw [if_pos h] at ht; simp at ht
    rw [if_neg hne]
    split <;> simp only [Term.shift] <;> split <;>
      first | rfl | (exfalso; omega) | (simp only [Term.Var.injEq]; omega)
  case Typ ih => simp only [Term.shift, ih d w ht]
  case Min iha ihb => simp only [Term.shift, iha d w (by omega), ihb d w (by omega)]
  case All ihA ihB =>
    simp only [Term.shift, ihA d w (by omega), ihB (d + 1) _ (by omega)]
  case Lam ihf => simp only [Term.shift, ihf (d + 1) _ ht]
  case App ihf iha => simp only [Term.shift, ihf d w (by omega), iha d w (by omega)]
  case Mat ihh ihm =>
    rw [Nat.max_eq_zero_iff] at ht
    simp only [Term.shift, ihh d w ht.1, ihm d w ht.2]
  case Eql iha ihb ihT =>
    simp only [Term.shift, iha d w (by omega), ihb d w (by omega), ihT d w (by omega)]
  case Rwt ihe ihP ihf =>
    simp only [Term.shift, ihe d w (by omega), ihP d w (by omega), ihf d w (by omega)]
  case Let ihv ihb =>
    simp only [Term.shift, ihv d w (by omega), ihb (d + 1) _ (by omega)]
  all_goals simp [Term.shift]

-- the context and the equation: Ctx.get on a cons, the let expansion of
-- a term with no variable at or above its depth, and the void equation
-- as a fixed point of the walks
theorem Ctx.get_zero (b : Bind) (Γ : Ctx) : Ctx.get (b :: Γ) 0 = some b.shift := rfl

theorem Ctx.get_succ (b : Bind) (Γ : Ctx) (i : Nat) :
    Ctx.get (b :: Γ) (i + 1) = (Ctx.get Γ i).map Bind.shift := rfl

theorem Ctx.δ_closed : ∀ (Γ : Ctx) (d : Nat) (t : Term), Term.Closed d t →
    Ctx.δ Γ d t = t := by
  intro Γ
  induction Γ with
  | nil => intro d t _; rfl
  | cons b Γ ih =>
    intro d t hc
    simp only [Ctx.δ]
    split
    · rw [Term.subst_closed t d d _ hc (Nat.le_refl d)]; exact ih d t hc
    · exact ih (d + 1) t (Term.Closed.mono t d (d + 1) hc (by omega))

theorem LHS.shift_void (β : Book) : (LHS.void β).shift = LHS.void β := rfl

theorem LHS.lam_void (β : Book) : (LHS.void β).lam = LHS.void β := rfl

theorem LHS.mat_void (β : Book) (a c fn : Nat) :
    (LHS.void β).mat a c fn = LHS.void β := rfl

theorem LHS.cols_void (β : Book) : (LHS.void β).cols = [] := rfl

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
  | nil => intro m i _; simp
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

-- a Let is never a weak value
theorem Term.Value.let_absurd (hv : Term.Value β (.Let qb v b)) :
    False := by
  generalize ht : Term.Let qb v b = t0 at hv
  cases hv <;> first
    | exact Term.noConfusion ht
    | exact Term.noConfusion
        (Term.apps_head_inv (h := .Let qb v b) (xs := []) (by trivial) (by trivial) ht).1

-- the function of an application value is a value: the head is the same
-- and the spine is one shorter
theorem Term.Value.app_inv (hv : Term.Value β (.App f a)) : Term.Value β f := by
  generalize ht : Term.App f a = t0 at hv
  cases hv with
  | lam => exact Term.noConfusion ht
  | mat => exact Term.noConfusion ht
  | ref hk hg =>
    obtain ⟨ys, hys, hf⟩ := Term.app_eq_apps (by trivial) ht
    subst hf hys
    rcases hg with hg | hg
    · exact .ref hk (.inl (by simp at hg; omega))
    · exact .ref hk (.inr hg)
  | @matS x as _ _ _ _ hx hne =>
    obtain ⟨ys, hys, hf⟩ := Term.app_eq_apps (by trivial) ht
    subst hf
    cases ys with
    | nil => exact .mat
    | cons y ys =>
      have h1 : x = y := (List.cons.inj hys).1
      subst h1
      exact .matS hx hne
  | _ =>
    obtain ⟨ys, _, hf⟩ := Term.app_eq_apps (by trivial) ht
    subst hf
    constructor <;> assumption

-- a bare Ref is a value only when its definition is stuck: positive
-- arity or no body
theorem Term.Value.ref_cases (hv : Term.Value β (.Ref k)) :
    ∀ {d : DefD}, Book.defn β k = some d → 0 < d.n ∨ d.body = none := by
  intro d hk
  generalize ht : Term.Ref k = t0 at hv
  cases hv with
  | lam => exact Term.noConfusion ht
  | mat => exact Term.noConfusion ht
  | fam hk2 _ =>
    obtain ⟨h1, _⟩ :=
      Term.apps_head_inv (h := .Ref k) (xs := []) (by trivial) (by trivial) ht
    cases h1
    cases h : Book.tld β k with
    | none => simp [Book.adt, h] at hk2
    | some t => cases t <;> simp [Book.adt, Book.defn, h] at hk hk2
  | ref hk2 hg =>
    obtain ⟨h1, h2⟩ :=
      Term.apps_head_inv (h := .Ref k) (xs := []) (by trivial) (by trivial) ht
    cases h1
    rw [hk] at hk2
    cases hk2
    rw [← h2] at hg
    rcases hg with hg | hg
    · exact .inl (by simp at hg; omega)
    · exact .inr hg
  | _ =>
    exact Term.noConfusion
      (Term.apps_head_inv (h := .Ref k) (xs := []) (by trivial) (by trivial) ht).1

-- a value stays a value under a shift, and under the substitution of a
-- variable it does not mention
theorem Term.shift_inj (h : Term.shift d a = Term.shift d b) : a = b := by
  have := congrArg (Term.subst d .Qnt) h
  rwa [Term.subst_shift, Term.subst_shift] at this

theorem Term.Value.shift (hv : Term.Value β t) (d : Nat) :
    Term.Value β (Term.shift d t) := by
  induction hv <;> simp only [Term.shift_apps, Term.shift]
  case var => split <;> exact .var
  case ref hk hg => exact .ref hk (by simpa using hg)
  case min ha hb hab iha ihb =>
    exact .min iha (fun h => ‹_ ≠ _› (Term.shift_inj (b := .Qua .Many) h))
      (fun h => ‹_ ≠ _› (Term.shift_inj (b := .Qua .None) h)) ihb
      (fun h => ‹_ ≠ _› (Term.shift_inj (b := .Qua .Many) h))
      (fun h => ‹_ ≠ _› (Term.shift_inj (b := .Qua .None) h))
      (fun h => hab ⟨Term.shift_inj (b := .Qua .Lone) h.1,
        Term.shift_inj (b := .Qua .Lone) h.2⟩)
  case rwt hne ih => exact .rwt ih (fun h => hne (Term.shift_inj (b := .Rfl) h))
  case matS hne ih =>
    refine .matS ih ?_
    intro a' c' xs heq
    apply hne a' c' (xs.map (Term.subst d .Qnt))
    have := congrArg (Term.subst d .Qnt) heq
    rwa [Term.subst_shift, Term.subst_apps] at this
  all_goals constructor <;> assumption

theorem Term.Value.subst (hv : Term.Value β t) (ho : Term.occ d t = 0) (w : Term) :
    Term.Value β (Term.subst d w t) := by
  have inj : ∀ {a b : Term}, Term.occ d a = 0 → Term.subst d w a = b →
      Term.shift d b = b → a = b := by
    intro a b ha h hb
    rw [← Term.shift_subst_occ a d w ha, h, hb]
  induction hv <;> simp only [Term.subst_apps, Term.subst]
  case var i as =>
    rw [Term.occ_apps] at ho
    simp only [Term.occ] at ho
    rw [if_neg (by intro h; rw [if_pos h] at ho; omega)]
    split <;> exact .var
  case ref hk hg => exact .ref hk (by simpa using hg)
  case min a b as ha hb hab iha ihb =>
    rw [Term.occ_apps] at ho
    simp only [Term.occ] at ho
    exact .min (iha (by omega)) (fun h => ‹_ ≠ _› (inj (by omega) h _root_.rfl))
      (fun h => ‹_ ≠ _› (inj (by omega) h _root_.rfl)) (ihb (by omega))
      (fun h => ‹_ ≠ _› (inj (by omega) h _root_.rfl))
      (fun h => ‹_ ≠ _› (inj (by omega) h _root_.rfl))
      (fun h => hab ⟨inj (by omega) h.1 _root_.rfl, inj (by omega) h.2 _root_.rfl⟩)
  case rwt e P f as he hne ih =>
    rw [Term.occ_apps] at ho
    simp only [Term.occ] at ho
    exact .rwt (ih (by omega)) (fun h => hne (inj (by omega) h _root_.rfl))
  case matS x as hx hne ih =>
    rw [Term.occ_apps] at ho
    simp only [Term.occ, List.map_cons, List.sum_cons] at ho
    refine .matS (ih (by omega)) ?_
    intro a' c' xs heq
    apply hne a' c' (xs.map (Term.shift d))
    have := congrArg (Term.shift d) heq
    rwa [Term.shift_subst_occ _ _ _ (by omega), Term.shift_apps] at this
  all_goals constructor <;> assumption

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
  | .Typ g         => 1 + Term.size g
  | .Qnt           => 1
  | .Qua _         => 1
  | .Min a b       => 1 + Term.size a + Term.size b
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

-- ============================================================================
-- METATHEORY §B — confluence: parallel reduction and claim (1).
-- The parallel step develops redexes and congruences at once; the mat
-- redexes leave their spine arguments undeveloped (the congruent
-- closure catches them next lap), which keeps the relation first-order
-- and the diamond a derivation induction. Books must be closed for the
-- δ-rule to commute with substitution.
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

theorem Book.Closed.adtd (hβ : Book.Closed β) (h : Book.adt β a = some A) :
    A.sig.Closed 0 ∧ ∀ c C, AdtD.ctr A c = some C → C.ty.Closed 0 := by
  unfold Book.adt at h
  split at h
  case _ heq => cases h; exact hβ _ _ heq
  case _ => cases h

theorem Book.defn_adt_clash (hd : Book.defn β k = some d)
    (ha : Book.adt β k = some A) : False := by
  cases h : Book.tld β k with
  | none => simp [Book.defn, h] at hd
  | some t => cases t <;> simp [Book.defn, Book.adt, h] at hd ha

-- a spine never equals a different head
theorem Term.apps_ne {h t : Term} {xs : List Term} (hh : h.IsHead) (ht : t.IsHead)
    (hne : h ≠ t) : Term.apps h xs ≠ t :=
  fun heq => hne (Term.apps_head_inv (ys := []) hh ht heq).1

-- spine transport: shifting or substituting under a spine with a
-- shift-invariant head maps the arguments and keeps the head
theorem Term.spine_shift {s h : Term} (hh : (Term.spine s).1 = h)
    (hd : h.IsHead) (hs : Term.shift d h = h) :
    Term.spine (Term.shift d s) = (h, (Term.spine s).2.map (Term.shift d)) := by
  obtain ⟨ts, hts⟩ : ∃ ts, (Term.spine s).2 = ts := ⟨_, rfl⟩
  have hsp : s = Term.apps h ts := by
    rw [← hts, ← hh]; exact (Term.apps_spine s).symm
  rw [hts, hsp, Term.shift_apps, hs, Term.spine_apps hd]

theorem Term.spine_subst {s h : Term} (hh : (Term.spine s).1 = h)
    (hd : h.IsHead) (hs : Term.subst d w h = h) :
    Term.spine (Term.subst d w s) = (h, (Term.spine s).2.map (Term.subst d w)) := by
  obtain ⟨ts, hts⟩ : ∃ ts, (Term.spine s).2 = ts := ⟨_, rfl⟩
  have hsp : s = Term.apps h ts := by
    rw [← hts, ← hh]; exact (Term.apps_spine s).symm
  rw [hts, hsp, Term.subst_apps, hs, Term.spine_apps hd]

-- parallel reduction: every redex and congruence develops at once.
-- The mat rules treat the scrutinee as ONE developed premise and
-- extract its fields by spine surgery, which keeps the relation
-- first-order (no lists of sub-derivations).
inductive Par (β : Book) : Term → Term → Prop
  | var  : Par β (.Var i) (.Var i)
  | ref  : Par β (.Ref k) (.Ref k)
  | typ  : Par β g g' → Par β (.Typ g) (.Typ g')
  | qnt  : Par β .Qnt .Qnt
  | qua  : Par β (.Qua q) (.Qua q)
  | min  : Par β a a' → Par β b b' → Par β (.Min a b) (.Min a' b')
  | adt  : Par β (.Adt a r) (.Adt a r)
  | ctr  : Par β (.Ctr a c) (.Ctr a c)
  | efq  : Par β .Efq .Efq
  | rfl  : Par β .Rfl .Rfl
  | all  : Par β A A' → Par β B B' → Par β (.All q A B) (.All q A' B')
  | eta  : Term.occ 0 F = 0 → Par β F F' →
           Par β (.Lam (.App F (.Var 0))) (Term.subst 0 .Qnt F')
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
             Par β ((Term.spine s).2.getD i .Qnt) (args'.getD i .Qnt)) →
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
  | minLM : Par β b b' → Par β (.Min (.Qua .Many) b) b'
  | minLN : Par β (.Min (.Qua .None) b) (.Qua .None)
  | minRM : Par β a a' → Par β (.Min a (.Qua .Many)) a'
  | minRN : Par β (.Min a (.Qua .None)) (.Qua .None)
  | minLL : Par β (.Min (.Qua .Lone) (.Qua .Lone)) (.Qua .Lone)

-- pointwise parallel reduction on lists (a plain relation)
inductive Pars (β : Book) : List Term → List Term → Prop
  | nil  : Pars β [] []
  | cons : Par β x y → Pars β xs ys → Pars β (x :: xs) (y :: ys)

theorem Par.refl : ∀ (t : Term), Par β t t := by
  intro t
  induction t with
  | Var i => exact .var
  | Ref k => exact .ref
  | Typ g ih => exact .typ ih
  | Qnt => exact .qnt
  | Qua q => exact .qua
  | Min a b iha ihb => exact .min iha ihb
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

theorem Pars.length (h : Pars β xs ys) : xs.length = ys.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem Pars.append (h1 : Pars β xs ys) (h2 : Pars β as bs) :
    Pars β (xs ++ as) (ys ++ bs) := by
  induction h1 with
  | nil => exact h2
  | cons hp _ ih => exact .cons hp ih

theorem Pars.drop (h : Pars β xs ys) : ∀ n, Pars β (xs.drop n) (ys.drop n) := by
  induction h with
  | nil => intro n; simp; exact Pars.nil
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
  | dref hk hb hsp hlen =>
    exact Par.dref hk hb hsp _root_.rfl (fun i _ => Par.refl _)
  | aref hk h0 => exact .aref hk h0
  | matc h1 h2 h3 h4 =>
    rename_i a A c C h m ps xs
    have hd : ((Term.spine (Term.apps (.Ctr a c) (ps ++ xs))).2.drop A.pn) = xs := by
      rw [Term.spine_apps (by trivial)]
      show (ps ++ xs).drop A.pn = xs
      rw [← h3]
      exact List.drop_left
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
  | minLM => exact .minLM (Par.refl _)
  | minLN => exact .minLN
  | minRM => exact .minRM (Par.refl _)
  | minRN => exact .minRN
  | minLL => exact .minLL
  | typ_g _ _ ih => exact .typ ih
  | min_a _ ih => exact .min ih (Par.refl _)
  | min_b _ ih => exact .min (Par.refl _) ih
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

-- the Red kit: strengths, chains, congruences at each rule's strength
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
  | minLM => exact .minLM
  | minLN => exact .minLN
  | minRM => exact .minRM
  | minRN => exact .minRN
  | minLL => exact .minLL
  | typ_g _ _ ih => exact .typ_g rfl ih
  | min_a _ ih => exact .min_a ih
  | min_b _ ih => exact .min_b ih
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

-- a step congruence lifts to runs
theorem Red.congr {F : Term → Term}
    (hF : ∀ {a b}, Step β p a b → Step β p (F a) (F b))
    (r : Red β p a b) : Red β p (F a) (F b) := by
  induction r with
  | refl => exact .refl
  | step s _ ih => exact .step (hF s) ih

theorem Red.typ_g (r : Red β .strong g g') : Red β .strong (.Typ g) (.Typ g') :=
  Red.congr (F := fun g => .Typ g) (fun s => .typ_g rfl s) r
theorem Red.min_a (r : Red β p a a') : Red β p (.Min a b) (.Min a' b) :=
  Red.congr (F := fun a => .Min a b) (fun s => .min_a s) r
theorem Red.min_b (r : Red β p b b') : Red β p (.Min a b) (.Min a b') :=
  Red.congr (F := fun b => .Min a b) (fun s => .min_b s) r
theorem Red.all_a (r : Red β .strong A A') :
    Red β .strong (.All q A B) (.All q A' B) :=
  Red.congr (F := fun A => .All q A B) (fun s => .all_a rfl s) r
theorem Red.all_b (r : Red β .strong B B') :
    Red β .strong (.All q A B) (.All q A B') :=
  Red.congr (F := fun B => .All q A B) (fun s => .all_b rfl s) r
theorem Red.lam_f (r : Red β .strong f f') : Red β .strong (.Lam f) (.Lam f') :=
  Red.congr (F := fun f => .Lam f) (fun s => .lam_f rfl s) r
theorem Red.app_f (r : Red β p f f') : Red β p (.App f a) (.App f' a) :=
  Red.congr (F := fun f => .App f a) (fun s => .app_f s) r
theorem Red.app_a (r : Red β p a a') : Red β p (.App f a) (.App f a') :=
  Red.congr (F := fun a => .App f a) (fun s => .app_a s) r
theorem Red.mat_h (r : Red β p h h') : Red β p (.Mat a c h m) (.Mat a c h' m) :=
  Red.congr (F := fun h => .Mat a c h m) (fun s => .mat_h s) r
theorem Red.mat_m (r : Red β p m m') : Red β p (.Mat a c h m) (.Mat a c h m') :=
  Red.congr (F := fun m => .Mat a c h m) (fun s => .mat_m s) r
theorem Red.eql_a (r : Red β p x x') : Red β p (.Eql x y T) (.Eql x' y T) :=
  Red.congr (F := fun x => .Eql x y T) (fun s => .eql_a s) r
theorem Red.eql_b (r : Red β p y y') : Red β p (.Eql x y T) (.Eql x y' T) :=
  Red.congr (F := fun y => .Eql x y T) (fun s => .eql_b s) r
theorem Red.eql_t (r : Red β p T T') : Red β p (.Eql x y T) (.Eql x y T') :=
  Red.congr (F := fun T => .Eql x y T) (fun s => .eql_t s) r
theorem Red.rwt_e (r : Red β p e e') : Red β p (.Rwt e P f) (.Rwt e' P f) :=
  Red.congr (F := fun e => .Rwt e P f) (fun s => .rwt_e s) r
theorem Red.rwt_p (r : Red β p P P') : Red β p (.Rwt e P f) (.Rwt e P' f) :=
  Red.congr (F := fun P => .Rwt e P f) (fun s => .rwt_p s) r
theorem Red.rwt_f (r : Red β p f f') : Red β p (.Rwt e P f) (.Rwt e P f') :=
  Red.congr (F := fun f => .Rwt e P f) (fun s => .rwt_f s) r
theorem Red.let_v (r : Red β p v v') : Red β p (.Let q v b) (.Let q v' b) :=
  Red.congr (F := fun v => .Let q v b) (fun s => .let_v s) r
theorem Red.let_b (r : Red β .strong b b') :
    Red β .strong (.Let q v b) (.Let q v b') :=
  Red.congr (F := fun b => .Let q v b) (fun s => .let_b rfl s) r

-- a spine's head reduces
theorem Red.apps_f (r : Red β p f f') : ∀ (xs : List Term),
    Red β p (Term.apps f xs) (Term.apps f' xs) := by
  intro xs
  induction xs generalizing f f' with
  | nil => exact r
  | cons x xs ih => exact ih (Red.app_f r)

-- pointwise runs on lists
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

-- indexed pointwise runs assemble into a Reds
theorem Reds.of_getD : ∀ {xs ys : List Term}, xs.length = ys.length →
    (∀ i, i < xs.length → Red β p (xs.getD i .Qnt) (ys.getD i .Qnt)) →
    Reds β p xs ys := by
  intro xs
  induction xs with
  | nil => intro ys hl _; cases ys with | nil => exact .nil | cons => simp at hl
  | cons x xs ih =>
    intro ys hl hr
    cases ys with
    | nil => simp at hl
    | cons y ys =>
      exact .cons (hr 0 (by simp)) (ih (by simp at hl; omega)
        (fun i hi => hr (i + 1) (by simp; omega)))

-- a spine's arguments reduce pointwise
theorem Red.apps_args (h : Reds β p as bs) : ∀ (f : Term),
    Red β p (Term.apps f as) (Term.apps f bs) := by
  induction h with
  | nil => intro f; exact .refl
  | cons hr _ ih => intro f; exact ((Red.app_a hr).apps_f _).trans (ih _)

-- stability: a parallel reduct of a Ctr-headed spine is a Ctr-headed
-- spine with pointwise-parallel arguments
theorem Par.ctr_spine_inv (hp : Par β s t) :
    ∀ {a c : Nat} {as : List Term}, s = Term.apps (.Ctr a c) as →
    ∃ as', t = Term.apps (.Ctr a c) as' ∧ Pars β as as' := by
  induction hp <;> intro a c as heq
  all_goals try exact absurd heq.symm (Term.apps_ne (by trivial) (by trivial) (fun h => Term.noConfusion h))
  all_goals try (obtain ⟨ys, _, hfy⟩ := Term.app_eq_apps (by trivial) heq
                 exact absurd hfy.symm (Term.apps_ne (by trivial) (by trivial) (fun h => Term.noConfusion h)))
  case ctr =>
    obtain ⟨h1, h2⟩ := Term.apps_head_inv (h := Term.Ctr _ _) (by trivial)
      (by trivial) (xs := []) heq
    cases h1
    cases h2
    exact ⟨[], _root_.rfl, .nil⟩
  case app _ _ _ _ hf ha ihf _ =>
    obtain ⟨ys, hys, hfy⟩ := Term.app_eq_apps (by trivial) heq
    obtain ⟨ys', hy1, hy2⟩ := ihf hfy
    subst hys hy1
    exact ⟨ys' ++ [_], (Term.apps_snoc _ _ _).symm,
      Pars.append hy2 (.cons ha .nil)⟩
  case dref _ _ _ _ _ _ _ hsp _ _ _ =>
    rw [heq, Term.spine_apps (by trivial)] at hsp
    exact Term.noConfusion hsp

-- spine-form of stability
theorem Par.spine_stable (hp : Par β s t) (hh : (Term.spine s).1 = .Ctr a c) :
    (Term.spine t).1 = .Ctr a c ∧ Pars β (Term.spine s).2 (Term.spine t).2 := by
  have hs : s = Term.apps (.Ctr a c) (Term.spine s).2 := by
    rw [← hh]; exact (Term.apps_spine s).symm
  obtain ⟨as', ht, hps⟩ := hp.ctr_spine_inv hs
  rw [ht, Term.spine_apps (by trivial)]
  exact ⟨_root_.rfl, hps⟩

-- occurrence sums over spines
theorem List.occ_sum_zero_of_getD (d : Nat) : ∀ (as : List Term),
    (∀ i, i < as.length → Term.occ d (as.getD i .Qnt) = 0) →
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
    ∀ i, i < as.length → Term.occ d (as.getD i .Qnt) = 0 := by
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
  | typ _ ih => exact fun d h => ih d h
  | qnt => exact fun _ h => h
  | qua => exact fun _ h => h
  | adt => exact fun _ h => h
  | ctr => exact fun _ h => h
  | efq => exact fun _ h => h
  | rfl => exact fun _ h => h
  | aref _ => exact fun _ _ => _root_.rfl
  | min _ _ iha ihb =>
    intro d h
    simp only [Term.occ] at h ⊢
    rw [iha d (by omega), ihb d (by omega)]
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
    exact Term.occ_subst_zero F' 0 d .Qnt (Nat.zero_le d)
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
  | minLM _ ih =>
    intro d h
    simp only [Term.occ] at h
    exact ih d (by omega)
  | minLN => exact fun _ _ => _root_.rfl
  | minRM _ ih =>
    intro d h
    simp only [Term.occ] at h
    exact ih d (by omega)
  | minRN => exact fun _ _ => _root_.rfl
  | minLL => exact fun _ _ => _root_.rfl

theorem Par.red (hβ : Book.Closed β) (hp : Par β a b) :
    Red β .strong a b := by
  induction hp with
  | @eta F F' hocc hF ih =>
    have hocc' : Term.occ 0 F' = 0 := Par.occ_zero hβ hF 0 hocc
    exact Red.trans (Red.lam_f (Red.app_f ih))
      (Red.one (Step.eta _root_.rfl hocc'))
  | var => exact .refl
  | ref => exact .refl
  | typ _ ih => exact Red.typ_g ih
  | qnt => exact .refl
  | qua => exact .refl
  | min _ _ iha ihb => exact (Red.min_a iha).trans (Red.min_b ihb)
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
    exact (Red.apps_args (Reds.of_getD hlen' ih) _).trans (Red.one hstep)
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
    exact ((Red.app_a ihs).trans (Red.one hstep)).trans (ihh.apps_f _)
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
  | minLM _ ih => exact (Red.one .minLM).trans ih
  | minLN => exact Red.one .minLN
  | minRM _ ih => exact (Red.one .minRM).trans ih
  | minRN => exact Red.one .minRN
  | minLL => exact Red.one .minLL

-- parallel reduction commutes with shift (closed book: δ-bodies are
-- fixed points of shift)
theorem Par.shift (hβ : Book.Closed β) (hp : Par β t t') :
    ∀ d, Par β (t.shift d) (t'.shift d) := by
  induction hp with
  | @eta F F' hocc hF ih =>
    intro d
    show Par β (.Lam (.App (Term.shift (d + 1) F)
      (Term.shift (d + 1) (.Var 0))))
      (Term.shift d (Term.subst 0 .Qnt F'))
    have h0 : Term.shift (d + 1) (Term.Var 0) = .Var 0 := by
      simp only [Term.shift]
      rw [if_pos (by omega)]
    have h1 : Term.shift d (Term.subst 0 .Qnt F')
        = Term.subst 0 .Qnt (Term.shift (d + 1) F') := by
      rw [Term.shift_subst_ge F' d 0 .Qnt (Nat.zero_le d)]
      rfl
    rw [h0, h1]
    exact .eta (by
        rw [Term.occ_shift_lt F 0 (d + 1) (by omega)]
        exact hocc)
      (ih (d + 1))
  | var => intro d; simp only [Term.shift]; split <;> exact .var
  | ref => intro d; exact .ref
  | typ _ ih => intro d; exact .typ (ih d)
  | qnt => intro d; exact .qnt
  | qua => intro d; exact .qua
  | min _ _ iha ihb => intro d; exact .min (iha d) (ihb d)
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
    rw [map_getD (Term.shift d) .Qnt .Qnt _ i (by omega),
      map_getD (Term.shift d) .Qnt .Qnt args' i (by omega)]
    exact ih i (by omega) d
  | aref hk h0 => intro d; exact .aref hk h0
  | matc h1 h2 h3 h4 hps hph ihs ihh =>
    rename_i a A c C s s' h h' m
    intro d
    obtain ⟨hh', hargs⟩ := hps.spine_stable h3
    have e1 : (Term.spine (Term.shift d s)).1 = Term.Ctr a c := by
      rw [Term.spine_shift h3 (by trivial) _root_.rfl]
    have e2 : (Term.spine (Term.shift d s)).2.length = A.pn + C.fn := by
      rw [Term.spine_shift h3 (by trivial) _root_.rfl]; simpa using h4
    have e3 : Term.shift d (Term.apps h' ((Term.spine s').2.drop A.pn))
        = Term.apps (Term.shift d h')
            ((Term.spine (Term.shift d s')).2.drop A.pn) := by
      rw [Term.shift_apps, Term.spine_shift hh' (by trivial) _root_.rfl]
      show _ = Term.apps _ (((Term.spine s').2.map (Term.shift d)).drop A.pn)
      rw [List.map_drop]
    rw [show Term.shift d (.App (.Mat a c h m) s)
        = .App (.Mat a c (Term.shift d h) (Term.shift d m)) (Term.shift d s)
      from _root_.rfl, e3]
    exact Par.matc h1 h2 e1 e2 (ihs d) (ihh d)
  | matm h1 hne hps hphm ihs ihm =>
    rename_i s a' c' a c s' m m' h
    intro d
    exact Par.matm (by rw [Term.spine_shift h1 (by trivial) _root_.rfl]) hne
      (ihs d) (ihm d)
  | rwtr _ ihf => intro d; exact .rwtr (ihf d)
  | minLM _ ih => intro d; exact .minLM (ih d)
  | minLN => intro d; exact .minLN
  | minRM _ ih => intro d; exact .minRM (ih d)
  | minRN => intro d; exact .minRN
  | minLL => intro d; exact .minLL

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
      (Term.subst d w' (Term.subst 0 .Qnt F'))
    have h0 : Term.subst (d + 1) (Term.shift 0 w) (Term.Var 0)
        = .Var 0 := by
      simp only [Term.subst]
      rw [if_neg (by omega), if_neg (by omega)]
    have h1 : Term.subst d w' (Term.subst 0 .Qnt F')
        = Term.subst 0 .Qnt (Term.subst (d + 1) (Term.shift 0 w') F') := by
      rw [Term.subst_subst0 F' w' .Qnt d]
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
  | typ _ ih => intro d w w' hw; exact .typ (ih d hw)
  | qnt => intro d w w' _; exact .qnt
  | qua => intro d w w' _; exact .qua
  | min _ _ iha ihb => intro d w w' hw; exact .min (iha d hw) (ihb d hw)
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
    rw [map_getD (Term.subst d w) .Qnt .Qnt _ i (by omega),
      map_getD (Term.subst d w') .Qnt .Qnt args' i (by omega)]
    exact ih i (by omega) d hw
  | aref hk h0 => intro d w w' _; exact .aref hk h0
  | matc h1 h2 h3 h4 hps hph ihs ihh =>
    rename_i a A c C s s' h h' m
    intro d w w' hw
    obtain ⟨hh', hargs⟩ := hps.spine_stable h3
    have e1 : (Term.spine (Term.subst d w s)).1 = Term.Ctr a c := by
      rw [Term.spine_subst h3 (by trivial) _root_.rfl]
    have e2 : (Term.spine (Term.subst d w s)).2.length = A.pn + C.fn := by
      rw [Term.spine_subst h3 (by trivial) _root_.rfl]; simpa using h4
    have e3 : Term.subst d w' (Term.apps h' ((Term.spine s').2.drop A.pn))
        = Term.apps (Term.subst d w' h')
            ((Term.spine (Term.subst d w' s')).2.drop A.pn) := by
      rw [Term.subst_apps, Term.spine_subst hh' (by trivial) _root_.rfl]
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
    exact Par.matm (by rw [Term.spine_subst h1 (by trivial) _root_.rfl]) hne
      (ihs d hw) (ihm d hw)
  | rwtr _ ihf =>
    intro d w w' hw
    exact .rwtr (ihf d hw)
  | minLM _ ih => intro d w w' hw; exact .minLM (ih d hw)
  | minLN => intro d w w' _; exact .minLN
  | minRM _ ih => intro d w w' hw; exact .minRM (ih d hw)
  | minRN => intro d w w' _; exact .minRN
  | minLL => intro d w w' _; exact .minLL

-- inversion: parallel reducts of the binder-formers and literals keep
-- their shape
theorem Par.lam_inv (hp : Par β (.Lam f) t) :
    (∃ f', t = .Lam f' ∧ Par β f f')
    ∨ (∃ G G', f = .App G (.Var 0) ∧ Term.occ 0 G = 0 ∧
        t = Term.subst 0 .Qnt G' ∧ Par β G G') := by
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
  | rfl => exact _root_.rfl
  | dref _ _ hsp _ _ => exact Term.noConfusion hsp

theorem Par.qua_inv (hp : Par β (.Qua q) t) : t = .Qua q := by
  cases hp with
  | qua => exact _root_.rfl
  | dref _ _ hsp _ _ => exact Term.noConfusion hsp

-- a parallel reduct of a defined-reference-headed spine: either the
-- head survives with pointwise-parallel arguments, or the definition
-- fired (at or above arity) and the reduct is the body's spine
theorem Par.ref_spine_cases (hd : Book.defn β k = some d)
    (hp : Par β s t) :
    ∀ {as : List Term}, s = Term.apps (.Ref k) as →
    (∃ as', t = Term.apps (.Ref k) as' ∧ as.length = as'.length ∧
      (∀ i, i < as.length → Par β (as.getD i .Qnt) (as'.getD i .Qnt)))
    ∨ (∃ b as', d.body = some b ∧
      as.length = as'.length ∧
      (∀ i, i < as.length → Par β (as.getD i .Qnt) (as'.getD i .Qnt)) ∧
      t = Term.apps b as') := by
  induction hp <;> intro as heq
  all_goals try exact absurd heq.symm (Term.apps_ne (by trivial) (by trivial) (fun h => Term.noConfusion h))
  all_goals try (obtain ⟨ys, _, hfy⟩ := Term.app_eq_apps (by trivial) heq
                 exact absurd hfy.symm (Term.apps_ne (by trivial) (by trivial) (fun h => Term.noConfusion h)))
  case app f f' a a' hf ha ihf iha =>
    obtain ⟨as0, hys, hfy⟩ := Term.app_eq_apps (by trivial) heq
    subst hys
    have hsnocp : ∀ (xs xs' : List Term) (x x' : Term),
        xs.length = xs'.length →
        (∀ i, i < xs.length →
          Par β (xs.getD i .Qnt) (xs'.getD i .Qnt)) →
        Par β x x' →
        ∀ i, i < (xs ++ [x]).length →
          Par β ((xs ++ [x]).getD i .Qnt)
            ((xs' ++ [x']).getD i .Qnt) := by
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
    rcases ihf hfy with ⟨as0', ht', hl', hp'⟩ |
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
  case dref _ k2 b2 s2 args2' hk2 hb2 hsp2 hlen2' hps2 _ =>
    subst heq
    rw [Term.spine_apps (by trivial)] at hsp2 hlen2' hps2
    injection hsp2 with hkk
    subst hkk
    rw [hk2] at hd
    cases hd
    exact Or.inr ⟨b2, args2', hb2, hlen2', hps2, _root_.rfl⟩
  case aref hk2 _ =>
    obtain ⟨h1, h2⟩ := Term.apps_head_inv (xs := []) (by trivial) (by trivial) heq
    cases h1
    exact absurd hk2 (fun hA => Book.defn_adt_clash hd hA)
  case ref =>
    obtain ⟨h1, h2⟩ := Term.apps_head_inv (xs := []) (by trivial) (by trivial) heq
    cases h1
    subst h2
    exact Or.inl ⟨[], _root_.rfl, _root_.rfl, fun i hi => absurd hi (by simp)⟩

-- parallel congruence over an application spine
theorem Par.apps_congr {h h' : Term} (hh : Par β h h') :
    ∀ {args args' : List Term},
    args.length = args'.length →
    (∀ i, i < args.length →
      Par β (args.getD i .Qnt) (args'.getD i .Qnt)) →
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
        Par β (f i) (qs.getD i .Qnt) ∧ Par β (g i) (qs.getD i .Qnt)) := by
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
      ∃ q, Par β (Term.subst 0 .Qnt F') q ∧ Par β (.Lam B2') q := by
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
      exact ⟨Term.subst 0 .Qnt F3,
        Par.subst hβ hF31 0 .qnt,
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
      refine ⟨Term.subst 0 .Qnt Q, Par.subst hβ hQ2 0 .qnt, ?_⟩
      have hrw : Term.Lam (Term.subst 0 (.Var 0) F0')
          = Term.subst 0 .Qnt (.Lam F0') := by
        show _ = Term.Lam (Term.subst 1 (Term.shift 0 .Qnt) F0')
        rw [Term.subst_var_eq_subst_above F0' 0 (Term.shift 0 .Qnt)
          hocc1']
      rw [hrw]
      exact Par.subst hβ hQ1 0 .qnt
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
          Term.occ 0 ((Term.spine F).2.getD i .Qnt) = 0 := by
        refine List.occ_getD_zero_of_sum 0 _ ?_
        have h0 : Term.occ 0 F = 0 := hocc
        rw [hsF, Term.occ_apps] at h0
        omega
      -- the fresh variable rides in the last argument slot
      have hlast : args'.getD (Term.spine F).2.length .Qnt = .Var 0 := by
        have hp := hpar (Term.spine F).2.length (by
          rw [hsp2eq, List.length_append]
          simp only [List.length_cons, List.length_nil]
          omega)
        have hg : ((Term.spine F).2 ++ [Term.Var 0]).getD
            (Term.spine F).2.length .Qnt = .Var 0 := by
          rw [show (Term.spine F).2.length
              = (Term.spine F).2.length + 0 from _root_.rfl,
            getD_append_right]
          rfl
        rw [hsp2eq, hg] at hp
        generalize hx : args'.getD (Term.spine F).2.length .Qnt = X at hp ⊢
        cases hp with
        | var => rfl
        | dref _ _ hsp2 _ _ => exact Term.noConfusion hsp2
      have hsplit : args' = args'.take (Term.spine F).2.length
          ++ [.Var 0] := by
        rw [← hlast]
        exact (take_getD_self .Qnt args' (Term.spine F).2.length
          (by omega)).symm
      have hpre : ∀ i, i < (Term.spine F).2.length →
          Par β ((Term.spine F).2.getD i .Qnt) (args'.getD i .Qnt) := by
        intro i hi
        have hp := hpar i (by
          rw [hsp2eq, List.length_append]
          simp only [List.length_cons, List.length_nil]
          omega)
        rw [hsp2eq, getD_append_left _ _ i hi] at hp
        exact hp
      have hoccpre : ∀ i, i < (Term.spine F).2.length →
          Term.occ 0 (args'.getD i .Qnt) = 0 := fun i hi =>
        Par.occ_zero hβ (hpre i hi) 0 (hoccas i hi)
      -- the joined spine, shared by both shapes of the eta side
      have hjoin : ∀ (bs : List Term), (Term.spine F).2.length = bs.length →
          (∀ i, i < (Term.spine F).2.length →
            Par β ((Term.spine F).2.getD i .Qnt) (bs.getD i .Qnt)) →
          ∃ QS : List Term, QS.length = (Term.spine F).2.length ∧
            (∀ i, i < (Term.spine F).2.length →
              Par β (Term.subst 0 .Qnt (bs.getD i .Qnt))
                (Term.subst 0 .Qnt (QS.getD i .Qnt))) ∧
            Par β (.Lam (Term.apps b args'))
              (Term.apps b (QS.map (Term.subst 0 .Qnt))) := by
        intro bs hlb hpb
        obtain ⟨QS, hqlen, hqs⟩ := Par.pointwise_join
          ((Term.spine F).2.length)
          (fun i => args'.getD i .Qnt) (fun i => bs.getD i .Qnt)
          (fun i hi => by
            refine IH (t := (Term.spine F).2.getD i .Qnt) ?_
              (hpre i hi) (hpb i hi)
            have h5 := Term.size_spine_arg F
              ((Term.spine F).2.getD i .Qnt) (getD_mem _ i hi)
            omega)
        refine ⟨QS, hqlen, fun i hi => Par.subst hβ (hqs i hi).2 0 .qnt, ?_⟩
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
        rw [Term.subst_apps_closed 0 .Qnt hbc QS] at he
        rw [Term.apps_snoc]
        exact he
      rcases Par.ref_spine_cases hk hF hsF with
        ⟨bs, hFeq, hlb, hpb⟩ | ⟨b2, bs, hb2, hlb, hpb, hFeq⟩
      · -- the head survived on the eta side: unfold it after the cut
        subst hFeq
        obtain ⟨QS, hqlen, hqs, hq2⟩ := hjoin bs hlb hpb
        refine ⟨Term.apps b (QS.map (Term.subst 0 .Qnt)), ?_, hq2⟩
        rw [Term.subst_apps,
          show Term.subst 0 .Qnt (Term.Ref k) = .Ref k from _root_.rfl]
        refine Par.dref (s := Term.apps (.Ref k)
            (bs.map (Term.subst 0 .Qnt))) hk hb
          (by rw [Term.spine_apps (by trivial)])
          (by
            rw [Term.spine_apps (by trivial)]
            simp only [List.length_map]
            omega) ?_
        rw [Term.spine_apps (by trivial)]
        intro i hi
        simp only [List.length_map] at hi
        rw [map_getD (Term.subst 0 .Qnt) .Qnt .Qnt bs i (by omega),
          map_getD (Term.subst 0 .Qnt) .Qnt .Qnt QS i (by omega)]
        exact hqs i (by omega)
      · -- both sides unfolded
        rw [hb] at hb2
        injection hb2 with hbb
        subst hbb
        subst hFeq
        obtain ⟨QS, hqlen, hqs, hq2⟩ := hjoin bs hlb hpb
        refine ⟨Term.apps b (QS.map (Term.subst 0 .Qnt)), ?_, hq2⟩
        rw [Term.subst_apps_closed 0 .Qnt hbc bs]
        refine Par.apps_congr (Par.refl b) (by
          simp only [List.length_map]
          omega) ?_
        intro i hi
        simp only [List.length_map] at hi
        rw [map_getD (Term.subst 0 .Qnt) .Qnt .Qnt bs i (by omega),
          map_getD (Term.subst 0 .Qnt) .Qnt .Qnt QS i (by omega)]
        exact hqs i (by omega)
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
      exact ⟨Term.subst 0 .Qnt F3, Par.subst hβ hF31 0 .qnt,
        Par.subst hβ hF32 0 .qnt⟩
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
  | @typ g g' hg =>
    cases h2 with
    | typ hg2 =>
      obtain ⟨g3, h31, h32⟩ := IH (t := g) (by
        simp only [Term.size] at hsz; omega) hg hg2
      exact ⟨.Typ g3, .typ h31, .typ h32⟩
    | dref _ _ hsp _ _ => exact Term.noConfusion hsp
  | qnt =>
    cases h2 with
    | qnt => exact ⟨_, .qnt, .qnt⟩
    | dref _ _ hsp _ _ => exact Term.noConfusion hsp
  | qua =>
    cases h2 with
    | qua => exact ⟨_, .qua, .qua⟩
    | dref _ _ hsp _ _ => exact Term.noConfusion hsp
  | @min a a' b b' ha hb =>
    have iha : ∀ {p2 : Term}, Par β a p2 →
        ∃ q2, Par β a' q2 ∧ Par β p2 q2 := fun h2' =>
      IH (t := a) (by simp only [Term.size] at hsz; omega) ha h2'
    have ihb : ∀ {p2 : Term}, Par β b p2 →
        ∃ q2, Par β b' q2 ∧ Par β p2 q2 := fun h2' =>
      IH (t := b) (by simp only [Term.size] at hsz; omega) hb h2'
    cases h2 with
    | min ha2 hb2 =>
      obtain ⟨a3, ha31, ha32⟩ := iha ha2
      obtain ⟨b3, hb31, hb32⟩ := ihb hb2
      exact ⟨.Min a3 b3, .min ha31 hb31, .min ha32 hb32⟩
    | minLM hb2 =>
      cases Par.qua_inv ha
      obtain ⟨b3, hb31, hb32⟩ := ihb hb2
      exact ⟨b3, .minLM hb31, hb32⟩
    | minLN =>
      cases Par.qua_inv ha
      exact ⟨_, .minLN, .qua⟩
    | minRM ha2 =>
      cases Par.qua_inv hb
      obtain ⟨a3, ha31, ha32⟩ := iha ha2
      exact ⟨a3, .minRM ha31, ha32⟩
    | minRN =>
      cases Par.qua_inv hb
      exact ⟨_, .minRN, .qua⟩
    | minLL =>
      cases Par.qua_inv ha
      cases Par.qua_inv hb
      exact ⟨_, .minLL, .qua⟩
    | dref _ _ hsp _ _ => exact Term.noConfusion hsp
  | @minLM b b' hb =>
    have ihb : ∀ {p2 : Term}, Par β b p2 →
        ∃ q2, Par β p1 q2 ∧ Par β p2 q2 := fun h2' =>
      IH (t := b) (by simp only [Term.size] at hsz; omega) hb h2'
    cases h2 with
    | min ha2 hb2 =>
      cases Par.qua_inv ha2
      obtain ⟨b3, hb31, hb32⟩ := ihb hb2
      exact ⟨b3, hb31, .minLM hb32⟩
    | minLM hb2 => exact ihb hb2
    | minRM ha2 =>
      cases Par.qua_inv ha2
      cases Par.qua_inv hb
      exact ⟨_, .qua, .qua⟩
    | minRN =>
      cases Par.qua_inv hb
      exact ⟨_, .qua, .qua⟩
    | dref _ _ hsp _ _ => exact Term.noConfusion hsp
  | minLN =>
    cases h2 with
    | min ha2 hb2 =>
      cases Par.qua_inv ha2
      exact ⟨_, .qua, .minLN⟩
    | minLN => exact ⟨_, .qua, .qua⟩
    | minRM ha2 =>
      cases Par.qua_inv ha2
      exact ⟨_, .qua, .qua⟩
    | minRN => exact ⟨_, .qua, .qua⟩
    | dref _ _ hsp _ _ => exact Term.noConfusion hsp
  | @minRM a a' ha =>
    have iha : ∀ {p2 : Term}, Par β a p2 →
        ∃ q2, Par β p1 q2 ∧ Par β p2 q2 := fun h2' =>
      IH (t := a) (by simp only [Term.size] at hsz; omega) ha h2'
    cases h2 with
    | min ha2 hb2 =>
      cases Par.qua_inv hb2
      obtain ⟨a3, ha31, ha32⟩ := iha ha2
      exact ⟨a3, ha31, .minRM ha32⟩
    | minLM hb2 =>
      cases Par.qua_inv hb2
      cases Par.qua_inv ha
      exact ⟨_, .qua, .qua⟩
    | minLN =>
      cases Par.qua_inv ha
      exact ⟨_, .qua, .qua⟩
    | minRM ha2 => exact iha ha2
    | dref _ _ hsp _ _ => exact Term.noConfusion hsp
  | minRN =>
    cases h2 with
    | min ha2 hb2 =>
      cases Par.qua_inv hb2
      exact ⟨_, .qua, .minRN⟩
    | minLM hb2 =>
      cases Par.qua_inv hb2
      exact ⟨_, .qua, .qua⟩
    | minLN => exact ⟨_, .qua, .qua⟩
    | minRN => exact ⟨_, .qua, .qua⟩
    | dref _ _ hsp _ _ => exact Term.noConfusion hsp
  | minLL =>
    cases h2 with
    | min ha2 hb2 =>
      cases Par.qua_inv ha2
      cases Par.qua_inv hb2
      exact ⟨_, .qua, .minLL⟩
    | minLL => exact ⟨_, .qua, .qua⟩
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
          Par β ((Term.spine t).2.getD i .Qnt) (cs.getD i .Qnt)) →
        ∀ i, i < (Term.spine t).2.length →
        ∃ q, Par β (args'.getD i .Qnt) q ∧
          Par β (cs.getD i .Qnt) q := by
      intro cs hcs i hi
      refine IH (t := (Term.spine t).2.getD i .Qnt) ?_ (hpar i hi)
        (hcs i hi)
      have h5 := Term.size_spine_arg t ((Term.spine t).2.getD i .Qnt)
        (getD_mem _ i hi)
      omega
    have hL2 : (Term.spine t).2.length = args'.length := hlen'
    rcases Par.ref_spine_cases hk h2 hs with
      ⟨bs, hp2eq, hlb, hpb⟩ | ⟨b2, bs, hb2, hlb, hpb, hp2eq⟩
    · subst hp2eq
      have hL3 : (Term.spine t).2.length = bs.length := hlb
      obtain ⟨qs, hqlen, hqs⟩ := Par.pointwise_join
        ((Term.spine t).2.length)
        (fun i => args'.getD i .Qnt) (fun i => bs.getD i .Qnt)
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
        (fun i => args'.getD i .Qnt) (fun i => bs.getD i .Qnt)
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
    | rwtr hf2 => exact ihf hf2
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
            = .App (Term.subst 0 .Qnt G') a2 := by
          show Term.App (Term.subst 0 a2 G')
            (if 0 = 0 then a2 else _) = _
          rw [if_pos _root_.rfl,
            Term.occ_zero_subst_irrel G' 0 a2 .Qnt hocc']
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
            = .App (Term.subst 0 .Qnt G') a' := by
          show Term.App (Term.subst 0 a' G')
            (if 0 = 0 then a' else _) = _
          rw [if_pos _root_.rfl,
            Term.occ_zero_subst_irrel G' 0 a' .Qnt hocc']
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
            Par β ((Term.spine (Term.App f a)).2.getD i .Qnt)
              (cs.getD i .Qnt)) →
          ∀ i, i < (Term.spine (Term.App f a)).2.length →
          ∃ q2, Par β (args2'.getD i .Qnt) q2 ∧
            Par β (cs.getD i .Qnt) q2 := by
        intro cs hcs i hi
        refine IH (t := (Term.spine (Term.App f a)).2.getD i .Qnt) ?_
          (hps2 i hi) (hcs i hi)
        have h5 := Term.size_spine_arg (Term.App f a)
          ((Term.spine (Term.App f a)).2.getD i .Qnt) (getD_mem _ i hi)
        omega
      have hL2 : (Term.spine (Term.App f a)).2.length = args2'.length :=
        hlen2'
      rcases Par.ref_spine_cases hk2 h1' hs with
        ⟨bs, hp1eq, hlb, hpb⟩ | ⟨b3, bs, hb3, hlb, hpb, hp1eq⟩
      · rw [hp1eq]
        have hL3 : (Term.spine (Term.App f a)).2.length = bs.length := hlb
        obtain ⟨qs, hqlen, hqs⟩ := Par.pointwise_join
          ((Term.spine (Term.App f a)).2.length)
          (fun i => args2'.getD i .Qnt) (fun i => bs.getD i .Qnt)
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
          (fun i => args2'.getD i .Qnt) (fun i => bs.getD i .Qnt)
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

-- confluence over a closed book
theorem church_rosser_closed (hβ : Book.Closed β)
    (h1 : Red β .strong a b) (h2 : Red β .strong a c) :
    ∃ d, Red β .strong b d ∧ Red β .strong c d := by
  obtain ⟨d, hd1, hd2⟩ :=
    ParRed.confluent hβ (ParRed.of_red h1) (ParRed.of_red h2)
  exact ⟨d, hd1.red hβ, hd2.red hβ⟩

-- ============================================================================
-- METATHEORY §B3 — the reduction kit: steps and runs commute with shift
-- and substitution (closed book), a substituted argument reduces under
-- its term, and conversion is an equivalence and a congruence.
-- ============================================================================

theorem Step.shift (hβ : Book.Closed β) (s : Step β p a b) :
    ∀ d, Step β p (Term.shift d a) (Term.shift d b) := by
  induction s with
  | beta => intro d; rw [Term.shift_subst0]; exact .beta
  | let_ => intro d; rw [Term.shift_subst0]; exact .let_
  | @dref k dd b s hk hb hsp hlen =>
    intro d
    have hc := (hβ.defn hk).2 _ hb
    have hs := Term.spine_shift hsp (by trivial) (d := d) rfl
    rw [Term.shift_apps, Term.shift_closed b 0 d hc (Nat.zero_le d)]
    have h := Step.dref (p := p) (s := Term.shift d s) hk hb (by rw [hs])
      (by rw [hs]; simpa using hlen)
    simpa [hs] using h
  | @drefS k dd b s hp hk hb hsp =>
    intro d
    have hc := (hβ.defn hk).2 _ hb
    have hs := Term.spine_shift hsp (by trivial) (d := d) rfl
    rw [Term.shift_apps, Term.shift_closed b 0 d hc (Nat.zero_le d)]
    have h := Step.drefS (s := Term.shift d s) hp hk hb (by rw [hs])
    simpa [hs] using h
  | aref hk h0 => intro d; exact .aref hk h0
  | matc h1 h2 h3 h4 =>
    intro d
    simp only [Term.shift, Term.shift_apps, List.map_append]
    exact .matc h1 h2 (by simp [h3]) (by simp [h4])
  | matm hne =>
    intro d
    simp only [Term.shift, Term.shift_apps]
    exact .matm hne
  | rwt => intro d; exact .rwt
  | minLM => intro d; exact .minLM
  | minLN => intro d; exact .minLN
  | minRM => intro d; exact .minRM
  | minRN => intro d; exact .minRN
  | minLL => intro d; exact .minLL
  | eta hp hocc =>
    intro d
    rw [Term.shift_subst_ge _ d 0 .Qnt (Nat.zero_le d)]
    simp only [Term.shift, Nat.zero_lt_succ, ↓reduceIte]
    exact .eta hp (by rw [Term.occ_shift_lt _ 0 (d + 1) (by omega)]; exact hocc)
  | typ_g hp _ ih => intro d; exact .typ_g hp (ih d)
  | min_a _ ih => intro d; exact .min_a (ih d)
  | min_b _ ih => intro d; exact .min_b (ih d)
  | all_a hp _ ih => intro d; exact .all_a hp (ih d)
  | all_b hp _ ih => intro d; exact .all_b hp (ih (d + 1))
  | lam_f hp _ ih => intro d; exact .lam_f hp (ih (d + 1))
  | app_f _ ih => intro d; exact .app_f (ih d)
  | app_a _ ih => intro d; exact .app_a (ih d)
  | mat_h _ ih => intro d; exact .mat_h (ih d)
  | mat_m _ ih => intro d; exact .mat_m (ih d)
  | eql_a _ ih => intro d; exact .eql_a (ih d)
  | eql_b _ ih => intro d; exact .eql_b (ih d)
  | eql_t _ ih => intro d; exact .eql_t (ih d)
  | rwt_e _ ih => intro d; exact .rwt_e (ih d)
  | rwt_p _ ih => intro d; exact .rwt_p (ih d)
  | rwt_f _ ih => intro d; exact .rwt_f (ih d)
  | let_v _ ih => intro d; exact .let_v (ih d)
  | let_b hp _ ih => intro d; exact .let_b hp (ih (d + 1))

theorem Step.subst (hβ : Book.Closed β) (s : Step β p a b) :
    ∀ d w, Step β p (Term.subst d w a) (Term.subst d w b) := by
  induction s with
  | beta => intro d w; rw [Term.subst_subst0]; exact .beta
  | let_ => intro d w; rw [Term.subst_subst0]; exact .let_
  | @dref k dd b s hk hb hsp hlen =>
    intro d w
    have hc := (hβ.defn hk).2 _ hb
    have hs := Term.spine_subst hsp (by trivial) (d := d) (w := w) rfl
    rw [Term.subst_apps, Term.subst_closed b 0 d w hc (Nat.zero_le d)]
    have h := Step.dref (p := p) (s := Term.subst d w s) hk hb (by rw [hs])
      (by rw [hs]; simpa using hlen)
    simpa [hs] using h
  | @drefS k dd b s hp hk hb hsp =>
    intro d w
    have hc := (hβ.defn hk).2 _ hb
    have hs := Term.spine_subst hsp (by trivial) (d := d) (w := w) rfl
    rw [Term.subst_apps, Term.subst_closed b 0 d w hc (Nat.zero_le d)]
    have h := Step.drefS (s := Term.subst d w s) hp hk hb (by rw [hs])
    simpa [hs] using h
  | aref hk h0 => intro d w; exact .aref hk h0
  | matc h1 h2 h3 h4 =>
    intro d w
    simp only [Term.subst, Term.subst_apps, List.map_append]
    exact .matc h1 h2 (by simp [h3]) (by simp [h4])
  | matm hne =>
    intro d w
    simp only [Term.subst, Term.subst_apps]
    exact .matm hne
  | rwt => intro d w; exact .rwt
  | minLM => intro d w; exact .minLM
  | minLN => intro d w; exact .minLN
  | minRM => intro d w; exact .minRM
  | minRN => intro d w; exact .minRN
  | minLL => intro d w; exact .minLL
  | @eta F hp hocc =>
    intro d w
    rw [Term.subst_subst0]
    have h0 : Term.subst (d + 1) (Term.shift 0 w) (Term.Var 0) = .Var 0 := by
      simp only [Term.subst]
      rw [if_neg (by omega), if_neg (by omega)]
    show Step β p (.Lam (.App (Term.subst (d + 1) (Term.shift 0 w) F)
      (Term.subst (d + 1) (Term.shift 0 w) (.Var 0)))) _
    rw [h0]
    exact .eta hp (Term.occ_subst_lt_zero F (d + 1) 0 (Term.shift 0 w)
      (by omega) hocc (Term.occ_shift_self w 0))
  | typ_g hp _ ih => intro d w; exact .typ_g hp (ih d w)
  | min_a _ ih => intro d w; exact .min_a (ih d w)
  | min_b _ ih => intro d w; exact .min_b (ih d w)
  | all_a hp _ ih => intro d w; exact .all_a hp (ih d w)
  | all_b hp _ ih => intro d w; exact .all_b hp (ih (d + 1) _)
  | lam_f hp _ ih => intro d w; exact .lam_f hp (ih (d + 1) _)
  | app_f _ ih => intro d w; exact .app_f (ih d w)
  | app_a _ ih => intro d w; exact .app_a (ih d w)
  | mat_h _ ih => intro d w; exact .mat_h (ih d w)
  | mat_m _ ih => intro d w; exact .mat_m (ih d w)
  | eql_a _ ih => intro d w; exact .eql_a (ih d w)
  | eql_b _ ih => intro d w; exact .eql_b (ih d w)
  | eql_t _ ih => intro d w; exact .eql_t (ih d w)
  | rwt_e _ ih => intro d w; exact .rwt_e (ih d w)
  | rwt_p _ ih => intro d w; exact .rwt_p (ih d w)
  | rwt_f _ ih => intro d w; exact .rwt_f (ih d w)
  | let_v _ ih => intro d w; exact .let_v (ih d w)
  | let_b hp _ ih => intro d w; exact .let_b hp (ih (d + 1) _)

-- a substituted term reduces when its argument does (strong: the
-- argument's copies sit under binders)
theorem Step.substR (hβ : Book.Closed β) : ∀ (t : Term) (d : Nat) {w w' : Term},
    Step β .strong w w' → Red β .strong (Term.subst d w t) (Term.subst d w' t) := by
  intro t
  induction t with
  | Var i =>
    intro d w w' s
    simp only [Term.subst]
    split
    · exact Red.one s
    · split <;> exact .refl
  | Ref k => intro d w w' _; exact .refl
  | Typ g ih => intro d w w' s; exact Red.typ_g (ih d s)
  | Qnt => intro d w w' _; exact .refl
  | Qua q => intro d w w' _; exact .refl
  | Min a b iha ihb =>
    intro d w w' s; exact (Red.min_a (iha d s)).trans (Red.min_b (ihb d s))
  | All q A B ihA ihB =>
    intro d w w' s
    exact (Red.all_a (ihA d s)).trans (Red.all_b (ihB (d + 1) (s.shift hβ 0)))
  | Lam f ih => intro d w w' s; exact Red.lam_f (ih (d + 1) (s.shift hβ 0))
  | App f a ihf iha =>
    intro d w w' s; exact (Red.app_f (ihf d s)).trans (Red.app_a (iha d s))
  | Adt a r => intro d w w' _; exact .refl
  | Ctr a c => intro d w w' _; exact .refl
  | Mat a c h m ihh ihm =>
    intro d w w' s; exact (Red.mat_h (ihh d s)).trans (Red.mat_m (ihm d s))
  | Efq => intro d w w' _; exact .refl
  | Eql x y T ihx ihy ihT =>
    intro d w w' s
    exact ((Red.eql_a (ihx d s)).trans (Red.eql_b (ihy d s))).trans
      (Red.eql_t (ihT d s))
  | Rfl => intro d w w' _; exact .refl
  | Rwt e P f ihe ihP ihf =>
    intro d w w' s
    exact ((Red.rwt_e (ihe d s)).trans (Red.rwt_p (ihP d s))).trans
      (Red.rwt_f (ihf d s))
  | Let q v b ihv ihb =>
    intro d w w' s
    exact (Red.let_v (ihv d s)).trans (Red.let_b (ihb (d + 1) (s.shift hβ 0)))

theorem Red.shift (hβ : Book.Closed β) (r : Red β p a b) (d : Nat) :
    Red β p (Term.shift d a) (Term.shift d b) := by
  induction r with
  | refl => exact .refl
  | step s _ ih => exact .step (s.shift hβ d) ih

theorem Red.subst (hβ : Book.Closed β) (r : Red β p a b) (d : Nat) (w : Term) :
    Red β p (Term.subst d w a) (Term.subst d w b) := by
  induction r with
  | refl => exact .refl
  | step s _ ih => exact .step (s.subst hβ d w) ih

theorem Red.substR (hβ : Book.Closed β) (r : Red β .strong w w') (d : Nat)
    (t : Term) : Red β .strong (Term.subst d w t) (Term.subst d w' t) := by
  induction r with
  | refl => exact .refl
  | step s _ ih => exact (Step.substR hβ t d s).trans ih

-- conversion: an equivalence (transitivity is confluence), stable under
-- shift and substitution, and a congruence
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

theorem Conv.red_l (hβ : Book.Closed β) (r : Red β .strong a a')
    (h : Conv β a b) : Conv β a' b :=
  (Conv.of_red_rev r).trans hβ h

theorem Conv.red_r (hβ : Book.Closed β) (r : Red β .strong b b')
    (h : Conv β a b) : Conv β a b' :=
  h.trans hβ (Conv.of_red r)

theorem Conv.shift (hβ : Book.Closed β) (h : Conv β a b) (d : Nat) :
    Conv β (Term.shift d a) (Term.shift d b) := by
  obtain ⟨c, h1, h2⟩ := h
  exact ⟨Term.shift d c, h1.shift hβ d, h2.shift hβ d⟩

theorem Conv.subst (hβ : Book.Closed β) (ht : Conv β t t') (hw : Conv β w w')
    (d : Nat) : Conv β (Term.subst d w t) (Term.subst d w' t') := by
  obtain ⟨c, h1, h2⟩ := ht
  obtain ⟨e, g1, g2⟩ := hw
  exact ⟨Term.subst d e c, (h1.subst hβ d w).trans (Red.substR hβ g1 d c),
    (h2.subst hβ d w').trans (Red.substR hβ g2 d c)⟩

theorem Conv.substR (hβ : Book.Closed β) (hw : Conv β w w') (d : Nat)
    (t : Term) : Conv β (Term.subst d w t) (Term.subst d w' t) :=
  Conv.subst hβ (Conv.refl t) hw d

theorem Conv.typ (h : Conv β g g') : Conv β (.Typ g) (.Typ g') := by
  obtain ⟨c, h1, h2⟩ := h
  exact ⟨.Typ c, Red.typ_g h1, Red.typ_g h2⟩

theorem Conv.min (ha : Conv β a a') (hb : Conv β b b') :
    Conv β (.Min a b) (.Min a' b') := by
  obtain ⟨ca, ha1, ha2⟩ := ha
  obtain ⟨cb, hb1, hb2⟩ := hb
  exact ⟨.Min ca cb, (Red.min_a ha1).trans (Red.min_b hb1),
    (Red.min_a ha2).trans (Red.min_b hb2)⟩

theorem Conv.all (hA : Conv β A A') (hB : Conv β B B') :
    Conv β (.All q A B) (.All q A' B') := by
  obtain ⟨cA, hA1, hA2⟩ := hA
  obtain ⟨cB, hB1, hB2⟩ := hB
  exact ⟨.All q cA cB, (Red.all_a hA1).trans (Red.all_b hB1),
    (Red.all_a hA2).trans (Red.all_b hB2)⟩

theorem Conv.lam (h : Conv β f f') : Conv β (.Lam f) (.Lam f') := by
  obtain ⟨c, h1, h2⟩ := h
  exact ⟨.Lam c, Red.lam_f h1, Red.lam_f h2⟩

theorem Conv.app (hf : Conv β f f') (ha : Conv β a a') :
    Conv β (.App f a) (.App f' a') := by
  obtain ⟨cf, hf1, hf2⟩ := hf
  obtain ⟨ca, ha1, ha2⟩ := ha
  exact ⟨.App cf ca, (Red.app_f hf1).trans (Red.app_a ha1),
    (Red.app_f hf2).trans (Red.app_a ha2)⟩

theorem Conv.mat (hh : Conv β h h') (hm : Conv β m m') :
    Conv β (.Mat a c h m) (.Mat a c h' m') := by
  obtain ⟨ch, hh1, hh2⟩ := hh
  obtain ⟨cm, hm1, hm2⟩ := hm
  exact ⟨.Mat a c ch cm, (Red.mat_h hh1).trans (Red.mat_m hm1),
    (Red.mat_h hh2).trans (Red.mat_m hm2)⟩

theorem Conv.eql (hx : Conv β x x') (hy : Conv β y y') (hT : Conv β T T') :
    Conv β (.Eql x y T) (.Eql x' y' T') := by
  obtain ⟨cx, hx1, hx2⟩ := hx
  obtain ⟨cy, hy1, hy2⟩ := hy
  obtain ⟨cT, hT1, hT2⟩ := hT
  exact ⟨.Eql cx cy cT,
    ((Red.eql_a hx1).trans (Red.eql_b hy1)).trans (Red.eql_t hT1),
    ((Red.eql_a hx2).trans (Red.eql_b hy2)).trans (Red.eql_t hT2)⟩

theorem Conv.rwt (he : Conv β e e') (hP : Conv β P P') (hf : Conv β f f') :
    Conv β (.Rwt e P f) (.Rwt e' P' f') := by
  obtain ⟨ce, he1, he2⟩ := he
  obtain ⟨cP, hP1, hP2⟩ := hP
  obtain ⟨cf, hf1, hf2⟩ := hf
  exact ⟨.Rwt ce cP cf,
    ((Red.rwt_e he1).trans (Red.rwt_p hP1)).trans (Red.rwt_f hf1),
    ((Red.rwt_e he2).trans (Red.rwt_p hP2)).trans (Red.rwt_f hf2)⟩

theorem Conv.let_ (hv : Conv β v v') (hb : Conv β b b') :
    Conv β (.Let q v b) (.Let q v' b') := by
  obtain ⟨cv, hv1, hv2⟩ := hv
  obtain ⟨cb, hb1, hb2⟩ := hb
  exact ⟨.Let q cv cb, (Red.let_v hv1).trans (Red.let_b hb1),
    (Red.let_v hv2).trans (Red.let_b hb2)⟩

-- pointwise conversion on lists
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
    | cons hr2 hrest2 => exact .cons ⟨_, hr, hr2⟩ (ih hrest2)

theorem Conv.apps (hh : Conv β h h') : ∀ {as as' : List Term},
    Convs β as as' → Conv β (Term.apps h as) (Term.apps h' as') := by
  intro as
  induction as generalizing h h' with
  | nil => intro as' hc; cases hc; exact hh
  | cons x xs ih =>
    intro as' hc
    cases hc with
    | cons hx hxs => exact ih (Conv.app hh hx) hxs

-- ============================================================================
-- METATHEORY §B4 — typed terms are closed; Book.Ok closes the book, which
-- discharges claim (1).
-- ============================================================================

theorem Term.closed_of_subst : ∀ (t : Term) (n d : Nat) (w : Term), d ≤ n →
    Term.Closed n (Term.subst d w t) → Term.Closed (n + 1) t := by
  intro t
  induction t with
  | Var i =>
    intro n d w hd h
    simp only [Term.subst] at h
    show i < n + 1
    split at h
    · omega
    · split at h
      · simp only [Term.Closed] at h; omega
      · simp only [Term.Closed] at h; omega
  | Ref k => intro n d w _ _; trivial
  | Typ g ih => intro n d w hd h; exact ih n d w hd h
  | Qnt => intro n d w _ _; trivial
  | Qua q => intro n d w _ _; trivial
  | Min a b iha ihb =>
    intro n d w hd h; exact ⟨iha n d w hd h.1, ihb n d w hd h.2⟩
  | All q A B ihA ihB =>
    intro n d w hd h
    exact ⟨ihA n d w hd h.1, ihB (n + 1) (d + 1) _ (by omega) h.2⟩
  | Lam f ih => intro n d w hd h; exact ih (n + 1) (d + 1) _ (by omega) h
  | App f a ihf iha =>
    intro n d w hd h; exact ⟨ihf n d w hd h.1, iha n d w hd h.2⟩
  | Adt a r => intro n d w _ _; trivial
  | Ctr a c => intro n d w _ _; trivial
  | Mat a c h m ihh ihm =>
    intro n d w hd hh; exact ⟨ihh n d w hd hh.1, ihm n d w hd hh.2⟩
  | Efq => intro n d w _ _; trivial
  | Eql x y T ihx ihy ihT =>
    intro n d w hd h
    exact ⟨ihx n d w hd h.1, ihy n d w hd h.2.1, ihT n d w hd h.2.2⟩
  | Rfl => intro n d w _ _; trivial
  | Rwt e P f ihe ihP ihf =>
    intro n d w hd h
    exact ⟨ihe n d w hd h.1, ihP n d w hd h.2.1, ihf n d w hd h.2.2⟩
  | Let q v b ihv ihb =>
    intro n d w hd h
    exact ⟨ihv n d w hd h.1, ihb (n + 1) (d + 1) _ (by omega) h.2⟩

theorem Term.Closed.shift : ∀ (t : Term) (n d : Nat), t.Closed n →
    (Term.shift d t).Closed (n + 1) := by
  intro t
  induction t with
  | Var i =>
    intro n d h
    simp only [Term.shift]
    split <;> simp only [Term.Closed] at h ⊢ <;> omega
  | Ref k => intro n d _; trivial
  | Typ g ih => intro n d h; exact ih n d h
  | Qnt => intro n d _; trivial
  | Qua q => intro n d _; trivial
  | Min a b iha ihb => intro n d h; exact ⟨iha n d h.1, ihb n d h.2⟩
  | All q A B ihA ihB => intro n d h; exact ⟨ihA n d h.1, ihB (n + 1) (d + 1) h.2⟩
  | Lam f ih => intro n d h; exact ih (n + 1) (d + 1) h
  | App f a ihf iha => intro n d h; exact ⟨ihf n d h.1, iha n d h.2⟩
  | Adt a r => intro n d _; trivial
  | Ctr a c => intro n d _; trivial
  | Mat a c h m ihh ihm => intro n d hh; exact ⟨ihh n d hh.1, ihm n d hh.2⟩
  | Efq => intro n d _; trivial
  | Eql x y T ihx ihy ihT =>
    intro n d h; exact ⟨ihx n d h.1, ihy n d h.2.1, ihT n d h.2.2⟩
  | Rfl => intro n d _; trivial
  | Rwt e P f ihe ihP ihf =>
    intro n d h; exact ⟨ihe n d h.1, ihP n d h.2.1, ihf n d h.2.2⟩
  | Let q v b ihv ihb => intro n d h; exact ⟨ihv n d h.1, ihb (n + 1) (d + 1) h.2⟩

theorem Term.closed_apps : ∀ (as : List Term) (h : Term) (m : Nat),
    h.Closed m → (∀ x ∈ as, x.Closed m) → (Term.apps h as).Closed m := by
  intro as
  induction as with
  | nil => intro h m hh _; exact hh
  | cons a as ih =>
    intro h m hh has
    exact ih (.App h a) m ⟨hh, has a (by simp)⟩ (fun x hx => has x (by simp [hx]))

theorem Ctx.get_lt : ∀ {Γ : Ctx} {i : Nat} {b : Bind},
    Ctx.get Γ i = some b → i < Γ.length := by
  intro Γ
  induction Γ with
  | nil => intro i b h; cases h
  | cons A Γ ih =>
    intro i b h
    cases i with
    | zero => exact Nat.succ_pos _
    | succ i =>
      simp only [Ctx.get, Option.map_eq_some_iff] at h
      obtain ⟨b', hb', _⟩ := h
      exact Nat.succ_lt_succ (ih hb')

theorem Check.closed (h : Check β Φ L sp q Γ t T π u) : t.Closed Γ.length := by
  induction h with
  | var hg => exact Ctx.get_lt hg
  | ref _ _ _ _ => trivial
  | refA _ _ => trivial
  | adt _ => trivial
  | ctr _ _ _ => trivial
  | typ _ ih => exact ih
  | qnt => trivial
  | qua => trivial
  | min _ _ iha ihb => exact ⟨iha, ihb⟩
  | all _ _ ihA ihB => exact ⟨ihA, ihB⟩
  | lam _ _ _ _ ihf => exact ihf
  | app _ _ ihf ihx => exact ⟨ihf, ihx⟩
  | appLam ha _ ih =>
    exact ⟨Term.closed_of_subst _ _ 0 _ (Nat.zero_le _) ih, ha⟩
  | let_ _ _ _ _ ihv _ ihb => exact ⟨ihv, ihb⟩
  | eql _ _ _ ihT iha ihb => exact ⟨iha, ihb, ihT⟩
  | rfl _ => trivial
  | rwt _ _ _ ihe ihP ihf => exact ⟨ihe, ihP, ihf⟩
  | mat _ _ _ _ _ _ _ _ _ ihh ihm => exact ⟨ihh, ihm⟩
  | efq _ _ _ => trivial
  | cnv _ _ iht => exact iht

-- a constructor telescope that passes adt_valid's walk is closed
theorem FTele.closed : ∀ (fn : Nat) (ps : List Term) (Γ : Ctx) (i : Nat) (T : Term),
    FTele a r ps fn T → CtrOk β k pn G Γ i T → (∀ p ∈ ps, p.Closed Γ.length) →
    T.Closed Γ.length := by
  intro fn
  induction fn with
  | zero =>
    intro ps Γ i T hT _ hps
    have hT' : T = Term.apps (.Adt a r) ps := hT
    rw [hT']
    exact Term.closed_apps ps _ _ trivial hps
  | succ fn ih =>
    intro ps Γ i T hT hok hps
    obtain ⟨qf, F, B, hTeq, hB⟩ := hT
    subst hTeq
    obtain ⟨⟨π, hF⟩, hokB⟩ := hok
    refine ⟨hF.closed, ih _ _ _ _ hB hokB ?_⟩
    intro p hp
    obtain ⟨p', hp', rfl⟩ := List.mem_map.mp hp
    exact Term.Closed.shift p' _ 0 (hps p' hp')

theorem WTele.closed : ∀ (pn : Nat) (ps : List Term) (Γ : Ctx) (i : Nat) (T : Term),
    WTele a r ps pn fn T → CtrOk β k pn' G Γ i T → (∀ p ∈ ps, p.Closed Γ.length) →
    T.Closed Γ.length := by
  intro pn
  induction pn with
  | zero => intro ps Γ i T hT hok hps; exact FTele.closed fn ps Γ i T hT hok hps
  | succ pn ih =>
    intro ps Γ i T hT hok hps
    obtain ⟨q, K, B, hTeq, hB⟩ := hT
    subst hTeq
    obtain ⟨⟨π, hK⟩, hokB⟩ := hok
    refine ⟨hK.closed, ih _ _ _ _ hB hokB ?_⟩
    intro p hp
    rw [List.mem_append] at hp
    rcases hp with hp | hp
    · obtain ⟨p', hp', rfl⟩ := List.mem_map.mp hp
      exact Term.Closed.shift p' _ 0 (hps p' hp')
    · rw [List.mem_singleton] at hp
      subst hp
      show 0 < Γ.length + 1
      omega

theorem Book.Ok.closed (hok : Book.Ok β) : Book.Closed β := by
  intro k t hk
  have h := hok k t hk
  cases t with
  | adt A =>
    obtain ⟨⟨π, hs⟩, G, _, hc⟩ := h
    refine ⟨hs.closed, ?_⟩
    intro c C hcc
    obtain ⟨hshape, hok'⟩ := hc c C hcc
    have hshape' : WTele k [] [] A.pn C.fn C.ty := hshape
    exact WTele.closed A.pn [] [] 0 C.ty hshape' hok' (fun _ h => nomatch h)
  | defn d =>
    obtain ⟨⟨π, hs⟩, _, _, hb⟩ := h
    refine ⟨hs.closed, ?_⟩
    intro b hbb
    obtain ⟨_, π', u, hc⟩ := hb b hbb
    exact hc.closed

theorem church_rosser_holds : church_rosser := by
  intro β a b c hok h1 h2
  exact church_rosser_closed hok.closed h1 h2

-- ============================================================================
-- METATHEORY §C — conversion and fitting. Head stability under strong
-- reduction (a rigid head keeps its spine; Typ, All and Eql reduce only
-- their parts), the head tag that separates the stable head classes, the
-- Conv and Le inversions, and the preorders KLe and Le.
-- ============================================================================

-- a rigid head never steps and heads no redex: its spine reduces only
-- in the arguments
def Term.Rigid : Term → Prop
  | .Var _ | .Qnt | .Qua _ | .Adt _ _ | .Ctr _ _ | .Efq | .Rfl => True
  | _ => False

theorem Term.Rigid.isHead (h : Term.Rigid t) : t.IsHead := by
  cases t <;> simp_all [Term.Rigid, Term.IsHead]

theorem Step.rigid_inv (s : Step β p t u) : ∀ {h : Term} {as : List Term},
    t = Term.apps h as → h.Rigid → ∃ bs, u = Term.apps h bs ∧ Reds β p as bs := by
  induction s <;> intro h as heq hr
  all_goals try
    (rcases apps_shape _ _ _ heq.symm with ⟨rfl, rfl⟩ | ⟨_, _, _, hX⟩
     · cases hr
     · cases hX)
  all_goals try
    (obtain ⟨ys, _, hfy⟩ := Term.app_eq_apps hr.isHead heq
     rcases apps_shape _ _ _ hfy.symm with ⟨rfl, rfl⟩ | ⟨_, _, _, hX⟩
     · cases hr
     · cases hX)
  case dref hsp _ =>
    rw [heq, Term.spine_apps hr.isHead] at hsp; subst hsp; cases hr
  case drefS hsp =>
    rw [heq, Term.spine_apps hr.isHead] at hsp; subst hsp; cases hr
  case app_f ih =>
    obtain ⟨ys, rfl, rfl⟩ := Term.app_eq_apps hr.isHead heq
    obtain ⟨bs, rfl, hred⟩ := ih rfl hr
    exact ⟨bs ++ [_], (Term.apps_snoc _ _ _).symm, hred.append (.cons .refl .nil)⟩
  case app_a sa _ =>
    obtain ⟨ys, rfl, rfl⟩ := Term.app_eq_apps hr.isHead heq
    exact ⟨ys ++ [_], (Term.apps_snoc _ _ _).symm,
      (Reds.refl ys).append (.cons (Red.one sa) .nil)⟩

theorem Red.rigid_inv (r : Red β p t u) : ∀ {h : Term} {as : List Term},
    t = Term.apps h as → h.Rigid → ∃ bs, u = Term.apps h bs ∧ Reds β p as bs := by
  induction r with
  | refl => intro h as heq _; exact ⟨as, heq, Reds.refl as⟩
  | step s _ ih =>
    intro h as heq hr
    obtain ⟨bs, hu, hred⟩ := s.rigid_inv heq hr
    obtain ⟨cs, hu2, hred2⟩ := ih hu hr
    exact ⟨cs, hu2, hred.trans hred2⟩

theorem Red.rigid_eq (r : Red β p h u) (hr : h.Rigid) : u = h := by
  obtain ⟨bs, hu, hred⟩ := r.rigid_inv (as := []) rfl hr
  cases hred; exact hu

theorem Red.adt_inv (r : Red β p (Term.apps (.Adt a rr) ps) u) :
    ∃ ps', u = Term.apps (.Adt a rr) ps' ∧ Reds β p ps ps' := r.rigid_inv rfl trivial

theorem Red.ctr_inv (r : Red β p (Term.apps (.Ctr a c) xs) u) :
    ∃ xs', u = Term.apps (.Ctr a c) xs' ∧ Reds β p xs xs' := r.rigid_inv rfl trivial

theorem Red.qnt_inv (r : Red β p .Qnt u) : u = .Qnt := r.rigid_eq trivial
theorem Red.qua_inv (r : Red β p (.Qua q) u) : u = .Qua q := r.rigid_eq trivial
theorem Red.rfl_inv (r : Red β p .Rfl u) : u = .Rfl := r.rigid_eq trivial
theorem Red.efq_inv (r : Red β p .Efq u) : u = .Efq := r.rigid_eq trivial

-- Typ, All and Eql reduce only in their parts
theorem Step.typ_inv (s : Step β p (.Typ g) u) : ∃ g', u = .Typ g' ∧ Step β p g g' := by
  cases s with
  | typ_g _ sg => exact ⟨_, rfl, sg⟩
  | dref _ _ hsp _ | drefS _ _ _ hsp => exact Term.noConfusion hsp

theorem Red.typ_inv (r : Red β p (.Typ g) u) : ∃ g', u = .Typ g' ∧ Red β p g g' := by
  generalize ht : Term.Typ g = t at r
  induction r generalizing g with
  | refl => exact ⟨g, ht.symm, .refl⟩
  | step s _ ih =>
    subst ht
    obtain ⟨g1, rfl, sg⟩ := Step.typ_inv s
    obtain ⟨g2, hu, hg⟩ := ih rfl
    exact ⟨g2, hu, .step sg hg⟩

theorem Step.all_inv (s : Step β p (.All q A B) u) :
    ∃ A' B', u = .All q A' B' ∧ Red β p A A' ∧ Red β p B B' := by
  cases s with
  | all_a _ sA => exact ⟨_, _, rfl, Red.one sA, .refl⟩
  | all_b _ sB => exact ⟨_, _, rfl, .refl, Red.one sB⟩
  | dref _ _ hsp _ | drefS _ _ _ hsp => exact Term.noConfusion hsp

theorem Red.all_inv (r : Red β p (.All q A B) u) :
    ∃ A' B', u = .All q A' B' ∧ Red β p A A' ∧ Red β p B B' := by
  generalize ht : Term.All q A B = t at r
  induction r generalizing A B with
  | refl => exact ⟨A, B, ht.symm, .refl, .refl⟩
  | step s _ ih =>
    subst ht
    obtain ⟨A1, B1, rfl, hA1, hB1⟩ := Step.all_inv s
    obtain ⟨A2, B2, hu, hA2, hB2⟩ := ih rfl
    exact ⟨A2, B2, hu, hA1.trans hA2, hB1.trans hB2⟩

theorem Step.eql_inv (s : Step β p (.Eql a b T) u) :
    ∃ a' b' T', u = .Eql a' b' T' ∧ Red β p a a' ∧ Red β p b b' ∧ Red β p T T' := by
  cases s with
  | eql_a sa => exact ⟨_, _, _, rfl, Red.one sa, .refl, .refl⟩
  | eql_b sb => exact ⟨_, _, _, rfl, .refl, Red.one sb, .refl⟩
  | eql_t st => exact ⟨_, _, _, rfl, .refl, .refl, Red.one st⟩
  | dref _ _ hsp _ | drefS _ _ _ hsp => exact Term.noConfusion hsp

theorem Red.eql_inv (r : Red β p (.Eql a b T) u) :
    ∃ a' b' T', u = .Eql a' b' T' ∧ Red β p a a' ∧ Red β p b b' ∧ Red β p T T' := by
  generalize ht : Term.Eql a b T = t at r
  induction r generalizing a b T with
  | refl => exact ⟨a, b, T, ht.symm, .refl, .refl, .refl⟩
  | step s _ ih =>
    subst ht
    obtain ⟨a1, b1, T1, rfl, h1, h2, h3⟩ := Step.eql_inv s
    obtain ⟨a2, b2, T2, hu, g1, g2, g3⟩ := ih rfl
    exact ⟨a2, b2, T2, hu, h1.trans g1, h2.trans g2, h3.trans g3⟩

-- a meet reduces in its parts until one side is a literal that fires
theorem Red.min_inv (r : Red β p (.Min a b) c) :
    (∃ a' b', c = .Min a' b' ∧ Red β p a a' ∧ Red β p b b') ∨
    (Red β p a (.Qua .Many) ∧ Red β p b c) ∨
    (Red β p b (.Qua .Many) ∧ Red β p a c) ∨
    (Red β p a (.Qua .None) ∧ c = .Qua .None) ∨
    (Red β p b (.Qua .None) ∧ c = .Qua .None) ∨
    (Red β p a (.Qua .Lone) ∧ Red β p b (.Qua .Lone) ∧ c = .Qua .Lone) := by
  generalize ht : Term.Min a b = t at r
  induction r generalizing a b with
  | refl => exact .inl ⟨a, b, ht.symm, .refl, .refl⟩
  | step s r ih =>
    subst ht
    cases s with
    | minLM => exact .inr (.inl ⟨.refl, r⟩)
    | minLN => exact .inr (.inr (.inr (.inl ⟨.refl, r.qua_inv⟩)))
    | minRM => exact .inr (.inr (.inl ⟨.refl, r⟩))
    | minRN => exact .inr (.inr (.inr (.inr (.inl ⟨.refl, r.qua_inv⟩))))
    | minLL => exact .inr (.inr (.inr (.inr (.inr ⟨.refl, .refl, r.qua_inv⟩))))
    | min_a sa =>
      rcases ih rfl with ⟨a', b', rfl, ha, hb⟩ | ⟨ha, hb⟩ | ⟨hb, ha⟩ | ⟨ha, hc⟩ | ⟨hb, hc⟩ | ⟨ha, hb, hc⟩
      · exact .inl ⟨a', b', rfl, .step sa ha, hb⟩
      · exact .inr (.inl ⟨.step sa ha, hb⟩)
      · exact .inr (.inr (.inl ⟨hb, .step sa ha⟩))
      · exact .inr (.inr (.inr (.inl ⟨.step sa ha, hc⟩)))
      · exact .inr (.inr (.inr (.inr (.inl ⟨hb, hc⟩))))
      · exact .inr (.inr (.inr (.inr (.inr ⟨.step sa ha, hb, hc⟩))))
    | min_b sb =>
      rcases ih rfl with ⟨a', b', rfl, ha, hb⟩ | ⟨ha, hb⟩ | ⟨hb, ha⟩ | ⟨ha, hc⟩ | ⟨hb, hc⟩ | ⟨ha, hb, hc⟩
      · exact .inl ⟨a', b', rfl, ha, .step sb hb⟩
      · exact .inr (.inl ⟨ha, .step sb hb⟩)
      · exact .inr (.inr (.inl ⟨.step sb hb, ha⟩))
      · exact .inr (.inr (.inr (.inl ⟨ha, hc⟩)))
      · exact .inr (.inr (.inr (.inr (.inl ⟨.step sb hb, hc⟩))))
      · exact .inr (.inr (.inr (.inr (.inr ⟨ha, .step sb hb, hc⟩))))
    | dref _ _ hsp _ | drefS _ _ _ hsp => exact Term.noConfusion hsp

-- the head tag: the spine head's constructor. Tags below 6 are the heads
-- a rule can rewrite (Ref, Min, Lam, Mat, Rwt, Let); a stable head keeps
-- its tag along any reduction
def Term.tag : Term → Nat
  | .Ref _       => 0
  | .Min _ _     => 1
  | .Lam _       => 2
  | .Mat _ _ _ _ => 3
  | .Rwt _ _ _   => 4
  | .Let _ _ _   => 5
  | .App f _     => Term.tag f
  | .Var _       => 6
  | .Typ _       => 7
  | .Qnt         => 8
  | .Qua _       => 9
  | .All _ _ _   => 10
  | .Adt _ _     => 11
  | .Ctr _ _     => 12
  | .Efq         => 13
  | .Eql _ _ _   => 14
  | .Rfl         => 15

@[simp] theorem Term.tag_apps : ∀ (as : List Term) (h : Term),
    Term.tag (Term.apps h as) = Term.tag h := by
  intro as
  induction as with
  | nil => intro h; rfl
  | cons a as ih => intro h; exact ih (.App h a)

theorem Term.tag_spine (t : Term) : Term.tag t = Term.tag (Term.spine t).1 := by
  induction t <;> simp [Term.tag, Term.spine, *]

theorem Step.tag (s : Step β p a b) (hs : 6 ≤ a.tag) : b.tag = a.tag := by
  induction s
  case dref hsp _ => rw [Term.tag_spine, hsp] at hs; simp [Term.tag] at hs
  case drefS hsp => rw [Term.tag_spine, hsp] at hs; simp [Term.tag] at hs
  all_goals simp_all [Term.tag]

theorem Red.tag (r : Red β p a b) (hs : 6 ≤ a.tag) : b.tag = a.tag := by
  induction r with
  | refl => rfl
  | step s _ ih => exact (ih (s.tag hs ▸ hs)).trans (s.tag hs)

theorem Conv.tag (h : Conv β a b) (ha : 6 ≤ a.tag) (hb : 6 ≤ b.tag) : a.tag = b.tag := by
  obtain ⟨c, h1, h2⟩ := h
  exact (h1.tag ha).symm.trans (h2.tag hb)

theorem Le.tag (h : Le β a b) (ha : 6 ≤ a.tag) (hb : 6 ≤ b.tag) : a.tag = b.tag := by
  induction h with
  | conv hc => exact hc.tag ha hb
  | red r1 r2 _ ih => rw [← r1.tag ha, ← r2.tag hb]; exact ih (r1.tag ha ▸ ha) (r2.tag hb ▸ hb)
  | typ => rfl
  | all => rfl
  | adt => simp [Term.tag]

theorem Le.conv_symm (h : Conv β a b) : Le β b a := .conv h.symm

-- head clashes: a fit between two stable head forms of different tags
-- is False (Le.tag / Conv.tag decide every pair; these are the named ones)
theorem Le.typ_all (h : Le β (.Typ g) (.All q A B)) : False := by simpa [Term.tag] using h.tag
theorem Le.all_typ (h : Le β (.All q A B) (.Typ g)) : False := by simpa [Term.tag] using h.tag
theorem Le.typ_adt (h : Le β (.Typ g) (Term.apps (.Adt a r) ps)) : False := by simpa [Term.tag] using h.tag
theorem Le.adt_typ (h : Le β (Term.apps (.Adt a r) ps) (.Typ g)) : False := by simpa [Term.tag] using h.tag
theorem Le.typ_eql (h : Le β (.Typ g) (.Eql x y T)) : False := by simpa [Term.tag] using h.tag
theorem Le.eql_typ (h : Le β (.Eql x y T) (.Typ g)) : False := by simpa [Term.tag] using h.tag
theorem Le.typ_qnt (h : Le β (.Typ g) .Qnt) : False := by simpa [Term.tag] using h.tag
theorem Le.qnt_typ (h : Le β .Qnt (.Typ g)) : False := by simpa [Term.tag] using h.tag
theorem Le.all_adt (h : Le β (.All q A B) (Term.apps (.Adt a r) ps)) : False := by simpa [Term.tag] using h.tag
theorem Le.adt_all (h : Le β (Term.apps (.Adt a r) ps) (.All q A B)) : False := by simpa [Term.tag] using h.tag
theorem Le.all_eql (h : Le β (.All q A B) (.Eql x y T)) : False := by simpa [Term.tag] using h.tag
theorem Le.eql_all (h : Le β (.Eql x y T) (.All q A B)) : False := by simpa [Term.tag] using h.tag
theorem Le.all_qnt (h : Le β (.All q A B) .Qnt) : False := by simpa [Term.tag] using h.tag
theorem Le.qnt_all (h : Le β .Qnt (.All q A B)) : False := by simpa [Term.tag] using h.tag
theorem Le.adt_eql (h : Le β (Term.apps (.Adt a r) ps) (.Eql x y T)) : False := by simpa [Term.tag] using h.tag
theorem Le.eql_adt (h : Le β (.Eql x y T) (Term.apps (.Adt a r) ps)) : False := by simpa [Term.tag] using h.tag
theorem Le.adt_qnt (h : Le β (Term.apps (.Adt a r) ps) .Qnt) : False := by simpa [Term.tag] using h.tag
theorem Le.qnt_adt (h : Le β .Qnt (Term.apps (.Adt a r) ps)) : False := by simpa [Term.tag] using h.tag
theorem Le.eql_qnt (h : Le β (.Eql x y T) .Qnt) : False := by simpa [Term.tag] using h.tag
theorem Le.qnt_eql (h : Le β .Qnt (.Eql x y T)) : False := by simpa [Term.tag] using h.tag

-- Le.adt's index form and the inductive Convs coincide
theorem Convs.get (h : Convs β xs ys) : ∀ (i : Nat) x y,
    xs[i]? = some x → ys[i]? = some y → Conv β x y := by
  induction h with
  | nil => intro i x y hx; simp at hx
  | cons hc _ ih =>
    intro i x y hx hy
    cases i with
    | zero => simp at hx hy; subst hx hy; exact hc
    | succ i => exact ih i x y hx hy

theorem Convs.of_index : ∀ {xs ys : List Term}, xs.length = ys.length →
    (∀ (i : Nat) x y, xs[i]? = some x → ys[i]? = some y → Conv β x y) → Convs β xs ys := by
  intro xs
  induction xs with
  | nil => intro ys hl _; cases ys with | nil => exact .nil | cons => simp at hl
  | cons x xs ih =>
    intro ys hl hc
    cases ys with
    | nil => simp at hl
    | cons y ys =>
      exact .cons (hc 0 x y rfl rfl)
        (ih (by simp at hl; omega) (fun i a b ha hb => hc (i + 1) a b ha hb))

-- the Conv inversions: conversion within a stable head class is componentwise
theorem Conv.typ_inv (h : Conv β (.Typ g) (.Typ g')) : Conv β g g' := by
  obtain ⟨c, h1, h2⟩ := h
  obtain ⟨g1, rfl, hg1⟩ := h1.typ_inv
  obtain ⟨g2, he, hg2⟩ := h2.typ_inv
  cases he; exact ⟨_, hg1, hg2⟩

theorem Conv.qua_inv (h : Conv β (.Qua q) (.Qua q')) : q = q' := by
  obtain ⟨c, h1, h2⟩ := h
  cases h1.qua_inv.symm.trans h2.qua_inv; rfl

theorem Conv.all_inv (h : Conv β (.All q A B) (.All q' A' B')) :
    q = q' ∧ Conv β A A' ∧ Conv β B B' := by
  obtain ⟨c, h1, h2⟩ := h
  obtain ⟨A1, B1, rfl, hA1, hB1⟩ := h1.all_inv
  obtain ⟨A2, B2, he, hA2, hB2⟩ := h2.all_inv
  cases he; exact ⟨rfl, ⟨A1, hA1, hA2⟩, ⟨B1, hB1, hB2⟩⟩

theorem Conv.eql_inv (h : Conv β (.Eql a b T) (.Eql a' b' T')) :
    Conv β a a' ∧ Conv β b b' ∧ Conv β T T' := by
  obtain ⟨c, h1, h2⟩ := h
  obtain ⟨a1, b1, T1, rfl, g1, g2, g3⟩ := h1.eql_inv
  obtain ⟨a2, b2, T2, he, f1, f2, f3⟩ := h2.eql_inv
  cases he; exact ⟨⟨a1, g1, f1⟩, ⟨b1, g2, f2⟩, ⟨T1, g3, f3⟩⟩

theorem Conv.adt_inv (h : Conv β (Term.apps (.Adt a r) ps) (Term.apps (.Adt a' r') ps')) :
    a = a' ∧ r = r' ∧ Convs β ps ps' := by
  obtain ⟨c, h1, h2⟩ := h
  obtain ⟨bs1, rfl, g1⟩ := h1.adt_inv
  obtain ⟨bs2, he, g2⟩ := h2.adt_inv
  obtain ⟨hh, rfl⟩ := Term.apps_head_inv (by trivial) (by trivial) he
  cases hh; exact ⟨rfl, rfl, g1.convs g2⟩

theorem Conv.ctr_inv (h : Conv β (Term.apps (.Ctr a c) xs) (Term.apps (.Ctr a' c') xs')) :
    a = a' ∧ c = c' ∧ Convs β xs xs' := by
  obtain ⟨d, h1, h2⟩ := h
  obtain ⟨bs1, rfl, g1⟩ := h1.ctr_inv
  obtain ⟨bs2, he, g2⟩ := h2.ctr_inv
  obtain ⟨hh, rfl⟩ := Term.apps_head_inv (by trivial) (by trivial) he
  cases hh; exact ⟨rfl, rfl, g1.convs g2⟩

-- KLe: reflexive, closed under reduction into either side (the easy way),
-- and its three inversions
theorem KLe.refl (g : Term) : KLe β g g := .conv (Conv.refl g)

theorem KLe.of_red_l (hr : Red β .strong g g') (h : KLe β g' k) : KLe β g k := by
  induction h with
  | many hm => exact .many (hr.trans hm)
  | lone hl hq => exact .lone hl hq
  | minL hm k1 k2 _ _ => exact .minL (hr.trans hm) k1 k2
  | minR1 hm _ ih => exact .minR1 hm (ih hr)
  | minR2 hm _ ih => exact .minR2 hm (ih hr)
  | conv hc => obtain ⟨c, h1, h2⟩ := hc; exact .conv ⟨c, hr.trans h1, h2⟩

theorem KLe.of_red_r (hr : Red β .strong k k') (h : KLe β g k') : KLe β g k := by
  induction h with
  | many hm => exact .many hm
  | lone hl hq => exact .lone (hr.trans hl) hq
  | minL hm _ _ ih1 ih2 => exact .minL hm (ih1 hr) (ih2 hr)
  | minR1 hm k1 _ => exact .minR1 (hr.trans hm) k1
  | minR2 hm k2 _ => exact .minR2 (hr.trans hm) k2
  | conv hc => obtain ⟨c, h1, h2⟩ := hc; exact .conv ⟨c, h1, hr.trans h2⟩

theorem KLe.many_inv (h : KLe β g (.Qua .Many)) : KLe β g k := by
  generalize hM : Term.Qua .Many = M at h
  induction h with
  | many hm => exact .many hm
  | lone hl hq => subst hM; exact absurd hl.qua_inv (by intro e; cases e; exact hq rfl)
  | minL hm _ _ ih1 ih2 => exact .minL hm (ih1 hM) (ih2 hM)
  | minR1 hm _ _ => subst hM; cases hm.qua_inv
  | minR2 hm _ _ => subst hM; cases hm.qua_inv
  | conv hc => subst hM; obtain ⟨c, h1, h2⟩ := hc; rw [h2.qua_inv] at h1; exact .many h1

theorem KLe.lone_inv (hq : q ≠ .Many) (h : KLe β (.Qua q) k) : KLe β g k := by
  generalize hQ : Term.Qua q = Q at h
  induction h with
  | many hm => subst hQ; exact absurd hm.qua_inv (by intro e; cases e; exact hq rfl)
  | lone hl hq' => exact .lone hl hq'
  | minL hm _ _ _ _ => subst hQ; cases hm.qua_inv
  | minR1 hm _ ih => exact .minR1 hm (ih hQ)
  | minR2 hm _ ih => exact .minR2 hm (ih hQ)
  | conv hc => subst hQ; obtain ⟨c, h1, h2⟩ := hc; rw [h1.qua_inv] at h2; exact .lone h2 hq

theorem KLe.minL_inv (h : KLe β (.Min h1 h2) k) : KLe β h1 k ∧ KLe β h2 k := by
  generalize hH : Term.Min h1 h2 = H at h
  induction h with
  | many hm =>
    subst hH
    rcases hm.min_inv with ⟨_, _, he, _⟩ | ⟨ha, hb⟩ | ⟨hb, ha⟩ | ⟨_, he⟩ | ⟨_, he⟩ | ⟨_, _, he⟩
    all_goals try cases he
    all_goals exact ⟨.many ha, .many hb⟩
  | lone hl hq => exact ⟨.lone hl hq, .lone hl hq⟩
  | minL hm k1 k2 _ _ =>
    subst hH
    rcases hm.min_inv with ⟨_, _, he, ha, hb⟩ | ⟨ha, hb⟩ | ⟨hb, ha⟩ | ⟨_, he⟩ | ⟨_, he⟩ | ⟨_, _, he⟩
    all_goals try cases he
    · exact ⟨.of_red_l ha k1, .of_red_l hb k2⟩
    · exact ⟨.many ha, .of_red_l hb (.minL .refl k1 k2)⟩
    · exact ⟨.of_red_l ha (.minL .refl k1 k2), .many hb⟩
  | minR1 hm _ ih => obtain ⟨i1, i2⟩ := ih hH; exact ⟨.minR1 hm i1, .minR1 hm i2⟩
  | minR2 hm _ ih => obtain ⟨i1, i2⟩ := ih hH; exact ⟨.minR2 hm i1, .minR2 hm i2⟩
  | conv hc =>
    subst hH
    obtain ⟨c, hm, hk⟩ := hc
    rcases hm.min_inv with ⟨_, _, rfl, ha, hb⟩ | ⟨ha, hb⟩ | ⟨hb, ha⟩ | ⟨ha, rfl⟩ | ⟨hb, rfl⟩ | ⟨ha, hb, rfl⟩
    · exact ⟨.minR1 hk (.conv ⟨_, ha, .refl⟩), .minR2 hk (.conv ⟨_, hb, .refl⟩)⟩
    · exact ⟨.many ha, .conv ⟨_, hb, hk⟩⟩
    · exact ⟨.conv ⟨_, ha, hk⟩, .many hb⟩
    all_goals exact ⟨.lone hk (by intro e; cases e), .lone hk (by intro e; cases e)⟩

-- Le: reflexive, and every derivation is a conversion or a reduction of
-- both sides into one of the three directional head forms
theorem Le.refl (t : Term) : Le β t t := .conv (Conv.refl t)

theorem Le.inv (h : Le β a b) :
    Conv β a b ∨
    (∃ g h', Red β .strong a (.Typ g) ∧ Red β .strong b (.Typ h') ∧ KLe β g h') ∨
    (∃ q A B A' B', Red β .strong a (.All q A B) ∧ Red β .strong b (.All q A' B') ∧
      Le β A' A ∧ Le β B B') ∨
    (∃ x r ps r' ps', Red β .strong a (Term.apps (.Adt x r) ps) ∧
      Red β .strong b (Term.apps (.Adt x r') ps') ∧
      (∀ c, c ∈ r' → c ∈ r) ∧ ps.length = ps'.length ∧
      (∀ (i : Nat) p p', ps[i]? = some p → ps'[i]? = some p' → Conv β p p')) := by
  induction h with
  | conv hc => exact .inl hc
  | red r1 r2 _ ih =>
    rcases ih with ⟨c, h1, h2⟩ | ⟨g, h', h1, h2, hk⟩ | ⟨q, A, B, A', B', h1, h2, hA, hB⟩
      | ⟨x, r, ps, r', ps', h1, h2, hr, hl, hc⟩
    · exact .inl ⟨c, r1.trans h1, r2.trans h2⟩
    · exact .inr (.inl ⟨g, h', r1.trans h1, r2.trans h2, hk⟩)
    · exact .inr (.inr (.inl ⟨q, A, B, A', B', r1.trans h1, r2.trans h2, hA, hB⟩))
    · exact .inr (.inr (.inr ⟨x, r, ps, r', ps', r1.trans h1, r2.trans h2, hr, hl, hc⟩))
  | typ hk => exact .inr (.inl ⟨_, _, .refl, .refl, hk⟩)
  | all hA hB => exact .inr (.inr (.inl ⟨_, _, _, _, _, .refl, .refl, hA, hB⟩))
  | adt hr hl hc => exact .inr (.inr (.inr ⟨_, _, _, _, _, .refl, .refl, hr, hl, hc⟩))

-- ----------------------------------------------------------------------------
-- with confluence: pointwise conversion composes, KLe and Le are closed
-- under reduction on either side and transitive, and a fit between two
-- head forms inverts componentwise
-- ----------------------------------------------------------------------------

theorem Convs.of_reds (h1 : Reds β .strong xs xs1) (h2 : Reds β .strong ys ys1)
    (hc : Convs β xs1 ys1) : Convs β xs ys := by
  induction h1 generalizing ys ys1 with
  | nil => cases hc; cases h2; exact .nil
  | cons r1 _ ih =>
    cases hc with
    | cons c hcs =>
      cases h2 with
      | cons r2 hrs =>
        obtain ⟨d, c1, c2⟩ := c
        exact .cons ⟨d, r1.trans c1, r2.trans c2⟩ (ih hrs hcs)

theorem Convs.red_l (hβ : Book.Closed β) (hr : Reds β .strong xs xs1) (hc : Convs β xs ys) :
    Convs β xs1 ys := by
  induction hr generalizing ys with
  | nil => exact hc
  | cons r _ ih => cases hc with | cons c hcs => exact .cons (Conv.red_l hβ r c) (ih hcs)

theorem Convs.red_r (hβ : Book.Closed β) (hr : Reds β .strong ys ys1) (hc : Convs β xs ys) :
    Convs β xs ys1 := by
  induction hr generalizing xs with
  | nil => exact hc
  | cons r _ ih => cases hc with | cons c hcs => exact .cons (Conv.red_r hβ r c) (ih hcs)

theorem Convs.trans (hβ : Book.Closed β) (h1 : Convs β xs ys) (h2 : Convs β ys zs) :
    Convs β xs zs := by
  induction h1 generalizing zs with
  | nil => exact h2
  | cons c1 _ ih => cases h2 with | cons c2 h2s => exact .cons (c1.trans hβ c2) (ih h2s)

theorem Convs.map (hc : Convs β xs ys) (F : Term → Term)
    (hF : ∀ p p', Conv β p p' → Conv β (F p) (F p')) : Convs β (xs.map F) (ys.map F) := by
  induction hc with
  | nil => exact .nil
  | cons c _ ih => exact .cons (hF _ _ c) ih

theorem KLe.red_l (hβ : Book.Closed β) (h : KLe β g k) :
    ∀ g', Red β .strong g g' → KLe β g' k := by
  induction h with
  | many hm =>
    intro g' hr
    obtain ⟨d, h1, h2⟩ := church_rosser_closed hβ hm hr
    rw [h1.qua_inv] at h2; exact .many h2
  | lone hl hq => intro g' _; exact .lone hl hq
  | minL hm _ _ ih1 ih2 =>
    intro g' hr
    obtain ⟨d, h1, h2⟩ := church_rosser_closed hβ hm hr
    refine .of_red_l h2 ?_
    rcases h1.min_inv with ⟨_, _, rfl, ha, hb⟩ | ⟨_, hb⟩ | ⟨_, ha⟩ | ⟨ha, rfl⟩ | ⟨hb, rfl⟩ | ⟨ha, _, rfl⟩
    · exact .minL .refl (ih1 _ ha) (ih2 _ hb)
    · exact ih2 _ hb
    · exact ih1 _ ha
    · exact ih1 _ ha
    · exact ih2 _ hb
    · exact ih1 _ ha
  | minR1 hm _ ih => intro g' hr; exact .minR1 hm (ih g' hr)
  | minR2 hm _ ih => intro g' hr; exact .minR2 hm (ih g' hr)
  | conv hc => intro g' hr; exact .conv (Conv.red_l hβ hr hc)

theorem KLe.red_r (hβ : Book.Closed β) (h : KLe β g k) :
    ∀ k', Red β .strong k k' → KLe β g k' := by
  induction h with
  | many hm => intro k' _; exact .many hm
  | lone hl hq =>
    intro k' hr
    obtain ⟨d, h1, h2⟩ := church_rosser_closed hβ hl hr
    rw [h1.qua_inv] at h2; exact .lone h2 hq
  | minL hm _ _ ih1 ih2 => intro k' hr; exact .minL hm (ih1 k' hr) (ih2 k' hr)
  | minR1 hm _ ih =>
    intro k' hr
    obtain ⟨d, h1, h2⟩ := church_rosser_closed hβ hm hr
    refine .of_red_r h2 ?_
    rcases h1.min_inv with ⟨_, _, rfl, ha, _⟩ | ⟨ha, _⟩ | ⟨_, ha⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, _, rfl⟩
    · exact .minR1 .refl (ih _ ha)
    · exact (ih _ ha).many_inv
    · exact ih _ ha
    all_goals exact .lone .refl (by intro e; cases e)
  | minR2 hm _ ih =>
    intro k' hr
    obtain ⟨d, h1, h2⟩ := church_rosser_closed hβ hm hr
    refine .of_red_r h2 ?_
    rcases h1.min_inv with ⟨_, _, rfl, _, hb⟩ | ⟨_, hb⟩ | ⟨hb, _⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, _, rfl⟩
    · exact .minR2 .refl (ih _ hb)
    · exact ih _ hb
    · exact (ih _ hb).many_inv
    all_goals exact .lone .refl (by intro e; cases e)
  | conv hc => intro k' hr; exact .conv (Conv.red_r hβ hr hc)

theorem KLe.trans (hβ : Book.Closed β) (h1 : KLe β g h) : ∀ k, KLe β h k → KLe β g k := by
  induction h1 with
  | many hm => intro k _; exact .many hm
  | lone hl hq => intro k h2; exact KLe.lone_inv hq (h2.red_l hβ _ hl)
  | minL hm _ _ ih1 ih2 => intro k h2; exact .minL hm (ih1 k h2) (ih2 k h2)
  | minR1 hm _ ih => intro k h2; exact ih k (h2.red_l hβ _ hm).minL_inv.1
  | minR2 hm _ ih => intro k h2; exact ih k (h2.red_l hβ _ hm).minL_inv.2
  | conv hc => intro k h2; obtain ⟨c, hc1, hc2⟩ := hc; exact .of_red_l hc1 (h2.red_l hβ _ hc2)

theorem KLe.shift (hβ : Book.Closed β) (h : KLe β g k) :
    ∀ d, KLe β (Term.shift d g) (Term.shift d k) := by
  induction h with
  | many hm => intro d; exact .many (hm.shift hβ d)
  | lone hl hq => intro d; exact .lone (hl.shift hβ d) hq
  | minL hm _ _ ih1 ih2 => intro d; exact .minL (hm.shift hβ d) (ih1 d) (ih2 d)
  | minR1 hm _ ih => intro d; exact .minR1 (hm.shift hβ d) (ih d)
  | minR2 hm _ ih => intro d; exact .minR2 (hm.shift hβ d) (ih d)
  | conv hc => intro d; exact .conv (hc.shift hβ d)

theorem KLe.subst (hβ : Book.Closed β) (h : KLe β g k) :
    ∀ d w, KLe β (Term.subst d w g) (Term.subst d w k) := by
  induction h with
  | many hm => intro d w; exact .many (hm.subst hβ d w)
  | lone hl hq => intro d w; exact .lone (hl.subst hβ d w) hq
  | minL hm _ _ ih1 ih2 => intro d w; exact .minL (hm.subst hβ d w) (ih1 d w) (ih2 d w)
  | minR1 hm _ ih => intro d w; exact .minR1 (hm.subst hβ d w) (ih d w)
  | minR2 hm _ ih => intro d w; exact .minR2 (hm.subst hβ d w) (ih d w)
  | conv hc => intro d w; exact .conv (hc.subst hβ (Conv.refl w) d)

theorem Le.red_lr (hβ : Book.Closed β) (h : Le β a b) :
    (∀ a', Red β .strong a a' → Le β a' b) ∧ (∀ b', Red β .strong b b' → Le β a b') := by
  induction h with
  | conv hc =>
    exact ⟨fun _ r => .conv (Conv.red_l hβ r hc), fun _ r => .conv (Conv.red_r hβ r hc)⟩
  | red r1 r2 _ ih =>
    refine ⟨fun a' r => ?_, fun b' r => ?_⟩
    · obtain ⟨d, h1, h2⟩ := church_rosser_closed hβ r1 r
      exact .red h2 r2 (ih.1 d h1)
    · obtain ⟨d, h1, h2⟩ := church_rosser_closed hβ r2 r
      exact .red r1 h2 (ih.2 d h1)
  | typ hk =>
    refine ⟨fun a' r => ?_, fun b' r => ?_⟩
    · obtain ⟨_, rfl, hg⟩ := r.typ_inv; exact .typ (hk.red_l hβ _ hg)
    · obtain ⟨_, rfl, hh⟩ := r.typ_inv; exact .typ (hk.red_r hβ _ hh)
  | all _ _ ihA ihB =>
    refine ⟨fun a' r => ?_, fun b' r => ?_⟩
    · obtain ⟨A1, B1, rfl, hA, hB⟩ := r.all_inv; exact .all (ihA.2 A1 hA) (ihB.1 B1 hB)
    · obtain ⟨A1, B1, rfl, hA, hB⟩ := r.all_inv; exact .all (ihA.1 A1 hA) (ihB.2 B1 hB)
  | adt hsub hlen hconv =>
    refine ⟨fun a' r => ?_, fun b' r => ?_⟩
    · obtain ⟨ps1, rfl, hps⟩ := r.adt_inv
      have hc := Convs.red_l hβ hps (Convs.of_index hlen hconv)
      exact .adt hsub hc.length hc.get
    · obtain ⟨ps1, rfl, hps⟩ := r.adt_inv
      have hc := Convs.red_r hβ hps (Convs.of_index hlen hconv)
      exact .adt hsub hc.length hc.get

theorem Le.red_l (hβ : Book.Closed β) (r : Red β .strong a a') (h : Le β a b) : Le β a' b :=
  (h.red_lr hβ).1 a' r

theorem Le.red_r (hβ : Book.Closed β) (r : Red β .strong b b') (h : Le β a b) : Le β a b' :=
  (h.red_lr hβ).2 b' r

theorem Le.trans_lr (hβ : Book.Closed β) (h : Le β a b) :
    (∀ c, Le β b c → Le β a c) ∧ (∀ x, Le β x a → Le β x b) := by
  induction h with
  | conv hc =>
    obtain ⟨d, h1, h2⟩ := hc
    exact ⟨fun c hbc => .red h1 .refl (hbc.red_l hβ h2),
           fun x hxa => .red .refl h2 (hxa.red_r hβ h1)⟩
  | red r1 r2 _ ih =>
    exact ⟨fun c hbc => .red r1 .refl (ih.1 c (hbc.red_l hβ r2)),
           fun x hxa => .red .refl r2 (ih.2 x (hxa.red_r hβ r1))⟩
  | typ hk =>
    refine ⟨fun c hbc => ?_, fun x hxa => ?_⟩
    · rcases hbc.inv with ⟨d, r1, r2⟩ | ⟨_, _, r1, r2, hk'⟩ | ⟨_, _, _, _, _, r1, _⟩
        | ⟨_, _, _, _, _, r1, _⟩
      · obtain ⟨_, rfl, hh⟩ := r1.typ_inv
        exact .red .refl r2 (.typ (hk.red_r hβ _ hh))
      · obtain ⟨_, he, hh⟩ := r1.typ_inv; cases he
        exact .red .refl r2 (.typ ((hk.red_r hβ _ hh).trans hβ _ hk'))
      · simpa [Term.tag] using r1.tag
      · simpa [Term.tag] using r1.tag
    · rcases hxa.inv with ⟨d, r1, r2⟩ | ⟨_, _, r1, r2, hk'⟩ | ⟨_, _, _, _, _, _, r2, _⟩
        | ⟨_, _, _, _, _, _, r2, _⟩
      · obtain ⟨_, rfl, hg⟩ := r2.typ_inv
        exact .red r1 .refl (.typ (hk.red_l hβ _ hg))
      · obtain ⟨_, he, hg⟩ := r2.typ_inv; cases he
        exact .red r1 .refl (.typ (hk'.trans hβ _ (hk.red_l hβ _ hg)))
      · simpa [Term.tag] using r2.tag
      · simpa [Term.tag] using r2.tag
  | all hA hB ihA ihB =>
    refine ⟨fun c hbc => ?_, fun x hxa => ?_⟩
    · rcases hbc.inv with ⟨d, r1, r2⟩ | ⟨_, _, r1, _⟩ | ⟨_, _, _, C1, C2, r1, r2, hC1, hC2⟩
        | ⟨_, _, _, _, _, r1, _⟩
      · obtain ⟨A1, B1, rfl, hA1, hB1⟩ := r1.all_inv
        exact .red .refl r2 (.all (hA.red_l hβ hA1) (hB.red_r hβ hB1))
      · simpa [Term.tag] using r1.tag
      · obtain ⟨A1, B1, he, hA1, hB1⟩ := r1.all_inv; cases he
        exact .red .refl r2 (.all (ihA.2 C1 (.red .refl hA1 hC1)) (ihB.1 C2 (.red hB1 .refl hC2)))
      · simpa [Term.tag] using r1.tag
    · rcases hxa.inv with ⟨d, r1, r2⟩ | ⟨_, _, _, r2, _⟩ | ⟨_, X1, X2, _, _, r1, r2, hX1, hX2⟩
        | ⟨_, _, _, _, _, _, r2, _⟩
      · obtain ⟨A1, B1, rfl, hA1, hB1⟩ := r2.all_inv
        exact .red r1 .refl (.all (hA.red_r hβ hA1) (hB.red_l hβ hB1))
      · simpa [Term.tag] using r2.tag
      · obtain ⟨A1, B1, he, hA1, hB1⟩ := r2.all_inv; cases he
        exact .red r1 .refl (.all (ihA.1 X1 (.red hA1 .refl hX1)) (ihB.2 X2 (.red .refl hB1 hX2)))
      · simpa [Term.tag] using r2.tag
  | adt hsub hlen hconv =>
    refine ⟨fun c hbc => ?_, fun x hxa => ?_⟩
    · rcases hbc.inv with ⟨d, r1, r2⟩ | ⟨_, _, r1, _⟩ | ⟨_, _, _, _, _, r1, _⟩
        | ⟨_, _, _, _, _, r1, r2, hsub', hlen', hconv'⟩
      · obtain ⟨ps1, rfl, hps⟩ := r1.adt_inv
        have hc := Convs.red_r hβ hps (Convs.of_index hlen hconv)
        exact .red .refl r2 (.adt hsub hc.length hc.get)
      · simpa [Term.tag] using r1.tag
      · simpa [Term.tag] using r1.tag
      · obtain ⟨ps1, he, hps⟩ := r1.adt_inv
        obtain ⟨hh, rfl⟩ := Term.apps_head_inv (by trivial) (by trivial) he; cases hh
        have hc := Convs.trans hβ (Convs.red_r hβ hps (Convs.of_index hlen hconv))
          (Convs.of_index hlen' hconv')
        exact .red .refl r2 (.adt (fun c hc => hsub c (hsub' c hc)) hc.length hc.get)
    · rcases hxa.inv with ⟨d, r1, r2⟩ | ⟨_, _, _, r2, _⟩ | ⟨_, _, _, _, _, _, r2, _⟩
        | ⟨_, _, _, _, _, r1, r2, hsub', hlen', hconv'⟩
      · obtain ⟨ps1, rfl, hps⟩ := r2.adt_inv
        have hc := Convs.red_l hβ hps (Convs.of_index hlen hconv)
        exact .red r1 .refl (.adt hsub hc.length hc.get)
      · simpa [Term.tag] using r2.tag
      · simpa [Term.tag] using r2.tag
      · obtain ⟨ps1, he, hps⟩ := r2.adt_inv
        obtain ⟨hh, rfl⟩ := Term.apps_head_inv (by trivial) (by trivial) he; cases hh
        have hc := Convs.trans hβ (Convs.of_index hlen' hconv')
          (Convs.red_l hβ hps (Convs.of_index hlen hconv))
        exact .red r1 .refl (.adt (fun c hc => hsub' c (hsub c hc)) hc.length hc.get)

theorem Le.trans (hβ : Book.Closed β) (h1 : Le β a b) (h2 : Le β b c) : Le β a c :=
  (h1.trans_lr hβ).1 c h2

theorem Le.conv_l (hβ : Book.Closed β) (hc : Conv β a b) (h : Le β b c) : Le β a c :=
  (Le.conv hc).trans hβ h

theorem Le.conv_r (hβ : Book.Closed β) (h : Le β a b) (hc : Conv β b c) : Le β a c :=
  h.trans hβ (.conv hc)

theorem Le.shift (hβ : Book.Closed β) (h : Le β a b) :
    ∀ d, Le β (Term.shift d a) (Term.shift d b) := by
  induction h with
  | conv hc => intro d; exact .conv (hc.shift hβ d)
  | red r1 r2 _ ih => intro d; exact .red (r1.shift hβ d) (r2.shift hβ d) (ih d)
  | typ hk => intro d; exact .typ (hk.shift hβ d)
  | all _ _ ihA ihB => intro d; exact .all (ihA d) (ihB (d + 1))
  | adt hsub hlen hconv =>
    intro d
    rw [Term.shift_apps, Term.shift_apps]
    have hc := Convs.map (Convs.of_index hlen hconv) (Term.shift d) (fun _ _ h => h.shift hβ d)
    exact .adt hsub hc.length hc.get

theorem Le.subst (hβ : Book.Closed β) (h : Le β a b) :
    ∀ d w, Le β (Term.subst d w a) (Term.subst d w b) := by
  induction h with
  | conv hc => intro d w; exact .conv (hc.subst hβ (Conv.refl w) d)
  | red r1 r2 _ ih => intro d w; exact .red (r1.subst hβ d w) (r2.subst hβ d w) (ih d w)
  | typ hk => intro d w; exact .typ (hk.subst hβ d w)
  | all _ _ ihA ihB => intro d w; exact .all (ihA d w) (ihB (d + 1) (Term.shift 0 w))
  | adt hsub hlen hconv =>
    intro d w
    rw [Term.subst_apps, Term.subst_apps]
    have hc := Convs.map (Convs.of_index hlen hconv) (Term.subst d w)
      (fun _ _ h => h.subst hβ (Conv.refl w) d)
    exact .adt hsub hc.length hc.get

theorem Le.substR (hβ : Book.Closed β) (h : Le β a b) (hw : Conv β w w') (d : Nat) :
    Le β (Term.subst d w a) (Term.subst d w' b) :=
  (h.subst hβ d w).conv_r hβ (hw.substR hβ d b)

-- the Le inversions: align both sides at their head forms, then read the
-- head relation off Le.inv
theorem Le.tag_red (hβ : Book.Closed β) (h : Le β a b) (ra : Red β .strong a a')
    (rb : Red β .strong b b') (ha : 6 ≤ a'.tag) (hb : 6 ≤ b'.tag) : a'.tag = b'.tag :=
  ((h.red_l hβ ra).red_r hβ rb).tag ha hb

theorem Le.typ_inv (hβ : Book.Closed β) (h : Le β a b) (ra : Red β .strong a (.Typ g))
    (rb : Red β .strong b (.Typ k)) : KLe β g k := by
  rcases ((h.red_l hβ ra).red_r hβ rb).inv with hc | ⟨_, _, r1, r2, hk⟩
    | ⟨_, _, _, _, _, r1, _⟩ | ⟨_, _, _, _, _, r1, _⟩
  · exact .conv hc.typ_inv
  · obtain ⟨_, he1, hg⟩ := r1.typ_inv; cases he1
    obtain ⟨_, he2, hk1⟩ := r2.typ_inv; cases he2
    exact (hk.of_red_l hg).of_red_r hk1
  · simpa [Term.tag] using r1.tag
  · simpa [Term.tag] using r1.tag

theorem Le.all_inv (hβ : Book.Closed β) (h : Le β a b) (ra : Red β .strong a (.All q A B))
    (rb : Red β .strong b (.All q' A' B')) : q = q' ∧ Le β A' A ∧ Le β B B' := by
  rcases ((h.red_l hβ ra).red_r hβ rb).inv with hc | ⟨_, _, r1, _⟩
    | ⟨_, _, _, _, _, r1, r2, hA, hB⟩ | ⟨_, _, _, _, _, r1, _⟩
  · obtain ⟨rfl, hA, hB⟩ := hc.all_inv; exact ⟨rfl, .conv hA.symm, .conv hB⟩
  · simpa [Term.tag] using r1.tag
  · obtain ⟨_, _, he1, hA3, hB3⟩ := r1.all_inv; cases he1
    obtain ⟨_, _, he2, hA4, hB4⟩ := r2.all_inv; cases he2
    exact ⟨rfl, .red hA4 hA3 hA, .red hB3 hB4 hB⟩
  · simpa [Term.tag] using r1.tag

theorem Le.adt_inv (hβ : Book.Closed β) (h : Le β a b)
    (ra : Red β .strong a (Term.apps (.Adt x r) ps))
    (rb : Red β .strong b (Term.apps (.Adt x' r') ps')) :
    x = x' ∧ (∀ c, c ∈ r' → c ∈ r) ∧ Convs β ps ps' := by
  rcases ((h.red_l hβ ra).red_r hβ rb).inv with hc | ⟨_, _, r1, _⟩
    | ⟨_, _, _, _, _, r1, _⟩ | ⟨_, _, _, _, _, r1, r2, hsub, hlen, hconv⟩
  · obtain ⟨rfl, rfl, hcs⟩ := hc.adt_inv; exact ⟨rfl, fun _ hm => hm, hcs⟩
  · simpa [Term.tag] using r1.tag
  · simpa [Term.tag] using r1.tag
  · obtain ⟨_, he1, hps1⟩ := r1.adt_inv
    obtain ⟨hh1, rfl⟩ := Term.apps_head_inv (by trivial) (by trivial) he1; cases hh1
    obtain ⟨_, he2, hps2⟩ := r2.adt_inv
    obtain ⟨hh2, rfl⟩ := Term.apps_head_inv (by trivial) (by trivial) he2; cases hh2
    exact ⟨rfl, hsub, Convs.of_reds hps1 hps2 (Convs.of_index hlen hconv)⟩

theorem Le.eql_inv (hβ : Book.Closed β) (h : Le β a b) (ra : Red β .strong a (.Eql x y T))
    (rb : Red β .strong b (.Eql x' y' T')) : Conv β x x' ∧ Conv β y y' ∧ Conv β T T' := by
  rcases ((h.red_l hβ ra).red_r hβ rb).inv with hc | ⟨_, _, r1, _⟩
    | ⟨_, _, _, _, _, r1, _⟩ | ⟨_, _, _, _, _, r1, _⟩
  · exact hc.eql_inv
  all_goals simpa [Term.tag] using r1.tag

theorem Le.ctr_inv (hβ : Book.Closed β) (h : Le β a b)
    (ra : Red β .strong a (Term.apps (.Ctr x c) xs))
    (rb : Red β .strong b (Term.apps (.Ctr x' c') xs')) :
    x = x' ∧ c = c' ∧ Convs β xs xs' := by
  rcases ((h.red_l hβ ra).red_r hβ rb).inv with hc | ⟨_, _, r1, _⟩
    | ⟨_, _, _, _, _, r1, _⟩ | ⟨_, _, _, _, _, r1, _⟩
  · exact hc.ctr_inv
  all_goals simpa [Term.tag] using r1.tag

-- ============================================================================
-- METATHEORY §D0 — typed terms are closed; Book.Ok closes the book
-- ============================================================================

theorem Term.era_closed (q : Quant) (h : Term.Closed n u) :
    Term.Closed n (Term.era q u) := by
  cases q <;> first | trivial | exact h

theorem Check.closed_era (h : Check β Φ L sp q Γ t T π u) : u.Closed Γ.length := by
  induction h with
  | var hg => exact Term.era_closed _ (Ctx.get_lt hg)
  | min _ _ iha ihb => exact Term.era_closed _ ⟨iha, ihb⟩
  | all _ _ _ _ => exact Term.era_closed _ ⟨trivial, trivial⟩
  | lam _ _ _ _ ihf => exact Term.era_closed _ ihf
  | app _ _ ihf ihx => exact Term.era_closed _ ⟨ihf, ihx⟩
  | appLam _ _ ih => exact ih
  | let_ _ _ _ _ ihv _ ihb => exact Term.era_closed _ ⟨ihv, ihb⟩
  | eql _ _ _ _ _ _ => exact Term.era_closed _ ⟨trivial, trivial, trivial⟩
  | rwt _ _ _ ihe _ ihf => exact Term.era_closed _ ⟨ihe, trivial, ihf⟩
  | mat _ _ _ _ _ _ _ _ _ ihh ihm => exact Term.era_closed _ ⟨ihh, ihm⟩
  | cnv _ _ iht => exact iht
  | qnt => trivial
  | _ => exact Term.era_closed _ (by trivial)

-- ============================================================================
-- METATHEORY §D1 — the dead fragment: a None-demand derivation measures
-- nothing and elaborates to the token; any derivation replays dead
-- ============================================================================

theorem Quant.dem_none (q' : Quant) : Quant.dem q' .None = .None := by
  cases q' <;> rfl

theorem Check.none_era (h : Check β Φ L sp q Γ t T π u) : q = .None → u = .Qnt := by
  induction h with
  | appLam _ _ ih => exact ih
  | cnv _ _ ih => exact ih
  | qnt => intro _; exact _root_.rfl
  | _ => intro hq; subst hq; exact _root_.rfl

theorem Check.none_uses (h : Check β Φ L sp q Γ t T π u) : q = .None → π = Uses.zero := by
  induction h with
  | var _ => intro hq; subst hq; funext i; simp [Uses.one, Uses.zero]
  | min _ _ iha ihb =>
    intro hq; subst hq
    rw [iha _root_.rfl, ihb _root_.rfl]; funext i; exact _root_.rfl
  | lam _ _ _ _ ihf => intro hq; subst hq; rw [ihf _root_.rfl]; funext i; exact _root_.rfl
  | app _ _ ihf ihx =>
    intro hq; subst hq
    rw [ihf _root_.rfl, ihx (Quant.dem_none _)]; funext i; exact _root_.rfl
  | appLam _ _ ih => exact ih
  | let_ _ _ _ _ ihv _ ihb =>
    intro hq; subst hq
    rw [ihv (Quant.dem_none _), ihb _root_.rfl]; funext i; exact _root_.rfl
  | rwt _ _ _ ihe _ ihf =>
    intro hq; subst hq
    rw [ihe _root_.rfl, ihf _root_.rfl]; funext i; exact _root_.rfl
  | mat _ _ _ _ _ _ _ _ _ ihh ihm =>
    intro hq; subst hq
    rw [ihh _root_.rfl, ihm _root_.rfl]; funext i; exact _root_.rfl
  | cnv _ _ ih => exact ih
  | _ => intro _; exact _root_.rfl

-- any judgment replays at the dead demand
theorem Check.at_none (h : Check β Φ L sp q Γ t T π u) :
    ∃ π' u', Check β Φ L sp .None Γ t T π' u' := by
  induction h with
  | var hg => exact ⟨_, _, .var hg⟩
  | ref hk _ _ _ =>
    exact ⟨_, _, .ref hk (fun h => absurd _root_.rfl h) (fun h => absurd _root_.rfl h)
      (fun h => absurd _root_.rfl h)⟩
  | refA hk h0 => exact ⟨_, _, .refA hk h0⟩
  | adt hk => exact ⟨_, _, .adt hk⟩
  | ctr hk hc hr => exact ⟨_, _, .ctr hk hc hr⟩
  | typ hg => exact ⟨_, _, .typ hg⟩
  | qnt => exact ⟨_, _, .qnt⟩
  | qua => exact ⟨_, _, .qua⟩
  | min _ _ iha ihb =>
    obtain ⟨_, _, ha⟩ := iha
    obtain ⟨_, _, hb⟩ := ihb
    exact ⟨_, _, .min ha hb⟩
  | all hA hB _ _ => exact ⟨_, _, .all hA hB⟩
  | lam hA _ _ _ ihf =>
    obtain ⟨π', _, hf'⟩ := ihf
    rw [hf'.none_uses _root_.rfl] at hf'
    exact ⟨_, _, .lam hA hf' trivial⟩
  | app _ _ ihf ihx =>
    obtain ⟨_, _, hf'⟩ := ihf
    obtain ⟨_, _, hx'⟩ := ihx
    exact ⟨_, _, .app hf' ((Quant.dem_none _).symm ▸ hx')⟩
  | appLam ha _ ih =>
    obtain ⟨_, _, h'⟩ := ih
    exact ⟨_, _, .appLam ha h'⟩
  | let_ _ hA _ _ ihv _ ihb =>
    obtain ⟨_, _, hv'⟩ := ihv
    obtain ⟨π', _, hb'⟩ := ihb
    rw [hb'.none_uses _root_.rfl] at hb'
    exact ⟨_, _, .let_ ((Quant.dem_none _).symm ▸ hv') hA hb' trivial⟩
  | eql hT ha hb _ _ _ => exact ⟨_, _, .eql hT ha hb⟩
  | rfl hc => exact ⟨_, _, .rfl hc⟩
  | rwt _ hP _ ihe _ ihf =>
    obtain ⟨_, _, he'⟩ := ihe
    obtain ⟨_, _, hf'⟩ := ihf
    exact ⟨_, _, .rwt he' hP hf'⟩
  | mat hk hc hr hlen _ hins hgoal _ _ ihh ihm =>
    obtain ⟨_, _, hh'⟩ := ihh
    obtain ⟨_, _, hm'⟩ := ihm
    exact ⟨_, _, .mat hk hc hr hlen (fun h => absurd _root_.rfl h) hins hgoal hh' hm'⟩
  | efq hk _ hd => exact ⟨_, _, .efq hk (fun h => absurd _root_.rfl h) hd⟩
  | cnv _ hc iht =>
    obtain ⟨_, _, ht'⟩ := iht
    exact ⟨_, _, .cnv ht' hc⟩

theorem Check.dead (h : Check β Φ L sp q Γ t T π u) :
    Check β Φ L sp .None Γ t T Uses.zero .Qnt := by
  obtain ⟨π', u', h'⟩ := h.at_none
  have e1 := h'.none_uses _root_.rfl
  have e2 := h'.none_era _root_.rfl
  subst e1 e2
  exact h'

-- ============================================================================
-- METATHEORY §D2 — the indices L and sp: every derivation replays under
-- the void equation with any pending spine, and with the wall up
-- ============================================================================

theorem Book.tld_lt : ∀ {β : Book} {k : Nat} {t : TLD},
    Book.tld β k = some t → k < β.length := by
  intro β
  induction β with
  | nil => intro k t h; cases h
  | cons d β ih =>
    intro k t h
    cases k with
    | zero => exact Nat.succ_pos _
    | succ k => exact Nat.succ_lt_succ (ih h)

theorem Book.defn_tld (h : Book.defn β k = some d) : Book.tld β k = some (.defn d) := by
  unfold Book.defn at h
  split at h
  case _ heq => cases h; exact heq
  case _ => cases h

theorem Book.defn_lt (h : Book.defn β k = some d) : k < β.length :=
  Book.tld_lt (Book.defn_tld h)

theorem Check.void_sp (h : Check β Φ L sp q Γ t T π u) :
    ∀ sp', Check β Φ (LHS.void β) sp' q Γ t T π u := by
  induction h with
  | var hg => intro sp'; exact .var hg
  | ref hk hb _ _ =>
    intro sp'
    have hj := Book.defn_lt hk
    exact .ref hk hb (fun _ _ => Nat.le_of_lt hj)
      (fun _ he => absurd he (Nat.ne_of_lt hj))
  | refA hk h0 => intro sp'; exact .refA hk h0
  | adt hk => intro sp'; exact .adt hk
  | ctr hk hc hr => intro sp'; exact .ctr hk hc hr
  | typ _ ihg => intro sp'; exact .typ (ihg [])
  | qnt => intro sp'; exact .qnt
  | qua => intro sp'; exact .qua
  | min _ _ iha ihb => intro sp'; exact .min (iha []) (ihb [])
  | all _ _ ihA ihB => intro sp'; exact .all (ihA []) (ihB [])
  | lam _ _ hle ihA ihf => intro sp'; exact .lam (ihA []) (ihf []) hle
  | app _ _ ihf ihx => intro sp'; exact .app (ihf _) (ihx [])
  | appLam ha _ ih => intro sp'; exact .appLam ha (ih sp')
  | let_ _ _ _ hle ihv ihA ihb => intro sp'; exact .let_ (ihv []) (ihA []) (ihb []) hle
  | eql _ _ _ ihT iha ihb => intro sp'; exact .eql (ihT []) (iha []) (ihb [])
  | rfl hc => intro sp'; exact .rfl hc
  | rwt _ _ _ ihe ihP ihf => intro sp'; exact .rwt (ihe []) (ihP []) (ihf [])
  | mat hk hc hr hlen hlive hins hgoal _ _ ihh ihm =>
    intro sp'; exact .mat hk hc hr hlen hlive hins hgoal (ihh []) (ihm [])
  | efq hk hlive hd => intro sp'; exact .efq hk hlive hd
  | cnv _ hc iht => intro sp'; exact .cnv (iht sp') hc

theorem Check.void (h : Check β Φ L sp q Γ t T π u) :
    Check β Φ (LHS.void β) sp q Γ t T π u :=
  h.void_sp sp

theorem Check.sp (h : Check β Φ (LHS.void β) s q Γ t T π u) (sp' : List Term) :
    Check β Φ (LHS.void β) sp' q Γ t T π u :=
  h.void_sp sp'

-- the wall up
def LHS.up (L : LHS) : LHS := { L with w := true }

theorem LHS.up_shift (L : LHS) : L.shift.up = L.up.shift := rfl

theorem LHS.up_lam (L : LHS) : L.lam.up = L.up.lam := by
  by_cases h : L.n = 0 <;> simp [LHS.lam, LHS.up, LHS.shift, h]

theorem LHS.up_mat (L : LHS) (a c fn : Nat) : (L.mat a c fn).up = L.up.mat a c fn := by
  by_cases h : L.n = 0 <;> simp [LHS.mat, LHS.up, h]

theorem Check.wall {sp : List Term} (hb : ∀ k d, Book.defn β k = some d → d.b = false)
    (h : Check β Φ L sp q Γ t T π u) : Check β Φ L.up sp q Γ t T π u := by
  induction h with
  | var hg => exact .var hg
  | ref hk hbd hw hd =>
    exact .ref hk hbd (fun hq _ => hw hq (Or.inr (hb _ _ hk))) hd
  | refA hk h0 => exact .refA hk h0
  | adt hk => exact .adt hk
  | ctr hk hc hr => exact .ctr hk hc hr
  | typ _ ihg => exact .typ ihg
  | qnt => exact .qnt
  | qua => exact .qua
  | min _ _ iha ihb => exact .min iha ihb
  | all _ _ ihA ihB => rw [LHS.up_shift] at ihB; exact .all ihA ihB
  | lam _ _ hle ihA ihf => rw [LHS.up_lam] at ihf; exact .lam ihA ihf hle
  | app _ _ ihf ihx => exact .app ihf ihx
  | appLam ha _ ih => exact .appLam ha ih
  | let_ _ _ _ hle ihv ihA ihb =>
    rw [LHS.up_shift] at ihb; exact .let_ ihv ihA ihb hle
  | eql _ _ _ ihT iha ihb => exact .eql ihT iha ihb
  | rfl hc => exact .rfl hc
  | rwt _ _ _ ihe ihP ihf => exact .rwt ihe ihP ihf
  | mat hk hc hr hlen hlive hins hgoal _ _ ihh ihm =>
    rw [LHS.up_mat] at ihh; exact .mat hk hc hr hlen hlive hins hgoal ihh ihm
  | efq hk hlive hd => exact .efq hk hlive hd
  | cnv _ hc iht => exact .cnv iht hc

theorem Book.Ok.wall (hok : Book.Ok β) (hb : ∀ k d, Book.defn β k = some d → d.b = false) :
    Book.Wall β := by
  intro k d b hk hbody
  have h := hok k _ (Book.defn_tld hk)
  obtain ⟨π, u, hc⟩ := (h.2.2.2 b hbody).2
  exact ⟨π, u, hc.wall hb⟩

-- ============================================================================
-- METATHEORY §D3 — the let expansion δ: through append, spines, shifts,
-- context insertion and the closed substitution at the last position
-- ============================================================================

theorem Term.shift_shiftN : ∀ (n d : Nat) (t : Term), d ≤ n →
    Term.shift d (Term.shiftN n t) = Term.shiftN (n + 1) t := by
  intro n
  induction n with
  | zero => intro d t hd; cases Nat.eq_zero_of_le_zero hd; rfl
  | succ n ih =>
    intro d t hd
    cases d with
    | zero => rfl
    | succ d =>
      show Term.shift (d + 1) (Term.shift 0 (Term.shiftN n t))
        = Term.shift 0 (Term.shiftN (n + 1) t)
      rw [Term.shift_shift0, ih d t (by omega)]

theorem Term.subst_shiftN (n : Nat) (w t : Term) :
    Term.subst n w (Term.shiftN (n + 1) t) = Term.shiftN n t := by
  rw [← Term.shift_shiftN n n t (Nat.le_refl n)]
  exact Term.subst_shift _ n w

theorem Term.shift_shiftN_add : ∀ (d m : Nat) (v : Term),
    Term.shift (d + m) (Term.shiftN d v) = Term.shiftN d (Term.shift m v) := by
  intro d
  induction d with
  | zero => intro m v; rw [Nat.zero_add]; rfl
  | succ d ih =>
    intro m v
    show Term.shift (d + 1 + m) (Term.shift 0 (Term.shiftN d v))
      = Term.shift 0 (Term.shiftN d (Term.shift m v))
    rw [Nat.add_right_comm, Term.shift_shift0, ih]

theorem Term.shiftN_shift0 : ∀ (n : Nat) (t : Term),
    Term.shiftN n (Term.shift 0 t) = Term.shiftN (n + 1) t := by
  intro n
  induction n with
  | zero => intro t; rfl
  | succ n ih => intro t; show Term.shift 0 (Term.shiftN n (Term.shift 0 t)) = _; rw [ih]; rfl

theorem Term.shiftN_closed (hw : Term.Closed 0 w) : ∀ k, Term.shiftN k w = w := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    show Term.shift 0 (Term.shiftN k w) = w
    rw [ih]; exact Term.shift_closed w 0 0 hw (Nat.le_refl 0)

-- a closed w is inert under subst at any index
theorem Term.subst_shiftN_add (hw : Term.Closed 0 w) : ∀ (d n : Nat) (v : Term),
    Term.subst (d + n) w (Term.shiftN d v) = Term.shiftN d (Term.subst n w v) := by
  intro d
  induction d with
  | zero => intro n v; rw [Nat.zero_add]; rfl
  | succ d ih =>
    intro n v
    show Term.subst (d + 1 + n) w (Term.shift 0 (Term.shiftN d v))
      = Term.shift 0 (Term.shiftN d (Term.subst n w v))
    rw [Nat.add_right_comm, ← ih, Term.shift_subst_lt _ 0 (d + n) w (Nat.zero_le _),
      Term.shift_closed w 0 0 hw (Nat.le_refl 0)]

theorem Term.closed_apps_inv : ∀ (as : List Term) (h : Term) (m : Nat),
    (Term.apps h as).Closed m → h.Closed m ∧ ∀ x ∈ as, x.Closed m := by
  intro as
  induction as with
  | nil => intro h m hc; exact ⟨hc, fun x hx => nomatch hx⟩
  | cons a as ih =>
    intro h m hc
    obtain ⟨⟨hh, ha⟩, hrest⟩ := ih (.App h a) m hc
    refine ⟨hh, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ha
    · exact hrest x hx

theorem Term.spine_closed {t : Term} {m : Nat} (h : t.Closed m) :
    (Term.spine t).1.Closed m ∧ ∀ x ∈ (Term.spine t).2, x.Closed m := by
  have := Term.closed_apps_inv (Term.spine t).2 (Term.spine t).1 m
  rw [Term.apps_spine t] at this
  exact this h

theorem Term.retip_closed (r : List Nat) : ∀ (n pn : Nat) (t : Term) (m : Nat),
    t.Closed m → (Term.retip r pn n t).Closed m := by
  intro n
  induction n with
  | zero =>
    intro pn t m hc
    cases pn with
    | zero =>
      simp only [Term.retip]
      split
      · obtain ⟨_, hargs⟩ := Term.spine_closed hc
        exact Term.closed_apps _ _ _ trivial hargs
      · exact hc
    | succ pn => simp only [Term.retip]; exact hc
  | succ n ih =>
    intro pn t m hc
    cases pn <;> cases t <;> simp only [Term.retip] <;> (try exact hc)
    · exact ⟨hc.1, ih 0 _ (m + 1) hc.2⟩
    · exact ⟨hc.1, ih _ _ (m + 1) hc.2⟩

theorem Term.shift_era (d : Nat) (q : Quant) (u : Term) :
    Term.shift d (Term.era q u) = Term.era q (Term.shift d u) := by
  cases q <;> rfl

theorem Term.subst_era (d : Nat) (w : Term) (q : Quant) (u : Term) :
    Term.subst d w (Term.era q u) = Term.era q (Term.subst d w u) := by
  cases q <;> rfl

-- the rigid binders of a context: the entries without a value
def Ctx.rigid : Ctx → Nat
  | [] => 0
  | b :: Γ =>
    match b.v with
    | some _ => Ctx.rigid Γ
    | none   => Ctx.rigid Γ + 1

theorem Ctx.δ_append : ∀ (Γ Δ : Ctx) (d : Nat) (t : Term),
    Ctx.δ (Γ ++ Δ) d t = Ctx.δ Δ (d + Γ.rigid) (Ctx.δ Γ d t) := by
  intro Γ
  induction Γ with
  | nil => intro Δ d t; rfl
  | cons b Γ ih =>
    intro Δ d t
    obtain ⟨q, T, v⟩ := b
    cases v <;> simp only [List.cons_append, Ctx.δ, Ctx.rigid]
    · rw [ih, show d + 1 + Ctx.rigid Γ = d + (Ctx.rigid Γ + 1) by omega]
    · exact ih Δ d _

theorem Ctx.δ_apps : ∀ (Γ : Ctx) (d : Nat) (f : Term) (xs : List Term),
    Ctx.δ Γ d (Term.apps f xs) = Term.apps (Ctx.δ Γ d f) (xs.map (Ctx.δ Γ d)) := by
  intro Γ
  induction Γ with
  | nil => intro d f xs; simp [Ctx.δ]
  | cons b Γ ih =>
    intro d f xs
    obtain ⟨q, T, v⟩ := b
    cases v <;> simp only [Ctx.δ]
    · exact ih _ f xs
    · rw [Term.subst_apps, ih, List.map_map]; rfl

-- δ commutes with a shift at or below its depth
theorem Ctx.δ_shift : ∀ (Γ : Ctx) (d d' : Nat) (t : Term), d ≤ d' →
    Ctx.δ Γ (d' + 1) (Term.shift d t) = Term.shift d (Ctx.δ Γ d' t) := by
  intro Γ
  induction Γ with
  | nil => intro d d' t _; rfl
  | cons b Γ ih =>
    intro d d' t h
    obtain ⟨q, T, v⟩ := b
    cases v <;> simp only [Ctx.δ]
    · exact ih d (d' + 1) t (by omega)
    · rw [← ih d d' _ h, Term.shift_subst_lt t d d' _ h, Term.shift_shiftN d' d _ h]

-- a term shifted above the whole context keeps only the rigid renumbering
theorem Ctx.δ_shiftN : ∀ (Γ : Ctx) (d k : Nat) (X : Term), d + Γ.length ≤ k →
    Ctx.δ Γ d (Term.shiftN k X) = Term.shiftN (k - Γ.length + Γ.rigid) X := by
  intro Γ
  induction Γ with
  | nil => intro d k X _; simp [Ctx.δ, Ctx.rigid]
  | cons b Γ ih =>
    intro d k X hk
    obtain ⟨q, T, v⟩ := b
    simp only [List.length_cons] at hk
    cases v <;> simp only [Ctx.δ, Ctx.rigid, List.length_cons]
    · rw [ih (d + 1) k X (by omega)]; congr 1; omega
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      rw [← Term.shift_shiftN k' d X (by omega), Term.subst_shift, ih d k' X (by omega)]
      congr 1; omega

theorem Ctx.get_append : ∀ (Γ Δ : Ctx) (i : Nat), i < Γ.length →
    Ctx.get (Γ ++ Δ) i = Ctx.get Γ i := by
  intro Γ
  induction Γ with
  | nil => intro Δ i h; cases h
  | cons b Γ ih =>
    intro Δ i h
    cases i with
    | zero => rfl
    | succ i =>
      simp only [List.cons_append, Ctx.get]
      rw [ih Δ i (by simp only [List.length_cons] at h; omega)]

def Bind.shiftN : Nat → Bind → Bind
  | 0, b => b
  | n + 1, b => (Bind.shiftN n b).shift

theorem Bind.shiftN_q : ∀ (n : Nat) (b : Bind), (Bind.shiftN n b).q = b.q := by
  intro n; induction n with
  | zero => intro b; rfl
  | succ n ih => intro b; exact ih b

theorem Bind.shiftN_T : ∀ (n : Nat) (b : Bind), (Bind.shiftN n b).T = Term.shiftN n b.T := by
  intro n; induction n with
  | zero => intro b; rfl
  | succ n ih => intro b; show Term.shift 0 (Bind.shiftN n b).T = _; rw [ih]; rfl

theorem Bind.shiftN_v : ∀ (n : Nat) (b : Bind), (Bind.shiftN n b).v = b.v.map (Term.shiftN n) := by
  intro n; induction n with
  | zero => intro b; obtain ⟨q, T, v⟩ := b; cases v <;> rfl
  | succ n ih =>
    intro b
    show ((Bind.shiftN n b).v).map (Term.shift 0) = _
    rw [ih, Option.map_map]; rfl

theorem Ctx.get_append_ge : ∀ (Γ Δ : Ctx) (j : Nat),
    Ctx.get (Γ ++ Δ) (Γ.length + j) = (Ctx.get Δ j).map (Bind.shiftN Γ.length) := by
  intro Γ
  induction Γ with
  | nil => intro Δ j; simp only [List.nil_append, List.length_nil, Nat.zero_add]; cases Ctx.get Δ j <;> rfl
  | cons b Γ ih =>
    intro Δ j
    simp only [List.cons_append, List.length_cons]
    rw [show Γ.length + 1 + j = (Γ.length + j) + 1 by omega]
    simp only [Ctx.get]
    rw [ih, Option.map_map]; rfl

theorem Ctx.get_append_last (Γ : Ctx) (b0 : Bind) :
    Ctx.get (Γ ++ [b0]) Γ.length = some (Bind.shiftN (Γ.length + 1) b0) := by
  have := Ctx.get_append_ge Γ [b0] 0
  rw [Nat.add_zero] at this
  rw [this]
  simp only [Ctx.get, Option.map_some]
  congr 1
  induction Γ.length with
  | zero => rfl
  | succ n ih => show (Bind.shiftN n b0.shift).shift = (Bind.shiftN (n + 1) b0).shift; rw [ih]

-- context insertion: Γ' is Γ with U slotted in at depth n (the entries
-- above it shifted past it)
def Bind.shiftAt (n : Nat) (b : Bind) : Bind :=
  { b with T := Term.shift n b.T, v := b.v.map (Term.shift n) }

inductive Ins (U : Bind) : Nat → Ctx → Ctx → Prop
  | zero : Ins U 0 Γ (U :: Γ)
  | succ : Ins U n Γ Γ' → Ins U (n + 1) (b :: Γ) (b.shiftAt n :: Γ')

theorem Bind.shift_shiftAt (b : Bind) (n : Nat) :
    (b.shiftAt n).shift = b.shift.shiftAt (n + 1) := by
  obtain ⟨q, T, v⟩ := b
  cases v <;> simp [Bind.shiftAt, Bind.shift, Term.shift_shift0]

theorem Ins.get_lt (h : Ins U n Γ Γ') : ∀ {i : Nat} {b : Bind}, i < n →
    Ctx.get Γ i = some b → Ctx.get Γ' i = some (b.shiftAt n) := by
  induction h with
  | zero => intro i b hi; cases hi
  | @succ n Γ Γ' b0 _ ih =>
    intro i b hi hg
    cases i with
    | zero =>
      simp only [Ctx.get] at hg ⊢
      cases hg
      rw [Bind.shift_shiftAt]
    | succ j =>
      simp only [Ctx.get, Option.map_eq_some_iff] at hg ⊢
      obtain ⟨b', hb', rfl⟩ := hg
      exact ⟨_, ih (by omega) hb', Bind.shift_shiftAt b' n⟩

theorem Ins.get_ge (h : Ins U n Γ Γ') : ∀ {i : Nat} {b : Bind}, n ≤ i →
    Ctx.get Γ i = some b → Ctx.get Γ' (i + 1) = some (b.shiftAt n) := by
  induction h with
  | zero => intro i b _ hg; simp only [Ctx.get, hg, Option.map_some]; rfl
  | @succ n Γ Γ' b0 _ ih =>
    intro i b hi hg
    cases i with
    | zero => cases hi
    | succ j =>
      simp only [Ctx.get, Option.map_eq_some_iff] at hg ⊢
      obtain ⟨b', hb', rfl⟩ := hg
      exact ⟨_, ih (by omega) hb', Bind.shift_shiftAt b' n⟩

theorem Ins.length (h : Ins U n Γ Γ') : n ≤ Γ.length := by
  induction h with
  | zero => exact Nat.zero_le _
  | succ _ ih => exact Nat.succ_le_succ ih

-- δ through an insertion: a let entry is cancelled by the shift, a rigid
-- one renumbers the result
theorem Ins.δ (h : Ins U n Γ Γ') :
    (∀ d t, Ctx.δ Γ' d (Term.shift (d + n) t) = Ctx.δ Γ d t) ∨
    (∃ r, ∀ d t, Ctx.δ Γ' d (Term.shift (d + n) t) = Term.shift (d + r) (Ctx.δ Γ d t)) := by
  induction h with
  | @zero Γ =>
    obtain ⟨q, T, v⟩ := U
    cases v
    · right; exact ⟨0, fun d t => by simp only [Ctx.δ]; exact Ctx.δ_shift Γ d d t (Nat.le_refl d)⟩
    · left; intro d t; simp only [Ctx.δ]; rw [Nat.add_zero, Term.subst_shift]
  | @succ n Γ Γ' b _ ih =>
    obtain ⟨q, T, v⟩ := b
    cases v with
    | none =>
      simp only [Bind.shiftAt, Option.map_none, Ctx.δ]
      rcases ih with ih | ⟨r, ih⟩
      · left; intro d t
        rw [show d + (n + 1) = (d + 1) + n by omega]; exact ih (d + 1) t
      · right; refine ⟨r + 1, fun d t => ?_⟩
        rw [show d + (n + 1) = (d + 1) + n by omega, ih (d + 1) t,
          show d + 1 + r = d + (r + 1) by omega]
    | some v =>
      simp only [Bind.shiftAt, Option.map_some, Ctx.δ]
      have e : ∀ d t, Term.subst d (Term.shiftN d (Term.shift n v)) (Term.shift (d + (n + 1)) t)
          = Term.shift (d + n) (Term.subst d (Term.shiftN d v) t) := by
        intro d t
        rw [Term.shift_subst_ge t (d + n) d _ (by omega), Term.shift_shiftN_add,
          show d + (n + 1) = d + n + 1 by omega]
      rcases ih with ih | ⟨r, ih⟩
      · left; intro d t; rw [e, ih]
      · right; exact ⟨r, fun d t => by rw [e, ih]⟩

-- the closed substitution at the last position of a context: entry j
-- sees the last binder as index Γ.length - 1 - j
def Bind.substAt (k : Nat) (w : Term) (b : Bind) : Bind :=
  { b with T := Term.subst k w b.T, v := b.v.map (Term.subst k w) }

def Ctx.substLast (w : Term) : Ctx → Ctx
  | [] => []
  | b :: Γ => Bind.substAt Γ.length w b :: Ctx.substLast w Γ

theorem Ctx.substLast_length (w : Term) : ∀ (Γ : Ctx), (Ctx.substLast w Γ).length = Γ.length := by
  intro Γ; induction Γ with
  | nil => rfl
  | cons b Γ ih => simp only [Ctx.substLast, List.length_cons, ih]

theorem Ctx.substLast_rigid (w : Term) : ∀ (Γ : Ctx), (Ctx.substLast w Γ).rigid = Γ.rigid := by
  intro Γ; induction Γ with
  | nil => rfl
  | cons b Γ ih =>
    obtain ⟨q, T, v⟩ := b
    cases v <;> simp only [Ctx.substLast, Bind.substAt, Ctx.rigid, Option.map_none, Option.map_some, ih]

theorem Bind.shift_substAt (hw : Term.Closed 0 w) (b : Bind) (k : Nat) :
    (b.substAt k w).shift = b.shift.substAt (k + 1) w := by
  obtain ⟨q, T, v⟩ := b
  have e : ∀ t, Term.shift 0 (Term.subst k w t) = Term.subst (k + 1) w (Term.shift 0 t) := by
    intro t
    rw [Term.shift_subst_lt t 0 k w (Nat.zero_le k), Term.shift_closed w 0 0 hw (Nat.le_refl 0)]
  cases v <;> simp [Bind.substAt, Bind.shift, e]

theorem Ctx.get_substLast (hw : Term.Closed 0 w) : ∀ (Γ : Ctx) (i : Nat) (b : Bind),
    Ctx.get Γ i = some b → Ctx.get (Ctx.substLast w Γ) i = some (b.substAt Γ.length w) := by
  intro Γ
  induction Γ with
  | nil => intro i b h; cases h
  | cons b0 Γ ih =>
    intro i b hg
    cases i with
    | zero =>
      simp only [Ctx.get, Ctx.substLast, List.length_cons] at hg ⊢
      cases hg
      rw [Bind.shift_substAt hw]
    | succ j =>
      simp only [Ctx.get, Ctx.substLast, List.length_cons, Option.map_eq_some_iff] at hg ⊢
      obtain ⟨b', hb', rfl⟩ := hg
      exact ⟨_, ih j b' hb', Bind.shift_substAt hw b' Γ.length⟩

-- δ of the substituted context on the substituted term is the substitution
-- of w into δ of the original, at the rigid depth
theorem Ctx.δ_substLast (hw : Term.Closed 0 w) : ∀ (Γ : Ctx) (d : Nat) (t : Term),
    Ctx.δ (Ctx.substLast w Γ) d (Term.subst (d + Γ.length) w t)
      = Term.subst (d + Γ.rigid) w (Ctx.δ Γ d t) := by
  intro Γ
  induction Γ with
  | nil => intro d t; rfl
  | cons b Γ ih =>
    intro d t
    obtain ⟨q, T, v⟩ := b
    cases v <;> simp only [Ctx.substLast, Bind.substAt, Option.map_none, Option.map_some, Ctx.δ,
      Ctx.rigid, List.length_cons]
    · rw [show d + (Γ.length + 1) = (d + 1) + Γ.length by omega, ih (d + 1) t,
        show d + 1 + Ctx.rigid Γ = d + (Ctx.rigid Γ + 1) by omega]
    · rw [show d + (Γ.length + 1) = (d + Γ.length) + 1 by omega, ← ih d,
        Term.subst_subst t (d + Γ.length) d w _ (by omega),
        Term.shift_closed w 0 d hw (Nat.zero_le d), Term.subst_shiftN_add hw]

-- δ of the extended context on a term in it
theorem Ctx.δ_append_none (hv : b0.v = none) (Γ : Ctx) (t : Term) :
    Ctx.δ (Γ ++ [b0]) 0 t = Ctx.δ Γ 0 t := by
  rw [Ctx.δ_append, Nat.zero_add]; simp only [Ctx.δ, hv]

theorem Ctx.δ_append_some (hw : Term.Closed 0 w) (hv : b0.v = some w) (Γ : Ctx) (t : Term) :
    Ctx.δ (Γ ++ [b0]) 0 t = Term.subst Γ.rigid w (Ctx.δ Γ 0 t) := by
  rw [Ctx.δ_append, Nat.zero_add]; simp only [Ctx.δ, hv]; rw [Term.shiftN_closed hw]

-- the use vectors of weakening and substitution
def Uses.lift (n : Nat) (π : Uses) : Uses :=
  fun i => if i < n then π i else if i = n then .None else π (i - 1)

def Uses.del (n : Nat) (π : Uses) : Uses :=
  fun i => if i < n then π i else π (i + 1)

theorem Uses.lift_one_lt (n i : Nat) (q : Quant) (h : i < n) :
    Uses.lift n (Uses.one i q) = Uses.one i q := by
  funext j
  simp only [Uses.lift, Uses.one]
  by_cases h1 : j < n
  · rw [if_pos h1]
  · rw [if_neg h1, if_neg (show ¬ j = i by omega)]
    by_cases h2 : j = n
    · rw [if_pos h2]
    · rw [if_neg h2, if_neg (show ¬ j - 1 = i by omega)]

theorem Uses.lift_one_ge (n i : Nat) (q : Quant) (h : n ≤ i) :
    Uses.lift n (Uses.one i q) = Uses.one (i + 1) q := by
  funext j
  simp only [Uses.lift, Uses.one]
  by_cases h1 : j < n
  · rw [if_pos h1, if_neg (show ¬ j = i by omega), if_neg (show ¬ j = i + 1 by omega)]
  · rw [if_neg h1]
    by_cases h2 : j = n
    · rw [if_pos h2, if_neg (show ¬ j = i + 1 by omega)]
    · rw [if_neg h2]
      by_cases h3 : j = i + 1
      · rw [if_pos h3, if_pos (show j - 1 = i by omega)]
      · rw [if_neg h3, if_neg (show ¬ j - 1 = i by omega)]

theorem Uses.lift_zero (n : Nat) : Uses.lift n Uses.zero = Uses.zero := by
  funext j; simp only [Uses.lift, Uses.zero]
  split
  · rfl
  · split <;> rfl

theorem Uses.lift_add (n : Nat) (a b : Uses) :
    Uses.lift n (Uses.add a b) = Uses.add (Uses.lift n a) (Uses.lift n b) := by
  funext j; simp only [Uses.lift, Uses.add]
  split
  · rfl
  · split <;> rfl

theorem Uses.lift_join (n : Nat) (a b : Uses) :
    Uses.lift n (Uses.join a b) = Uses.join (Uses.lift n a) (Uses.lift n b) := by
  funext j; simp only [Uses.lift, Uses.join]
  split
  · rfl
  · split <;> rfl

theorem Uses.lift_tail (n : Nat) (π : Uses) :
    Uses.lift n (Uses.tail π) = Uses.tail (Uses.lift (n + 1) π) := by
  funext j
  simp only [Uses.lift, Uses.tail]
  by_cases h1 : j < n
  · rw [if_pos h1, if_pos (show j + 1 < n + 1 by omega)]
  · rw [if_neg h1, if_neg (show ¬ j + 1 < n + 1 by omega)]
    by_cases h2 : j = n
    · rw [if_pos h2, if_pos (show j + 1 = n + 1 by omega)]
    · rw [if_neg h2, if_neg (show ¬ j + 1 = n + 1 by omega)]; congr 1; omega

theorem Uses.lift_head (n : Nat) (π : Uses) : Uses.lift (n + 1) π 0 = π 0 := by
  simp only [Uses.lift]; rw [if_pos (show 0 < n + 1 by omega)]

theorem Uses.del_one_lt (n i : Nat) (q : Quant) (h : i < n) :
    Uses.del n (Uses.one i q) = Uses.one i q := by
  funext j
  simp only [Uses.del, Uses.one]
  by_cases h1 : j < n
  · rw [if_pos h1]
  · rw [if_neg h1, if_neg (show ¬ j + 1 = i by omega), if_neg (show ¬ j = i by omega)]

theorem Uses.del_one_eq (n : Nat) (q : Quant) :
    Uses.del n (Uses.one n q) = Uses.zero := by
  funext j
  simp only [Uses.del, Uses.one, Uses.zero]
  by_cases h1 : j < n
  · rw [if_pos h1, if_neg (show ¬ j = n by omega)]
  · rw [if_neg h1, if_neg (show ¬ j + 1 = n by omega)]

theorem Uses.del_one_gt (n i : Nat) (q : Quant) (h : n < i + 1) :
    Uses.del n (Uses.one (i + 1) q) = Uses.one i q := by
  funext j
  simp only [Uses.del, Uses.one]
  by_cases h1 : j < n
  · rw [if_pos h1, if_neg (show ¬ j = i + 1 by omega), if_neg (show ¬ j = i by omega)]
  · rw [if_neg h1]
    by_cases h2 : j = i
    · rw [if_pos (show j + 1 = i + 1 by omega), if_pos h2]
    · rw [if_neg (show ¬ j + 1 = i + 1 by omega), if_neg h2]

theorem Uses.del_zero (n : Nat) : Uses.del n Uses.zero = Uses.zero := by
  funext j; simp only [Uses.del, Uses.zero]; split <;> rfl

theorem Uses.del_add (n : Nat) (a b : Uses) :
    Uses.del n (Uses.add a b) = Uses.add (Uses.del n a) (Uses.del n b) := by
  funext j; simp only [Uses.del, Uses.add]; split <;> rfl

theorem Uses.del_join (n : Nat) (a b : Uses) :
    Uses.del n (Uses.join a b) = Uses.join (Uses.del n a) (Uses.del n b) := by
  funext j; simp only [Uses.del, Uses.join]; split <;> rfl

theorem Uses.del_tail (n : Nat) (π : Uses) :
    Uses.del n (Uses.tail π) = Uses.tail (Uses.del (n + 1) π) := by
  funext j
  simp only [Uses.del, Uses.tail]
  by_cases h1 : j < n
  · rw [if_pos h1, if_pos (show j + 1 < n + 1 by omega)]
  · rw [if_neg h1, if_neg (show ¬ j + 1 < n + 1 by omega)]

theorem Uses.del_head (n : Nat) (π : Uses) : Uses.del (n + 1) π 0 = π 0 := by
  simp only [Uses.del]; rw [if_pos (show 0 < n + 1 by omega)]

theorem Quant.add_eq_none : ∀ {a b : Quant}, Quant.add a b = .None → a = .None ∧ b = .None := by
  intro a b h; cases a <;> cases b <;> simp_all [Quant.add]

theorem Quant.join_eq_none : ∀ {a b : Quant}, Quant.join a b = .None → a = .None ∧ b = .None := by
  intro a b h; cases a <;> cases b <;> simp_all [Quant.join]

theorem Quant.dem_ne_many : ∀ {q' q : Quant}, q ≠ .Many → Quant.dem q' q ≠ .Many := by
  intro q' q h; cases q' <;> cases q <;> simp_all [Quant.dem]

-- shift and subst transport for the mat premises
theorem Insts.shift (h : Insts T ps T') (d : Nat) :
    Insts (T.shift d) (ps.map (Term.shift d)) (T'.shift d) := by
  induction h generalizing d with
  | nil => exact .nil
  | cons _ ih =>
    refine Insts.cons ?_
    rw [← Term.shift_subst0]
    exact ih d

theorem MatGoal.shift (h : MatGoal q' n B s tel G) :
    ∀ d, MatGoal q' n (B.shift (d + 1)) (s.shift d) (tel.shift d) (G.shift d) := by
  induction h with
  | zero =>
    intro d
    rw [Term.shift_subst0]
    exact .zero
  | @succ n B s Bf G qf F _ ih =>
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

theorem Insts.subst (h : Insts T ps T') :
    ∀ (d : Nat) (w : Term),
    Insts (Term.subst d w T) (ps.map (Term.subst d w)) (Term.subst d w T') := by
  induction h with
  | nil => intro d w; exact .nil
  | cons _ ih =>
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
  | @succ n B s Bf G qf F _ ih =>
    intro d w
    show MatGoal q' (n + 1) _ _
      (.All qf (Term.subst d w F) (Term.subst (d + 1) (Term.shift 0 w) Bf))
      (.All (Quant.mul qf q') (Term.subst d w F)
        (Term.subst (d + 1) (Term.shift 0 w) G))
    have h2 := ih (d + 1) (Term.shift 0 w)
    have eB : Term.subst (d + 1 + 1) (Term.shift 0 (Term.shift 0 w)) (Term.shift 1 B)
        = Term.shift 1 (Term.subst (d + 1) (Term.shift 0 w) B) := by
      rw [Term.shift_subst_lt B 1 (d + 1) (Term.shift 0 w) (by omega), Term.shift_shift0]
    rw [eB] at h2
    have e1 : Term.subst (d + 1) (Term.shift 0 w) (.App (Term.shift 0 s) (.Var 0))
        = .App (Term.shift 0 (Term.subst d w s)) (.Var 0) := by
      show Term.App _ _ = _
      rw [← Term.shift_subst_lt s 0 d w (Nat.zero_le d)]
      simp only [Term.subst]
      rw [if_neg (by omega : ¬ (0 : Nat) = d + 1), if_neg (by omega : ¬ d + 1 < 0)]
    rw [e1] at h2
    exact MatGoal.succ h2

-- a derivation measures nothing past its context
theorem Check.uses_ge {sp : List Term} (h : Check β Φ L sp q Γ t T π u) :
    ∀ i, Γ.length ≤ i → π i = .None := by
  induction h with
  | var hg =>
    intro i hi
    have := Ctx.get_lt hg
    simp only [Uses.one]; rw [if_neg (by omega)]
  | min _ _ iha ihb => intro i hi; simp only [Uses.add, iha i hi, ihb i hi]; rfl
  | lam _ _ _ _ ihf => intro i hi; exact ihf (i + 1) (by simp only [List.length_cons]; omega)
  | app _ _ ihf ihx => intro i hi; simp only [Uses.add, ihf i hi, ihx i hi]; rfl
  | appLam _ _ ih => exact ih
  | let_ _ _ _ _ ihv _ ihb =>
    intro i hi
    simp only [Uses.add, Uses.tail, ihv i hi, ihb (i + 1) (by simp only [List.length_cons]; omega)]
    rfl
  | rwt _ _ _ ihe _ ihf => intro i hi; simp only [Uses.add, ihe i hi, ihf i hi]; rfl
  | mat _ _ _ _ _ _ _ _ _ ihh ihm => intro i hi; simp only [Uses.join, ihh i hi, ihm i hi]; rfl
  | cnv _ _ ih => exact ih
  | _ => intro i _; rfl

theorem Check.closed_uses {sp : List Term} (h : Check β Φ L sp q [] t T π u) : π = Uses.zero := by
  funext i; exact h.uses_ge i (Nat.zero_le i)

-- ============================================================================
-- METATHEORY §D4 — weakening under the void equation: appending a context
-- at the outer end (nothing shifts), and inserting an entry at any depth
-- (Ins: the subject, type, measure and elaboration lift past it)
-- ============================================================================

theorem Ctx.δ_rel (R : Term → Term → Prop)
    (hR : ∀ d w x y, R x y → R (Term.subst d w x) (Term.subst d w y)) (Δ : Ctx) :
    ∀ (d : Nat) (x y : Term), R x y → R (Ctx.δ Δ d x) (Ctx.δ Δ d y) := by
  induction Δ with
  | nil => intro d x y h; exact h
  | cons b Δ ih =>
    intro d x y h
    obtain ⟨q, T, v⟩ := b
    cases v <;> simp only [Ctx.δ]
    · exact ih (d + 1) x y h
    · exact ih d _ _ (hR d _ x y h)

theorem Ctx.δ_red (hβ : Book.Closed β) (Δ : Ctx) (d : Nat) (h : Red β p x y) :
    Red β p (Ctx.δ Δ d x) (Ctx.δ Δ d y) :=
  Ctx.δ_rel (Red β p) (fun d w _ _ h => h.subst hβ d w) Δ d x y h

theorem Ctx.δ_conv (hβ : Book.Closed β) (Δ : Ctx) (d : Nat) (h : Conv β x y) :
    Conv β (Ctx.δ Δ d x) (Ctx.δ Δ d y) :=
  Ctx.δ_rel (Conv β) (fun d w _ _ h => Conv.subst hβ h (Conv.refl w) d) Δ d x y h

theorem Ctx.δ_le (hβ : Book.Closed β) (Δ : Ctx) (d : Nat) (h : Le β x y) :
    Le β (Ctx.δ Δ d x) (Ctx.δ Δ d y) :=
  Ctx.δ_rel (Le β) (fun d w _ _ h => h.subst hβ d w) Δ d x y h

theorem CtxDead.append (hβ : Book.Closed β) (Δ : Ctx) (hd : CtxDead β Γ) :
    CtxDead β (Γ ++ Δ) := by
  obtain ⟨i, b, a, r, ps, hg, hq, hred, hemp⟩ := hd
  refine ⟨i, b, a, r, ps.map (Ctx.δ Δ Γ.rigid), ?_, hq, ?_, hemp⟩
  · rw [Ctx.get_append _ _ _ (Ctx.get_lt hg)]; exact hg
  · rw [Ctx.δ_append, Nat.zero_add]
    have := Ctx.δ_conv hβ Δ Γ.rigid hred
    rwa [Ctx.δ_apps, Ctx.δ_closed Δ Γ.rigid (.Adt a r) (by trivial)] at this

-- a policy that survives the context moves of weakening: its conversion
-- is closed under substitution and shift, its emptiness test under
-- appending and inserting entries (Pol.std is one, see Pol.std_weak)
structure Pol.Weak (Φ : Pol) : Prop where
  subst : ∀ d w x y, Φ.conv x y → Φ.conv (Term.subst d w x) (Term.subst d w y)
  shift : ∀ d x y, Φ.conv x y → Φ.conv (Term.shift d x) (Term.shift d y)
  append : ∀ Γ Δ, Φ.efq Γ → Φ.efq (Γ ++ Δ)
  ins : ∀ U n Γ Γ', Ins U n Γ Γ' → Φ.efq Γ → Φ.efq Γ'

theorem Check.weaken (hβ : Book.Closed β) (hΦ : Φ.Weak) {sp : List Term}
    (h : Check β Φ L sp q Γ t T π u) (Δ : Ctx) :
    Check β Φ (LHS.void β) sp q (Γ ++ Δ) t T π u := by
  induction h with
  | var hg => rw [← Ctx.get_append _ Δ _ (Ctx.get_lt hg)] at hg; exact .var hg
  | ref hk hb _ _ =>
    have hj := Book.defn_lt hk
    exact .ref hk hb (fun _ _ => Nat.le_of_lt hj) (fun _ he => absurd he (Nat.ne_of_lt hj))
  | refA hk h0 => exact .refA hk h0
  | adt hk => exact .adt hk
  | ctr hk hc hr => exact .ctr hk hc hr
  | typ _ ihg => exact .typ ihg
  | qnt => exact .qnt
  | qua => exact .qua
  | min _ _ iha ihb => exact .min iha ihb
  | all _ _ ihA ihB => exact .all ihA ihB
  | lam _ _ hle ihA ihf => exact .lam ihA ihf hle
  | app _ _ ihf ihx => exact .app ihf ihx
  | appLam ha _ ih =>
    exact .appLam (Term.Closed.mono _ _ _ ha (by simp only [List.length_append]; omega)) ih
  | let_ _ _ _ hle ihv ihA ihb => exact .let_ ihv ihA ihb hle
  | eql _ _ _ ihT iha ihb => exact .eql ihT iha ihb
  | rfl hc =>
    refine .rfl ?_
    rw [Ctx.δ_append, Ctx.δ_append]
    exact Ctx.δ_conv hβ Δ _ hc
  | rwt _ _ _ ihe ihP ihf => exact .rwt ihe ihP ihf
  | mat hk hc hr hlen hlive hins hgoal _ _ ihh ihm =>
    exact .mat hk hc hr hlen hlive hins hgoal ihh ihm
  | efq hk hlive hd => exact .efq hk hlive (hd.imp id (hΦ.append _ Δ))
  | cnv _ hc iht =>
    refine .cnv iht ?_
    rw [Ctx.δ_append, Ctx.δ_append]
    exact Ctx.δ_rel Φ.conv hΦ.subst Δ _ _ _ hc

theorem Ins.δ0 (h : Ins U n Γ Γ') :
    (∀ t, Ctx.δ Γ' 0 (Term.shift n t) = Ctx.δ Γ 0 t) ∨
    (∃ r, ∀ t, Ctx.δ Γ' 0 (Term.shift n t) = Term.shift r (Ctx.δ Γ 0 t)) := by
  rcases h.δ with e | ⟨r, e⟩
  · left; intro t; have := e 0 t; rwa [Nat.zero_add] at this
  · right; exact ⟨r, fun t => by have := e 0 t; rwa [Nat.zero_add, Nat.zero_add] at this⟩

theorem Ins.length_eq (h : Ins U n Γ Γ') : Γ'.length = Γ.length + 1 := by
  induction h with
  | zero => rfl
  | succ _ ih => simp only [List.length_cons, ih]

theorem CtxDead.ins (hβ : Book.Closed β) (hins : Ins U n Γ Γ') (hd : CtxDead β Γ) :
    CtxDead β Γ' := by
  obtain ⟨i, b, a, r, ps, hg, hq, hred, hemp⟩ := hd
  have key : ∃ i', Ctx.get Γ' i' = some (b.shiftAt n) := by
    by_cases hi : i < n
    · exact ⟨i, hins.get_lt hi hg⟩
    · exact ⟨i + 1, hins.get_ge (by omega) hg⟩
  obtain ⟨i', hg'⟩ := key
  rcases hins.δ0 with e | ⟨r', e⟩
  · exact ⟨i', _, a, r, ps, hg', hq, by
      show Conv β (Ctx.δ Γ' 0 (Term.shift n b.T)) _
      rw [e]; exact hred, hemp⟩
  · refine ⟨i', _, a, r, ps.map (Term.shift r'), hg', hq, ?_, hemp⟩
    show Conv β (Ctx.δ Γ' 0 (Term.shift n b.T)) _
    rw [e]
    have := hred.shift hβ r'
    rwa [Term.shift_apps] at this

theorem Pol.std_weak (hβ : Book.Closed β) : (Pol.std β).Weak :=
  ⟨fun d w x y (h : Le β x y) => h.subst hβ d w, fun d x y (h : Le β x y) => h.shift hβ d,
   fun _ Δ h => CtxDead.append hβ Δ h, fun _ _ _ _ hins h => CtxDead.ins hβ hins h⟩

theorem Check.ins (hβ : Book.Closed β) (hΦ : Φ.Weak) {sp : List Term}
    (h : Check β Φ L sp q Γ t T π u) :
    ∀ {n : Nat} {U : Bind} {Γ' : Ctx}, Ins U n Γ Γ' → ∀ sp',
    Check β Φ (LHS.void β) sp' q Γ' (Term.shift n t) (Term.shift n T) (Uses.lift n π)
      (Term.shift n u) := by
  induction h with
  | @var Γ i b L sp q hg =>
    intro n U Γ' hins sp'
    simp only [Term.shift, Term.shift_era]
    by_cases hi : i < n
    · rw [if_pos hi, Uses.lift_one_lt n i q hi]
      exact .var (hins.get_lt hi hg)
    · rw [if_neg hi, Uses.lift_one_ge n i q (by omega)]
      exact .var (hins.get_ge (by omega) hg)
  | ref hk hb _ _ =>
    intro n U Γ' hins sp'
    rw [Term.shift_closed _ 0 n (hβ.defn hk).1 (Nat.zero_le n), Uses.lift_zero,
      Term.shift_era]
    have hj := Book.defn_lt hk
    exact .ref hk hb (fun _ _ => Nat.le_of_lt hj) (fun _ he => absurd he (Nat.ne_of_lt hj))
  | refA hk h0 =>
    intro n U Γ' hins sp'
    rw [Term.shift_closed _ 0 n (hβ.adtd hk).1 (Nat.zero_le n), Uses.lift_zero,
      Term.shift_era]
    exact .refA hk h0
  | adt hk =>
    intro n U Γ' hins sp'
    rw [Term.shift_closed _ 0 n (hβ.adtd hk).1 (Nat.zero_le n), Uses.lift_zero,
      Term.shift_era]
    exact .adt hk
  | ctr hk hc hr =>
    intro n U Γ' hins sp'
    rw [Term.shift_closed _ 0 n
      (Term.retip_closed _ _ _ _ 0 ((hβ.adtd hk).2 _ _ hc)) (Nat.zero_le n),
      Uses.lift_zero, Term.shift_era]
    exact .ctr hk hc hr
  | typ _ ihg =>
    intro n U Γ' hins sp'
    rw [Uses.lift_zero, Term.shift_era]
    exact .typ (ihg hins [])
  | qnt => intro n U Γ' hins sp'; rw [Uses.lift_zero]; exact .qnt
  | qua => intro n U Γ' hins sp'; rw [Uses.lift_zero, Term.shift_era]; exact .qua
  | min _ _ iha ihb =>
    intro n U Γ' hins sp'
    rw [Uses.lift_add, Term.shift_era]
    exact .min (iha hins []) (ihb hins [])
  | all _ _ ihA ihB =>
    intro n U Γ' hins sp'
    rw [Uses.lift_zero, Term.shift_era]
    exact .all (ihA hins []) (ihB (Ins.succ hins) [])
  | lam _ _ hle ihA ihf =>
    intro n U Γ' hins sp'
    rw [Uses.lift_tail, Term.shift_era]
    refine .lam (ihA hins []) (ihf (Ins.succ hins) []) ?_
    rw [Uses.lift_head]; exact hle
  | app _ _ ihf ihx =>
    intro n U Γ' hins sp'
    rw [Uses.lift_add, Term.shift_subst0, Term.shift_era]
    exact .app (ihf hins _) (ihx hins [])
  | appLam ha _ ih =>
    intro n U Γ' hins sp'
    have := ih hins sp'
    rw [Term.shift_subst0] at this
    refine .appLam ?_ this
    rw [hins.length_eq]; exact Term.Closed.shift _ _ _ ha
  | let_ _ _ _ hle ihv ihA ihb =>
    intro n U Γ' hins sp'
    rw [Uses.lift_add, Uses.lift_tail, Term.shift_era]
    have hb' := ihb (Ins.succ hins) []
    rw [Term.shift_shift0] at hb'
    refine .let_ (ihv hins []) (ihA hins []) hb' ?_
    rw [Uses.lift_head]; exact hle
  | eql _ _ _ ihT iha ihb =>
    intro n U Γ' hins sp'
    rw [Uses.lift_zero, Term.shift_era]
    exact .eql (ihT hins []) (iha hins []) (ihb hins [])
  | rfl hc =>
    intro n U Γ' hins sp'
    rw [Uses.lift_zero, Term.shift_era]
    refine .rfl ?_
    rcases hins.δ0 with e | ⟨r, e⟩
    · rw [e, e]; exact hc
    · rw [e, e]; exact hc.shift hβ r
  | rwt _ _ _ ihe ihP ihf =>
    intro n U Γ' hins sp'
    rw [Uses.lift_add, Term.shift_era]
    have hP' := ihP hins []
    rw [Term.shift_jmotive] at hP'
    exact .rwt (ihe hins []) hP' (ihf hins [])
  | mat hk hc hr hlen hlive hins hgoal _ _ ihh ihm =>
    intro n U Γ' hI sp'
    rw [Uses.lift_join, Term.shift_era]
    simp only [Term.shift, Term.shift_apps]
    have hi' := hins.shift n
    rw [Term.shift_closed _ 0 n ((hβ.adtd hk).2 _ _ hc) (Nat.zero_le n)] at hi'
    have hg' := hgoal.shift n
    rw [Term.shift_apps] at hg'
    refine Check.mat hk hc hr (by simp [hlen]) hlive hi' hg' (ihh hI []) ?_
    have := ihm hI []
    simp only [Term.shift, Term.shift_apps] at this
    exact this
  | efq hk hlive hd =>
    intro n U Γ' hins sp'
    rw [Uses.lift_zero, Term.shift_era]
    simp only [Term.shift, Term.shift_apps]
    exact .efq hk hlive (hd.imp id (hΦ.ins _ _ _ _ hins))
  | cnv _ hc iht =>
    intro n U Γ' hins sp'
    refine .cnv (iht hins sp') ?_
    rcases hins.δ0 with e | ⟨r, e⟩
    · rw [e, e]; exact hc
    · rw [e, e]; exact hΦ.shift r _ _ hc

-- a closed judgment replays in any context, its type shifted past it
theorem Check.weaken_closed (hβ : Book.Closed β) (hΦ : Φ.Weak) {sp : List Term}
    (h : Check β Φ L sp q [] t T π u) :
    ∀ (Δ : Ctx) (sp' : List Term),
    Check β Φ (LHS.void β) sp' q Δ t (Term.shiftN Δ.length T) π u := by
  have ht := h.closed
  have hu := h.closed_era
  have hπ := h.closed_uses
  intro Δ
  induction Δ with
  | nil => intro sp'; exact h.void_sp sp'
  | cons g Δ ih =>
    intro sp'
    have := (ih []).ins hβ hΦ (Ins.zero (U := g)) sp'
    rw [Term.shift_closed t 0 0 ht (Nat.le_refl 0), Term.shift_closed u 0 0 hu (Nat.le_refl 0),
      hπ, Uses.lift_zero] at this
    rw [hπ]
    exact this

-- ============================================================================
-- METATHEORY §D5 — the closed substitution at the last position of the
-- context: a var of index Γ.length becomes w (its dead or live closed
-- derivation replayed in the substituted context), every other index is
-- renumbered, and the measure drops the slot
-- ============================================================================

theorem Term.Closed.subst (hw : Term.Closed 0 w) : ∀ (t : Term) (n d : Nat), d ≤ n →
    t.Closed (n + 1) → (Term.subst d w t).Closed n := by
  intro t
  induction t <;> intro n d hd hc <;> simp only [Term.Closed, Term.subst] at *
  case Var =>
    split
    · exact Term.Closed.mono w 0 n hw (Nat.zero_le n)
    · split <;> simp only [Term.Closed] <;> omega
  case Typ ih => exact ih n d hd hc
  case Min iha ihb => exact ⟨iha n d hd hc.1, ihb n d hd hc.2⟩
  case All ihA ihB =>
    rw [Term.shift_closed w 0 0 hw (Nat.le_refl 0)]
    exact ⟨ihA n d hd hc.1, ihB (n + 1) (d + 1) (by omega) hc.2⟩
  case Lam ihf =>
    rw [Term.shift_closed w 0 0 hw (Nat.le_refl 0)]
    exact ihf (n + 1) (d + 1) (by omega) hc
  case App ihf iha => exact ⟨ihf n d hd hc.1, iha n d hd hc.2⟩
  case Mat ihh ihm => exact ⟨ihh n d hd hc.1, ihm n d hd hc.2⟩
  case Eql iha ihb ihT => exact ⟨iha n d hd hc.1, ihb n d hd hc.2.1, ihT n d hd hc.2.2⟩
  case Rwt ihe ihP ihf => exact ⟨ihe n d hd hc.1, ihP n d hd hc.2.1, ihf n d hd hc.2.2⟩
  case Let ihv ihb =>
    rw [Term.shift_closed w 0 0 hw (Nat.le_refl 0)]
    exact ⟨ihv n d hd hc.1, ihb (n + 1) (d + 1) (by omega) hc.2⟩

theorem Term.subst_shift0_closed (hw : Term.Closed 0 w) (n : Nat) (T : Term) :
    Term.subst (n + 1) w (Term.shift 0 T) = Term.shift 0 (Term.subst n w T) := by
  rw [Term.shift_subst_lt T 0 n w (Nat.zero_le n), Term.shift_closed w 0 0 hw (Nat.le_refl 0)]

theorem Ctx.δ_substLast0 (hw : Term.Closed 0 w) (Γ : Ctx) (t : Term) :
    Ctx.δ (Ctx.substLast w Γ) 0 (Term.subst Γ.length w t)
      = Term.subst Γ.rigid w (Ctx.δ Γ 0 t) := by
  have := Ctx.δ_substLast hw Γ 0 t
  rwa [Nat.zero_add, Nat.zero_add] at this

-- a comparison of let-expanded terms survives the substitution
theorem Ctx.δ_last (hw : Term.Closed 0 w) (hv : b0.v = none ∨ b0.v = some w)
    (R : Term → Term → Prop) (hR : ∀ d x y, R x y → R (Term.subst d w x) (Term.subst d w y))
    (Γ : Ctx) (a b : Term)
    (h : R (Ctx.δ (Γ ++ [b0]) 0 a) (Ctx.δ (Γ ++ [b0]) 0 b)) :
    R (Ctx.δ (Ctx.substLast w Γ) 0 (Term.subst Γ.length w a))
      (Ctx.δ (Ctx.substLast w Γ) 0 (Term.subst Γ.length w b)) := by
  rw [Ctx.δ_substLast0 hw, Ctx.δ_substLast0 hw]
  rcases hv with hv | hv
  · rw [Ctx.δ_append_none hv, Ctx.δ_append_none hv] at h; exact hR _ _ _ h
  · rw [Ctx.δ_append_some hw hv, Ctx.δ_append_some hw hv] at h; exact h

theorem CtxDead.substLast (hβ : Book.Closed β) (hw : Term.Closed 0 w)
    (hv : b0.v = none ∨ b0.v = some w)
    (hdead : b0.q ≠ .None → ∀ m a r ps,
      Conv β (Term.shiftN m b0.T) (Term.apps (.Adt a r) ps) → ¬ Book.empty β a r)
    (Γ : Ctx) (hd : CtxDead β (Γ ++ [b0])) : CtxDead β (Ctx.substLast w Γ) := by
  obtain ⟨i, b, a, r, ps, hg, hq, hred, hemp⟩ := hd
  have hi := Ctx.get_lt hg
  simp only [List.length_append, List.length_singleton] at hi
  by_cases hin : i < Γ.length
  · rw [Ctx.get_append _ _ _ hin] at hg
    have hg' := Ctx.get_substLast hw Γ i b hg
    rcases hv with hv | hv
    · refine ⟨i, _, a, r, ps.map (Term.subst Γ.rigid w), hg', hq, ?_, hemp⟩
      show Conv β (Ctx.δ (Ctx.substLast w Γ) 0 (Term.subst Γ.length w b.T)) _
      rw [Ctx.δ_substLast0 hw, ← Term.subst_apps_closed Γ.rigid w (b := .Adt a r) (by trivial),
        Ctx.δ_append_none hv] at *
      exact Conv.subst hβ hred (Conv.refl _) _
    · refine ⟨i, _, a, r, ps, hg', hq, ?_, hemp⟩
      show Conv β (Ctx.δ (Ctx.substLast w Γ) 0 (Term.subst Γ.length w b.T)) _
      rw [Ctx.δ_substLast0 hw, Ctx.δ_append_some hw hv] at *
      exact hred
  · exfalso
    have hi' : i = Γ.length := by omega
    subst hi'
    rw [Ctx.get_append_last] at hg
    cases hg
    rw [Bind.shiftN_q] at hq
    rw [Bind.shiftN_T, Ctx.δ_append, Nat.zero_add,
      Ctx.δ_shiftN Γ 0 _ _ (by simp only [Nat.zero_add]; omega),
      show Γ.length + 1 - Γ.length + Γ.rigid = Γ.rigid + 1 by omega] at hred
    rcases hv with hv | hv <;> simp only [Ctx.δ, hv] at hred
    · exact hdead hq _ a r ps hred hemp
    · rw [Term.subst_shiftN] at hred
      exact hdead hq _ a r ps hred hemp

theorem Check.none_at {sp : List Term} (h : Check β Φ L sp .None Γ t T π u) (i : Nat) :
    π i = .None := by
  rw [h.none_uses _root_.rfl]; rfl

theorem Check.subst (hβ : Book.Closed β) (hΦ : Φ.Weak) {sp : List Term}
    (h : Check β Φ L sp q Γb t T π u)
    (hw : Term.Closed 0 w) (huw : Term.Closed 0 uw) (hv : b0.v = none ∨ b0.v = some w)
    (h0 : Check β Φ (LHS.void β) [] .None [] w b0.T Uses.zero .Qnt)
    (hefq : ∀ Γ, Φ.efq (Γ ++ [b0]) → Φ.efq (Ctx.substLast w Γ)) :
    ∀ (Γ : Ctx), Γb = Γ ++ [b0] → q ≠ .Many →
    (π Γ.length ≠ .None → ∃ πw, Check β Φ (LHS.void β) [] .Lone [] w b0.T πw uw) →
    Check β Φ (LHS.void β) sp q (Ctx.substLast w Γ) (Term.subst Γ.length w t)
      (Term.subst Γ.length w T) (Uses.del Γ.length π) (Term.subst Γ.length uw u) := by
  have hw0 : Term.shift 0 w = w := Term.shift_closed w 0 0 hw (Nat.le_refl 0)
  have huw0 : Term.shift 0 uw = uw := Term.shift_closed uw 0 0 huw (Nat.le_refl 0)
  induction h with
  | @var Γb i b L sp q hg =>
    intro Γ hΓ hq h1
    subst hΓ
    have hi := Ctx.get_lt hg
    simp only [List.length_append, List.length_singleton] at hi
    by_cases hin : i < Γ.length
    · rw [Ctx.get_append _ _ _ hin] at hg
      have e1 : Term.subst Γ.length w (.Var i) = .Var i := by
        simp [Term.subst, show ¬ i = Γ.length by omega, show ¬ Γ.length < i by omega]
      have e2 : Term.subst Γ.length uw (.Var i) = .Var i := by
        simp [Term.subst, show ¬ i = Γ.length by omega, show ¬ Γ.length < i by omega]
      rw [e1, Term.subst_era, e2, Uses.del_one_lt _ _ _ hin]
      exact .var (Ctx.get_substLast hw Γ i b hg)
    · have hi' : i = Γ.length := by omega
      subst hi'
      rw [Ctx.get_append_last] at hg
      cases hg
      have e1 : Term.subst Γ.length w (.Var Γ.length) = w := by simp [Term.subst]
      have e2 : Term.subst Γ.length uw (.Var Γ.length) = uw := by simp [Term.subst]
      rw [e1, Term.subst_era, e2, Uses.del_one_eq, Bind.shiftN_T, Term.subst_shiftN]
      cases q with
      | None =>
        have := h0.weaken_closed hβ hΦ (Ctx.substLast w Γ) sp
        rwa [Ctx.substLast_length] at this
      | Lone =>
        obtain ⟨πw, hw1⟩ := h1 (by simp [Uses.one])
        have := hw1.weaken_closed hβ hΦ (Ctx.substLast w Γ) sp
        rwa [Ctx.substLast_length, hw1.closed_uses] at this
      | Many => exact absurd _root_.rfl hq
  | ref hk hb _ _ =>
    intro Γ hΓ hq h1
    rw [Term.subst_closed _ 0 _ w (hβ.defn hk).1 (Nat.zero_le _), Uses.del_zero, Term.subst_era]
    have hj := Book.defn_lt hk
    exact .ref hk hb (fun _ _ => Nat.le_of_lt hj) (fun _ he => absurd he (Nat.ne_of_lt hj))
  | refA hk h0' =>
    intro Γ hΓ hq h1
    rw [Term.subst_closed _ 0 _ w (hβ.adtd hk).1 (Nat.zero_le _), Uses.del_zero, Term.subst_era]
    exact .refA hk h0'
  | adt hk =>
    intro Γ hΓ hq h1
    rw [Term.subst_closed _ 0 _ w (hβ.adtd hk).1 (Nat.zero_le _), Uses.del_zero, Term.subst_era]
    exact .adt hk
  | ctr hk hc hr =>
    intro Γ hΓ hq h1
    rw [Term.subst_closed _ 0 _ w (Term.retip_closed _ _ _ _ 0 ((hβ.adtd hk).2 _ _ hc))
      (Nat.zero_le _), Uses.del_zero, Term.subst_era]
    exact .ctr hk hc hr
  | typ hg ihg =>
    intro Γ hΓ hq h1
    rw [Uses.del_zero, Term.subst_era]
    exact .typ (ihg Γ hΓ (by simp) (fun hne => absurd (hg.none_at _) hne))
  | qnt => intro Γ hΓ hq h1; rw [Uses.del_zero]; exact .qnt
  | qua => intro Γ hΓ hq h1; rw [Uses.del_zero, Term.subst_era]; exact .qua
  | min _ _ iha ihb =>
    intro Γ hΓ hq h1
    rw [Uses.del_add, Term.subst_era]
    exact .min (iha Γ hΓ hq (fun hne => h1 (fun he => hne (Quant.add_eq_none he).1)))
      (ihb Γ hΓ hq (fun hne => h1 (fun he => hne (Quant.add_eq_none he).2)))
  | all hA hB ihA ihB =>
    intro Γ hΓ hq h1
    subst hΓ
    rw [Uses.del_zero, Term.subst_era]
    simp only [Term.subst, hw0]
    exact .all (ihA Γ _root_.rfl (by simp) (fun hne => absurd (hA.none_at _) hne))
      (ihB (⟨_, _, none⟩ :: Γ) _root_.rfl (by simp) (fun hne => absurd (hB.none_at _) hne))
  | lam hA _ hle ihA ihf =>
    intro Γ hΓ hq h1
    subst hΓ
    rw [Uses.del_tail, Term.subst_era]
    simp only [Term.subst, hw0, huw0]
    refine .lam (ihA Γ _root_.rfl (by simp) (fun hne => absurd (hA.none_at _) hne))
      (ihf (⟨_, _, none⟩ :: Γ) _root_.rfl hq h1) ?_
    rw [Uses.del_head]; exact hle
  | app _ _ ihf ihx =>
    intro Γ hΓ hq h1
    subst hΓ
    rw [Uses.del_add, Term.subst_subst0, hw0, Term.subst_era]
    have hf' := ihf Γ _root_.rfl hq (fun hne => h1 (fun he => hne (Quant.add_eq_none he).1))
    simp only [Term.subst, hw0] at hf'
    exact .app (hf'.sp _)
      (ihx Γ _root_.rfl (Quant.dem_ne_many hq) (fun hne => h1 (fun he => hne (Quant.add_eq_none he).2)))
  | appLam ha _ ih =>
    intro Γ hΓ hq h1
    subst hΓ
    have := ih Γ _root_.rfl hq h1
    rw [Term.subst_subst0, hw0] at this
    simp only [Term.subst, hw0]
    refine .appLam ?_ this
    rw [Ctx.substLast_length]
    simp only [List.length_append, List.length_singleton] at ha
    exact Term.Closed.subst hw _ _ _ (Nat.le_refl _) ha
  | let_ _ hA _ hle ihv ihA ihb =>
    intro Γ hΓ hq h1
    subst hΓ
    rw [Uses.del_add, Uses.del_tail, Term.subst_era]
    simp only [Term.subst, hw0, huw0]
    have hb' := ihb (⟨_, _, some _⟩ :: Γ) _root_.rfl hq
      (fun hne => h1 (fun he => hne (Quant.add_eq_none he).2))
    simp only [List.length_cons, Ctx.substLast, Bind.substAt, Option.map_some,
      Term.subst_shift0_closed hw] at hb'
    refine .let_ (ihv Γ _root_.rfl (Quant.dem_ne_many hq)
      (fun hne => h1 (fun he => hne (Quant.add_eq_none he).1)))
      (ihA Γ _root_.rfl (by simp) (fun hne => absurd (hA.none_at _) hne)) hb' ?_
    rw [Uses.del_head]; exact hle
  | eql hT ha hb ihT iha ihb =>
    intro Γ hΓ hq h1
    rw [Uses.del_zero, Term.subst_era]
    exact .eql (ihT Γ hΓ (by simp) (fun hne => absurd (hT.none_at _) hne))
      (iha Γ hΓ (by simp) (fun hne => absurd (ha.none_at _) hne))
      (ihb Γ hΓ (by simp) (fun hne => absurd (hb.none_at _) hne))
  | rfl hc =>
    intro Γ hΓ hq h1
    subst hΓ
    rw [Uses.del_zero, Term.subst_era]
    exact .rfl (Ctx.δ_last hw hv (Conv β) (fun d x y h => Conv.subst hβ h (Conv.refl w) d) Γ _ _ hc)
  | rwt _ hP _ ihe ihP ihf =>
    intro Γ hΓ hq h1
    rw [Uses.del_add, Term.subst_era]
    have hP' := ihP Γ hΓ (by simp) (fun hne => absurd (hP.none_at _) hne)
    rw [Term.subst_jmotive] at hP'
    exact .rwt (ihe Γ hΓ hq (fun hne => h1 (fun he => hne (Quant.add_eq_none he).1))) hP'
      (ihf Γ hΓ hq (fun hne => h1 (fun he => hne (Quant.add_eq_none he).2)))
  | mat hk hc hr hlen hlive hins hgoal _ _ ihh ihm =>
    intro Γ hΓ hq h1
    rw [Uses.del_join, Term.subst_era]
    simp only [Term.subst, Term.subst_apps, hw0]
    have hi' := hins.subst Γ.length w
    rw [Term.subst_closed _ 0 _ w ((hβ.adtd hk).2 _ _ hc) (Nat.zero_le _)] at hi'
    have hg' := hgoal.subst Γ.length w
    simp only [Term.subst_apps, Term.subst, hw0] at hg'
    refine Check.mat hk hc hr (by simp [hlen]) hlive hi' hg'
      (ihh Γ hΓ hq (fun hne => h1 (fun he => hne (Quant.join_eq_none he).1))) ?_
    have := ihm Γ hΓ hq (fun hne => h1 (fun he => hne (Quant.join_eq_none he).2))
    simp only [Term.subst, Term.subst_apps, hw0] at this
    exact this
  | efq hk hlive hd =>
    intro Γ hΓ hq h1
    subst hΓ
    rw [Uses.del_zero, Term.subst_era]
    simp only [Term.subst, Term.subst_apps, hw0]
    exact .efq hk hlive (hd.imp id (hefq Γ))
  | cnv _ hc iht =>
    intro Γ hΓ hq h1
    subst hΓ
    exact .cnv (iht Γ _root_.rfl hq h1)
      (Ctx.δ_last hw hv Φ.conv (fun d x y h => hΦ.subst d w x y h) Γ _ _ hc)

-- the standard policy: the substituted binder must not be the live emptied
-- binding that justified an Efq (hdead), as no derivation survives that
theorem Check.subst_std (hβ : Book.Closed β) {sp : List Term}
    (h : Check β (Pol.std β) L sp q (Γ ++ [b0]) t T π u)
    (hq : q ≠ .Many) (hw : Term.Closed 0 w) (huw : Term.Closed 0 uw)
    (hv : b0.v = none ∨ b0.v = some w)
    (h0 : Check β (Pol.std β) (LHS.void β) [] .None [] w b0.T Uses.zero .Qnt)
    (h1 : π Γ.length ≠ .None →
      ∃ πw, Check β (Pol.std β) (LHS.void β) [] .Lone [] w b0.T πw uw)
    (hdead : b0.q ≠ .None → ∀ m a r ps,
      Conv β (Term.shiftN m b0.T) (Term.apps (.Adt a r) ps) → ¬ Book.empty β a r) :
    Check β (Pol.std β) (LHS.void β) sp q (Ctx.substLast w Γ) (Term.subst Γ.length w t)
      (Term.subst Γ.length w T) (Uses.del Γ.length π) (Term.subst Γ.length uw u) :=
  Check.subst hβ (Pol.std_weak hβ) h hw huw hv h0 (CtxDead.substLast hβ hw hv hdead) Γ
    _root_.rfl hq h1

-- ============================================================================
-- METATHEORY §D6 — filling natives: typing only grows when a bodiless
-- definition gains a body. Reduction, conversion, fitting, descent and
-- validity are monotone in the book's bodies
-- ============================================================================

theorem Book.tld_defn (h : Book.tld β k = some (.defn d)) : Book.defn β k = some d := by
  simp [Book.defn, h]

theorem Book.tld_adt (h : Book.tld β k = some (.adt A)) : Book.adt β k = some A := by
  simp [Book.adt, h]

theorem Book.adt_tld (h : Book.adt β k = some A) : Book.tld β k = some (.adt A) := by
  unfold Book.adt at h
  split at h
  case _ heq => cases h; exact heq
  case _ => cases h

theorem Book.tld_some : ∀ {β : Book} {k : Nat}, k < β.length → ∃ t, Book.tld β k = some t := by
  intro β
  induction β with
  | nil => intro k h; cases h
  | cons d β ih =>
    intro k h
    cases k with
    | zero => exact ⟨d, rfl⟩
    | succ k => exact ih (by simp only [List.length_cons] at h; omega)

theorem Book.fill.adt (hf : Book.fill β β') (h : Book.adt β k = some A) :
    Book.adt β' k = some A :=
  ((hf.2 k).1 A).mp h

theorem Book.fill.defn (hf : Book.fill β β') (h : Book.defn β k = some d) :
    ∃ d', Book.defn β' k = some d' ∧ d'.n = d.n ∧ d'.qs = d.qs ∧ d'.ty = d.ty ∧
      d'.b = d.b ∧ (d.body ≠ none → d'.body = d.body) :=
  (hf.2 k).2 d h

-- the definitions of the filled book come from the old one
theorem Book.fill.defn_inv (hf : Book.fill β β') (h : Book.defn β' k = some d') :
    ∃ d, Book.defn β k = some d ∧ d'.n = d.n ∧ d'.qs = d.qs ∧ d'.ty = d.ty ∧
      d'.b = d.b ∧ (d.body ≠ none → d'.body = d.body) := by
  have hk : k < β.length := by rw [hf.1]; exact Book.tld_lt (Book.defn_tld h)
  obtain ⟨t, ht⟩ := Book.tld_some hk
  cases t with
  | adt A =>
    have := Book.adt_tld (hf.adt (Book.tld_adt ht))
    rw [Book.defn_tld h] at this
    cases this
  | defn d =>
    obtain ⟨d'', hd'', hn, hqs, hty, hb, hbody⟩ := hf.defn (Book.tld_defn ht)
    rw [h] at hd''
    cases hd''
    exact ⟨d, Book.tld_defn ht, hn, hqs, hty, hb, hbody⟩

theorem Book.empty.fill (hf : Book.fill β β') (h : Book.empty β a r) : Book.empty β' a r := by
  obtain ⟨A, hA, hc⟩ := h
  exact ⟨A, hf.adt hA, hc⟩

theorem Step.fill (hf : Book.fill β β') (h : Step β p a b) : Step β' p a b := by
  induction h with
  | dref hk hb hs hn =>
    obtain ⟨d', hk', hn', _, _, _, hbody⟩ := hf.defn hk
    exact .dref hk' (by rw [hbody (by rw [hb]; exact Option.some_ne_none _)]; exact hb) hs
      (by rw [hn']; exact hn)
  | drefS hp hk hb hs =>
    obtain ⟨d', hk', _, _, _, _, hbody⟩ := hf.defn hk
    exact .drefS hp hk' (by rw [hbody (by rw [hb]; exact Option.some_ne_none _)]; exact hb) hs
  | aref hk hpn => exact .aref (hf.adt hk) hpn
  | matc hk hc hps hxs => exact .matc (hf.adt hk) hc hps hxs
  | matm hne => exact .matm hne
  | beta => exact .beta
  | let_ => exact .let_
  | rwt => exact .rwt
  | minLM => exact .minLM
  | minLN => exact .minLN
  | minRM => exact .minRM
  | minRN => exact .minRN
  | minLL => exact .minLL
  | eta hp ho => exact .eta hp ho
  | typ_g hp _ ih => exact .typ_g hp ih
  | min_a _ ih => exact .min_a ih
  | min_b _ ih => exact .min_b ih
  | all_a hp _ ih => exact .all_a hp ih
  | all_b hp _ ih => exact .all_b hp ih
  | lam_f hp _ ih => exact .lam_f hp ih
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
  | let_b hp _ ih => exact .let_b hp ih

theorem Red.fill (hf : Book.fill β β') (h : Red β p a b) : Red β' p a b := by
  induction h with
  | refl => exact .refl
  | step s _ ih => exact .step (s.fill hf) ih

theorem Conv.fill (hf : Book.fill β β') (h : Conv β a b) : Conv β' a b := by
  obtain ⟨c, h1, h2⟩ := h
  exact ⟨c, h1.fill hf, h2.fill hf⟩

theorem KLe.fill (hf : Book.fill β β') (h : KLe β g k) : KLe β' g k := by
  induction h with
  | many r => exact .many (r.fill hf)
  | lone r hq => exact .lone (r.fill hf) hq
  | minL r _ _ ih1 ih2 => exact .minL (r.fill hf) ih1 ih2
  | minR1 r _ ih => exact .minR1 (r.fill hf) ih
  | minR2 r _ ih => exact .minR2 (r.fill hf) ih
  | conv c => exact .conv (c.fill hf)

theorem Le.fill (hf : Book.fill β β') (h : Le β a b) : Le β' a b := by
  induction h with
  | conv c => exact .conv (c.fill hf)
  | red r1 r2 _ ih => exact .red (r1.fill hf) (r2.fill hf) ih
  | typ hk => exact .typ (hk.fill hf)
  | all _ _ ih1 ih2 => exact .all ih1 ih2
  | adt hr hl hc => exact .adt hr hl (fun i p p' h1 h2 => (hc i p p' h1 h2).fill hf)

theorem CtxDead.fill (hf : Book.fill β β') (h : CtxDead β Γ) : CtxDead β' Γ := by
  obtain ⟨i, b, a, r, ps, hg, hq, hred, hemp⟩ := h
  exact ⟨i, b, a, r, ps, hg, hq, hred.fill hf, hemp.fill hf⟩

mutual
theorem PEq.fill (hf : Book.fill β β') : PEq β t p → PEq β' t p
  | .var => .var
  | .ctr hk hc hps hxs hs => .ctr (hf.adt hk) hc hps hxs (PEqs.fill hf hs)
theorem PEqs.fill (hf : Book.fill β β') : PEqs β xs ys → PEqs β' xs ys
  | .nil => .nil
  | .cons h hs => .cons (PEq.fill hf h) (PEqs.fill hf hs)
end

mutual
theorem PLt.fill (hf : Book.fill β β') : PLt β t p → PLt β' t p
  | .subEq hk hc hl hy he => .subEq (hf.adt hk) hc hl hy (PEq.fill hf he)
  | .subLt hk hc hl hy hl' => .subLt (hf.adt hk) hc hl hy (PLt.fill hf hl')
  | .ctr hk hc hps hxs hs => .ctr (hf.adt hk) hc hps hxs (PLts.fill hf hs)
theorem PLts.fill (hf : Book.fill β β') : PLts β xs ys → PLts β' xs ys
  | .here h hs => .here (PLt.fill hf h) (PLes.fill hf hs)
  | .there h hs => .there (PEq.fill hf h) (PLts.fill hf hs)
theorem PLes.fill (hf : Book.fill β β') : PLes β xs ys → PLes β' xs ys
  | .nil => .nil
  | .consEq h hs => .consEq (PEq.fill hf h) (PLes.fill hf hs)
  | .consLt h hs => .consLt (PLt.fill hf h) (PLes.fill hf hs)
end

theorem SpineLt.fill (hf : Book.fill β β') (h : SpineLt β qs j cs ts) : SpineLt β' qs j cs ts := by
  induction h with
  | here hq hl => exact .here hq (hl.fill hf)
  | skip hq _ ih => exact .skip hq ih
  | there hq he _ ih => exact .there hq (he.fill hf) ih

theorem Check.fill (hf : Book.fill β β') (hc : ∀ x y, Φ.conv x y → Φ'.conv x y)
    (he : ∀ Γ, Φ.efq Γ → Φ'.efq Γ) {sp : List Term}
    (h : Check β Φ L sp q Γ t T π u) : Check β' Φ' L sp q Γ t T π u := by
  induction h with
  | var hg => exact .var hg
  | ref hk hb hw hd =>
    obtain ⟨d', hk', _, _, hty, hbd, hbody⟩ := hf.defn hk
    rw [← hty]
    refine .ref hk' ?_ ?_ (fun hq he => (hd hq he).fill hf)
    · intro hq
      rcases hb hq with h | h
      · left; rw [hbody h]; exact h
      · right; rw [hbd]; exact h
    · intro hq h'; rw [hbd] at h'; exact hw hq h'
  | refA hk h0 => exact .refA (hf.adt hk) h0
  | adt hk => exact .adt (hf.adt hk)
  | ctr hk hc' hr => exact .ctr (hf.adt hk) hc' hr
  | typ _ ihg => exact .typ ihg
  | qnt => exact .qnt
  | qua => exact .qua
  | min _ _ iha ihb => exact .min iha ihb
  | all _ _ ihA ihB => exact .all ihA ihB
  | lam _ _ hle ihA ihf => exact .lam ihA ihf hle
  | app _ _ ihf ihx => exact .app ihf ihx
  | appLam ha _ ih => exact .appLam ha ih
  | let_ _ _ _ hle ihv ihA ihb => exact .let_ ihv ihA ihb hle
  | eql _ _ _ ihT iha ihb => exact .eql ihT iha ihb
  | rfl hc' => exact .rfl (hc'.fill hf)
  | rwt _ _ _ ihe ihP ihf => exact .rwt ihe ihP ihf
  | mat hk hc' hr hlen hlive hins hgoal _ _ ihh ihm =>
    exact .mat (hf.adt hk) hc' hr hlen hlive hins hgoal ihh ihm
  | efq hk hlive hd => exact .efq (hf.adt hk) hlive (hd.imp (Book.empty.fill hf) (he _))
  | cnv _ hc' iht => exact .cnv iht (hc _ _ hc')

theorem Check.fill_std (hf : Book.fill β β') {sp : List Term}
    (h : Check β (Pol.std β) L sp q Γ t T π u) : Check β' (Pol.std β') L sp q Γ t T π u :=
  h.fill hf (fun _ _ (hl : Le β _ _) => hl.fill hf) (fun _ (hd : CtxDead β _) => hd.fill hf)

theorem Tree.fill (hf : Book.fill β β') (h : Tree β n t) : Tree β' n t := by
  induction h with
  | leaf => exact .leaf
  | lam _ ih => exact .lam ih
  | mat hk hc _ _ ihh ihm => exact .mat (hf.adt hk) hc ihh ihm
  | efq => exact .efq

theorem STele.fill (hf : Book.fill β β') : ∀ n T G, STele β n T G → STele β' n T G := by
  intro n
  induction n with
  | zero => intro T G h; exact Red.fill hf h
  | succ n ih =>
    intro T G h
    obtain ⟨q, K, B, rfl, h'⟩ := h
    exact ⟨q, K, B, rfl, ih B G h'⟩

theorem TeleQs.fill (hf : Book.fill β β') (h : TeleQs β T n qs) : TeleQs β' T n qs := by
  induction h with
  | nil => exact .nil
  | cons r _ ih => exact .cons (r.fill hf) ih

theorem CtrOk.fill (hf : Book.fill β β') : ∀ (Γ : Ctx) (i : Nat) (T : Term),
    CtrOk β k pn G Γ i T → CtrOk β' k pn G Γ i T := by
  intro Γ i T
  induction T generalizing Γ i with
  | All q A B _ ihB =>
    intro h
    obtain ⟨⟨π, hA⟩, hB⟩ := h
    exact ⟨⟨π, hA.fill_std hf⟩, ihB _ _ hB⟩
  | _ => intro _; trivial

-- the wall down: a derivation with the wall up is one without it
theorem Check.unwall {sp : List Term} (h : Check β Φ L' sp q Γ t T π u) :
    ∀ L, L' = L.up → Check β Φ L sp q Γ t T π u := by
  induction h with
  | var hg => intro L hL; exact .var hg
  | ref hk hbd hw hd =>
    intro L hL; subst hL
    exact .ref hk hbd (fun hq _ => hw hq (Or.inl _root_.rfl)) hd
  | refA hk h0 => intro L hL; exact .refA hk h0
  | adt hk => intro L hL; exact .adt hk
  | ctr hk hc hr => intro L hL; exact .ctr hk hc hr
  | typ _ ihg => intro L hL; exact .typ (ihg L hL)
  | qnt => intro L hL; exact .qnt
  | qua => intro L hL; exact .qua
  | min _ _ iha ihb => intro L hL; exact .min (iha L hL) (ihb L hL)
  | all _ _ ihA ihB =>
    intro L hL; subst hL
    exact .all (ihA L _root_.rfl) (ihB L.shift (LHS.up_shift L).symm)
  | lam _ _ hle ihA ihf =>
    intro L hL; subst hL
    exact .lam (ihA L _root_.rfl) (ihf L.lam (LHS.up_lam L).symm) hle
  | app _ _ ihf ihx => intro L hL; exact .app (ihf L hL) (ihx L hL)
  | appLam ha _ ih => intro L hL; exact .appLam ha (ih L hL)
  | let_ _ _ _ hle ihv ihA ihb =>
    intro L hL; subst hL
    exact .let_ (ihv L _root_.rfl) (ihA L _root_.rfl) (ihb L.shift (LHS.up_shift L).symm) hle
  | eql _ _ _ ihT iha ihb => intro L hL; exact .eql (ihT L hL) (iha L hL) (ihb L hL)
  | rfl hc => intro L hL; exact .rfl hc
  | rwt _ _ _ ihe ihP ihf => intro L hL; exact .rwt (ihe L hL) (ihP L hL) (ihf L hL)
  | mat hk hc hr hlen hlive hins hgoal _ _ ihh ihm =>
    intro L hL; subst hL
    exact .mat hk hc hr hlen hlive hins hgoal (ihh _ (LHS.up_mat L _ _ _).symm) (ihm L _root_.rfl)
  | efq hk hlive hd => intro L hL; exact .efq hk hlive hd
  | cnv _ hc iht => intro L hL; exact .cnv (iht L hL) hc

-- the new bodies of a filling validate in the old book, with the wall up
-- (what Book.Native promises; a filling of garbage does not preserve Ok)
def Book.fillOk (β β' : Book) : Prop :=
  ∀ k d d', Book.defn β k = some d → Book.defn β' k = some d' → d.body = none →
    ∀ b, d'.body = some b → Tree β d.n b ∧
      ∃ π u, Check β (Pol.std β) ⟨k, .Ref k, d.n, d.qs, true⟩ [] .Lone [] b d.ty π u

theorem Book.Ok.fill (hf : Book.fill β β') (hok' : Book.fillOk β β') (hok : Book.Ok β) :
    Book.Ok β' := by
  intro k t hk
  cases t with
  | adt A =>
    have hA := Book.adt_tld (((hf.2 k).1 A).mpr (Book.tld_adt hk))
    obtain ⟨⟨π, hs⟩, G, hst, hc⟩ := hok k _ hA
    refine ⟨⟨π, hs.fill_std hf⟩, G, STele.fill hf _ _ _ hst, fun c C hcC => ?_⟩
    exact ⟨(hc c C hcC).1, CtrOk.fill hf _ _ _ (hc c C hcC).2⟩
  | defn d' =>
    obtain ⟨d, hd, hn, hqs, hty, hb, hbody⟩ := hf.defn_inv (Book.tld_defn hk)
    obtain ⟨⟨π, hs⟩, htq, hnat, hbodies⟩ := hok k _ (Book.defn_tld hd)
    refine ⟨⟨π, by rw [hty]; exact hs.fill_std hf⟩, by rw [hty, hn, hqs]; exact htq.fill hf, ?_, ?_⟩
    · intro hnone
      rw [hb]
      by_cases h0 : d.body = none
      · exact hnat h0
      · rw [hbody h0] at hnone; exact absurd hnone h0
    · intro b hb'
      by_cases h0 : d.body = none
      · obtain ⟨ht, π', u, hc⟩ := hok' k d d' hd (Book.tld_defn hk) h0 b hb'
        refine ⟨by rw [hn]; exact ht.fill hf, π', u, ?_⟩
        rw [hn, hqs, hty]
        exact (hc.fill_std hf).unwall _ _root_.rfl
      · rw [hbody h0] at hb'
        obtain ⟨ht, π', u, hc⟩ := hbodies b hb'
        refine ⟨by rw [hn]; exact ht.fill hf, π', u, ?_⟩
        rw [hn, hqs, hty]
        exact hc.fill_std hf

theorem Book.Wall.fill (hf : Book.fill β β') (hok' : Book.fillOk β β') (hw : Book.Wall β) :
    Book.Wall β' := by
  intro k d' b hk hb'
  obtain ⟨d, hd, hn, hqs, hty, _, hbody⟩ := hf.defn_inv hk
  rw [hn, hqs, hty]
  by_cases h0 : d.body = none
  · obtain ⟨_, π, u, hc⟩ := hok' k d d' hd hk h0 b hb'
    exact ⟨π, u, hc.fill_std hf⟩
  · rw [hbody h0] at hb'
    obtain ⟨π, u, hc⟩ := hw k d b hd hb'
    exact ⟨π, u, hc.fill_std hf⟩

-- a book with natives has a filling: each bodiless definition takes the
-- body its Book.Native witness names
noncomputable def Book.fillOne (β : Book) (hN : Book.Native β) (k : Nat) : TLD → TLD
  | .adt A => .adt A
  | .defn d =>
    if h : Book.defn β k = some d ∧ d.body = none then
      .defn { d with body := some (hN k d h.1 h.2).choose }
    else .defn d

noncomputable def Book.fillFrom (β : Book) (hN : Book.Native β) : Nat → Book → Book
  | _, [] => []
  | k, t :: ts => Book.fillOne β hN k t :: Book.fillFrom β hN (k + 1) ts

theorem Book.fillFrom_length (β : Book) (hN : Book.Native β) : ∀ (k : Nat) (ts : Book),
    (Book.fillFrom β hN k ts).length = ts.length := by
  intro k ts
  induction ts generalizing k with
  | nil => rfl
  | cons t ts ih => simp only [Book.fillFrom, List.length_cons, ih]

theorem Book.fillFrom_tld (β : Book) (hN : Book.Native β) : ∀ (ts : Book) (k0 k : Nat),
    Book.tld (Book.fillFrom β hN k0 ts) k = (Book.tld ts k).map (Book.fillOne β hN (k0 + k)) := by
  intro ts
  induction ts with
  | nil => intro k0 k; rfl
  | cons t ts ih =>
    intro k0 k
    cases k with
    | zero => rfl
    | succ k =>
      simp only [Book.fillFrom, Book.tld]
      rw [ih (k0 + 1) k, show k0 + 1 + k = k0 + (k + 1) by omega]

theorem Book.fillOne_defn (β : Book) (hN : Book.Native β) (k : Nat) (d : DefD) :
    ∃ d', Book.fillOne β hN k (.defn d) = .defn d' ∧ d'.n = d.n ∧ d'.qs = d.qs ∧
      d'.ty = d.ty ∧ d'.b = d.b ∧ (d.body ≠ none → d'.body = d.body) ∧
      (Book.defn β k = some d → d'.body ≠ none) ∧
      (Book.defn β k = some d → d.body = none → ∀ b, d'.body = some b →
        Tree β d.n b ∧
        ∃ π u, Check β (Pol.std β) ⟨k, .Ref k, d.n, d.qs, true⟩ [] .Lone [] b d.ty π u) := by
  simp only [Book.fillOne]
  split
  case _ h =>
    refine ⟨_, rfl, rfl, rfl, rfl, rfl, fun hb => absurd h.2 hb, fun _ => Option.some_ne_none _,
      fun _ _ b hb => ?_⟩
    obtain ⟨π, u, ht, hc⟩ := (hN k _ h.1 h.2).choose_spec
    cases hb
    exact ⟨ht, π, u, hc⟩
  case _ h =>
    exact ⟨d, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, fun hd hb => h ⟨hd, hb⟩,
      fun hd hb _ _ => (h ⟨hd, hb⟩).elim⟩

theorem Book.fill_exists (hN : Book.Native β) :
    ∃ β', Book.fill β β' ∧ Book.fillOk β β' ∧ Book.Filled β' := by
  refine ⟨Book.fillFrom β hN 0 β, ⟨(Book.fillFrom_length β hN 0 β).symm, fun k => ⟨?_, ?_⟩⟩, ?_, ?_⟩
  · intro A
    unfold Book.adt
    rw [Book.fillFrom_tld, Nat.zero_add]
    cases h : Book.tld β k with
    | none => simp
    | some t =>
      cases t with
      | adt A' => simp [Book.fillOne]
      | defn d =>
        obtain ⟨d', hd', _⟩ := Book.fillOne_defn β hN k d
        simp [hd']
  · intro d hd
    obtain ⟨d', hd', hn, hqs, hty, hb, hbody, _, _⟩ := Book.fillOne_defn β hN k d
    refine ⟨d', ?_, hn, hqs, hty, hb, hbody⟩
    apply Book.tld_defn
    rw [Book.fillFrom_tld, Nat.zero_add, Book.defn_tld hd, Option.map_some, hd']
  · intro k d d' hd hd'' h0 b hb
    obtain ⟨d1, hd1, _, _, _, _, _, _, hok⟩ := Book.fillOne_defn β hN k d
    have : Book.tld (Book.fillFrom β hN 0 β) k = some (.defn d1) := by
      rw [Book.fillFrom_tld, Nat.zero_add, Book.defn_tld hd, Option.map_some, hd1]
    rw [Book.defn_tld hd''] at this
    cases this
    exact hok hd h0 b hb
  · intro k d' hd'
    have ht := Book.defn_tld hd'
    rw [Book.fillFrom_tld, Nat.zero_add] at ht
    cases h : Book.tld β k with
    | none => rw [h] at ht; cases ht
    | some t =>
      rw [h] at ht
      cases t with
      | adt A => simp [Book.fillOne] at ht
      | defn d =>
        obtain ⟨d1, hd1, _, _, _, _, _, hfilled, _⟩ := Book.fillOne_defn β hN k d
        rw [Option.map_some, hd1] at ht
        cases ht
        exact hfilled (Book.tld_defn h)


-- ============================================================================
-- METATHEORY §E — generation: every derivation of a given subject shape
-- factors through its rule, modulo the conversion accumulated by cnv. The
-- inversions hold for any policy whose conversion is a preorder; the
-- standard policy is one (C's Le.refl / Le.trans).
-- ============================================================================

structure Pol.Pre (Φ : Pol) : Prop where
  refl  : ∀ a, Φ.conv a a
  trans : ∀ {a b c}, Φ.conv a b → Φ.conv b c → Φ.conv a c

theorem Pol.std_pre (hβ : Book.Closed β) : Pol.Pre (Pol.std β) :=
  ⟨fun a => Le.refl a, fun h1 h2 => Le.trans hβ h1 h2⟩

theorem Check.var_inv (hΦ : Pol.Pre Φ) {sp : List Term} (h : Check β Φ L sp q Γ (.Var i) T π u) :
    ∃ b, Ctx.get Γ i = some b ∧ Φ.conv (Ctx.δ Γ 0 b.T) (Ctx.δ Γ 0 T) ∧
      π = Uses.one i q ∧ u = Term.era q (.Var i) := by
  generalize he : Term.Var i = t0 at h
  induction h <;> try exact Term.noConfusion he
  case var hg => cases he; exact ⟨_, hg, hΦ.refl _, _root_.rfl, _root_.rfl⟩
  case cnv _ hc ih =>
    obtain ⟨b, hg, hcv, hπ, hu⟩ := ih he
    exact ⟨b, hg, hΦ.trans hcv hc, hπ, hu⟩

theorem Check.ref_inv (hΦ : Pol.Pre Φ) {sp : List Term} (h : Check β Φ L sp q Γ (.Ref j) T π u) :
    (∃ d, Book.defn β j = some d ∧
      (q ≠ .None → d.body ≠ none ∨ d.b = true) ∧
      (q ≠ .None → L.w = true ∨ d.b = false → j ≤ L.k) ∧
      (q ≠ .None → j = L.k →
        SpineLt β L.qs 0 (L.cols.map (Ctx.δ Γ 0)) (sp.map (Ctx.δ Γ 0))) ∧
      Φ.conv (Ctx.δ Γ 0 d.ty) (Ctx.δ Γ 0 T) ∧ π = Uses.zero ∧ u = Term.era q (.Ref j)) ∨
    (∃ A, Book.adt β j = some A ∧ A.pn = 0 ∧
      Φ.conv (Ctx.δ Γ 0 A.sig) (Ctx.δ Γ 0 T) ∧ π = Uses.zero ∧ u = Term.era q (.Ref j)) := by
  generalize he : Term.Ref j = t0 at h
  induction h <;> try exact Term.noConfusion he
  case ref hk hb hw hd => cases he; exact .inl ⟨_, hk, hb, hw, hd, hΦ.refl _, _root_.rfl, _root_.rfl⟩
  case refA hk h0 => cases he; exact .inr ⟨_, hk, h0, hΦ.refl _, _root_.rfl, _root_.rfl⟩
  case cnv _ hc ih =>
    rcases ih he with ⟨d, hk, hb, hw, hd, hcv, hπ, hu⟩ | ⟨A, hk, h0, hcv, hπ, hu⟩
    · exact .inl ⟨d, hk, hb, hw, hd, hΦ.trans hcv hc, hπ, hu⟩
    · exact .inr ⟨A, hk, h0, hΦ.trans hcv hc, hπ, hu⟩

theorem Check.adt_inv (hΦ : Pol.Pre Φ) {sp : List Term} (h : Check β Φ L sp q Γ (.Adt a r) T π u) :
    ∃ A, Book.adt β a = some A ∧ Φ.conv (Ctx.δ Γ 0 A.sig) (Ctx.δ Γ 0 T) ∧
      π = Uses.zero ∧ u = Term.era q (.Adt a r) := by
  generalize he : Term.Adt a r = t0 at h
  induction h <;> try exact Term.noConfusion he
  case adt hk => cases he; exact ⟨_, hk, hΦ.refl _, _root_.rfl, _root_.rfl⟩
  case cnv _ hc ih =>
    obtain ⟨A, hk, hcv, hπ, hu⟩ := ih he
    exact ⟨A, hk, hΦ.trans hcv hc, hπ, hu⟩

theorem Check.ctr_inv (hΦ : Pol.Pre Φ) {sp : List Term} (h : Check β Φ L sp q Γ (.Ctr a c) T π u) :
    ∃ A C r, Book.adt β a = some A ∧ AdtD.ctr A c = some C ∧ c ∉ r ∧
      Φ.conv (Ctx.δ Γ 0 (Term.retip r A.pn (A.pn + C.fn) C.ty)) (Ctx.δ Γ 0 T) ∧
      π = Uses.zero ∧ u = Term.era q (.Ctr a c) := by
  generalize he : Term.Ctr a c = t0 at h
  induction h <;> try exact Term.noConfusion he
  case ctr hk hc hr => cases he; exact ⟨_, _, _, hk, hc, hr, hΦ.refl _, _root_.rfl, _root_.rfl⟩
  case cnv _ hc ih =>
    obtain ⟨A, C, r, hk, hc0, hr, hcv, hπ, hu⟩ := ih he
    exact ⟨A, C, r, hk, hc0, hr, hΦ.trans hcv hc, hπ, hu⟩

theorem Check.typ_inv (hΦ : Pol.Pre Φ) {sp : List Term} (h : Check β Φ L sp q Γ (.Typ g) T π u) :
    ∃ πg, Check β Φ L [] .None Γ g .Qnt πg .Qnt ∧
      Φ.conv (Ctx.δ Γ 0 (.Typ (.Qua .Lone))) (Ctx.δ Γ 0 T) ∧
      π = Uses.zero ∧ u = Term.era q (.Typ .Qnt) := by
  generalize he : Term.Typ g = t0 at h
  induction h <;> try exact Term.noConfusion he
  case typ hg _ => cases he; exact ⟨_, hg, hΦ.refl _, _root_.rfl, _root_.rfl⟩
  case cnv _ hc ih =>
    obtain ⟨πg, hg, hcv, hπ, hu⟩ := ih he
    exact ⟨πg, hg, hΦ.trans hcv hc, hπ, hu⟩

theorem Check.qnt_inv (hΦ : Pol.Pre Φ) {sp : List Term} (h : Check β Φ L sp q Γ .Qnt T π u) :
    Φ.conv (Ctx.δ Γ 0 (.Typ (.Qua .Lone))) (Ctx.δ Γ 0 T) ∧ π = Uses.zero ∧ u = .Qnt := by
  generalize he : Term.Qnt = t0 at h
  induction h <;> try exact Term.noConfusion he
  case qnt => exact ⟨hΦ.refl _, _root_.rfl, _root_.rfl⟩
  case cnv _ hc ih =>
    obtain ⟨hcv, hπ, hu⟩ := ih he
    exact ⟨hΦ.trans hcv hc, hπ, hu⟩

theorem Check.qua_inv (hΦ : Pol.Pre Φ) {sp : List Term} (h : Check β Φ L sp q Γ (.Qua q') T π u) :
    Φ.conv (Ctx.δ Γ 0 .Qnt) (Ctx.δ Γ 0 T) ∧ π = Uses.zero ∧ u = Term.era q (.Qua q') := by
  generalize he : Term.Qua q' = t0 at h
  induction h <;> try exact Term.noConfusion he
  case qua => cases he; exact ⟨hΦ.refl _, _root_.rfl, _root_.rfl⟩
  case cnv _ hc ih =>
    obtain ⟨hcv, hπ, hu⟩ := ih he
    exact ⟨hΦ.trans hcv hc, hπ, hu⟩

theorem Check.min_inv (hΦ : Pol.Pre Φ) {sp : List Term} (h : Check β Φ L sp q Γ (.Min a b) T π u) :
    ∃ πa ua πb ub, Check β Φ L [] q Γ a .Qnt πa ua ∧ Check β Φ L [] q Γ b .Qnt πb ub ∧
      Φ.conv (Ctx.δ Γ 0 .Qnt) (Ctx.δ Γ 0 T) ∧
      π = Uses.add πa πb ∧ u = Term.era q (.Min ua ub) := by
  generalize he : Term.Min a b = t0 at h
  induction h <;> try exact Term.noConfusion he
  case min ha hb _ _ => cases he; exact ⟨_, _, _, _, ha, hb, hΦ.refl _, _root_.rfl, _root_.rfl⟩
  case cnv _ hc ih =>
    obtain ⟨πa, ua, πb, ub, ha, hb, hcv, hπ, hu⟩ := ih he
    exact ⟨πa, ua, πb, ub, ha, hb, hΦ.trans hcv hc, hπ, hu⟩

theorem Check.all_inv (hΦ : Pol.Pre Φ) {sp : List Term} (h : Check β Φ L sp q Γ (.All q' A B) T π u) :
    ∃ πA πB, Check β Φ L [] .None Γ A (.Typ (.Qua q')) πA .Qnt ∧
      Check β Φ L.shift [] .None (⟨q', A, none⟩ :: Γ) B (.Typ (.Qua .Lone)) πB .Qnt ∧
      Φ.conv (Ctx.δ Γ 0 (.Typ (.Qua .Lone))) (Ctx.δ Γ 0 T) ∧
      π = Uses.zero ∧ u = Term.era q (.All q' .Qnt .Qnt) := by
  generalize he : Term.All q' A B = t0 at h
  induction h <;> try exact Term.noConfusion he
  case all hA hB _ _ => cases he; exact ⟨_, _, hA, hB, hΦ.refl _, _root_.rfl, _root_.rfl⟩
  case cnv _ hc ih =>
    obtain ⟨πA, πB, hA, hB, hcv, hπ, hu⟩ := ih he
    exact ⟨πA, πB, hA, hB, hΦ.trans hcv hc, hπ, hu⟩

theorem Check.lam_inv (hΦ : Pol.Pre Φ) {sp : List Term} (h : Check β Φ L sp q Γ (.Lam f) T π u) :
    ∃ q' A B πA π' uf, Check β Φ L [] .None Γ A (.Typ (.Qua q')) πA .Qnt ∧
      Check β Φ L.lam [] q (⟨q', A, none⟩ :: Γ) f B π' uf ∧ Quant.le (π' 0) q' ∧
      Φ.conv (Ctx.δ Γ 0 (.All q' A B)) (Ctx.δ Γ 0 T) ∧
      π = Uses.tail π' ∧ u = Term.era q (.Lam uf) := by
  generalize he : Term.Lam f = t0 at h
  induction h <;> try exact Term.noConfusion he
  case lam hA hf hle _ _ =>
    cases he; exact ⟨_, _, _, _, _, _, hA, hf, hle, hΦ.refl _, _root_.rfl, _root_.rfl⟩
  case cnv _ hc ih =>
    obtain ⟨q', A, B, πA, π', uf, hA, hf, hle, hcv, hπ, hu⟩ := ih he
    exact ⟨q', A, B, πA, π', uf, hA, hf, hle, hΦ.trans hcv hc, hπ, hu⟩

theorem Check.app_inv (hΦ : Pol.Pre Φ) {sp : List Term} (h : Check β Φ L sp q Γ (.App f x) T π u) :
    (∃ q' A B πf uf πx ux, Check β Φ L (x :: sp) q Γ f (.All q' A B) πf uf ∧
      Check β Φ L [] (Quant.dem q' q) Γ x A πx ux ∧
      Φ.conv (Ctx.δ Γ 0 (Term.subst 0 x B)) (Ctx.δ Γ 0 T) ∧
      π = Uses.add πf πx ∧ u = Term.era q (.App uf ux)) ∨
    (∃ g T0, f = .Lam g ∧ Term.Closed Γ.length x ∧
      Check β Φ L sp q Γ (Term.subst 0 x g) T0 π u ∧
      Φ.conv (Ctx.δ Γ 0 T0) (Ctx.δ Γ 0 T)) := by
  generalize he : Term.App f x = t0 at h
  induction h <;> try exact Term.noConfusion he
  case app hf hx _ _ =>
    cases he; exact .inl ⟨_, _, _, _, _, _, _, hf, hx, hΦ.refl _, _root_.rfl, _root_.rfl⟩
  case appLam ha hb _ => cases he; exact .inr ⟨_, _, _root_.rfl, ha, hb, hΦ.refl _⟩
  case cnv _ hc ih =>
    rcases ih he with ⟨q', A, B, πf, uf, πx, ux, hf, hx, hcv, hπ, hu⟩ | ⟨g, T0, hg, ha, hb, hcv⟩
    · exact .inl ⟨q', A, B, πf, uf, πx, ux, hf, hx, hΦ.trans hcv hc, hπ, hu⟩
    · exact .inr ⟨g, T0, hg, ha, hb, hΦ.trans hcv hc⟩

theorem Check.let_inv (hΦ : Pol.Pre Φ) {sp : List Term} (h : Check β Φ L sp q Γ (.Let qb v b) T π u) :
    ∃ A T0 πv uv πA π' ub, Check β Φ L [] (Quant.dem qb q) Γ v A πv uv ∧
      Check β Φ L [] .None Γ A (.Typ (.Qua qb)) πA .Qnt ∧
      Check β Φ L.shift [] q (⟨qb, A, some v⟩ :: Γ) b (Term.shift 0 T0) π' ub ∧
      Quant.le (π' 0) qb ∧ Φ.conv (Ctx.δ Γ 0 T0) (Ctx.δ Γ 0 T) ∧
      π = Uses.add πv (Uses.tail π') ∧ u = Term.era q (.Let qb uv ub) := by
  generalize he : Term.Let qb v b = t0 at h
  induction h <;> try exact Term.noConfusion he
  case let_ hv hA hb hle _ _ _ =>
    cases he; exact ⟨_, _, _, _, _, _, _, hv, hA, hb, hle, hΦ.refl _, _root_.rfl, _root_.rfl⟩
  case cnv _ hc ih =>
    obtain ⟨A, T0, πv, uv, πA, π', ub, hv, hA, hb, hle, hcv, hπ, hu⟩ := ih he
    exact ⟨A, T0, πv, uv, πA, π', ub, hv, hA, hb, hle, hΦ.trans hcv hc, hπ, hu⟩

theorem Check.eql_inv (hΦ : Pol.Pre Φ) {sp : List Term} (h : Check β Φ L sp q Γ (.Eql a b T') T π u) :
    ∃ πT πa πb, Check β Φ L [] .None Γ T' (.Typ (.Qua .Lone)) πT .Qnt ∧
      Check β Φ L [] .None Γ a T' πa .Qnt ∧ Check β Φ L [] .None Γ b T' πb .Qnt ∧
      Φ.conv (Ctx.δ Γ 0 (.Typ (.Qua .Many))) (Ctx.δ Γ 0 T) ∧
      π = Uses.zero ∧ u = Term.era q (.Eql .Qnt .Qnt .Qnt) := by
  generalize he : Term.Eql a b T' = t0 at h
  induction h <;> try exact Term.noConfusion he
  case eql hT ha hb _ _ _ =>
    cases he; exact ⟨_, _, _, hT, ha, hb, hΦ.refl _, _root_.rfl, _root_.rfl⟩
  case cnv _ hc ih =>
    obtain ⟨πT, πa, πb, hT, ha, hb, hcv, hπ, hu⟩ := ih he
    exact ⟨πT, πa, πb, hT, ha, hb, hΦ.trans hcv hc, hπ, hu⟩

theorem Check.rfl_inv (hΦ : Pol.Pre Φ) {sp : List Term} (h : Check β Φ L sp q Γ .Rfl T π u) :
    ∃ a b T0, Conv β (Ctx.δ Γ 0 a) (Ctx.δ Γ 0 b) ∧
      Φ.conv (Ctx.δ Γ 0 (.Eql a b T0)) (Ctx.δ Γ 0 T) ∧
      π = Uses.zero ∧ u = Term.era q .Rfl := by
  generalize he : Term.Rfl = t0 at h
  induction h <;> try exact Term.noConfusion he
  case rfl hab => exact ⟨_, _, _, hab, hΦ.refl _, _root_.rfl, _root_.rfl⟩
  case cnv _ hc ih =>
    obtain ⟨a, b, T0, hab, hcv, hπ, hu⟩ := ih he
    exact ⟨a, b, T0, hab, hΦ.trans hcv hc, hπ, hu⟩

theorem Check.rwt_inv (hΦ : Pol.Pre Φ) {sp : List Term} (h : Check β Φ L sp q Γ (.Rwt e P f) T π u) :
    ∃ a b T0 πe ue πP πf uf, Check β Φ L [] q Γ e (.Eql a b T0) πe ue ∧
      Check β Φ L [] .None Γ P (Term.jmotive a T0) πP .Qnt ∧
      Check β Φ L [] q Γ f (.App (.App P a) .Rfl) πf uf ∧
      Φ.conv (Ctx.δ Γ 0 (.App (.App P b) e)) (Ctx.δ Γ 0 T) ∧
      π = Uses.add πe πf ∧ u = Term.era q (.Rwt ue .Qnt uf) := by
  generalize he : Term.Rwt e P f = t0 at h
  induction h <;> try exact Term.noConfusion he
  case rwt he0 hP hf _ _ _ =>
    cases he; exact ⟨_, _, _, _, _, _, _, _, he0, hP, hf, hΦ.refl _, _root_.rfl, _root_.rfl⟩
  case cnv _ hc ih =>
    obtain ⟨a, b, T0, πe, ue, πP, πf, uf, he0, hP, hf, hcv, hπ, hu⟩ := ih he
    exact ⟨a, b, T0, πe, ue, πP, πf, uf, he0, hP, hf, hΦ.trans hcv hc, hπ, hu⟩

theorem Check.mat_inv (hΦ : Pol.Pre Φ) {sp : List Term} (h : Check β Φ L sp q Γ (.Mat a c hh mm) T π u) :
    ∃ A C r ps q' telF B G πh uh πm um,
      Book.adt β a = some A ∧ AdtD.ctr A c = some C ∧ c ∉ r ∧ ps.length = A.pn ∧
      (q ≠ .None → q' ≠ .None) ∧ Insts C.ty ps telF ∧
      MatGoal q' C.fn B (Term.apps (.Ctr a c) ps) telF G ∧
      Check β Φ (L.mat a c C.fn) [] q Γ hh G πh uh ∧
      Check β Φ L [] q Γ mm (.All q' (Term.apps (.Adt a (c :: r)) ps) B) πm um ∧
      Φ.conv (Ctx.δ Γ 0 (.All q' (Term.apps (.Adt a r) ps) B)) (Ctx.δ Γ 0 T) ∧
      π = Uses.join πh πm ∧ u = Term.era q (.Mat a c uh um) := by
  generalize he : Term.Mat a c hh mm = t0 at h
  induction h <;> try exact Term.noConfusion he
  case mat hk hc0 hr hlen hlive hins hgoal hh0 hm0 _ _ =>
    cases he
    exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, hk, hc0, hr, hlen, hlive, hins, hgoal, hh0, hm0,
      hΦ.refl _, _root_.rfl, _root_.rfl⟩
  case cnv _ hc ih =>
    obtain ⟨A, C, r, ps, q', telF, B, G, πh, uh, πm, um, hk, hc0, hr, hlen, hlive, hins, hgoal,
      hh0, hm0, hcv, hπ, hu⟩ := ih he
    exact ⟨A, C, r, ps, q', telF, B, G, πh, uh, πm, um, hk, hc0, hr, hlen, hlive, hins, hgoal,
      hh0, hm0, hΦ.trans hcv hc, hπ, hu⟩

theorem Check.efq_inv (hΦ : Pol.Pre Φ) {sp : List Term} (h : Check β Φ L sp q Γ .Efq T π u) :
    ∃ a A r q' ps B, Book.adt β a = some A ∧ (q ≠ .None → q' ≠ .None) ∧
      (Book.empty β a r ∨ Φ.efq Γ) ∧
      Φ.conv (Ctx.δ Γ 0 (.All q' (Term.apps (.Adt a r) ps) B)) (Ctx.δ Γ 0 T) ∧
      π = Uses.zero ∧ u = Term.era q .Efq := by
  generalize he : Term.Efq = t0 at h
  induction h <;> try exact Term.noConfusion he
  case efq hk hlive hd => exact ⟨_, _, _, _, _, _, hk, hlive, hd, hΦ.refl _, _root_.rfl, _root_.rfl⟩
  case cnv _ hc ih =>
    obtain ⟨a, A, r, q', ps, B, hk, hlive, hd, hcv, hπ, hu⟩ := ih he
    exact ⟨a, A, r, q', ps, B, hk, hlive, hd, hΦ.trans hcv hc, hπ, hu⟩

-- ============================================================================
-- METATHEORY §E2 — spines: a checked application spine walks the head's
-- type one fitted All at a time (Args: the arguments' demands, measures
-- and erasures collected along), and a walk rebuilds the checked spine.
-- ============================================================================

theorem Quant.add_assoc : ∀ a b c : Quant,
    Quant.add (Quant.add a b) c = Quant.add a (Quant.add b c) := by
  intro a b c; cases a <;> cases b <;> cases c <;> rfl

theorem Uses.add_zero (π : Uses) : Uses.add π Uses.zero = π := by
  funext i; show Quant.add (π i) .None = π i; cases π i <;> rfl

theorem Uses.zero_add (π : Uses) : Uses.add Uses.zero π = π := by
  funext i; rfl

theorem Uses.add_assoc (a b c : Uses) :
    Uses.add (Uses.add a b) c = Uses.add a (Uses.add b c) := by
  funext i; exact Quant.add_assoc _ _ _

theorem Term.era_apps_era (q : Quant) (f : Term) (us : List Term) :
    Term.era q (Term.apps (Term.era q f) us) = Term.era q (Term.apps f us) := by
  cases q <;> rfl

theorem Check.era_self {sp : List Term} (h : Check β Φ L sp q Γ t T π u) :
    Term.era q u = u := by
  cases q
  · exact (h.none_era _root_.rfl).symm
  all_goals rfl

-- the let expansion enters an All and commutes with a substitution below
-- its depth
theorem Ctx.δ_all : ∀ (Γ : Ctx) (d : Nat) (q : Quant) (A B : Term),
    Ctx.δ Γ d (.All q A B) = .All q (Ctx.δ Γ d A) (Ctx.δ Γ (d + 1) B) := by
  intro Γ
  induction Γ with
  | nil => intros; rfl
  | cons b Γ ih =>
    intro d q A B
    obtain ⟨_, _, v⟩ := b
    cases v <;> simp only [Ctx.δ, Term.subst, ih]
    rfl

theorem Ctx.δ_typ : ∀ (Γ : Ctx) (d : Nat) (g : Term),
    Ctx.δ Γ d (.Typ g) = .Typ (Ctx.δ Γ d g) := by
  intro Γ
  induction Γ with
  | nil => intros; rfl
  | cons b Γ ih =>
    intro d g
    obtain ⟨_, _, v⟩ := b
    cases v <;> simp only [Ctx.δ, Term.subst, ih]

theorem Ctx.δ_subst : ∀ (Γ : Ctx) (d e : Nat) (x B : Term), d ≤ e →
    Ctx.δ Γ e (Term.subst d x B) = Term.subst d (Ctx.δ Γ e x) (Ctx.δ Γ (e + 1) B) := by
  intro Γ
  induction Γ with
  | nil => intros; rfl
  | cons b Γ ih =>
    intro d e x B hde
    obtain ⟨_, _, v⟩ := b
    cases v <;> simp only [Ctx.δ]
    · exact ih d (e + 1) x B (by omega)
    · rw [Term.subst_subst B e d _ x hde, ih d e _ _ hde, Term.shift_shiftN e d _ hde]

inductive Args (β : Book) (Φ : Pol) (L : LHS) (q : Quant) (Γ : Ctx) :
    Term → List Term → Term → Uses → List Term → Prop
  | nil  : Args β Φ L q Γ T [] T Uses.zero []
  | cons : Φ.conv (Ctx.δ Γ 0 T0) (Ctx.δ Γ 0 (.All q' A B)) →
           Check β Φ L [] (Quant.dem q' q) Γ a A πa ua →
           Args β Φ L q Γ (Term.subst 0 a B) as T πs us →
           Args β Φ L q Γ T0 (a :: as) T (Uses.add πa πs) (ua :: us)

theorem Args.length (h : Args β Φ L q Γ T0 as T πs us) : us.length = as.length := by
  induction h with
  | nil => rfl
  | cons _ _ _ ih => simp [ih]

-- a walk restarts at any type fitting its start
theorem Args.le_start (hΦ : Pol.Pre Φ) (h : Args β Φ L q Γ T0 as T πs us)
    (hc : Φ.conv (Ctx.δ Γ 0 X) (Ctx.δ Γ 0 T0)) :
    ∃ T', Args β Φ L q Γ X as T' πs us ∧ Φ.conv (Ctx.δ Γ 0 T') (Ctx.δ Γ 0 T) := by
  cases h with
  | nil => exact ⟨X, .nil, hc⟩
  | cons hc0 ha hr => exact ⟨_, .cons (hΦ.trans hc hc0) ha hr, hΦ.refl _⟩

theorem Args.split (h : Args β Φ L q Γ T0 (as ++ bs) T πs us) :
    ∃ Tm πa ua πb ub, Args β Φ L q Γ T0 as Tm πa ua ∧ Args β Φ L q Γ Tm bs T πb ub ∧
      πs = Uses.add πa πb ∧ us = ua ++ ub := by
  induction as generalizing T0 πs us with
  | nil => exact ⟨T0, Uses.zero, [], πs, us, .nil, h, (Uses.zero_add πs).symm, _root_.rfl⟩
  | cons a as ih =>
    simp only [List.cons_append] at h
    cases h with
    | cons hc ha hr =>
      obtain ⟨Tm, πa, ua, πb, ub, h1, h2, hπ, hu⟩ := ih hr
      subst hπ hu
      exact ⟨Tm, _, _, πb, ub, .cons hc ha h1, h2, (Uses.add_assoc _ _ _).symm, _root_.rfl⟩

-- inversion of a whole application spine (a Lam head may be a beta redex:
-- excluded)
theorem Check.apps_inv (hΦ : Pol.Pre Φ) {sp : List Term} :
    ∀ (as : List Term) (f : Term), (∀ g, f ≠ .Lam g) →
    Check β Φ L sp q Γ (Term.apps f as) T π u →
    ∃ T0 π0 u0 T1 πs us, Check β Φ L (as ++ sp) q Γ f T0 π0 u0 ∧
      Args β Φ L q Γ T0 as T1 πs us ∧ Φ.conv (Ctx.δ Γ 0 T1) (Ctx.δ Γ 0 T) ∧
      π = Uses.add π0 πs ∧ u = Term.era q (Term.apps u0 us) := by
  intro as
  induction as with
  | nil =>
    intro f _ h
    exact ⟨T, π, u, T, Uses.zero, [], h, .nil, hΦ.refl _, (Uses.add_zero π).symm,
      h.era_self.symm⟩
  | cons a as ih =>
    intro f hl h
    obtain ⟨T0, π0, u0, T1, πs, us, hfa, hargs, hle, hπ, hu⟩ :=
      ih (.App f a) (fun _ e => Term.noConfusion e) h
    rcases hfa.app_inv hΦ with ⟨q', A, B, πf, uf, πa, ua, hf, ha, hle', hπ', hu'⟩ | ⟨g, _, hg, _⟩
    · obtain ⟨T1', hargs', hle''⟩ := hargs.le_start hΦ hle'
      subst hπ hu hπ' hu'
      exact ⟨_, πf, uf, T1', _, _, hf, .cons (hΦ.refl _) ha hargs', hΦ.trans hle'' hle,
        Uses.add_assoc _ _ _, Term.era_apps_era q (.App uf ua) us⟩
    · exact absurd hg (hl g)

-- a walk rebuilds the checked spine (cnv at each App)
theorem Check.apps {sp : List Term} (h : Check β Φ L (as ++ sp) q Γ f T0 π0 u0)
    (hargs : Args β Φ L q Γ T0 as T1 πs us) :
    Check β Φ L sp q Γ (Term.apps f as) T1 (Uses.add π0 πs) (Term.era q (Term.apps u0 us)) := by
  induction hargs generalizing f π0 u0 with
  | nil => simpa only [Term.apps, List.nil_append, Uses.add_zero, h.era_self] using h
  | cons hc ha _ ih =>
    have := ih (Check.app (Check.cnv h hc) ha)
    rw [Term.era_apps_era, Uses.add_assoc] at this
    exact this

-- ============================================================================
-- METATHEORY §E3 — telescopes: substitution and retip transport the shaped
-- constructor telescopes, a walk against one lands on the family instance,
-- and the fired arm's goal walks against the scrutinee's fields.
-- ============================================================================

theorem Term.map_subst_shift (x : Term) : ∀ (ps : List Term),
    (ps.map (Term.shift 0)).map (Term.subst 0 x) = ps := by
  intro ps
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [ih, Term.subst_shift]

theorem Term.map_shift_subst (d : Nat) (w : Term) : ∀ (ps : List Term),
    (ps.map (Term.shift 0)).map (Term.subst (d + 1) (Term.shift 0 w))
      = (ps.map (Term.subst d w)).map (Term.shift 0) := by
  intro ps
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [List.map, ih, Term.shift_subst_lt p 0 d w (Nat.zero_le d)]

theorem FTele.subst : ∀ {k : Nat} {ps : List Term} {B : Term},
    FTele a r ps k B → ∀ (d : Nat) (w : Term),
    FTele a r (ps.map (Term.subst d w)) k (Term.subst d w B) := by
  intro k
  induction k with
  | zero =>
    intro ps B h d w
    simp only [FTele] at h ⊢
    subst h
    rw [Term.subst_apps]; rfl
  | succ k ih =>
    intro ps B h d w
    obtain ⟨qf, F, B0, hB, hrest⟩ := h
    subst hB
    refine ⟨qf, _, _, _root_.rfl, ?_⟩
    have h2 := ih hrest (d + 1) (Term.shift 0 w)
    rwa [Term.map_shift_subst] at h2

theorem WTele.subst : ∀ {pn : Nat} {ps : List Term} {B : Term},
    WTele a r ps pn fn B → ∀ (d : Nat) (w : Term),
    WTele a r (ps.map (Term.subst d w)) pn fn (Term.subst d w B) := by
  intro pn
  induction pn with
  | zero => intro ps B h d w; exact FTele.subst h d w
  | succ pn ih =>
    intro ps B h d w
    obtain ⟨q, K, B0, hB, hrest⟩ := h
    subst hB
    refine ⟨q, _, _, _root_.rfl, ?_⟩
    have h2 := ih hrest (d + 1) (Term.shift 0 w)
    rwa [List.map_append, Term.map_shift_subst, show [Term.Var 0].map (Term.subst (d + 1) (Term.shift 0 w))
      = [Term.Var 0] by simp [Term.subst]] at h2

-- one parameter step and one field step: binding the next binder to x
theorem WTele.param (h : WTele a r ps (pn + 1) fn T) :
    ∃ q K B, T = .All q K B ∧ WTele a r (ps.map (Term.shift 0) ++ [.Var 0]) pn fn B ∧
      WTele a r (ps ++ [x]) pn fn (Term.subst 0 x B) := by
  obtain ⟨q, K, B, hT, hrest⟩ := h
  refine ⟨q, K, B, hT, hrest, ?_⟩
  have h2 := WTele.subst hrest 0 x
  rwa [List.map_append, Term.map_subst_shift, show [Term.Var 0].map (Term.subst 0 x) = [x]
    by simp [Term.subst]] at h2

theorem FTele.field (h : FTele a r ps (k + 1) T) :
    ∃ qf F B, T = .All qf F B ∧ FTele a r (ps.map (Term.shift 0)) k B ∧
      FTele a r ps k (Term.subst 0 x B) := by
  obtain ⟨qf, F, B, hT, hrest⟩ := h
  refine ⟨qf, F, B, hT, hrest, ?_⟩
  have h2 := FTele.subst hrest 0 x
  rwa [Term.map_subst_shift] at h2

-- retip re-tips a shaped telescope (its first pn binders now erased)
theorem Term.retip_adt_apps (a : Nat) (r r' : List Nat) (ps : List Term) :
    Term.retip r' 0 0 (Term.apps (.Adt a r) ps) = Term.apps (.Adt a r') ps := by
  simp only [Term.retip, Term.spine_apps (h := .Adt a r) trivial]

theorem FTele.retip (r' : List Nat) : ∀ {k : Nat} {ps : List Term} {T : Term},
    FTele a r ps k T → FTele a r' ps k (Term.retip r' 0 k T) := by
  intro k
  induction k with
  | zero =>
    intro ps T h
    simp only [FTele] at h ⊢
    subst h
    exact Term.retip_adt_apps a r r' ps
  | succ k ih =>
    intro ps T h
    obtain ⟨qf, F, B, hT, hrest⟩ := h
    subst hT
    exact ⟨qf, F, _, _root_.rfl, ih hrest⟩

theorem WTele.retip (r' : List Nat) : ∀ {pn : Nat} {ps : List Term} {T : Term},
    WTele a r ps pn fn T → WTele a r' ps pn fn (Term.retip r' pn (pn + fn) T) := by
  intro pn
  induction pn with
  | zero => intro ps T h; rw [Nat.zero_add]; exact FTele.retip r' h
  | succ pn ih =>
    intro ps T h
    obtain ⟨q, K, B, hT, hrest⟩ := h
    subst hT
    rw [show pn + 1 + fn = pn + fn + 1 by omega]
    exact ⟨.None, K, _, _root_.rfl, ih hrest⟩

theorem FTele.retip_subst : ∀ {k : Nat} {ps : List Term} {B : Term},
    FTele a r ps k B → ∀ (r' : List Nat) (d : Nat) (w : Term),
    Term.subst d w (Term.retip r' 0 k B) = Term.retip r' 0 k (Term.subst d w B) := by
  intro k
  induction k with
  | zero =>
    intro ps B h r' d w
    simp only [FTele] at h
    subst h
    rw [Term.retip_adt_apps, Term.subst_apps, Term.subst_apps]
    exact (Term.retip_adt_apps a r r' _).symm
  | succ k ih =>
    intro ps B h r' d w
    obtain ⟨qf, F, B0, hB, hrest⟩ := h
    subst hB
    show Term.All qf (Term.subst d w F) (Term.subst (d + 1) (Term.shift 0 w) (Term.retip r' 0 k B0))
      = Term.All qf (Term.subst d w F) (Term.retip r' 0 k (Term.subst (d + 1) (Term.shift 0 w) B0))
    rw [ih hrest]

theorem WTele.retip_subst : ∀ {pn : Nat} {ps : List Term} {B : Term},
    WTele a r ps pn fn B → ∀ (r' : List Nat) (d : Nat) (w : Term),
    Term.subst d w (Term.retip r' pn (pn + fn) B)
      = Term.retip r' pn (pn + fn) (Term.subst d w B) := by
  intro pn
  induction pn with
  | zero => intro ps B h r' d w; rw [Nat.zero_add]; exact FTele.retip_subst h r' d w
  | succ pn ih =>
    intro ps B h r' d w
    obtain ⟨q, K, B0, hB, hrest⟩ := h
    subst hB
    rw [show pn + 1 + fn = pn + fn + 1 by omega]
    show Term.All .None (Term.subst d w K) (Term.subst (d + 1) (Term.shift 0 w) (Term.retip r' pn (pn + fn) B0))
      = Term.All .None (Term.subst d w K) (Term.retip r' pn (pn + fn) (Term.subst (d + 1) (Term.shift 0 w) B0))
    rw [ih hrest]

-- instantiating convertible telescopes at pointwise convertible arguments
theorem Insts.conv (hβ : Book.Closed β) :
    ∀ {ps : List Term} {T X : Term}, Insts T ps X →
    ∀ {T' Y : Term} {qs : List Term}, Insts T' qs Y →
    Conv β T T' → Convs β ps qs → Conv β X Y := by
  intro ps
  induction ps with
  | nil => intro T X h T' Y qs h' hc hcs; cases h; cases hcs; cases h'; exact hc
  | cons p ps ih =>
    intro T X h T' Y qs h' hc hcs
    cases h with
    | cons hrest =>
      cases hcs with
      | cons hpq hrest2 =>
        cases h' with
        | cons hrest' =>
          obtain ⟨_, hA, hB⟩ := hc.all_inv
          exact ih hrest hrest' (Conv.subst hβ hB hpq 0) hrest2

-- one step of a walk against a syntactic All: the argument checks at the
-- All's domain, and the rest walks the substituted codomains, still fitted
theorem Args.step (hβ : Book.Closed β)
    (hle : Le β (Ctx.δ Γ 0 (.All qw K Bw)) (Ctx.δ Γ 0 T0))
    (h : Args β (Pol.std β) L q Γ T0 (x :: as) T1 πs us) :
    ∃ πx ux πs' us' B1, πs = Uses.add πx πs' ∧ us = ux :: us' ∧
      Check β (Pol.std β) L [] (Quant.dem qw q) Γ x K πx ux ∧
      Le β (Ctx.δ Γ 0 (Term.subst 0 x Bw)) (Ctx.δ Γ 0 (Term.subst 0 x B1)) ∧
      Args β (Pol.std β) L q Γ (Term.subst 0 x B1) as T1 πs' us' := by
  cases h with
  | cons hc hx hr =>
    rename_i q1 A1 B1 πx ux πs' us'
    have ra : Red β .strong (Ctx.δ Γ 0 (.All qw K Bw)) (.All qw (Ctx.δ Γ 0 K) (Ctx.δ Γ 1 Bw)) := by
      rw [Ctx.δ_all]; exact .refl
    have rb : Red β .strong (Ctx.δ Γ 0 (.All q1 A1 B1)) (.All q1 (Ctx.δ Γ 0 A1) (Ctx.δ Γ 1 B1)) := by
      rw [Ctx.δ_all]; exact .refl
    obtain ⟨rfl, hA, hB⟩ := Le.all_inv hβ (Le.trans hβ hle hc) ra rb
    refine ⟨_, _, _, _, _, _root_.rfl, _root_.rfl, Check.cnv hx hA, ?_, hr⟩
    rw [Ctx.δ_subst Γ 0 0 _ _ (Nat.le_refl 0), Ctx.δ_subst Γ 0 0 _ _ (Nat.le_refl 0)]
    exact Le.subst hβ hB 0 _

-- the constructor walk: too few arguments leaves a function type, exactly
-- enough lands on the family instance, too many is impossible
theorem Args.wtele (hβ : Book.Closed β) :
    ∀ {as : List Term} {pn fn : Nat} {ps : List Term} {Tw T0 T1 : Term} {πs : Uses} {us : List Term},
    WTele a r ps pn fn Tw → Args β (Pol.std β) L q Γ T0 as T1 πs us →
    Le β (Ctx.δ Γ 0 Tw) (Ctx.δ Γ 0 T0) →
    (as.length < pn + fn ∧ ∃ qA A B, Le β (Ctx.δ Γ 0 (.All qA A B)) (Ctx.δ Γ 0 T1)) ∨
    (as.length = pn + fn ∧
      Le β (Ctx.δ Γ 0 (Term.apps (.Adt a r) (ps ++ as.take pn))) (Ctx.δ Γ 0 T1)) := by
  intro as
  induction as with
  | nil =>
    intro pn fn ps Tw T0 T1 πs us hw h hle
    cases h
    cases pn with
    | zero =>
      cases fn with
      | zero => simp only [WTele, FTele] at hw; subst hw; right; simpa using hle
      | succ fk => obtain ⟨qf, F, B, hT, _⟩ := hw; subst hT; left; exact ⟨by simp, _, _, _, hle⟩
    | succ pk => obtain ⟨q0, K, B, hT, _⟩ := hw; subst hT; left; exact ⟨by show 0 < pk + 1 + fn; omega, _, _, _, hle⟩
  | cons x as ih =>
    intro pn fn ps Tw T0 T1 πs us hw h hle
    cases pn with
    | succ pk =>
      obtain ⟨qw, K, Bw, hT, _, hw'⟩ := WTele.param (x := x) hw
      subst hT
      obtain ⟨πx, ux, πs', us', B1, _, _, _, hB, hr⟩ := Args.step hβ hle h
      rcases ih hw' hr hB with ⟨hlt, hex⟩ | ⟨hlen, hcv⟩
      · left; exact ⟨by simp; omega, hex⟩
      · right; refine ⟨by simp at hlen ⊢; omega, ?_⟩
        simpa [List.take, List.append_assoc] using hcv
    | zero =>
      cases fn with
      | zero =>
        exfalso
        simp only [WTele, FTele] at hw
        subst hw
        cases h with
        | cons hc _ _ =>
          have := Le.trans hβ hle hc
          rw [Ctx.δ_apps, Ctx.δ_closed Γ 0 (.Adt a r) (by trivial), Ctx.δ_all] at this
          exact this.adt_all
      | succ fk =>
        obtain ⟨qf, F, Bw, hT, _, hw'⟩ := FTele.field (x := x) hw
        subst hT
        obtain ⟨πx, ux, πs', us', B1, _, _, _, hB, hr⟩ := Args.step hβ hle h
        rcases ih (pn := 0) hw' hr hB with ⟨hlt, hex⟩ | ⟨hlen, hcv⟩
        · left; exact ⟨by simp at hlt ⊢; omega, hex⟩
        · right; exact ⟨by simp at hlen ⊢; omega, by simpa using hcv⟩

-- the parameter prefix of a walk against a re-tipped constructor telescope
-- instantiates the telescope, leaving the field telescope shaped and fitted
theorem Args.params (hβ : Book.Closed β) :
    ∀ {qs : List Term} {pn : Nat} {ps0 : List Term} {Tw T0 Tm : Term} {πp : Uses} {up : List Term},
    WTele a r ps0 pn fn Tw → Args β (Pol.std β) L q Γ T0 qs Tm πp up →
    Le β (Ctx.δ Γ 0 (Term.retip r' pn (pn + fn) Tw)) (Ctx.δ Γ 0 T0) → qs.length = pn →
    ∃ TS, Insts Tw qs TS ∧ FTele a r (ps0 ++ qs) fn TS ∧
      Le β (Ctx.δ Γ 0 (Term.retip r' 0 fn TS)) (Ctx.δ Γ 0 Tm) := by
  intro qs
  induction qs with
  | nil =>
    intro pn ps0 Tw T0 Tm πp up hw h hle hlen
    cases h
    cases pn with
    | zero => rw [Nat.zero_add] at hle; exact ⟨Tw, .nil, by rw [List.append_nil]; exact hw, hle⟩
    | succ pk => simp at hlen
  | cons x qs ih =>
    intro pn ps0 Tw T0 Tm πp up hw h hle hlen
    cases pn with
    | zero => simp at hlen
    | succ pk =>
      obtain ⟨qw, K, Bw, hT, hwB, hw'⟩ := WTele.param (x := x) hw
      subst hT
      rw [show pk + 1 + fn = pk + fn + 1 by omega] at hle
      obtain ⟨πx, ux, πs', us', B1, _, _, _, hB, hr⟩ :=
        Args.step hβ (qw := .None) (K := K) (Bw := Term.retip r' pk (pk + fn) Bw) hle h
      rw [WTele.retip_subst hwB r' 0 x] at hB
      obtain ⟨TS, hI, hF, hle'⟩ := ih hw' hr hB (by simp at hlen; omega)
      exact ⟨TS, .cons hI, by simpa [List.append_assoc] using hF, hle'⟩

-- the field walk restarts exactly on the shaped field telescope, whatever
-- re-tipping it was walked through, and lands on the family instance; the
-- walked re-tipped instance fits the walk's end
theorem Args.ftele (hβ : Book.Closed β) :
    ∀ {xs : List Term} {fn : Nat} {ps : List Term} {TS T0 T1 : Term} {πs : Uses} {us : List Term},
    FTele a r ps fn TS → Args β (Pol.std β) L q Γ T0 xs T1 πs us →
    Le β (Ctx.δ Γ 0 (Term.retip r' 0 fn TS)) (Ctx.δ Γ 0 T0) → xs.length = fn →
    Args β (Pol.std β) L q Γ TS xs (Term.apps (.Adt a r) ps) πs us ∧
      Le β (Ctx.δ Γ 0 (Term.apps (.Adt a r') ps)) (Ctx.δ Γ 0 T1) := by
  intro xs
  induction xs with
  | nil =>
    intro fn ps TS T0 T1 πs us hF h hle hlen
    cases h
    cases fn with
    | zero =>
      simp only [FTele] at hF; subst hF
      rw [Term.retip_adt_apps] at hle
      exact ⟨.nil, hle⟩
    | succ fk => simp at hlen
  | cons x xs ih =>
    intro fn ps TS T0 T1 πs us hF h hle hlen
    cases fn with
    | zero => simp at hlen
    | succ fk =>
      obtain ⟨qf, F, Bs, hT, hFB, hF'⟩ := FTele.field (x := x) hF
      subst hT
      obtain ⟨πx, ux, πs', us', B1, rfl, rfl, hx, hB, hr⟩ :=
        Args.step hβ (qw := qf) (K := F) (Bw := Term.retip r' 0 fk Bs) hle h
      rw [FTele.retip_subst hFB r' 0 x] at hB
      obtain ⟨hw, hle'⟩ := ih hF' hr hB (by simp at hlen; omega)
      exact ⟨.cons (Le.refl _) hx hw, hle'⟩

theorem Quant.dem_mul (h : q ≠ .None → q' ≠ .None) :
    Quant.dem (Quant.mul qf q') q = Quant.dem qf (Quant.dem q' q) := by
  cases q <;> cases q' <;> cases qf <;> simp_all [Quant.dem, Quant.mul, Quant.add]

-- the fired arm walks its goal against the scrutinee's field checks: the
-- goal's field telescope fits the walked one, the demands reassociate, and
-- the tip lands on the motive at the rebuilt constructor
theorem MatGoal.apply (hβ : Book.Closed β) :
    ∀ (n : Nat) {B s tel G : Term}, MatGoal q' n B s tel G → (q ≠ .None → q' ≠ .None) →
    ∀ {TS xs T1 πs us}, Args β (Pol.std β) L (Quant.dem q' q) Γ TS xs T1 πs us →
    Le β (Ctx.δ Γ 0 tel) (Ctx.δ Γ 0 TS) → xs.length = n →
    Args β (Pol.std β) L q Γ G xs (Term.subst 0 (Term.apps s xs) B) πs us := by
  intro n
  induction n with
  | zero =>
    intro B s tel G hg hq TS xs T1 πs us h hle hlen
    cases hg
    cases xs with
    | nil => cases h; exact .nil
    | cons => simp at hlen
  | succ n ih =>
    intro B s tel G hg hq TS xs T1 πs us h hle hlen
    cases hg with
    | succ hrest =>
      rename_i Bf G0 qf F
      cases xs with
      | nil => simp at hlen
      | cons x xs =>
        obtain ⟨πx, ux, πs', us', B1, rfl, rfl, hx, hB, hr⟩ := Args.step hβ hle h
        have hsub := hrest.subst 0 x
        rw [Term.subst_shift B 1 _] at hsub
        have es : Term.subst 0 x (.App (Term.shift 0 s) (.Var 0)) = .App s x := by
          show Term.App _ _ = _
          rw [Term.subst_shift s 0 x]; simp [Term.subst]
        rw [es] at hsub
        have hx' : Check β (Pol.std β) L [] (Quant.dem (Quant.mul qf q') q) Γ x F πx ux := by
          rw [Quant.dem_mul hq]; exact hx
        exact .cons (Le.refl _) hx' (ih hsub hq hr hB (by simp at hlen; omega))

-- the signature walk: a family head applied to fewer parameters than its
-- arity has a function type, to exactly its arity a kind
theorem STele.subst (hβ : Book.Closed β) : ∀ {n : Nat} {T G : Term}, STele β n T G →
    ∀ (d : Nat) (w : Term),
    STele β n (Term.subst d w T) (Term.subst (d + n) (Term.shiftN n w) G) := by
  intro n
  induction n with
  | zero => intro T G h d w; exact Red.subst hβ h d w
  | succ n ih =>
    intro T G h d w
    obtain ⟨q, K, B, hT, hr⟩ := h
    subst hT
    refine ⟨q, _, _, _root_.rfl, ?_⟩
    rw [show d + (n + 1) = d + 1 + n by omega, ← Term.shiftN_shift0]
    exact ih hr (d + 1) (Term.shift 0 w)

theorem Args.stele (hβ : Book.Closed β) :
    ∀ {as : List Term} {n : Nat} {Tw G T0 T1 : Term} {πs : Uses} {us : List Term},
    STele β n Tw G → Args β (Pol.std β) L q Γ T0 as T1 πs us →
    Le β (Ctx.δ Γ 0 Tw) (Ctx.δ Γ 0 T0) →
    (as.length < n ∧ ∃ qA A B, Le β (Ctx.δ Γ 0 (.All qA A B)) (Ctx.δ Γ 0 T1)) ∨
    (as.length = n ∧ ∃ G', Le β (Ctx.δ Γ 0 (.Typ G')) (Ctx.δ Γ 0 T1)) := by
  intro as
  induction as with
  | nil =>
    intro n Tw G T0 T1 πs us hs h hle
    cases h
    cases n with
    | zero => right; exact ⟨_root_.rfl, G, Le.red_l hβ (Ctx.δ_red hβ Γ 0 hs).strong hle⟩
    | succ n => obtain ⟨q0, K, B, hT, _⟩ := hs; subst hT; left; exact ⟨by simp, _, _, _, hle⟩
  | cons x as ih =>
    intro n Tw G T0 T1 πs us hs h hle
    cases n with
    | zero =>
      exfalso
      cases h with
      | cons hc _ _ =>
        have := Le.red_l hβ (Ctx.δ_red hβ Γ 0 hs).strong (Le.trans hβ hle hc)
        rw [Ctx.δ_typ, Ctx.δ_all] at this
        exact this.typ_all
    | succ n =>
      obtain ⟨q0, K, Bw, hT, hs'⟩ := hs
      subst hT
      obtain ⟨πx, ux, πs', us', B1, _, _, _, hB, hr⟩ := Args.step hβ hle h
      rcases ih (hs'.subst hβ 0 x) hr hB with ⟨hlt, hex⟩ | ⟨hlen, hcv⟩
      · left; exact ⟨by simp at hlt ⊢; omega, hex⟩
      · right; exact ⟨by simp at hlen ⊢; omega, hcv⟩


-- ============================================================================
-- METATHEORY §G — canonical forms and progress (claim 3). A closed live
-- value is classified by its head. A typed head (VT) carries the type its
-- rule gives it, fitted below the value's type; a stuck spine (VS) sits at
-- any type and keeps the live sub-derivation that holds it stuck. In a
-- filled book a stuck spine hides, down its stuck positions, a closed live
-- term of an emptied family (Bad): what claim (5) refutes, so the exact
-- forms are stated under ¬ Bad. Every closed live term is a value or
-- weak-steps.
-- ============================================================================

theorem Book.Ok.defn (hok : Book.Ok β) (hk : Book.defn β k = some d) :
    (∃ π, Check β (Pol.std β) ⟨k, .Ref k, 0, [], false⟩ [] .None [] d.ty (.Typ (.Qua .Lone)) π .Qnt) ∧
    TeleQs β d.ty d.n d.qs ∧ (d.body = none → d.b = true) ∧
    (∀ b, d.body = some b → Tree β d.n b ∧
      ∃ π u, Check β (Pol.std β) ⟨k, .Ref k, d.n, d.qs, false⟩ [] .Lone [] b d.ty π u) :=
  hok k _ (Book.defn_tld hk)

theorem Book.Ok.adt (hok : Book.Ok β) (hk : Book.adt β a = some A) :
    (∃ π, Check β (Pol.std β) ⟨a, .Ref a, 0, [], false⟩ [] .None [] A.sig (.Typ (.Qua .Lone)) π .Qnt) ∧
    ∃ G, STele β A.pn A.sig G ∧
    ∀ c C, AdtD.ctr A c = some C → CtrD.Shape a A.pn C ∧ CtrOk β a A.pn G [] 0 C.ty :=
  hok a _ (Book.adt_tld hk)

theorem AdtD.ctr_lt {A : AdtD} (h : AdtD.ctr A c = some C) : c < A.ctrs.length := by
  unfold AdtD.ctr at h
  generalize A.ctrs = cs at h ⊢
  induction cs generalizing c with
  | nil => cases h
  | cons C0 cs ih =>
    cases c with
    | zero => exact Nat.succ_pos _
    | succ c => exact Nat.succ_lt_succ (ih h)

-- the closed context is never dead
theorem CtxDead.nil : ¬ CtxDead β [] := by
  rintro ⟨i, b, _, _, _, hg, -⟩
  simp [Ctx.get] at hg

theorem Term.era_live (hq : q ≠ .None) (t : Term) : Term.era q t = t := by
  cases q <;> first | exact absurd _root_.rfl hq | rfl

theorem Quant.dem_live (hq' : q' ≠ .None) : Quant.dem q' q = q := by
  cases q' <;> first | exact absurd _root_.rfl hq' | rfl

theorem Ctx.δ_nil (d : Nat) (t : Term) : Ctx.δ [] d t = t := rfl

theorem Pol.std_conv (a b : Term) : (Pol.std β).conv a b = Le β a b := rfl

theorem Term.size_le_apps (h : Term) : ∀ (as : List Term), Term.size h ≤ Term.size (Term.apps h as) := by
  intro as
  induction as generalizing h with
  | nil => exact Nat.le_refl _
  | cons a as ih => exact Nat.le_trans (by simp only [Term.size]; omega) (ih (.App h a))

theorem Term.size_rwt (e P f : Term) (as : List Term) :
    Term.size e < Term.size (Term.apps (.Rwt e P f) as) :=
  Nat.lt_of_lt_of_le (by simp only [Term.size]; omega) (Term.size_le_apps _ as)

theorem Term.size_matS (a c : Nat) (h m x : Term) (as : List Term) :
    Term.size x < Term.size (Term.apps (.Mat a c h m) (x :: as)) :=
  Term.size_spine_arg _ x (by rw [Term.spine_apps (h := .Mat a c h m) (by trivial)]; simp)

theorem TeleQs.subst (hβ : Book.Closed β) : ∀ {T : Term} {n : Nat} {qs : List Quant},
    TeleQs β T n qs → ∀ (d : Nat) (w : Term), TeleQs β (Term.subst d w T) n qs := by
  intro T n qs h
  induction h with
  | nil => intros; exact .nil
  | cons hr _ ih => intro d w; exact .cons (hr.subst hβ d w) (ih (d + 1) (Term.shift 0 w))

-- the definition walk: fewer arguments than the columns leaves a function type
theorem Args.teleqs (hβ : Book.Closed β) :
    ∀ {as : List Term} {n : Nat} {Tw T0 T1 : Term} {qs : List Quant} {πs : Uses} {us : List Term},
    TeleQs β Tw n qs → Args β (Pol.std β) L q [] T0 as T1 πs us → Le β Tw T0 → as.length < n →
    ∃ qA A B, Le β (.All qA A B) T1 := by
  intro as
  induction as with
  | nil =>
    intro n Tw T0 T1 qs πs us hs h hle hlt
    cases h
    cases hs with
    | nil => simp at hlt
    | cons hr _ => exact ⟨_, _, _, Le.red_l hβ hr.strong hle⟩
  | cons x as ih =>
    intro n Tw T0 T1 qs πs us hs h hle hlt
    cases hs with
    | nil => simp at hlt
    | cons hr hs' =>
      obtain ⟨_, _, _, _, _, -, -, -, hB, hr'⟩ :=
        Args.step (Γ := []) hβ (Le.red_l hβ hr.strong hle) h
      exact ih (hs'.subst hβ 0 x) hr' hB (by simp at hlt; omega)

-- a walk from a stable non-function type takes no argument
theorem Args.nil_of (hβ : Book.Closed β) (h : Args β (Pol.std β) L q [] T0 as T1 πs us)
    (hle : Le β X T0) (hX : 6 ≤ X.tag) (hX' : X.tag ≠ 10) : as = [] ∧ T1 = T0 ∧ us = [] := by
  cases h with
  | nil => exact ⟨_root_.rfl, _root_.rfl, _root_.rfl⟩
  | cons hc _ _ =>
    simp only [Ctx.δ_nil, Pol.std_conv] at hc
    have := (Le.trans hβ hle hc).tag hX (by simp [Term.tag])
    simp [Term.tag] at this
    exact (hX' this).elim

-- the typed heads of a closed live value: its shape and the type its head
-- rule gives it, fitted below the value's type
inductive Check.VT (β : Book) : Term → Term → Prop
  | typ  : Le β (.Typ (.Qua .Lone)) T → Check.VT β (.Typ g) T
  | qnt  : Le β (.Typ (.Qua .Lone)) T → Check.VT β .Qnt T
  | all  : Le β (.Typ (.Qua .Lone)) T → Check.VT β (.All q A B) T
  | eql  : Le β (.Typ (.Qua .Many)) T → Check.VT β (.Eql a b T') T
  | adtT : Book.adt β a = some A → as.length = A.pn → Le β (.Typ G) T →
           Check.VT β (Term.apps (.Adt a r) as) T
  | qua  : Le β .Qnt T → Check.VT β (.Qua q) T
  | lam  : Le β (.All q A B) T → Check.VT β (.Lam f) T
  | mat  : q ≠ .None → Le β (.All q (Term.apps (.Adt a r) ps) B) T → Check.VT β (.Mat a c h m) T
  | efq  : Le β (.All q A B) T → Check.VT β .Efq T
  | adtF : Book.adt β a = some A → as.length < A.pn → Le β (.All q A' B) T →
           Check.VT β (Term.apps (.Adt a r) as) T
  | ctrF : Book.adt β a = some A → AdtD.ctr A c = some C → as.length < A.pn + C.fn →
           Le β (.All q A' B) T → Check.VT β (Term.apps (.Ctr a c) as) T
  | ref  : Book.defn β k = some d → d.body = some b → as.length < d.n → Le β (.All q A B) T →
           Check.VT β (Term.apps (.Ref k) as) T
  | ctr  : Book.adt β a = some A → AdtD.ctr A c = some C → c ∉ r → as.length = A.pn + C.fn →
           Le β (Term.apps (.Adt a r) (as.take A.pn)) T → Check.VT β (Term.apps (.Ctr a c) as) T
  | rfl  : Le β (.Eql a b T') T → Check.VT β .Rfl T

-- the stuck spines of a closed live value, at any type: a bodiless
-- definition, a stuck meet, a rewrite on stuck evidence, a match on a
-- stuck scrutinee, an empty match applied; each keeps the live
-- sub-derivation that holds it stuck, and its erasure
inductive Check.VS (β : Book) (q : Quant) : Term → Term → Prop
  | nat  : Book.defn β k = some d → d.body = none → Check.VS β q (Term.apps (.Ref k) as) u
  | min  : Term.Value β a → a ≠ .Qua .Many → a ≠ .Qua .None →
           Term.Value β b → b ≠ .Qua .Many → b ≠ .Qua .None →
           ¬ (a = .Qua .Lone ∧ b = .Qua .Lone) →
           Check β (Pol.std β) (LHS.void β) [] q [] a .Qnt πa ua →
           Check β (Pol.std β) (LHS.void β) [] q [] b .Qnt πb ub →
           Check.VS β q (.Min a b) (.Min ua ub)
  | rwt  : Term.Value β e → e ≠ .Rfl →
           Check β (Pol.std β) (LHS.void β) [] q [] e (.Eql a b T') πe ue →
           Check.VS β q (Term.apps (.Rwt e P f) as) (Term.apps (.Rwt ue .Qnt uf) us)
  | matS : Term.Value β x → (∀ a' c' xs, x ≠ Term.apps (.Ctr a' c') xs) →
           Check β (Pol.std β) (LHS.void β) [] q [] x (Term.apps (.Adt a r) ps) πx ux →
           Check.VS β q (Term.apps (.Mat a c h m) (x :: as)) (Term.apps (.Mat a c uh um) (ux :: us))
  | efqS : Book.empty β a r →
           Check β (Pol.std β) (LHS.void β) [] q [] x (Term.apps (.Adt a r) ps) πx ux →
           Check.VS β q (Term.apps .Efq (x :: as)) (Term.apps .Efq (ux :: us))

theorem Check.VS.ne_ctr (hvs : Check.VS β q v u) : ∀ a' c' xs, v ≠ Term.apps (.Ctr a' c') xs := by
  intro a' c' xs
  cases hvs with
  | min => exact fun h => Term.apps_ctr_ne (by trivial) (fun e => Term.noConfusion e) h.symm
  | nat | rwt | matS | efqS =>
    exact fun h => Term.noConfusion (Term.apps_head_inv (by trivial) (by trivial) h).1

theorem Check.VS.ne_rfl (hvs : Check.VS β q v u) : v ≠ .Rfl := by
  cases hvs with
  | min => exact fun e => Term.noConfusion e
  | nat | rwt | matS | efqS => exact Term.apps_ne (by trivial) (by trivial) (fun e => Term.noConfusion e)

-- the classification: a closed live value is a typed head or a stuck spine
theorem Check.value_inv (hok : Book.Ok β) (hq : q ≠ .None) {sp : List Term}
    (hv : Term.Value β v) (h : Check β (Pol.std β) (LHS.void β) sp q [] v T π u) :
    Check.VT β v T ∨ Check.VS β q v u := by
  have hβ := hok.closed
  have hpre := Pol.std_pre hβ
  cases hv with
  | var =>
    obtain ⟨_, _, _, _, _, _, h0, -, -, -, -⟩ := Check.apps_inv hpre _ _ (by intro _ e; cases e) h
    obtain ⟨b, hg, -⟩ := h0.var_inv hpre
    simp [Ctx.get] at hg
  | typ =>
    obtain ⟨T0, _, _, T1, _, _, h0, hargs, hle, -, -⟩ := Check.apps_inv hpre _ _ (by intro _ e; cases e) h
    obtain ⟨_, -, hc, -, -⟩ := h0.typ_inv hpre
    simp only [Ctx.δ_nil, Pol.std_conv] at hc hle
    obtain ⟨rfl, rfl, -⟩ := Args.nil_of hβ hargs hc (by simp [Term.tag]) (by simp [Term.tag])
    exact .inl (.typ (Le.trans hβ hc hle))
  | qnt =>
    obtain ⟨T0, _, _, T1, _, _, h0, hargs, hle, -, -⟩ := Check.apps_inv hpre _ _ (by intro _ e; cases e) h
    obtain ⟨hc, -, -⟩ := h0.qnt_inv hpre
    simp only [Ctx.δ_nil, Pol.std_conv] at hc hle
    obtain ⟨rfl, rfl, -⟩ := Args.nil_of hβ hargs hc (by simp [Term.tag]) (by simp [Term.tag])
    exact .inl (.qnt (Le.trans hβ hc hle))
  | qua =>
    obtain ⟨T0, _, _, T1, _, _, h0, hargs, hle, -, -⟩ := Check.apps_inv hpre _ _ (by intro _ e; cases e) h
    obtain ⟨hc, -, -⟩ := h0.qua_inv hpre
    simp only [Ctx.δ_nil, Pol.std_conv] at hc hle
    obtain ⟨rfl, rfl, -⟩ := Args.nil_of hβ hargs hc (by simp [Term.tag]) (by simp [Term.tag])
    exact .inl (.qua (Le.trans hβ hc hle))
  | all =>
    obtain ⟨T0, _, _, T1, _, _, h0, hargs, hle, -, -⟩ := Check.apps_inv hpre _ _ (by intro _ e; cases e) h
    obtain ⟨_, _, -, -, hc, -, -⟩ := h0.all_inv hpre
    simp only [Ctx.δ_nil, Pol.std_conv] at hc hle
    obtain ⟨rfl, rfl, -⟩ := Args.nil_of hβ hargs hc (by simp [Term.tag]) (by simp [Term.tag])
    exact .inl (.all (Le.trans hβ hc hle))
  | lam =>
    obtain ⟨_, _, _, _, _, _, -, -, -, hc, -, -⟩ := h.lam_inv hpre
    simp only [Ctx.δ_nil, Pol.std_conv] at hc
    exact .inl (.lam hc)
  | mat =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, -, -, -, -, hq', -, -, -, -, hc, -, -⟩ := h.mat_inv hpre
    simp only [Ctx.δ_nil, Pol.std_conv] at hc
    exact .inl (.mat (hq' hq) hc)
  | @efq as =>
    obtain ⟨T0, _, u0, T1, _, us, h0, hargs, hle, -, hu⟩ := Check.apps_inv hpre _ _ (by intro _ e; cases e) h
    obtain ⟨a, A, r, q', ps, B, -, hq', hemp, hc, -, hu0⟩ := h0.efq_inv hpre
    simp only [Ctx.δ_nil, Pol.std_conv] at hc hle
    have hemp := hemp.resolve_right CtxDead.nil
    cases as with
    | nil => cases hargs; exact .inl (.efq (Le.trans hβ hc hle))
    | cons x as =>
      obtain ⟨πx, ux, πs', us', B1, -, rfl, hx, -, -⟩ := Args.step (Γ := []) hβ hc hargs
      rw [Quant.dem_live (hq' hq)] at hx
      subst hu hu0
      simp only [Term.era_live hq]
      exact .inr (.efqS hemp hx)
  | eql =>
    obtain ⟨T0, _, _, T1, _, _, h0, hargs, hle, -, -⟩ := Check.apps_inv hpre _ _ (by intro _ e; cases e) h
    obtain ⟨_, _, _, -, -, -, hc, -, -⟩ := h0.eql_inv hpre
    simp only [Ctx.δ_nil, Pol.std_conv] at hc hle
    obtain ⟨rfl, rfl, -⟩ := Args.nil_of hβ hargs hc (by simp [Term.tag]) (by simp [Term.tag])
    exact .inl (.eql (Le.trans hβ hc hle))
  | rfl =>
    obtain ⟨T0, _, _, T1, _, _, h0, hargs, hle, -, -⟩ := Check.apps_inv hpre _ _ (by intro _ e; cases e) h
    obtain ⟨_, _, _, -, hc, -, -⟩ := h0.rfl_inv hpre
    simp only [Ctx.δ_nil, Pol.std_conv] at hc hle
    obtain ⟨rfl, rfl, -⟩ := Args.nil_of hβ hargs hc (by simp [Term.tag]) (by simp [Term.tag])
    exact .inl (.rfl (Le.trans hβ hc hle))
  | @adt a r as =>
    obtain ⟨T0, _, _, T1, _, _, h0, hargs, hle, -, -⟩ := Check.apps_inv hpre _ _ (by intro _ e; cases e) h
    obtain ⟨A, hA, hc, -, -⟩ := h0.adt_inv hpre
    simp only [Ctx.δ_nil, Pol.std_conv] at hc hle
    obtain ⟨-, G, hs, -⟩ := hok.adt hA
    rcases Args.stele (Γ := []) hβ hs hargs hc with ⟨hlt, _, _, _, hl⟩ | ⟨hlen, G', hl⟩
    · simp only [Ctx.δ_nil] at hl
      exact .inl (.adtF hA hlt (Le.trans hβ hl hle))
    · simp only [Ctx.δ_nil] at hl
      exact .inl (.adtT hA hlen (Le.trans hβ hl hle))
  | @ctr a c as =>
    obtain ⟨T0, _, _, T1, _, _, h0, hargs, hle, -, -⟩ := Check.apps_inv hpre _ _ (by intro _ e; cases e) h
    obtain ⟨A, C, r, hA, hC, hr, hc, -, -⟩ := h0.ctr_inv hpre
    simp only [Ctx.δ_nil, Pol.std_conv] at hc hle
    obtain ⟨-, _, _, hcs⟩ := hok.adt hA
    have hw := WTele.retip r (show WTele a [] [] A.pn C.fn C.ty from (hcs c C hC).1)
    rcases Args.wtele (Γ := []) hβ hw hargs hc with ⟨hlt, _, _, _, hl⟩ | ⟨hlen, hl⟩
    · simp only [Ctx.δ_nil] at hl
      exact .inl (.ctrF hA hC hlt (Le.trans hβ hl hle))
    · simp only [Ctx.δ_nil, List.nil_append] at hl
      exact .inl (.ctr hA hC hr hlen (Le.trans hβ hl hle))
  | @fam k A as hk hpn =>
    obtain ⟨_, _, _, _, _, _, h0, -, -, -, -⟩ := Check.apps_inv hpre _ _ (by intro _ e; cases e) h
    rcases h0.ref_inv hpre with ⟨d, hd, -, -, -, -, -, -⟩ | ⟨A', hA', h0', -, -, -⟩
    · exact (Book.defn_adt_clash hd hk).elim
    · rw [hk] at hA'; cases hA'; omega
  | @ref k d as hk hgate =>
    obtain ⟨T0, _, _, T1, _, _, h0, hargs, hle, -, -⟩ := Check.apps_inv hpre _ _ (by intro _ e; cases e) h
    rcases h0.ref_inv hpre with ⟨d', hd', -, -, -, hc, -, -⟩ | ⟨A', hA', -, -, -, -⟩
    · rw [hk] at hd'; cases hd'
      simp only [Ctx.δ_nil, Pol.std_conv] at hc hle
      cases hb : d.body with
      | none => exact .inr (.nat hk hb)
      | some b =>
        have hlt : as.length < d.n := hgate.resolve_right (by simp [hb])
        obtain ⟨_, _, _, hl⟩ := Args.teleqs hβ (hok.defn hk).2.1 hargs hc hlt
        exact .inl (.ref hk hb hlt (Le.trans hβ hl hle))
    · exact (Book.defn_adt_clash hk hA').elim
  | min hva hna1 hna2 hvb hnb1 hnb2 hnab =>
    obtain ⟨T0, _, u0, T1, _, us, h0, hargs, hle, -, hu⟩ := Check.apps_inv hpre _ _ (by intro _ e; cases e) h
    obtain ⟨πa, ua, πb, ub, ha, hb, hc, -, hu0⟩ := h0.min_inv hpre
    simp only [Ctx.δ_nil, Pol.std_conv] at hc
    obtain ⟨rfl, rfl, rfl⟩ := Args.nil_of hβ hargs hc (by simp [Term.tag]) (by simp [Term.tag])
    subst hu hu0
    simp only [Term.apps, Term.era_live hq]
    exact .inr (.min hva hna1 hna2 hvb hnb1 hnb2 hnab ha hb)
  | rwt hve hne =>
    obtain ⟨T0, _, u0, T1, _, us, h0, hargs, hle, -, hu⟩ := Check.apps_inv hpre _ _ (by intro _ e; cases e) h
    obtain ⟨_, _, _, _, _, _, _, _, he, -, -, -, -, hu0⟩ := h0.rwt_inv hpre
    subst hu hu0
    simp only [Term.era_live hq]
    exact .inr (.rwt hve hne he)
  | matS hvx hnx =>
    obtain ⟨T0, _, u0, T1, _, us, h0, hargs, hle, -, hu⟩ := Check.apps_inv hpre _ _ (by intro _ e; cases e) h
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, -, -, -, -, hq', -, -, -, -, hc, -, hu0⟩ := h0.mat_inv hpre
    simp only [Ctx.δ_nil, Pol.std_conv] at hc
    obtain ⟨πx, ux, πs', us', B1, -, rfl, hx, -, -⟩ := Args.step (Γ := []) hβ hc hargs
    rw [Quant.dem_live (hq' hq)] at hx
    subst hu hu0
    simp only [Term.era_live hq]
    exact .inr (.matS hvx hnx hx)

-- the function values: what a closed live value at a function type is,
-- beside a stuck spine
inductive Term.FunV (β : Book) : Term → Prop
  | lam : Term.FunV β (.Lam f)
  | mat : Term.FunV β (.Mat a c h m)
  | efq : Term.FunV β .Efq
  | adt : Book.adt β a = some A → as.length < A.pn → Term.FunV β (Term.apps (.Adt a r) as)
  | ctr : Book.adt β a = some A → AdtD.ctr A c = some C → as.length < A.pn + C.fn →
          Term.FunV β (Term.apps (.Ctr a c) as)
  | ref : Book.defn β k = some d → d.body = some b → as.length < d.n →
          Term.FunV β (Term.apps (.Ref k) as)

-- a typed head at a function, family, equation or Quant type: the heads
-- of the other classes clash
theorem Check.VT.at_all (hβ : Book.Closed β) (hvt : Check.VT β v T) (hT : Le β T (.All q' A B)) :
    Term.FunV β v := by
  cases hvt with
  | lam _ => exact .lam
  | mat _ _ => exact .mat
  | efq _ => exact .efq
  | adtF hA hlt _ => exact .adt hA hlt
  | ctrF hA hC hlt _ => exact .ctr hA hC hlt
  | ref hk hb hlt _ => exact .ref hk hb hlt
  | typ hl | qnt hl | all hl | eql hl | adtT _ _ hl | qua hl | ctr _ _ _ _ hl | rfl hl =>
    simpa [Term.tag] using (Le.trans hβ hl hT).tag

theorem Check.VT.at_adt (hβ : Book.Closed β) (hvt : Check.VT β v T)
    (hT : Le β T (Term.apps (.Adt a r) ps)) :
    ∃ c A C as, v = Term.apps (.Ctr a c) as ∧ Book.adt β a = some A ∧ AdtD.ctr A c = some C ∧
      c ∉ r ∧ as.length = A.pn + C.fn ∧ Convs β (as.take A.pn) ps := by
  cases hvt with
  | ctr hA hC hr hlen hl =>
    obtain ⟨rfl, hsub, hcv⟩ := Le.adt_inv hβ (Le.trans hβ hl hT) .refl .refl
    exact ⟨_, _, _, _, _root_.rfl, hA, hC, fun hc => hr (hsub _ hc), hlen, hcv⟩
  | typ hl | qnt hl | all hl | eql hl | adtT _ _ hl | qua hl | lam hl | mat _ hl | efq hl
  | adtF _ _ hl | ctrF _ _ _ hl | ref _ _ _ hl | rfl hl =>
    simpa [Term.tag] using (Le.trans hβ hl hT).tag

theorem Check.VT.at_eql (hβ : Book.Closed β) (hvt : Check.VT β v T) (hT : Le β T (.Eql a b T')) :
    v = .Rfl := by
  cases hvt with
  | rfl _ => exact _root_.rfl
  | typ hl | qnt hl | all hl | eql hl | adtT _ _ hl | qua hl | lam hl | mat _ hl | efq hl
  | adtF _ _ hl | ctrF _ _ _ hl | ref _ _ _ hl | ctr _ _ _ _ hl =>
    simpa [Term.tag] using (Le.trans hβ hl hT).tag

theorem Check.VT.at_qnt (hβ : Book.Closed β) (hvt : Check.VT β v T) (hT : Le β T .Qnt) :
    ∃ q', v = .Qua q' := by
  cases hvt with
  | qua _ => exact ⟨_, _root_.rfl⟩
  | typ hl | qnt hl | all hl | eql hl | adtT _ _ hl | lam hl | mat _ hl | efq hl
  | adtF _ _ hl | ctrF _ _ _ hl | ref _ _ _ hl | ctr _ _ _ _ hl | rfl hl =>
    simpa [Term.tag] using (Le.trans hβ hl hT).tag

-- the general canonical forms
theorem Check.canon_all (hok : Book.Ok β) (hq : q ≠ .None) {sp : List Term} (hv : Term.Value β v)
    (h : Check β (Pol.std β) (LHS.void β) sp q [] v T π u) (hT : Le β T (.All q' A B)) :
    Term.FunV β v ∨ Check.VS β q v u :=
  (Check.value_inv hok hq hv h).imp (fun hvt => hvt.at_all hok.closed hT) id

theorem Check.canon_adt (hok : Book.Ok β) (hq : q ≠ .None) {sp : List Term} (hv : Term.Value β v)
    (h : Check β (Pol.std β) (LHS.void β) sp q [] v T π u)
    (hT : Le β T (Term.apps (.Adt a r) ps)) :
    (∃ c A C as, v = Term.apps (.Ctr a c) as ∧ Book.adt β a = some A ∧ AdtD.ctr A c = some C ∧
      c ∉ r ∧ as.length = A.pn + C.fn ∧ Convs β (as.take A.pn) ps) ∨ Check.VS β q v u :=
  (Check.value_inv hok hq hv h).imp (fun hvt => hvt.at_adt hok.closed hT) id

theorem Check.canon_eql (hok : Book.Ok β) (hq : q ≠ .None) {sp : List Term} (hv : Term.Value β v)
    (h : Check β (Pol.std β) (LHS.void β) sp q [] v T π u) (hT : Le β T (.Eql a b T')) :
    v = .Rfl ∨ Check.VS β q v u :=
  (Check.value_inv hok hq hv h).imp (fun hvt => hvt.at_eql hok.closed hT) id

theorem Check.canon_qnt (hok : Book.Ok β) (hq : q ≠ .None) {sp : List Term} (hv : Term.Value β v)
    (h : Check β (Pol.std β) (LHS.void β) sp q [] v T π u) (hT : Le β T .Qnt) :
    (∃ q', v = .Qua q') ∨ Check.VS β q v u :=
  (Check.value_inv hok hq hv h).imp (fun hvt => hvt.at_qnt hok.closed hT) id

-- Term.Bad β q v u: the value v, erased to u, hides down its stuck positions a
-- closed live term of an emptied family (with its erasure). What holds a
-- stuck spine stuck in a filled book; claim (5) says there is none
inductive Term.Bad (β : Book) (q : Quant) : Term → Term → Prop
  | efq  : Book.empty β a r →
           Check β (Pol.std β) (LHS.void β) [] q [] x (Term.apps (.Adt a r) ps) πx ux →
           Term.Bad β q (Term.apps .Efq (x :: as)) (Term.apps .Efq (ux :: us))
  | rwt  : Term.Bad β q e ue → Term.Bad β q (Term.apps (.Rwt e P f) as) (Term.apps (.Rwt ue .Qnt uf) us)
  | matS : Term.Bad β q x ux →
           Term.Bad β q (Term.apps (.Mat a c h m) (x :: as)) (Term.apps (.Mat a c uh um) (ux :: us))
  | minL : Term.Bad β q a ua → Term.Bad β q (.Min a b) (.Min ua ub)
  | minR : Term.Bad β q b ub → Term.Bad β q (.Min a b) (.Min ua ub)

theorem Term.Bad.witness (hb : Term.Bad β q v u) :
    ∃ x a r ps πx ux, Book.empty β a r ∧
      Check β (Pol.std β) (LHS.void β) [] q [] x (Term.apps (.Adt a r) ps) πx ux ∧
      Term.size x < Term.size v ∧ Term.size ux < Term.size u := by
  induction hb with
  | efq hemp hx =>
    exact ⟨_, _, _, _, _, _, hemp, hx,
      Term.size_spine_arg _ _ (by rw [Term.spine_apps (h := .Efq) (by trivial)]; simp),
      Term.size_spine_arg _ _ (by rw [Term.spine_apps (h := .Efq) (by trivial)]; simp)⟩
  | rwt _ ih =>
    obtain ⟨x, a, r, ps, πx, ux, hemp, hx, h1, h2⟩ := ih
    exact ⟨x, a, r, ps, πx, ux, hemp, hx, Nat.lt_trans h1 (Term.size_rwt _ _ _ _),
      Nat.lt_trans h2 (Term.size_rwt _ _ _ _)⟩
  | matS _ ih =>
    obtain ⟨x, a, r, ps, πx, ux, hemp, hx, h1, h2⟩ := ih
    exact ⟨x, a, r, ps, πx, ux, hemp, hx, Nat.lt_trans h1 (Term.size_matS _ _ _ _ _ _),
      Nat.lt_trans h2 (Term.size_matS _ _ _ _ _ _)⟩
  | minL _ ih | minR _ ih =>
    obtain ⟨x, a, r, ps, πx, ux, hemp, hx, h1, h2⟩ := ih
    exact ⟨x, a, r, ps, πx, ux, hemp, hx, Nat.lt_trans h1 (by simp only [Term.size]; omega),
      Nat.lt_trans h2 (by simp only [Term.size]; omega)⟩

-- in a filled book a closed live value that hides no emptied-typed term is
-- a typed head: a stuck spine's stuck position is a smaller value of an
-- equation, family or Quant type, which its own exact form contradicts
theorem Check.value_filled (hok : Book.Ok β) (hF : Book.Filled β) (hq : q ≠ .None) {sp : List Term}
    (hv : Term.Value β v) (h : Check β (Pol.std β) (LHS.void β) sp q [] v T π u)
    (hnb : ¬ Term.Bad β q v u) : Check.VT β v T := by
  have hβ := hok.closed
  suffices H : ∀ (n : Nat) (v : Term), Term.size v ≤ n → ∀ {sp : List Term} {T : Term} {π : Uses} {u : Term},
      Term.Value β v → Check β (Pol.std β) (LHS.void β) sp q [] v T π u →
      ¬ Term.Bad β q v u → Check.VT β v T from H _ v (Nat.le_refl _) hv h hnb
  intro n
  induction n with
  | zero => intro v hn; have := Term.size_pos v; omega
  | succ n ih =>
    intro v hn sp T π u hv h hnb
    rcases Check.value_inv hok hq hv h with hvt | hvs
    · exact hvt
    cases hvs with
    | nat hk hb => exact absurd hb (hF _ _ hk)
    | min hva hna1 hna2 hvb hnb1 hnb2 hnab ha hb =>
      obtain ⟨qa, rfl⟩ := (ih _ (by simp only [Term.size] at hn; omega) hva ha
        fun hb => hnb (.minL hb)).at_qnt hβ (Le.refl _)
      obtain ⟨qb, rfl⟩ := (ih _ (by simp only [Term.size] at hn; omega) hvb hb
        fun hb => hnb (.minR hb)).at_qnt hβ (Le.refl _)
      cases qa <;> cases qb <;> simp at hna1 hna2 hnb1 hnb2 hnab
    | rwt hve hne he =>
      exact absurd ((ih _ (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (Term.size_rwt _ _ _ _) hn)) hve he
        fun hb => hnb (.rwt hb)).at_eql hβ (Le.refl _)) hne
    | matS hvx hnx hx =>
      obtain ⟨_, _, _, _, he, -⟩ :=
        (ih _ (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (Term.size_matS _ _ _ _ _ _) hn)) hvx hx
          fun hb => hnb (.matS hb)).at_adt hβ (Le.refl _)
      exact absurd he (hnx _ _ _)
    | efqS hemp hx => exact (hnb (.efq hemp hx)).elim

-- the exact canonical forms of a filled book
theorem Check.canon_all' (hok : Book.Ok β) (hF : Book.Filled β) (hq : q ≠ .None) {sp : List Term}
    (hv : Term.Value β v) (h : Check β (Pol.std β) (LHS.void β) sp q [] v T π u)
    (hnb : ¬ Term.Bad β q v u) (hT : Le β T (.All q' A B)) : Term.FunV β v :=
  (Check.value_filled hok hF hq hv h hnb).at_all hok.closed hT

theorem Check.canon_adt' (hok : Book.Ok β) (hF : Book.Filled β) (hq : q ≠ .None) {sp : List Term}
    (hv : Term.Value β v) (h : Check β (Pol.std β) (LHS.void β) sp q [] v T π u)
    (hnb : ¬ Term.Bad β q v u) (hT : Le β T (Term.apps (.Adt a r) ps)) :
    ∃ c A C as, v = Term.apps (.Ctr a c) as ∧ Book.adt β a = some A ∧ AdtD.ctr A c = some C ∧
      c ∉ r ∧ as.length = A.pn + C.fn ∧ Convs β (as.take A.pn) ps :=
  (Check.value_filled hok hF hq hv h hnb).at_adt hok.closed hT

theorem Check.canon_eql' (hok : Book.Ok β) (hF : Book.Filled β) (hq : q ≠ .None) {sp : List Term}
    (hv : Term.Value β v) (h : Check β (Pol.std β) (LHS.void β) sp q [] v T π u)
    (hnb : ¬ Term.Bad β q v u) (hT : Le β T (.Eql a b T')) : v = .Rfl :=
  (Check.value_filled hok hF hq hv h hnb).at_eql hok.closed hT

theorem Check.canon_qnt' (hok : Book.Ok β) (hF : Book.Filled β) (hq : q ≠ .None) {sp : List Term}
    (hv : Term.Value β v) (h : Check β (Pol.std β) (LHS.void β) sp q [] v T π u)
    (hnb : ¬ Term.Bad β q v u) (hT : Le β T .Qnt) : ∃ q', v = .Qua q' :=
  (Check.value_filled hok hF hq hv h hnb).at_qnt hok.closed hT

-- a closed live value of an emptied family hides an emptied-typed term:
-- the constructor case contradicts the peeled set
theorem Check.canon_empty (hok : Book.Ok β) (hF : Book.Filled β) (hq : q ≠ .None) {sp : List Term}
    (hv : Term.Value β v) (h : Check β (Pol.std β) (LHS.void β) sp q [] v T π u)
    (hT : Le β T (Term.apps (.Adt a r) ps)) (hemp : Book.empty β a r) : Term.Bad β q v u := by
  refine Classical.byContradiction fun hnb => ?_
  obtain ⟨c, A, C, as, -, hA, hC, hr, -, -⟩ :=
    (Check.value_filled hok hF hq hv h hnb).at_adt hok.closed hT
  obtain ⟨A', hA', hall⟩ := hemp
  rw [hA] at hA'
  cases hA'
  exact hr (hall c (AdtD.ctr_lt hC))

-- ============================================================================
-- progress (claim 3)
-- ============================================================================

-- a definition head: it fires at its arity with a body, else stays stuck
theorem Check.progress_ref (hk : Book.defn β k = some d) :
    Term.Value β (.Ref k) ∨ ∃ t', Step β .weak (.Ref k) t' := by
  cases hb : d.body with
  | none => exact .inl (Term.Value.ref (as := []) hk (.inr hb))
  | some b =>
    by_cases hn : d.n = 0
    · exact .inr ⟨_, Step.dref (s := .Ref k) hk hb _root_.rfl (by rw [hn]; exact _root_.rfl)⟩
    · exact .inl (Term.Value.ref (as := []) hk (.inl (by simp only [List.length_nil]; omega)))

theorem Check.step_ref (hk : Book.defn β k = some d) (hgate : as.length < d.n ∨ d.body = none)
    (x : Term) :
    Term.Value β (.App (Term.apps (.Ref k) as) x) ∨
    ∃ t', Step β .weak (.App (Term.apps (.Ref k) as) x) t' := by
  rw [← Term.apps_snoc]
  cases hb : d.body with
  | none => exact .inl (Term.Value.ref hk (.inr hb))
  | some b =>
    have hlt : as.length < d.n := hgate.resolve_right (by simp [hb])
    by_cases hn : as.length + 1 = d.n
    · exact .inr ⟨_, Step.dref hk hb (by rw [Term.spine_apps (h := .Ref k) (by trivial)])
        (by rw [Term.spine_apps (h := .Ref k) (by trivial)]; simpa using hn)⟩
    · exact .inl (Term.Value.ref hk (.inl (by simp only [List.length_append, List.length_singleton]; omega)))

-- a meet of two values: a literal side fires a min rule, else it is stuck
theorem Check.step_min (hva : Term.Value β a) (hvb : Term.Value β b) :
    Term.Value β (.Min a b) ∨ ∃ t', Step β .weak (.Min a b) t' := by
  by_cases h1 : a = .Qua .Many
  · subst h1; exact .inr ⟨_, .minLM⟩
  by_cases h2 : a = .Qua .None
  · subst h2; exact .inr ⟨_, .minLN⟩
  by_cases h3 : b = .Qua .Many
  · subst h3; exact .inr ⟨_, .minRM⟩
  by_cases h4 : b = .Qua .None
  · subst h4; exact .inr ⟨_, .minRN⟩
  by_cases h5 : a = .Qua .Lone ∧ b = .Qua .Lone
  · obtain ⟨rfl, rfl⟩ := h5; exact .inr ⟨_, .minLL⟩
  · exact .inl (Term.Value.min (as := []) hva h1 h2 hvb h3 h4 h5)

-- a match applied to a value of its family: a constructor fires the arm or
-- the tail, a stuck scrutinee keeps the match stuck
theorem Check.step_mat (hok : Book.Ok β) (hq : q ≠ .None) (hvx : Term.Value β x)
    (hx : Check β (Pol.std β) (LHS.void β) [] q [] x (Term.apps (.Adt a r) ps) πx ux) :
    Term.Value β (.App (.Mat a c hh mm) x) ∨ ∃ t', Step β .weak (.App (.Mat a c hh mm) x) t' := by
  rcases Check.value_inv hok hq hvx hx with hvt | hvs
  · obtain ⟨c', A, C, as, rfl, hA, hC, -, hlen, -⟩ := hvt.at_adt hok.closed (Le.refl _)
    by_cases hcc : c' = c
    · subst hcc
      rw [← List.take_append_drop A.pn as]
      exact .inr ⟨_, Step.matc hA hC (by simp [List.length_take]; omega)
        (by simp [List.length_drop]; omega)⟩
    · exact .inr ⟨_, Step.matm (by intro e; cases e; exact hcc _root_.rfl)⟩
  · exact .inl (Term.Value.matS (as := []) hvx hvs.ne_ctr)

theorem progress_holds : progress := by
  intro β q t T π u hok hq h
  have hβ := hok.closed
  generalize hΓ : ([] : Ctx) = Γ0 at h
  generalize hL : LHS.void β = L0 at h
  generalize ([] : List Term) = sp0 at h
  induction h with
  | var hg => subst hΓ; simp [Ctx.get] at hg
  | ref hk _ _ _ => exact Check.progress_ref hk
  | refA hk h0 => exact .inr ⟨_, .aref hk h0⟩
  | adt _ => exact .inl (Term.Value.adt (as := []))
  | ctr _ _ _ => exact .inl (Term.Value.ctr (as := []))
  | typ _ _ => exact .inl (Term.Value.typ (as := []))
  | qnt => exact .inl (Term.Value.qnt (as := []))
  | qua => exact .inl (Term.Value.qua (as := []))
  | min _ _ iha ihb =>
    rcases iha hq hΓ hL with hva | ⟨a', hs⟩
    · rcases ihb hq hΓ hL with hvb | ⟨b', hs⟩
      · exact Check.step_min hva hvb
      · exact .inr ⟨_, .min_b hs⟩
    · exact .inr ⟨_, .min_a hs⟩
  | all _ _ _ _ => exact .inl (Term.Value.all (as := []))
  | lam _ _ _ _ _ => exact .inl .lam
  | app hf hx ihf ihx =>
    subst hΓ hL
    rcases ihf hq _root_.rfl _root_.rfl with hvf | ⟨f', hs⟩
    · rcases Check.value_inv hok hq hvf hf with hvt | hvs
      · cases hvt with
        | lam _ => exact .inr ⟨_, .beta⟩
        | mat hq' hl =>
          obtain ⟨rfl, hA, -⟩ := Le.all_inv hβ hl .refl .refl
          rw [Quant.dem_live hq'] at hx ihx
          rcases ihx hq _root_.rfl _root_.rfl with hvx | ⟨x', hs⟩
          · exact Check.step_mat hok hq hvx (Check.cnv hx hA)
          · exact .inr ⟨_, .app_a hs⟩
        | efq _ => exact .inl (Term.Value.efq (as := [_]))
        | adtF _ _ _ => rw [← Term.apps_snoc]; exact .inl .adt
        | ctrF _ _ _ _ => rw [← Term.apps_snoc]; exact .inl .ctr
        | ref hk _ hlt _ => exact Check.step_ref hk (.inl hlt) _
        | typ hl | qnt hl | all hl | eql hl | adtT _ _ hl | qua hl | ctr _ _ _ _ hl | rfl hl =>
          simpa [Term.tag] using hl.tag
      · cases hvs with
        | nat hk hb => exact Check.step_ref hk (.inr hb) _
        | min hva hna1 hna2 hvb hnb1 hnb2 hnab _ _ =>
          exact .inl (Term.Value.min (as := [_]) hva hna1 hna2 hvb hnb1 hnb2 hnab)
        | rwt hve hne _ => rw [← Term.apps_snoc]; exact .inl (Term.Value.rwt hve hne)
        | matS hvx hnx _ => rw [← Term.apps_snoc, List.cons_append]; exact .inl (Term.Value.matS hvx hnx)
        | efqS _ _ => rw [← Term.apps_snoc]; exact .inl .efq
    · exact .inr ⟨_, .app_f hs⟩
  | appLam _ _ _ => exact .inr ⟨_, .beta⟩
  | let_ _ _ _ _ _ _ _ => exact .inr ⟨_, .let_⟩
  | eql _ _ _ _ _ _ => exact .inl (Term.Value.eql (as := []))
  | rfl _ => exact .inl (Term.Value.rfl (as := []))
  | rwt he _ _ ihe _ _ =>
    subst hΓ hL
    rcases ihe hq _root_.rfl _root_.rfl with hve | ⟨e', hs⟩
    · rcases Check.value_inv hok hq hve he with hvt | hvs
      · obtain rfl := hvt.at_eql hβ (Le.refl _)
        exact .inr ⟨_, .rwt⟩
      · exact .inl (Term.Value.rwt (as := []) hve hvs.ne_rfl)
    · exact .inr ⟨_, .rwt_e hs⟩
  | mat _ _ _ _ _ _ _ _ _ _ _ => exact .inl .mat
  | efq _ _ _ => exact .inl (Term.Value.efq (as := []))
  | cnv _ _ ih => exact ih hq hΓ hL


-- ============================================================================
-- METATHEORY §F — subject reduction (claim 2) with the erasure simulation:
-- a weak step of a closed live term at a live position of its erasure
-- keeps its type, and the erasure takes the erased image of the step (or
-- stays, when the fired beta was typed by appLam). The book of erasures
-- Book.Era carries each definition's erased body for the dref case.
-- ============================================================================

@[simp] theorem Term.era_lone (u : Term) : Term.era .Lone u = u := rfl

theorem Convs.symm (h : Convs β xs ys) : Convs β ys xs := by
  induction h with
  | nil => exact .nil
  | cons h _ ih => exact .cons h.symm ih

theorem Convs.append (h1 : Convs β xs ys) (h2 : Convs β xs' ys') :
    Convs β (xs ++ xs') (ys ++ ys') := by
  induction h1 with
  | nil => exact h2
  | cons h _ ih => exact .cons h ih

-- ----------------------------------------------------------------------------
-- Book.Era β w k bs bs': bs' is bs (the suffix of β from position k) with
-- every filled body replaced by one of its erasures under its own equation
-- (wall flag w); adts and bodiless defs are kept
-- ----------------------------------------------------------------------------

inductive Book.Era (β : Book) (w : Bool) : Nat → Book → Book → Prop
  | nil  : Book.Era β w k [] []
  | keepA : Book.Era β w (k + 1) bs bs' → Book.Era β w k (.adt A :: bs) (.adt A :: bs')
  | keepD : d.body = none → Book.Era β w (k + 1) bs bs' →
            Book.Era β w k (.defn d :: bs) (.defn d :: bs')
  | era  : d.body = some b →
           Check β (Pol.std β) ⟨k, .Ref k, d.n, d.qs, w⟩ [] .Lone [] b d.ty π ub →
           Book.Era β w (k + 1) bs bs' →
           Book.Era β w k (.defn d :: bs) (.defn { d with body := some ub } :: bs')

theorem Book.Era.tld_adt (h : Book.Era β w k bs bs') :
    ∀ j A, Book.tld bs j = some (.adt A) → Book.tld bs' j = some (.adt A) := by
  induction h with
  | nil => intro j A h; cases j <;> cases h
  | keepA _ ih => intro j A h; cases j with | zero => exact h | succ j => exact ih j A h
  | keepD _ _ ih => intro j A h; cases j with | zero => cases h | succ j => exact ih j A h
  | era _ _ _ ih => intro j A h; cases j with | zero => cases h | succ j => exact ih j A h

theorem Book.Era.tld_defn (h : Book.Era β w k bs bs') :
    ∀ j d b, Book.tld bs j = some (.defn d) → d.body = some b →
    ∃ ub π, Book.tld bs' j = some (.defn { d with body := some ub }) ∧
      Check β (Pol.std β) ⟨k + j, .Ref (k + j), d.n, d.qs, w⟩ [] .Lone [] b d.ty π ub := by
  induction h with
  | nil => intro j d b h; cases j <;> cases h
  | keepA _ ih =>
    intro j d b h hb
    cases j with
    | zero => cases h
    | succ j => simpa [Book.tld, Nat.add_assoc, Nat.add_comm 1 j] using ih j d b h hb
  | keepD hn _ ih =>
    intro j d b h hb
    cases j with
    | zero => cases h; rw [hn] at hb; cases hb
    | succ j => simpa [Book.tld, Nat.add_assoc, Nat.add_comm 1 j] using ih j d b h hb
  | era hs hc _ ih =>
    intro j d b h hb
    cases j with
    | zero => cases h; rw [hs] at hb; cases hb; exact ⟨_, _, rfl, hc⟩
    | succ j => simpa [Book.tld, Nat.add_assoc, Nat.add_comm 1 j] using ih j d b h hb

theorem Book.Era.adt (h : Book.Era β w 0 β βe) (hA : Book.adt β a = some A) :
    Book.adt βe a = some A :=
  Book.tld_adt (h.tld_adt a A (Book.adt_tld hA))

theorem Book.Era.defn (h : Book.Era β w 0 β βe) (hd : Book.defn β k = some d)
    (hb : d.body = some b) :
    ∃ ub π, Book.defn βe k = some { d with body := some ub } ∧
      Check β (Pol.std β) ⟨k, .Ref k, d.n, d.qs, w⟩ [] .Lone [] b d.ty π ub := by
  obtain ⟨ub, π, h1, h2⟩ := h.tld_defn k d b (Book.defn_tld hd) hb
  exact ⟨ub, π, Book.tld_defn h1, by simpa using h2⟩

theorem Book.Era.exists (hb : ∀ k d b, Book.defn β k = some d → d.body = some b →
    ∃ π u, Check β (Pol.std β) ⟨k, .Ref k, d.n, d.qs, w⟩ [] .Lone [] b d.ty π u) :
    ∃ βe, Book.Era β w 0 β βe := by
  suffices H : ∀ (bs : Book) (k : Nat), (∀ j t, Book.tld bs j = some t → Book.tld β (k + j) = some t) →
      ∃ bs', Book.Era β w k bs bs' from H β 0 (fun j t h => by simpa using h)
  intro bs
  induction bs with
  | nil => intro k _; exact ⟨[], .nil⟩
  | cons t bs ih =>
    intro k hk
    obtain ⟨bs', hbs'⟩ := ih (k + 1)
      (fun j t h => by rw [show k + 1 + j = k + (j + 1) by omega]; exact hk (j + 1) t h)
    cases t with
    | adt A => exact ⟨_, .keepA hbs'⟩
    | defn d =>
      cases hd : d.body with
      | none => exact ⟨_, .keepD hd hbs'⟩
      | some b =>
        obtain ⟨π, u, hc⟩ := hb k d b (Book.tld_defn (by simpa using hk 0 _ rfl)) hd
        exact ⟨_, .era hd hc hbs'⟩

theorem Book.Ok.era (hok : Book.Ok β) : ∃ βe, Book.Era β false 0 β βe :=
  Book.Era.exists fun k _ b hd hb => ((hok k _ (Book.defn_tld hd)).2.2.2 b hb).2

theorem Book.Wall.era (hW : Book.Wall β) : ∃ βe, Book.Era β true 0 β βe :=
  Book.Era.exists hW

-- ----------------------------------------------------------------------------
-- LStep β V t u t': a weak step of t at a position that is live in its
-- erasure u (a dead subterm is the token, and no rule enters a token), whose
-- fired beta or let, when the erasure shows the argument (the app-typed
-- redex: appLam types no argument), takes one satisfying V with its erasure
-- ----------------------------------------------------------------------------

inductive LStep (β : Book) (V : Term → Term → Prop) : Term → Term → Term → Prop
  | beta  : (∀ uf ua, u = .App (.Lam uf) ua → V a ua) →
            LStep β V (.App (.Lam f) a) u (Term.subst 0 a f)
  | let_  : (∀ uv ub, u = .Let q uv ub → V v uv) →
            LStep β V (.Let q v b) u (Term.subst 0 v b)
  | dref  : Book.defn β k = some d → d.body = some b →
            (Term.spine s).1 = .Ref k → (Term.spine s).2.length = d.n →
            LStep β V s u (Term.apps b (Term.spine s).2)
  | aref  : Book.adt β k = some A → A.pn = 0 → LStep β V (.Ref k) u (.Adt k [])
  | matc  : Book.adt β a = some A → AdtD.ctr A c = some C →
            ps.length = A.pn → xs.length = C.fn →
            LStep β V (.App (.Mat a c h m) (Term.apps (.Ctr a c) (ps ++ xs))) u (Term.apps h xs)
  | matm  : (a', c') ≠ (a, c) →
            LStep β V (.App (.Mat a c h m) (Term.apps (.Ctr a' c') as)) u
                      (.App m (Term.apps (.Ctr a' c') as))
  | rwt   : LStep β V (.Rwt .Rfl P f) u f
  | minLM : LStep β V (.Min (.Qua .Many) b) u b
  | minLN : LStep β V (.Min (.Qua .None) b) u (.Qua .None)
  | minRM : LStep β V (.Min a (.Qua .Many)) u a
  | minRN : LStep β V (.Min a (.Qua .None)) u (.Qua .None)
  | minLL : LStep β V (.Min (.Qua .Lone) (.Qua .Lone)) u (.Qua .Lone)
  | min_a : LStep β V a ua a' → LStep β V (.Min a b) (.Min ua ub) (.Min a' b)
  | min_b : LStep β V b ub b' → LStep β V (.Min a b) (.Min ua ub) (.Min a b')
  | app_f : LStep β V f uf f' → LStep β V (.App f x) (.App uf ux) (.App f' x)
  | app_a : (∀ g, f ≠ .Lam g) → ux ≠ .Qnt → LStep β V x ux x' →
            LStep β V (.App f x) (.App uf ux) (.App f x')
  | mat_h : LStep β V h uh h' → LStep β V (.Mat a c h m) (.Mat a c uh um) (.Mat a c h' m)
  | mat_m : LStep β V m um m' → LStep β V (.Mat a c h m) (.Mat a c uh um) (.Mat a c h m')
  | rwt_e : LStep β V e ue e' → LStep β V (.Rwt e P f) (.Rwt ue uP uf) (.Rwt e' P f)
  | rwt_f : LStep β V f uf f' → LStep β V (.Rwt e P f) (.Rwt ue uP uf) (.Rwt e P f')

theorem LStep.step (h : LStep β V t u t') : Step β .weak t t' := by
  induction h with
  | beta _ => exact .beta
  | let_ _ => exact .let_
  | dref hk hb hsp hn => exact .dref hk hb hsp hn
  | aref hk h0 => exact .aref hk h0
  | matc hA hC hp hx => exact .matc hA hC hp hx
  | matm hne => exact .matm hne
  | rwt => exact .rwt
  | minLM => exact .minLM
  | minLN => exact .minLN
  | minRM => exact .minRM
  | minRN => exact .minRN
  | minLL => exact .minLL
  | min_a _ ih => exact .min_a ih
  | min_b _ ih => exact .min_b ih
  | app_f _ ih => exact .app_f ih
  | app_a _ _ _ ih => exact .app_a ih
  | mat_h _ ih => exact .mat_h ih
  | mat_m _ ih => exact .mat_m ih
  | rwt_e _ ih => exact .rwt_e ih
  | rwt_f _ ih => exact .rwt_f ih

theorem LStep.lam (h : LStep β V (.Lam g) u t') : False := by
  cases h with
  | dref _ _ hsp _ => simp [Term.spine] at hsp

-- ----------------------------------------------------------------------------
-- the root steps, at the void equation, in the empty context, at demand
-- Lone. Each takes the redex's derivation and gives the reduct's, with the
-- erasure pinned to the erased image of the rule
-- ----------------------------------------------------------------------------

-- a closed live argument, erased to ua, entering a binder of an emptied
-- type: what the caller refutes (G's canonical forms on a value with ¬Bad,
-- N3's deep_empty on a deep erasure, normalization in general)
abbrev Check.Dead (β : Book) (a ua : Term) : Prop :=
  ∀ {A πa}, Check β (Pol.std β) (LHS.void β) [] .Lone [] a A πa ua →
    ∀ e r ps, Conv β A (Term.apps (.Adt e r) ps) → Book.empty β e r → False

theorem Quant.le_none_eq (h : Quant.le q .None) : q = .None := by
  cases q <;> simp_all [Quant.le]

theorem Check.beta (hβ : Book.Closed β)
    (h : Check β (Pol.std β) (LHS.void β) [] .Lone [] (.App (.Lam f) a) T π u)
    (hd : ∀ uf ua, u = .App (.Lam uf) ua → Check.Dead β a ua) :
    ∃ π' u', Check β (Pol.std β) (LHS.void β) [] .Lone [] (Term.subst 0 a f) T π' u' ∧
      (u' = u ∨ ∃ uf ua, u = .App (.Lam uf) ua ∧ u' = Term.subst 0 ua uf) := by
  have hΦ := Pol.std_pre hβ
  rcases h.app_inv hΦ with ⟨q', A, B, πf, uf, πa, ua, hf, ha, hle, hπ, hu⟩ | ⟨g, T0, hg, _, hb, hle⟩
  · obtain ⟨q1, A1, B1, πA, π1, uf1, hA, hb, hle1, hleF, hπf, huf⟩ := hf.lam_inv hΦ
    obtain ⟨rfl, hAA, hBB⟩ := Le.all_inv hβ hleF .refl .refl
    have hA1 : Term.Closed 0 A1 := hA.closed
    have hres : Check β (Pol.std β) (LHS.void β) [] .Lone [] (Term.subst 0 a f)
        (Term.subst 0 a B1) (Uses.del 0 π1) (Term.subst 0 ua uf1) := by
      by_cases hq : q1 = .None
      · subst hq
        exact Check.subst_std hβ (Γ := []) (b0 := ⟨.None, A1, none⟩) hb (by decide) ha.closed
          ha.closed_era (.inl _root_.rfl) (ha.dead.cnv hAA)
          (fun hne => absurd (Quant.le_none_eq hle1) hne) (fun h => absurd _root_.rfl h)
      · rw [Quant.dem_live hq] at ha
        exact Check.subst_std hβ (Γ := []) (b0 := ⟨q1, A1, none⟩) hb (by decide) ha.closed
          ha.closed_era (.inl _root_.rfl) (ha.dead.cnv hAA) (fun _ => ⟨πa, ha.cnv hAA⟩)
          (fun _ m e r ps hred hemp => hd uf1 ua (by subst hu huf; rfl) (ha.cnv hAA) e r ps
            (by rwa [Term.shiftN_closed hA1] at hred) hemp)
    subst hu huf
    exact ⟨_, _, hres.cnv (Le.trans hβ (Le.subst hβ hBB 0 a) hle), .inr ⟨uf1, ua, _root_.rfl, _root_.rfl⟩⟩
  · cases hg; exact ⟨π, u, .cnv hb hle, .inl _root_.rfl⟩

theorem Check.let_step (hβ : Book.Closed β)
    (h : Check β (Pol.std β) (LHS.void β) [] .Lone [] (.Let qb v b) T π u)
    (hd : ∀ uv ub, u = .Let qb uv ub → Check.Dead β v uv) :
    ∃ π' uv ub, Check β (Pol.std β) (LHS.void β) [] .Lone [] (Term.subst 0 v b) T π'
      (Term.subst 0 uv ub) ∧ u = .Let qb uv ub := by
  have hΦ := Pol.std_pre hβ
  obtain ⟨A, T0, πv, uv, πA, π1, ub, hv, hA, hb, hle1, hle, hπ, hu⟩ := h.let_inv hΦ
  have hA0 : Term.Closed 0 A := hA.closed
  have hres : Check β (Pol.std β) (LHS.void β) [] .Lone [] (Term.subst 0 v b)
      (Term.subst 0 v (Term.shift 0 T0)) (Uses.del 0 π1) (Term.subst 0 uv ub) := by
    by_cases hq : qb = .None
    · subst hq
      exact Check.subst_std hβ (Γ := []) (b0 := ⟨.None, A, some v⟩) hb (by decide) hv.closed
        hv.closed_era (.inr _root_.rfl) hv.dead
        (fun hne => absurd (Quant.le_none_eq hle1) hne) (fun h => absurd _root_.rfl h)
    · rw [Quant.dem_live hq] at hv
      exact Check.subst_std hβ (Γ := []) (b0 := ⟨qb, A, some v⟩) hb (by decide) hv.closed
        hv.closed_era (.inr _root_.rfl) hv.dead (fun _ => ⟨πv, hv⟩)
        (fun _ m e r ps hred hemp => hd uv ub (by subst hu; rfl) hv e r ps
          (by rwa [Term.shiftN_closed hA0] at hred) hemp)
  rw [Term.subst_shift] at hres
  subst hu
  exact ⟨_, uv, ub, hres.cnv hle, _root_.rfl⟩

theorem Check.dref_step (hβ : Book.Closed β) (hE : Book.Era β w 0 β βe)
    (hk : Book.defn β k = some d) (hb : d.body = some b)
    (h : Check β (Pol.std β) (LHS.void β) [] .Lone [] (Term.apps (.Ref k) as) T π u) :
    ∃ π' ub us, Check β (Pol.std β) (LHS.void β) [] .Lone [] (Term.apps b as) T π' (Term.apps ub us) ∧
      u = Term.apps (.Ref k) us ∧ us.length = as.length ∧
      Book.defn βe k = some { d with body := some ub } := by
  have hΦ := Pol.std_pre hβ
  obtain ⟨T0, π0, u0, T1, πs, us, hhead, hargs, hle, hπ, hu⟩ :=
    h.apps_inv hΦ as (.Ref k) (fun _ e => Term.noConfusion e)
  rcases hhead.ref_inv hΦ with ⟨d', hk', _, _, _, hle0, hπ0, hu0⟩ | ⟨A, hA, _⟩
  · rw [hk] at hk'; cases hk'
    obtain ⟨ub, πb, hkE, hc⟩ := hE.defn hk hb
    have hres := Check.apps ((hc.void_sp (as ++ [])).cnv hle0) hargs
    subst hu hu0
    exact ⟨_, ub, us, hres.cnv hle, _root_.rfl, hargs.length, hkE⟩
  · exact (Book.defn_adt_clash hk hA).elim

theorem Check.aref_step (hβ : Book.Closed β) (hA : Book.adt β k = some A)
    (h : Check β (Pol.std β) (LHS.void β) [] .Lone [] (.Ref k) T π u) :
    Check β (Pol.std β) (LHS.void β) [] .Lone [] (.Adt k []) T Uses.zero (.Adt k []) ∧
      u = .Ref k := by
  rcases h.ref_inv (Pol.std_pre hβ) with ⟨d, hd, _⟩ | ⟨A', hA', _, hle, _, hu⟩
  · exact (Book.defn_adt_clash hd hA).elim
  · rw [hA] at hA'; cases hA'; subst hu; exact ⟨(Check.adt hA).cnv hle, _root_.rfl⟩

theorem Check.rwt_step (hβ : Book.Closed β)
    (h : Check β (Pol.std β) (LHS.void β) [] .Lone [] (.Rwt .Rfl P f) T π u) :
    ∃ π' uf, Check β (Pol.std β) (LHS.void β) [] .Lone [] f T π' uf ∧ u = .Rwt .Rfl .Qnt uf := by
  have hΦ := Pol.std_pre hβ
  obtain ⟨a, b, T0, πe, ue, πP, πf, uf, he, _, hf, hle, _, hu⟩ := h.rwt_inv hΦ
  obtain ⟨a1, b1, T1, hab, hleE, _, hue⟩ := he.rfl_inv hΦ
  obtain ⟨hca, hcb, _⟩ := Le.eql_inv hβ hleE .refl .refl
  have hab' : Conv β a b := (hca.symm.trans hβ hab).trans hβ hcb
  subst hu hue
  exact ⟨πf, uf, hf.cnv (Le.trans hβ (.conv (Conv.app (Conv.app (Conv.refl P) hab') (Conv.refl _))) hle),
    _root_.rfl⟩

-- the constructor walk rebuilt along the shaped telescope with any re-tipping:
-- the same arguments, the same measures and erasures, tipped at the family
-- with that residual (matm re-checks a mismatched scrutinee at the peeled tail)
theorem Args.rebuild (hβ : Book.Closed β) :
    ∀ {as : List Term} {pn fn : Nat} {ps : List Term} {Tw T0 T1 : Term} {πs : Uses} {us : List Term},
    WTele a r ps pn fn Tw → Args β (Pol.std β) L q Γ T0 as T1 πs us →
    Le β (Ctx.δ Γ 0 (Term.retip r1 pn (pn + fn) Tw)) (Ctx.δ Γ 0 T0) → as.length = pn + fn →
    ∀ r2, Args β (Pol.std β) L q Γ (Term.retip r2 pn (pn + fn) Tw) as
      (Term.apps (.Adt a r2) (ps ++ as.take pn)) πs us := by
  intro as
  induction as with
  | nil =>
    intro pn fn ps Tw T0 T1 πs us hw h hle hlen r2
    cases h
    cases pn with
    | zero =>
      cases fn with
      | zero =>
        simp only [WTele, FTele] at hw; subst hw
        rw [Term.retip_adt_apps]; simpa using Args.nil
      | succ fk => rw [List.length_nil] at hlen; omega
    | succ pk => rw [List.length_nil] at hlen; omega
  | cons x as ih =>
    intro pn fn ps Tw T0 T1 πs us hw h hle hlen r2
    cases pn with
    | succ pk =>
      obtain ⟨qw, K, Bw, hT, hwB, hw'⟩ := WTele.param (x := x) hw
      subst hT
      rw [show pk + 1 + fn = pk + fn + 1 by omega] at hle ⊢
      obtain ⟨πx, ux, πs', us', B1, rfl, rfl, hx, hB, hr⟩ :=
        Args.step hβ (qw := .None) (K := K) (Bw := Term.retip r1 pk (pk + fn) Bw) hle h
      rw [WTele.retip_subst hwB r1 0 x] at hB
      have := ih hw' hr hB (by simp at hlen; omega) r2
      show Args β (Pol.std β) L q Γ (.All .None K (Term.retip r2 pk (pk + fn) Bw)) (x :: as) _ _ _
      refine .cons (Le.refl _) hx ?_
      rw [WTele.retip_subst hwB r2 0 x]
      simpa [List.take, List.append_assoc] using this
    | zero =>
      cases fn with
      | zero => rw [List.length_cons] at hlen; omega
      | succ fk =>
        obtain ⟨qf, F, Bw, hT, hFB, hw'⟩ := FTele.field (x := x) hw
        subst hT
        rw [Nat.zero_add] at hle ⊢
        obtain ⟨πx, ux, πs', us', B1, rfl, rfl, hx, hB, hr⟩ :=
          Args.step hβ (qw := qf) (K := F) (Bw := Term.retip r1 0 fk Bw) hle h
        rw [FTele.retip_subst hFB r1 0 x] at hB
        have := ih (pn := 0) hw' hr (by simpa using hB) (by simp at hlen; omega) r2
        rw [Nat.zero_add] at this
        show Args β (Pol.std β) L q Γ (.All qf F (Term.retip r2 0 fk Bw)) (x :: as) _ _ _
        refine .cons (Le.refl _) hx ?_
        rw [FTele.retip_subst hFB r2 0 x]
        simpa using this

theorem Book.Ok.shape (hok : Book.Ok β) (hA : Book.adt β a = some A) (hC : AdtD.ctr A c = some C) :
    CtrD.Shape a A.pn C := by
  obtain ⟨_, _, _, hctrs⟩ := hok a _ (Book.adt_tld hA)
  exact (hctrs c C hC).1

theorem Check.matc_step (hok : Book.Ok β)
    (hA : Book.adt β a = some A) (hC : AdtD.ctr A c = some C)
    (hps : ps.length = A.pn) (hxs : xs.length = C.fn)
    (h : Check β (Pol.std β) (LHS.void β) [] .Lone []
      (.App (.Mat a c hh mm) (Term.apps (.Ctr a c) (ps ++ xs))) T π u) :
    ∃ π' uh um up ux, Check β (Pol.std β) (LHS.void β) [] .Lone [] (Term.apps hh xs) T π'
        (Term.apps uh ux) ∧
      u = .App (.Mat a c uh um) (Term.apps (.Ctr a c) (up ++ ux)) ∧
      up.length = A.pn ∧ ux.length = C.fn := by
  have hβ := hok.closed
  have hΦ := Pol.std_pre hβ
  rcases h.app_inv hΦ with ⟨q1, A1, B1, πf, uf, πx, ux, hf, hx, hle, hπ, hu⟩ | ⟨g, _, hg, _⟩
  · obtain ⟨A', C', r, ps', q', telF, B, G, πh, uh, πm, um, hA', hC', hr, hlen, hlive, hI, hg,
      hh0, hm0, hleM, hπf, huf⟩ := hf.mat_inv hΦ
    rw [hA] at hA'; cases hA'; rw [hC] at hC'; cases hC'
    obtain ⟨rfl, hA1, hB1⟩ := Le.all_inv hβ hleM .refl .refl
    obtain ⟨T0, π0, u0, T1, πs, us, hhead, hargs, hleT1, hπx, hux⟩ :=
      hx.apps_inv hΦ (ps ++ xs) (.Ctr a c) (fun _ e => Term.noConfusion e)
    obtain ⟨A'', C'', r0, hA'', hC'', hr0, hleR, hπ0, hu0⟩ := hhead.ctr_inv hΦ
    rw [hA] at hA''; cases hA''; rw [hC] at hC''; cases hC''
    obtain ⟨Tm, πp, up, πq, uq, hargsP, hargsF, hπs, hus⟩ := hargs.split
    obtain ⟨TS0, hI0, hF0, hleTS⟩ := Args.params hβ (r' := r0) (hok.shape hA hC) hargsP hleR hps
    obtain ⟨hargsF', htip⟩ := Args.ftele hβ hF0 hargsF hleTS hxs
    obtain ⟨_, _, hconvs⟩ := Le.adt_inv hβ (Le.trans hβ htip (Le.trans hβ hleT1 hA1)) .refl .refl
    simp only [List.nil_append] at hconvs hargsF'
    have hconvT : Conv β telF TS0 := (Insts.conv hβ hI0 hI (Conv.refl _) hconvs).symm
    have hG := MatGoal.apply hβ C.fn hg hlive hargsF' (Le.conv hconvT) hxs
    have hres := Check.apps (hh0.void_sp (xs ++ [])) hG
    refine ⟨_, uh, um, up, uq, hres.cnv (Le.trans hβ ?_ hle), ?_, ?_, ?_⟩
    · rw [← Term.apps_append]
      exact Le.substR hβ hB1 (Conv.apps (Conv.refl _) (Convs.append hconvs.symm (Convs.refl xs))) 0
    · rw [Quant.dem_live (hlive (by decide))] at hux hu0
      subst hu huf hux hu0 hus; rfl
    · rw [hargsP.length, hps]
    · rw [hargsF.length, hxs]
  · exact Term.noConfusion hg

theorem Check.matm_step (hok : Book.Ok β) (hne : (a', c') ≠ (a, c))
    (h : Check β (Pol.std β) (LHS.void β) [] .Lone []
      (.App (.Mat a c hh mm) (Term.apps (.Ctr a' c') as)) T π u) :
    ∃ π' uh um us, Check β (Pol.std β) (LHS.void β) [] .Lone []
        (.App mm (Term.apps (.Ctr a' c') as)) T π' (.App um (Term.apps (.Ctr a' c') us)) ∧
      u = .App (.Mat a c uh um) (Term.apps (.Ctr a' c') us) := by
  have hβ := hok.closed
  have hΦ := Pol.std_pre hβ
  rcases h.app_inv hΦ with ⟨q1, A1, B1, πf, uf, πx, ux, hf, hx, hle, hπ, hu⟩ | ⟨g, _, hg, _⟩
  · obtain ⟨A0, C0, r, ps, q', telF, B, G, πh, uh, πm, um, hA0, hC0, hr, hlen, hlive, hI, hg,
      hh0, hm0, hleM, hπf, huf⟩ := hf.mat_inv hΦ
    obtain ⟨rfl, hA1, hB1⟩ := Le.all_inv hβ hleM .refl .refl
    have hq' := Quant.dem_live (q := .Lone) (hlive (by decide))
    rw [hq'] at hx
    obtain ⟨T0, π0, u0, T1, πs, us, hhead, hargs, hleT1, hπx, hux⟩ :=
      hx.apps_inv hΦ as (.Ctr a' c') (fun _ e => Term.noConfusion e)
    obtain ⟨A2, C2, r0, hA2, hC2, hr0, hleR, hπ0, hu0⟩ := hhead.ctr_inv hΦ
    have hshape := hok.shape hA2 hC2
    rcases Args.wtele hβ (WTele.retip r0 hshape) hargs hleR with ⟨_, qA, X, Y, hall⟩ | ⟨hlenAs, hadt⟩
    · exact absurd (Le.trans hβ hall (Le.trans hβ hleT1 hA1)) Le.all_adt
    · obtain ⟨rfl, hsub, hconvs⟩ :=
        Le.adt_inv hβ (Le.trans hβ hadt (Le.trans hβ hleT1 hA1)) .refl .refl
      simp only [List.nil_append] at hconvs
      have hcc : c' ≠ c := fun e => hne (by rw [e])
      have hargs' := Args.rebuild hβ hshape hargs hleR hlenAs (c :: r0)
      simp only [List.nil_append] at hargs'
      have hhead' := Check.ctr (β := β) (Φ := Pol.std β) (L := LHS.void β) (sp := as ++ [])
        (q := .Lone) (Γ := []) (r := c :: r0) hA2 hC2 (fun hm => by
          rcases List.mem_cons.mp hm with e | e
          · exact hcc e
          · exact hr0 e)
      have hscr := (Check.apps hhead' hargs').cnv
        (Le.adt (r := c :: r0) (r' := c :: r) (ps := as.take A2.pn) (ps' := ps)
          (fun x hx => by
            rcases List.mem_cons.mp hx with e | e
            · exact e ▸ List.mem_cons_self
            · exact List.mem_cons_of_mem _ (hsub x e))
          hconvs.length hconvs.get)
      rw [← hq'] at hscr
      have hres := Check.app (hm0.void_sp [_]) hscr
      rw [hq'] at hres
      refine ⟨_, uh, um, us, hres.cnv (Le.trans hβ (Le.subst hβ hB1 0 _) hle), ?_⟩
      subst hu huf hux hu0; rfl
  · exact Term.noConfusion hg

theorem Step.dref_apps (hk : Book.defn β k = some d) (hb : d.body = some b) (hn : as.length = d.n) :
    Step β p (Term.apps (.Ref k) as) (Term.apps b as) := by
  have := Step.dref (β := β) (p := p) (s := Term.apps (.Ref k) as) hk hb
    (by rw [Term.spine_apps (by trivial)]) (by rw [Term.spine_apps (by trivial)]; simpa using hn)
  rwa [Term.spine_apps (by trivial)] at this

-- ----------------------------------------------------------------------------
-- subject reduction with the erasure simulation: a live-position weak step
-- of a closed live term keeps its type, and the erasure takes the erased
-- image of the step in the book of erasures, or stays when the fired beta
-- was typed by appLam
-- ----------------------------------------------------------------------------

theorem Check.step (hok : Book.Ok β) (hE : Book.Era β w 0 β βe)
    (hV : ∀ {a ua A πa}, V a ua → Check β (Pol.std β) (LHS.void β) [] .Lone [] a A πa ua →
      ∀ e r ps, Conv β A (Term.apps (.Adt e r) ps) → Book.empty β e r → False)
    (hs : LStep β V t u t') :
    ∀ {T π}, Check β (Pol.std β) (LHS.void β) [] .Lone [] t T π u →
    ∃ π' u', Check β (Pol.std β) (LHS.void β) [] .Lone [] t' T π' u' ∧
      (Step βe .weak u u' ∨ u' = u) := by
  have hβ := hok.closed
  have hΦ := Pol.std_pre hβ
  induction hs with
  | beta hv =>
    intro T π h
    obtain ⟨π', u', h', hu⟩ := Check.beta hβ h (fun uf ua e => hV (hv uf ua e))
    rcases hu with rfl | ⟨uf, ua, rfl, rfl⟩
    · exact ⟨π', _, h', .inr _root_.rfl⟩
    · exact ⟨π', _, h', .inl .beta⟩
  | let_ hv =>
    intro T π h
    obtain ⟨π', uv, ub, h', rfl⟩ := Check.let_step hβ h (fun uv ub e => hV (hv uv ub e))
    exact ⟨_, _, h', .inl .let_⟩
  | @dref k d b s _ hk hb hsp hn =>
    intro T π h
    have hs : s = Term.apps (.Ref k) (Term.spine s).2 := by
      have := Term.apps_spine s; rw [hsp] at this; exact this.symm
    rw [hs] at h
    obtain ⟨π', ub, us, h', rfl, hlen, hkE⟩ := Check.dref_step hβ hE hk hb h
    exact ⟨_, _, h', .inl (Step.dref_apps hkE _root_.rfl (hlen.trans hn))⟩
  | aref hk h0 =>
    intro T π h
    obtain ⟨h', rfl⟩ := Check.aref_step hβ hk h
    exact ⟨_, _, h', .inl (.aref (hE.adt hk) h0)⟩
  | matc hA hC hps hxs =>
    intro T π h
    obtain ⟨π', uh, um, up, ux, h', rfl, hup, hux⟩ := Check.matc_step hok hA hC hps hxs h
    exact ⟨_, _, h', .inl (.matc (hE.adt hA) hC hup hux)⟩
  | matm hne =>
    intro T π h
    obtain ⟨π', uh, um, us, h', rfl⟩ := Check.matm_step hok hne h
    exact ⟨_, _, h', .inl (.matm hne)⟩
  | rwt =>
    intro T π h
    obtain ⟨π', uf, h', rfl⟩ := Check.rwt_step hβ h
    exact ⟨_, _, h', .inl .rwt⟩
  | minLM =>
    intro T π h
    obtain ⟨πa, ua, πb, ub, ha, hb, hle, -, hu⟩ := h.min_inv hΦ
    obtain ⟨-, -, hua⟩ := ha.qua_inv hΦ
    subst hu hua
    exact ⟨_, _, hb.cnv hle, .inl .minLM⟩
  | minLN =>
    intro T π h
    obtain ⟨πa, ua, πb, ub, ha, hb, hle, -, hu⟩ := h.min_inv hΦ
    obtain ⟨-, -, hua⟩ := ha.qua_inv hΦ
    subst hu hua
    exact ⟨_, _, Check.qua.cnv hle, .inl .minLN⟩
  | minRM =>
    intro T π h
    obtain ⟨πa, ua, πb, ub, ha, hb, hle, -, hu⟩ := h.min_inv hΦ
    obtain ⟨-, -, hub⟩ := hb.qua_inv hΦ
    subst hu hub
    exact ⟨_, _, ha.cnv hle, .inl .minRM⟩
  | minRN =>
    intro T π h
    obtain ⟨πa, ua, πb, ub, ha, hb, hle, -, hu⟩ := h.min_inv hΦ
    obtain ⟨-, -, hub⟩ := hb.qua_inv hΦ
    subst hu hub
    exact ⟨_, _, Check.qua.cnv hle, .inl .minRN⟩
  | minLL =>
    intro T π h
    obtain ⟨πa, ua, πb, ub, ha, hb, hle, -, hu⟩ := h.min_inv hΦ
    obtain ⟨-, -, hua⟩ := ha.qua_inv hΦ
    obtain ⟨-, -, hub⟩ := hb.qua_inv hΦ
    subst hu hua hub
    exact ⟨_, _, Check.qua.cnv hle, .inl .minLL⟩
  | min_a _ ih =>
    intro T π h
    obtain ⟨πa, ua, πb, ub, ha, hb, hle, -, hu⟩ := h.min_inv hΦ
    simp only [Term.era_lone] at hu; cases hu
    obtain ⟨πa', ua', ha', hs⟩ := ih ha
    refine ⟨_, _, (Check.min ha' hb).cnv hle, ?_⟩
    rcases hs with hs | rfl
    · exact .inl (.min_a hs)
    · exact .inr _root_.rfl
  | min_b _ ih =>
    intro T π h
    obtain ⟨πa, ua, πb, ub, ha, hb, hle, -, hu⟩ := h.min_inv hΦ
    simp only [Term.era_lone] at hu; cases hu
    obtain ⟨πb', ub', hb', hs⟩ := ih hb
    refine ⟨_, _, (Check.min ha hb').cnv hle, ?_⟩
    rcases hs with hs | rfl
    · exact .inl (.min_b hs)
    · exact .inr _root_.rfl
  | app_f hstep ih =>
    intro T π h
    rcases h.app_inv hΦ with ⟨q', A, B, πf, uf, πx, ux, hf, hx, hle, -, hu⟩ | ⟨g, _, rfl, -⟩
    · simp only [Term.era_lone] at hu; cases hu
      obtain ⟨πf', uf', hf', hs⟩ := ih (hf.sp [])
      refine ⟨_, _, (Check.app (hf'.sp [_]) hx).cnv hle, ?_⟩
      rcases hs with hs | rfl
      · exact .inl (.app_f hs)
      · exact .inr _root_.rfl
    · exact hstep.lam.elim
  | app_a hnl hne hstep ih =>
    intro T π h
    rcases h.app_inv hΦ with ⟨q', A, B, πf, uf, πx, ux, hf, hx, hle, -, hu⟩ | ⟨g, _, hg, -⟩
    · simp only [Term.era_lone] at hu; cases hu
      have hq' : q' ≠ .None := fun e => hne (by subst e; exact hx.none_era _root_.rfl)
      rw [Quant.dem_live hq'] at hx
      obtain ⟨πx', ux', hx', hs⟩ := ih hx
      rw [← Quant.dem_live (q := .Lone) hq'] at hx'
      have hconv : Conv β (Term.subst 0 _ B) (Term.subst 0 _ B) :=
        Conv.substR hβ (Conv.of_red_rev (Red.one hstep.step.strong)) 0 B
      refine ⟨_, _, (Check.app (hf.sp [_]) hx').cnv (Le.trans hβ (.conv hconv) hle), ?_⟩
      rcases hs with hs | rfl
      · exact .inl (.app_a hs)
      · exact .inr _root_.rfl
    · exact absurd hg (hnl g)
  | mat_h _ ih =>
    intro T π h
    obtain ⟨A, C, r, ps, q', telF, B, G, πh, uh, πm, um, hA, hC, hr, hlen, hlive, hI, hg, hh, hm,
      hle, -, hu⟩ := h.mat_inv hΦ
    simp only [Term.era_lone] at hu; cases hu
    obtain ⟨πh', uh', hh', hs⟩ := ih hh
    refine ⟨_, _, (Check.mat hA hC hr hlen hlive hI hg hh' hm).cnv hle, ?_⟩
    rcases hs with hs | rfl
    · exact .inl (.mat_h hs)
    · exact .inr _root_.rfl
  | mat_m _ ih =>
    intro T π h
    obtain ⟨A, C, r, ps, q', telF, B, G, πh, uh, πm, um, hA, hC, hr, hlen, hlive, hI, hg, hh, hm,
      hle, -, hu⟩ := h.mat_inv hΦ
    simp only [Term.era_lone] at hu; cases hu
    obtain ⟨πm', um', hm', hs⟩ := ih hm
    refine ⟨_, _, (Check.mat hA hC hr hlen hlive hI hg hh hm').cnv hle, ?_⟩
    rcases hs with hs | rfl
    · exact .inl (.mat_m hs)
    · exact .inr _root_.rfl
  | @rwt_e e ue e' P f uP uf hstep ih =>
    intro T π h
    obtain ⟨a, b, T0, πe, ue, πP, πf, uf, he, hP, hf, hle, -, hu⟩ := h.rwt_inv hΦ
    simp only [Term.era_lone] at hu; cases hu
    obtain ⟨πe', ue', he', hs⟩ := ih he
    have hconv : Conv β (.App (.App P b) _) (.App (.App P b) _) :=
      Conv.app (Conv.refl _) (Conv.of_red_rev (Red.one hstep.step.strong))
    refine ⟨_, _, (Check.rwt he' hP hf).cnv (Le.trans hβ (.conv hconv) hle), ?_⟩
    rcases hs with hs | rfl
    · exact .inl (.rwt_e hs)
    · exact .inr _root_.rfl
  | rwt_f _ ih =>
    intro T π h
    obtain ⟨a, b, T0, πe, ue, πP, πf, uf, he, hP, hf, hle, -, hu⟩ := h.rwt_inv hΦ
    simp only [Term.era_lone] at hu; cases hu
    obtain ⟨πf', uf', hf', hs⟩ := ih hf
    refine ⟨_, _, (Check.rwt he hP hf').cnv hle, ?_⟩
    rcases hs with hs | rfl
    · exact .inl (.rwt_f hs)
    · exact .inr _root_.rfl

-- the instance for a filled book with G's residual: a fired beta/let takes a
-- value whose erasure is not Bad (canon_empty refutes the emptied binder)
theorem Check.step_bad (hok : Book.Ok β) (hF : Book.Filled β) (hE : Book.Era β w 0 β βe)
    (hs : LStep β (fun a ua => Term.Value β a ∧ ¬ Term.Bad β .Lone a ua) t u t')
    (h : Check β (Pol.std β) (LHS.void β) [] .Lone [] t T π u) :
    ∃ π' u', Check β (Pol.std β) (LHS.void β) [] .Lone [] t' T π' u' ∧
      (Step βe .weak u u' ∨ u' = u) :=
  Check.step hok hE (fun hv hx e r ps hred hemp => hv.2
    (Check.canon_empty hok hF (by decide) hv.1 hx (Le.conv hred) hemp)) hs h

end BendCore
