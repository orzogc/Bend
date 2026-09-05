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
--       where bend.ts takes one beta step first (both are here).
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
-- TYPING (§9). One judgment, Check β L sp q Γ t T π u: under the
-- equation L and the pending spine sp, at demand q, t has type T
-- consuming π and elaborates to u, the certified term with its dead
-- parts erased to the token Quant (bend.ts answers the elaborated term;
-- comp.ts erases exactly these parts). Every rule is bend.ts's rule of
-- the same name, spelled as its derivation comment. The var rule charges the ambient demand; a type position, an
-- erased argument, a kind's quantity, an equality endpoint and a motive
-- check dead; no rule coerces dead to live. A live reference to a
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
-- region is unreachable (bend.ts ctx_dead; an erased binding proves
-- nothing, since dead code inhabits Empty)
def CtxDead (β : Book) (Γ : Ctx) : Prop :=
  ∃ i b a r ps, Ctx.get Γ i = some b ∧ b.q ≠ .None ∧
    Red β .weak (Ctx.δ Γ 0 b.T) (Term.apps (.Adt a r) ps) ∧ Book.empty β a r

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

end BendCore
