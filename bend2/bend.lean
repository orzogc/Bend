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
-- THE MODEL REFUSES one thing bend.ts accepts: a book with an @unsafe
-- def or a surviving ?TODO. bend.ts reports both in its verdict, and the
-- claims are for clean verdicts. Every other bend.ts permission is a
-- rule below.
-- TWO HYPOTHESES beyond Book.Ok enter the termination claims (4, 5):
--   Wall: no live call runs ahead in fill order. A user def cannot make
--       one (a live reference needs a filled or native target), but a
--       base def may live-call a base law filled later — the b flag —
--       and base.bend does, in seventeen helper pairs (a helper calls
--       the pending law that calls it back). The checker tests descent
--       on self-calls only, so those cycles are trusted by inspection,
--       like the natives; the model says so by naming the hypothesis.
--   Tipped: every bodiless native (base's F32 primitives, a foreign
--       fill) is typed at a telescope tipped at a family with a
--       constructor. It is what makes a stuck native call harmless;
--       base.bend satisfies it (F32, U32, Bool, String, Maybe, IO).
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
-- (1) confluence of strong reduction; (2) subject reduction along weak
-- steps of closed terms; (3) progress at live demand; (4) weak
-- normalization of closed live terms; (5) consistency: no closed live
-- term inhabits an empty family, given Tipped natives.
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

-- retip r n ty: reannotate the Adt head at the tip of an n-binder
-- telescope with the peeled set r. A constructor checks against the
-- REMAINDER of its family (bend.ts ctrs_find over book_adt's filtered
-- constructors): its head type here carries any peeled set that does not
-- contain it, which is what lets a mismatched scrutinee re-check at the
-- peeled domain of a match's tail
def Term.retip (r : List Nat) : Nat → Term → Term
  | 0, t =>
    match (Term.spine t).1 with
    | .Adt a _ => Term.apps (.Adt a r) (Term.spine t).2
    | _        => t
  | n + 1, .All q A B => .All q A (Term.retip r n B)
  | _ + 1, t => t

-- CtxDead β Γ: some LIVE binding in scope has an emptied datatype, so the
-- region is unreachable (bend.ts ctx_dead; an erased binding proves
-- nothing, since dead code inhabits Empty)
def CtxDead (β : Book) (Γ : Ctx) : Prop :=
  ∃ i b a r ps, Ctx.get Γ i = some b ∧ b.q ≠ .None ∧
    Red β .weak (Ctx.δ Γ 0 b.T) (Term.apps (.Adt a r) ps) ∧ Book.empty β a r

-- Check β L sp q Γ t T π u: under the equation L and the pending spine
-- sp (the arguments above t, infer-app's sp), at demand q, t has type T
-- consuming π, and elaborates to u: the certified term with every part
-- checked dead replaced by the token Quant (what the compiler runs;
-- bend.ts's Infer/Check answer tm, the same term with its dead parts kept
-- for printing). Demands are None and Lone only in any derivation rooted
-- at Book.Ok; Many is a measure value. A None-demand derivation measures
-- only None and elaborates to the token, and the rule that checks a
-- premise dead drops its measure from the conclusion, as in bend.ts.
inductive Check (β : Book) : LHS → List Term → Quant → Ctx → Term → Term → Uses → Term → Prop
  -- Γ[i] = q' A
  -- ------------------------- infer-var
  -- Γ ⊢ x_i : A ~ {i : q}
  | var : Ctx.get Γ i = some b →
          Check β L sp q Γ (.Var i) b.T (Uses.one i q) (Term.era q (.Var i))
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
          Check β L sp q Γ (.Ref j) d.ty Uses.zero (Term.era q (.Ref j))
  -- β[k] = adt(sig, cs), nullary: the one bare-head spelling (a
  -- parameterized family head is an error: D<..> is the one spelling)
  -- --------------------------------------------------------- infer-ref (adt)
  -- Γ ⊢ @k : sig ~ {}
  | refA : Book.adt β k = some A → A.pn = 0 →
           Check β L sp q Γ (.Ref k) A.sig Uses.zero (Term.era q (.Ref k))
  -- β[a] = adt(sig, cs)
  -- ------------------------- infer-adt (head; the parameters apply)
  -- Γ ⊢ Adt a r : sig ~ {}
  | adt : Book.adt β a = some A →
          Check β L sp q Γ (.Adt a r) A.sig Uses.zero (Term.era q (.Adt a r))
  -- β[a].cs[c] = ctr(T)    c not peeled by r
  -- ----------------------------------------- check-ctr (head; the
  -- Γ ⊢ Ctr a c : retip r T ~ {}                parameters and fields apply)
  | ctr : Book.adt β a = some A → AdtD.ctr A c = some C → c ∉ r →
          Check β L sp q Γ (.Ctr a c) (Term.retip r (A.pn + C.fn) C.ty) Uses.zero
            (Term.era q (.Ctr a c))
  -- Γ ⊢ g : Quant    (dead)
  -- ------------------------- infer-typ
  -- Γ ⊢ Kind(g) : Type ~ {}
  | typ : Check β L [] .None Γ g .Qnt πg .Qnt →
          Check β L sp q Γ (.Typ g) (.Typ (.Qua .Lone)) Uses.zero
            (Term.era q (.Typ .Qnt))
  -- ------------------------- infer-qnt
  -- Γ ⊢ Quant : Type ~ {}      Γ ⊢ &q : Quant ~ {}
  | qnt : Check β L sp q Γ .Qnt (.Typ (.Qua .Lone)) Uses.zero .Qnt
  | qua : Check β L sp q Γ (.Qua q') .Qnt Uses.zero (Term.era q (.Qua q'))
  -- Γ ⊢ a : Quant ~ πa    Γ ⊢ b : Quant ~ πb    (both at the ambient demand)
  -- ------------------------------------------------ infer-min
  -- Γ ⊢ a <&> b : Quant ~ πa + πb
  | min : Check β L [] q Γ a .Qnt πa ua →
          Check β L [] q Γ b .Qnt πb ub →
          Check β L sp q Γ (.Min a b) .Qnt (Uses.add πa πb) (Term.era q (.Min ua ub))
  -- Γ ⊢ A : Kind(q')    Γ, q' A ⊢ B : Type    (both dead)
  -- ------------------------------------------------ infer-all
  -- Γ ⊢ @q' A -> B : Type ~ {}
  | all : Check β L [] .None Γ A (.Typ (.Qua q')) πA .Qnt →
          Check β L.shift [] .None (⟨q', A, none⟩ :: Γ) B (.Typ (.Qua .Lone)) πB .Qnt →
          Check β L sp q Γ (.All q' A B) (.Typ (.Qua .Lone)) Uses.zero
            (Term.era q (.All q' .Qnt .Qnt))
  -- Γ, q' A ⊢ f : B ~ π    π[0] <= q'
  -- where L binds the next column by x while one remains
  -- ------------------------------------------------ check-lam
  -- Γ ⊢ λ f : @q' A -> B ~ tail π
  | lam : Check β L.lam [] q (⟨q', A, none⟩ :: Γ) f B π uf →
          Quant.le (π 0) q' →
          Check β L sp q Γ (.Lam f) (.All q' A B) (Uses.tail π) (Term.era q (.Lam uf))
  -- Γ ⊢ f : @q' A -> B ~ πf (with x pending)    Γ ⊢ x : A ~ πx at dem q' q
  -- where x is dead if q' is -, and consumed once otherwise: its measure
  --       adds unscaled (certify-once), a + callee copies it
  -- --------------------------------------------------------------- infer-app
  -- Γ ⊢ f(x) : B[0 := x] ~ πf + πx
  | app : Check β L (x :: sp) q Γ f (.All q' A B) πf uf →
          Check β L [] (Quant.dem q' q) Γ x A πx ux →
          Check β L sp q Γ (.App f x) (Term.subst 0 x B) (Uses.add πf πx)
            (Term.era q (.App uf ux))
  -- Γ ⊢ f[0 := a] : T ~ π
  -- ------------------------------ infer-app (a lambda head: one beta step)
  -- Γ ⊢ (λ f)(a) : T ~ π
  | appLam : Check β L sp q Γ (Term.subst 0 a f) T π u →
             Check β L sp q Γ (.App (.Lam f) a) T π u
  -- Γ ⊢ v : A ~ πv at dem qb q    Γ ⊢ A : Kind(qb)    (dead)
  -- Γ, qb A = v ⊢ b : T↑ ~ π    π[0] <= qb
  -- ------------------------------------------------------------------- check-let
  -- Γ ⊢ qb x = v; b : T ~ πv + tail π
  | let_ : Check β L [] (Quant.dem qb q) Γ v A πv uv →
           Check β L [] .None Γ A (.Typ (.Qua qb)) πA .Qnt →
           Check β L.shift [] q (⟨qb, A, some v⟩ :: Γ) b (Term.shift 0 T) π ub →
           Quant.le (π 0) qb →
           Check β L sp q Γ (.Let qb v b) T (Uses.add πv (Uses.tail π))
             (Term.era q (.Let qb uv ub))
  -- Γ ⊢ T : Type    Γ ⊢ a : T    Γ ⊢ b : T    (all dead; evidence is erased)
  -- --------------------------------------------------- infer-eql
  -- Γ ⊢ {a == b : T} : Data ~ {}
  | eql : Check β L [] .None Γ T (.Typ (.Qua .Lone)) πT .Qnt →
          Check β L [] .None Γ a T πa .Qnt →
          Check β L [] .None Γ b T πb .Qnt →
          Check β L sp q Γ (.Eql a b T) (.Typ (.Qua .Many)) Uses.zero
            (Term.era q (.Eql .Qnt .Qnt .Qnt))
  -- a == b    (let-expanded, compare EQ)
  -- ------------------------------ check-rfl
  -- Γ ⊢ {==} : {a == b : T} ~ {}
  | rfl : Conv β (Ctx.δ Γ 0 a) (Ctx.δ Γ 0 b) →
          Check β L sp q Γ .Rfl (.Eql a b T) Uses.zero (Term.era q .Rfl)
  -- Γ ⊢ e : {a == b : T} ~ πe
  -- Γ ⊢ P : @x:T -> @_:{a == x : T} -> Type    (dead; the J motive)
  -- Γ ⊢ f : P(a, {==}) ~ πf
  -- ------------------------------------------ check-rwt
  -- Γ ⊢ %e : P; f : P(b, e) ~ πe + πf
  | rwt : Check β L [] q Γ e (.Eql a b T) πe ue →
          Check β L [] .None Γ P (Term.jmotive a T) πP .Qnt →
          Check β L [] q Γ f (.App (.App P a) .Rfl) πf uf →
          Check β L sp q Γ (.Rwt e P f) (.App (.App P b) e) (Uses.add πe πf)
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
          Check β (L.mat a c C.fn) [] q Γ h G πh uh →
          Check β L [] q Γ m (.All q' (Term.apps (.Adt a (c :: r)) ps) B) πm um →
          Check β L sp q Γ (.Mat a c h m) (.All q' (Term.apps (.Adt a r) ps) B)
            (Uses.join πh πm) (Term.era q (.Mat a c uh um))
  -- every constructor of β[a] is peeled, or a LIVE binding in scope has an
  -- emptied type; q' is live in a live region
  -- --------------------------------------------------------------------- check-efq
  -- Γ ⊢ \{} : @q' (Adt a r) · ps -> B ~ {}
  | efq : Book.adt β a = some A →
          (q ≠ .None → q' ≠ .None) →
          (Book.empty β a r ∨ CtxDead β Γ) →
          Check β L sp q Γ .Efq (.All q' (Term.apps (.Adt a r) ps) B) Uses.zero
            (Term.era q .Efq)
  -- Γ ⊢ t : A ~ π    A <= B    (let-expanded, compare LE)
  -- ------------------------ check-any
  -- Γ ⊢ t : B ~ π
  | cnv : Check β L sp q Γ t A π u → Le β (Ctx.δ Γ 0 A) (Ctx.δ Γ 0 B) →
          Check β L sp q Γ t B π u

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
      (∃ π, Check β ⟨k, .Ref k, 0, [], false⟩ [] .None Γ A
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
        (∃ π, Check β ⟨k, .Ref k, 0, [], false⟩ [] .None [] A.sig (.Typ (.Qua .Lone)) π .Qnt) ∧
        ∃ G, STele β A.pn A.sig G ∧
        ∀ c C, AdtD.ctr A c = some C →
          CtrD.Shape k A.pn C ∧ CtrOk β k A.pn G [] 0 C.ty
    | .defn d =>
        (∃ π, Check β ⟨k, .Ref k, 0, [], false⟩ [] .None [] d.ty (.Typ (.Qua .Lone)) π .Qnt) ∧
        TeleQs β d.ty d.n d.qs ∧
        (d.body = none → d.b = true) ∧
        (∀ b, d.body = some b → Tree β d.n b ∧
          ∃ π u, Check β ⟨k, .Ref k, d.n, d.qs, false⟩ [] .Lone [] b d.ty π u)

-- Book.Wall: every body also checks with the wall up, so no live call
-- runs ahead in fill order and the live reference graph is well-founded.
-- A book without natives has it for free (only base.bend mints the b
-- flag); base.bend itself breaks it in seventeen helper pairs
-- (Map.seek.bit calls the pending law Map.seek, which calls it back),
-- each a structural recursion by inspection that the checker does not
-- test. Claims (4) and (5) assume it
def Book.Wall (β : Book) : Prop :=
  ∀ k d b, Book.defn β k = some d → d.body = some b →
    ∃ π u, Check β ⟨k, .Ref k, d.n, d.qs, true⟩ [] .Lone [] b d.ty π u

-- Tipped β T: a telescope tipped at a family with a constructor. The
-- consistency claim assumes it of every bodiless native's type: a stuck
-- native call then never inhabits an empty family (base's F32 primitives
-- answer F32, U32, Bool or String; a foreign fill answers IO)
inductive Tipped (β : Book) : Term → Prop
  | adt : Book.adt β a = some A → A.ctrs ≠ [] → Tipped β (Term.apps (.Adt a r) ps)
  | all : Tipped β B → Tipped β (.All q A B)
  | red : Red β .strong T T' → Tipped β T' → Tipped β T

def Book.Tipped (β : Book) : Prop :=
  ∀ k d, Book.defn β k = some d → d.body = none → BendCore.Tipped β d.ty

-- ============================================================================
-- §11 Claims (bend.ts states these in prose; PART II proves them)
-- ============================================================================

def church_rosser : Prop :=
  ∀ (β : Book) (a b c : Term),
    Book.Ok β → Red β .strong a b → Red β .strong a c →
    ∃ d, Red β .strong b d ∧ Red β .strong c d

def subject_reduction : Prop :=
  ∀ (β : Book) (q : Quant) (t t' T : Term) (π : Uses) (u : Term),
    Book.Ok β → Check β (LHS.void β) [] q [] t T π u → Step β .weak t t' →
    ∃ π' u', Check β (LHS.void β) [] q [] t' T π' u'

def progress : Prop :=
  ∀ (β : Book) (q : Quant) (t T : Term) (π : Uses) (u : Term),
    Book.Ok β → q ≠ .None → Check β (LHS.void β) [] q [] t T π u →
    Term.Value β t ∨ ∃ t', Step β .weak t t'

def normalization : Prop :=
  ∀ (β : Book) (t T : Term) (π : Uses) (u : Term),
    Book.Ok β → Book.Wall β → Check β (LHS.void β) [] .Lone [] t T π u →
    ∃ v π' u', Red β .weak t v ∧ Term.Value β v ∧
      Check β (LHS.void β) [] .Lone [] v T π' u'

def consistency : Prop :=
  ∀ (β : Book) (a : Nat) (A : AdtD) (r : List Nat) (ps : List Term)
    (t : Term) (π : Uses) (u : Term),
    Book.Ok β → Book.Wall β → Book.Tipped β →
    Book.adt β a = some A → A.ctrs = [] →
    ¬ Check β (LHS.void β) [] .Lone [] t (Term.apps (.Adt a r) ps) π u



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

end BendCore
