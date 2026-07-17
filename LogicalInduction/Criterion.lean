/-
# Part I — Criterion (`LogicalInduction.Criterion`)

The expressible-feature DSL keystone, traders, and the Logical Induction Criterion. The
DSL is the keystone — invest disproportionately and add non-vacuity examples. Nodes
hosted here (see roadmap §3, Part I):

* `def:tf` (keystone) → `EF`, `EF.denote`, `EF.cost`, `instCommRing EF_n`. An inductive
  syntax over price features `pf φ`, `ℚ`, `+`, `×`, `max(·,·)`, safe reciprocation
  `max(1,·)⁻¹`, with two semantics:
    - `EF.denote : EF → (History → ℝ)` — continuous ℝ-valued; feeds Brouwer.
    - `EF.cost   : EF → ℕ` — syntactic size; an auxiliary bound on description size.
  `EF_n` (rank ≤ `n`) is a commutative ring. The continuity of `denote` is *stated* here;
  its proof may defer.
* `def:valfeature` → `ValuationFeature` — semantic target `EF.denote` lands in.
* `def:tradestrat` → `TradingStrategy` — affine combo `cash + Σ ef_i · φ_i`.
* `def:trader`     → `Trader` — sequence of `n`-strategies.
* `def:exploitation` → `Exploits` — plausible-world values bounded below, `sup = +∞`.
* `def:lic`        → `IsLogicalInductor` — "no e.c. trader exploits the market." The
  hypothesis the entire property tail is conditioned on.

Status (M1): the `def:tf` keystone is landed below (`EF`, `denote`, `cost`, `rank`, the
`CommRing` on rank-≤`n` features, continuity **proved**, non-vacuity witnesses). The
remaining Part-I criterion nodes (`ValuationFeature`, `TradingStrategy`, `Trader`,
`Exploits`, `IsLogicalInductor`) are still TODO in this milestone.
-/
import LogicalInduction.Foundations
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.Computability.PartrecCode
import Mathlib.Data.Rat.Encodable
import Foundation.Propositional.Boolean.Basic

namespace LogicalInduction

/-! ## `def:tf` — Expressible Features (the keystone)

A reified DSL (`dd:dsl`) with two semantics. The *syntax* `EF` is the object that carries
`cost` (for efficient computability) and `rank` (dependence horizon); the *denotation*
`EF.denote` is the continuous ℝ-valued feature the paper's algebra lives on. -/

/-- `def:tf` (Expressible Feature), as syntax. Built from price features `pf φ n`,
rational constants, `+`, `×`, `max(·,·)`, and the safe reciprocation `max(1,·)⁻¹`. -/
inductive EF : Type where
  /-- The price feature `φ^{*n}`: the value of `φ` on day `n`. -/
  | price (φ : Sentence) (n : ℕ) : EF
  /-- A rational constant. -/
  | const (q : ℚ) : EF
  | add (a b : EF) : EF
  | mul (a b : EF) : EF
  | max (a b : EF) : EF
  /-- Safe reciprocation `max(1, a)⁻¹` — never divides by zero, stays in `(0, 1]`. -/
  | safeRecip (a : EF) : EF
  /-- De Bruijn reference used inside a shared `letE` expression. A free reference
  evaluates to zero, making all raw syntax total. -/
  | var (i : ℕ) : EF
  /-- Shared straight-line binding: evaluate `value` once, then evaluate `body` with that
  value available as variable `0` (and prior variables shifted by one). -/
  | letE (value body : EF) : EF
  deriving DecidableEq

namespace EF

/-- Continuous ℝ-valued semantics (`def:tf`). Feeds Brouwer via `continuous_denote`.
Noncomputable because safe reciprocation uses `ℝ`'s (noncomputable) inverse; efficient
computability is tracked syntactically by `cost`, not by running `denote`. -/
noncomputable def denoteWith : EF → List ℝ → History → ℝ
  | price φ n,   _, V => V n φ
  | const q,     _, _ => (q : ℝ)
  | add a b,     ρ, V => a.denoteWith ρ V + b.denoteWith ρ V
  | mul a b,     ρ, V => a.denoteWith ρ V * b.denoteWith ρ V
  | max a b,     ρ, V => Max.max (a.denoteWith ρ V) (b.denoteWith ρ V)
  | safeRecip a, ρ, V => (Max.max 1 (a.denoteWith ρ V))⁻¹
  | var i,       ρ, _ => ρ.getD i 0
  | letE x body, ρ, V => body.denoteWith (x.denoteWith ρ V :: ρ) V

noncomputable def denote (e : EF) (V : History) : ℝ := e.denoteWith [] V

@[simp] theorem denoteWith_price (φ : Sentence) (n : ℕ) (ρ : List ℝ) (V : History) :
    (price φ n).denoteWith ρ V = V n φ := rfl
@[simp] theorem denoteWith_const (q : ℚ) (ρ : List ℝ) (V : History) :
    (const q).denoteWith ρ V = (q : ℝ) := rfl
@[simp] theorem denoteWith_add (a b : EF) (ρ : List ℝ) (V : History) :
    (add a b).denoteWith ρ V = a.denoteWith ρ V + b.denoteWith ρ V := rfl
@[simp] theorem denoteWith_mul (a b : EF) (ρ : List ℝ) (V : History) :
    (mul a b).denoteWith ρ V = a.denoteWith ρ V * b.denoteWith ρ V := rfl
@[simp] theorem denoteWith_max (a b : EF) (ρ : List ℝ) (V : History) :
    (max a b).denoteWith ρ V = Max.max (a.denoteWith ρ V) (b.denoteWith ρ V) := rfl
@[simp] theorem denoteWith_safeRecip (a : EF) (ρ : List ℝ) (V : History) :
    (safeRecip a).denoteWith ρ V = (Max.max 1 (a.denoteWith ρ V))⁻¹ := rfl
@[simp] theorem denoteWith_var (i : ℕ) (ρ : List ℝ) (V : History) :
    (var i).denoteWith ρ V = ρ.getD i 0 := rfl
@[simp] theorem denoteWith_letE (x body : EF) (ρ : List ℝ) (V : History) :
    (letE x body).denoteWith ρ V = body.denoteWith (x.denoteWith ρ V :: ρ) V := rfl

/-- Exact rational evaluation of an expressible feature against a rational price table.
This is the executable semantics used when a computable-market certificate is available. -/
def denoteRatWith : EF → List ℚ → (ℕ → Sentence → ℚ) → ℚ
  | price φ n,   _, V => V n φ
  | const q,     _, _ => q
  | add a b,     ρ, V => a.denoteRatWith ρ V + b.denoteRatWith ρ V
  | mul a b,     ρ, V => a.denoteRatWith ρ V * b.denoteRatWith ρ V
  | max a b,     ρ, V => Max.max (a.denoteRatWith ρ V) (b.denoteRatWith ρ V)
  | safeRecip a, ρ, V => (Max.max 1 (a.denoteRatWith ρ V))⁻¹
  | var i,       ρ, _ => ρ.getD i 0
  | letE x body, ρ, V => body.denoteRatWith (x.denoteRatWith ρ V :: ρ) V

def denoteRat (e : EF) (V : ℕ → Sentence → ℚ) : ℚ := e.denoteRatWith [] V

/-- Rational and real feature semantics agree under pointwise-related variable
environments and price tables. -/
theorem denoteWith_eq_ratCast (e : EF) (P : History) (Q : ℕ → Sentence → ℚ)
    (hQ : ∀ n φ, P n φ = (Q n φ : ℝ)) :
    ∀ (ρR : List ℝ) (ρQ : List ℚ),
      (∀ i, ρR.getD i 0 = (ρQ.getD i 0 : ℝ)) →
      e.denoteWith ρR P = (e.denoteRatWith ρQ Q : ℝ) := by
  induction e with
  | price φ n => intro ρR ρQ hρ; simpa [denoteWith, denoteRatWith] using hQ n φ
  | const q => intro ρR ρQ hρ; rfl
  | add a b iha ihb => intro ρR ρQ hρ; simp [denoteWith, denoteRatWith, iha ρR ρQ hρ, ihb ρR ρQ hρ]
  | mul a b iha ihb => intro ρR ρQ hρ; simp [denoteWith, denoteRatWith, iha ρR ρQ hρ, ihb ρR ρQ hρ]
  | max a b iha ihb => intro ρR ρQ hρ; simp [denoteWith, denoteRatWith, iha ρR ρQ hρ, ihb ρR ρQ hρ]
  | safeRecip a iha => intro ρR ρQ hρ; simp [denoteWith, denoteRatWith, iha ρR ρQ hρ]
  | var i => intro ρR ρQ hρ; exact hρ i
  | letE x body ihx ihbody =>
      intro ρR ρQ hρ
      simp only [denoteWith, denoteRatWith]
      apply ihbody
      intro i
      cases i with
      | zero => simpa using ihx ρR ρQ hρ
      | succ i => simpa using hρ i

/-- Rational and real feature semantics agree when the real history is the coercion of the
rational price table. -/
theorem denote_eq_ratCast (e : EF) (P : History) (Q : ℕ → Sentence → ℚ)
    (hQ : ∀ n φ, P n φ = (Q n φ : ℝ)) :
    e.denote P = (e.denoteRat Q : ℝ) := by
  exact denoteWith_eq_ratCast e P Q hQ [] [] (by simp)

/-- Syntactic size of an expressible feature (`def:tf`): the structural node count. An
auxiliary complexity measure — a small feature is cheap to write down. (Efficient
computability itself is *not* defined via `cost`; it goes through the clocked interpreter,
see `EfficientlyComputable`. `cost` remains a convenient bound on description size.) -/
def cost : EF → ℕ
  | price _ _   => 1
  | const _     => 1
  | add a b     => a.cost + b.cost + 1
  | mul a b     => a.cost + b.cost + 1
  | max a b     => a.cost + b.cost + 1
  | safeRecip a => a.cost + 1
  | var _       => 1
  | letE x body => x.cost + body.cost + 1

/-- Rank = the latest day the feature inspects (`def:valfeature`); `EF_n` = rank ≤ `n`.
`const` inspects nothing (rank `0`); a binary node takes the `max` of its children. -/
def rankWith : EF → List ℕ → ℕ
  | price _ n,   _ => n
  | const _,     _ => 0
  | add a b,     ρ => Nat.max (a.rankWith ρ) (b.rankWith ρ)
  | mul a b,     ρ => Nat.max (a.rankWith ρ) (b.rankWith ρ)
  | max a b,     ρ => Nat.max (a.rankWith ρ) (b.rankWith ρ)
  | safeRecip a, ρ => a.rankWith ρ
  | var i,       ρ => ρ.getD i 0
  | letE x body, ρ => body.rankWith (x.rankWith ρ :: ρ)

def rank : EF → ℕ
  | price _ n   => n
  | const _     => 0
  | add a b     => Nat.max a.rank b.rank
  | mul a b     => Nat.max a.rank b.rank
  | max a b     => Nat.max a.rank b.rank
  | safeRecip a => a.rank
  | var _       => 0
  | letE x body => Nat.max x.rank body.rank

@[simp] theorem rank_price (φ : Sentence) (n : ℕ) : (price φ n).rank = n := rfl
@[simp] theorem rank_const (q : ℚ) : (const q).rank = 0 := rfl
@[simp] theorem rank_add (a b : EF) : (add a b).rank = Nat.max a.rank b.rank := rfl
@[simp] theorem rank_mul (a b : EF) : (mul a b).rank = Nat.max a.rank b.rank := rfl
@[simp] theorem rank_max (a b : EF) : (max a b).rank = Nat.max a.rank b.rank := rfl
@[simp] theorem rank_safeRecip (a : EF) : (safeRecip a).rank = a.rank := rfl
@[simp] theorem rank_var (i : ℕ) : (var i).rank = 0 := rfl
@[simp] theorem rank_letE (x body : EF) : (letE x body).rank = Nat.max x.rank body.rank := rfl

/-! ### `denote` is a ring map on the nose (all `rfl`), packaged for `simp`. -/

@[simp] theorem denote_price (φ : Sentence) (n : ℕ) :
    (price φ n).denote = fun V => V n φ := rfl

@[simp] theorem denote_const (q : ℚ) :
    (const q).denote = fun _ => (q : ℝ) := rfl

@[simp] theorem denote_add (a b : EF) : (add a b).denote = a.denote + b.denote := by
  funext V; simp [denote, denoteWith, Pi.add_apply]

@[simp] theorem denote_mul (a b : EF) : (mul a b).denote = a.denote * b.denote := by
  funext V; simp [denote, denoteWith, Pi.mul_apply]

@[simp] theorem denote_max (a b : EF) (V : History) :
    (max a b).denote V = Max.max (a.denote V) (b.denote V) := rfl

@[simp] theorem denote_safeRecip (a : EF) (V : History) :
    (safeRecip a).denote V = (Max.max 1 (a.denote V))⁻¹ := rfl

/-! ### Continuity (`def:tf`).  Discharged for the whole DSL rather than left as a
constraint — this is what breaks the price/trade circularity the paper needs for Brouwer.
Safe reciprocation is the only nontrivial case: `max 1 x ≥ 1 > 0`, so the reciprocal is
continuous with no removable singularity. -/

private theorem continuous_env_getD (ρ : List (History → ℝ))
    (hρ : ∀ f ∈ ρ, Continuous f) (i : ℕ) :
    Continuous (fun V => (ρ.map (fun f => f V)).getD i 0) := by
  induction ρ generalizing i with
  | nil => simp; exact continuous_const
  | cons f ρ ih =>
      cases i with
      | zero => simpa using hρ f (by simp)
      | succ i =>
          simp only [List.map_cons, List.getD_cons_succ]
          exact ih (fun g hg => hρ g (by simp [hg])) i

theorem continuous_denoteWith (e : EF) : ∀ (ρ : List (History → ℝ)),
    (∀ f ∈ ρ, Continuous f) →
    Continuous (fun V => e.denoteWith (ρ.map (fun f => f V)) V) := by
  induction e with
  | price φ n => intro ρ hρ; exact (continuous_apply φ).comp (continuous_apply n)
  | const q => intro ρ hρ; exact continuous_const
  | add a b ha hb => intro ρ hρ; exact (ha ρ hρ).add (hb ρ hρ)
  | mul a b ha hb => intro ρ hρ; exact (ha ρ hρ).mul (hb ρ hρ)
  | max a b ha hb => intro ρ hρ; exact (ha ρ hρ).max (hb ρ hρ)
  | safeRecip a ha =>
      intro ρ hρ
      refine (continuous_const.max (ha ρ hρ)).inv₀ (fun V => ?_)
      have : (1 : ℝ) ≤ Max.max 1 (a.denoteWith (ρ.map (fun f => f V)) V) :=
        le_max_left _ _
      positivity
  | var i => intro ρ hρ; exact continuous_env_getD ρ hρ i
  | letE x body hx hbody =>
      intro ρ hρ
      simpa [denoteWith] using hbody
        ((fun V => x.denoteWith (ρ.map (fun f => f V)) V) :: ρ)
        (by
          intro f hf
          simp only [List.mem_cons] at hf
          rcases hf with rfl | hf
          · exact hx ρ hρ
          · exact hρ f hf)

theorem continuous_denote (e : EF) : Continuous e.denote := by
  simpa [denote] using continuous_denoteWith e [] (by simp)

/-! ### `EF_n` is a commutative ring (`def:tf`).

Features *are* functions (`def:valfeature`), so the ring structure lives on the semantic
side: `History → ℝ` is a commutative ring pointwise, and the rank-≤`n` expressible
features are a **subring** of it (closed under `+`, `×`, and — via `const (-1) * ·` —
negation). We keep the syntax `EF` as the DSL for `cost`; `EFn n` is the ring the paper's
algebra (`2 - φ*6`, etc.) actually takes place in. -/

/-- The set of rank-≤`n` expressible features, as a subring of the pointwise function
ring `History → ℝ`. -/
def ExpressibleRankLE (n : ℕ) : Subring (History → ℝ) where
  carrier := { f | ∃ e : EF, e.rank ≤ n ∧ e.denote = f }
  zero_mem' := ⟨const 0, by simp, by funext V; simp [denote, denoteWith]⟩
  one_mem' := ⟨const 1, by simp, by funext V; simp [denote, denoteWith]⟩
  add_mem' := by
    rintro f g ⟨ef, hf, rfl⟩ ⟨eg, hg, rfl⟩
    exact ⟨add ef eg, Nat.max_le.mpr ⟨hf, hg⟩, by simp⟩
  mul_mem' := by
    rintro f g ⟨ef, hf, rfl⟩ ⟨eg, hg, rfl⟩
    exact ⟨mul ef eg, Nat.max_le.mpr ⟨hf, hg⟩, by simp⟩
  neg_mem' := by
    rintro f ⟨ef, hf, rfl⟩
    refine ⟨mul (const (-1)) ef, by simpa using hf, ?_⟩
    funext V; simp [denote, denoteWith]

/-- `EF_n`: the rank-≤`n` expressible features. A commutative ring (`def:tf`). -/
abbrev EFn (n : ℕ) : Subring (History → ℝ) := ExpressibleRankLE n

/-- The required `CommRing EF_n` instance (`def:tf`), inherited from the ambient function
ring via the subring structure. -/
example (n : ℕ) : CommRing (EFn n) := inferInstance

theorem denote_mem_EFn (e : EF) : e.denote ∈ EFn e.rank := ⟨e, le_rfl, rfl⟩

/-! ### Non-vacuity witnesses (`def:tf`).  Concrete features with computed denotations,
so the DSL is not an empty shell. -/

/-- Non-vacuity 1 — the paper's running example (`def:tf`): `max(0, φ*6 − ψ*7)`.
Subtraction is sugar for `add a (mul (const (-1)) b)`. -/
def exMaxDiff (φ ψ : Sentence) : EF :=
  max (const 0) (add (price φ 6) (mul (const (-1)) (price ψ 7)))

/-- Its rank is `7`, matching the paper. -/
example (φ ψ : Sentence) : (exMaxDiff φ ψ).rank = 7 := by
  simp [exMaxDiff]

/-- The paper's computed value: with `p₆(φ) = 0.5` and `p₇(ψ) = 0.2`, it returns `0.3`. -/
example (φ ψ : Sentence) (V : History) (h6 : V 6 φ = 0.5) (h7 : V 7 ψ = 0.2) :
    (exMaxDiff φ ψ).denote V = 0.3 := by
  simp only [exMaxDiff, denote_max, denote_add, denote_mul, denote_price, denote_const,
    Pi.add_apply, Pi.mul_apply, h6, h7]
  norm_num

/-- Non-vacuity 2 — safe reciprocation genuinely lands in `(0, 1]`, for *any* argument
feature and history: it never divides by zero. This is the property `max(1,·)⁻¹` exists
to guarantee. -/
example (a : EF) (V : History) :
    0 < (safeRecip a).denote V ∧ (safeRecip a).denote V ≤ 1 := by
  rw [denote_safeRecip]
  have h1 : (1 : ℝ) ≤ Max.max 1 (a.denote V) := le_max_left _ _
  constructor
  · positivity
  · rw [inv_le_one_iff₀]; right; exact h1

/-! ### `Encodable EF` — computable codes for expressible features.

Efficient computability (`def:ec`) requires talking about a machine that *outputs* a
trader's strategies, so those strategies must be encodable as naturals — with a
**computable** decoder (a classical `Countable`-derived encoding would not let a machine
recover the strategy). We build the encoding by hand (there is no `deriving Encodable`),
following Mathlib's own `Nat.Partrec.Code` template: a structural `toNat` and a
well-founded `ofNat`, each child encoded strictly smaller than its parent. -/

/-- Structural encoding of an expressible feature as a natural number, tag-then-payload via
`Nat.pair` only — **no multiplication**. This matters for `def:ec`: `Nat.pair` is a
`Nat.Partrec.Code` *primitive* (`Code.pair`, no `prec`), so a program that builds a
strategy's code from `n` is a tree of `const`/`pair`/`comp` whose clocked-interpreter fuel
is a clean `n + O(1)` — which is what makes responsive traders' efficient computability
provable (see `Computable.lean`). The encoding is still a genuine computable bijection, so
faithfulness of the poly-time e.c. class is unchanged. -/
def toNat : EF → ℕ
  | const q     => Nat.pair 0 (Encodable.encode q)
  | price φ n   => Nat.pair 1 (Nat.pair (Encodable.encode φ) n)
  | add a b     => Nat.pair 2 (Nat.pair a.toNat b.toNat)
  | mul a b     => Nat.pair 3 (Nat.pair a.toNat b.toNat)
  | max a b     => Nat.pair 4 (Nat.pair a.toNat b.toNat)
  | safeRecip a => Nat.pair 5 a.toNat
  | var i       => Nat.pair 6 i
  | letE x body => Nat.pair 7 (Nat.pair x.toNat body.toNat)

/-- Fuel-clocked decoder inverting `EF.toNat`. Structural recursion on `fuel`; each child's
code is strictly smaller (tag `≥ 1` ⇒ `Nat.pair tag X > X`), so `fuel = m + 1` suffices. -/
def ofNatAux : ℕ → ℕ → Option EF
  | 0, _ => none
  | fuel + 1, m =>
    match m.unpair.1 with
    | 0 => (Encodable.decode m.unpair.2 : Option ℚ).map const
    | 1 => (Encodable.decode m.unpair.2.unpair.1 : Option Sentence).map
             (fun φ => price φ m.unpair.2.unpair.2)
    | 2 => (ofNatAux fuel m.unpair.2.unpair.1).bind
             (fun a => (ofNatAux fuel m.unpair.2.unpair.2).map (add a))
    | 3 => (ofNatAux fuel m.unpair.2.unpair.1).bind
             (fun a => (ofNatAux fuel m.unpair.2.unpair.2).map (mul a))
    | 4 => (ofNatAux fuel m.unpair.2.unpair.1).bind
             (fun a => (ofNatAux fuel m.unpair.2.unpair.2).map (max a))
    | 5 => (ofNatAux fuel m.unpair.2).map safeRecip
    | 6 => some (var m.unpair.2)
    | 7 => (ofNatAux fuel m.unpair.2.unpair.1).bind
             (fun x => (ofNatAux fuel m.unpair.2.unpair.2).map (letE x))
    | _ => none

/-- Decoder inverting `EF.toNat`, with fuel `m + 1` (always enough). -/
def ofNat (m : ℕ) : Option EF := ofNatAux (m + 1) m

/-- `Nat.pair t X > X` when the tag `t ≥ 1` — the strict decrease making children smaller. -/
private theorem lt_pair_tag (t X : ℕ) (ht : 0 < t) : X < Nat.pair t X :=
  lt_of_le_of_lt (Nat.right_le_pair 0 X) (Nat.pair_lt_pair_left X ht)

theorem ofNatAux_toNat : ∀ (fuel : ℕ) (e : EF), e.toNat < fuel → ofNatAux fuel e.toNat = some e := by
  intro fuel
  induction fuel with
  | zero => intro e he; omega
  | succ fuel ih =>
      intro e he
      cases e with
      | const q => simp [toNat, ofNatAux, Nat.unpair_pair]
      | price φ n => simp [toNat, ofNatAux, Nat.unpair_pair]
      | add a b =>
          simp only [toNat] at he ⊢
          have h1 := Nat.left_le_pair a.toNat b.toNat
          have h2 := Nat.right_le_pair a.toNat b.toNat
          have h3 := lt_pair_tag 2 (Nat.pair a.toNat b.toNat) (by norm_num)
          simp only [ofNatAux, Nat.unpair_pair, ih a (by omega), ih b (by omega),
            Option.bind_some, Option.map_some]
      | mul a b =>
          simp only [toNat] at he ⊢
          have h1 := Nat.left_le_pair a.toNat b.toNat
          have h2 := Nat.right_le_pair a.toNat b.toNat
          have h3 := lt_pair_tag 3 (Nat.pair a.toNat b.toNat) (by norm_num)
          simp only [ofNatAux, Nat.unpair_pair, ih a (by omega), ih b (by omega),
            Option.bind_some, Option.map_some]
      | max a b =>
          simp only [toNat] at he ⊢
          have h1 := Nat.left_le_pair a.toNat b.toNat
          have h2 := Nat.right_le_pair a.toNat b.toNat
          have h3 := lt_pair_tag 4 (Nat.pair a.toNat b.toNat) (by norm_num)
          simp only [ofNatAux, Nat.unpair_pair, ih a (by omega), ih b (by omega),
            Option.bind_some, Option.map_some]
      | safeRecip a =>
          simp only [toNat] at he ⊢
          have h3 := lt_pair_tag 5 a.toNat (by norm_num)
          simp only [ofNatAux, Nat.unpair_pair, ih a (by omega), Option.map_some]
      | var i => simp [toNat, ofNatAux, Nat.unpair_pair]
      | letE x body =>
          simp only [toNat] at he ⊢
          have h1 := Nat.left_le_pair x.toNat body.toNat
          have h2 := Nat.right_le_pair x.toNat body.toNat
          have h3 := lt_pair_tag 7 (Nat.pair x.toNat body.toNat) (by norm_num)
          simp only [ofNatAux, Nat.unpair_pair, ih x (by omega), ih body (by omega),
            Option.bind_some, Option.map_some]

theorem ofNat_toNat (e : EF) : ofNat e.toNat = some e :=
  ofNatAux_toNat _ e (Nat.lt_succ_self _)

instance : Encodable EF := ⟨toNat, ofNat, ofNat_toNat⟩

/-! ### `EF.serialize` — a **flat, poly-size** token stream for the feature.

`toNat` (above) is a faithful *bijective* code, but its **value blows up doubly-exponentially
in tree depth** (`Nat.pair`-nesting squares the magnitude per level), so a size-`n`, depth-`n`
feature has a `2^{2^n}`-value `toNat` — a `4ⁿ`-*bit* number. Under the clocked interpreter a
fixed program run for `poly n` fuel can only *output* a `poly n`-**value** natural (every
`evaln` clause fuel-guards its inputs, so intermediates stay `≤ fuel`; see
`EfficientlyComputableTok`), i.e. `O(log n)` bits. So whole-number emission of `toNat` wrongly
excludes deep-but-poly-*size* features — the wall behind OPEN RISK 4.

`serialize` is the fix: a flat postfix (RPN) token stream whose **length is `Θ(node count)`**
(`serialize_length_le_cost`), so poly-*size* ⇔ poly-*length*, and whose individual tokens are
small (tags `0..5`, day indices, and the atomic sentence/constant codes). Efficient
computability (`EfficientlyComputableTok`) asks a program to emit this stream *one token at a
time* — polynomially many small tokens — which deep poly-size features admit. The stream is a
genuine encoding: `serialize_injective` (via the stack machine `readM`) shows it determines the
feature. -/
def serialize : EF → List ℕ
  | price φ n   => [0, Encodable.encode φ, n]
  | const q     => [1, Encodable.encode q]
  | add a b     => a.serialize ++ b.serialize ++ [2]
  | mul a b     => a.serialize ++ b.serialize ++ [3]
  | max a b     => a.serialize ++ b.serialize ++ [4]
  | safeRecip a => a.serialize ++ [5]
  | var i       => [7, i]
  | letE x body => x.serialize ++ body.serialize ++ [8]

/-- `serialize`'s length is bounded by `3 · cost` — linear in the node count. This is the
whole point: poly-*size* (poly-`cost`) features have poly-*length* serializations, so
`EfficientlyComputableTok` admits them (unlike `toNat`, whose *value* is exponential). -/
theorem serialize_length_le_cost (e : EF) : (serialize e).length ≤ 3 * e.cost := by
  induction e with
  | price φ n => simp [serialize, cost]
  | const q => simp [serialize, cost]
  | add a b iha ihb => simp only [serialize, cost, List.length_append, List.length_cons,
      List.length_nil]; omega
  | mul a b iha ihb => simp only [serialize, cost, List.length_append, List.length_cons,
      List.length_nil]; omega
  | max a b iha ihb => simp only [serialize, cost, List.length_append, List.length_cons,
      List.length_nil]; omega
  | safeRecip a iha => simp only [serialize, cost, List.length_append, List.length_cons,
      List.length_nil]; omega
  | var i => simp [serialize, cost]
  | letE x body ihx ihbody => simp only [serialize, cost, List.length_append,
      List.length_cons, List.length_nil]; omega

end EF

/-! ## Flat serialization of strategies + unique decodability

A **strategy** is a `List (EF × Sentence)`; `serializeTrades` flattens it to a token stream by
concatenating each coefficient's `EF.serialize` followed by a trade-frame `[6, ⌜φ⌝]`. A single
stack machine `readM` decodes both features (tags `0..5`, pushing onto an `EF` stack) and trade
frames (tag `6`, popping a coefficient and recording the trade), which lets us prove both
`serialize` and `serializeTrades` injective from one roundtrip induction — the honesty guarantee
that the token stream `EfficientlyComputableTok` emits genuinely determines the strategy. -/

namespace EF

/-- The stack machine decoding a token stream. `efst` is the stack of features built so far;
`tr` accumulates decoded trades. Tags `0..5` build features (pushing); tag `6` reads a sentence
code and pops one feature to record a trade. Returns the final `(feature stack, trades)`. -/
def readM : List ℕ → List EF → List (EF × Sentence) → Option (List EF × List (EF × Sentence))
  | [], efst, tr => some (efst, tr)
  | (0 :: p1 :: p2 :: rest), efst, tr =>
      match (Encodable.decode p1 : Option Sentence) with
      | some φ => readM rest (price φ p2 :: efst) tr
      | none => none
  | (1 :: p :: rest), efst, tr =>
      match (Encodable.decode p : Option ℚ) with
      | some q => readM rest (const q :: efst) tr
      | none => none
  | (2 :: rest), (b :: a :: efst), tr => readM rest (add a b :: efst) tr
  | (3 :: rest), (b :: a :: efst), tr => readM rest (mul a b :: efst) tr
  | (4 :: rest), (b :: a :: efst), tr => readM rest (max a b :: efst) tr
  | (5 :: rest), (a :: efst), tr => readM rest (safeRecip a :: efst) tr
  | (6 :: p :: rest), (e :: efst), tr =>
      match (Encodable.decode p : Option Sentence) with
      | some φ => readM rest efst (tr ++ [(e, φ)])
      | none => none
  | (7 :: i :: rest), efst, tr => readM rest (var i :: efst) tr
  | (8 :: rest), (body :: x :: efst), tr => readM rest (letE x body :: efst) tr
  | _, _, _ => none

/-- Reading a feature's serialization pushes exactly that feature (for any stack/trade state).
The single roundtrip induction both `serialize` and `serializeTrades` injectivity rest on. -/
theorem readM_serialize (e : EF) : ∀ (rest : List ℕ) (efst : List EF)
    (tr : List (EF × Sentence)), readM (e.serialize ++ rest) efst tr = readM rest (e :: efst) tr := by
  induction e with
  | price φ n => intro rest efst tr; simp [serialize, readM, Encodable.encodek]
  | const q => intro rest efst tr; simp [serialize, readM, Encodable.encodek]
  | add a b iha ihb => intro rest efst tr
                       simp only [serialize, List.append_assoc, List.cons_append,
                         List.nil_append]
                       rw [iha, ihb]; simp only [readM]
  | mul a b iha ihb => intro rest efst tr
                       simp only [serialize, List.append_assoc, List.cons_append,
                         List.nil_append]
                       rw [iha, ihb]; simp only [readM]
  | max a b iha ihb => intro rest efst tr
                       simp only [serialize, List.append_assoc, List.cons_append,
                         List.nil_append]
                       rw [iha, ihb]; simp only [readM]
  | safeRecip a iha => intro rest efst tr
                       simp only [serialize, List.append_assoc, List.cons_append,
                         List.nil_append]
                       rw [iha]; simp only [readM]
  | var i => intro rest efst tr; simp [serialize, readM]
  | letE x body ihx ihbody => intro rest efst tr
                              simp only [serialize, List.append_assoc, List.cons_append,
                                List.nil_append]
                              rw [ihx, ihbody]; simp only [readM]

/-- Decode a lone feature: accept iff the machine ends with a single feature and no trades. -/
def deserialize (toks : List ℕ) : Option EF :=
  match readM toks [] [] with
  | some ([e], []) => some e
  | _ => none

theorem deserialize_serialize (e : EF) : deserialize e.serialize = some e := by
  unfold deserialize
  rw [← List.append_nil e.serialize, readM_serialize]
  simp only [readM]

/-- **`serialize` is injective** — the token stream determines the feature. -/
theorem serialize_injective : Function.Injective serialize := by
  intro a b h
  have ha := deserialize_serialize a
  rw [h, deserialize_serialize] at ha
  exact (Option.some.inj ha).symm

end EF

/-- Flatten a strategy to a token stream: each trade is its coefficient's `EF.serialize`
followed by the frame `[6, ⌜φ⌝]`. This is the object `EfficientlyComputableTok` requires a
program to emit token-by-token. -/
def serializeTrades : List (EF × Sentence) → List ℕ
  | [] => []
  | (e, φ) :: rest => e.serialize ++ (6 :: Encodable.encode φ :: serializeTrades rest)

/-! ### A one-token streaming decoder

`EF.readM` above is convenient for round-trip proofs, but several of its equations consume
two or three tokens at once.  The equivalent streaming presentation below records that small
amount of parser control state explicitly, so execution is one `List.foldl`.  This is the form
used by the concrete LIA compiler.

The state is `((mode, pendingSentence), (featureStack, trades))`.  Mode `0` is ready; modes
`1,2` read a price's sentence/day; mode `3` reads a constant; mode `4` reads a trade sentence;
and mode `5` reads a variable index. -/

abbrev EF.StreamState :=
  (ℕ × Option Sentence) × (List EF × List (EF × Sentence))

def EF.streamInitial : EF.StreamState := ((0, none), ([], []))

/-- Consume exactly one token of the flat strategy serialization. -/
def EF.streamStep : Option EF.StreamState → ℕ → Option EF.StreamState
  | none, _ => none
  | some ((mode, pending), (efst, trades)), token =>
      if mode = 0 then
        if token = 0 then some ((1, none), (efst, trades))
        else if token = 1 then some ((3, none), (efst, trades))
        else if token = 2 then
          match efst with
          | b :: a :: rest => some ((0, none), (EF.add a b :: rest, trades))
          | _ => none
        else if token = 3 then
          match efst with
          | b :: a :: rest => some ((0, none), (EF.mul a b :: rest, trades))
          | _ => none
        else if token = 4 then
          match efst with
          | b :: a :: rest => some ((0, none), (EF.max a b :: rest, trades))
          | _ => none
        else if token = 5 then
          match efst with
          | a :: rest => some ((0, none), (EF.safeRecip a :: rest, trades))
          | [] => none
        else if token = 6 then some ((4, none), (efst, trades))
        else if token = 7 then some ((5, none), (efst, trades))
        else if token = 8 then
          match efst with
          | body :: x :: rest => some ((0, none), (EF.letE x body :: rest, trades))
          | _ => none
        else none
      else if mode = 1 then
        (Encodable.decode (α := Sentence) token).map fun φ =>
          ((2, some φ), (efst, trades))
      else if mode = 2 then
        pending.map fun φ => ((0, none), (EF.price φ token :: efst, trades))
      else if mode = 3 then
        (Encodable.decode (α := ℚ) token).map fun q =>
          ((0, none), (EF.const q :: efst, trades))
      else if mode = 4 then
        match efst, Encodable.decode (α := Sentence) token with
        | e :: rest, some φ => some ((0, none), (rest, trades ++ [(e, φ)]))
        | _, _ => none
      else if mode = 5 then
        some ((0, none), (EF.var token :: efst, trades))
      else none

/-- Run the streaming parser from an explicit state. -/
def EF.streamReadFrom (tokens : List ℕ) (state : Option EF.StreamState) :
    Option EF.StreamState :=
  tokens.foldl EF.streamStep state

@[simp] theorem EF.streamReadFrom_append (left right : List ℕ)
    (state : Option EF.StreamState) :
    EF.streamReadFrom (left ++ right) state =
      EF.streamReadFrom right (EF.streamReadFrom left state) := by
  simp [EF.streamReadFrom, List.foldl_append]

/-- Reading one canonical feature serialization pushes exactly that feature. -/
theorem EF.streamReadFrom_serialize_self (e : EF) (efst : List EF)
    (trades : List (EF × Sentence)) :
    EF.streamReadFrom e.serialize (some ((0, none), (efst, trades))) =
      some ((0, none), (e :: efst, trades)) := by
  induction e generalizing efst trades with
  | price φ n => simp [EF.serialize, EF.streamReadFrom, EF.streamStep, Encodable.encodek]
  | const q => simp [EF.serialize, EF.streamReadFrom, EF.streamStep, Encodable.encodek]
  | add a b iha ihb =>
      simp only [EF.serialize, List.append_assoc]
      rw [EF.streamReadFrom_append, iha, EF.streamReadFrom_append, ihb]
      simp [EF.streamReadFrom, EF.streamStep]
  | mul a b iha ihb =>
      simp only [EF.serialize, List.append_assoc]
      rw [EF.streamReadFrom_append, iha, EF.streamReadFrom_append, ihb]
      simp [EF.streamReadFrom, EF.streamStep]
  | max a b iha ihb =>
      simp only [EF.serialize, List.append_assoc]
      rw [EF.streamReadFrom_append, iha, EF.streamReadFrom_append, ihb]
      simp [EF.streamReadFrom, EF.streamStep]
  | safeRecip a iha =>
      simp only [EF.serialize]
      rw [EF.streamReadFrom_append, iha]
      simp [EF.streamReadFrom, EF.streamStep]
  | var i => simp [EF.serialize, EF.streamReadFrom, EF.streamStep]
  | letE x body ihx ihbody =>
      simp only [EF.serialize, List.append_assoc]
      rw [EF.streamReadFrom_append, ihx, EF.streamReadFrom_append, ihbody]
      simp [EF.streamReadFrom, EF.streamStep]

theorem EF.streamReadFrom_serialize (e : EF) (rest : List ℕ) (efst : List EF)
    (trades : List (EF × Sentence)) :
    EF.streamReadFrom (e.serialize ++ rest)
      (some ((0, none), (efst, trades))) =
    EF.streamReadFrom rest (some ((0, none), (e :: efst, trades))) := by
  rw [EF.streamReadFrom_append, EF.streamReadFrom_serialize_self]

/-- Reading a canonical strategy serialization records exactly its trades. -/
theorem EF.streamReadFrom_serializeTrades_self (l : List (EF × Sentence))
    (efst : List EF) (trades : List (EF × Sentence)) :
    EF.streamReadFrom (serializeTrades l)
      (some ((0, none), (efst, trades))) =
      some ((0, none), (efst, trades ++ l)) := by
  induction l generalizing efst trades with
  | nil => simp [serializeTrades, EF.streamReadFrom]
  | cons trade rest ih =>
      rcases trade with ⟨e, φ⟩
      change EF.streamReadFrom
        (e.serialize ++ ([6, Encodable.encode φ] ++ serializeTrades rest))
        (some ((0, none), (efst, trades))) = _
      rw [EF.streamReadFrom_append, EF.streamReadFrom_serialize_self,
        EF.streamReadFrom_append]
      have hframe : EF.streamReadFrom [6, Encodable.encode φ]
          (some ((0, none), (e :: efst, trades))) =
          some ((0, none), (efst, trades ++ [(e, φ)])) := by
        simp [EF.streamReadFrom, EF.streamStep, Encodable.encodek]
      rw [hframe, ih]
      simp [List.append_assoc]

/-- Reading a strategy's serialization records exactly its trades (onto any state). -/
theorem readM_serializeTrades (l : List (EF × Sentence)) : ∀ (rest : List ℕ) (efst : List EF)
    (tr : List (EF × Sentence)),
    EF.readM (serializeTrades l ++ rest) efst tr = EF.readM rest efst (tr ++ l) := by
  induction l with
  | nil => intro rest efst tr; simp [serializeTrades]
  | cons t rest_l ih =>
      obtain ⟨e, φ⟩ := t
      intro rest efst tr
      simp only [serializeTrades, List.append_assoc, List.cons_append]
      rw [EF.readM_serialize]
      simp only [EF.readM, Encodable.encodek]
      rw [ih, List.append_assoc]
      rfl

/-- Decode a strategy with the one-token streaming machine: accept iff parsing ends ready
with an empty feature stack. -/
def deserializeTrades (toks : List ℕ) : Option (List (EF × Sentence)) :=
  match EF.streamReadFrom toks (some EF.streamInitial) with
  | some ((0, none), ([], l)) => some l
  | _ => none

theorem deserializeTrades_serializeTrades (l : List (EF × Sentence)) :
    deserializeTrades (serializeTrades l) = some l := by
  unfold deserializeTrades EF.streamInitial
  rw [EF.streamReadFrom_serializeTrades_self]
  rfl

/-- **`serializeTrades` is injective** — the token stream determines the strategy. -/
theorem serializeTrades_injective : Function.Injective serializeTrades := by
  intro a b h
  have ha := deserializeTrades_serializeTrades a
  rw [h, deserializeTrades_serializeTrades] at ha
  exact (Option.some.inj ha).symm

/-! ## `def:world` + Propositional Consistency

A world (`def:world`) is a truth assignment `Sentence → 𝔹`. The only worlds the criterion
quantifies over are the **propositionally consistent** ones (`def:pc`): those determined by
Boolean algebra from an assignment to prime sentences. Rather than re-derive Boolean
recursion over Foundation's connectives, we take a p.c. world to *be* a Foundation Boolean
model — an atom valuation `ℕ → Prop` read through `Formula.Boolean.val` — which is exactly
"determined by Boolean algebra from the atoms". Provenance `(b)`. -/

/-- A propositionally consistent world (`def:world` + p.c.): an assignment to the atoms,
whose truth value on a compound sentence is fixed by Foundation's classical Boolean
semantics. -/
def PCWorld : Type := LO.Propositional.Boolean.Valuation ℕ

namespace PCWorld

open Classical

/-- Whether `φ` is true in the p.c. world `v` (Foundation's Boolean evaluation). -/
def Holds (v : PCWorld) (φ : Sentence) : Prop :=
  LO.Propositional.Formula.Boolean.val v φ

/-- The truth value of `φ` in `v` as a real number in `{0, 1}` — the payout of a
`φ`-share in world `v`. Used to value a trader's holdings. -/
noncomputable def payout (v : PCWorld) (φ : Sentence) : ℝ :=
  if v.Holds φ then 1 else 0

/-- `v` is propositionally consistent **with** a finite set `D` (`v ∈ pcworlds(D)`): it
makes every sentence in `D` true. (Consistency itself is automatic — `v` is a Boolean
model.) -/
def ConsistentWith (v : PCWorld) (D : Finset Sentence) : Prop :=
  ∀ φ ∈ D, v.Holds φ

end PCWorld

/-! ## `def:dedproc` — Deductive Process -/

/-- `def:dedproc`. A nested sequence `D 0 ⊆ D 1 ⊆ ⋯` of finite sets of sentences,
interpreted as the theorems revealed by day `n`.

Computability is packaged separately below, so the bare order-theoretic object remains
convenient in semantic lemmas while logical-inductor instances carry the paper-required
certificate. -/
structure DeductiveProcess where
  /-- The sentences revealed by day `n`. -/
  D : ℕ → Finset Sentence
  /-- The revealed sets are nondecreasing. -/
  mono : ∀ n, D n ⊆ D (n + 1)

/-- A deductive process is computable in the paper's unary-time sense: one fixed partial
recursive program eventually emits the encoded finite set `D n`.  No polynomial runtime is
required. -/
def ComputableDeductiveProcess (DP : DeductiveProcess) : Prop :=
  ∃ code : Nat.Partrec.Code, ∀ n, Encodable.encode (DP.D n) ∈ code.eval n

/-- A named presentation of a computable deductive process.  This is equivalent to
`ComputableDeductiveProcess`, but keeps the program and its semantic specification
available to finite certificate checkers. -/
structure DeductiveProcessComputation (DP : DeductiveProcess) where
  code : Nat.Partrec.Code
  code_spec : ∀ n, Encodable.encode (DP.D n) ∈ code.eval n

theorem ComputableDeductiveProcess.nonemptyComputation
    {DP : DeductiveProcess} (h : ComputableDeductiveProcess DP) :
    Nonempty (DeductiveProcessComputation DP) := by
  obtain ⟨code, hcode⟩ := h
  exact ⟨⟨code, hcode⟩⟩

theorem DeductiveProcessComputation.toComputable
    {DP : DeductiveProcess} (c : DeductiveProcessComputation DP) :
    ComputableDeductiveProcess DP :=
  ⟨c.code, c.code_spec⟩

/-- Any terminating clocked output of the certified deductive-process program is the
unique encoding of the claimed finite stage.  This is the soundness bridge used by a
bounded dovetailer. -/
theorem DeductiveProcessComputation.evaln_eq_stage
    {DP : DeductiveProcess} (c : DeductiveProcessComputation DP)
    {n fuel out : ℕ}
    (h : out ∈ Nat.Partrec.Code.evaln fuel c.code n) :
    out = Encodable.encode (DP.D n) := by
  exact Part.mem_unique (Nat.Partrec.Code.evaln_sound h) (c.code_spec n)

/-- Every certified deductive stage eventually appears at some finite clock. -/
theorem DeductiveProcessComputation.exists_evaln_stage
    {DP : DeductiveProcess} (c : DeductiveProcessComputation DP) (n : ℕ) :
    ∃ fuel, Encodable.encode (DP.D n) ∈
      Nat.Partrec.Code.evaln fuel c.code n :=
  Nat.Partrec.Code.evaln_complete.mp (c.code_spec n)

/-- Run the deductive-process program for exactly `fuel` interpreter steps and decode its
output as a finite sentence set.  `none` represents either timeout or malformed output. -/
def DeductiveProcessComputation.stageAtFuel
    {DP : DeductiveProcess} (c : DeductiveProcessComputation DP)
    (fuel n : ℕ) : Option (Finset Sentence) :=
  (Nat.Partrec.Code.evaln fuel c.code n).bind
    (Encodable.decode (α := Finset Sentence))

theorem DeductiveProcessComputation.stageAtFuel_sound
    {DP : DeductiveProcess} (c : DeductiveProcessComputation DP)
    {fuel n : ℕ} {stage : Finset Sentence}
    (h : c.stageAtFuel fuel n = some stage) :
    stage = DP.D n := by
  unfold stageAtFuel at h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨out, hout, hdecode⟩ := h
  have houtEq := c.evaln_eq_stage hout
  subst out
  simpa using hdecode.symm

theorem DeductiveProcessComputation.stageAtFuel_complete
    {DP : DeductiveProcess} (c : DeductiveProcessComputation DP) (n : ℕ) :
    ∃ fuel, c.stageAtFuel fuel n = some (DP.D n) := by
  obtain ⟨fuel, hfuel⟩ := c.exists_evaln_stage n
  refine ⟨fuel, ?_⟩
  unfold stageAtFuel
  change Nat.Partrec.Code.evaln fuel c.code n =
    some (Encodable.encode (DP.D n)) at hfuel
  rw [hfuel]
  simp

/-- A decoded deductive stage, once available, remains available at every larger clock. -/
theorem DeductiveProcessComputation.stageAtFuel_mono
    {DP : DeductiveProcess} (c : DeductiveProcessComputation DP)
    {fuel fuel' n : ℕ} {stage : Finset Sentence}
    (hff : fuel ≤ fuel') (h : c.stageAtFuel fuel n = some stage) :
    c.stageAtFuel fuel' n = some stage := by
  unfold stageAtFuel at h ⊢
  rw [Option.bind_eq_some_iff] at h ⊢
  obtain ⟨out, hout, hdecode⟩ := h
  exact ⟨out, Nat.Partrec.Code.evaln_mono hff hout, hdecode⟩

/-- Search the first `fuel` interpreter clocks for a decoded deductive stage.  This is a
literal bounded dovetail: it is total for each bound and retains the first successful
decode. -/
def DeductiveProcessComputation.stageSearchUpTo
    {DP : DeductiveProcess} (c : DeductiveProcessComputation DP) (n : ℕ) :
    ℕ → Option (Finset Sentence)
  | 0 => none
  | fuel + 1 =>
      match c.stageSearchUpTo n fuel with
      | some stage => some stage
      | none => c.stageAtFuel fuel n

/-- Every successful bounded stage search returns the certified semantic stage; malformed
outputs and timeouts can never manufacture a different finite theory. -/
theorem DeductiveProcessComputation.stageSearchUpTo_sound
    {DP : DeductiveProcess} (c : DeductiveProcessComputation DP)
    {n fuel : ℕ} {stage : Finset Sentence}
    (h : c.stageSearchUpTo n fuel = some stage) :
    stage = DP.D n := by
  induction fuel with
  | zero => simp [stageSearchUpTo] at h
  | succ fuel ih =>
      rw [stageSearchUpTo] at h
      cases hprev : c.stageSearchUpTo n fuel with
      | some prior =>
          simp only [hprev] at h
          cases h
          exact ih hprev
      | none =>
          simp only [hprev] at h
          exact c.stageAtFuel_sound h

/-- The bounded deductive-stage dovetail reaches the exact stage at a finite clock. -/
theorem DeductiveProcessComputation.exists_stageSearchUpTo
    {DP : DeductiveProcess} (c : DeductiveProcessComputation DP) (n : ℕ) :
    ∃ clock, c.stageSearchUpTo n clock = some (DP.D n) := by
  obtain ⟨fuel, hfuel⟩ := c.stageAtFuel_complete n
  cases hprev : c.stageSearchUpTo n fuel with
  | some stage =>
      have hstage := c.stageSearchUpTo_sound hprev
      subst stage
      exact ⟨fuel, hprev⟩
  | none =>
      refine ⟨fuel + 1, ?_⟩
      simp [stageSearchUpTo, hprev, hfuel]

/-- The least successful bound for the deductive-stage dovetail.  As with MarketMaker's
stopping index, the noncomputable minimum is used only to state totality; execution is the
bounded function `stageSearchUpTo`. -/
noncomputable def DeductiveProcessComputation.stageSearchClock
    {DP : DeductiveProcess} (c : DeductiveProcessComputation DP) (n : ℕ) : ℕ :=
  Nat.find (c.exists_stageSearchUpTo n)

theorem DeductiveProcessComputation.stageSearch_clock
    {DP : DeductiveProcess} (c : DeductiveProcessComputation DP) (n : ℕ) :
    c.stageSearchUpTo n (c.stageSearchClock n) = some (DP.D n) :=
  Nat.find_spec (c.exists_stageSearchUpTo n)

/-- Exact finite stage decoded at the certified stopping clock. -/
noncomputable def DeductiveProcessComputation.computedStage
    {DP : DeductiveProcess} (c : DeductiveProcessComputation DP) (n : ℕ) :
    Finset Sentence :=
  (c.stageSearchUpTo n (c.stageSearchClock n)).get
    (by rw [c.stageSearch_clock n]; rfl)

theorem DeductiveProcessComputation.computedStage_eq
    {DP : DeductiveProcess} (c : DeductiveProcessComputation DP) (n : ℕ) :
    c.computedStage n = DP.D n := by
  apply Option.some.inj
  calc
    some (c.computedStage n) =
        c.stageSearchUpTo n (c.stageSearchClock n) := by
      exact Option.some_get _
    _ = some (DP.D n) := c.stageSearch_clock n

/-- The deductive process reconstructed solely through the bounded stage-search interface.
Its monotonicity is transported from the certified semantic specification. -/
noncomputable def DeductiveProcessComputation.computedProcess
    {DP : DeductiveProcess} (c : DeductiveProcessComputation DP) : DeductiveProcess where
  D := c.computedStage
  mono n := by
    rw [c.computedStage_eq n, c.computedStage_eq (n + 1)]
    exact DP.mono n

theorem DeductiveProcessComputation.computedProcess_eq
    {DP : DeductiveProcess} (c : DeductiveProcessComputation DP) :
    c.computedProcess = DP := by
  unfold computedProcess
  congr 1
  funext n
  exact c.computedStage_eq n

/-- A paper-faithful computable rational market certificate. `quote n ⌜φ⌝` is the exact
rational price of `φ` on day `n`, and one fixed partial-recursive program computes this
two-argument table (with its input paired into one natural). No polynomial runtime is
required of the market itself.

The extra values of `quote` on naturals that do not encode a sentence are harmless and make
the computational interface total. -/
def ComputableMarket (P : History) : Prop :=
  ∃ (quote : ℕ → ℕ → ℚ) (code : Nat.Partrec.Code),
    (∀ n φ, P n φ = (quote n (Encodable.encode φ) : ℝ)) ∧
    ∀ z, Encodable.encode (quote z.unpair.1 z.unpair.2) ∈ code.eval z

/-- A named exact rational program presenting a computable market.  The existential
paper-facing predicate above is convenient in theorem statements; this structure is the
operational form consumed by finite clocked certificate checkers. -/
structure MarketComputation (P : History) where
  quote : ℕ → ℕ → ℚ
  code : Nat.Partrec.Code
  quote_exact : ∀ n φ, P n φ = (quote n (Encodable.encode φ) : ℝ)
  code_spec : ∀ z, Encodable.encode (quote z.unpair.1 z.unpair.2) ∈ code.eval z

theorem ComputableMarket.nonemptyComputation
    {P : History} (h : ComputableMarket P) : Nonempty (MarketComputation P) := by
  obtain ⟨quote, code, hexact, hcode⟩ := h
  exact ⟨⟨quote, code, hexact, hcode⟩⟩

theorem MarketComputation.toComputable
    {P : History} (c : MarketComputation P) : ComputableMarket P :=
  ⟨c.quote, c.code, c.quote_exact, c.code_spec⟩

/-- Any terminating clocked output of the certified market program is the unique exact
rational quote for that paired input. -/
theorem MarketComputation.evaln_eq_quote
    {P : History} (c : MarketComputation P) {z fuel out : ℕ}
    (h : out ∈ Nat.Partrec.Code.evaln fuel c.code z) :
    out = Encodable.encode (c.quote z.unpair.1 z.unpair.2) := by
  exact Part.mem_unique (Nat.Partrec.Code.evaln_sound h) (c.code_spec z)

/-- Decoded rational form of `MarketComputation.evaln_eq_quote`. -/
theorem MarketComputation.evaln_quote_eq
    {P : History} (c : MarketComputation P) {z fuel : ℕ} {q : ℚ}
    (h : Encodable.encode q ∈ Nat.Partrec.Code.evaln fuel c.code z) :
    q = c.quote z.unpair.1 z.unpair.2 := by
  exact Encodable.encode_injective (c.evaln_eq_quote h)

/-- Every exact rational market quote eventually appears at some finite clock. -/
theorem MarketComputation.exists_evaln_quote
    {P : History} (c : MarketComputation P) (z : ℕ) :
    ∃ fuel, Encodable.encode (c.quote z.unpair.1 z.unpair.2) ∈
      Nat.Partrec.Code.evaln fuel c.code z :=
  Nat.Partrec.Code.evaln_complete.mp (c.code_spec z)

/-- Run the market program for exactly `fuel` interpreter steps and decode its output as
an exact rational.  This is the executable quote source for historical maturity checks. -/
def MarketComputation.quoteAtFuel
    {P : History} (c : MarketComputation P)
    (fuel day : ℕ) (φ : Sentence) : Option ℚ :=
  (Nat.Partrec.Code.evaln fuel c.code
    (Nat.pair day (Encodable.encode φ))).bind (Encodable.decode (α := ℚ))

theorem MarketComputation.quoteAtFuel_sound
    {P : History} (c : MarketComputation P)
    {fuel day : ℕ} {φ : Sentence} {q : ℚ}
    (h : c.quoteAtFuel fuel day φ = some q) :
    q = c.quote day (Encodable.encode φ) := by
  unfold quoteAtFuel at h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨out, hout, hdecode⟩ := h
  have houtEq := c.evaln_eq_quote hout
  simp only [Nat.unpair_pair] at houtEq
  subst out
  simpa using hdecode.symm

theorem MarketComputation.quoteAtFuel_complete
    {P : History} (c : MarketComputation P) (day : ℕ) (φ : Sentence) :
    ∃ fuel, c.quoteAtFuel fuel day φ =
      some (c.quote day (Encodable.encode φ)) := by
  let z := Nat.pair day (Encodable.encode φ)
  obtain ⟨fuel, hfuel⟩ := c.exists_evaln_quote z
  refine ⟨fuel, ?_⟩
  unfold quoteAtFuel
  change Nat.Partrec.Code.evaln fuel c.code z =
    some (Encodable.encode (c.quote z.unpair.1 z.unpair.2)) at hfuel
  simp only [z, Nat.unpair_pair] at hfuel
  rw [hfuel]
  simp

/-- A decoded market quote, once available, remains available at every larger clock. -/
theorem MarketComputation.quoteAtFuel_mono
    {P : History} (c : MarketComputation P)
    {fuel fuel' day : ℕ} {φ : Sentence} {q : ℚ}
    (hff : fuel ≤ fuel') (h : c.quoteAtFuel fuel day φ = some q) :
    c.quoteAtFuel fuel' day φ = some q := by
  unfold quoteAtFuel at h ⊢
  rw [Option.bind_eq_some_iff] at h ⊢
  obtain ⟨out, hout, hdecode⟩ := h
  exact ⟨out, Nat.Partrec.Code.evaln_mono hff hout, hdecode⟩

/-- One finite clock simultaneously recovers every quote in a finite query list.  This is
the compactness step used to evaluate a whole finite strategy prefix at one fuel value. -/
theorem MarketComputation.exists_fuel_quoteAtFuel_list
    {P : History} (c : MarketComputation P)
    (queries : List (ℕ × Sentence)) :
    ∃ fuel, ∀ query ∈ queries,
      c.quoteAtFuel fuel query.1 query.2 =
        some (c.quote query.1 (Encodable.encode query.2)) := by
  induction queries with
  | nil => exact ⟨0, by simp⟩
  | cons head tail ih =>
      obtain ⟨headFuel, hhead⟩ := c.quoteAtFuel_complete head.1 head.2
      obtain ⟨tailFuel, htail⟩ := ih
      refine ⟨max headFuel tailFuel, ?_⟩
      intro query hquery
      simp only [List.mem_cons] at hquery
      rcases hquery with rfl | hquery
      · exact c.quoteAtFuel_mono (le_max_left _ _) hhead
      · exact c.quoteAtFuel_mono (le_max_right _ _) (htail query hquery)

namespace EF

/-- The finite market cells inspected by an expressible feature.  Duplicates are harmless:
the list is syntax-directed and therefore directly executable. -/
def priceQueries : EF → List (ℕ × Sentence)
  | price φ n => [(n, φ)]
  | const _ => []
  | add a b => a.priceQueries ++ b.priceQueries
  | mul a b => a.priceQueries ++ b.priceQueries
  | max a b => a.priceQueries ++ b.priceQueries
  | safeRecip a => a.priceQueries
  | var _ => []
  | letE value body => value.priceQueries ++ body.priceQueries

/-- Exact rational evaluation with a partial quote table.  At a price node it runs the
certified market program for `fuel` steps; timeout or malformed output propagates as `none`. -/
def denoteRatWithAtFuel {P : History} (market : MarketComputation P) (fuel : ℕ) :
    EF → List ℚ → Option ℚ
  | price φ n,   _ => market.quoteAtFuel fuel n φ
  | const q,     _ => some q
  | add a b,     ρ => do
      let qa ← a.denoteRatWithAtFuel market fuel ρ
      let qb ← b.denoteRatWithAtFuel market fuel ρ
      pure (qa + qb)
  | mul a b,     ρ => do
      let qa ← a.denoteRatWithAtFuel market fuel ρ
      let qb ← b.denoteRatWithAtFuel market fuel ρ
      pure (qa * qb)
  | max a b,     ρ => do
      let qa ← a.denoteRatWithAtFuel market fuel ρ
      let qb ← b.denoteRatWithAtFuel market fuel ρ
      pure (Max.max qa qb)
  | safeRecip a, ρ => do
      let qa ← a.denoteRatWithAtFuel market fuel ρ
      pure (Max.max 1 qa)⁻¹
  | var i,       ρ => some (ρ.getD i 0)
  | letE value body, ρ => do
      let q ← value.denoteRatWithAtFuel market fuel ρ
      body.denoteRatWithAtFuel market fuel (q :: ρ)

/-- Every successful bounded evaluation is semantically exact.  In particular, malformed
decoded outputs cannot make a finite certificate checker accept: quote soundness fixes each
price leaf, and the remaining computation is exact rational arithmetic. -/
theorem denoteRatWithAtFuel_sound
    {P : History} (market : MarketComputation P) (fuel : ℕ) (e : EF) (ρ : List ℚ)
    {q : ℚ} (h : e.denoteRatWithAtFuel market fuel ρ = some q) :
    q = e.denoteRatWith ρ
      (fun n φ => market.quote n (Encodable.encode φ)) := by
  induction e generalizing ρ q with
  | price φ n =>
      exact market.quoteAtFuel_sound h
  | const value =>
      simpa [denoteRatWithAtFuel, denoteRatWith] using h.symm
  | add a b iha ihb =>
      simp only [denoteRatWithAtFuel, Option.bind_eq_bind] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨qa, ha, h⟩ := h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨qb, hb, hq⟩ := h
      change some (qa + qb) = some q at hq
      injection hq with hq
      subst q
      simp only [denoteRatWith]
      rw [iha ρ ha, ihb ρ hb]
  | mul a b iha ihb =>
      simp only [denoteRatWithAtFuel, Option.bind_eq_bind] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨qa, ha, h⟩ := h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨qb, hb, hq⟩ := h
      change some (qa * qb) = some q at hq
      injection hq with hq
      subst q
      simp only [denoteRatWith]
      rw [iha ρ ha, ihb ρ hb]
  | max a b iha ihb =>
      simp only [denoteRatWithAtFuel, Option.bind_eq_bind] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨qa, ha, h⟩ := h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨qb, hb, hq⟩ := h
      change some (Max.max qa qb) = some q at hq
      injection hq with hq
      subst q
      simp only [denoteRatWith]
      rw [iha ρ ha, ihb ρ hb]
  | safeRecip a iha =>
      simp only [denoteRatWithAtFuel, Option.bind_eq_bind] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨qa, ha, hq⟩ := h
      change some (Max.max 1 qa)⁻¹ = some q at hq
      injection hq with hq
      subst q
      simp only [denoteRatWith]
      rw [iha ρ ha]
  | var i =>
      simpa [denoteRatWithAtFuel, denoteRatWith] using h.symm
  | letE value body ihvalue ihbody =>
      simp only [denoteRatWithAtFuel, Option.bind_eq_bind] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨qvalue, hvalue, hbody⟩ := h
      have hv := ihvalue ρ hvalue
      have hb := ihbody (qvalue :: ρ) hbody
      simpa only [denoteRatWith, hv] using hb

/-- Successful bounded feature evaluation is monotone in the interpreter clock. -/
theorem denoteRatWithAtFuel_mono
    {P : History} (market : MarketComputation P) {fuel fuel' : ℕ} (e : EF)
    (ρ : List ℚ) {q : ℚ} (hff : fuel ≤ fuel')
    (h : e.denoteRatWithAtFuel market fuel ρ = some q) :
    e.denoteRatWithAtFuel market fuel' ρ = some q := by
  induction e generalizing ρ q with
  | price φ n => exact market.quoteAtFuel_mono hff h
  | const value => simpa [denoteRatWithAtFuel] using h
  | add a b iha ihb =>
      simp only [denoteRatWithAtFuel, Option.bind_eq_bind] at h ⊢
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨qa, ha, h⟩ := h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨qb, hb, hq⟩ := h
      rw [iha ρ ha, ihb ρ hb]
      exact hq
  | mul a b iha ihb =>
      simp only [denoteRatWithAtFuel, Option.bind_eq_bind] at h ⊢
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨qa, ha, h⟩ := h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨qb, hb, hq⟩ := h
      rw [iha ρ ha, ihb ρ hb]
      exact hq
  | max a b iha ihb =>
      simp only [denoteRatWithAtFuel, Option.bind_eq_bind] at h ⊢
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨qa, ha, h⟩ := h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨qb, hb, hq⟩ := h
      rw [iha ρ ha, ihb ρ hb]
      exact hq
  | safeRecip a iha =>
      simp only [denoteRatWithAtFuel, Option.bind_eq_bind] at h ⊢
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨qa, ha, hq⟩ := h
      rw [iha ρ ha]
      exact hq
  | var i => simpa [denoteRatWithAtFuel] using h
  | letE value body ihvalue ihbody =>
      simp only [denoteRatWithAtFuel, Option.bind_eq_bind] at h ⊢
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨qvalue, hvalue, hbody⟩ := h
      rw [ihvalue ρ hvalue]
      exact ihbody (qvalue :: ρ) hbody

/-- With every syntactically requested quote ready at the shared clock, bounded evaluation
returns exactly the total rational semantics. -/
theorem denoteRatWithAtFuel_complete
    {P : History} (market : MarketComputation P) (fuel : ℕ) (e : EF) (ρ : List ℚ)
    (hready : ∀ query ∈ e.priceQueries,
      market.quoteAtFuel fuel query.1 query.2 =
        some (market.quote query.1 (Encodable.encode query.2))) :
    e.denoteRatWithAtFuel market fuel ρ =
      some (e.denoteRatWith ρ
        (fun n φ => market.quote n (Encodable.encode φ))) := by
  induction e generalizing ρ with
  | price φ n => exact hready (n, φ) (by simp [priceQueries])
  | const q => rfl
  | add a b iha ihb =>
      have ha := iha ρ (fun query hquery => hready query (by
        simp only [priceQueries, List.mem_append]
        exact Or.inl hquery))
      have hb := ihb ρ (fun query hquery => hready query (by
        simp only [priceQueries, List.mem_append]
        exact Or.inr hquery))
      simp [denoteRatWithAtFuel, denoteRatWith, ha, hb]
  | mul a b iha ihb =>
      have ha := iha ρ (fun query hquery => hready query (by
        simp only [priceQueries, List.mem_append]
        exact Or.inl hquery))
      have hb := ihb ρ (fun query hquery => hready query (by
        simp only [priceQueries, List.mem_append]
        exact Or.inr hquery))
      simp [denoteRatWithAtFuel, denoteRatWith, ha, hb]
  | max a b iha ihb =>
      have ha := iha ρ (fun query hquery => hready query (by
        simp only [priceQueries, List.mem_append]
        exact Or.inl hquery))
      have hb := ihb ρ (fun query hquery => hready query (by
        simp only [priceQueries, List.mem_append]
        exact Or.inr hquery))
      simp [denoteRatWithAtFuel, denoteRatWith, ha, hb]
  | safeRecip a iha =>
      have ha := iha ρ (fun query hquery => hready query (by
        simpa only [priceQueries] using hquery))
      simp [denoteRatWithAtFuel, denoteRatWith, ha]
  | var i => rfl
  | letE value body ihvalue ihbody =>
      have hvalue := ihvalue ρ (fun query hquery => hready query (by
        simp only [priceQueries, List.mem_append]
        exact Or.inl hquery))
      let q := value.denoteRatWith ρ
        (fun n φ => market.quote n (Encodable.encode φ))
      have hbody := ihbody (q :: ρ) (fun query hquery => hready query (by
        simp only [priceQueries, List.mem_append]
        exact Or.inr hquery))
      simpa [denoteRatWithAtFuel, denoteRatWith, hvalue, q] using hbody

/-- Every finite expressible feature eventually evaluates exactly under the certified
market program, at one shared clock for all of its price queries. -/
theorem exists_fuel_denoteRatWithAtFuel
    {P : History} (market : MarketComputation P) (e : EF) (ρ : List ℚ) :
    ∃ fuel, e.denoteRatWithAtFuel market fuel ρ =
      some (e.denoteRatWith ρ
        (fun n φ => market.quote n (Encodable.encode φ))) := by
  obtain ⟨fuel, hfuel⟩ := market.exists_fuel_quoteAtFuel_list e.priceQueries
  exact ⟨fuel, e.denoteRatWithAtFuel_complete market fuel ρ hfuel⟩

end EF

/-! ## `def:tradestrat`, `def:trader` — Trading strategies and traders

An `n`-strategy (`def:tradestrat`) is the paper's canonical encoding: a finite list of
`(coefficient, sentence)` pairs `(eᵢ, φᵢ)` with each `eᵢ` an expressible feature of rank
`≤ n`. It denotes `∑ᵢ eᵢ · (φᵢ − φᵢ*ⁿ)` — "buy `eᵢ(𝓥)` shares of `φᵢ` at the day-`n`
price", the cash term being determined by the pairs. -/

/-- `def:tradestrat`. A trading strategy for day `n`. -/
structure Strategy (n : ℕ) where
  /-- The `(expressible-feature coefficient, sentence)` pairs `(eᵢ, φᵢ)`. -/
  trades : List (EF × Sentence)
  /-- Every coefficient has rank `≤ n` (the strategy sees only prices up to day `n`). -/
  rank_le : ∀ p ∈ trades, p.1.rank ≤ n

namespace Strategy

/-- The value of an `n`-strategy against a history `𝓥`, as assessed by a world with payout
`w` (`w φ ∈ {0,1}`): `∑ᵢ eᵢ(𝓥) · (w φᵢ − 𝓥ₙ(φᵢ))`. Each summand is "shares bought times
(world payout − price paid at day `n`)". -/
noncomputable def value {n : ℕ} (T : Strategy n) (V : History) (w : Sentence → ℝ) : ℝ :=
  (T.trades.map (fun p => p.1.denote V * (w p.2 - V n p.2))).sum

/-- Syntactic size of a strategy, summing its coefficients' `EF.cost`. Feeds the
efficient-computability bound (`dd:fuel`). -/
def cost {n : ℕ} (T : Strategy n) : ℕ :=
  (T.trades.map (fun p => p.1.cost)).sum + T.trades.length + 1

end Strategy

/-- `def:trader`. A sequence of trading strategies, one per day. -/
structure Trader where
  /-- The strategy the trader plays on day `n`. -/
  strat : (n : ℕ) → Strategy n

namespace Trader

/-- The trader's net worth after day `n`, assessed by the p.c. world `v`:
`∑_{i ≤ n} vᵢ(𝓥)` — the sum of its day-`i` strategy values, priced at each day `i`. -/
noncomputable def netWorth (Tr : Trader) (V : History) (v : PCWorld) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), (Tr.strat i).value V v.payout

/-- The set of **plausible assessments** of `Tr`'s net worth against history `𝓥`: its net
worth on day `n`, as valued by any world propositionally consistent with `D n`, over all
`n` (`def:exploitation`). -/
def plausibleAssessments (Tr : Trader) (V : History) (DP : DeductiveProcess) : Set ℝ :=
  { x | ∃ (n : ℕ) (v : PCWorld), v.ConsistentWith (DP.D n) ∧ x = Tr.netWorth V v n }

/-- `def:exploitation`. `Tr` **exploits** the history `𝓥` relative to `DP` if its plausible
assessments are bounded below but not bounded above — unbounded upside off bounded
downside. -/
def Exploits (Tr : Trader) (V : History) (DP : DeductiveProcess) : Prop :=
  BddBelow (Tr.plausibleAssessments V DP) ∧ ¬ BddAbove (Tr.plausibleAssessments V DP)

end Trader

/-! ## `def:ec`, `def:lic` — Efficient computability and the Logical Induction Criterion -/

/-- Fuel bound for the constant code: `Code.const K` on input `n` halts with output `K`
within `n + K + 1` steps of the clocked interpreter. (`comp` layers share fuel in `evaln`,
so the budget is just the input length `n` plus the `K` successor steps.) A reusable tool
for certifying that constant-strategy traders are efficiently computable. -/
theorem evaln_const_self : ∀ (K n : ℕ),
    K ∈ Nat.Partrec.Code.evaln (n + K + 1) (Nat.Partrec.Code.const K) n := by
  intro K
  induction K with
  | zero =>
      intro n
      show 0 ∈ Nat.Partrec.Code.evaln (n + 1) Nat.Partrec.Code.zero n
      simp [Nat.Partrec.Code.evaln]
  | succ K ih =>
      intro n
      have hxe : Nat.Partrec.Code.evaln (n + (K + 1) + 1) (Nat.Partrec.Code.const K) n
          = some K := Nat.Partrec.Code.evaln_mono (by omega) (ih n)
      show (K + 1) ∈ Nat.Partrec.Code.evaln (n + (K + 1) + 1)
        (Nat.Partrec.Code.comp .succ (Nat.Partrec.Code.const K)) n
      simp [Nat.Partrec.Code.evaln, hxe, Option.bind_eq_some_iff, Option.guard_eq_some']
      omega

/-- `def:ec` (`dd:fuel`) — **whole-number clocked model. SUPERSEDED by
`EfficientlyComputableTok`** (below); no longer the definition `IsLogicalInductor` uses. Kept
because its statement is true and its certification pipeline (`EfficientlyComputable.of_fueled`,
`ec_of_polyEF`, …) is sound — but it is **faithful only for bounded-depth traders**: it asks a
program to output the day-`n` strategy's `Encodable.encode` *as one number*, and that number's
value is `2^{poly n}` for a deep poly-size feature, unemittable in `evaln (poly n)`. That is
OPEN RISK 4; the fix is the token-indexed `EfficientlyComputableTok`. A trader is (Val-)e.c. if a
program `c`, run on input `n` for a *polynomial* fuel budget `a·(n+1)ᵏ + a`, outputs the encoded
day-`n` strategy. -/
def EfficientlyComputable (Tr : Trader) : Prop :=
  ∃ (c : Nat.Partrec.Code) (a k : ℕ),
    ∀ n, Nat.Partrec.Code.evaln (a * (n + 1) ^ k + a) c n
        = some (Encodable.encode (Tr.strat n).trades)

/-! `def:ec` (`dd:fuel`) — **token-indexed emission, the poly-*size* model**. A trader is
**efficiently computable** if one program emits the length of the day-`n` strategy's flat
token stream and a second program emits that stream **one token at a time**.  Both programs
run under one polynomial clock.  The length emitter is load-bearing: a mere polynomial
*bound* on the extensional stream length would admit traders whose stopping length varies
uncomputably with `n`, and such a class could not be redundantly enumerated by the
construction's `TradingFirm`.

This replaces whole-number emission of `Encodable.encode` (`EfficientlyComputable` above). The
reason is a hard limit of the clocked interpreter, not a stylistic choice: every `evaln` clause
fuel-guards its inputs (`guard (n ≤ k)` in `Mathlib.Computability.PartrecCode`), so a fixed
program run for `poly n` fuel can only *output* a value `≤ poly n` — `O(log n)` bits.

That claim is **proved**, not read off the source: `codeEvaln_result_le` with
`codeEvalBound_poly` (`Construction/M7Witnesses.lean`) bound a fixed code's output by an
explicit polynomial in the fuel; compose with the clock. Note it is *not* "output `≤ fuel`"
— that is false, and proved false (`evaln_output_can_exceed_fuel`, `Computable.lean`) — and
it does not follow from Mathlib's `evaln_bound`, which bounds the input only. A strategy
whose `Encodable.encode` is a large number (any poly-*size* but deep feature: its `toNat` value
is `2^{poly n}`) is therefore *unemittable as one number*, though the paper's poly-*size*
`def:ec` admits it. Emitting the `serializeTrades` stream token-by-token — polynomially many
`poly n`-value tokens (`serialize_length_le_cost` makes the stream length `Θ(size)`) — is the
faithful poly-*size* rendering, and it is what deep traders (`thm:con` hysteresis, `thm:nd`
purchase counters) need. See OPEN RISK 4 in `PROGRESS.md`.

**Residual disclosure (type-`(c)`):** each token's *value* is still generated by a clocked
program, so a traded
sentence's atomic code `⌜φ⌝` must be `poly n`-value on day `n`. Fixed sentences (every current
trader) are constant, absorbed into `a`; varying-sentence traders already carry a poly bound on
`⌜φₙ⌝`. Formula-level sub-tokenization would remove even this and is a later refinement. -/

/-- Run a length program and then a token program under a shared clock.  The requested
length is clamped to the clock, so every index emits a polynomial-size stream even when its
length program returns a large paired numeral. -/
def clockedTokens (lengthCode tokenCode : Nat.Partrec.Code) (clock n : ℕ) : List ℕ :=
  match Nat.Partrec.Code.evaln clock lengthCode n with
  | none => []
  | some length => List.ofFn fun i : Fin (min length clock) =>
      (Nat.Partrec.Code.evaln clock tokenCode (Nat.pair n i)).getD 0

/-- Validate a serialized day-`n` strategy, including its rank discipline.  Malformed
streams denote the zero strategy. -/
def strategyOfTokens (n : ℕ) (tokens : List ℕ) : Strategy n :=
  match hdecode : deserializeTrades tokens with
  | none => ⟨[], by simp⟩
  | some trades =>
      if h : ∀ trade ∈ trades, trade.1.rank ≤ n then ⟨trades, h⟩ else ⟨[], by simp⟩

/-- The total trader denoted by two programs and a day-dependent clock. -/
def clockedTrader (lengthCode tokenCode : Nat.Partrec.Code) (clock : ℕ → ℕ) : Trader where
  strat n := strategyOfTokens n (clockedTokens lengthCode tokenCode (clock n) n)

def EfficientlyComputableTok (Tr : Trader) : Prop :=
  ∃ (lengthCode tokenCode : Nat.Partrec.Code) (a k : ℕ),
    clockedTrader lengthCode tokenCode (fun n => a * (n + 1) ^ k + a) = Tr

/-- `def:lic`. The market `P` satisfies the **Logical Induction Criterion** relative to
`DP` if no efficiently computable trader exploits it. This is the hypothesis the entire
property tail is conditioned on (`[IsLogicalInductor P DP]`). With the faithful
`EfficientlyComputableTok` above (the poly-*size*, token-indexed model — OPEN RISK 4
resolved), this is the paper's `def:lic` on the nose, and it now admits deep poly-size
exploiters (hysteresis, purchase counters) that the whole-number `EfficientlyComputable`
excluded. -/
class IsLogicalInductor (P : History) (DP : DeductiveProcess) : Prop where
  /-- Markets are computable rational pricing sequences in the paper's definition. -/
  marketComputable : ComputableMarket P
  /-- Deductive processes are computable nested finite-set sequences in the paper's
  definition. -/
  processComputable : ComputableDeductiveProcess DP
  /-- No efficiently computable trader exploits `P`. -/
  noExploit : ∀ Tr : Trader, EfficientlyComputableTok Tr → ¬ Tr.Exploits P DP

/-! ### Sanity / non-vacuity for the criterion machinery.

`Exploits` must be a genuinely refutable condition, not vacuously true — otherwise `def:lic`
would be empty. The do-nothing trader witnesses this: it never trades, so its net worth is
identically `0`, its plausible assessments lie in `{0}`, and it does **not** exploit. -/

/-- The trader that never trades. -/
def Trader.zero : Trader := ⟨fun _ => ⟨[], by simp⟩⟩

@[simp] theorem Trader.zero_netWorth (V : History) (v : PCWorld) (n : ℕ) :
    Trader.zero.netWorth V v n = 0 := by
  simp [Trader.netWorth, Trader.zero, Strategy.value]

/-- The do-nothing trader exploits nothing: `Exploits` is refutable, so the criterion is
not vacuous. -/
theorem Trader.zero_not_exploits (V : History) (DP : DeductiveProcess) :
    ¬ Trader.zero.Exploits V DP := by
  rintro ⟨_, hnab⟩
  refine hnab ⟨0, ?_⟩
  rintro x ⟨n, v, _, rfl⟩
  simp

end LogicalInduction
