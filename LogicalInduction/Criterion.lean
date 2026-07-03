/-
# Part I — Criterion (`LogicalInduction.Criterion`)

The expressible-feature DSL keystone, traders, and the Logical Induction Criterion. The
DSL is the keystone — invest disproportionately and add non-vacuity examples. Nodes
hosted here (see roadmap §3, Part I):

* `def:tf` (keystone) → `EF`, `EF.denote`, `EF.cost`, `instCommRing EF_n`. An inductive
  syntax over price features `pf φ`, `ℚ`, `+`, `×`, `max(·,·)`, safe reciprocation
  `max(1,·)⁻¹`, with two semantics:
    - `EF.denote : EF → (History → ℝ)` — continuous ℝ-valued; feeds Brouwer.
    - `EF.cost   : EF → ℕ` — syntactic size; certifies efficient computability in the
      construction **and in every property proof's exploiting trader**.
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
  deriving DecidableEq

namespace EF

/-- Continuous ℝ-valued semantics (`def:tf`). Feeds Brouwer via `continuous_denote`.
Noncomputable because safe reciprocation uses `ℝ`'s (noncomputable) inverse; efficient
computability is tracked syntactically by `cost`, not by running `denote`. -/
noncomputable def denote : EF → History → ℝ
  | price φ n,   V => V n φ
  | const q,     _ => (q : ℝ)
  | add a b,     V => a.denote V + b.denote V
  | mul a b,     V => a.denote V * b.denote V
  | max a b,     V => Max.max (a.denote V) (b.denote V)
  | safeRecip a, V => (Max.max 1 (a.denote V))⁻¹

/-- Syntactic size (`def:tf`). Certifies efficient computability of any feature we build:
a trader whose coefficients have bounded `cost` is e.c. This is the structural node count.

Disclosed modeling note (`dd:fuel`): the *precise* unary charging that ties `cost` to a
polynomial runtime bound — in particular charging the price-feature day index `n` and the
sentence code length — is deferred to M2, where the exploiting-trader e.c. certification
first consumes `cost`. The structural measure here is a lower bound on that. -/
def cost : EF → ℕ
  | price _ _   => 1
  | const _     => 1
  | add a b     => a.cost + b.cost + 1
  | mul a b     => a.cost + b.cost + 1
  | max a b     => a.cost + b.cost + 1
  | safeRecip a => a.cost + 1

/-- Rank = the latest day the feature inspects (`def:valfeature`); `EF_n` = rank ≤ `n`.
`const` inspects nothing (rank `0`); a binary node takes the `max` of its children. -/
def rank : EF → ℕ
  | price _ n   => n
  | const _     => 0
  | add a b     => Nat.max a.rank b.rank
  | mul a b     => Nat.max a.rank b.rank
  | max a b     => Nat.max a.rank b.rank
  | safeRecip a => a.rank

/-! ### `denote` is a ring map on the nose (all `rfl`), packaged for `simp`. -/

@[simp] theorem denote_price (φ : Sentence) (n : ℕ) :
    (price φ n).denote = fun V => V n φ := rfl

@[simp] theorem denote_const (q : ℚ) :
    (const q).denote = fun _ => (q : ℝ) := rfl

@[simp] theorem denote_add (a b : EF) : (add a b).denote = a.denote + b.denote := by
  funext V; simp [denote, Pi.add_apply]

@[simp] theorem denote_mul (a b : EF) : (mul a b).denote = a.denote * b.denote := by
  funext V; simp [denote, Pi.mul_apply]

@[simp] theorem denote_max (a b : EF) (V : History) :
    (max a b).denote V = Max.max (a.denote V) (b.denote V) := rfl

@[simp] theorem denote_safeRecip (a : EF) (V : History) :
    (safeRecip a).denote V = (Max.max 1 (a.denote V))⁻¹ := rfl

/-! ### Continuity (`def:tf`).  Discharged for the whole DSL rather than left as a
constraint — this is what breaks the price/trade circularity the paper needs for Brouwer.
Safe reciprocation is the only nontrivial case: `max 1 x ≥ 1 > 0`, so the reciprocal is
continuous with no removable singularity. -/

theorem continuous_denote (e : EF) : Continuous e.denote := by
  induction e with
  | price φ n => exact (continuous_apply φ).comp (continuous_apply n)
  | const q => exact continuous_const
  | add a b ha hb => exact ha.add hb
  | mul a b ha hb => exact ha.mul hb
  | max a b ha hb => exact ha.max hb
  | safeRecip a ha =>
      refine (continuous_const.max ha).inv₀ (fun V => ?_)
      have : (1 : ℝ) ≤ Max.max 1 (a.denote V) := le_max_left _ _
      positivity

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
  zero_mem' := ⟨const 0, by simp [rank], by funext V; simp [denote]⟩
  one_mem' := ⟨const 1, by simp [rank], by funext V; simp [denote]⟩
  add_mem' := by
    rintro f g ⟨ef, hf, rfl⟩ ⟨eg, hg, rfl⟩
    exact ⟨add ef eg, Nat.max_le.mpr ⟨hf, hg⟩, by simp⟩
  mul_mem' := by
    rintro f g ⟨ef, hf, rfl⟩ ⟨eg, hg, rfl⟩
    exact ⟨mul ef eg, Nat.max_le.mpr ⟨hf, hg⟩, by simp⟩
  neg_mem' := by
    rintro f ⟨ef, hf, rfl⟩
    refine ⟨mul (const (-1)) ef, by simpa [rank] using hf, ?_⟩
    funext V; simp [denote]

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
  simp [exMaxDiff, rank]

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

end EF

end LogicalInduction
