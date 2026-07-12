/-
# Part III — Expectations of LUVs (`def:luv`, `def:e`, the LUV bridge)

The deference / dose-response corpora run almost entirely on **expectations** `E^H_n(X)` of
logically uncertain variables — objects they treat as abstract `ℕ → ℝ` sequences. This file
makes that object *concrete*, which is what lets their expectation-level hypotheses be
discharged from our side (roadmap M3/M4 LUV bridge).

The unlock is the paper's `def:e`: the day-`n` expectation of a `[0,1]`-LUV `X` is a **finite
sum of the market's prices** on `X`'s threshold sentences,
`𝔼ₙ(X) = (1/n) · ∑_{i<n} Pₙ(⌜X > i/n⌝)`. So once a LUV is presented by its threshold
sentences, `𝔼ₙ(X)` is a genuine `ℕ → ℝ` derived from `P : History`.

Modeling note (`def:luv`, disclosed type-`(c)`): the paper's LUVs are *first-order* — a
formula `X(ν)` free in one variable, over a theory `Θ` that represents computations — whereas
our `Sentence = Formula ℕ` is propositional. We model a `[0,1]`-LUV faithfully **by its
observable content for the market**: the family of threshold sentences `X.gt r = ⌜X > r⌝ ∈
Sentence`. The paper's well-definedness (`Θ` proves a unique value) becomes monotonicity /
coherence conditions on that family; we carry only what a given theorem needs, as explicit
hypotheses, rather than reconstructing the first-order syntax.
-/
import LogicalInduction.Criterion
import LogicalInduction.Asymptotics
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace LogicalInduction

open Filter Topology

/-- `def:luv` (abstracted). A `[0,1]`-logically-uncertain variable, presented by its
threshold sentences: `X.gt r = ⌜X > r⌝`. This is the LUV's entire observable content for a
market, which prices those sentences. -/
structure LUV where
  /-- The sentence `⌜X > r⌝`, for a rational threshold `r`. -/
  gt : ℚ → Sentence

namespace LUV

/-- `def:e`. The **approximate expectation** of `X` under a valuation `V` at precision `k`:
`𝔼_k^V(X) = ∑_{i<k} (1/k) · V(⌜X > i/k⌝)`. Lands in `[0,1]` when `V` does (a share is worth
at most 1), so expectations of `[0,1]`-LUVs are themselves `[0,1]`-valued. -/
noncomputable def expectApprox (V : Valuation) (k : ℕ) (X : LUV) : ℝ :=
  (k : ℝ)⁻¹ * ∑ i ∈ Finset.range k, V (X.gt ((i : ℚ) / (k : ℚ)))

/-- `𝔼ₙ := 𝔼_n^{Pₙ}` — the day-`n` expectation, precision tied to the day (`def:e`). -/
noncomputable def expect (P : History) (n : ℕ) (X : LUV) : ℝ :=
  X.expectApprox (P n) n

/-- The **expectation sequence** `n ↦ 𝔼ₙ(X)`. This is the concrete object the deference
corpus abstracts as `E^H_n(X) : ℕ → ℝ`; a hypothesis `Approx (E_now X) (E_now Y)` there is
`expectSeq P X ≈ₙ expectSeq P Y` here. -/
noncomputable def expectSeq (P : History) (X : LUV) : ℕ → ℝ := fun n => X.expect P n

/-! ### Basic bounds — `𝔼` inherits `[0,1]` from the prices. -/

theorem expectApprox_nonneg (V : Valuation) (k : ℕ) (X : LUV)
    (hV : ∀ s, 0 ≤ V s) : 0 ≤ X.expectApprox V k := by
  refine mul_nonneg (by positivity) (Finset.sum_nonneg (fun i _ => hV _))

theorem expectApprox_le_one (V : Valuation) (k : ℕ) (X : LUV)
    (hV : ∀ s, V s ≤ 1) : X.expectApprox V k ≤ 1 := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · simp [expectApprox, hk]
  · have hsum : ∑ i ∈ Finset.range k, V (X.gt ((i : ℚ) / (k : ℚ))) ≤ (k : ℝ) := by
      calc ∑ i ∈ Finset.range k, V (X.gt ((i : ℚ) / (k : ℚ)))
          ≤ ∑ _i ∈ Finset.range k, (1 : ℝ) := Finset.sum_le_sum (fun i _ => hV _)
        _ = k := by simp
    rw [expectApprox, inv_mul_le_iff₀ (by exact_mod_cast hk)]
    simpa using hsum

theorem expect_mem_Icc (P : History) (n : ℕ) (X : LUV)
    (hP : ∀ s, 0 ≤ P n s ∧ P n s ≤ 1) : 0 ≤ X.expect P n ∧ X.expect P n ≤ 1 :=
  ⟨X.expectApprox_nonneg (P n) n (fun s => (hP s).1),
   X.expectApprox_le_one (P n) n (fun s => (hP s).2)⟩

/-! ### `thm:ec` — Expectations Converge.

The day-`n` expectation of any `[0,1]`-LUV converges. Stated conditionally on a logical
inductor. **Proof deferred**: it is a genuine property-tail theorem (`app:ec`) — it needs
per-threshold price convergence (`thm:con`) plus control of the moving precision, which
routes through the trader machinery not yet built for moving-threshold sequences. Ledgered
as `sorry`. -/
theorem expect_converges (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (X : LUV) (hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1) :
    ∃ L : ℝ, ConvergesTo (X.expectSeq P) L := by
  sorry

/-- `𝔼_∞(X)` — the limiting expectation (`thm:ec`), extracted from `expect_converges`. -/
noncomputable def expectInf (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (X : LUV) (hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1) : ℝ :=
  (X.expect_converges P DP hP).choose

end LUV

/-! ### World-side LUV values (`lem:conluvapprox` substrate, D1 modeling)

The paper's "`Θ` represents computations, so every consistent world assigns each LUV its
true value" becomes, in our threshold presentation, a coherence condition relating a world
to a value: `v` affirms every threshold strictly below `x` and denies every one strictly
above. **Disclosed type-`(c)`**: this is the market-observable content of "`v` believes
`X = x`", not a first-order reconstruction. -/

/-- The p.c. world `v` **values** the `[0,1]`-LUV `X` at `x`: threshold coherence around
`x`. -/
def PCWorld.ValuesAt (v : PCWorld) (X : LUV) (x : ℝ) : Prop :=
  0 ≤ x ∧ x ≤ 1 ∧
    ∀ r : ℚ, ((r : ℝ) < x → v.Holds (X.gt r)) ∧ (x < (r : ℝ) → ¬ v.Holds (X.gt r))

/-! ### The expectation family — statements (proofs → M4, per the G1 decision)

`thm:ei`, `thm:loe`, `thm:expprovind` are stated here faithfully and left `sorry`: their
proofs ride the affine lift hubs (`thm:affpolymax` etc.), which the roadmap places in M4.
**General principle (D3):** paper-side LUV *constructions* — indicators, affine
combinations — enter our modeling as **relational predicates over arbitrary threshold
families**, never as canonical `LUV` values. Constructing a representative (e.g. defining
the indicator of `φ` as `gt r := φ` on `[0,1)`) would make the theorem *definitional* —
the collapse is a modeling artifact, since the paper's thresholds are distinct sentences
provably linked to `φ`, and the theorem's content is the inductor learning that growing
bundle of equivalences uniformly. -/

/-- `Y` is an **indicator family for `φ`** (relational rendering of the paper's `1(φ)`):
in every plausible world, `Y`'s thresholds below `0` hold, thresholds in `[0,1)` are
equivalent to `φ`, and thresholds at `≥ 1` fail. -/
def LUV.IsIndicator (Y : LUV) (φ : Sentence) (DP : DeductiveProcess) : Prop :=
  ∀ n (v : PCWorld), v.ConsistentWith (DP.D n) → ∀ r : ℚ,
    ((r : ℝ) < 0 → v.Holds (Y.gt r)) ∧
    (0 ≤ (r : ℝ) → (r : ℝ) < 1 → (v.Holds (Y.gt r) ↔ v.Holds φ)) ∧
    (1 ≤ (r : ℝ) → ¬ v.Holds (Y.gt r))

/-- **Expectations of indicators** (`thm:ei`): `𝔼ₙ(1(φ)) ≈ₙ Pₙ(φ)` for any indicator
family for `φ`. Note per-threshold `thm:lex` does *not* suffice — the threshold set grows
with `n`, so the exploiter is a bundle trader (the D2/hysteresis shape). -/
theorem lic_expectation_indicator (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (φ : Sentence) (Y : LUV) (hY : Y.IsIndicator φ DP) :
    AsympEq (Y.expectSeq P) (fun n => P n φ) := by
  -- TODO(blueprint:thm:ei): proof in M4 (bundle trader, D2's engine).
  sorry

/-- **Linearity of expectation** (`thm:loe`, fixed `X, Y, Z` form): if every plausible
world values `Z` as the affine combination `a·X + b·Y`, the expectations combine the same
way in the limit. (The `𝓔𝓒`-sequence form is the M4 target.) -/
theorem lic_linearity_of_expectation (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (a b : ℚ) (X Y Z : LUV)
    (hlin : ∀ n (v : PCWorld), v.ConsistentWith (DP.D n) → ∀ x y z,
      v.ValuesAt X x → v.ValuesAt Y y → v.ValuesAt Z z → z = a * x + b * y) :
    AsympEq (fun n => (a : ℝ) * X.expect P n + (b : ℝ) * Y.expect P n)
      (Z.expectSeq P) := by
  -- TODO(blueprint:thm:loe): proof in M4 (affine machinery, thm:affpolymax).
  sorry

/-- **Expectation provability induction** (`thm:expprovind`, single-LUV form): if every
plausible world values `X` at least `c`, the expectation is eventually at least `c − ε`. -/
theorem lic_expectation_provind (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (X : LUV) (c : ℝ)
    (hval : ∀ n (v : PCWorld), v.ConsistentWith (DP.D n) → ∃ x, c ≤ x ∧ v.ValuesAt X x) :
    AsympGE (X.expectSeq P) (fun _ => c) := by
  -- TODO(blueprint:thm:expprovind): proof in M4 (affine machinery).
  sorry

end LogicalInduction
