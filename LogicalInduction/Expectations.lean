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

/-- **`lem:conluvapprox`, single-LUV form (D1)** (paper `main.tex` 4982): a world that
values `X` at `x` assesses the precision-`n` approximate expectation within `1/n` of `x`.

Counting argument: thresholds `i/n` strictly below `x` pay `1` (there are at least
`⌈nx⌉ ≥ nx` of them among `i < n`, since `x ≤ 1`), thresholds strictly above pay `0`
(so the payout sum is at most `⌊nx⌋ + 1 ≤ nx + 1` — only `i ≤ ⌊nx⌋` can pay), and the
one possible threshold *equal* to `x` is the `+1` slack. Hence
`x ≤ 𝔼ₙ ≤ x + 1/n` — one-sided, which `|·|` weakens. The combination (`b/n`) form for
affine LUV combinations waits for M4's affine layer. -/
theorem PCWorld.ValuesAt.expectApprox_near {v : PCWorld} {X : LUV} {x : ℝ}
    (hval : v.ValuesAt X x) {n : ℕ} (hn : 0 < n) :
    |X.expectApprox v.payout n - x| ≤ 1 / n := by
  obtain ⟨hx0, hx1, hthr⟩ := hval
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hcast : ∀ i : ℕ, (((i : ℚ) / (n : ℚ) : ℚ) : ℝ) = (i : ℝ) / (n : ℝ) := by
    intro i; push_cast; ring
  have hmem : ∀ i : ℕ, 0 ≤ v.payout (X.gt ((i : ℚ) / (n : ℚ)))
      ∧ v.payout (X.gt ((i : ℚ) / (n : ℚ))) ≤ 1 := by
    intro i; rw [PCWorld.payout]; split <;> norm_num
  have hone : ∀ i : ℕ, (i : ℝ) / n < x → v.payout (X.gt ((i : ℚ) / (n : ℚ))) = 1 := by
    intro i hi
    have h := (hthr ((i : ℚ) / (n : ℚ))).1 (by rw [hcast]; exact hi)
    rw [PCWorld.payout, if_pos h]
  have hzero : ∀ i : ℕ, x < (i : ℝ) / n → v.payout (X.gt ((i : ℚ) / (n : ℚ))) = 0 := by
    intro i hi
    have h := (hthr ((i : ℚ) / (n : ℚ))).2 (by rw [hcast]; exact hi)
    rw [PCWorld.payout, if_neg h]
  -- Lower bound: the first `min n ⌈nx⌉` thresholds all pay 1, and `min n ⌈nx⌉ ≥ nx`.
  have hsum_lo : (n : ℝ) * x
      ≤ ∑ i ∈ Finset.range n, v.payout (X.gt ((i : ℚ) / (n : ℚ))) := by
    calc (n : ℝ) * x ≤ (min n ⌈(n : ℝ) * x⌉₊ : ℕ) := by
          rcases le_total (⌈(n : ℝ) * x⌉₊) n with h | h
          · rw [min_eq_right h]
            exact_mod_cast Nat.le_ceil _
          · rw [min_eq_left h]
            nlinarith
      _ = ∑ i ∈ Finset.range (min n ⌈(n : ℝ) * x⌉₊),
            v.payout (X.gt ((i : ℚ) / (n : ℚ))) := by
          rw [Finset.sum_congr rfl (fun i hi => ?_), Finset.sum_const, Finset.card_range,
            nsmul_eq_mul, mul_one]
          rw [Finset.mem_range] at hi
          refine hone i ?_
          have hic : (i : ℝ) < (n : ℝ) * x :=
            Nat.lt_ceil.mp (lt_of_lt_of_le hi (min_le_right _ _))
          rw [div_lt_iff₀ hnR]
          linarith
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.mpr (min_le_left _ _)) (fun i _ _ => (hmem i).1)
  -- Upper bound: only thresholds with `i ≤ ⌊nx⌋` can pay, so the sum is `≤ ⌊nx⌋ + 1`.
  have hsum_hi : ∑ i ∈ Finset.range n, v.payout (X.gt ((i : ℚ) / (n : ℚ)))
      ≤ (n : ℝ) * x + 1 := by
    set c' := min n (⌊(n : ℝ) * x⌋₊ + 1) with hc'
    have hc'n : c' ≤ n := min_le_left _ _
    have hsplit := Finset.sum_range_add_sum_Ico
      (fun i => v.payout (X.gt ((i : ℚ) / (n : ℚ)))) hc'n
    have hpart1 : ∑ i ∈ Finset.range c', v.payout (X.gt ((i : ℚ) / (n : ℚ)))
        ≤ (c' : ℝ) := by
      calc ∑ i ∈ Finset.range c', v.payout (X.gt ((i : ℚ) / (n : ℚ)))
          ≤ ∑ _i ∈ Finset.range c', (1 : ℝ) :=
            Finset.sum_le_sum (fun i _ => (hmem i).2)
        _ = c' := by simp
    have hpart2 : ∑ i ∈ Finset.Ico c' n, v.payout (X.gt ((i : ℚ) / (n : ℚ))) = 0 := by
      refine Finset.sum_eq_zero (fun i hi => ?_)
      rw [Finset.mem_Ico] at hi
      obtain ⟨hi1, hi2⟩ := hi
      have hiM : ⌊(n : ℝ) * x⌋₊ + 1 ≤ i := by
        rcases le_total (⌊(n : ℝ) * x⌋₊ + 1) n with h | h
        · rwa [hc', min_eq_right h] at hi1
        · rw [hc', min_eq_left h] at hi1
          omega
      refine hzero i ?_
      have h1 : (n : ℝ) * x < (⌊(n : ℝ) * x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
      have h2 : ((⌊(n : ℝ) * x⌋₊ : ℝ) + 1) ≤ (i : ℝ) := by exact_mod_cast hiM
      rw [lt_div_iff₀ hnR]
      linarith
    have hc'M : (c' : ℝ) ≤ (⌊(n : ℝ) * x⌋₊ : ℝ) + 1 := by
      have h := min_le_right n (⌊(n : ℝ) * x⌋₊ + 1)
      exact_mod_cast h
    have hfl : ((⌊(n : ℝ) * x⌋₊ : ℝ)) ≤ (n : ℝ) * x :=
      Nat.floor_le (mul_nonneg hnR.le hx0)
    linarith
  -- Assemble: `x ≤ 𝔼 ≤ x + 1/n`.
  rw [LUV.expectApprox, abs_le]
  constructor
  · have hlo : x ≤ (n : ℝ)⁻¹
        * ∑ i ∈ Finset.range n, v.payout (X.gt ((i : ℚ) / (n : ℚ))) := by
      rw [le_inv_mul_iff₀ hnR]
      exact hsum_lo
    have h1n : (0 : ℝ) < 1 / n := by positivity
    linarith
  · have hhi : (n : ℝ)⁻¹
        * ∑ i ∈ Finset.range n, v.payout (X.gt ((i : ℚ) / (n : ℚ))) ≤ x + 1 / n := by
      rw [inv_mul_le_iff₀ hnR]
      calc ∑ i ∈ Finset.range n, v.payout (X.gt ((i : ℚ) / (n : ℚ)))
          ≤ (n : ℝ) * x + 1 := hsum_hi
        _ = (n : ℝ) * (x + 1 / n) := by field_simp
    linarith

#print axioms PCWorld.ValuesAt.expectApprox_near

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
