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
import LogicalInduction.Framework.Computable
import LogicalInduction.Framework.Asymptotics
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace LogicalInduction

open Filter Topology

/-! ### Efficient family interfaces used by the M4 lifts

The paper's affine and Self-Trust theorems quantify over efficiently computable sequences.
An arbitrary Lean function `ℕ → Sentence` or `ℕ → LUV` is much broader: it can encode an
uncomputable diagonal that no legal trader can follow.  These interfaces expose exactly the
compact codes consumed by the token-emission model. -/

/-- An efficiently codeable sequence of sentences. -/
def PolySentenceCodes (φ : ℕ → Sentence) : Prop :=
  ∃ c : Nat.Partrec.Code, PolyFueled c (fun n => Encodable.encode (φ n))

/-- An efficiently codeable sequence of rational constants. -/
def PolyRatCodes (q : ℕ → ℚ) : Prop :=
  ∃ c : Nat.Partrec.Code, PolyFueled c (fun n => Encodable.encode (q n))

/-- A rational sequence generated continuously from the market by a polynomial-size,
closed feature progression. This is the propositional/token-model rendering of the
paper's `def:pgen` for rational sequences. Closure is load-bearing: internal `EF.var`
nodes are legal only underneath the shared `letE` emitter and cannot be free inputs. -/
structure GeneratedRatFeature (P : History) (q : ℕ → ℚ)
    (feature : ℕ → EF) : Prop where
  rank_le : ∀ n, (feature n).rank ≤ n
  polyTok : PolyTokenStream (fun n => (feature n).serialize)
  closed : ∀ n ρ V, (feature n).denoteWith ρ V = (feature n).denote V
  denote : ∀ n, (feature n).denote P = (q n : ℝ)

def PGenerableRat (P : History) (q : ℕ → ℚ) : Prop :=
  ∃ feature : ℕ → EF, GeneratedRatFeature P q feature

/-- `def:luv` (abstracted). A `[0,1]`-logically-uncertain variable, presented by its
threshold sentences: `X.gt r = ⌜X > r⌝`. This is the LUV's entire observable content for a
market, which prices those sentences. -/
structure LUV where
  /-- The sentence `⌜X > r⌝`, for a rational threshold `r`. -/
  gt : ℚ → Sentence

namespace LUV

/-- A threshold presentation is **polynomially codeable** when the sentence code for
`X > i/n` is computable with polynomial fuel from `⟨n,i⟩`.  Paper LUVs are
Θ-definable, so this is the propositional interface corresponding to their compact
syntactic presentation (`def:ec`, disclosed type-`(c)`). -/
def PolyThresholdCodes (X : LUV) : Prop :=
  ∃ c : Nat.Partrec.Code, PolyFueled c (fun m =>
    Encodable.encode (X.gt ((m.unpair.2 : ℚ) / (m.unpair.1 : ℚ))))

/-- A sequence of LUV presentations is polynomially codeable when `⌜X_n > i/k⌝` can be
emitted from `⟨n,⟨k,i⟩⟩`. This is the varying-LUV analogue of `PolyThresholdCodes` and is
the interface needed by the affine and Self-Trust traders. -/
def PolyThresholdCodeSeq (X : ℕ → LUV) : Prop :=
  ∃ c : Nat.Partrec.Code, PolyFueled c (fun m =>
    Encodable.encode ((X m.unpair.1).gt
      ((m.unpair.2.unpair.2 : ℚ) / (m.unpair.2.unpair.1 : ℚ))))

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

Proved in `Properties/ExpectationConvergence.lean` (`LUV.expect_converges`, Phase D2):
the bundle-hysteresis trader — `thm:con`'s state driven by the expectation feature,
trading the day-`n` threshold bundle, gated to absorb the `lem:conluvapprox` payout
error. The statement lives there (it needs the world-value linkage `hval` and daily
plausible worlds, on top of the price bounds). -/

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

/-! ### Relational expectation-family substrate

The definitions live here because expectation convergence consumes them. The M4 theorems
`thm:ei`, `thm:loe`, and `thm:expprovind` are proved in
`Properties/ExpectationAffine.lean`, after the affine machinery is available.
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

/-- The relational indicator hypotheses really assign the indicator its intended world value:
`1` in `φ`-worlds and `0` otherwise. This is the world-side input to the M4 LUV lift. -/
theorem LUV.IsIndicator.valuesAt {Y : LUV} {φ : Sentence} {DP : DeductiveProcess}
    (hY : Y.IsIndicator φ DP) {n : ℕ} {v : PCWorld}
    (hv : v.ConsistentWith (DP.D n)) : v.ValuesAt Y (v.payout φ) := by
  have hlink := hY n v hv
  by_cases hφ : v.Holds φ
  · rw [PCWorld.payout, if_pos hφ]
    refine ⟨by norm_num, by norm_num, fun r => ?_⟩
    obtain ⟨hneg, hmid, hhi⟩ := hlink r
    constructor
    · intro hr
      by_cases hr0 : (r : ℝ) < 0
      · exact hneg hr0
      · exact (hmid (le_of_not_gt hr0) hr).2 hφ
    · intro hr
      exact hhi (le_of_lt hr)
  · rw [PCWorld.payout, if_neg hφ]
    refine ⟨by norm_num, by norm_num, fun r => ?_⟩
    obtain ⟨hneg, hmid, hhi⟩ := hlink r
    constructor
    · exact hneg
    · intro hr
      by_cases hr1 : (r : ℝ) < 1
      · exact fun h => hφ ((hmid (le_of_lt hr) hr1).1 h)
      · exact hhi (le_of_not_gt hr1)

#print axioms LUV.IsIndicator.valuesAt

/-! The three expectation-family theorems are proved in
`Properties/ExpectationAffine.lean`, after the affine machinery is available.  Keeping
their relational LUV definitions here avoids an import cycle with expectation convergence. -/

end LogicalInduction
