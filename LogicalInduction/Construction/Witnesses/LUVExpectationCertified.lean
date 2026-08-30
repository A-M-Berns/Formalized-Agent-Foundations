import LogicalInduction.Construction.Witnesses.FeedbackTruth
import LogicalInduction.Construction.Witnesses.LUVDeductiveProcess
import LogicalInduction.Construction.Witnesses.LUVSyntax
import LogicalInduction.Properties.ExpectationAffine

/-!
# Certified expectation endpoints for arithmetically presented LUVs

The paper's LUV expectation theorems (`thm:expprovind`, `thm:loe`, `thm:expcoh`,
`thm:perexpkno`, `thm:exppolymax`, `thm:wubexp`) are stated in `Properties.ExpectationAffine`
against a finite-precision world hypothesis: every world consistent with the day-`n` deductive
stage values the LUV within `1/n` of a fixed real.  This file discharges that hypothesis for a
`ComputableLUV`, whose values are explicit rationals `numᵢ/denᵢ`, so that the endpoints below
carry no world-value premise.

The mechanism is the scheduled-reveal deductive process `gridDP`: stage `n` contains, for every
LUV index `i ≤ n` and grid point `j/m` with `m ≤ n + 1` and `j < m`, the threshold literal in
whichever polarity `Θ` decides.  A world consistent with that stage therefore reads back the whole
grid, and `expectApprox_near_ofGrid` pins its day-`n` expectation within `1/n` of `numᵢ/denᵢ`
uniformly over consistent worlds — uniformity being what the trader argument consumes.

The endpoints then come in two strengths.  The `_arith` forms assume a logical inductor over
`gridDP` and the threshold-code efficiency certificate; the `_unconditional` forms discharge both
(`gridDP` is proved computable here, the threshold codes are poly-fueled) and run over the
constructed inductor `liaHistory gridDP`, leaving the rational hypothesis on `numᵢ/denᵢ` as the
sole premise.
-/

namespace LogicalInduction

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment Filter Topology

/-- **Combination-level expectation provability induction, `≤` form, at the paper's premise.**

This is `thm:expprovind` as stated at tex:1753-1760: only the *one-sided* world bound is
assumed — every `W ∈ cworlds(Θ)` values `Aₙ` at most `c`, and different completed worlds are
free to disagree.  `hwv` is the paper's own representation premise (each completed world
assigns *some* coherent value to every LUV of `Aₙ`, which the paper's `sup` definition of
`W(X)` supplies by construction); it is what produces the valuation `ν` the bound is stated
against.  No `def:affthmval` determinacy is required — contrast
`lic_expect_combination_provind_le_ofDetermined`, which assumes it and is a corollary of this.

Proof kind `C`; hypotheses `(a)` throughout — the diagonal mesh of `⟨A⟩` is a polynomial
affine sequence whose completed-theory values sit within `shareNorm · (1/n)` of the LUV
values, so the paper's affine provability induction `thm:affprovind` applies with vanishing
slack.
Paper node: `thm:expprovind` -/
theorem lic_expect_combination_provind_le
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    (h : LUVCombination.BoundedSequence As P)
    (hwv : LUVCombination.WorldValued As DP)
    (c : ℝ)
    (hval : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      ∀ ν, (As n).ValuesAt v ν → (As n).value P ν ≤ c)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (As n).expect P n) ≲ₙ (fun _ => c) := by
  have hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1 :=
    fun n φ => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n φ
  obtain ⟨B, hB⟩ := h.bounded
  obtain ⟨b, hbB⟩ := exists_rat_gt (max B 0)
  have hshare : ∀ n, (As n).shareNorm P ≤ (b : ℝ) := fun n => by
    have h1 : (As n).shareNorm P ≤ (As n).l1Norm P :=
      le_add_of_nonneg_left (abs_nonneg _)
    exact h1.trans ((hB n).trans ((le_max_left B 0).trans hbB.le))
  have hbounded : BoundedAffinePrices (fun n => (As n).meshAffine (n + 1)) P :=
    ⟨max B 0, le_max_right _ _, fun n m =>
      le_trans (le_trans ((((As n).meshAffine (n + 1)).abs_price_le_l1Norm P m
        (fun φ => hP m φ)).trans
        ((As n).meshAffine_l1Norm_le P (n + 1))) (hB n)) (le_max_left _ _)⟩
  have hmag : ∃ C : ℝ, ∀ n, ((As n).meshAffine (n + 1)).magnitude P ≤ C :=
    ⟨(b : ℝ), fun n =>
      ((As n).meshAffine_magnitude_le_shareNorm P (n + 1)).trans (hshare n)⟩
  have hmesh : ∀ ε > 0, ∀ᶠ n in atTop, ∀ v : PCWorld, v.ConsistentWithTheory DP →
      ((As n).meshAffine (n + 1)).value P v.payout ≤ c + ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt ((b : ℝ) / ε)
    filter_upwards [Filter.eventually_ge_atTop (max 1 N)] with n hn v hv
    have hn0 : 0 < n := by omega
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
    obtain ⟨ν, hν⟩ := hwv n v hv
    have hvalue : (As n).value P ν ≤ c := hval n v hv ν hν
    have hnear : |((As n).meshAffine (n + 1)).value P v.payout -
        (As n).value P ν| ≤ (As n).shareNorm P * (1 / (n : ℝ)) := by
      have hstep : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / (n : ℝ) :=
        one_div_le_one_div_of_le hnR (by linarith)
      refine LE.le.trans ?_ (mul_le_mul_of_nonneg_left hstep ((As n).shareNorm_nonneg P))
      simpa using (As n).meshAffine_value_near (k := n + 1) P v ν n.succ_pos hν
    rw [abs_le] at hnear
    have hbound : (As n).shareNorm P * (1 / n) ≤ (b : ℝ) * (1 / n) :=
      mul_le_mul_of_nonneg_right (hshare n) (by positivity)
    have hsmall : (b : ℝ) * (1 / n) ≤ ε := by
      rw [mul_one_div, div_le_iff₀ hnR]
      nlinarith [(div_lt_iff₀ hε).mp (hN.trans_le
        (show ((N : ℕ) : ℝ) ≤ n by exact_mod_cast le_trans (le_max_right 1 N) hn))]
    linarith [hnear.2, hbound, hsmall, hvalue]
  simpa only [LUVCombination.meshAffine_price_diagonal] using
    (h.poly.mesh_poly).affine_provind_theory_le_const P DP hbounded hmag hworld c hmesh

/-- **Combination-level expectation provability induction, `≥` form, at the paper's premise.**
The `≥` dual of `lic_expect_combination_provind_le`: only a one-sided lower bound
over `cworlds(Θ)` is assumed.  Proof kind `C`; hypotheses `(a)`.
Paper node: `thm:expprovind` -/
theorem lic_expect_combination_provind_ge
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    (h : LUVCombination.BoundedSequence As P)
    (hwv : LUVCombination.WorldValued As DP)
    (c : ℝ)
    (hval : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      ∀ ν, (As n).ValuesAt v ν → c ≤ (As n).value P ν)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (As n).expect P n) ≳ₙ (fun _ => c) := by
  have hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1 :=
    fun n φ => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n φ
  obtain ⟨B, hB⟩ := h.bounded
  obtain ⟨b, hbB⟩ := exists_rat_gt (max B 0)
  have hshare : ∀ n, (As n).shareNorm P ≤ (b : ℝ) := fun n => by
    have h1 : (As n).shareNorm P ≤ (As n).l1Norm P :=
      le_add_of_nonneg_left (abs_nonneg _)
    exact h1.trans ((hB n).trans ((le_max_left B 0).trans hbB.le))
  have hbounded : BoundedAffinePrices (fun n => (As n).meshAffine (n + 1)) P :=
    ⟨max B 0, le_max_right _ _, fun n m =>
      le_trans (le_trans ((((As n).meshAffine (n + 1)).abs_price_le_l1Norm P m
        (fun φ => hP m φ)).trans
        ((As n).meshAffine_l1Norm_le P (n + 1))) (hB n)) (le_max_left _ _)⟩
  have hmag : ∃ C : ℝ, ∀ n, ((As n).meshAffine (n + 1)).magnitude P ≤ C :=
    ⟨(b : ℝ), fun n =>
      ((As n).meshAffine_magnitude_le_shareNorm P (n + 1)).trans (hshare n)⟩
  have hmesh : ∀ ε > 0, ∀ᶠ n in atTop, ∀ v : PCWorld, v.ConsistentWithTheory DP →
      c - ε ≤ ((As n).meshAffine (n + 1)).value P v.payout := by
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt ((b : ℝ) / ε)
    filter_upwards [Filter.eventually_ge_atTop (max 1 N)] with n hn v hv
    have hn0 : 0 < n := by omega
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
    obtain ⟨ν, hν⟩ := hwv n v hv
    have hvalue : c ≤ (As n).value P ν := hval n v hv ν hν
    have hnear : |((As n).meshAffine (n + 1)).value P v.payout -
        (As n).value P ν| ≤ (As n).shareNorm P * (1 / (n : ℝ)) := by
      have hstep : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / (n : ℝ) :=
        one_div_le_one_div_of_le hnR (by linarith)
      refine LE.le.trans ?_ (mul_le_mul_of_nonneg_left hstep ((As n).shareNorm_nonneg P))
      simpa using (As n).meshAffine_value_near (k := n + 1) P v ν n.succ_pos hν
    rw [abs_le] at hnear
    have hbound : (As n).shareNorm P * (1 / n) ≤ (b : ℝ) * (1 / n) :=
      mul_le_mul_of_nonneg_right (hshare n) (by positivity)
    have hsmall : (b : ℝ) * (1 / n) ≤ ε := by
      rw [mul_one_div, div_le_iff₀ hnR]
      nlinarith [(div_lt_iff₀ hε).mp (hN.trans_le
        (show ((N : ℕ) : ℝ) ≤ n by exact_mod_cast le_trans (le_max_right 1 N) hn))]
    linarith [hnear.1, hbound, hsmall, hvalue]
  simpa only [LUVCombination.meshAffine_price_diagonal] using
    (h.poly.mesh_poly).affine_provind_theory_ge_const P DP hbounded hmag hworld c hmesh

/-- **Combination-level expectation provability induction, `=` form, at the paper's premise.**
Two-sided world bound, from the two one-sided forms; worlds may still disagree with each other
only up to the two bounds coinciding.  Proof kind `C`; hypotheses `(a)`.
Paper node: `thm:expprovind` -/
theorem lic_expect_combination_provind_eq
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    (h : LUVCombination.BoundedSequence As P)
    (hwv : LUVCombination.WorldValued As DP)
    (c : ℝ)
    (hval : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      ∀ ν, (As n).ValuesAt v ν → (As n).value P ν = c)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (As n).expect P n) ≈ₙ (fun _ => c) := by
  rw [asympEq_iff_asympLE_asympGE]
  exact ⟨lic_expect_combination_provind_le h hwv c
      (fun n v hv ν hν => (hval n v hv ν hν).le) hworld,
    lic_expect_combination_provind_ge h hwv c
      (fun n v hv ν hν => (hval n v hv ν hν).ge) hworld⟩

/-- **Combination-level expectation provability induction, `≤` form.**  A bounded LUV-combination
sequence whose completed-theory value stays `≤ c` has diagonal expectation `≲ₙ c`.

The representation premises are the paper's own: `hwv` says each completed world assigns *some*
coherent value to every LUV of `Aₙ` (which for `W ∈ cworlds(Θ)` the paper's `sup` definition of
`W(X)` supplies by construction), and `hdet` is `def:affthmval` — the *combination* takes the
same value `truth n` in every completed world.  Neither demands a canonical per-LUV value fixed
independently of the world.

This determinacy form is what `thm:recurringunbiasednessexp` / `thm:wubexp` / `thm:prandexp`
consume, where `def:affthmval` *is* the paper's premise.  `thm:expprovind` itself needs only the
one-sided world bound; see `lic_expect_combination_provind_le`, of which this is a
one-line corollary.
Paper node: `thm:expprovind` -/
theorem lic_expect_combination_provind_le_ofDetermined
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    (h : LUVCombination.BoundedSequence As P)
    (hwv : LUVCombination.WorldValued As DP)
    {truth : ℕ → ℝ} (hdet0 : LUVCombination.DeterminedViaTheory As P DP truth)
    (c : ℝ) (hdet : ∀ n, truth n ≤ c)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (As n).expect P n) ≲ₙ (fun _ => c) :=
  lic_expect_combination_provind_le h hwv c
    (fun n v hv ν hν => (hdet0 n v ν hv hν).trans_le (hdet n)) hworld

/-- **Combination-level expectation provability induction, `≥` form.**  The `def:affthmval`
determinacy form, consumed by `thm:recurringunbiasednessexp` / `thm:wubexp` / `thm:prandexp`;
a one-line corollary of `lic_expect_combination_provind_ge`, which carries
`thm:expprovind` at the paper's weaker one-sided world bound.
Paper node: `thm:expprovind` -/
theorem lic_expect_combination_provind_ge_ofDetermined
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    (h : LUVCombination.BoundedSequence As P)
    (hwv : LUVCombination.WorldValued As DP)
    {truth : ℕ → ℝ} (hdet0 : LUVCombination.DeterminedViaTheory As P DP truth)
    (c : ℝ) (hdet : ∀ n, c ≤ truth n)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (As n).expect P n) ≳ₙ (fun _ => c) :=
  lic_expect_combination_provind_ge h hwv c
    (fun n v hv ν hν => (hdet n).trans (hdet0 n v ν hv hν).ge) hworld

/-- **Combination-level expectation provability induction, `=` form.**  The `def:affthmval`
determinacy form; `lic_expect_combination_provind_eq` carries `thm:expprovind` at
the paper's weaker two-sided world bound.
Paper node: `thm:expprovind` -/
theorem lic_expect_combination_provind_eq_ofDetermined
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    (h : LUVCombination.BoundedSequence As P)
    (hwv : LUVCombination.WorldValued As DP)
    {truth : ℕ → ℝ} (hdet0 : LUVCombination.DeterminedViaTheory As P DP truth)
    (c : ℝ) (hdet : ∀ n, truth n = c)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (As n).expect P n) ≈ₙ (fun _ => c) := by
  rw [asympEq_iff_asympLE_asympGE]
  exact ⟨lic_expect_combination_provind_le_ofDetermined h hwv hdet0 c (fun n => (hdet n).le) hworld,
    lic_expect_combination_provind_ge_ofDetermined h hwv hdet0 c (fun n => (hdet n).ge) hworld⟩

/-- **Combination-level expectation provability induction, `= 0` form** (`thm:loe` substrate).
The paper's own route to linearity (`app:loe`): apply `thm:expprovind` to the combination
`aX+bY−Z`, valued `0` because `Θ ⊢ Z = aX+bY`.
Paper node: `thm:loe` -/
theorem lic_expect_combination_provind_zero
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    (h : LUVCombination.BoundedSequence As P)
    (hwv : LUVCombination.WorldValued As DP)
    (hdet0 : LUVCombination.DeterminedViaTheory As P DP (fun _ => 0))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (As n).expect P n) ≈ₙ (fun _ => 0) :=
  lic_expect_combination_provind_eq_ofDetermined h hwv hdet0 0 (fun _ => rfl) hworld

/-- The paper's linearity LUV-combination `aₙXₙ + bₙYₙ − Zₙ`. -/
def linearityLUVComb (a b : ℕ → ℚ) (X Y Z : ℕ → LUV) (n : ℕ) : LUVCombination where
  const := .const 0
  terms := [(.const (a n), X n), (.const (b n), Y n), (.const (-1), Z n)]

lemma linearityLUVComb_expect (a b : ℕ → ℚ) (X Y Z : ℕ → LUV) (P : History) (n : ℕ) :
    (linearityLUVComb a b X Y Z n).expect P n
      = (a n : ℝ) * (X n).expect P n + (b n : ℝ) * (Y n).expect P n - (Z n).expect P n := by
  simp only [linearityLUVComb, LUVCombination.expect, LUVCombination.expectAt, LUV.expect,
    EF.denote_const, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast; ring

/-- **Linearity of Expectation** (`thm:loe`), the paper's varying-sequence statement.  For
efficiently generated bounded rational sequences `a, b` and ec sequences of `[0,1]`-LUVs `X, Y, Z`
with `Θ ⊢ Zₙ = aₙXₙ + bₙYₙ` (encoded as the combination being valued `0`), the diagonal
expectations are asymptotically linear.  Derived, as in the paper's own proof (`app:loe`), from
`thm:expprovind` for the LUV-combination `aX+bY−Z`.  Efficiency (`BoundedSequence`) and
representation (`WorldValued`, discharged from compact syntax in `LUVSyntax.lean` and from
arithmetic in `LUVPresentation.lean`) enter as the disclosed hypotheses; `hdet0` is the paper's
`Θ ⊢ Zₙ = aₙXₙ + bₙYₙ` in the determined-value form of `def:affthmval`.
Paper node: `thm:loe` -/
theorem lic_linearity_of_expectation_seq
    {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    (a b : ℕ → ℚ) (X Y Z : ℕ → LUV)
    (h : LUVCombination.BoundedSequence (linearityLUVComb a b X Y Z) P)
    (hwv : LUVCombination.WorldValued (linearityLUVComb a b X Y Z) DP)
    (hdet0 : LUVCombination.DeterminedViaTheory
      (linearityLUVComb a b X Y Z) P DP (fun _ => 0))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    AsympEq (fun n => (a n : ℝ) * (X n).expect P n + (b n : ℝ) * (Y n).expect P n)
      (fun n => (Z n).expect P n) := by
  have hzero := lic_expect_combination_provind_zero h hwv hdet0 hworld
  unfold AsympEq at hzero ⊢
  have hfun : (fun n => (a n : ℝ) * (X n).expect P n + (b n : ℝ) * (Y n).expect P n
      - (Z n).expect P n)
      = (fun n => (linearityLUVComb a b X Y Z n).expect P n - 0) := by
    funext n; rw [linearityLUVComb_expect]; ring
  rw [hfun]; exact hzero

namespace ComputableLUV

variable (L : ComputableLUV)

/-- The `Θ`-decided threshold literal for `Xᵢ` at grid point `j/m`: the positive atom if the
value exceeds `j/m`, its refutation otherwise. -/
noncomputable def gridLiteral (i j m : ℕ) : Sentence :=
  if L.ThresholdPred (thresholdCode i ((j : ℚ) / (m : ℚ)))
  then thresholdSentence i ((j : ℚ) / (m : ℚ))
  else ∼ thresholdSentence i ((j : ℚ) / (m : ℚ))

/-- Scheduled-reveal stage: all grid literals for indices up to `n` and precisions up to
day `n`'s own grid `n + 1`. -/
noncomputable def gridStage (n : ℕ) : Finset Sentence :=
  (Finset.range (n + 1)).biUnion (fun i =>
    (Finset.range (n + 2)).biUnion (fun m =>
      (Finset.range m).image (fun j => L.gridLiteral i j m)))

lemma mem_gridStage {φ : Sentence} {n : ℕ} :
    φ ∈ L.gridStage n ↔ ∃ i m j, i ≤ n ∧ m ≤ n + 1 ∧ j < m ∧ φ = L.gridLiteral i j m := by
  simp only [gridStage, Finset.mem_biUnion, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨i, hi, m, hm, j, hj, rfl⟩; exact ⟨i, m, j, by omega, by omega, hj, rfl⟩
  · rintro ⟨i, m, j, hi, hm, hj, rfl⟩; exact ⟨i, by omega, m, by omega, j, hj, rfl⟩

lemma gridStage_mono (n : ℕ) : L.gridStage n ⊆ L.gridStage (n + 1) := by
  intro φ hφ
  rw [mem_gridStage] at hφ ⊢
  obtain ⟨i, m, j, hi, hm, hj, rfl⟩ := hφ
  exact ⟨i, m, j, by omega, by omega, hj, rfl⟩

/-- The scheduled-reveal deductive process for the LUV family. -/
noncomputable def gridDP : DeductiveProcess where
  D := L.gridStage
  mono := L.gridStage_mono

attribute [local irreducible] Nat.sqrt in
/-- The standard-truth world is consistent with every scheduled stage.  The scheduled
process publishes literals by actual threshold truth, so this is the truth world, not the
provability world `luvWorld` that the full enumerator `luvThresholdDP` uses. -/
lemma truthWorld_consistent_gridStage (n : ℕ) :
    (L.truthWorld).ConsistentWith ((L.gridDP).D n) := by
  intro φ hφ
  rw [show (L.gridDP).D n = L.gridStage n from rfl, mem_gridStage] at hφ
  obtain ⟨i, m, j, _, _, _, rfl⟩ := hφ
  unfold gridLiteral
  by_cases hp : L.ThresholdPred (thresholdCode i ((j : ℚ) / (m : ℚ)))
  · rw [if_pos hp]; exact hp
  · rw [if_neg hp, holds_not]; exact hp

/-- `hcons` for the scheduled process. -/
lemma gridDP_hcons (n : ℕ) : ∃ v : PCWorld, v.ConsistentWith ((L.gridDP).D n) :=
  ⟨L.truthWorld, L.truthWorld_consistent_gridStage n⟩

attribute [local irreducible] Nat.sqrt in
/-- **Grid coherence from stage membership.**  A world consistent with stage `m` reads each grid
literal's polarity for every index `i ≤ m` and precision `n ≤ m`, so `⌜Xᵢ > j/n⌝` holds exactly
when the threshold predicate does. -/
lemma holds_thresholdSentence_iff {v : PCWorld} {m n : ℕ}
    (hv : v.ConsistentWith ((L.gridDP).D m)) {i j : ℕ} (hi : i ≤ m) (hnm : n ≤ m + 1)
    (hj : j < n) :
    v.Holds (thresholdSentence i ((j : ℚ) / (n : ℚ)))
      ↔ L.ThresholdPred (thresholdCode i ((j : ℚ) / (n : ℚ))) := by
  have hmem : L.gridLiteral i j n ∈ (L.gridDP).D m := by
    rw [show (L.gridDP).D m = L.gridStage m from rfl, mem_gridStage]
    exact ⟨i, n, j, hi, hnm, hj, rfl⟩
  have hholds : v.Holds (L.gridLiteral i j n) := hv _ hmem
  unfold gridLiteral at hholds
  by_cases hp : L.ThresholdPred (thresholdCode i ((j : ℚ) / (n : ℚ)))
  · rw [if_pos hp] at hholds
    exact ⟨fun _ => hp, fun _ => hholds⟩
  · rw [if_neg hp, holds_not] at hholds
    exact ⟨fun h => absurd h hholds, fun h => absurd h hp⟩

/-- **The value-agreement discharge.**  For a world consistent with scheduled stage `m`, any LUV
index `i ≤ m`, and any precision `0 < n ≤ m + 1` (in particular stage `m`'s own grid `m + 1`),
the precision-`n` approximate expectation of `Xᵢ` is within `1/n` of its standard rational value —
with no world-value hypothesis. -/
lemma expectApprox_near_gridDP {v : PCWorld} {m n : ℕ} (hn : 0 < n)
    (hv : v.ConsistentWith ((L.gridDP).D m)) {i : ℕ} (hi : i ≤ m) (hnm : n ≤ m + 1) :
    |(toLUV i).expectApprox v.payout n - (L.value i : ℝ)| ≤ 1 / n := by
  refine PCWorld.expectApprox_near_ofGrid (by exact_mod_cast L.value_nonneg i)
    (by exact_mod_cast L.value_le_one i) hn (fun j hj => ?_)
  have hiff := L.holds_thresholdSentence_iff hv hi hnm hj
  have hpred := L.thresholdPred_code_iff i ((j : ℚ) / (n : ℚ))
  have hc : (((j : ℚ) / (n : ℚ) : ℚ) : ℝ) = (j : ℝ) / (n : ℝ) := by push_cast; ring
  rw [toLUV_gt]
  refine ⟨fun hlt => ?_, fun hlt hHolds => ?_⟩
  · rw [hiff, hpred]; exact_mod_cast (hc.symm ▸ hlt)
  · rw [hiff, hpred] at hHolds
    have : (((j : ℚ) / (n : ℚ) : ℚ) : ℝ) < (L.value i : ℝ) := by exact_mod_cast hHolds
    rw [hc] at this
    exact absurd this (not_lt.mpr (le_of_lt hlt))

/-- **Certified expectation provability induction.**  Provability induction for a `dd:luv-arith`
LUV, with the world-value hypothesis discharged from arithmetic: it follows from the plain
rational bound `c ≤ numᵢ/denᵢ`.  The remaining premises are the disclosed boundaries — the
threshold-code efficiency certificate and a logical inductor over the scheduled process.
Paper node: `thm:expprovind` -/
theorem lic_expectation_provind_arith (P : History) [IsLogicalInductor P (L.gridDP)]
    (i : ℕ) (hcode : (toLUV i).RpnThresholdCodes)
    (c : ℝ) (hc : c ≤ (L.value i : ℝ)) :
    AsympGE ((toLUV i).expectSeq P) (fun _ => c) :=
  lic_expectation_provind P (L.gridDP) (toLUV i) hcode L.gridDP_hcons c
    ((Filter.eventually_ge_atTop (max 1 i)).mono (fun n hin v hv =>
      ⟨(L.value i : ℝ), hc,
        (by simpa using L.expectApprox_near_gridDP (n := n + 1) (by omega) hv (by omega) (by omega))⟩))

/-- Certified expectation provability induction, upper (`≤`) form.
Paper node: `thm:expprovind` -/
theorem lic_expectation_provind_le_arith (P : History) [IsLogicalInductor P (L.gridDP)]
    (i : ℕ) (hcode : (toLUV i).RpnThresholdCodes)
    (c : ℝ) (hc : (L.value i : ℝ) ≤ c) :
    AsympLE ((toLUV i).expectSeq P) (fun _ => c) :=
  lic_expectation_provind_le P (L.gridDP) (toLUV i) hcode L.gridDP_hcons c
    ((Filter.eventually_ge_atTop (max 1 i)).mono (fun n hin v hv =>
      ⟨(L.value i : ℝ), hc, (by simpa using L.expectApprox_near_gridDP (n := n + 1) (by omega) hv (by omega) (by omega))⟩))

/-- Certified expectation provability induction, equality (`=`) form: a determined
`dd:luv-arith` value forces the expectation sequence to it.
Paper node: `thm:expprovind` -/
theorem lic_expectation_provind_eq_arith (P : History) [IsLogicalInductor P (L.gridDP)]
    (i : ℕ) (hcode : (toLUV i).RpnThresholdCodes)
    (c : ℝ) (hc : (L.value i : ℝ) = c) :
    AsympEq ((toLUV i).expectSeq P) (fun _ => c) :=
  lic_expectation_provind_eq P (L.gridDP) (toLUV i) hcode L.gridDP_hcons c
    ((Filter.eventually_ge_atTop (max 1 i)).mono (fun n hin v hv =>
      hc ▸ (by simpa using L.expectApprox_near_gridDP (n := n + 1) (by omega) hv (by omega) (by omega))))

/-- **Certified linearity of expectation.**  Linearity for `dd:luv-arith` LUVs `Xᵢ`,
`Xⱼ`, `Xₖ`, with the world-value and linear-relation hypotheses discharged from arithmetic: the
sole content is the plain rational identity `valueₖ = a·valueᵢ + b·valueⱼ`.
Paper node: `thm:loe` -/
theorem lic_linearity_of_expectation_arith (P : History) [IsLogicalInductor P (L.gridDP)]
    (a b : ℚ) (i j k : ℕ)
    (hcodeI : (toLUV i).RpnThresholdCodes) (hcodeJ : (toLUV j).RpnThresholdCodes)
    (hcodeK : (toLUV k).RpnThresholdCodes)
    (hlin : L.value k = a * L.value i + b * L.value j) :
    AsympEq (fun n => (a : ℝ) * (toLUV i).expect P n + (b : ℝ) * (toLUV j).expect P n)
      ((toLUV k).expectSeq P) :=
  lic_linearity_of_expectation P (L.gridDP) a b (toLUV i) (toLUV j) (toLUV k)
    hcodeI hcodeJ hcodeK L.gridDP_hcons
    ((Filter.eventually_ge_atTop (max 1 (max i (max j k)))).mono (fun n hin v hv =>
      ⟨(L.value i : ℝ), (L.value j : ℝ), (L.value k : ℝ), by exact_mod_cast hlin,
        (by simpa using L.expectApprox_near_gridDP (n := n + 1) (by omega) hv (by omega) (by omega)),
        (by simpa using L.expectApprox_near_gridDP (n := n + 1) (by omega) hv (by omega) (by omega)),
        (by simpa using L.expectApprox_near_gridDP (n := n + 1) (by omega) hv (by omega) (by omega))⟩))

/-- **Certified `thm:exppolymax`.**  The sequence-level polynomial-max expectation identity for a
`dd:luv-arith` LUV-combination sequence, with the `WorldValued` *representation* hypothesis
discharged from arithmetic over `luvThresholdDP`, the process that reveals every `T`-provable
threshold, and the mesh-softmax operational witness derived from the sequence's compact syntax.
Paper node: `thm:exppolymax` -/
theorem exppolymax_arith {As : ℕ → LUVCombination} {P : History} {T : ArithmeticTheory}
    [𝗥₀ ⪯ T] [T.Δ₁] [𝗜𝚺₁ ⪯ T] [RepresentsComputations T] [Entailment.Consistent T]
    [IsLogicalInductor P (L.luvThresholdDP T)]
    (hAs : ∀ n, ∀ p ∈ (As n).terms, ∃ i, p.2 = toLUV i)
    (h : LUVCombination.BoundedSequence As P) (S : LUVCombinationSyntax As) :
    liminf (fun n => (As n).expect P n) atTop =
        liminf (LUVCombination.futureHigh As P) atTop ∧
      limsup (fun n => (As n).expect P n) atTop =
        limsup (LUVCombination.futureLow As P) atTop :=
  h.exppolymax_ofSyntax S (L.worldValued_ofArithmetic (L.luvArithmeticPresentation T) As hAs)
    (L.luvThresholdDP_hworld T)

/-- **Certified `thm:wubexp`.**  Weighted unbiasedness of determined-value expectation for a
`dd:luv-arith` LUV-combination sequence, with the `WorldValued` *representation* hypothesis
discharged from arithmetic over `luvThresholdDP`.

Two inputs stay assumed, and both are the paper's own.  `hdet` is determination via `Θ`
(`def:affthmval`) together with the resulting truth stream — a semantic object, not a
computable oracle, so it is given rather than derived.  `C` is the paper's operational
premise, "`thmval` computable by the next deferral deadline", at the normalized threshold
mesh the trader actually quotes.

Everything else the argument needs is constructed: the feedback traders' emission
certificates (`FeedbackEmission.feedbackTraderEmissionSigns`) and the sparse delayed-truth
affine sequence (`FeedbackTruth.feedbackTruthSequence`).  The bridge is built at
*approximate* determination, so no per-component-LUV determinedness is assumed anywhere;
see `FeedbackTruth.luv_wubexp_ofComputation` for why the mesh route survives
combination-level determination.

Kind `C`; provenance: `hAs`, `h`, `hdet`, `hshare`, `hWgen`, `hWdiv`, `hstrict`, `hsupport`
(a); `C` (a), in the `dd:fuel` efficiency model.
Paper node: `thm:wubexp` -/
theorem wubexp_arith {As : ℕ → LUVCombination} {P : History} {T : ArithmeticTheory}
    [𝗥₀ ⪯ T] [T.Δ₁] [𝗜𝚺₁ ⪯ T] [RepresentsComputations T] [Entailment.Consistent T]
    [IsLogicalInductor P (L.luvThresholdDP T)]
    (hAs : ∀ n, ∀ p ∈ (As n).terms, ∃ i, p.2 = toLUV i)
    (h : LUVCombination.BoundedSequence As P)
    {truth : ℕ → ℝ}
    (hdet : LUVCombination.DeterminedViaTheory As P (L.luvThresholdDP T) truth)
    (b : ℚ) (hshare : ∀ n, (As n).shareNorm P ≤ (b : ℝ))
    {W : ℕ → EF} (hWgen : PGenerableWeighting W) (hWdiv : DivergentWeighting W P)
    {f : DeferralFunction} (hstrict : StrictlyIncreasingDeferral f)
    (hsupport : WeightingSupportedOnDeferralImage W P f)
    (C : FeedbackTruth.FeedbackTruthComputation
      (LUVCombination.normalizedMeshTruth As P (L.luvThresholdDP T)
        (L.luvThresholdDP_hworld T) b) f) :
    weightedBias (fun i => (W i).denote P)
      (fun i => (As i).expect P i) truth ≈ₙ (fun _ => 0) :=
  FeedbackTruth.luv_wubexp_ofComputation h
    (L.worldValued_ofArithmetic (L.luvArithmeticPresentation T) As hAs)
    hdet b hshare hWgen hWdiv hstrict (L.luvThresholdDP_hworld T) C hsupport

/-! ## Certified liminf/limsup coherence (`thm:expcoh`, `thm:perexpkno`)

`expcoh`/`perexpkno` need the **completed-world** values (`WorldValued`, all thresholds), which
the full provability enumerator `luvThresholdDP` supplies. -/
section Combined
variable (T : ArithmeticTheory) [𝗥₀ ⪯ T] [T.Δ₁] [𝗜𝚺₁ ⪯ T] [RepresentsComputations T]
  [Entailment.Consistent T]

/-- **Certified `thm:expcoh`.**  Completed/limiting/diagonal expectation coherence for
a `dd:luv-arith` LUV-combination sequence, with the `WorldValued` representation hypothesis
discharged from arithmetic and both the mesh-softmax operational witness and the threshold-code
certificates derived from the sequence's compact syntax.
Paper node: `thm:expcoh` -/
theorem expcoh_arith {As : ℕ → LUVCombination} {P : History}
    [IsLogicalInductor P (L.luvThresholdDP T)]
    (hAs : ∀ n, ∀ p ∈ (As n).terms, ∃ i, p.2 = toLUV i)
    (h : LUVCombination.BoundedSequence As P)
    (S : LUVCombinationSyntax As) :
    (liminf (LUVCombination.completedLow As P (L.luvThresholdDP T)) atTop ≤
        liminf (fun n => (As n).expectInf P) atTop ∧
      liminf (fun n => (As n).expectInf P) atTop ≤
        liminf (fun n => (As n).expect P n) atTop) ∧
      (limsup (fun n => (As n).expect P n) atTop ≤
          limsup (fun n => (As n).expectInf P) atTop ∧
        limsup (fun n => (As n).expectInf P) atTop ≤
          limsup (LUVCombination.completedHigh As P (L.luvThresholdDP T)) atTop) :=
  h.expcoh_ofSyntax S (L.worldValued_ofArithmetic (L.luvArithmeticPresentation T) As hAs)
    (L.luvThresholdDP_hworld T)

/-- **Certified `thm:perexpkno`.**  Persistence of expectation knowledge, with the
representation hypotheses discharged from arithmetic as in `expcoh_arith`.
Paper node: `thm:perexpkno` -/
theorem perexpkno_arith {As : ℕ → LUVCombination} {P : History}
    [IsLogicalInductor P (L.luvThresholdDP T)]
    (hAs : ∀ n, ∀ p ∈ (As n).terms, ∃ i, p.2 = toLUV i)
    (h : LUVCombination.BoundedSequence As P)
    (S : LUVCombinationSyntax As) :
    liminf (LUVCombination.futureLow As P) atTop =
        liminf (fun n => (As n).expectInf P) atTop ∧
      limsup (LUVCombination.futureHigh As P) atTop =
        limsup (fun n => (As n).expectInf P) atTop :=
  h.perexpkno_ofSyntax S (L.worldValued_ofArithmetic (L.luvArithmeticPresentation T) As hAs)
    (L.luvThresholdDP_hworld T)

end Combined

/-! ## Efficient computability of the scheduled processes

The scheduled grid process (and hence the combined process) is computable: stage `n` is the
`toFinset` of a total, computably generated literal list — the in-range grid literals plus a
harmless in-range default for out-of-range event codes (deduplicated by `toFinset`).  The literal
polarity runs `L.num`/`L.den`, so this layer works with `Computable` rather than `Primrec`. -/

/-- Total per-event literal emitter for stage `n`: decode `e = ⟨i, ⟨m, j⟩⟩` and emit the grid
literal when in range, else the fixed in-range literal `⌜X₀ > 0/1⌝` (deduplicated away). -/
private noncomputable def gridEmit (n e : ℕ) : Sentence :=
  if e.unpair.1 ≤ n ∧ e.unpair.2.unpair.1 ≤ n + 1 ∧ e.unpair.2.unpair.2 < e.unpair.2.unpair.1
  then L.gridLiteral e.unpair.1 e.unpair.2.unpair.2 e.unpair.2.unpair.1
  else L.gridLiteral 0 0 1

attribute [local irreducible] Nat.sqrt in
private lemma gridEmit_computable : Computable₂ (L.gridEmit) := by
  have hatom : Primrec (fun c : ℕ => (LO.Propositional.Formula.atom c : Sentence)) :=
    Primrec.encode_iff.mp
      ((Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 1) Primrec.id)).of_eq
        (fun c => (encode_atom c).symm))
  have hneg : Primrec (fun c : ℕ => (∼(LO.Propositional.Formula.atom c) : Sentence)) :=
    Primrec.encode_iff.mp
      ((Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 2)
        (Primrec₂.natPair.comp
          (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 1) Primrec.id))
          (Primrec.const (Nat.pair 0 0 + 1))))).of_eq
        (fun c => (encode_negAtom c).symm))
  -- the grid literal on a packed code `e = ⟨i, ⟨m, j⟩⟩`
  have hlit : Computable (fun e : ℕ =>
      L.gridLiteral e.unpair.1 e.unpair.2.unpair.2 e.unpair.2.unpair.1) := by
    have htc := thresholdCodeNat_primrec
    have hd : Computable (fun e : ℕ => decide (L.ThresholdPred
        (thresholdCodeNat e.unpair.1 e.unpair.2.unpair.2 e.unpair.2.unpair.1))) :=
      L.thresholdPred_computable.decide.comp htc.to_comp
    have hpos := (hatom.comp htc).to_comp
    have hng := (hneg.comp htc).to_comp
    refine (Computable.cond hd hpos hng).of_eq (fun e => ?_)
    unfold gridLiteral
    rw [← thresholdCodeNat_eq]
    by_cases h : L.ThresholdPred
        (thresholdCodeNat e.unpair.1 e.unpair.2.unpair.2 e.unpair.2.unpair.1)
    · simp [thresholdSentence, thresholdCodeNat_eq]
    · simp [thresholdSentence, thresholdCodeNat_eq]
  -- the range test is primitive recursive on the pair `(n, e)`
  have hc : Computable (fun p : ℕ × ℕ => decide (p.2.unpair.1 ≤ p.1
      ∧ p.2.unpair.2.unpair.1 ≤ p.1 + 1 ∧ p.2.unpair.2.unpair.2 < p.2.unpair.2.unpair.1)) := by
    have hi : Primrec (fun p : ℕ × ℕ => p.2.unpair.1) :=
      Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)
    have hm : Primrec (fun p : ℕ × ℕ => p.2.unpair.2.unpair.1) :=
      Primrec.fst.comp (Primrec.unpair.comp
        (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))
    have hj : Primrec (fun p : ℕ × ℕ => p.2.unpair.2.unpair.2) :=
      Primrec.snd.comp (Primrec.unpair.comp
        (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))
    exact (PrimrecPred.decide (PrimrecPred.and (Primrec.nat_le.comp hi Primrec.fst)
      (PrimrecPred.and (Primrec.nat_le.comp hm (Primrec.succ.comp Primrec.fst))
        (Primrec.nat_lt.comp hj hm)))).to_comp
  exact (Computable.cond hc (hlit.comp Computable.snd)
    (Computable.const (L.gridLiteral 0 0 1))).of_eq (fun p => by
      unfold gridEmit
      by_cases h : p.2.unpair.1 ≤ p.1 ∧ p.2.unpair.2.unpair.1 ≤ p.1 + 1
          ∧ p.2.unpair.2.unpair.2 < p.2.unpair.2.unpair.1
      · simp [h]
      · simp [h])

/-- The stage-`n` literal list is computable (built by `Nat.rec` over the event bound). -/
private lemma gridList_computable :
    Computable (fun n =>
      (List.range (Nat.pair n (Nat.pair (n + 1) (n + 1)) + 1)).map (L.gridEmit n)) := by
  have hB : Computable (fun n : ℕ => Nat.pair n (Nat.pair (n + 1) (n + 1)) + 1) :=
    (Primrec.succ.comp (Primrec₂.natPair.comp Primrec.id
      (Primrec₂.natPair.comp (Primrec.succ.comp Primrec.id)
        (Primrec.succ.comp Primrec.id)))).to_comp
  have hh : Computable₂ (fun (n : ℕ) (p : ℕ × List Sentence) => p.2 ++ [L.gridEmit n p.1]) :=
    (Computable.list_concat.comp (Computable.snd.comp Computable.snd)
      (L.gridEmit_computable.comp Computable.fst (Computable.fst.comp Computable.snd))).to₂
  have h := Computable.nat_rec hB (Computable.const ([] : List Sentence)) hh
  refine h.of_eq (fun n => ?_)
  generalize Nat.pair n (Nat.pair (n + 1) (n + 1)) + 1 = N
  induction N with
  | zero => simp
  | succ N ih => simp [List.range_succ, ih]

private lemma gridStage_eq_list_toFinset (n : ℕ) :
    L.gridStage n
      = ((List.range (Nat.pair n (Nat.pair (n + 1) (n + 1)) + 1)).map
          (L.gridEmit n)).toFinset := by
  ext φ
  rw [mem_gridStage]
  simp only [List.mem_toFinset, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, m, j, hi, hm, hj, rfl⟩
    refine ⟨Nat.pair i (Nat.pair m j), ?_, ?_⟩
    · have hbound : Nat.pair i (Nat.pair m j) ≤ Nat.pair n (Nat.pair (n + 1) (n + 1)) :=
        le_trans (pair_le_pair_right' _
          (le_trans (pair_le_pair_right' _ (by omega)) (pair_le_pair_left' _ hm)))
          (pair_le_pair_left' _ hi)
      omega
    · unfold gridEmit
      simp only [Nat.unpair_pair]
      rw [if_pos ⟨hi, hm, hj⟩]
  · rintro ⟨e, _, rfl⟩
    unfold gridEmit
    by_cases hc : e.unpair.1 ≤ n ∧ e.unpair.2.unpair.1 ≤ n + 1
        ∧ e.unpair.2.unpair.2 < e.unpair.2.unpair.1
    · rw [if_pos hc]
      exact ⟨e.unpair.1, e.unpair.2.unpair.1, e.unpair.2.unpair.2, hc.1, hc.2.1, hc.2.2, rfl⟩
    · rw [if_neg hc]
      exact ⟨0, 1, 0, Nat.zero_le n, by omega, Nat.zero_lt_one, rfl⟩

/-- **The scheduled grid process is computable.** -/
lemma gridDP_computable : ComputableDeductiveProcess (L.gridDP) := by
  have hsorted : Computable (fun n =>
      Encodable.encode ((sentenceDedup
        ((List.range (Nat.pair n (Nat.pair (n + 1) (n + 1)) + 1)).map
          (L.gridEmit n))).insertionSort sentenceCodeLE)) :=
    Computable.encode.comp (sentenceInsertionSort_prim.to_comp.comp
      (sentenceDedup_prim.to_comp.comp (L.gridList_computable)))
  have henc : Computable (fun n => Encodable.encode ((L.gridDP).D n)) := by
    refine hsorted.of_eq (fun n => ?_)
    show Encodable.encode ((sentenceDedup _).insertionSort sentenceCodeLE)
      = Encodable.encode (L.gridStage n)
    rw [L.gridStage_eq_list_toFinset n, encode_toFinset_eq]
  obtain ⟨code, hcode⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp henc.partrec)
  refine ⟨code, fun n => ?_⟩
  rw [hcode]
  exact Part.mem_some _

/-! ## Fully unconditional certified endpoints

With the scheduled grid process proved computable and the threshold codes proved poly-fueled,
the certified expectation endpoints need **no** hypotheses beyond the plain rational bound: the
logical inductor is the constructed `LIA` over `gridDP`, its price range comes from the criterion
class, and the efficiency certificate is `toLUV_polyThresholdCodes`. -/

/-- **Fully unconditional certified expectation provability induction (`≥`).**
Paper node: `thm:expprovind` -/
theorem lic_expectation_provind_arith_unconditional (i : ℕ) (c : ℝ)
    (hc : c ≤ (L.value i : ℝ)) :
    AsympGE ((toLUV i).expectSeq (liaHistory (L.gridDP))) (fun _ => c) := by
  haveI := LIA_is_logical_inductor (L.gridDP) L.gridDP_computable
  exact L.lic_expectation_provind_arith (liaHistory (L.gridDP)) i
    (LUV.RpnThresholdCodes.ofPolyThresholdCodes (toLUV_polyThresholdCodes i))
    c hc

/-- **Fully unconditional certified expectation provability induction (`≤`).**
Paper node: `thm:expprovind` -/
theorem lic_expectation_provind_le_arith_unconditional (i : ℕ) (c : ℝ)
    (hc : (L.value i : ℝ) ≤ c) :
    AsympLE ((toLUV i).expectSeq (liaHistory (L.gridDP))) (fun _ => c) := by
  haveI := LIA_is_logical_inductor (L.gridDP) L.gridDP_computable
  exact L.lic_expectation_provind_le_arith (liaHistory (L.gridDP)) i
    (LUV.RpnThresholdCodes.ofPolyThresholdCodes (toLUV_polyThresholdCodes i))
    c hc

/-- **Fully unconditional certified expectation provability induction (`=`).**
Paper node: `thm:expprovind` -/
theorem lic_expectation_provind_eq_arith_unconditional (i : ℕ) (c : ℝ)
    (hc : (L.value i : ℝ) = c) :
    AsympEq ((toLUV i).expectSeq (liaHistory (L.gridDP))) (fun _ => c) := by
  haveI := LIA_is_logical_inductor (L.gridDP) L.gridDP_computable
  exact L.lic_expectation_provind_eq_arith (liaHistory (L.gridDP)) i
    (LUV.RpnThresholdCodes.ofPolyThresholdCodes (toLUV_polyThresholdCodes i))
    c hc

/-- **Fully unconditional certified linearity of expectation.**  The sole hypothesis is the
rational identity `valueₖ = a·valueᵢ + b·valueⱼ`.
Paper node: `thm:loe` -/
theorem lic_linearity_of_expectation_arith_unconditional (a b : ℚ) (i j k : ℕ)
    (hlin : L.value k = a * L.value i + b * L.value j) :
    AsympEq (fun n => (a : ℝ) * (toLUV i).expect (liaHistory (L.gridDP)) n
        + (b : ℝ) * (toLUV j).expect (liaHistory (L.gridDP)) n)
      ((toLUV k).expectSeq (liaHistory (L.gridDP))) := by
  haveI := LIA_is_logical_inductor (L.gridDP) L.gridDP_computable
  exact L.lic_linearity_of_expectation_arith (liaHistory (L.gridDP)) a b i j k
    (LUV.RpnThresholdCodes.ofPolyThresholdCodes (toLUV_polyThresholdCodes i))
    (LUV.RpnThresholdCodes.ofPolyThresholdCodes (toLUV_polyThresholdCodes j))
    (LUV.RpnThresholdCodes.ofPolyThresholdCodes (toLUV_polyThresholdCodes k))
    hlin

end ComputableLUV

end LogicalInduction
