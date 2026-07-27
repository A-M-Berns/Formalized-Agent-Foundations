import LogicalInduction.Construction.Witnesses.LUVDeductiveProcess
import LogicalInduction.Properties.ExpectationAffine

/-!
# End-to-end certified expectation endpoint (F7, item 5 discharge)

`ExpectationAffine.lean` now states `lic_expectation_provind` with a **finite-precision, eventual**
world hypothesis (`|𝔼_n^v(X) − x| ≤ 1/n`), which a finite deductive-process stage can realize.
This file *discharges that hypothesis from the certified arithmetic*: it builds a scheduled-reveal
deductive process `gridDP` whose stage `n` contains, for every LUV index `i ≤ n` and grid point
`j/n` (`j < n`), the `Θ`-decided threshold literal.  Every world consistent with that stage then
satisfies grid coherence, so `expectApprox_near_ofGrid` pins its day-`n` expectation within `1/n`
of the standard value `numᵢ/denᵢ` — for **all** consistent worlds, which is what the trader
engine needs.

The resulting `lic_expectation_provind_arith` is the paper's provability-induction endpoint with
the value-agreement hypothesis (`ValuesAt`/the audit's "operational hypothesis the paper
discharges") **replaced by arithmetic**: nothing but `c ≤ numᵢ/denᵢ`, the disclosed
efficiency-code and price-range boundaries, and the existence of a logical inductor over `gridDP`.
-/

namespace LogicalInduction

open LO.FirstOrder LO.FirstOrder.Arithmetic Filter Topology

/-- **Combination-level expectation provability induction, `≤` form.**  A bounded LUV-combination
sequence whose completed-theory value stays `≤ c` has diagonal expectation `≲ₙ c`.
Paper node: `thm:expprovind` -/
theorem lic_expect_combination_provind_le
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    (h : LUVCombination.BoundedSequence As P)
    (hexact : LUVCombination.ExactTheoryPresentation As DP)
    (c : ℝ) (hdet : ∀ n, (As n).value P (hexact.value n) ≤ c)
    (b : ℚ) (hshare : ∀ n, (As n).shareNorm P ≤ (b : ℝ))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (As n).expect P n) ≲ₙ (fun _ => c) := by
  have hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1 :=
    fun n φ => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n φ
  obtain ⟨B, hB⟩ := h.bounded
  have hbounded : BoundedAffinePrices (fun n => (As n).meshAffine n) P :=
    ⟨max B 0, le_max_right _ _, fun n m =>
      le_trans (le_trans ((((As n).meshAffine n).abs_price_le_l1Norm P m (fun φ => hP m φ)).trans
        ((As n).meshAffine_l1Norm_le P n)) (hB n)) (le_max_left _ _)⟩
  have hmag : ∃ C : ℝ, ∀ n, ((As n).meshAffine n).magnitude P ≤ C :=
    ⟨(b : ℝ), fun n => ((As n).meshAffine_magnitude_le_shareNorm P n).trans (hshare n)⟩
  have hval : ∀ ε > 0, ∀ᶠ n in atTop, ∀ v : PCWorld, v.ConsistentWithTheory DP →
      ((As n).meshAffine n).value P v.payout ≤ c + ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt ((b : ℝ) / ε)
    filter_upwards [Filter.eventually_ge_atTop (max 1 N)] with n hn v hv
    have hn0 : 0 < n := by omega
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
    have hnear := (As n).meshAffine_value_near P v (hexact.value n) hn0 (hexact.valuesAt n v hv)
    rw [abs_le] at hnear
    have hbound : (As n).shareNorm P * (1 / n) ≤ (b : ℝ) * (1 / n) :=
      mul_le_mul_of_nonneg_right (hshare n) (by positivity)
    have hsmall : (b : ℝ) * (1 / n) ≤ ε := by
      rw [mul_one_div, div_le_iff₀ hnR]
      nlinarith [(div_lt_iff₀ hε).mp (hN.trans_le
        (show ((N : ℕ) : ℝ) ≤ n by exact_mod_cast le_trans (le_max_right 1 N) hn))]
    linarith [hnear.2, hdet n, hbound, hsmall]
  simpa only [LUVCombination.meshAffine_price_diagonal] using
    (h.poly.mesh_poly).affine_provind_theory_le_const P DP hbounded hmag hworld c hval

/-- **Combination-level expectation provability induction, `≥` form.**
Paper node: `thm:expprovind` -/
theorem lic_expect_combination_provind_ge
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    (h : LUVCombination.BoundedSequence As P)
    (hexact : LUVCombination.ExactTheoryPresentation As DP)
    (c : ℝ) (hdet : ∀ n, c ≤ (As n).value P (hexact.value n))
    (b : ℚ) (hshare : ∀ n, (As n).shareNorm P ≤ (b : ℝ))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (As n).expect P n) ≳ₙ (fun _ => c) := by
  have hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1 :=
    fun n φ => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n φ
  obtain ⟨B, hB⟩ := h.bounded
  have hbounded : BoundedAffinePrices (fun n => (As n).meshAffine n) P :=
    ⟨max B 0, le_max_right _ _, fun n m =>
      le_trans (le_trans ((((As n).meshAffine n).abs_price_le_l1Norm P m (fun φ => hP m φ)).trans
        ((As n).meshAffine_l1Norm_le P n)) (hB n)) (le_max_left _ _)⟩
  have hmag : ∃ C : ℝ, ∀ n, ((As n).meshAffine n).magnitude P ≤ C :=
    ⟨(b : ℝ), fun n => ((As n).meshAffine_magnitude_le_shareNorm P n).trans (hshare n)⟩
  have hval : ∀ ε > 0, ∀ᶠ n in atTop, ∀ v : PCWorld, v.ConsistentWithTheory DP →
      c - ε ≤ ((As n).meshAffine n).value P v.payout := by
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt ((b : ℝ) / ε)
    filter_upwards [Filter.eventually_ge_atTop (max 1 N)] with n hn v hv
    have hn0 : 0 < n := by omega
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
    have hnear := (As n).meshAffine_value_near P v (hexact.value n) hn0 (hexact.valuesAt n v hv)
    rw [abs_le] at hnear
    have hbound : (As n).shareNorm P * (1 / n) ≤ (b : ℝ) * (1 / n) :=
      mul_le_mul_of_nonneg_right (hshare n) (by positivity)
    have hsmall : (b : ℝ) * (1 / n) ≤ ε := by
      rw [mul_one_div, div_le_iff₀ hnR]
      nlinarith [(div_lt_iff₀ hε).mp (hN.trans_le
        (show ((N : ℕ) : ℝ) ≤ n by exact_mod_cast le_trans (le_max_right 1 N) hn))]
    linarith [hnear.1, hdet n, hbound, hsmall]
  simpa only [LUVCombination.meshAffine_price_diagonal] using
    (h.poly.mesh_poly).affine_provind_theory_ge_const P DP hbounded hmag hworld c hval

/-- **Combination-level expectation provability induction, `=` form.**
Paper node: `thm:expprovind` -/
theorem lic_expect_combination_provind_eq
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    (h : LUVCombination.BoundedSequence As P)
    (hexact : LUVCombination.ExactTheoryPresentation As DP)
    (c : ℝ) (hdet : ∀ n, (As n).value P (hexact.value n) = c)
    (b : ℚ) (hshare : ∀ n, (As n).shareNorm P ≤ (b : ℝ))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (As n).expect P n) ≈ₙ (fun _ => c) := by
  rw [asympEq_iff_asympLE_asympGE]
  exact ⟨lic_expect_combination_provind_le h hexact c (fun n => (hdet n).le) b hshare hworld,
    lic_expect_combination_provind_ge h hexact c (fun n => (hdet n).ge) b hshare hworld⟩

/-- **Combination-level expectation provability induction, `= 0` form** (`thm:loe` substrate).
The paper's own route to linearity (`app:loe`): apply `thm:expprovind` to the combination
`aX+bY−Z`, valued `0` because `Θ ⊢ Z = aX+bY`.
Paper node: `thm:loe` -/
theorem lic_expect_combination_provind_zero
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    (h : LUVCombination.BoundedSequence As P)
    (hexact : LUVCombination.ExactTheoryPresentation As DP)
    (hdet0 : ∀ n, (As n).value P (hexact.value n) = 0)
    (b : ℚ) (hshare : ∀ n, (As n).shareNorm P ≤ (b : ℝ))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (As n).expect P n) ≈ₙ (fun _ => 0) :=
  lic_expect_combination_provind_eq h hexact 0 hdet0 b hshare hworld

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
representation (`ExactTheoryPresentation`, F7-derivable) enter as the disclosed hypotheses.
Paper node: `thm:loe` -/
theorem lic_linearity_of_expectation_seq
    {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    (a b : ℕ → ℚ) (X Y Z : ℕ → LUV)
    (h : LUVCombination.BoundedSequence (linearityLUVComb a b X Y Z) P)
    (hexact : LUVCombination.ExactTheoryPresentation (linearityLUVComb a b X Y Z) DP)
    (hdet0 : ∀ n, (linearityLUVComb a b X Y Z n).value P (hexact.value n) = 0)
    (bnd : ℚ)
    (hshare : ∀ n, (linearityLUVComb a b X Y Z n).shareNorm P ≤ (bnd : ℝ))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    AsympEq (fun n => (a n : ℝ) * (X n).expect P n + (b n : ℝ) * (Y n).expect P n)
      (fun n => (Z n).expect P n) := by
  have hzero := lic_expect_combination_provind_zero h hexact hdet0 bnd hshare hworld
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

/-- Scheduled-reveal stage: all grid literals for indices and precisions up to `n`. -/
noncomputable def gridStage (n : ℕ) : Finset Sentence :=
  (Finset.range (n + 1)).biUnion (fun i =>
    (Finset.range (n + 1)).biUnion (fun m =>
      (Finset.range m).image (fun j => L.gridLiteral i j m)))

lemma mem_gridStage {φ : Sentence} {n : ℕ} :
    φ ∈ L.gridStage n ↔ ∃ i m j, i ≤ n ∧ m ≤ n ∧ j < m ∧ φ = L.gridLiteral i j m := by
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
/-- The standard-truth world is consistent with every scheduled stage. -/
lemma luvWorld_consistent_gridStage (n : ℕ) :
    (L.luvWorld).ConsistentWith ((L.gridDP).D n) := by
  intro φ hφ
  rw [show (L.gridDP).D n = L.gridStage n from rfl, mem_gridStage] at hφ
  obtain ⟨i, m, j, _, _, _, rfl⟩ := hφ
  unfold gridLiteral
  by_cases hp : L.ThresholdPred (thresholdCode i ((j : ℚ) / (m : ℚ)))
  · rw [if_pos hp]; exact hp
  · rw [if_neg hp, holds_not]; exact hp

/-- `hcons` for the scheduled process. -/
lemma gridDP_hcons (n : ℕ) : ∃ v : PCWorld, v.ConsistentWith ((L.gridDP).D n) :=
  ⟨L.luvWorld, L.luvWorld_consistent_gridStage n⟩

attribute [local irreducible] Nat.sqrt in
/-- **Grid coherence from stage membership.**  A world consistent with stage `m` reads each grid
literal's polarity for every index `i ≤ m` and precision `n ≤ m`, so `⌜Xᵢ > j/n⌝` holds exactly
when the threshold predicate does. -/
lemma holds_thresholdSentence_iff {v : PCWorld} {m n : ℕ}
    (hv : v.ConsistentWith ((L.gridDP).D m)) {i j : ℕ} (hi : i ≤ m) (hnm : n ≤ m) (hj : j < n) :
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
index `i ≤ m`, and any precision `0 < n ≤ m`, the day-`n` approximate expectation of `Xᵢ` is within
`1/n` of its standard rational value — with no world-value hypothesis. -/
lemma expectApprox_near_gridDP {v : PCWorld} {m n : ℕ} (hn : 0 < n)
    (hv : v.ConsistentWith ((L.gridDP).D m)) {i : ℕ} (hi : i ≤ m) (hnm : n ≤ m) :
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

/-- **F7 item 5, certified provability induction.**  Expectation provability induction for a
`dd:luv-arith` LUV, with the world-value hypothesis discharged from arithmetic: it follows from
the plain rational bound `c ≤ numᵢ/denᵢ`.  Remaining premises are the disclosed boundaries — the
efficiency codes, the price range, and a logical inductor over the scheduled process.
Paper node: `thm:expprovind` -/
theorem lic_expectation_provind_arith (P : History) [IsLogicalInductor P (L.gridDP)]
    (i : ℕ) (hcode : (toLUV i).RpnThresholdCodes)
    (c : ℝ) (hc : c ≤ (L.value i : ℝ)) :
    AsympGE ((toLUV i).expectSeq P) (fun _ => c) :=
  lic_expectation_provind P (L.gridDP) (toLUV i) hcode L.gridDP_hcons c
    ((Filter.eventually_ge_atTop (max 1 i)).mono (fun n hin v hv =>
      ⟨(L.value i : ℝ), hc,
        L.expectApprox_near_gridDP (by omega) hv (by omega) le_rfl⟩))

/-- Certified expectation provability induction, upper (`≤`) form.
Paper node: `thm:expprovind` -/
theorem lic_expectation_provind_le_arith (P : History) [IsLogicalInductor P (L.gridDP)]
    (i : ℕ) (hcode : (toLUV i).RpnThresholdCodes)
    (c : ℝ) (hc : (L.value i : ℝ) ≤ c) :
    AsympLE ((toLUV i).expectSeq P) (fun _ => c) :=
  lic_expectation_provind_le P (L.gridDP) (toLUV i) hcode L.gridDP_hcons c
    ((Filter.eventually_ge_atTop (max 1 i)).mono (fun n hin v hv =>
      ⟨(L.value i : ℝ), hc, L.expectApprox_near_gridDP (by omega) hv (by omega) le_rfl⟩))

/-- Certified expectation provability induction, equality (`=`) form: a determined
`dd:luv-arith` value forces the expectation sequence to it.
Paper node: `thm:expprovind` -/
theorem lic_expectation_provind_eq_arith (P : History) [IsLogicalInductor P (L.gridDP)]
    (i : ℕ) (hcode : (toLUV i).RpnThresholdCodes)
    (c : ℝ) (hc : (L.value i : ℝ) = c) :
    AsympEq ((toLUV i).expectSeq P) (fun _ => c) :=
  lic_expectation_provind_eq P (L.gridDP) (toLUV i) hcode L.gridDP_hcons c
    ((Filter.eventually_ge_atTop (max 1 i)).mono (fun n hin v hv =>
      hc ▸ L.expectApprox_near_gridDP (by omega) hv (by omega) le_rfl))

/-- **F7 item 5, certified linearity of expectation.**  Linearity for `dd:luv-arith` LUVs `Xᵢ`,
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
        L.expectApprox_near_gridDP (by omega) hv (by omega) le_rfl,
        L.expectApprox_near_gridDP (by omega) hv (by omega) le_rfl,
        L.expectApprox_near_gridDP (by omega) hv (by omega) le_rfl⟩))

/-- **F7 item 5, certified `thm:exppolymax`.**  The sequence-level polynomial-max expectation
identity for a `dd:luv-arith` LUV-combination sequence, with the `WorldValued` *representation*
hypothesis discharged from arithmetic (Phase B, over `luvThresholdDP` which reveals every provable
threshold).  The residual `MeshSoftmaxOperationalWitness` is the disclosed operational/efficiency
boundary the paper's own construction supplies.
Paper node: `thm:exppolymax` -/
theorem exppolymax_arith {As : ℕ → LUVCombination} {P : History} {T : ArithmeticTheory}
    [𝗥₀ ⪯ T] [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]
    [IsLogicalInductor P (L.luvThresholdDP T)]
    (hAs : ∀ n, ∀ p ∈ (As n).terms, ∃ i, p.2 = toLUV i)
    (h : LUVCombination.BoundedSequence As P) (ops : LUVCombination.MeshSoftmaxOperationalWitness As P)
    (b : ℚ) (hb : 0 ≤ (b : ℝ)) (hshare : ∀ n, (As n).shareNorm P ≤ (b : ℝ))
     :
    liminf (fun n => (As n).expect P n) atTop =
        liminf (LUVCombination.futureHigh As P) atTop ∧
      limsup (fun n => (As n).expect P n) atTop =
        limsup (LUVCombination.futureLow As P) atTop :=
  h.exppolymax ops (L.worldValued_ofArithmetic (L.luvArithmeticPresentation T) As hAs)
    b hb hshare (L.luvThresholdDP_hworld T)

/-- **F7 item 5, certified `thm:wubexp`.**  Weighted-unbiasedness of exact-value expectation for a
`dd:luv-arith` LUV-combination sequence, with the `ExactTheoryPresentation` *representation*
hypothesis discharged from arithmetic (Phase B, over `luvThresholdDP`).  The residual feedback
witnesses (`M7-FEEDBACK-EMIT`/`M7-FEEDBACK-TRUTH`) and determinacy datum are the disclosed
operational boundaries the paper's own construction supplies.
Paper node: `thm:wubexp` -/
theorem wubexp_arith {As : ℕ → LUVCombination} {P : History} {T : ArithmeticTheory}
    [𝗥₀ ⪯ T] [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]
    [IsLogicalInductor P (L.luvThresholdDP T)]
    (hAs : ∀ n, ∀ p ∈ (As n).terms, ∃ i, p.2 = toLUV i)
    (h : LUVCombination.BoundedSequence As P)
    {truth : ℕ → ℝ}
    (hdet : LUVCombination.DeterminedViaTheory As P (L.luvThresholdDP T) truth)
    (b : ℚ) (hshare : ∀ n, (As n).shareNorm P ≤ (b : ℝ))
    {W : ℕ → EF} (hWgen : PGenerableWeighting W) (hWdiv : DivergentWeighting W P)
    {f : DeferralFunction} (hstrict : StrictlyIncreasingDeferral f)
    (hsupport : WeightingSupportedOnDeferralImage W P f)
    (emit : AffineCombination.FeedbackTraderEmissionSigns
      (h.normalizedMesh_poly b) hWgen hstrict)
    (bridge : AffineCombination.FeedbackTruthSequence
      (LUVCombination.normalizedMesh As b)
      (LUVCombination.normalizedMeshTruth As P (L.luvThresholdDP T)
        (L.luvThresholdDP_hworld T) b) P (L.luvThresholdDP T) f) :
    weightedBias (fun i => (W i).denote P)
      (fun i => (As i).expect P i) truth ≈ₙ (fun _ => 0) :=
  h.wubexp (L.exactTheoryPresentation_ofArithmetic (L.luvArithmeticPresentation T) As hAs)
    hdet b hshare hWgen hWdiv hstrict hsupport (L.luvThresholdDP_hworld T) emit bridge

/-! ## Certified liminf/limsup coherence (`thm:expcoh`, `thm:perexpkno`)

`expcoh`/`perexpkno` need both the **completed-world** values (`WorldValued`, all thresholds) and
the **daily** finite-precision values (`ConvergencePresentation`).  No single scheduled process
gives both, so we run them over `combinedDP`, the union of the scheduled grid process (for daily
values) and the full provability enumerator `luvThresholdDP` (for completed-world values). -/
section Combined
variable (T : ArithmeticTheory) [𝗥₀ ⪯ T] [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]

/-- The scheduled grid process unioned with the full provability enumerator. -/
noncomputable def combinedDP : DeductiveProcess where
  D m := L.gridStage m ∪ (L.luvThresholdDP T).D m
  mono m := Finset.union_subset_union (L.gridStage_mono m) ((L.luvThresholdDP T).mono m)

lemma combinedDP_consistent_grid {v : PCWorld} {m : ℕ}
    (hv : v.ConsistentWith ((L.combinedDP T).D m)) : v.ConsistentWith (L.gridStage m) :=
  fun φ hφ => hv φ (Finset.mem_union_left _ hφ)

lemma combinedDP_consistentWithTheory_luv {v : PCWorld}
    (hv : v.ConsistentWithTheory (L.combinedDP T)) :
    v.ConsistentWithTheory (L.luvThresholdDP T) :=
  fun k φ hφ => hv k φ (Finset.mem_union_right _ hφ)

lemma combinedDP_hworld (m : ℕ) : ∃ v : PCWorld, v.ConsistentWith ((L.combinedDP T).D m) :=
  ⟨L.luvWorld, fun φ hφ => (Finset.mem_union.mp hφ).elim
    (L.luvWorld_consistent_gridStage m φ) (L.luvWorld_consistent T m φ)⟩

/-- `WorldValued` over `combinedDP`, from Phase B (over the ⊆ provability enumerator). -/
lemma worldValued_combinedDP {As : ℕ → LUVCombination}
    (hAs : ∀ n, ∀ p ∈ (As n).terms, ∃ i, p.2 = toLUV i) :
    LUVCombination.WorldValued As (L.combinedDP T) :=
  fun n v hv => L.worldValued_ofArithmetic (L.luvArithmeticPresentation T) As hAs n v
    (L.combinedDP_consistentWithTheory_luv T hv)

/-- `ConvergencePresentation` over `combinedDP`: the daily finite-precision values come from the
scheduled grid (eventually, once the stage reaches the LUV index); the threshold-code efficiency
certificate is the disclosed `dd:fuel` hypothesis. -/
noncomputable def convergencePresentation_combinedDP {As : ℕ → LUVCombination}
    (hAs : ∀ n, ∀ p ∈ (As n).terms, ∃ i, p.2 = toLUV i)
    (hcode : ∀ n p, p ∈ (As n).terms → p.2.RpnThresholdCodes) :
    LUVCombination.ConvergencePresentation As (L.combinedDP T) where
  threshold_code := hcode
  daily_value := by
    intro n p hp
    obtain ⟨i, hie⟩ := hAs n p hp
    filter_upwards [Filter.eventually_ge_atTop i] with m hmi v hv
    rw [hie]
    exact ⟨(L.value i : ℝ), by exact_mod_cast L.value_nonneg i, fun k hk hkm =>
      L.expectApprox_near_gridDP hk (L.combinedDP_consistent_grid T hv) hmi hkm⟩

/-- **F7 item 5, certified `thm:expcoh`.**  Completed/limiting/diagonal expectation coherence for
a `dd:luv-arith` LUV-combination sequence, with the `WorldValued` and `ConvergencePresentation`
representation hypotheses discharged from arithmetic; only the disclosed mesh-softmax operational
witness and threshold-code efficiency remain.
Paper node: `thm:expcoh` -/
theorem expcoh_arith {As : ℕ → LUVCombination} {P : History}
    [IsLogicalInductor P (L.combinedDP T)]
    (hAs : ∀ n, ∀ p ∈ (As n).terms, ∃ i, p.2 = toLUV i)
    (h : LUVCombination.BoundedSequence As P)
    (ops : LUVCombination.MeshSoftmaxOperationalWitness As P)
    (hcode : ∀ n p, p ∈ (As n).terms → p.2.RpnThresholdCodes)
    (b : ℚ) (hb : 0 ≤ (b : ℝ)) (hshare : ∀ n, (As n).shareNorm P ≤ (b : ℝ))
     :
    (liminf (LUVCombination.completedLow As P (L.combinedDP T)) atTop ≤
        liminf (fun n => (As n).expectInf P) atTop ∧
      liminf (fun n => (As n).expectInf P) atTop ≤
        liminf (fun n => (As n).expect P n) atTop) ∧
      (limsup (fun n => (As n).expect P n) atTop ≤
          limsup (fun n => (As n).expectInf P) atTop ∧
        limsup (fun n => (As n).expectInf P) atTop ≤
          limsup (LUVCombination.completedHigh As P (L.combinedDP T)) atTop) :=
  h.expcoh ops (L.worldValued_combinedDP T hAs)
    (L.convergencePresentation_combinedDP T hAs hcode) b hb hshare (L.combinedDP_hworld T)

/-- **F7 item 5, certified `thm:perexpkno`.**  Persistence of expectation knowledge, with the
representation hypotheses discharged from arithmetic as in `expcoh_arith`.
Paper node: `thm:perexpkno` -/
theorem perexpkno_arith {As : ℕ → LUVCombination} {P : History}
    [IsLogicalInductor P (L.combinedDP T)]
    (hAs : ∀ n, ∀ p ∈ (As n).terms, ∃ i, p.2 = toLUV i)
    (h : LUVCombination.BoundedSequence As P)
    (ops : LUVCombination.MeshSoftmaxOperationalWitness As P)
    (hcode : ∀ n p, p ∈ (As n).terms → p.2.RpnThresholdCodes)
    (b : ℚ) (hb : 0 ≤ (b : ℝ)) (hshare : ∀ n, (As n).shareNorm P ≤ (b : ℝ))
     :
    liminf (LUVCombination.futureLow As P) atTop =
        liminf (fun n => (As n).expectInf P) atTop ∧
      limsup (LUVCombination.futureHigh As P) atTop =
        limsup (fun n => (As n).expectInf P) atTop :=
  h.perexpkno ops (L.worldValued_combinedDP T hAs)
    (L.convergencePresentation_combinedDP T hAs hcode) b hb hshare (L.combinedDP_hworld T)

end Combined

/-! ## Efficient computability of the scheduled processes

The scheduled grid process (and hence the combined process) is computable: stage `n` is the
`toFinset` of a total, computably generated literal list — the in-range grid literals plus a
harmless in-range default for out-of-range event codes (deduplicated by `toFinset`).  The literal
polarity runs `L.num`/`L.den`, so this layer works with `Computable` rather than `Primrec`. -/

/-- Total per-event literal emitter for stage `n`: decode `e = ⟨i, ⟨m, j⟩⟩` and emit the grid
literal when in range, else the fixed in-range literal `⌜X₀ > 0/1⌝` (deduplicated away). -/
private noncomputable def gridEmit (n e : ℕ) : Sentence :=
  if e.unpair.1 ≤ n ∧ e.unpair.2.unpair.1 ≤ n ∧ e.unpair.2.unpair.2 < e.unpair.2.unpair.1
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
    · simp [h, thresholdSentence, thresholdCodeNat_eq]
    · simp [h, thresholdSentence, thresholdCodeNat_eq]
  -- the range test is primitive recursive on the pair `(n, e)`
  have hc : Computable (fun p : ℕ × ℕ => decide (p.2.unpair.1 ≤ p.1
      ∧ p.2.unpair.2.unpair.1 ≤ p.1 ∧ p.2.unpair.2.unpair.2 < p.2.unpair.2.unpair.1)) := by
    have hi : Primrec (fun p : ℕ × ℕ => p.2.unpair.1) :=
      Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)
    have hm : Primrec (fun p : ℕ × ℕ => p.2.unpair.2.unpair.1) :=
      Primrec.fst.comp (Primrec.unpair.comp
        (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))
    have hj : Primrec (fun p : ℕ × ℕ => p.2.unpair.2.unpair.2) :=
      Primrec.snd.comp (Primrec.unpair.comp
        (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))
    exact (PrimrecPred.decide (PrimrecPred.and (Primrec.nat_le.comp hi Primrec.fst)
      (PrimrecPred.and (Primrec.nat_le.comp hm Primrec.fst)
        (Primrec.nat_lt.comp hj hm)))).to_comp
  exact (Computable.cond hc (hlit.comp Computable.snd)
    (Computable.const (L.gridLiteral 0 0 1))).of_eq (fun p => by
      unfold gridEmit
      by_cases h : p.2.unpair.1 ≤ p.1 ∧ p.2.unpair.2.unpair.1 ≤ p.1
          ∧ p.2.unpair.2.unpair.2 < p.2.unpair.2.unpair.1
      · simp [h]
      · simp [h])

/-- The stage-`n` literal list is computable (built by `Nat.rec` over the event bound). -/
private lemma gridList_computable :
    Computable (fun n => (List.range (Nat.pair n (Nat.pair n n) + 1)).map (L.gridEmit n)) := by
  have hB : Computable (fun n : ℕ => Nat.pair n (Nat.pair n n) + 1) :=
    (Primrec.succ.comp (Primrec₂.natPair.comp Primrec.id
      (Primrec₂.natPair.comp Primrec.id Primrec.id))).to_comp
  have hh : Computable₂ (fun (n : ℕ) (p : ℕ × List Sentence) => p.2 ++ [L.gridEmit n p.1]) :=
    (Computable.list_concat.comp (Computable.snd.comp Computable.snd)
      (L.gridEmit_computable.comp Computable.fst (Computable.fst.comp Computable.snd))).to₂
  have h := Computable.nat_rec hB (Computable.const ([] : List Sentence)) hh
  refine h.of_eq (fun n => ?_)
  generalize Nat.pair n (Nat.pair n n) + 1 = N
  induction N with
  | zero => simp
  | succ N ih => simp [List.range_succ, ih]

private lemma gridStage_zero : L.gridStage 0 = ∅ := by
  ext φ
  simp only [Finset.notMem_empty, iff_false]
  rw [mem_gridStage]
  rintro ⟨i, m, j, _, hm, hj, _⟩
  omega

private lemma gridStage_eq_list_toFinset {n : ℕ} (hn : 1 ≤ n) :
    L.gridStage n
      = ((List.range (Nat.pair n (Nat.pair n n) + 1)).map (L.gridEmit n)).toFinset := by
  ext φ
  rw [mem_gridStage]
  simp only [List.mem_toFinset, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, m, j, hi, hm, hj, rfl⟩
    refine ⟨Nat.pair i (Nat.pair m j), ?_, ?_⟩
    · have hbound : Nat.pair i (Nat.pair m j) ≤ Nat.pair n (Nat.pair n n) :=
        le_trans (pair_le_pair_right' _
          (le_trans (pair_le_pair_right' _ (by omega)) (pair_le_pair_left' _ hm)))
          (pair_le_pair_left' _ hi)
      omega
    · unfold gridEmit
      simp only [Nat.unpair_pair]
      rw [if_pos ⟨hi, hm, hj⟩]
  · rintro ⟨e, _, rfl⟩
    unfold gridEmit
    by_cases hc : e.unpair.1 ≤ n ∧ e.unpair.2.unpair.1 ≤ n
        ∧ e.unpair.2.unpair.2 < e.unpair.2.unpair.1
    · rw [if_pos hc]
      exact ⟨e.unpair.1, e.unpair.2.unpair.1, e.unpair.2.unpair.2, hc.1, hc.2.1, hc.2.2, rfl⟩
    · rw [if_neg hc]
      exact ⟨0, 1, 0, Nat.zero_le n, hn, Nat.zero_lt_one, rfl⟩

/-- **The scheduled grid process is computable.** -/
lemma gridDP_computable : ComputableDeductiveProcess (L.gridDP) := by
  have hsorted : Computable (fun n =>
      Encodable.encode ((sentenceDedup ((List.range (Nat.pair n (Nat.pair n n) + 1)).map
        (L.gridEmit n))).insertionSort sentenceCodeLE)) :=
    Computable.encode.comp (sentenceInsertionSort_prim.to_comp.comp
      (sentenceDedup_prim.to_comp.comp (L.gridList_computable)))
  have henc : Computable (fun n => Encodable.encode ((L.gridDP).D n)) := by
    refine (Computable.nat_casesOn Computable.id
      (Computable.const (Encodable.encode (∅ : Finset Sentence)))
      (hsorted.comp Computable.fst).to₂).of_eq (fun n => ?_)
    cases n with
    | zero =>
        show Encodable.encode (∅ : Finset Sentence) = Encodable.encode (L.gridStage 0)
        rw [L.gridStage_zero]
    | succ k =>
        show Encodable.encode ((sentenceDedup _).insertionSort sentenceCodeLE)
          = Encodable.encode (L.gridStage (k + 1))
        rw [L.gridStage_eq_list_toFinset (Nat.succ_le_succ (Nat.zero_le k)),
          encode_toFinset_eq]
  obtain ⟨code, hcode⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp henc.partrec)
  refine ⟨code, fun n => ?_⟩
  rw [hcode]
  exact Part.mem_some _

section CombinedComputable
variable (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]

/-- **The combined process is computable** (union of the two computable stages). -/
lemma combinedDP_computable : ComputableDeductiveProcess (L.combinedDP T) := by
  have hgrid := (L.gridDP_computable).nonemptyComputation.some
  have hluv := (L.luvThresholdDP_computable T).nonemptyComputation.some
  exact (hgrid.union hluv).toComputable

end CombinedComputable

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
