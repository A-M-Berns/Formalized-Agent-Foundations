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

/-- **Combination-level expectation provability induction** (`thm:loe` substrate).  A bounded
LUV-combination sequence that the completed theory determines to have value `0` in every
consistent world has diagonal expectation `≈ₙ 0`.  This is the paper's own route to linearity
(`app:loe`): apply `thm:expprovind` to the combination `aX+bY−Z` (valued `0` because
`Θ ⊢ Z = aX+bY`).  It runs on the combination's mesh via `affine_provind_theory_tendsto_zero`,
whose `ConsistentWithTheory` hypothesis is exactly what `ExactTheoryPresentation` (F7 Phase B)
supplies.
Paper node: `thm:loe` -/
theorem lic_expect_combination_provind_zero
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    (h : LUVCombination.BoundedSequence As P)
    (hexact : LUVCombination.ExactTheoryPresentation As DP)
    (hdet0 : ∀ n, (As n).value P (hexact.value n) = 0)
    (b : ℚ) (hshare : ∀ n, (As n).shareNorm P ≤ (b : ℝ))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (As n).expect P n) ≈ₙ (fun _ => 0) := by
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
      |((As n).meshAffine n).value P v.payout| ≤ ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt ((b : ℝ) / ε)
    filter_upwards [Filter.eventually_ge_atTop (max 1 N)] with n hn v hv
    have hn0 : 0 < n := by omega
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
    have hvals := hexact.valuesAt n v hv
    have hnear := (As n).meshAffine_value_near P v (hexact.value n) hn0 hvals
    rw [hdet0 n, _root_.sub_zero] at hnear
    have hb0 : 0 ≤ (b : ℝ) := le_trans ((As n).shareNorm_nonneg P) (hshare n)
    have hbound : (As n).shareNorm P * (1 / n) ≤ (b : ℝ) * (1 / n) :=
      mul_le_mul_of_nonneg_right (hshare n) (by positivity)
    have hlt : (b : ℝ) / ε < n :=
      hN.trans_le (by exact_mod_cast le_trans (le_max_right 1 N) hn)
    have hsmall : (b : ℝ) * (1 / n) ≤ ε := by
      rw [mul_one_div, div_le_iff₀ hnR]; nlinarith [(div_lt_iff₀ hε).mp hlt]
    linarith [hnear, hbound, hsmall]
  have hmesh := (h.poly.mesh_poly).affine_provind_theory_tendsto_zero P DP hbounded hmag hworld hval
  simpa only [LUVCombination.meshAffine_price_diagonal] using hmesh

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
/-- **Grid coherence from stage membership.**  A world consistent with stage `n` reads each
grid literal's polarity, so `⌜Xᵢ > j/n⌝` holds exactly when the threshold predicate does. -/
lemma holds_thresholdSentence_iff {v : PCWorld} {n : ℕ}
    (hv : v.ConsistentWith ((L.gridDP).D n)) {i j : ℕ} (hi : i ≤ n) (hj : j < n) :
    v.Holds (thresholdSentence i ((j : ℚ) / (n : ℚ)))
      ↔ L.ThresholdPred (thresholdCode i ((j : ℚ) / (n : ℚ))) := by
  have hmem : L.gridLiteral i j n ∈ (L.gridDP).D n := by
    rw [show (L.gridDP).D n = L.gridStage n from rfl, mem_gridStage]
    exact ⟨i, n, j, hi, le_rfl, hj, rfl⟩
  have hholds : v.Holds (L.gridLiteral i j n) := hv _ hmem
  unfold gridLiteral at hholds
  by_cases hp : L.ThresholdPred (thresholdCode i ((j : ℚ) / (n : ℚ)))
  · rw [if_pos hp] at hholds
    exact ⟨fun _ => hp, fun _ => hholds⟩
  · rw [if_neg hp, holds_not] at hholds
    exact ⟨fun h => absurd h hholds, fun h => absurd h hp⟩

/-- **The value-agreement discharge.**  For a world consistent with scheduled stage `n` and any
LUV index `i ≤ n`, the day-`n` approximate expectation of `Xᵢ` is within `1/n` of its standard
rational value — with no world-value hypothesis. -/
lemma expectApprox_near_gridDP {v : PCWorld} {n : ℕ} (hn : 0 < n)
    (hv : v.ConsistentWith ((L.gridDP).D n)) {i : ℕ} (hi : i ≤ n) :
    |(toLUV i).expectApprox v.payout n - (L.value i : ℝ)| ≤ 1 / n := by
  refine PCWorld.expectApprox_near_ofGrid (by exact_mod_cast L.value_nonneg i)
    (by exact_mod_cast L.value_le_one i) hn (fun j hj => ?_)
  have hiff := L.holds_thresholdSentence_iff hv hi hj
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
    (i : ℕ) (hcode : (toLUV i).PolyThresholdCodes)
    (hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1)
    (c : ℝ) (hc : c ≤ (L.value i : ℝ)) :
    AsympGE ((toLUV i).expectSeq P) (fun _ => c) :=
  lic_expectation_provind P (L.gridDP) (toLUV i) hcode hP L.gridDP_hcons c
    ((Filter.eventually_ge_atTop (max 1 i)).mono (fun n hin v hv =>
      ⟨(L.value i : ℝ), hc,
        L.expectApprox_near_gridDP (by omega) hv (by omega)⟩))

/-- Certified expectation provability induction, upper (`≤`) form.
Paper node: `thm:expprovind` -/
theorem lic_expectation_provind_le_arith (P : History) [IsLogicalInductor P (L.gridDP)]
    (i : ℕ) (hcode : (toLUV i).PolyThresholdCodes)
    (hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1)
    (c : ℝ) (hc : (L.value i : ℝ) ≤ c) :
    AsympLE ((toLUV i).expectSeq P) (fun _ => c) :=
  lic_expectation_provind_le P (L.gridDP) (toLUV i) hcode hP L.gridDP_hcons c
    ((Filter.eventually_ge_atTop (max 1 i)).mono (fun n hin v hv =>
      ⟨(L.value i : ℝ), hc, L.expectApprox_near_gridDP (by omega) hv (by omega)⟩))

/-- Certified expectation provability induction, equality (`=`) form: a determined
`dd:luv-arith` value forces the expectation sequence to it.
Paper node: `thm:expprovind` -/
theorem lic_expectation_provind_eq_arith (P : History) [IsLogicalInductor P (L.gridDP)]
    (i : ℕ) (hcode : (toLUV i).PolyThresholdCodes)
    (hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1)
    (c : ℝ) (hc : (L.value i : ℝ) = c) :
    AsympEq ((toLUV i).expectSeq P) (fun _ => c) :=
  lic_expectation_provind_eq P (L.gridDP) (toLUV i) hcode hP L.gridDP_hcons c
    ((Filter.eventually_ge_atTop (max 1 i)).mono (fun n hin v hv =>
      hc ▸ L.expectApprox_near_gridDP (by omega) hv (by omega)))

/-- **F7 item 5, certified linearity of expectation.**  Linearity for `dd:luv-arith` LUVs `Xᵢ`,
`Xⱼ`, `Xₖ`, with the world-value and linear-relation hypotheses discharged from arithmetic: the
sole content is the plain rational identity `valueₖ = a·valueᵢ + b·valueⱼ`.
Paper node: `thm:loe` -/
theorem lic_linearity_of_expectation_arith (P : History) [IsLogicalInductor P (L.gridDP)]
    (a b : ℚ) (i j k : ℕ)
    (hcodeI : (toLUV i).PolyThresholdCodes) (hcodeJ : (toLUV j).PolyThresholdCodes)
    (hcodeK : (toLUV k).PolyThresholdCodes)
    (hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1)
    (hlin : L.value k = a * L.value i + b * L.value j) :
    AsympEq (fun n => (a : ℝ) * (toLUV i).expect P n + (b : ℝ) * (toLUV j).expect P n)
      ((toLUV k).expectSeq P) :=
  lic_linearity_of_expectation P (L.gridDP) a b (toLUV i) (toLUV j) (toLUV k)
    hcodeI hcodeJ hcodeK hP L.gridDP_hcons
    ((Filter.eventually_ge_atTop (max 1 (max i (max j k)))).mono (fun n hin v hv =>
      ⟨(L.value i : ℝ), (L.value j : ℝ), (L.value k : ℝ), by exact_mod_cast hlin,
        L.expectApprox_near_gridDP (by omega) hv (by omega),
        L.expectApprox_near_gridDP (by omega) hv (by omega),
        L.expectApprox_near_gridDP (by omega) hv (by omega)⟩))

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
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1) :
    liminf (fun n => (As n).expect P n) atTop =
        liminf (LUVCombination.futureHigh As P) atTop ∧
      limsup (fun n => (As n).expect P n) atTop =
        limsup (LUVCombination.futureLow As P) atTop :=
  h.exppolymax ops (L.worldValued_ofArithmetic (L.luvArithmeticPresentation T) As hAs)
    b hb hshare hP (L.luvThresholdDP_hworld T)

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
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (emit : AffineCombination.FeedbackTraderEmissionSigns
      (h.normalizedMesh_poly b) hWgen hstrict)
    (bridge : AffineCombination.FeedbackTruthSequence
      (LUVCombination.normalizedMesh As b)
      (LUVCombination.normalizedMeshTruth As P (L.luvThresholdDP T)
        (L.luvThresholdDP_hworld T) b) P (L.luvThresholdDP T) f) :
    weightedBias (fun i => (W i).denote P)
      (fun i => (As i).expect P i) truth ≈ₙ (fun _ => 0) :=
  h.wubexp (L.exactTheoryPresentation_ofArithmetic (L.luvArithmeticPresentation T) As hAs)
    hdet b hshare hWgen hWdiv hstrict hsupport hP (L.luvThresholdDP_hworld T) emit bridge

end ComputableLUV

end LogicalInduction
