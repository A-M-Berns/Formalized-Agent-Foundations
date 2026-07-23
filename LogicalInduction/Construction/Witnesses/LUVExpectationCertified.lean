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

end ComputableLUV

end LogicalInduction
