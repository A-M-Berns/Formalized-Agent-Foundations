import LogicalInduction.Construction.Witnesses.SemanticSource
import LogicalInduction.Construction.Witnesses.SemanticProduct

/-!
# Joint semantic-source/product stress tests

Syntactic separation blocks the self-referential source diagonal, but it does not by
itself make the existing universal product closure jointly satisfiable with an interpreter
for every fresh emitter.  Product clauses require their factor leaves to behave as
coherent rational cuts.  This file gives the finite, kernel-checked counterexample.
-/

namespace LogicalInduction

open LO LO.Propositional

attribute [local irreducible] Nat.sqrt

/-- The universal product clauses are inconsistent with factors that are false at zero
but true at one.  Genuine `[0,1]` cuts cannot have this pattern. -/
theorem semanticProductDP_no_increasing_factor_assignment {v : PCWorld}
    (hv : v.ConsistentWithTheory semanticProductDP) (left right n : ℕ)
    (hleftOne : v.Holds (semanticPrimeSentence left
      (Nat.pair n (Encodable.encode (1 : ℚ)))))
    (hrightOne : v.Holds (semanticPrimeSentence right
      (Nat.pair n (Encodable.encode (1 : ℚ)))))
    (hleftZero : ¬v.Holds (semanticPrimeSentence left
      (Nat.pair n (Encodable.encode (0 : ℚ)))))
    (hrightZero : ¬v.Holds (semanticPrimeSentence right
      (Nat.pair n (Encodable.encode (0 : ℚ))))) : False := by
  obtain ⟨z0, hz0⟩ := exists_meshIndexRat (show (0 : ℚ) ≤ 0 by norm_num)
  obtain ⟨z1, hz1⟩ := exists_meshIndexRat (show (0 : ℚ) ≤ 1 by norm_num)
  have hprod : v.Holds (semanticProductAtom left right n 1) :=
    holds_semanticProduct_pos hv left right n (zs := z1) (zt := z1)
      (by rw [hz1]; norm_num)
      (by simpa only [hz1] using hleftOne)
      (by simpa only [hz1] using hrightOne)
  have hnprod : ¬v.Holds (semanticProductAtom left right n 1) :=
    not_holds_semanticProduct_neg hv left right n (zs := z0) (zt := z0)
      (by rw [hz0]; norm_num)
      (by simpa only [hz0] using hleftZero)
      (by simpa only [hz0] using hrightZero)
  exact hnprod hprod

/-- A syntactically fresh but malformed threshold family: false below one and true from
one upward.  It witnesses why a fixed interpreter cannot safely interpret every fresh
program and then feed all resulting schemas to the universal product closure. -/
def semanticFreshIncreasingLUVSeq (_ : ℕ) : LUV where
  gt r := if r < 1 then ⊥ else ⊤

@[simp] lemma semanticFreshIncreasingLUVSeq_gt (n : ℕ) (r : ℚ) :
    (semanticFreshIncreasingLUVSeq n).gt r = if r < 1 then ⊥ else ⊤ := rfl

lemma semanticFreshIncreasingLUVSeq_fresh :
    SemanticPrimeFreshLUVSeq semanticFreshIncreasingLUVSeq := by
  intro n r a ha
  by_cases hr : r < 1
  · rw [semanticFreshIncreasingLUVSeq_gt, if_pos hr] at ha
    change a ∈ sentenceAtomCodes (⊥ : Sentence) at ha
    simp at ha
  · rw [semanticFreshIncreasingLUVSeq_gt, if_neg hr] at ha
    change a ∈ sentenceAtomCodes (⊤ : Sentence) at ha
    simp at ha

lemma semanticFreshIncreasingLUVSeq_rpnThresholdCodeSeq :
    LUV.RpnThresholdCodeSeq semanticFreshIncreasingLUVSeq := by
  obtain ⟨c, hc⟩ := semanticValuedDiagonalMeshSelector_polyFueled
  have h := RpnSentenceCodes.ifZero (RpnSentenceCodes.const (⊥ : Sentence))
    (RpnSentenceCodes.const (⊤ : Sentence)) hc
  refine h.of_eq (fun m => ?_)
  rw [semanticFreshIncreasingLUVSeq_gt]
  by_cases hk0 : m.unpair.2.unpair.1 = 0
  · simp [semanticValuedDiagonalMeshSelector, hk0, ifzSelFn]
  · by_cases hi : m.unpair.2.unpair.2 < m.unpair.2.unpair.1
    · have hsub : m.unpair.2.unpair.2 + 1 - m.unpair.2.unpair.1 = 0 := by omega
      have hrat : (m.unpair.2.unpair.2 : ℚ) /
          (m.unpair.2.unpair.1 : ℚ) < 1 := by
        rw [div_lt_one (by exact_mod_cast Nat.pos_of_ne_zero hk0)]
        exact_mod_cast hi
      simp [semanticValuedDiagonalMeshSelector, hk0, hsub, hrat, ifzSelFn]
    · have hsub : 0 < m.unpair.2.unpair.2 + 1 - m.unpair.2.unpair.1 := by omega
      have hrat : ¬(m.unpair.2.unpair.2 : ℚ) /
          (m.unpair.2.unpair.1 : ℚ) < 1 := by
        rw [not_lt, one_le_div (by exact_mod_cast Nat.pos_of_ne_zero hk0)]
        exact_mod_cast (Nat.le_of_not_gt hi)
      simp [semanticValuedDiagonalMeshSelector, hk0, hsub.ne', hrat, ifzSelFn]

/-- Freshness plus efficient emission is not sufficient for joint source/product
non-vacuity: exact reflection of the fresh malformed source makes the fixed product
closure inconsistent. -/
theorem semanticFreshIncreasing_not_jointly_reflected (Xhat : PresentedLUVSeq) :
    ¬∃ v : PCWorld, v.ConsistentWithTheory semanticProductDP ∧
      ∀ n r, v.Holds ((Xhat.toLUV n).gt r) ↔
        v.Holds ((semanticFreshIncreasingLUVSeq n).gt r) := by
  rintro ⟨v, hv, hreflect⟩
  have hzero : ¬v.Holds (semanticPrimeSentence Xhat.thresholdSchema
      (Nat.pair 0 (Encodable.encode (0 : ℚ)))) := by
    rw [← PresentedLUVSeq.gt_eq]
    have h := hreflect 0 0
    simpa [semanticFreshIncreasingLUVSeq_gt, PCWorld.Holds,
      LO.Propositional.Formula.Boolean.val] using not_congr h
  have hone : v.Holds (semanticPrimeSentence Xhat.thresholdSchema
      (Nat.pair 0 (Encodable.encode (1 : ℚ)))) := by
    rw [← PresentedLUVSeq.gt_eq]
    exact (hreflect 0 1).mpr (by
      simp [semanticFreshIncreasingLUVSeq_gt, PCWorld.Holds,
        LO.Propositional.Formula.Boolean.val])
  exact semanticProductDP_no_increasing_factor_assignment hv
    Xhat.thresholdSchema Xhat.thresholdSchema 0 hone hone hzero hzero

#print axioms semanticProductDP_no_increasing_factor_assignment
#print axioms semanticFreshIncreasingLUVSeq_rpnThresholdCodeSeq
#print axioms semanticFreshIncreasing_not_jointly_reflected

end LogicalInduction
