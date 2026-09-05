import LogicalInduction.Construction.Witnesses.SemanticSource
import LogicalInduction.Construction.Witnesses.SemanticProduct
import LogicalInduction.Construction.Witnesses.SemanticQuote

/-!
# Joint semantic-source/product obstructions

Two proved obstructions that force explicit factor-schema ownership in the semantic-CCEE
lane.  Syntactic separation blocks the self-referential source diagonal, but it does not by
itself make a universal product closure jointly satisfiable with an interpreter for every
fresh emitter: product clauses require their factor leaves to behave as coherent rational
cuts, and neither freshness nor efficient emission secures that.  Both obstructions here
are finite, kernel-checked counterexamples; this module renders no paper node.

* `semanticProductDP_no_increasing_factor_assignment` is the core inconsistency: the
  universal product clauses cannot be satisfied by a factor family that is false at `0` and
  true at `1`, a pattern no genuine `[0,1]` rational cut has.
* `semanticFreshIncreasingLUVSeq` is the witness family — syntactically fresh
  (`semanticFreshIncreasingLUVSeq_fresh`) and efficiently emitted
  (`semanticFreshIncreasingLUVSeq_rpnThresholdCodeSeq`), yet malformed in exactly that way.
  `semanticFreshIncreasing_not_jointly_reflected` is the resulting obstruction.
* `theorem_quote_product_not_jointly_satisfiable`: `theoremDP`, `semanticQuoteDP` and a
  schema-unrestricted `semanticProductDP` have no joint completed world, because the quote
  interpreter interprets every partial-recursive Boolean selector while the product closure
  treats every schema as a factor.

`SemanticCertifiedProduct.lean` answers both by guarding product clauses on tag-`0` factor
ownership; `CertifiedSource.lean` consumes the fresh-family witness as the negative side of
its admission test.
-/

namespace LogicalInduction

open LO LO.Propositional LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

attribute [local irreducible] Nat.sqrt

/-! ## The malformed-factor obstruction -/

/-- The universal product clauses are inconsistent with factors that are false at zero
but true at one.  Genuine `[0,1]` cuts cannot have this pattern. -/
lemma semanticProductDP_no_increasing_factor_assignment {v : PCWorld}
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

/-! ## A fresh, efficiently emitted, malformed threshold family -/

/-- A syntactically fresh but malformed threshold family: false below one and true from
one upward.  It witnesses why a fixed interpreter cannot safely interpret every fresh
program and then feed all resulting schemas to the universal product closure. -/
def semanticFreshIncreasingLUVSeq (_ : ℕ) : LUV where
  gt r := if r < 1 then ⊥ else ⊤

@[simp] lemma semanticFreshIncreasingLUVSeq_gt (n : ℕ) (r : ℚ) :
    (semanticFreshIncreasingLUVSeq n).gt r = if r < 1 then ⊥ else ⊤ := rfl

/-- The family mentions no semantic-prime handle: both of its threshold formulas are
propositional constants.  This is the proof of the word *fresh* in the definition above. -/
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

/-- The family is efficiently emitted: its threshold literals are selected by the mesh
selector under a polynomial clock. -/
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
closure inconsistent.  The family is syntactically fresh
(`semanticFreshIncreasingLUVSeq_fresh`) and efficiently emitted
(`semanticFreshIncreasingLUVSeq_rpnThresholdCodeSeq`), and neither helps. -/
lemma semanticFreshIncreasing_not_jointly_reflected (Xhat : PresentedLUVSeq) :
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

/-! ## Quote and product ownership must also be separated

`semanticQuoteDP` deliberately interprets every partial-recursive Boolean selector, and such
a selector need not be a coherent LUV threshold family.  `semanticProductDP` ranges over
every schema number, so it treats quote schemas as product factors too.  The finite
contradiction below is why product clauses must be guarded by factor-schema ownership
(`SemanticCertifiedProduct.semanticCertifiedProductDP`).
-/

/-- The quote code of the decidable predicate "the input is the threshold query at `1`": a
perfectly legal Boolean selector whose reflected leaf family is not a coherent LUV threshold
family.  It is the witness in `theorem_quote_product_not_jointly_satisfiable`. -/
noncomputable def increasingQuoteCode (T : ArithmeticTheory)
    [𝗥₀ ⪯ T] : BooleanQuoteCode T
      (fun input => input = Nat.pair 0 (Encodable.encode (1 : ℚ))) :=
  BooleanQuoteCode.ofComputable
    ((Primrec.eq.comp Primrec.id
      (Primrec.const (Nat.pair 0 (Encodable.encode (1 : ℚ))))).computablePred)

/-- The unrestricted quote interpreter and unrestricted product interpreter have no joint
completed world, even together with the ordinary theorem process.  This is what forces
explicit factor-schema ownership on the product closure. -/
lemma theorem_quote_product_not_jointly_satisfiable
    (T : ArithmeticTheory) [T.Δ₁] [𝗥₀ ⪯ T] :
    ¬∃ v : PCWorld,
      v.ConsistentWithTheory (theoremDP T) ∧
      v.ConsistentWithTheory semanticQuoteDP ∧
      v.ConsistentWithTheory semanticProductDP := by
  rintro ⟨v, htheorem, hquote, hproduct⟩
  let q := increasingQuoteCode T
  let input0 := Nat.pair 0 (Encodable.encode (0 : ℚ))
  let input1 := Nat.pair 0 (Encodable.encode (1 : ℚ))
  have hq0 : ¬v.Holds (quoteAtom (Nat.pair q.code input0)) := by
    intro h
    have hfalse := (BooleanQuoteCode.reflected (quotationPresentation T) q input0 v htheorem).mp h
    simp [input0, input1] at hfalse
  have hq1 : v.Holds (quoteAtom (Nat.pair q.code input1)) :=
    (BooleanQuoteCode.reflected (quotationPresentation T) q input1 v htheorem).mpr (by rfl)
  have hzero : ¬v.Holds (semanticQuoteLeaf q.code input0) := by
    intro h
    exact hq0 ((semanticQuoteLeaf_reflected hquote q.code input0).mp h)
  have hone : v.Holds (semanticQuoteLeaf q.code input1) :=
    (semanticQuoteLeaf_reflected hquote q.code input1).mpr hq1
  exact semanticProductDP_no_increasing_factor_assignment hproduct
    (semanticQuoteSchema q.code) (semanticQuoteSchema q.code) 0
    (by simpa [semanticQuoteLeaf, input1] using hone)
    (by simpa [semanticQuoteLeaf, input1] using hone)
    (by simpa [semanticQuoteLeaf, input0] using hzero)
    (by simpa [semanticQuoteLeaf, input0] using hzero)

end LogicalInduction
