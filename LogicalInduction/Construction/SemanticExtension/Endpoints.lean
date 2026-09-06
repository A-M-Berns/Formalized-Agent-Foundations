import LogicalInduction.Construction.SemanticExtension.LanguageCopy
import LogicalInduction.Construction.SemanticExtension.Registry

/-!
# `thm:ccee` in generalized semantic-extension form

This module renders `thm:ccee` at zero slack over the canonical lifted-language process
`canonicalCCEEDP T`.  The paper rendering of the node is
`lic_no_expected_net_update_conditional_paperLUV_closed`
(`Construction/Quotation/ExactCCEE.lean`), priced on the single market
`liaHistory (paperDP T)`; the endpoint here is the one canonical endpoint priced outside
that market.

What the generalized form buys is a wider input class — an abstract threshold-only source
`X : ℕ → LUV` with `LUV.RpnThresholdCodeSeq X`, which the literal-`PaperLUVSeq` rendering
does not reach.  What it costs is pricing on a different, fixed enlarged language.

Objects defined: `liftedCCEEBaseDP` (the quotation base together with an independent
renamed copy of the theorem stream) with its computation and world; `canonicalCCEEDP` (its
semantic registry closure) with `canonicalCCEEDPComputation`,
`canonicalCCEEMarketComputation`, and the two internally constructed quote codes
`canonicalDeferredWeightQuoteCode` and `canonicalConditionalExpectationQuoteCode`.

Non-vacuity holds on both sides: `liftedCCEEBaseWorld_hworld` and `canonicalCCEEDP_hworld`
give the process an explicit completed world, and `canonicalCCEE_weight_nonvacuous`
exhibits the harmonic weight `n ↦ 1/(n+1)` as `[0,1]`-valued, ℙ‾-generable against every
market, and not constant.

The fixed-before-choice discipline: the old-language copy and every semantic registry are
fixed from `T` alone — before a source `X`, market, deferral `f`, or weight `w` is
selected.  No axiom identifies the copied vocabulary with the original.

One binder asymmetry is deliberate mathematics rather than an oversight: `source_valued`
is quantified over worlds consistent with `theoremDP T`, a *smaller* process than
`canonicalCCEEDP T`, hence over a **superset** of worlds — a stronger premise on the
caller, and the form the proof consumes.

Consumers: `AxiomAudit.lean` inventories all nine `Paper node: thm:ccee` declarations of this
module — `liftedCCEEBaseDP_computable`, `liftedCCEEBaseWorld_hworld`,
`canonicalCCEEDP_computable`, `canonicalCCEEDP_hworld`, `liftedRpnSemanticHandle_valuesAt`,
`liftedRpnSource_factor_eventually`, `canonicalRationalQuote_factor_eventually`,
`canonicalCCEE_weight_nonvacuous` and
`lic_no_expected_net_update_conditional_exact_canonical`; the `thm:ccee` row of
`scripts/coverage-classification.md` records the two-rendering split.
-/

namespace LogicalInduction

open LO LO.Propositional LO.FirstOrder LO.FirstOrder.Arithmetic
open Classical

/-! ## The lifted quotation base -/

/-- The quotation base together with an independent renamed copy of the theorem stream. -/
noncomputable def liftedCCEEBaseDP
    (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T]
    [Entailment.Consistent T] : DeductiveProcess :=
  (theoremQuoteBaseDP T).union (liftDP (theoremDP T))

/-- A computation for the lifted quotation base: the quotation base's own computation
unioned with a lifted copy of the theorem process's. -/
noncomputable def liftedCCEEBaseDPComputation
    (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T]
    [Entailment.Consistent T] :
    DeductiveProcessComputation (liftedCCEEBaseDP T) :=
  (theoremQuoteBaseDPComputation T).union
    (liftDPComputation ((theoremDP_computable T).nonemptyComputation.some))

/-- The fixed original/renamed quotation base is computable.

Paper node: `thm:ccee` -/
lemma liftedCCEEBaseDP_computable
    (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T]
    [Entailment.Consistent T] :
    ComputableDeductiveProcess (liftedCCEEBaseDP T) :=
  (liftedCCEEBaseDPComputation T).toComputable

/-- Independent model copies for the original quotation substrate and renamed theorem
substrate. -/
noncomputable def liftedCCEEBaseWorld (T : ArithmeticTheory) : PCWorld := fun a =>
  if a.unpair.1 = oldLanguageTag then
    provabilityWorld T a.unpair.2
  else theoremQuoteCertifiedProductWorld T a

lemma liftedCCEEBaseWorld_agree_original (T : ArithmeticTheory) {a : ℕ}
    (ha : a.unpair.1 ≠ oldLanguageTag) :
    liftedCCEEBaseWorld T a ↔ theoremQuoteCertifiedProductWorld T a := by
  simp [liftedCCEEBaseWorld, ha]

@[simp] lemma liftedCCEEBaseWorld_oldAtom (T : ArithmeticTheory) (a : ℕ) :
    liftedCCEEBaseWorld T (oldAtom a) ↔ provabilityWorld T a := by
  simp [liftedCCEEBaseWorld, oldAtom]

/-! ## Its completed world -/

/-- A quotation leaf is read the same way in the lifted base world as in the certified
product world it copies. -/
lemma liftedCCEEBaseWorld_quoteLeaf (T : ArithmeticTheory) (code input : ℕ) :
    (liftedCCEEBaseWorld T).Holds (semanticQuoteLeaf code input) ↔
      (theoremQuoteCertifiedProductWorld T).Holds (semanticQuoteLeaf code input) := by
  change liftedCCEEBaseWorld T (semanticPrimeCode (semanticQuoteSchema code) input) ↔ _
  apply liftedCCEEBaseWorld_agree_original
  simp [semanticPrimeCode, oldLanguageTag, semanticPrimeTag]

/-- The same for a quotation atom. -/
lemma liftedCCEEBaseWorld_quoteAtom (T : ArithmeticTheory) (w : ℕ) :
    (liftedCCEEBaseWorld T).Holds (quoteAtom w) ↔
      (theoremQuoteCertifiedProductWorld T).Holds (quoteAtom w) := by
  change liftedCCEEBaseWorld T
      (quotationClaimCode universalQuotePos universalQuoteNeg w) ↔ _
  apply liftedCCEEBaseWorld_agree_original
  simp [quotationClaimCode, oldLanguageTag]

/-- **Quotation agreement is determined leafwise**: two worlds that agree on every
quotation leaf and every quotation atom agree on every quotation definition sentence.
Both world layers below are compared through this one lemma. -/
private lemma semanticQuoteDefSentence_congr {w₁ w₂ : PCWorld}
    (hleaf : ∀ code input, w₁.Holds (semanticQuoteLeaf code input) ↔
      w₂.Holds (semanticQuoteLeaf code input))
    (hatom : ∀ z, w₁.Holds (quoteAtom z) ↔ w₂.Holds (quoteAtom z)) (e : ℕ) :
    w₁.Holds (semanticQuoteDefSentence e) ↔ w₂.Holds (semanticQuoteDefSentence e) := by
  unfold semanticQuoteDefSentence
  by_cases hkind : e.unpair.1 = 0
  · rw [if_pos hkind]
    exact imp_congr (hatom _) (hleaf _ _)
  · rw [if_neg hkind]
    exact imp_congr (hleaf _ _) (hatom _)

/-- Quotation definition sentences agree between the lifted base world and the certified
product world. -/
lemma liftedCCEEBaseWorld_semanticQuoteDefSentence_iff
    (T : ArithmeticTheory) (e : ℕ) :
    (liftedCCEEBaseWorld T).Holds (semanticQuoteDefSentence e) ↔
      (theoremQuoteCertifiedProductWorld T).Holds (semanticQuoteDefSentence e) :=
  semanticQuoteDefSentence_congr (liftedCCEEBaseWorld_quoteLeaf T)
    (liftedCCEEBaseWorld_quoteAtom T) e

set_option maxHeartbeats 2000000 in
lemma liftedCCEEBaseWorld_consistent_theorem
    (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T]
    [Entailment.Consistent T] :
    (liftedCCEEBaseWorld T).ConsistentWithTheory (theoremDP T) := by
  intro k phi hphi
  apply (PCWorld.holds_congr_atomCodes phi (fun a ha =>
    liftedCCEEBaseWorld_agree_original T
      (theoremDP_oldLanguageFresh T k phi hphi a ha))).mpr
  exact theoremQuoteCertifiedProductWorld_consistent_theorem T k phi hphi

set_option maxHeartbeats 2000000 in
lemma liftedCCEEBaseWorld_consistent_quote
    (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T]
    [Entailment.Consistent T] :
    (liftedCCEEBaseWorld T).ConsistentWithTheory semanticQuoteDP := by
  intro k phi hphi
  obtain ⟨e, rfl⟩ := exists_of_mem_semanticQuoteStageList
    (List.mem_toFinset.mp hphi)
  exact (liftedCCEEBaseWorld_semanticQuoteDefSentence_iff T e).mpr
    (theoremQuoteCertifiedProductWorld_consistent_quote T e _
      (List.mem_toFinset.mpr (mem_semanticQuoteStageList (le_refl e))))

set_option maxHeartbeats 2000000 in
lemma liftedCCEEBaseWorld_consistent_lifted
    (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T]
    [Entailment.Consistent T] :
    (liftedCCEEBaseWorld T).ConsistentWithTheory (liftDP (theoremDP T)) := by
  rw [consistentWithTheory_liftDP_iff]
  have hpull : pullOldWorld (liftedCCEEBaseWorld T) = provabilityWorld T := by
    funext a
    apply propext
    exact liftedCCEEBaseWorld_oldAtom T a
  rw [hpull]
  exact theoremDP_hworld T

set_option maxHeartbeats 2000000 in
/-- The independent original/lifted base has a completed world.

Paper node: `thm:ccee` -/
lemma liftedCCEEBaseWorld_hworld
    (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T]
    [Entailment.Consistent T] :
    (liftedCCEEBaseWorld T).ConsistentWithTheory (liftedCCEEBaseDP T) := by
  intro k phi hphi
  rw [liftedCCEEBaseDP, DeductiveProcess.union_stage, Finset.mem_union,
    theoremQuoteBaseDP, DeductiveProcess.union_stage, Finset.mem_union] at hphi
  rcases hphi with (htheorem | hquote) | hlift
  · exact liftedCCEEBaseWorld_consistent_theorem T k phi htheorem
  · exact liftedCCEEBaseWorld_consistent_quote T k phi hquote
  · exact liftedCCEEBaseWorld_consistent_lifted T k phi hlift

/-! ## The canonical CCEE process -/

/-- The single deductive process this file's `thm:ccee` endpoint prices against, fixed from
`T` alone — before any source `X`, deferral `f`, or weight `w` is chosen — as the semantic
registry closure of the lifted quotation base.  It is **not** the process of the repo's
main construction: the single market every other market-bearing canonical endpoint reads is
`liaHistory (paperDP T)`, and
`lic_no_expected_net_update_conditional_exact_canonical` is the one canonical endpoint
priced outside it.  The paper rendering of `thm:ccee` lives on `paperDP` instead
(`lic_no_expected_net_update_conditional_paperLUV_closed`,
`Construction/Quotation/ExactCCEE.lean`). -/
noncomputable def canonicalCCEEDP
    (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T]
    [Entailment.Consistent T] : DeductiveProcess :=
  semanticRegistryClosureDP (liftedCCEEBaseDPComputation T)

/-- A computation for the canonical CCEE process, obtained from the base computation by
the registry closure. -/
noncomputable def canonicalCCEEDPComputation
    (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T]
    [Entailment.Consistent T] :
    DeductiveProcessComputation (canonicalCCEEDP T) :=
  semanticRegistryClosureDPComputation (liftedCCEEBaseDPComputation T)

/-- The single process used by exact CCEE is computable.

Paper node: `thm:ccee` -/
lemma canonicalCCEEDP_computable
    (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T]
    [Entailment.Consistent T] :
    ComputableDeductiveProcess (canonicalCCEEDP T) :=
  (canonicalCCEEDPComputation T).toComputable

/-! ## The canonical joint world -/

/-- The joint world of the canonical process: the source extension of the lifted base
world, further extended by the registry-admitted product clauses. -/
private noncomputable abbrev canonicalCCEEWorld
    (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T]
    [Entailment.Consistent T] : PCWorld :=
  semanticRegistryProductExtensionWorld (liftedCCEEBaseDPComputation T)
    (semanticSourceExtensionWorld (liftedCCEEBaseWorld T))

set_option maxHeartbeats 2000000 in
lemma canonicalCCEEWorld_quoteLeaf
    (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T]
    [Entailment.Consistent T] (code input : ℕ) :
    (canonicalCCEEWorld T).Holds (semanticQuoteLeaf code input) ↔
      (liftedCCEEBaseWorld T).Holds (semanticQuoteLeaf code input) := by
  change (semanticRegistryProductExtensionWorld (liftedCCEEBaseDPComputation T)
    (semanticSourceExtensionWorld (liftedCCEEBaseWorld T))).Holds
      (semanticPrimeSentence (semanticQuoteSchema code) input) ↔ _
  rw [semanticRegistryProductExtensionWorld_leaf
    (liftedCCEEBaseDPComputation T)
    (semanticSourceExtensionWorld (liftedCCEEBaseWorld T))
    (semanticQuoteSchema code) input (by simp [semanticQuoteSchema])]
  exact semanticSourceExtensionWorld_leaf_other (liftedCCEEBaseWorld T)
    (semanticQuoteSchema code) input (by simp [semanticQuoteSchema])

set_option maxHeartbeats 2000000 in
lemma canonicalCCEEWorld_quoteAtom
    (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T]
    [Entailment.Consistent T] (w : ℕ) :
    (canonicalCCEEWorld T).Holds (quoteAtom w) ↔
      (liftedCCEEBaseWorld T).Holds (quoteAtom w) := by
  change semanticRegistryProductExtensionWorld (liftedCCEEBaseDPComputation T)
      (semanticSourceExtensionWorld (liftedCCEEBaseWorld T))
        (quotationClaimCode universalQuotePos universalQuoteNeg w) ↔ _
  rw [semanticRegistryProductExtensionWorld_agree]
  · apply semanticSourceExtensionWorld_agree
    simp [quotationClaimCode, semanticPrimeTag]
  · simp [quotationClaimCode, semanticPrimeTag]

/-- Quotation definition sentences agree between the canonical joint world and the lifted
base world it extends. -/
lemma canonicalCCEEWorld_semanticQuoteDefSentence_iff
    (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T]
    [Entailment.Consistent T] (e : ℕ) :
    (canonicalCCEEWorld T).Holds (semanticQuoteDefSentence e) ↔
      (liftedCCEEBaseWorld T).Holds (semanticQuoteDefSentence e) :=
  semanticQuoteDefSentence_congr (canonicalCCEEWorld_quoteLeaf T)
    (canonicalCCEEWorld_quoteAtom T) e

set_option maxHeartbeats 2000000 in
lemma canonicalCCEEWorld_consistent_quote
    (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T]
    [Entailment.Consistent T] :
    (canonicalCCEEWorld T).ConsistentWithTheory semanticQuoteDP := by
  intro k phi hphi
  obtain ⟨e, rfl⟩ := exists_of_mem_semanticQuoteStageList
    (List.mem_toFinset.mp hphi)
  exact (canonicalCCEEWorld_semanticQuoteDefSentence_iff T e).mpr
    (liftedCCEEBaseWorld_consistent_quote T e _
      (List.mem_toFinset.mpr (mem_semanticQuoteStageList (le_refl e))))

set_option maxHeartbeats 2000000 in
/-- The full fixed CCEE process has a completed world.

Paper node: `thm:ccee` -/
lemma canonicalCCEEDP_hworld
    (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T]
    [Entailment.Consistent T] :
    (canonicalCCEEWorld T).ConsistentWithTheory (canonicalCCEEDP T) := by
  intro k phi hphi
  rw [canonicalCCEEDP, semanticRegistryClosureDP,
    DeductiveProcess.union_stage, Finset.mem_union,
    DeductiveProcess.union_stage, Finset.mem_union] at hphi
  rcases hphi with (hbase | hsource) | hproduct
  · rw [liftedCCEEBaseDP, DeductiveProcess.union_stage, Finset.mem_union,
      theoremQuoteBaseDP, DeductiveProcess.union_stage, Finset.mem_union] at hbase
    rcases hbase with (htheorem | hquote) | hlift
    · have hfresh := theoremDP_semanticPrimeFresh T k phi htheorem
      exact (semanticRegistryProductExtensionWorld_holds_fresh
        (liftedCCEEBaseDPComputation T)
        (semanticSourceExtensionWorld (liftedCCEEBaseWorld T)) hfresh).mpr
          ((semanticSourceExtensionWorld_holds_fresh (liftedCCEEBaseWorld T) hfresh).mpr
            (liftedCCEEBaseWorld_consistent_theorem T k phi htheorem))
    · exact canonicalCCEEWorld_consistent_quote T k phi hquote
    · have hfresh : SemanticPrimeFreshSentence phi := by
        intro a ha htag
        change phi ∈ ((theoremDP T).D k).image liftSentence at hlift
        rw [Finset.mem_image] at hlift
        obtain ⟨psi, _, rfl⟩ := hlift
        rw [sentenceAtomCodes_liftSentence] at ha
        obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp ha
        simp [oldAtom, oldLanguageTag, semanticPrimeTag] at htag
      exact (semanticRegistryProductExtensionWorld_holds_fresh
        (liftedCCEEBaseDPComputation T)
        (semanticSourceExtensionWorld (liftedCCEEBaseWorld T)) hfresh).mpr
          ((semanticSourceExtensionWorld_holds_fresh (liftedCCEEBaseWorld T) hfresh).mpr
            (liftedCCEEBaseWorld_consistent_lifted T k phi hlift))
  · obtain ⟨e, rfl⟩ := semanticSourceStageList_exists
      (List.mem_toFinset.mp hsource)
    exact semanticRegistryProductExtensionWorld_holds_sourceDef
      (liftedCCEEBaseDPComputation T) (liftedCCEEBaseWorld T) e
  · exact semanticRegistryProductDP_hworld (liftedCCEEBaseDPComputation T)
      (liftedCCEEBaseWorld T) (liftedCCEEBaseWorld_hworld T) k phi hproduct

private lemma canonicalCCEE_consistent_base
    {T : ArithmeticTheory} [T.Δ₁] [𝗣𝗔⁻ ⪯ T]
    [Entailment.Consistent T] {v : PCWorld}
    (hv : v.ConsistentWithTheory (canonicalCCEEDP T)) :
    v.ConsistentWithTheory (liftedCCEEBaseDP T) :=
  PCWorld.consistentWithTheory_union_left
    (PCWorld.consistentWithTheory_union_left hv)

private lemma canonicalCCEE_consistent_source
    {T : ArithmeticTheory} [T.Δ₁] [𝗣𝗔⁻ ⪯ T]
    [Entailment.Consistent T] {v : PCWorld}
    (hv : v.ConsistentWithTheory (canonicalCCEEDP T)) :
    v.ConsistentWithTheory semanticSourceDP :=
  PCWorld.consistentWithTheory_union_right
    (PCWorld.consistentWithTheory_union_left hv)

private lemma canonicalCCEE_consistent_product
    {T : ArithmeticTheory} [T.Δ₁] [𝗣𝗔⁻ ⪯ T]
    [Entailment.Consistent T] {v : PCWorld}
    (hv : v.ConsistentWithTheory (canonicalCCEEDP T)) :
    v.ConsistentWithTheory
      (semanticRegistryProductDP (liftedCCEEBaseDPComputation T)) :=
  PCWorld.consistentWithTheory_union_right hv

private lemma canonicalCCEE_consistent_lifted
    {T : ArithmeticTheory} [T.Δ₁] [𝗣𝗔⁻ ⪯ T]
    [Entailment.Consistent T] {v : PCWorld}
    (hv : v.ConsistentWithTheory (canonicalCCEEDP T)) :
    v.ConsistentWithTheory (liftDP (theoremDP T)) :=
  PCWorld.consistentWithTheory_union_right (canonicalCCEE_consistent_base hv)

private lemma canonicalCCEE_consistent_theorem
    {T : ArithmeticTheory} [T.Δ₁] [𝗣𝗔⁻ ⪯ T]
    [Entailment.Consistent T] {v : PCWorld}
    (hv : v.ConsistentWithTheory (canonicalCCEEDP T)) :
    v.ConsistentWithTheory (theoremDP T) :=
  PCWorld.consistentWithTheory_union_left
    (PCWorld.consistentWithTheory_union_left (canonicalCCEE_consistent_base hv))

private lemma canonicalCCEE_consistent_quote
    {T : ArithmeticTheory} [T.Δ₁] [𝗣𝗔⁻ ⪯ T]
    [Entailment.Consistent T] {v : PCWorld}
    (hv : v.ConsistentWithTheory (canonicalCCEEDP T)) :
    v.ConsistentWithTheory semanticQuoteDP :=
  PCWorld.consistentWithTheory_union_right
    (PCWorld.consistentWithTheory_union_left (canonicalCCEE_consistent_base hv))

/-! ## Admitting the source as an exact factor -/

set_option maxHeartbeats 2000000 in
/-- Exact values of the internally represented source handle.

Paper node: `thm:ccee` -/
lemma liftedRpnSemanticHandle_valuesAt {X : ℕ → LUV}
    (hX : LUV.RpnThresholdCodeSeq X) (n : ℕ) (v : PCWorld) (x : ℝ)
    (hsource : v.ConsistentWithTheory semanticSourceDP)
    (hx : v.ValuesAt (liftLUV (X n)) x) :
    v.ValuesAt (semanticHandleLUVSeq
      (liftedRpnSourceSchema hX) n) x := by
  refine ⟨hx.1, hx.2.1, fun r => ⟨?_, ?_⟩⟩
  · intro hr
    rw [semanticHandleLUVSeq_gt]
    apply (liftedRpnSource_reflected hX n r v hsource).2
    by_cases hr0 : r < 0
    · rw [liftedRpnSourceSentence, if_pos hr0]
      exact PCWorld.holds_top v
    · simpa [liftedRpnSourceSentence, hr0, liftLUV] using (hx.2.2 r).1 hr
  · intro hr hleaf
    rw [semanticHandleLUVSeq_gt] at hleaf
    have hemitted := (liftedRpnSource_reflected hX n r v hsource).1 hleaf
    by_cases hr0 : r < 0
    · exfalso
      exact (not_lt_of_ge hx.1) (lt_trans hr (by exact_mod_cast hr0))
    · exact (hx.2.2 r).2 hr (by
        simpa [liftedRpnSourceSentence, hr0, liftLUV] using hemitted)

set_option maxHeartbeats 2000000 in
/-- Every paper-facing valued RPN source is automatically admitted by the fixed registry.

Paper node: `thm:ccee` -/
lemma liftedRpnSource_factor_eventually
    (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T]
    [Entailment.Consistent T]
    {X : ℕ → LUV} (hX : LUV.RpnThresholdCodeSeq X)
    (source_valued : ∀ n (v : PCWorld),
      v.ConsistentWithTheory (theoremDP T) → ∃ x, v.ValuesAt (X n) x)
    (limit : ℕ) :
    ∃ fuel, semanticFactorPrefixValidAtFuel (liftedCCEEBaseDPComputation T)
      (liftedRpnSourceSchema hX) limit fuel = true := by
  obtain ⟨fuel, hfuel⟩ := liftedRpnSourcePrefix_eventually_valid
    (liftedCCEEBaseDPComputation T) hX source_valued
    (fun _ hv => PCWorld.consistentWithTheory_union_right hv) limit
  refine ⟨fuel, ?_⟩
  simp [semanticFactorPrefixValidAtFuel, liftedRpnSourceSchema_source,
    hfuel]

set_option maxHeartbeats 2000000 in
/-- Every internally constructed rational quote is admitted as an exact product factor.

Paper node: `thm:ccee` -/
lemma canonicalRationalQuote_factor_eventually
    (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T]
    [Entailment.Consistent T]
    {value : ℕ → ℚ} (q : RationalQuoteCode T value) (limit : ℕ) :
    ∃ fuel, semanticFactorPrefixValidAtFuel (liftedCCEEBaseDPComputation T)
      (semanticQuoteSchema q.code) limit fuel = true := by
  obtain ⟨fuel, hfuel⟩ :=
    rationalQuote_semanticQuoteFactorPrefix_eventually_of_subprocess T
      (liftedCCEEBaseDPComputation T)
      (fun _ _ h => Finset.mem_union_left _ h) q limit
  refine ⟨fuel, ?_⟩
  rw [semanticFactorPrefixValidAtFuel,
    if_neg (by simp [semanticQuoteSchema]), if_pos (by simp [semanticQuoteSchema])]
  simpa only [semanticQuoteSchema] using hfuel

/-- The canonical process's own LIA market is a logical inductor over it. -/
private noncomputable abbrev canonicalCCEELIA
    (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T]
    [Entailment.Consistent T] :
    IsLogicalInductor (liaHistory (canonicalCCEEDP T)) (canonicalCCEEDP T) :=
  LIA_is_logical_inductor _ (canonicalCCEEDPComputation T).toComputable

/-- The market computation of the LIA market over `canonicalCCEEDP T`, which the two
quote codes below are built against. -/
noncomputable def canonicalCCEEMarketComputation
    (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T]
    [Entailment.Consistent T] :
    MarketComputation (liaHistory (canonicalCCEEDP T)) :=
  liaMarketComputation (canonicalCCEEDP T) (canonicalCCEEDPComputation T).toComputable

/-! ## Internally constructed weight and expectation quotations -/

/-- The internally constructed quotation of the deferred weight `n ↦ w (f n)`: the caller
supplies only the weight, not a quotation of it. -/
noncomputable def canonicalDeferredWeightQuoteCode
    (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T]
    [Entailment.Consistent T]
    (f : DeferralFunction) (w : ℕ → ℚ)
    (hw : PGenerableRat (liaHistory (canonicalCCEEDP T)) w)
    (weight_mem : ∀ n, 0 ≤ w n ∧ w n ≤ 1) :
    RationalQuoteCode T (fun n => w (f n)) :=
  deferredWeightQuoteCode T (canonicalCCEEMarketComputation T)
    f w hw weight_mem

/-- The internally constructed quotation of the deferred conditional expectation
`n ↦ 𝔼[schema | f n] · w (f n)`, the right-hand side of the endpoint's conclusion. -/
noncomputable def canonicalConditionalExpectationQuoteCode
    (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T]
    [Entailment.Consistent T]
    (f : DeferralFunction) (schema : ℕ) (w : ℕ → ℚ)
    (hw : PGenerableRat (liaHistory (canonicalCCEEDP T)) w)
    (weight_mem : ∀ n, 0 ≤ w n ∧ w n ≤ 1) :
    RationalQuoteCode T (fun n =>
      (canonicalCCEEMarketComputation T).expectQuoteAt
        (semanticHandleLUVSeq schema) n (f n) * w (f n)) :=
  conditionalExpectationQuoteCode T (canonicalCCEEMarketComputation T)
    f (semanticHandleLUVSeq schema)
    (semanticHandleLUVSeq_rpnThresholdCodeSeq schema)
    w hw weight_mem

/-! ## `thm:ccee`, generalized semantic-extension form -/

set_option maxHeartbeats 2000000 in
/-- **`thm:ccee`, generalized semantic-extension form, at zero slack.**  The source is
automatically renamed and admitted by finite semantic consequence; the weight and
right-hand quotation are built internally.  The sole LIA process is `canonicalCCEEDP T`,
fixed before `X`, `f`, and `w`.

The paper rendering of `thm:ccee` is
`lic_no_expected_net_update_conditional_paperLUV_closed`
(`Construction/Quotation/ExactCCEE.lean`), priced on the single market
`liaHistory (paperDP T)`.  This is the generalized semantic-extension form: it takes the
wider, threshold-only source interface (`X : ℕ → LUV` with `LUV.RpnThresholdCodeSeq X`),
which the literal-`PaperLUVSeq` rendering does not reach, and prices on the different
process `canonicalCCEEDP T` — the one canonical endpoint outside the shared market.

One binder asymmetry is deliberate and worth reading twice: `source_valued` is quantified
over worlds consistent with `theoremDP T`, a *smaller* process than `canonicalCCEEDP T`,
hence over a **superset** of worlds.  That makes it a stronger premise on the caller, not a
weaker one, and it is the form the proof consumes.  Non-vacuity of the weight binder is
witnessed by `canonicalCCEE_weight_nonvacuous`.
Kind: `C` composition; provenance: (a) derived in-project.
Paper node: `thm:ccee` -/
theorem lic_no_expected_net_update_conditional_exact_canonical
    (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T]
    [Entailment.Consistent T]
    (f : DeferralFunction)
    (X : ℕ → LUV) (hX : LUV.RpnThresholdCodeSeq X)
    (source_valued : ∀ n (v : PCWorld),
      v.ConsistentWithTheory (theoremDP T) → ∃ x, v.ValuesAt (X n) x)
    (w : ℕ → ℚ) (weight_mem : ∀ n, 0 ≤ w n ∧ w n ≤ 1)
    (weight_generable : PGenerableRat (liaHistory (canonicalCCEEDP T)) w) :
    (fun n => (semanticSchemaProductLUV (liftedRpnSourceSchema hX)
      (semanticQuoteSchema
        (canonicalDeferredWeightQuoteCode T f w weight_generable weight_mem).code) n).expect
          (liaHistory (canonicalCCEEDP T)) n) ≈ₙ
    fun n => ((canonicalConditionalExpectationQuoteCode T f
      (liftedRpnSourceSchema hX) w weight_generable weight_mem).luv n).expect
        (liaHistory (canonicalCCEEDP T)) n := by
  haveI := canonicalCCEELIA T
  let sourceSchema := liftedRpnSourceSchema hX
  let sourceHandle := semanticHandleLUVSeq sourceSchema
  let weightQ := canonicalDeferredWeightQuoteCode T f w weight_generable weight_mem
  let rightQ := canonicalConditionalExpectationQuoteCode T f sourceSchema w
    weight_generable weight_mem
  refine lic_no_expected_net_update_conditional_ofRepresentation
    (DP := canonicalCCEEDP T) f sourceHandle
    (semanticSchemaProductLUV sourceSchema (semanticQuoteSchema weightQ.code))
    rightQ.luv w weight_mem weight_generable
    (semanticHandleLUVSeq_rpnThresholdCodeSeq sourceSchema)
    (semanticSchemaProductLUV_rpnThresholdCodeSeq sourceSchema
      (semanticQuoteSchema weightQ.code)) rightQ.poly
    (fun _ => 0) tendsto_const_nhds (fun n v hv => ?_)
    (fun n v hv x hx => ?_) (fun n v hv => ?_)
    (fun n => ⟨canonicalCCEEWorld T, canonicalCCEEDP_hworld T n⟩)
  · obtain ⟨x, hx⟩ := source_valued n (pullOldWorld v)
      ((consistentWithTheory_liftDP_iff v (theoremDP T)).mp
        (canonicalCCEE_consistent_lifted hv))
    have hxlift : v.ValuesAt (liftLUV (X n)) x :=
      (liftLUV_valuesAt_iff v (X n) x).2 hx
    exact ⟨x, by
      simpa [sourceHandle, sourceSchema] using
        liftedRpnSemanticHandle_valuesAt hX n v x
          (canonicalCCEE_consistent_source hv) hxlift⟩
  · refine ⟨x * (w (f n) : ℝ), ?_, by simp⟩
    apply semanticSchemaProductLUV_valuesAt (liftedCCEEBaseDPComputation T)
      (canonicalCCEE_consistent_product hv) sourceSchema
      (semanticQuoteSchema weightQ.code)
      (fun limit => by simpa [sourceSchema] using
        (liftedRpnSource_factor_eventually T hX source_valued limit))
      (canonicalRationalQuote_factor_eventually T weightQ) n hx
    exact rationalQuote_semanticHandle_valuesAt weightQ n v
      (canonicalCCEE_consistent_theorem hv) (canonicalCCEE_consistent_quote hv)
  · have h := RationalQuoteCode.reflected (quotationPresentation T) rightQ n v
      (canonicalCCEE_consistent_theorem hv)
    rwa [Rat.cast_mul,
      ← (canonicalCCEEMarketComputation T).expectQuoteAt_cast sourceHandle n (f n)] at h

/-! ## Non-vacuity of the weight binder -/

/-- **Non-vacuity of the weight binder over `canonicalCCEEDP`** — kind `N+` non-vacuity
witness.  `lic_no_expected_net_update_conditional_exact_canonical`'s `weight_mem` and
`weight_generable` hypotheses are jointly inhabited over the canonical process by a
genuinely **non-constant** weight, the harmonic sequence `n ↦ 1/(n+1)`: it is
`[0,1]`-valued, ℙ‾-generable against *every* market — `PGenerableRat.ofPolyRatCodes` is
history-arbitrary, so the harmonic weight discharges `weight_generable` at every market
including this one — and not constant.
Provenance: (a) `harmonicWeight_mem`, `harmonicWeight_polyRatCodes`,
`harmonicWeight_not_constant`.
Paper node: `thm:ccee` -/
lemma canonicalCCEE_weight_nonvacuous
    (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] :
    (∀ n : ℕ, 0 ≤ 1 / ((n : ℚ) + 1) ∧ 1 / ((n : ℚ) + 1) ≤ 1) ∧
      PGenerableRat (liaHistory (canonicalCCEEDP T)) (fun n : ℕ => 1 / ((n : ℚ) + 1)) ∧
      ¬ ∀ m n : ℕ, 1 / ((m : ℚ) + 1) = 1 / ((n : ℚ) + 1) :=
  ⟨harmonicWeight_mem,
    PGenerableRat.ofPolyRatCodes harmonicWeight_polyRatCodes _,
    harmonicWeight_not_constant⟩

end LogicalInduction
