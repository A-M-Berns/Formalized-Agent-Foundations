import LogicalInduction.Construction.Witnesses.SemanticJoint
import LogicalInduction.Construction.Witnesses.SemanticQuote

/-!
# Certified-factor semantic product closure

`SemanticJoint.theorem_quote_product_not_jointly_satisfiable` shows that the original
unrestricted product process cannot be combined with the universal quote interpreter: it
treats every schema, including arbitrary Boolean quote programs, as a coherent LUV factor.

This file repairs schema ownership without changing the exact product mathematics.  Product
clauses are active only when both factor schemas belong to tag `0`, the namespace reserved
for proof-carrying source/cut presentations.  Quote aliases remain in tag `2`; malformed
quote programs therefore cannot become product factors accidentally.
-/

namespace LogicalInduction

open LO LO.Propositional LO.FirstOrder LO.FirstOrder.Arithmetic

attribute [local irreducible] Nat.sqrt

/-- Whether a product job's two factor schemas belong to the certified source namespace. -/
def certifiedProductJobOwned (e : ℕ) : Prop :=
  e.unpair.1.unpair.1 = 0 ∧ e.unpair.2.unpair.1.unpair.1 = 0

instance (e : ℕ) : Decidable (certifiedProductJobOwned e) := by
  unfold certifiedProductJobOwned
  exact instDecidableAnd

/-- Guard the existing exact clause by certified factor ownership. -/
def semanticCertifiedProductDefSentence (e : ℕ) : Sentence :=
  if certifiedProductJobOwned e then semanticProductDefSentence e else ⊤

def semanticCertifiedProductStageList : ℕ → List Sentence
  | 0 => [semanticCertifiedProductDefSentence 0]
  | k + 1 => semanticCertifiedProductDefSentence (k + 1) ::
      semanticCertifiedProductStageList k

lemma mem_semanticCertifiedProductStageList {e k : ℕ} (h : e ≤ k) :
    semanticCertifiedProductDefSentence e ∈ semanticCertifiedProductStageList k := by
  induction k with
  | zero => simp [semanticCertifiedProductStageList, Nat.le_zero.mp h]
  | succ k ih =>
      rcases Nat.lt_or_ge e (k + 1) with hlt | hge
      · exact List.mem_cons_of_mem _ (ih (Nat.lt_succ_iff.mp hlt))
      · have he : e = k + 1 := le_antisymm h hge
        simp [semanticCertifiedProductStageList, he]

lemma semanticCertifiedProductStageList_exists {φ : Sentence} {k : ℕ}
    (h : φ ∈ semanticCertifiedProductStageList k) :
    ∃ e, φ = semanticCertifiedProductDefSentence e := by
  induction k with
  | zero => exact ⟨0, by simpa [semanticCertifiedProductStageList] using h⟩
  | succ k ih =>
      rcases List.mem_cons.mp h with h | h
      · exact ⟨k + 1, h⟩
      · exact ih h

/-- The fixed exact product process for certified factor schemas. -/
def semanticCertifiedProductDP : DeductiveProcess where
  D k := (semanticCertifiedProductStageList k).toFinset
  mono k := by
    intro φ hφ
    simp only [List.mem_toFinset] at hφ ⊢
    exact List.mem_cons_of_mem _ hφ

lemma certifiedProductJobOwned_computablePred : ComputablePred certifiedProductJobOwned := by
  have hl : Primrec fun e : ℕ => e.unpair.1.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))
  have hr : Primrec fun e : ℕ => e.unpair.2.unpair.1.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp
      (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))
  exact ((Primrec.eq.comp hl (Primrec.const 0)).and
    (Primrec.eq.comp hr (Primrec.const 0))).computablePred

lemma semanticCertifiedProductDefSentence_computable :
    Computable semanticCertifiedProductDefSentence := by
  classical
  have hguard : Computable fun e => decide (certifiedProductJobOwned e) :=
    computablePred_iff_computable_decide.mp certifiedProductJobOwned_computablePred
  exact (Computable.cond hguard semanticProductDefSentence_computable
    (Computable.const (⊤ : Sentence))).of_eq (fun e => by
      simp only [semanticCertifiedProductDefSentence]
      by_cases h : certifiedProductJobOwned e <;> simp [h])

lemma semanticCertifiedProductDP_computable :
    ComputableDeductiveProcess semanticCertifiedProductDP := by
  have hlist : Computable semanticCertifiedProductStageList := by
    have hstep : Computable fun p : ℕ × List Sentence =>
        semanticCertifiedProductDefSentence (p.1 + 1) :: p.2 :=
      Computable.list_cons.comp
        (semanticCertifiedProductDefSentence_computable.comp
          (Primrec.succ.to_comp.comp Computable.fst)) Computable.snd
    refine (Computable.nat_rec Computable.id
      (Computable.const [semanticCertifiedProductDefSentence 0])
      (hstep.comp₂ Computable.snd.to₂)).of_eq (fun k => ?_)
    induction k with
    | zero => rfl
    | succ k ih => simpa [semanticCertifiedProductStageList] using ih
  have hkey : Computable fun k => Encodable.encode
      ((sentenceDedup (semanticCertifiedProductStageList k)).insertionSort sentenceCodeLE) :=
    Computable.encode.comp
      ((sentenceInsertionSort_prim.comp sentenceDedup_prim).to_comp.comp hlist)
  obtain ⟨code, hcode⟩ := Nat.Partrec.Code.exists_code.mp
    (Partrec.nat_iff.mp hkey)
  refine ⟨code, fun k => ?_⟩
  rw [hcode]
  exact Part.mem_some_iff.mpr (encode_toFinset_eq (semanticCertifiedProductStageList k))

lemma semanticCertifiedProductDefSentence_mem_stage (e : ℕ) :
    semanticCertifiedProductDefSentence e ∈ semanticCertifiedProductDP.D e :=
  List.mem_toFinset.mpr (mem_semanticCertifiedProductStageList (le_refl e))

lemma holds_semanticCertifiedProductDefSentence {v : PCWorld}
    (hv : v.ConsistentWithTheory semanticCertifiedProductDP) (e : ℕ) :
    v.Holds (semanticCertifiedProductDefSentence e) :=
  hv e _ (semanticCertifiedProductDefSentence_mem_stage e)

lemma semanticProductJob_owned {X W : PresentedLUVSeq} (n kind : ℕ) (r : ℚ) (zs zt : ℕ) :
    certifiedProductJobOwned
      (semanticProductJob X.thresholdSchema W.thresholdSchema n kind r zs zt) := by
  exact ⟨by simpa [semanticProductJob] using X.source_schema,
    by simpa [semanticProductJob] using W.source_schema⟩

lemma holds_semanticCertifiedProduct_pos {v : PCWorld}
    (hv : v.ConsistentWithTheory semanticCertifiedProductDP) (X W : PresentedLUVSeq)
    (n : ℕ) {r : ℚ} {zs zt : ℕ}
    (hst : r ≤ meshIndexRat zs * meshIndexRat zt)
    (hX : v.Holds (semanticPrimeSentence X.thresholdSchema
      (Nat.pair n (Encodable.encode (meshIndexRat zs)))))
    (hW : v.Holds (semanticPrimeSentence W.thresholdSchema
      (Nat.pair n (Encodable.encode (meshIndexRat zt))))) :
    v.Holds (semanticProductAtom X.thresholdSchema W.thresholdSchema n r) := by
  have h := holds_semanticCertifiedProductDefSentence hv
    (semanticProductJob X.thresholdSchema W.thresholdSchema n 0 r zs zt)
  rw [semanticCertifiedProductDefSentence, if_pos (semanticProductJob_owned n 0 r zs zt),
    semanticProductDefSentence_job, semanticProductSchemaInstance,
    if_pos rfl, if_pos hst] at h
  exact h ⟨hX, hW⟩

lemma not_holds_semanticCertifiedProduct_neg {v : PCWorld}
    (hv : v.ConsistentWithTheory semanticCertifiedProductDP) (X W : PresentedLUVSeq)
    (n : ℕ) {r : ℚ} {zs zt : ℕ}
    (hst : meshIndexRat zs * meshIndexRat zt ≤ r)
    (hX : ¬v.Holds (semanticPrimeSentence X.thresholdSchema
      (Nat.pair n (Encodable.encode (meshIndexRat zs)))))
    (hW : ¬v.Holds (semanticPrimeSentence W.thresholdSchema
      (Nat.pair n (Encodable.encode (meshIndexRat zt))))) :
    ¬v.Holds (semanticProductAtom X.thresholdSchema W.thresholdSchema n r) := by
  have h := holds_semanticCertifiedProductDefSentence hv
    (semanticProductJob X.thresholdSchema W.thresholdSchema n 1 r zs zt)
  rw [semanticCertifiedProductDefSentence, if_pos (semanticProductJob_owned n 1 r zs zt),
    semanticProductDefSentence_job, semanticProductSchemaInstance,
    if_neg (by decide : ¬(1 : ℕ) = 0), if_pos rfl, if_pos hst] at h
  intro hp
  rcases h hp with hx | hw
  · exact hX hx
  · exact hW hw

lemma holds_semanticCertifiedProduct_below {v : PCWorld}
    (hv : v.ConsistentWithTheory semanticCertifiedProductDP) (X W : PresentedLUVSeq)
    (n : ℕ) {r : ℚ} (hr : r < 0) :
    v.Holds (semanticProductAtom X.thresholdSchema W.thresholdSchema n r) := by
  have h := holds_semanticCertifiedProductDefSentence hv
    (semanticProductJob X.thresholdSchema W.thresholdSchema n 2 r 0 0)
  rw [semanticCertifiedProductDefSentence, if_pos (semanticProductJob_owned n 2 r 0 0),
    semanticProductDefSentence_job, semanticProductSchemaInstance,
    if_neg (by decide : ¬(2 : ℕ) = 0), if_neg (by decide : ¬(2 : ℕ) = 1), if_pos hr] at h
  exact h

/-- Exact multiplication is unchanged for certified tag-`0` factor presentations. -/
lemma semanticCertifiedProductLUV_valuesAt {v : PCWorld}
    (hv : v.ConsistentWithTheory semanticCertifiedProductDP)
    (X W : PresentedLUVSeq) (n : ℕ) {x c : ℝ}
    (hx : v.ValuesAt (X.toLUV n) x) (hc : v.ValuesAt (W.toLUV n) c) :
    v.ValuesAt (semanticProductLUV X W n) (x * c) := by
  obtain ⟨hx0, hx1, hxthr⟩ := hx
  obtain ⟨hc0, hc1, hcthr⟩ := hc
  refine ⟨mul_nonneg hx0 hc0, by nlinarith, fun r => ⟨?_, ?_⟩⟩
  · intro hr
    rw [semanticProductLUV_gt]
    rcases lt_or_ge r 0 with hneg | hpos
    · exact holds_semanticCertifiedProduct_below hv X W n hneg
    · obtain ⟨s, t, hs0, ht0, hst, hsx, htc⟩ :=
        exists_rat_pair_lt_mul hx0 hc0 hpos hr
      obtain ⟨zs, rfl⟩ := exists_meshIndexRat hs0
      obtain ⟨zt, rfl⟩ := exists_meshIndexRat ht0
      exact holds_semanticCertifiedProduct_pos hv X W n hst
        (by simpa only [PresentedLUVSeq.gt_eq] using (hxthr _).1 hsx)
        (by simpa only [PresentedLUVSeq.gt_eq] using (hcthr _).1 htc)
  · intro hr
    rw [semanticProductLUV_gt]
    obtain ⟨s, t, hs0, ht0, hst, hxs, hct⟩ :=
      exists_rat_pair_mul_lt hx0 hc0 hr
    obtain ⟨zs, rfl⟩ := exists_meshIndexRat hs0
    obtain ⟨zt, rfl⟩ := exists_meshIndexRat ht0
    exact not_holds_semanticCertifiedProduct_neg hv X W n hst
      (by simpa only [PresentedLUVSeq.gt_eq] using (hxthr _).2 hxs)
      (by simpa only [PresentedLUVSeq.gt_eq] using (hcthr _).2 hct)

/-- The old canonical product world also satisfies the guarded process. -/
lemma semanticCertifiedProductDP_hworld :
    semanticProductWorld.ConsistentWithTheory semanticCertifiedProductDP := by
  intro k φ hφ
  obtain ⟨e, rfl⟩ := semanticCertifiedProductStageList_exists
    (List.mem_toFinset.mp hφ)
  rw [semanticCertifiedProductDefSentence]
  split_ifs with howned
  · rw [semanticProductDefSentence]
    exact semanticProductWorld_holds_schema _ _ _ _ _ _ _
  · exact PCWorld.holds_top _

/-! ## Joint theorem/quote/product non-vacuity -/

open Classical in
/-- A joint world uses ordinary provability off the semantic tag, gives quote schemas their
canonical quotation meaning, and uses the product world's coherent zero cut everywhere
else in the semantic namespace. -/
noncomputable def theoremQuoteCertifiedProductWorld (T : ArithmeticTheory) : PCWorld := fun a =>
  if a.unpair.1 = semanticPrimeTag then
    if a.unpair.2.unpair.1.unpair.1 = 2 then
      (provabilityWorld T).Holds
        (quoteAtom (Nat.pair a.unpair.2.unpair.1.unpair.2 a.unpair.2.unpair.2))
    else semanticProductWorld a
  else provabilityWorld T a

lemma theoremQuoteCertifiedProductWorld_agree_base (T : ArithmeticTheory) {a : ℕ}
    (ha : a.unpair.1 ≠ semanticPrimeTag) :
    theoremQuoteCertifiedProductWorld T a ↔ provabilityWorld T a := by
  simp [theoremQuoteCertifiedProductWorld, ha]

lemma theoremQuoteCertifiedProductWorld_quote (T : ArithmeticTheory) (code input : ℕ) :
    (theoremQuoteCertifiedProductWorld T).Holds (semanticQuoteLeaf code input) ↔
      (provabilityWorld T).Holds (quoteAtom (Nat.pair code input)) := by
  change theoremQuoteCertifiedProductWorld T
    (semanticPrimeCode (semanticQuoteSchema code) input) ↔ _
  simp [theoremQuoteCertifiedProductWorld, semanticPrimeCode, semanticQuoteSchema]

lemma theoremQuoteCertifiedProductWorld_quoteAtom (T : ArithmeticTheory) (w : ℕ) :
    (theoremQuoteCertifiedProductWorld T).Holds (quoteAtom w) ↔
      (provabilityWorld T).Holds (quoteAtom w) := by
  change theoremQuoteCertifiedProductWorld T
      (quotationClaimCode universalQuotePos universalQuoteNeg w) ↔
    provabilityWorld T (quotationClaimCode universalQuotePos universalQuoteNeg w)
  apply theoremQuoteCertifiedProductWorld_agree_base T
  simp [quotationClaimCode, semanticPrimeTag]

lemma theoremQuoteCertifiedProductWorld_semantic_nonquote (T : ArithmeticTheory)
    (schema input : ℕ) (hschema : schema.unpair.1 ≠ 2) :
    (theoremQuoteCertifiedProductWorld T).Holds (semanticPrimeSentence schema input) ↔
      semanticProductWorld.Holds (semanticPrimeSentence schema input) := by
  change theoremQuoteCertifiedProductWorld T (semanticPrimeCode schema input) ↔
    semanticProductWorld (semanticPrimeCode schema input)
  simp [theoremQuoteCertifiedProductWorld, semanticPrimeCode, hschema]

lemma theoremQuoteCertifiedProductWorld_holds_product_schema (T : ArithmeticTheory)
    (left right n kind : ℕ) (r : ℚ) (zs zt : ℕ)
    (hleft : left.unpair.1 = 0) (hright : right.unpair.1 = 0) :
    (theoremQuoteCertifiedProductWorld T).Holds
      (semanticProductSchemaInstance left right n kind r zs zt) := by
  rw [semanticProductSchemaInstance]
  have hleft_ne : left.unpair.1 ≠ 2 := by omega
  have hright_ne : right.unpair.1 ≠ 2 := by omega
  have hproduct_ne : (semanticProductSchema left right).unpair.1 ≠ 2 := by
    simp [semanticProductSchema]
  have hleft_iff (q : ℚ) :
      (theoremQuoteCertifiedProductWorld T).Holds
        (semanticPrimeSentence left (Nat.pair n (Encodable.encode q))) ↔
      semanticProductWorld.Holds
        (semanticPrimeSentence left (Nat.pair n (Encodable.encode q))) :=
    theoremQuoteCertifiedProductWorld_semantic_nonquote T _ _ hleft_ne
  have hright_iff (q : ℚ) :
      (theoremQuoteCertifiedProductWorld T).Holds
        (semanticPrimeSentence right (Nat.pair n (Encodable.encode q))) ↔
      semanticProductWorld.Holds
        (semanticPrimeSentence right (Nat.pair n (Encodable.encode q))) :=
    theoremQuoteCertifiedProductWorld_semantic_nonquote T _ _ hright_ne
  have hproduct_iff :
      (theoremQuoteCertifiedProductWorld T).Holds
        (semanticProductAtom left right n r) ↔
      semanticProductWorld.Holds (semanticProductAtom left right n r) := by
    exact theoremQuoteCertifiedProductWorld_semantic_nonquote T _ _ hproduct_ne
  split_ifs with hkind hpos hkind hneg hr
  · intro h
    have hs : semanticProductWorld.Holds
        (semanticPrimeSentence left
          (Nat.pair n (Encodable.encode (meshIndexRat zs)))) :=
      (hleft_iff _).mp h.1
    exact False.elim
      ((semanticProductWorld_nonneg left n _ (meshIndexRat_nonneg zs)) hs)
  · exact PCWorld.holds_top _
  · intro hp
    have hp' := hproduct_iff.mp hp
    have h := semanticProductWorld_holds_schema left right n 1 r zs zt
    rw [semanticProductSchemaInstance, if_neg (by decide : ¬(1 : ℕ) = 0),
      if_pos rfl, if_pos hneg] at h
    rcases h hp' with hx | hw
    · exact Or.inl ((hleft_iff _).mpr hx)
    · exact Or.inr ((hright_iff _).mpr hw)
  · exact PCWorld.holds_top _
  · exact hproduct_iff.mpr (semanticProductWorld_productAtom left right n r |>.mpr hr)
  · exact PCWorld.holds_top _

lemma theoremQuoteCertifiedProductWorld_consistent_product (T : ArithmeticTheory) :
    (theoremQuoteCertifiedProductWorld T).ConsistentWithTheory
      semanticCertifiedProductDP := by
  intro k φ hφ
  obtain ⟨e, rfl⟩ := semanticCertifiedProductStageList_exists
    (List.mem_toFinset.mp hφ)
  rw [semanticCertifiedProductDefSentence]
  split_ifs with howned
  · rcases howned with ⟨hl, hr⟩
    rw [semanticProductDefSentence]
    exact theoremQuoteCertifiedProductWorld_holds_product_schema T _ _ _ _ _ _ _ hl hr
  · exact PCWorld.holds_top _

lemma exists_of_mem_semanticQuoteStageList {φ : Sentence} {k : ℕ}
    (h : φ ∈ semanticQuoteStageList k) : ∃ e, φ = semanticQuoteDefSentence e := by
  induction k with
  | zero => exact ⟨0, by simpa [semanticQuoteStageList] using h⟩
  | succ k ih =>
      rcases List.mem_cons.mp h with h | h
      · exact ⟨k + 1, h⟩
      · exact ih h

lemma theoremQuoteCertifiedProductWorld_consistent_quote (T : ArithmeticTheory) :
    (theoremQuoteCertifiedProductWorld T).ConsistentWithTheory semanticQuoteDP := by
  intro k φ hφ
  obtain ⟨e, rfl⟩ := exists_of_mem_semanticQuoteStageList (List.mem_toFinset.mp hφ)
  rw [semanticQuoteDefSentence]
  by_cases hkind : e.unpair.1 = 0
  · rw [if_pos hkind]
    intro hbase
    exact (theoremQuoteCertifiedProductWorld_quote T _ _).mpr
      ((theoremQuoteCertifiedProductWorld_quoteAtom T _).mp hbase)
  · rw [if_neg hkind]
    intro hleaf
    exact (theoremQuoteCertifiedProductWorld_quoteAtom T _).mpr
      ((theoremQuoteCertifiedProductWorld_quote T _ _).mp hleaf)

lemma theoremQuoteCertifiedProductWorld_consistent_theorem
    (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1] :
    (theoremQuoteCertifiedProductWorld T).ConsistentWithTheory (theoremDP T) := by
  intro n φ hφ
  have hφ' := hφ
  simp only [theoremDP, theoremStage, Finset.mem_image, Finset.mem_filter,
    Finset.mem_range] at hφ'
  obtain ⟨e, _, rfl⟩ := hφ'
  apply (PCWorld.holds_congr_atomCodes (eventAtom e) (fun a ha =>
    theoremQuoteCertifiedProductWorld_agree_base T
      (eventAtom_atomCodes_ne_semanticPrimeTag e a ha))).mpr
  exact theoremDP_hworld T n (eventAtom e) hφ

/-- The repaired fixed process, chosen from `T` before any source, market, weight, or
deferral. -/
noncomputable def theoremQuoteCertifiedProductDP
    (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1] :
    DeductiveProcess :=
  ((theoremDP T).union semanticQuoteDP).union semanticCertifiedProductDP

noncomputable def theoremQuoteCertifiedProductDPComputation
    (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1] :
    DeductiveProcessComputation (theoremQuoteCertifiedProductDP T) :=
  (((theoremDP_computable T).nonemptyComputation.some).union
    semanticQuoteDP_computable.nonemptyComputation.some).union
      semanticCertifiedProductDP_computable.nonemptyComputation.some

/-- Joint non-vacuity of the fixed theorem, quotation, and certified-product substrate. -/
lemma theoremQuoteCertifiedProductDP_hworld
    (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1] :
    (theoremQuoteCertifiedProductWorld T).ConsistentWithTheory
      (theoremQuoteCertifiedProductDP T) := by
  intro n φ hφ
  rw [theoremQuoteCertifiedProductDP, DeductiveProcess.union_stage,
    Finset.mem_union, DeductiveProcess.union_stage, Finset.mem_union] at hφ
  rcases hφ with (htheorem | hquote) | hproduct
  · exact theoremQuoteCertifiedProductWorld_consistent_theorem T n φ htheorem
  · exact theoremQuoteCertifiedProductWorld_consistent_quote T n φ hquote
  · exact theoremQuoteCertifiedProductWorld_consistent_product T n φ hproduct

/-! ## Exact conditional expectation over the repaired fixed process -/

/-- Exact multiplication enters the generic CCEE theorem over the jointly non-vacuous
theorem/quote/certified-product process.  The remaining presentation premises are kept
explicit here; the proof-carrying source interpreter is responsible for discharging them. -/
lemma lic_no_expected_net_update_conditional_certifiedSemantic
    {T : ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]
    {P : History} [IsLogicalInductor P (theoremQuoteCertifiedProductDP T)]
    (f : DeferralFunction) (X W : PresentedLUVSeq) (Z' : ℕ → LUV) (w : ℕ → ℚ)
    (weight_mem : ∀ n, 0 ≤ w n ∧ w n ≤ 1)
    (weight_generable : PGenerableRat P w)
    (hZ' : LUV.RpnThresholdCodeSeq Z')
    (source_valued : ∀ n (v : PCWorld),
      v.ConsistentWithTheory (theoremQuoteCertifiedProductDP T) →
      ∃ x, v.ValuesAt (X.toLUV n) x)
    (weight_valued : ∀ n (v : PCWorld),
      v.ConsistentWithTheory (theoremQuoteCertifiedProductDP T) →
      v.ValuesAt (W.toLUV n) (w (f n)))
    (right_reflected : ∀ n (v : PCWorld),
      v.ConsistentWithTheory (theoremQuoteCertifiedProductDP T) →
      v.ValuesAt (Z' n) ((X.toLUV n).expect P (f n) * w (f n))) :
    (fun n => (semanticProductLUV X W n).expect P n) ≈ₙ
      fun n => (Z' n).expect P n := by
  refine lic_no_expected_net_update_conditional_ofRepresentation
    (DP := theoremQuoteCertifiedProductDP T) f X.toLUV (semanticProductLUV X W) Z' w
    weight_mem weight_generable X.threshold_codes
    (semanticProductLUV_rpnThresholdCodeSeq X W) hZ' (fun _ => 0)
    tendsto_const_nhds source_valued (fun n v hv x hx => ?_) right_reflected
    (fun n => ⟨theoremQuoteCertifiedProductWorld T,
      theoremQuoteCertifiedProductDP_hworld T n⟩)
  refine ⟨x * (w (f n) : ℝ), ?_, by simp⟩
  exact semanticCertifiedProductLUV_valuesAt
    (PCWorld.consistentWithTheory_union_right hv) X W n hx (weight_valued n v hv)

private noncomputable abbrev theoremQuoteCertifiedProductLIA
    (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1] :
    IsLogicalInductor (liaHistory (theoremQuoteCertifiedProductDP T))
      (theoremQuoteCertifiedProductDP T) :=
  LIA_is_logical_inductor _ (theoremQuoteCertifiedProductDPComputation T).toComputable

/-- Closed-inductor form of the repaired exact semantic endpoint.  This is not yet the
paper-facing capstone: `PresentedLUVSeq`, weight presentation, and the right quote remain
visible until the universal certified-source registry is implemented. -/
lemma lic_no_expected_net_update_conditional_certifiedSemantic_closed
    (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]
    (f : DeferralFunction) (X W : PresentedLUVSeq) (Z' : ℕ → LUV) (w : ℕ → ℚ)
    (weight_mem : ∀ n, 0 ≤ w n ∧ w n ≤ 1)
    (weight_generable : PGenerableRat (liaHistory (theoremQuoteCertifiedProductDP T)) w)
    (hZ' : LUV.RpnThresholdCodeSeq Z')
    (source_valued : ∀ n (v : PCWorld),
      v.ConsistentWithTheory (theoremQuoteCertifiedProductDP T) →
      ∃ x, v.ValuesAt (X.toLUV n) x)
    (weight_valued : ∀ n (v : PCWorld),
      v.ConsistentWithTheory (theoremQuoteCertifiedProductDP T) →
      v.ValuesAt (W.toLUV n) (w (f n)))
    (right_reflected : ∀ n (v : PCWorld),
      v.ConsistentWithTheory (theoremQuoteCertifiedProductDP T) →
      v.ValuesAt (Z' n) ((X.toLUV n).expect
        (liaHistory (theoremQuoteCertifiedProductDP T)) (f n) * w (f n))) :
    (fun n => (semanticProductLUV X W n).expect
      (liaHistory (theoremQuoteCertifiedProductDP T)) n) ≈ₙ
      fun n => (Z' n).expect (liaHistory (theoremQuoteCertifiedProductDP T)) n := by
  haveI := theoremQuoteCertifiedProductLIA T
  exact lic_no_expected_net_update_conditional_certifiedSemantic
    f X W Z' w weight_mem weight_generable hZ' source_valued weight_valued right_reflected

#print axioms semanticCertifiedProductDP_computable
#print axioms semanticCertifiedProductDP_hworld
#print axioms semanticCertifiedProductLUV_valuesAt
#print axioms theoremQuoteCertifiedProductDP_hworld
#print axioms lic_no_expected_net_update_conditional_certifiedSemantic_closed

end LogicalInduction
