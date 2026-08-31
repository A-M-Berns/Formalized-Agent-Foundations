import LogicalInduction.Construction.Witnesses.SemanticPrime
import LogicalInduction.Construction.Witnesses.ProductDefinition

/-!
# Fixed semantic-prime product closure

This is the source-independent counterpart of `ProductDefinition`'s exact product
mathematics.  A product handle carries the schemas of both factors in its own name, so one
deductive process can enumerate the existing positive, negative, and below-zero rational
cut clauses for *every* product before a market or source LUV is chosen.
-/

namespace LogicalInduction

open LO LO.Propositional LO.FirstOrder LO.FirstOrder.Arithmetic

-- Keep the pairing decoder opaque while elaborating fixed job syntax.
attribute [local irreducible] Nat.sqrt

/-- Tag-`1` constructor of the semantic schema language: a product of two schema names. -/
def semanticProductSchema (left right : ℕ) : ℕ := Nat.pair 1 (Nat.pair left right)

/-- The semantic-prime name of `X_n * W_n > r`. -/
def semanticProductAtom (left right n : ℕ) (r : ℚ) : Sentence :=
  semanticPrimeSentence (semanticProductSchema left right) (Nat.pair n (Encodable.encode r))

/-- The product LUV associated with two syntax-bearing source presentations. -/
def semanticProductLUV (X W : PresentedLUVSeq) (n : ℕ) : LUV :=
  ⟨semanticProductAtom X.thresholdSchema W.thresholdSchema n⟩

@[simp] lemma semanticProductLUV_gt (X W : PresentedLUVSeq) (n : ℕ) (r : ℚ) :
    (semanticProductLUV X W n).gt r =
      semanticProductAtom X.thresholdSchema W.thresholdSchema n r := rfl

/-- A leaf presentation cannot collide with the product constructor. -/
lemma PresentedLUVSeq.schema_ne_product (X : PresentedLUVSeq) (right : ℕ) :
    X.thresholdSchema ≠ semanticProductSchema X.thresholdSchema right := by
  intro h
  have hx := X.source_schema
  rw [h] at hx
  simp [semanticProductSchema] at hx

/-- The fixed clause family, directly ported from `productSchemaInstance`.  The source
thresholds are recovered from the two schema names embedded in the product handle. -/
def semanticProductSchemaInstance (left right n kind : ℕ) (r : ℚ) (zs zt : ℕ) : Sentence :=
  if kind = 0 then
    (if r ≤ meshIndexRat zs * meshIndexRat zt then
      (semanticPrimeSentence left (Nat.pair n (Encodable.encode (meshIndexRat zs))) ⋏
        semanticPrimeSentence right (Nat.pair n (Encodable.encode (meshIndexRat zt)))) 🡒
          semanticProductAtom left right n r else ⊤)
  else if kind = 1 then
    (if meshIndexRat zs * meshIndexRat zt ≤ r then
      semanticProductAtom left right n r 🡒
        (semanticPrimeSentence left (Nat.pair n (Encodable.encode (meshIndexRat zs))) ⋎
          semanticPrimeSentence right (Nat.pair n (Encodable.encode (meshIndexRat zt)))) else ⊤)
  else if r < 0 then semanticProductAtom left right n r else ⊤

/-- Pack a fixed product-closure job. -/
def semanticProductJob (left right n kind : ℕ) (r : ℚ) (zs zt : ℕ) : ℕ :=
  Nat.pair left <| Nat.pair right <| Nat.pair n <| Nat.pair kind <|
    Nat.pair (Encodable.encode r) (Nat.pair zs zt)

/-- Decode one product-closure job. -/
def semanticProductDefSentence (e : ℕ) : Sentence :=
  semanticProductSchemaInstance e.unpair.1 e.unpair.2.unpair.1 e.unpair.2.unpair.2.unpair.1
    e.unpair.2.unpair.2.unpair.2.unpair.1
    (decodedQuotationRat e.unpair.2.unpair.2.unpair.2.unpair.2.unpair.1)
    e.unpair.2.unpair.2.unpair.2.unpair.2.unpair.2.unpair.1
    e.unpair.2.unpair.2.unpair.2.unpair.2.unpair.2.unpair.2

/-- All jobs through the stage number, independent of any source family. -/
def semanticProductStageList : ℕ → List Sentence
  | 0 => [semanticProductDefSentence 0]
  | k + 1 => semanticProductDefSentence (k + 1) :: semanticProductStageList k

lemma mem_semanticProductStageList {e k : ℕ} (h : e ≤ k) :
    semanticProductDefSentence e ∈ semanticProductStageList k := by
  induction k with
  | zero => simp [semanticProductStageList, Nat.le_zero.mp h]
  | succ k ih =>
      rcases Nat.lt_or_ge e (k + 1) with hlt | hge
      · exact List.mem_cons_of_mem _ (ih (Nat.lt_succ_iff.mp hlt))
      · have he : e = k + 1 := le_antisymm h hge
        simp [semanticProductStageList, he]

lemma semanticProductStageList_exists {φ : Sentence} {k : ℕ}
    (h : φ ∈ semanticProductStageList k) : ∃ e, φ = semanticProductDefSentence e := by
  induction k with
  | zero => exact ⟨0, by simpa [semanticProductStageList] using h⟩
  | succ k ih =>
      rcases List.mem_cons.mp h with h | h
      · exact ⟨k + 1, h⟩
      · exact ih h

/-- The fixed semantic closure process.  It has no `X`, `W`, market, weight, or deferral
parameter. -/
def semanticProductDP : DeductiveProcess where
  D k := (semanticProductStageList k).toFinset
  mono k := by
    intro φ hφ
    simp only [List.mem_toFinset] at hφ ⊢
    exact List.mem_cons_of_mem _ hφ

/-! ### Computability of the fixed closure -/

set_option maxHeartbeats 4000000 in
lemma semanticProductDefSentence_computable : Computable semanticProductDefSentence := by
  classical
  refine Computable.encode_iff.mp ?_
  have hl : Primrec fun e : ℕ => e.unpair.1 := Primrec.fst.comp Primrec.unpair
  have ha : Primrec fun e : ℕ => e.unpair.2 := Primrec.snd.comp Primrec.unpair
  have hr : Primrec fun e : ℕ => e.unpair.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp ha)
  have hb : Primrec fun e : ℕ => e.unpair.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp ha)
  have hn : Primrec fun e : ℕ => e.unpair.2.unpair.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp hb)
  have hc : Primrec fun e : ℕ => e.unpair.2.unpair.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp hb)
  have hkind : Primrec fun e : ℕ => e.unpair.2.unpair.2.unpair.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp hc)
  have hd : Primrec fun e : ℕ => e.unpair.2.unpair.2.unpair.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp hc)
  have hcr : Primrec fun e : ℕ => e.unpair.2.unpair.2.unpair.2.unpair.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp hd)
  have he : Primrec fun e : ℕ => e.unpair.2.unpair.2.unpair.2.unpair.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp hd)
  have hzs : Primrec fun e : ℕ => e.unpair.2.unpair.2.unpair.2.unpair.2.unpair.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp he)
  have hzt : Primrec fun e : ℕ => e.unpair.2.unpair.2.unpair.2.unpair.2.unpair.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp he)
  have hq : Primrec fun e : ℕ => decodedQuotationRat e.unpair.2.unpair.2.unpair.2.unpair.2.unpair.1 :=
    decodedQuotationRat_prim.comp hcr
  have hs : Primrec fun e : ℕ => meshIndexRat e.unpair.2.unpair.2.unpair.2.unpair.2.unpair.2.unpair.1 :=
    meshIndexRat_prim.comp hzs
  have ht : Primrec fun e : ℕ => meshIndexRat e.unpair.2.unpair.2.unpair.2.unpair.2.unpair.2.unpair.2 :=
    meshIndexRat_prim.comp hzt
  have hatom : Primrec fun p : ℕ × ℕ =>
      Encodable.encode (semanticPrimeSentence p.1 p.2) :=
    (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 1)
      (Primrec₂.natPair.comp (Primrec.const semanticPrimeTag)
        (Primrec₂.natPair.comp Primrec.fst Primrec.snd)))).of_eq (fun _ => rfl)
  have hinput : Primrec fun e : ℕ => Nat.pair e.unpair.2.unpair.2.unpair.1
      (Encodable.encode (decodedQuotationRat e.unpair.2.unpair.2.unpair.2.unpair.2.unpair.1)) :=
    Primrec₂.natPair.comp hn (Primrec.encode.comp hq)
  have hleft : Primrec fun e : ℕ => Encodable.encode
      (semanticPrimeSentence e.unpair.1 (Nat.pair e.unpair.2.unpair.2.unpair.1
        (Encodable.encode (meshIndexRat e.unpair.2.unpair.2.unpair.2.unpair.2.unpair.2.unpair.1)))) :=
    hatom.comp (hl.pair (Primrec₂.natPair.comp hn (Primrec.encode.comp hs)))
  have hright : Primrec fun e : ℕ => Encodable.encode
      (semanticPrimeSentence e.unpair.2.unpair.1 (Nat.pair e.unpair.2.unpair.2.unpair.1
        (Encodable.encode (meshIndexRat e.unpair.2.unpair.2.unpair.2.unpair.2.unpair.2.unpair.2)))) :=
    hatom.comp (hr.pair (Primrec₂.natPair.comp hn (Primrec.encode.comp ht)))
  have hschema : Primrec fun e : ℕ => semanticProductSchema e.unpair.1 e.unpair.2.unpair.1 :=
    (Primrec₂.natPair.comp (Primrec.const 1) (Primrec₂.natPair.comp hl hr)).of_eq (fun _ => rfl)
  have hproduct : Primrec fun e : ℕ => Encodable.encode
      (semanticProductAtom e.unpair.1 e.unpair.2.unpair.1 e.unpair.2.unpair.2.unpair.1
        (decodedQuotationRat e.unpair.2.unpair.2.unpair.2.unpair.2.unpair.1)) :=
    hatom.comp (hschema.pair hinput)
  have hk0 : PrimrecPred fun e : ℕ => e.unpair.2.unpair.2.unpair.2.unpair.1 = 0 :=
    Primrec.eq.comp hkind (Primrec.const 0)
  have hk1 : PrimrecPred fun e : ℕ => e.unpair.2.unpair.2.unpair.2.unpair.1 = 1 :=
    Primrec.eq.comp hkind (Primrec.const 1)
  have hmul : Primrec fun e : ℕ =>
      meshIndexRat e.unpair.2.unpair.2.unpair.2.unpair.2.unpair.2.unpair.1 *
        meshIndexRat e.unpair.2.unpair.2.unpair.2.unpair.2.unpair.2.unpair.2 :=
    ratMul_prim.comp hs ht
  have hg0 : PrimrecPred fun e : ℕ =>
      decodedQuotationRat e.unpair.2.unpair.2.unpair.2.unpair.2.unpair.1 ≤
        meshIndexRat e.unpair.2.unpair.2.unpair.2.unpair.2.unpair.2.unpair.1 *
          meshIndexRat e.unpair.2.unpair.2.unpair.2.unpair.2.unpair.2.unpair.2 :=
    ratLE_prim.comp hq hmul
  have hg1 : PrimrecPred fun e : ℕ =>
      meshIndexRat e.unpair.2.unpair.2.unpair.2.unpair.2.unpair.2.unpair.1 *
          meshIndexRat e.unpair.2.unpair.2.unpair.2.unpair.2.unpair.2.unpair.2 ≤
        decodedQuotationRat e.unpair.2.unpair.2.unpair.2.unpair.2.unpair.1 :=
    ratLE_prim.comp hmul hq
  have hneg : PrimrecPred fun e : ℕ =>
      decodedQuotationRat e.unpair.2.unpair.2.unpair.2.unpair.2.unpair.1 < 0 := by
    exact (ratLE_prim.comp (Primrec.const 0) hq).not.of_eq (fun e => by simp [not_le])
  have hand := Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 2)
    (Primrec₂.natPair.comp
      (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 3)
        (Primrec₂.natPair.comp hleft hright))) hproduct))
  have hor := Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 2)
    (Primrec₂.natPair.comp hproduct
      (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 4)
        (Primrec₂.natPair.comp hleft hright)))))
  have htop : Primrec fun _ : ℕ => Encodable.encode (⊤ : Sentence) := Primrec.const _
  refine (((hk0.decide.cond (hg0.decide.cond hand htop)
    (hk1.decide.cond (hg1.decide.cond hor htop)
      (hneg.decide.cond hproduct htop))).to_comp).of_eq (fun e => ?_))
  rw [semanticProductDefSentence, semanticProductSchemaInstance]
  split_ifs with h0 hg0' h1 hg1' hneg'
  · simp only [h0, hg0', decide_true, cond_true]
    rfl
  · simp [h0, hg0']
  · simp only [h1, hg1', decide_true, cond_true]
    rfl
  · simp [h1, hg1']
  · simp only [h0, h1, hneg', decide_true, decide_false, cond_true, cond_false]
  · simp [h0, h1, hneg']

set_option maxHeartbeats 1000000 in
/-- The whole fixed semantic closure is a computable deductive process. -/
lemma semanticProductDP_computable : ComputableDeductiveProcess semanticProductDP := by
  have hlist : Computable semanticProductStageList := by
    have hstep : Computable fun p : ℕ × List Sentence =>
        semanticProductDefSentence (p.1 + 1) :: p.2 :=
      Computable.list_cons.comp
        (semanticProductDefSentence_computable.comp (Primrec.succ.to_comp.comp Computable.fst))
        Computable.snd
    refine (Computable.nat_rec Computable.id
      (Computable.const [semanticProductDefSentence 0])
      (hstep.comp₂ Computable.snd.to₂)).of_eq (fun k => ?_)
    induction k with
    | zero => rfl
    | succ k ih => simpa [semanticProductStageList] using ih
  have hkey : Computable fun k => Encodable.encode
      ((sentenceDedup (semanticProductStageList k)).insertionSort sentenceCodeLE) :=
    Computable.encode.comp
      ((sentenceInsertionSort_prim.comp sentenceDedup_prim).to_comp.comp hlist)
  obtain ⟨code, hcode⟩ := Nat.Partrec.Code.exists_code.mp
    (Partrec.nat_iff.mp hkey)
  refine ⟨code, fun k => ?_⟩
  rw [hcode]
  exact Part.mem_some_iff.mpr (encode_toFinset_eq (semanticProductStageList k))

/-! ### Fixed-process non-vacuity -/

open Classical in
noncomputable def semanticProductWorld : PCWorld := fun a =>
  if a.unpair.1 = semanticPrimeTag ∧ a.unpair.2.unpair.1.unpair.1 = 1 then
    decodedQuotationRat a.unpair.2.unpair.2.unpair.2 < 0
  else False

lemma semanticProductWorld_nonneg (schema n : ℕ) (q : ℚ) (hq : 0 ≤ q) :
    ¬ semanticProductWorld.Holds
      (semanticPrimeSentence schema (Nat.pair n (Encodable.encode q))) := by
  change ¬ semanticProductWorld
    (semanticPrimeCode schema (Nat.pair n (Encodable.encode q)))
  simp only [semanticProductWorld, semanticPrimeCode, Nat.unpair_pair,
    decodedQuotationRat_encode]
  split <;> simp_all

lemma semanticProductWorld_productAtom (left right n : ℕ) (r : ℚ) :
    semanticProductWorld.Holds (semanticProductAtom left right n r) ↔ r < 0 := by
  change semanticProductWorld
    (semanticPrimeCode (semanticProductSchema left right) (Nat.pair n (Encodable.encode r))) ↔ _
  simp [semanticProductWorld, semanticPrimeCode, semanticProductSchema,
    decodedQuotationRat_encode]

lemma semanticProductWorld_holds_schema (left right n kind : ℕ) (r : ℚ) (zs zt : ℕ) :
    semanticProductWorld.Holds (semanticProductSchemaInstance left right n kind r zs zt) := by
  rw [semanticProductSchemaInstance]
  split_ifs with hkind hpos hkind hneg hr
  · intro h
    exact False.elim
      ((semanticProductWorld_nonneg left n (meshIndexRat zs) (meshIndexRat_nonneg zs)) h.1)
  · exact PCWorld.holds_top _
  · intro hp
    have hp' : r < 0 := (semanticProductWorld_productAtom left right n r).mp hp
    have hs : 0 ≤ meshIndexRat zs * meshIndexRat zt :=
      mul_nonneg (meshIndexRat_nonneg zs) (meshIndexRat_nonneg zt)
    linarith
  · exact PCWorld.holds_top _
  · exact (semanticProductWorld_productAtom left right n r).mpr hr
  · exact PCWorld.holds_top _

/-- The process used for the eventual `LIA` is fixed from the arithmetic theory alone:
the ordinary provability stream and the semantic product closure are combined before any
market, source LUV, weight, or deferral is selected. -/
noncomputable def theoremSemanticProductDP (T : ArithmeticTheory) [T.Δ₁]
    [Entailment.Consistent T] : DeductiveProcess :=
  (theoremDP T).union semanticProductDP

noncomputable def theoremSemanticProductDPComputation (T : ArithmeticTheory)
    [T.Δ₁] [Entailment.Consistent T] :
    DeductiveProcessComputation (theoremSemanticProductDP T) :=
  ((theoremDP_computable T).nonemptyComputation.some).union
    semanticProductDP_computable.nonemptyComputation.some

/-! ### A joint completed world -/

/-- The original theorem stream never uses the semantic-prime atom tag. -/
lemma eventAtom_atomCodes_ne_semanticPrimeTag (e : ℕ) :
    ∀ a ∈ sentenceAtomCodes (eventAtom e), a.unpair.1 ≠ semanticPrimeTag := by
  intro a ha
  rcases h : e.unpair.1 with _ | _ | _ | _ | _ | _ | m
  all_goals simp only [eventAtom, h, sentenceAtomCodes_neg] at ha
  · exact fun hc => by
      simp [sentenceAtomCodes_computationClaimSentence _ a ha, haltingClaim,
        ComputationClaimKind.godelCode, semanticPrimeTag] at hc
  · exact fun hc => by
      simp [sentenceAtomCodes_computationClaimSentence _ a ha, haltingClaim,
        ComputationClaimKind.godelCode, semanticPrimeTag] at hc
  · exact fun hc => by
      simp [sentenceAtomCodes_computationClaimSentence _ a ha, boundedHaltingClaim,
        ComputationClaimKind.godelCode, semanticPrimeTag] at hc
  · exact fun hc => by
      simp [sentenceAtomCodes_computationClaimSentence _ a ha, boundedHaltingClaim,
        ComputationClaimKind.godelCode, semanticPrimeTag] at hc
  · exact fun hc => by
      simp [sentenceAtomCodes_quoteAtom _ a ha, semanticPrimeTag] at hc
  · exact fun hc => by
      simp [sentenceAtomCodes_quoteAtom _ a ha, semanticPrimeTag] at hc
  · simp at ha

open Classical in
noncomputable def theoremSemanticProductWorld (T : ArithmeticTheory) : PCWorld := fun a =>
  if a.unpair.1 = semanticPrimeTag then semanticProductWorld a else provabilityWorld T a

section

lemma theoremSemanticProductWorld_agree_base (T : ArithmeticTheory) {a : ℕ}
    (ha : a.unpair.1 ≠ semanticPrimeTag) :
    theoremSemanticProductWorld T a ↔ provabilityWorld T a := by
  simp [theoremSemanticProductWorld, ha]

lemma theoremSemanticProductWorld_agree_semantic (T : ArithmeticTheory) (schema input : ℕ) :
    theoremSemanticProductWorld T (semanticPrimeCode schema input) ↔
      semanticProductWorld (semanticPrimeCode schema input) := by
  simp [theoremSemanticProductWorld, semanticPrimeCode]

lemma theoremSemanticProductWorld_holds_base_iff (T : ArithmeticTheory) {φ : Sentence}
    (hφ : ∀ a ∈ sentenceAtomCodes φ, a.unpair.1 ≠ semanticPrimeTag) :
    (theoremSemanticProductWorld T).Holds φ ↔ (provabilityWorld T).Holds φ :=
  PCWorld.holds_congr_atomCodes φ
    (fun a ha => theoremSemanticProductWorld_agree_base T (hφ a ha))

lemma theoremSemanticProductWorld_holds_semanticPrime (T : ArithmeticTheory) (schema input : ℕ) :
    (theoremSemanticProductWorld T).Holds (semanticPrimeSentence schema input) ↔
      semanticProductWorld.Holds (semanticPrimeSentence schema input) :=
  theoremSemanticProductWorld_agree_semantic T schema input

lemma theoremSemanticProductWorld_nonneg (T : ArithmeticTheory) (schema n : ℕ) (q : ℚ)
    (hq : 0 ≤ q) :
    ¬ (theoremSemanticProductWorld T).Holds
      (semanticPrimeSentence schema (Nat.pair n (Encodable.encode q))) :=
  fun h => semanticProductWorld_nonneg schema n q hq
    ((theoremSemanticProductWorld_holds_semanticPrime T schema _).mp h)

lemma theoremSemanticProductWorld_productAtom (T : ArithmeticTheory) (left right n : ℕ) (r : ℚ) :
    (theoremSemanticProductWorld T).Holds (semanticProductAtom left right n r) ↔ r < 0 := by
  change (theoremSemanticProductWorld T).Holds
      (semanticPrimeSentence (semanticProductSchema left right)
        (Nat.pair n (Encodable.encode r))) ↔ r < 0
  rw [theoremSemanticProductWorld_holds_semanticPrime]
  change semanticProductWorld.Holds (semanticProductAtom left right n r) ↔ r < 0
  exact semanticProductWorld_productAtom left right n r

lemma theoremSemanticProductWorld_holds_schema (T : ArithmeticTheory)
    (left right n kind : ℕ) (r : ℚ) (zs zt : ℕ) :
    (theoremSemanticProductWorld T).Holds
      (semanticProductSchemaInstance left right n kind r zs zt) := by
  rw [semanticProductSchemaInstance]
  split_ifs with hkind hpos hkind hneg hr
  · intro h
    exact False.elim ((theoremSemanticProductWorld_nonneg T left n (meshIndexRat zs)
      (meshIndexRat_nonneg zs)) h.1)
  · exact PCWorld.holds_top _
  · intro hp
    have hp' : r < 0 := (theoremSemanticProductWorld_productAtom T left right n r).mp hp
    have hs : 0 ≤ meshIndexRat zs * meshIndexRat zt :=
      mul_nonneg (meshIndexRat_nonneg zs) (meshIndexRat_nonneg zt)
    linarith
  · exact PCWorld.holds_top _
  · exact (theoremSemanticProductWorld_productAtom T left right n r).mpr hr
  · exact PCWorld.holds_top _

end

/-- The pre-market combined process has a completed world at every stage. -/
lemma theoremSemanticProductDP_hworld (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T]
    [Entailment.Consistent T] :
    (theoremSemanticProductWorld T).ConsistentWithTheory (theoremSemanticProductDP T) := by
  intro n φ hφ
  rw [theoremSemanticProductDP, DeductiveProcess.union_stage, Finset.mem_union] at hφ
  rcases hφ with hbase | hsemantic
  · apply (theoremSemanticProductWorld_holds_base_iff T
      (fun a ha => ?_)).mpr (theoremDP_hworld T n φ hbase)
    simp only [theoremDP, theoremStage, Finset.mem_image, Finset.mem_filter,
      Finset.mem_range] at hbase
    obtain ⟨e, _, rfl⟩ := hbase
    exact eventAtom_atomCodes_ne_semanticPrimeTag e a ha
  · obtain ⟨e, rfl⟩ := semanticProductStageList_exists (List.mem_toFinset.mp hsemantic)
    rw [semanticProductDefSentence]
    exact theoremSemanticProductWorld_holds_schema T _ _ _ _ _ _ _

lemma semanticProductDefSentence_mem_stage (e : ℕ) :
    semanticProductDefSentence e ∈ semanticProductDP.D e :=
  List.mem_toFinset.mpr (mem_semanticProductStageList (le_refl e))

lemma holds_semanticProductDefSentence {v : PCWorld}
    (hv : v.ConsistentWithTheory semanticProductDP) (e : ℕ) :
    v.Holds (semanticProductDefSentence e) :=
  hv e _ (semanticProductDefSentence_mem_stage e)

section

lemma semanticProductDefSentence_job (left right n kind : ℕ) (r : ℚ) (zs zt : ℕ) :
    semanticProductDefSentence (semanticProductJob left right n kind r zs zt) =
      semanticProductSchemaInstance left right n kind r zs zt := by
  simp [semanticProductDefSentence, semanticProductJob, decodedQuotationRat_encode]

lemma holds_semanticProduct_pos {v : PCWorld}
    (hv : v.ConsistentWithTheory semanticProductDP) (left right n : ℕ) {r : ℚ} {zs zt : ℕ}
    (hst : r ≤ meshIndexRat zs * meshIndexRat zt)
    (hX : v.Holds (semanticPrimeSentence left (Nat.pair n (Encodable.encode (meshIndexRat zs)))))
    (hW : v.Holds (semanticPrimeSentence right (Nat.pair n (Encodable.encode (meshIndexRat zt)))) ) :
    v.Holds (semanticProductAtom left right n r) := by
  have h := holds_semanticProductDefSentence hv (semanticProductJob left right n 0 r zs zt)
  rw [semanticProductDefSentence_job, semanticProductSchemaInstance,
    if_pos rfl, if_pos hst] at h
  exact h ⟨hX, hW⟩

lemma not_holds_semanticProduct_neg {v : PCWorld}
    (hv : v.ConsistentWithTheory semanticProductDP) (left right n : ℕ) {r : ℚ} {zs zt : ℕ}
    (hst : meshIndexRat zs * meshIndexRat zt ≤ r)
    (hX : ¬ v.Holds (semanticPrimeSentence left (Nat.pair n (Encodable.encode (meshIndexRat zs)))))
    (hW : ¬ v.Holds (semanticPrimeSentence right (Nat.pair n (Encodable.encode (meshIndexRat zt)))) ) :
    ¬ v.Holds (semanticProductAtom left right n r) := by
  have h := holds_semanticProductDefSentence hv (semanticProductJob left right n 1 r zs zt)
  rw [semanticProductDefSentence_job, semanticProductSchemaInstance,
    if_neg (by decide : ¬ (1 : ℕ) = 0), if_pos rfl, if_pos hst] at h
  intro hp
  rcases h hp with hx | hw
  · exact hX hx
  · exact hW hw

lemma holds_semanticProduct_below {v : PCWorld}
    (hv : v.ConsistentWithTheory semanticProductDP) (left right n : ℕ) {r : ℚ} (hr : r < 0) :
    v.Holds (semanticProductAtom left right n r) := by
  have h := holds_semanticProductDefSentence hv (semanticProductJob left right n 2 r 0 0)
  rw [semanticProductDefSentence_job, semanticProductSchemaInstance,
    if_neg (by decide : ¬ (2 : ℕ) = 0), if_neg (by decide : ¬ (2 : ℕ) = 1), if_pos hr] at h
  exact h

end

lemma exists_of_mem_semanticProductStageList {φ : Sentence} {k : ℕ}
    (h : φ ∈ semanticProductStageList k) : ∃ e, φ = semanticProductDefSentence e := by
  induction k with
  | zero => exact ⟨0, by simpa [semanticProductStageList] using h⟩
  | succ k ih =>
      rcases List.mem_cons.mp h with h | h
      · exact ⟨k + 1, h⟩
      · exact ih h

/-- Every stage of the fixed semantic closure has a canonical satisfying world. -/
lemma semanticProductDP_hworld :
    semanticProductWorld.ConsistentWithTheory semanticProductDP := by
  intro k φ hφ
  obtain ⟨e, rfl⟩ := exists_of_mem_semanticProductStageList (List.mem_toFinset.mp hφ)
  rw [semanticProductDefSentence]
  exact semanticProductWorld_holds_schema _ _ _ _ _ _ _

/-- Exact product reflection over the single fixed semantic closure process.  This is the
existing `productLUV_valuesAt` rational-density proof with only the three schema lookups
replaced by their self-describing semantic-prime counterparts. -/
lemma semanticProductLUV_valuesAt {v : PCWorld}
    (hv : v.ConsistentWithTheory semanticProductDP) (X W : PresentedLUVSeq) (n : ℕ)
    {x c : ℝ} (hx : v.ValuesAt (X.toLUV n) x) (hc : v.ValuesAt (W.toLUV n) c) :
    v.ValuesAt (semanticProductLUV X W n) (x * c) := by
  obtain ⟨hx0, hx1, hxthr⟩ := hx
  obtain ⟨hc0, hc1, hcthr⟩ := hc
  refine ⟨mul_nonneg hx0 hc0, by nlinarith, fun r => ⟨?_, ?_⟩⟩
  · intro hr
    rw [semanticProductLUV_gt]
    rcases lt_or_ge r 0 with hneg | hpos
    · exact holds_semanticProduct_below hv X.thresholdSchema W.thresholdSchema n hneg
    · obtain ⟨s, t, hs0, ht0, hst, hsx, htc⟩ := exists_rat_pair_lt_mul hx0 hc0 hpos hr
      obtain ⟨zs, rfl⟩ := exists_meshIndexRat hs0
      obtain ⟨zt, rfl⟩ := exists_meshIndexRat ht0
      exact holds_semanticProduct_pos hv X.thresholdSchema W.thresholdSchema n hst
        (by simpa only [PresentedLUVSeq.gt_eq] using (hxthr _).1 hsx)
        (by simpa only [PresentedLUVSeq.gt_eq] using (hcthr _).1 htc)
  · intro hr
    rw [semanticProductLUV_gt]
    obtain ⟨s, t, hs0, ht0, hst, hxs, hct⟩ := exists_rat_pair_mul_lt hx0 hc0 hr
    obtain ⟨zs, rfl⟩ := exists_meshIndexRat hs0
    obtain ⟨zt, rfl⟩ := exists_meshIndexRat ht0
    exact not_holds_semanticProduct_neg hv X.thresholdSchema W.thresholdSchema n hst
      (by simpa only [PresentedLUVSeq.gt_eq] using (hxthr _).2 hxs)
      (by simpa only [PresentedLUVSeq.gt_eq] using (hcthr _).2 hct)

/-! ## `def:ec` for semantic products -/

lemma semanticProductAtom_mesh_encode_polyFueled (left right : ℕ) :
    ∃ c, PolyFueled c (fun m => Encodable.encode (semanticProductAtom left right m.unpair.1
      ((m.unpair.2.unpair.2 : ℚ) / (m.unpair.2.unpair.1 : ℚ)))) := by
  obtain ⟨cg, hgcd⟩ := gcdc_polyFueled
  obtain ⟨cdm, hdm⟩ := divmod1_polyFueled
  obtain ⟨cad, had⟩ := addc_polyFueled
  have hn := PolyFueled.left
  have hk := PolyFueled.left.comp PolyFueled.right
  have hi := PolyFueled.right.comp PolyFueled.right
  have gPF := hgcd.comp (hi.pair hk)
  have pgPF := predc_polyFueled.comp gPF
  have numPF := PolyFueled.left.comp (hdm.comp (pgPF.pair hi))
  have denPF := PolyFueled.left.comp (hdm.comp (pgPF.pair hk))
  have h2num := had.comp (numPF.pair numPF)
  have meshPF := ifzSel_polyFueled.comp
    (((PolyFueled.const (Nat.pair 0 1)).pair (h2num.pair denPF)).pair hk)
  have fullPF := ((PolyFueled.const 1).pair
    ((PolyFueled.const semanticPrimeTag).pair
      ((PolyFueled.const (semanticProductSchema left right)).pair (hn.pair meshPF)))).succ_comp
  refine ⟨_, fullPF.of_eq (fun m => ?_)⟩
  rw [semanticProductAtom, semanticPrimeSentence, semanticPrimeCode, encode_atom]
  simp only [Nat.unpair_pair, ifzSelFn]
  by_cases hk0 : m.unpair.2.unpair.1 = 0
  · rw [if_pos hk0, hk0]
    norm_num
    rfl
  · rw [if_neg hk0]
    have hg : 0 < Nat.gcd m.unpair.2.unpair.2 m.unpair.2.unpair.1 :=
      Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero hk0)
    have hg1 : (Nat.gcd m.unpair.2.unpair.2 m.unpair.2.unpair.1).pred + 1 =
        Nat.gcd m.unpair.2.unpair.2 m.unpair.2.unpair.1 :=
      Nat.succ_pred_eq_of_pos hg
    rw [hg1, encode_rat_natCast_div hk0, two_mul]

lemma semanticProductLUV_polyThresholdCodeSeq (X W : PresentedLUVSeq) :
    LUV.PolyThresholdCodeSeq (semanticProductLUV X W) := by
  obtain ⟨c, hc⟩ := semanticProductAtom_mesh_encode_polyFueled X.thresholdSchema W.thresholdSchema
  exact ⟨c, hc.of_eq (fun m => by rw [semanticProductLUV_gt])⟩

lemma semanticProductLUV_rpnThresholdCodeSeq (X W : PresentedLUVSeq) :
    LUV.RpnThresholdCodeSeq (semanticProductLUV X W) :=
  LUV.RpnThresholdCodeSeq.ofPolyThresholdCodeSeq
    (semanticProductLUV_polyThresholdCodeSeq X W)

/-! ## Exact conditional expectation over the fixed process -/

/-- The paper's conditional-expectation conclusion with the exact semantic product, over
the single process fixed from `T` before the market and all source data are chosen. -/
lemma lic_no_expected_net_update_conditional_semantic
    {T : ArithmeticTheory} [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]
    {P : History} [IsLogicalInductor P (theoremSemanticProductDP T)]
    (f : DeferralFunction) (X W : PresentedLUVSeq) (Z' : ℕ → LUV) (w : ℕ → ℚ)
    (weight_mem : ∀ n, 0 ≤ w n ∧ w n ≤ 1)
    (weight_generable : PGenerableRat P w)
    (hZ' : LUV.RpnThresholdCodeSeq Z')
    (source_valued : ∀ n (v : PCWorld), v.ConsistentWithTheory (theoremSemanticProductDP T) →
      ∃ x, v.ValuesAt (X.toLUV n) x)
    (weight_valued : ∀ n (v : PCWorld), v.ConsistentWithTheory (theoremSemanticProductDP T) →
      v.ValuesAt (W.toLUV n) (w (f n)))
    (right_reflected : ∀ n (v : PCWorld), v.ConsistentWithTheory (theoremSemanticProductDP T) →
      v.ValuesAt (Z' n) ((X.toLUV n).expect P (f n) * w (f n))) :
    (fun n ↦ (semanticProductLUV X W n).expect P n) ≈ₙ
      fun n ↦ (Z' n).expect P n := by
  refine lic_no_expected_net_update_conditional_ofRepresentation
    (DP := theoremSemanticProductDP T) f X.toLUV (semanticProductLUV X W) Z' w
    weight_mem weight_generable X.threshold_codes (semanticProductLUV_rpnThresholdCodeSeq X W)
    hZ' (fun _ => 0) tendsto_const_nhds source_valued (fun n v hv x hx => ?_)
    right_reflected (fun n => ⟨theoremSemanticProductWorld T,
      (theoremSemanticProductDP_hworld T) n⟩)
  refine ⟨x * (w (f n) : ℝ), ?_, by simp⟩
  exact semanticProductLUV_valuesAt
    (PCWorld.consistentWithTheory_union_right hv) X W n hx (weight_valued n v hv)

private noncomputable abbrev theoremSemanticProductLIA (T : ArithmeticTheory)
    [T.Δ₁] [Entailment.Consistent T] :
    IsLogicalInductor (liaHistory (theoremSemanticProductDP T)) (theoremSemanticProductDP T) :=
  LIA_is_logical_inductor _ (theoremSemanticProductDPComputation T).toComputable

/-- Closed-process form of the exact semantic endpoint: the inductor and its completed
worlds are constructed internally.  Its remaining hypotheses are precisely the paper's
source/weight/right-quotation representation premises, now carried by semantic-prime LUV
presentations rather than a mesh approximation. -/
lemma lic_no_expected_net_update_conditional_semantic_closed
    (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]
    (f : DeferralFunction) (X W : PresentedLUVSeq) (Z' : ℕ → LUV) (w : ℕ → ℚ)
    (weight_mem : ∀ n, 0 ≤ w n ∧ w n ≤ 1)
    (weight_generable : PGenerableRat (liaHistory (theoremSemanticProductDP T)) w)
    (hZ' : LUV.RpnThresholdCodeSeq Z')
    (source_valued : ∀ n (v : PCWorld), v.ConsistentWithTheory (theoremSemanticProductDP T) →
      ∃ x, v.ValuesAt (X.toLUV n) x)
    (weight_valued : ∀ n (v : PCWorld), v.ConsistentWithTheory (theoremSemanticProductDP T) →
      v.ValuesAt (W.toLUV n) (w (f n)))
    (right_reflected : ∀ n (v : PCWorld), v.ConsistentWithTheory (theoremSemanticProductDP T) →
      v.ValuesAt (Z' n) ((X.toLUV n).expect
        (liaHistory (theoremSemanticProductDP T)) (f n) * w (f n))) :
    (fun n ↦ (semanticProductLUV X W n).expect
      (liaHistory (theoremSemanticProductDP T)) n) ≈ₙ
      fun n ↦ (Z' n).expect (liaHistory (theoremSemanticProductDP T)) n := by
  haveI := theoremSemanticProductLIA T
  exact lic_no_expected_net_update_conditional_semantic f X W Z' w weight_mem
    weight_generable hZ' source_valued weight_valued right_reflected

end LogicalInduction
