import LogicalInduction.Construction.Witnesses.SemanticSourceDP
import LogicalInduction.Construction.Witnesses.SemanticProduct
import LogicalInduction.Construction.Witnesses.SemanticCertifiedProduct

/-!
# Registry-guarded exact semantic products

The tag-only product gate is too weak: a malformed program can claim the source namespace.
This process instead dovetails over product jobs and checker fuel, activating a product clause
only after both named factors pass the fixed coherent-cut registry on the finite prefix needed
by that job.  The process depends only on the already fixed base-process computation.
-/

namespace LogicalInduction

open LO LO.Propositional LO.FirstOrder LO.FirstOrder.Arithmetic

attribute [local irreducible] Nat.sqrt

/-- The finite source-query prefix needed to justify a decoded product job. -/
def semanticRegistryProductLimit (e : ℕ) : ℕ :=
  max e.unpair.2.unpair.2.unpair.1 <|
    max (Encodable.encode (meshIndexRat
      e.unpair.2.unpair.2.unpair.2.unpair.2.unpair.2.unpair.1))
      (Encodable.encode (meshIndexRat
        e.unpair.2.unpair.2.unpair.2.unpair.2.unpair.2.unpair.2))

/-- Decode a universal registry-product task as `(productJob, checkerFuel)`. -/
def semanticRegistryProductDefSentence {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) (q : ℕ) : Sentence :=
  let e := q.unpair.1
  let fuel := q.unpair.2
  let left := e.unpair.1
  let right := e.unpair.2.unpair.1
  let limit := semanticRegistryProductLimit e
  bif (left.unpair.1 == 0) && (right.unpair.1 == 0) &&
      semanticSourcePrefixValidAtFuel base left limit fuel &&
      semanticSourcePrefixValidAtFuel base right limit fuel then
    semanticProductDefSentence e
  else ⊤

def semanticRegistryProductStageList {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) : ℕ → List Sentence
  | 0 => [semanticRegistryProductDefSentence base 0]
  | k + 1 => semanticRegistryProductDefSentence base (k + 1) ::
      semanticRegistryProductStageList base k

lemma mem_semanticRegistryProductStageList {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) {q k : ℕ} (h : q ≤ k) :
    semanticRegistryProductDefSentence base q ∈
      semanticRegistryProductStageList base k := by
  induction k with
  | zero => simp [semanticRegistryProductStageList, Nat.le_zero.mp h]
  | succ k ih =>
      rcases Nat.lt_or_ge q (k + 1) with hlt | hge
      · exact List.mem_cons_of_mem _ (ih (Nat.lt_succ_iff.mp hlt))
      · have hq : q = k + 1 := le_antisymm h hge
        simp [semanticRegistryProductStageList, hq]

lemma semanticRegistryProductStageList_exists {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) {φ : Sentence} {k : ℕ}
    (h : φ ∈ semanticRegistryProductStageList base k) :
    ∃ q, φ = semanticRegistryProductDefSentence base q := by
  induction k with
  | zero => exact ⟨0, by simpa [semanticRegistryProductStageList] using h⟩
  | succ k ih =>
      rcases List.mem_cons.mp h with h | h
      · exact ⟨k + 1, h⟩
      · exact ih h

/-- Fixed exact-product closure for sources admitted by `base`'s executable registry. -/
def semanticRegistryProductDP {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) : DeductiveProcess where
  D k := (semanticRegistryProductStageList base k).toFinset
  mono k := by
    intro φ hφ
    simp only [List.mem_toFinset] at hφ ⊢
    exact List.mem_cons_of_mem _ hφ

lemma semanticRegistryProductLimit_prim : Primrec semanticRegistryProductLimit := by
  have he : Primrec fun e : ℕ => e.unpair.2 := Primrec.snd.comp Primrec.unpair
  have heb : Primrec fun e : ℕ => e.unpair.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp he)
  have hec : Primrec fun e : ℕ => e.unpair.2.unpair.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp heb)
  have hed : Primrec fun e : ℕ => e.unpair.2.unpair.2.unpair.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp hec)
  have hee : Primrec fun e : ℕ => e.unpair.2.unpair.2.unpair.2.unpair.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp hed)
  have hn : Primrec fun e : ℕ => e.unpair.2.unpair.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp heb)
  have hzs : Primrec fun e : ℕ =>
      e.unpair.2.unpair.2.unpair.2.unpair.2.unpair.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp hee)
  have hzt : Primrec fun e : ℕ =>
      e.unpair.2.unpair.2.unpair.2.unpair.2.unpair.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp hee)
  have hsz : Primrec fun e : ℕ => Encodable.encode (meshIndexRat
      e.unpair.2.unpair.2.unpair.2.unpair.2.unpair.2.unpair.1) :=
    Primrec.encode.comp (meshIndexRat_prim.comp hzs)
  have htz : Primrec fun e : ℕ => Encodable.encode (meshIndexRat
      e.unpair.2.unpair.2.unpair.2.unpair.2.unpair.2.unpair.2) :=
    Primrec.encode.comp (meshIndexRat_prim.comp hzt)
  exact Primrec.nat_max.comp hn (Primrec.nat_max.comp hsz htz)

set_option maxHeartbeats 2000000 in
lemma semanticRegistryProductDefSentence_computable {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) :
    Computable (semanticRegistryProductDefSentence base) := by
  classical
  have he : Primrec fun q : ℕ => q.unpair.1 := Primrec.fst.comp Primrec.unpair
  have hfuel : Primrec fun q : ℕ => q.unpair.2 := Primrec.snd.comp Primrec.unpair
  have hleft : Primrec fun q : ℕ => q.unpair.1.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp he)
  have hright : Primrec fun q : ℕ => q.unpair.1.unpair.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp
      (Primrec.snd.comp (Primrec.unpair.comp he)))
  have hlimit : Primrec fun q : ℕ => semanticRegistryProductLimit q.unpair.1 :=
    semanticRegistryProductLimit_prim.comp he
  have hlpack : Primrec fun q : ℕ =>
      ((q.unpair.1.unpair.1, semanticRegistryProductLimit q.unpair.1), q.unpair.2) :=
    (hleft.pair hlimit).pair hfuel
  have hrpack : Primrec fun q : ℕ =>
      ((q.unpair.1.unpair.2.unpair.1, semanticRegistryProductLimit q.unpair.1),
        q.unpair.2) :=
    (hright.pair hlimit).pair hfuel
  have hlvalid : Primrec fun q : ℕ => semanticSourcePrefixValidAtFuel base
      q.unpair.1.unpair.1 (semanticRegistryProductLimit q.unpair.1) q.unpair.2 :=
    (semanticSourcePrefixValidAtFuel_prim base).comp hlpack
  have hrvalid : Primrec fun q : ℕ => semanticSourcePrefixValidAtFuel base
      q.unpair.1.unpair.2.unpair.1 (semanticRegistryProductLimit q.unpair.1) q.unpair.2 :=
    (semanticSourcePrefixValidAtFuel_prim base).comp hrpack
  have hltag : Primrec fun q : ℕ => q.unpair.1.unpair.1.unpair.1 == 0 :=
    (Primrec.eq.comp
      (Primrec.fst.comp (Primrec.unpair.comp hleft)) (Primrec.const 0)).decide
  have hrtag : Primrec fun q : ℕ => q.unpair.1.unpair.2.unpair.1.unpair.1 == 0 :=
    (Primrec.eq.comp
      (Primrec.fst.comp (Primrec.unpair.comp hright)) (Primrec.const 0)).decide
  have hguard : Computable fun q : ℕ =>
      (q.unpair.1.unpair.1.unpair.1 == 0) &&
      (q.unpair.1.unpair.2.unpair.1.unpair.1 == 0) &&
      semanticSourcePrefixValidAtFuel base q.unpair.1.unpair.1
        (semanticRegistryProductLimit q.unpair.1) q.unpair.2 &&
      semanticSourcePrefixValidAtFuel base q.unpair.1.unpair.2.unpair.1
        (semanticRegistryProductLimit q.unpair.1) q.unpair.2 :=
    (Primrec.dom_bool₂ (· && ·)).comp
      ((Primrec.dom_bool₂ (· && ·)).comp
        ((Primrec.dom_bool₂ (· && ·)).comp hltag hrtag) hlvalid) hrvalid |>.to_comp
  exact Computable.cond hguard (semanticProductDefSentence_computable.comp he.to_comp)
    (Computable.const (⊤ : Sentence))

lemma semanticRegistryProductDP_computable {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) :
    ComputableDeductiveProcess (semanticRegistryProductDP base) := by
  have hlist : Computable (semanticRegistryProductStageList base) := by
    have hstep : Computable fun p : ℕ × List Sentence =>
        semanticRegistryProductDefSentence base (p.1 + 1) :: p.2 :=
      Computable.list_cons.comp
        (semanticRegistryProductDefSentence_computable base |>.comp
          (Primrec.succ.to_comp.comp Computable.fst)) Computable.snd
    refine (Computable.nat_rec Computable.id
      (Computable.const [semanticRegistryProductDefSentence base 0])
      (hstep.comp₂ Computable.snd.to₂)).of_eq (fun k => ?_)
    induction k with
    | zero => rfl
    | succ k ih => simpa [semanticRegistryProductStageList] using ih
  have hkey : Computable fun k => Encodable.encode
      ((sentenceDedup (semanticRegistryProductStageList base k)).insertionSort sentenceCodeLE) :=
    Computable.encode.comp
      ((sentenceInsertionSort_prim.comp sentenceDedup_prim).to_comp.comp hlist)
  obtain ⟨code, hcode⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hkey)
  refine ⟨code, fun k => ?_⟩
  rw [hcode]
  exact Part.mem_some_iff.mpr
    (encode_toFinset_eq (semanticRegistryProductStageList base k))

lemma semanticRegistryProductDefSentence_mem_stage {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) (q : ℕ) :
    semanticRegistryProductDefSentence base q ∈ (semanticRegistryProductDP base).D q :=
  List.mem_toFinset.mpr (mem_semanticRegistryProductStageList base (le_refl q))

lemma holds_semanticRegistryProductDefSentence {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) {v : PCWorld}
    (hv : v.ConsistentWithTheory (semanticRegistryProductDP base)) (q : ℕ) :
    v.Holds (semanticRegistryProductDefSentence base q) :=
  hv q _ (semanticRegistryProductDefSentence_mem_stage base q)

/-- Every product clause whose two factors are genuine certified sources is eventually
activated by the fixed registry process. -/
lemma holds_semanticRegistryProduct_schema {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) {v : PCWorld}
    (hv : v.ConsistentWithTheory (semanticRegistryProductDP base))
    (X W : CertifiedSourceLUVSeq DP) (n kind : ℕ) (r : ℚ) (zs zt : ℕ) :
    v.Holds (semanticProductSchemaInstance X.thresholdSchema W.thresholdSchema
      n kind r zs zt) := by
  let e := semanticProductJob X.thresholdSchema W.thresholdSchema n kind r zs zt
  let limit := semanticRegistryProductLimit e
  obtain ⟨fx, hX⟩ := certifiedSourcePrefix_eventually_valid base X limit
  obtain ⟨fw, hW⟩ := certifiedSourcePrefix_eventually_valid base W limit
  let fuel := max fx fw
  have hX' : semanticSourcePrefixValidAtFuel base X.thresholdSchema limit fuel = true :=
    semanticSourcePrefixValidAtFuel_mono base (Nat.le_max_left _ _) hX
  have hW' : semanticSourcePrefixValidAtFuel base W.thresholdSchema limit fuel = true :=
    semanticSourcePrefixValidAtFuel_mono base (Nat.le_max_right _ _) hW
  have hX'' : semanticSourcePrefixValidAtFuel base X.thresholdSchema
      (semanticRegistryProductLimit e) fuel = true := by simpa [limit] using hX'
  have hW'' : semanticSourcePrefixValidAtFuel base W.thresholdSchema
      (semanticRegistryProductLimit e) fuel = true := by simpa [limit] using hW'
  have h := holds_semanticRegistryProductDefSentence base hv (Nat.pair e fuel)
  have heleft : e.unpair.1 = X.thresholdSchema := by simp [e, semanticProductJob]
  have heright : e.unpair.2.unpair.1 = W.thresholdSchema := by
    simp [e, semanticProductJob]
  have h' : v.Holds (semanticProductDefSentence e) := by
    simp only [semanticRegistryProductDefSentence, Nat.unpair_pair, heleft, heright,
      X.thresholdSchema_source, W.thresholdSchema_source, beq_self_eq_true,
      Bool.true_and, hX'', hW'', Bool.and_self, cond_true] at h
    exact h
  simpa [e, semanticProductDefSentence_job] using h'

lemma holds_semanticRegistryProduct_pos {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) {v : PCWorld}
    (hv : v.ConsistentWithTheory (semanticRegistryProductDP base))
    (X W : CertifiedSourceLUVSeq DP) (n : ℕ) {r : ℚ} {zs zt : ℕ}
    (hst : r ≤ meshIndexRat zs * meshIndexRat zt)
    (hX : v.Holds (semanticPrimeSentence X.thresholdSchema
      (Nat.pair n (Encodable.encode (meshIndexRat zs)))))
    (hW : v.Holds (semanticPrimeSentence W.thresholdSchema
      (Nat.pair n (Encodable.encode (meshIndexRat zt))))) :
    v.Holds (semanticProductAtom X.thresholdSchema W.thresholdSchema n r) := by
  have h := holds_semanticRegistryProduct_schema base hv X W n 0 r zs zt
  rw [semanticProductSchemaInstance, if_pos rfl, if_pos hst] at h
  exact h ⟨hX, hW⟩

lemma not_holds_semanticRegistryProduct_neg {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) {v : PCWorld}
    (hv : v.ConsistentWithTheory (semanticRegistryProductDP base))
    (X W : CertifiedSourceLUVSeq DP) (n : ℕ) {r : ℚ} {zs zt : ℕ}
    (hst : meshIndexRat zs * meshIndexRat zt ≤ r)
    (hX : ¬v.Holds (semanticPrimeSentence X.thresholdSchema
      (Nat.pair n (Encodable.encode (meshIndexRat zs)))))
    (hW : ¬v.Holds (semanticPrimeSentence W.thresholdSchema
      (Nat.pair n (Encodable.encode (meshIndexRat zt))))) :
    ¬v.Holds (semanticProductAtom X.thresholdSchema W.thresholdSchema n r) := by
  have h := holds_semanticRegistryProduct_schema base hv X W n 1 r zs zt
  rw [semanticProductSchemaInstance, if_neg (by decide : ¬(1 : ℕ) = 0),
    if_pos rfl, if_pos hst] at h
  intro hp
  rcases h hp with hx | hw
  · exact hX hx
  · exact hW hw

lemma holds_semanticRegistryProduct_below {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) {v : PCWorld}
    (hv : v.ConsistentWithTheory (semanticRegistryProductDP base))
    (X W : CertifiedSourceLUVSeq DP) (n : ℕ) {r : ℚ} (hr : r < 0) :
    v.Holds (semanticProductAtom X.thresholdSchema W.thresholdSchema n r) := by
  have h := holds_semanticRegistryProduct_schema base hv X W n 2 r 0 0
  simpa [semanticProductSchemaInstance, hr] using h

/-- Registry admission recovers exact multiplication for arbitrary certified factors. -/
theorem semanticRegistryProductLUV_valuesAt {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) {v : PCWorld}
    (hv : v.ConsistentWithTheory (semanticRegistryProductDP base))
    (X W : CertifiedSourceLUVSeq DP) (n : ℕ) {x c : ℝ}
    (hx : v.ValuesAt (X.toPresented.toLUV n) x)
    (hc : v.ValuesAt (W.toPresented.toLUV n) c) :
    v.ValuesAt (semanticProductLUV X.toPresented W.toPresented n) (x * c) := by
  obtain ⟨hx0, hx1, hxthr⟩ := hx
  obtain ⟨hc0, hc1, hcthr⟩ := hc
  refine ⟨mul_nonneg hx0 hc0, by nlinarith, fun r => ⟨?_, ?_⟩⟩
  · intro hr
    rw [semanticProductLUV_gt]
    rcases lt_or_ge r 0 with hneg | hpos
    · exact holds_semanticRegistryProduct_below base hv X W n hneg
    · obtain ⟨s, t, hs0, ht0, hst, hsx, htc⟩ :=
        exists_rat_pair_lt_mul hx0 hc0 hpos hr
      obtain ⟨zs, rfl⟩ := exists_meshIndexRat hs0
      obtain ⟨zt, rfl⟩ := exists_meshIndexRat ht0
      exact holds_semanticRegistryProduct_pos base hv X W n hst
        (by simpa only [CertifiedSourceLUVSeq.toPresented_gt] using (hxthr _).1 hsx)
        (by simpa only [CertifiedSourceLUVSeq.toPresented_gt] using (hcthr _).1 htc)
  · intro hr
    rw [semanticProductLUV_gt]
    obtain ⟨s, t, hs0, ht0, hst, hxs, hct⟩ :=
      exists_rat_pair_mul_lt hx0 hc0 hr
    obtain ⟨zs, rfl⟩ := exists_meshIndexRat hs0
    obtain ⟨zt, rfl⟩ := exists_meshIndexRat ht0
    exact not_holds_semanticRegistryProduct_neg base hv X W n hst
      (by simpa only [CertifiedSourceLUVSeq.toPresented_gt] using (hxthr _).2 hxs)
      (by simpa only [CertifiedSourceLUVSeq.toPresented_gt] using (hcthr _).2 hct)

lemma semanticRegistryProductLimit_job_n (left right n kind : ℕ) (r : ℚ) (zs zt : ℕ) :
    n ≤ semanticRegistryProductLimit (semanticProductJob left right n kind r zs zt) := by
  simp [semanticRegistryProductLimit, semanticProductJob]

lemma semanticRegistryProductLimit_job_left (left right n kind : ℕ)
    (r : ℚ) (zs zt : ℕ) :
    Encodable.encode (meshIndexRat zs) ≤
      semanticRegistryProductLimit (semanticProductJob left right n kind r zs zt) := by
  simp [semanticRegistryProductLimit, semanticProductJob]

lemma semanticRegistryProductLimit_job_right (left right n kind : ℕ)
    (r : ℚ) (zs zt : ℕ) :
    Encodable.encode (meshIndexRat zt) ≤
      semanticRegistryProductLimit (semanticProductJob left right n kind r zs zt) := by
  simp [semanticRegistryProductLimit, semanticProductJob]

/-! ## Canonical joint model -/

/-- Positive closure of one product atom over an already interpreted source world. -/
def semanticRegistryProductPositive {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) (v : PCWorld)
    (left right n : ℕ) (r : ℚ) : Prop :=
  ∃ zs zt fuel,
    let e := semanticProductJob left right n 0 r zs zt
    semanticSourcePrefixValidAtFuel base left (semanticRegistryProductLimit e) fuel = true ∧
    semanticSourcePrefixValidAtFuel base right (semanticRegistryProductLimit e) fuel = true ∧
    r ≤ meshIndexRat zs * meshIndexRat zt ∧
    v.Holds (semanticPrimeSentence left
      (Nat.pair n (Encodable.encode (meshIndexRat zs)))) ∧
    v.Holds (semanticPrimeSentence right
      (Nat.pair n (Encodable.encode (meshIndexRat zt))) )

/-- Extend a source world by interpreting tag-`1` product atoms as the positive closure
of exactly those finite clauses admitted by the registry. -/
noncomputable def semanticRegistryProductExtensionWorld {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) (v : PCWorld) : PCWorld := fun a =>
  if a.unpair.1 = semanticPrimeTag ∧ a.unpair.2.unpair.1.unpair.1 = 1 then
    let schema := a.unpair.2.unpair.1
    let input := a.unpair.2.unpair.2
    let left := schema.unpair.2.unpair.1
    let right := schema.unpair.2.unpair.2
    let n := input.unpair.1
    let r := decodedQuotationRat input.unpair.2
    r < 0 ∨ semanticRegistryProductPositive base v left right n r
  else v a

lemma semanticRegistryProductExtensionWorld_agree {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) (v : PCWorld) {a : ℕ}
    (ha : ¬(a.unpair.1 = semanticPrimeTag ∧ a.unpair.2.unpair.1.unpair.1 = 1)) :
    semanticRegistryProductExtensionWorld base v a ↔ v a := by
  simp [semanticRegistryProductExtensionWorld, ha]

lemma semanticRegistryProductExtensionWorld_leaf {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) (v : PCWorld)
    (schema input : ℕ) (hschema : schema.unpair.1 ≠ 1) :
    (semanticRegistryProductExtensionWorld base v).Holds
        (semanticPrimeSentence schema input) ↔
      v.Holds (semanticPrimeSentence schema input) := by
  change semanticRegistryProductExtensionWorld base v (semanticPrimeCode schema input) ↔ _
  apply semanticRegistryProductExtensionWorld_agree
  simp [semanticPrimeCode, hschema]

lemma semanticRegistryProductExtensionWorld_holds_fresh {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) (v : PCWorld) {φ : Sentence}
    (hφ : SemanticPrimeFreshSentence φ) :
    (semanticRegistryProductExtensionWorld base v).Holds φ ↔ v.Holds φ :=
  PCWorld.holds_congr_atomCodes φ fun a ha =>
    semanticRegistryProductExtensionWorld_agree base v (by
      intro hproduct
      exact hφ a ha hproduct.1)

lemma semanticRegistryProductExtensionWorld_productAtom {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) (v : PCWorld)
    (left right n : ℕ) (r : ℚ) :
    (semanticRegistryProductExtensionWorld base v).Holds
        (semanticProductAtom left right n r) ↔
      r < 0 ∨ semanticRegistryProductPositive base v left right n r := by
  change semanticRegistryProductExtensionWorld base v
    (semanticPrimeCode (semanticProductSchema left right)
      (Nat.pair n (Encodable.encode r))) ↔ _
  simp [semanticRegistryProductExtensionWorld, semanticPrimeCode,
    semanticProductSchema, decodedQuotationRat_encode]

lemma semanticRegistryProductExtensionWorld_downward {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) (v₀ : PCWorld)
    (hv₀ : v₀.ConsistentWithTheory DP) {schema limit fuel n zr zs : ℕ}
    (hvalid : semanticSourcePrefixValidAtFuel base schema limit fuel = true)
    (hn : n ≤ limit) (hzr : zr ≤ limit) (hzs : zs ≤ limit)
    (hrs : decodedQuotationRat zr < decodedQuotationRat zs) :
    (semanticRegistryProductExtensionWorld base
      (semanticSourceExtensionWorld v₀)).Holds
        (semanticPrimeSentence schema
          (Nat.pair n (Encodable.encode (decodedQuotationRat zs)))) →
    (semanticRegistryProductExtensionWorld base
      (semanticSourceExtensionWorld v₀)).Holds
        (semanticPrimeSentence schema
          (Nat.pair n (Encodable.encode (decodedQuotationRat zr)))) := by
  have hseen := semanticSourcePrefixValidAtFuel_downward base hvalid hn hzr hzs hrs
  obtain ⟨f, _, law, hchecked⟩ :=
    (semanticSourceLawSeen_iff base schema
      (sourceCutDownwardJob n (decodedQuotationRat zr)
        (decodedQuotationRat zs)) fuel).1 hseen
  have hschema : schema.unpair.1 = 0 :=
    semanticSourceCheckedLawAtFuel_source base hchecked
  have hne : schema.unpair.1 ≠ 1 := by omega
  intro hs
  have hs' : (semanticSourceExtensionWorld v₀).Holds
      (semanticPrimeSentence schema
        (Nat.pair n (Encodable.encode (decodedQuotationRat zs)))) :=
    (semanticRegistryProductExtensionWorld_leaf base (semanticSourceExtensionWorld v₀)
      schema (Nat.pair n (Encodable.encode (decodedQuotationRat zs))) hne).mp hs
  have hr' := semanticSourceExtensionWorld_downward_of_seen base v₀ hv₀ hrs hseen hs'
  exact (semanticRegistryProductExtensionWorld_leaf base (semanticSourceExtensionWorld v₀)
    schema (Nat.pair n (Encodable.encode (decodedQuotationRat zr))) hne).mpr hr'

lemma semanticRegistryProductExtensionWorld_downward_two_prefixes {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) (v₀ : PCWorld)
    (hv₀ : v₀.ConsistentWithTheory DP) {schema n za zb limitA limitB fuelA fuelB : ℕ}
    (hA : semanticSourcePrefixValidAtFuel base schema limitA fuelA = true)
    (hB : semanticSourcePrefixValidAtFuel base schema limitB fuelB = true)
    (hnA : n ≤ limitA) (hnB : n ≤ limitB)
    (hza : za ≤ limitA) (hzb : zb ≤ limitB)
    (hab : decodedQuotationRat za < decodedQuotationRat zb) :
    (semanticRegistryProductExtensionWorld base
      (semanticSourceExtensionWorld v₀)).Holds
        (semanticPrimeSentence schema
          (Nat.pair n (Encodable.encode (decodedQuotationRat zb)))) →
    (semanticRegistryProductExtensionWorld base
      (semanticSourceExtensionWorld v₀)).Holds
        (semanticPrimeSentence schema
          (Nat.pair n (Encodable.encode (decodedQuotationRat za)))) := by
  rcases le_total limitA limitB with hAB | hBA
  · exact semanticRegistryProductExtensionWorld_downward base v₀ hv₀ hB hnB
      (hza.trans hAB) hzb hab
  · exact semanticRegistryProductExtensionWorld_downward base v₀ hv₀ hA hnA
      hza (hzb.trans hBA) hab

private lemma mul_factor_le_of_nonneg {a b c d : ℚ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hprod : a * b ≤ c * d) : a ≤ c ∨ b ≤ d := by
  by_contra hnot
  push Not at hnot
  nlinarith

set_option maxHeartbeats 2000000 in
/-- Every registry-activated exact-product clause is true in the canonical joint world. -/
lemma semanticRegistryProductExtensionWorld_holds_schema {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) (v₀ : PCWorld)
    (hv₀ : v₀.ConsistentWithTheory DP)
    (left right n kind : ℕ) (r : ℚ) (zs zt fuel : ℕ)
    (hleft0 : left.unpair.1 = 0) (hright0 : right.unpair.1 = 0)
    (hleft : semanticSourcePrefixValidAtFuel base left
      (semanticRegistryProductLimit
        (semanticProductJob left right n kind r zs zt)) fuel = true)
    (hright : semanticSourcePrefixValidAtFuel base right
      (semanticRegistryProductLimit
        (semanticProductJob left right n kind r zs zt)) fuel = true) :
    (semanticRegistryProductExtensionWorld base
      (semanticSourceExtensionWorld v₀)).Holds
        (semanticProductSchemaInstance left right n kind r zs zt) := by
  let sv := semanticSourceExtensionWorld v₀
  let pv := semanticRegistryProductExtensionWorld base sv
  have hleft_ne : left.unpair.1 ≠ 1 := by omega
  have hright_ne : right.unpair.1 ≠ 1 := by omega
  rw [semanticProductSchemaInstance]
  split_ifs with hkind hpos hkind hneg hr
  · intro h
    apply (semanticRegistryProductExtensionWorld_productAtom base sv left right n r).2
    right
    exact ⟨zs, zt, fuel, by simpa [hkind] using hleft,
      by simpa [hkind] using hright, hpos,
      (semanticRegistryProductExtensionWorld_leaf base sv left _ hleft_ne).mp h.1,
      (semanticRegistryProductExtensionWorld_leaf base sv right _ hright_ne).mp h.2⟩
  · exact PCWorld.holds_top _
  · intro hp
    have hp' := (semanticRegistryProductExtensionWorld_productAtom
      base sv left right n r).1 hp
    rcases hp' with hr0 | ⟨zs', zt', fuel', hleft', hright', hpos', hls, hrs⟩
    · have hnonneg : 0 ≤ meshIndexRat zs * meshIndexRat zt :=
        mul_nonneg (meshIndexRat_nonneg zs) (meshIndexRat_nonneg zt)
      exfalso
      linarith
    · have hfactor : meshIndexRat zs ≤ meshIndexRat zs' ∨
          meshIndexRat zt ≤ meshIndexRat zt' :=
        mul_factor_le_of_nonneg (meshIndexRat_nonneg zs) (meshIndexRat_nonneg zt)
          (meshIndexRat_nonneg zs') (meshIndexRat_nonneg zt') (hneg.trans hpos')
      have hleftCur : semanticSourcePrefixValidAtFuel base left
          (semanticRegistryProductLimit
            (semanticProductJob left right n 1 r zs zt)) fuel = true := by
        simpa [hkind] using hleft
      have hrightCur : semanticSourcePrefixValidAtFuel base right
          (semanticRegistryProductLimit
            (semanticProductJob left right n 1 r zs zt)) fuel = true := by
        simpa [hkind] using hright
      rcases hfactor with hsle | htle
      · left
        have hhigh : pv.Holds (semanticPrimeSentence left
            (Nat.pair n (Encodable.encode (meshIndexRat zs')))) :=
          (semanticRegistryProductExtensionWorld_leaf base sv left _ hleft_ne).2 hls
        rcases hsle.eq_or_lt with hEq | hLt
        · change pv.Holds (semanticPrimeSentence left
            (Nat.pair n (Encodable.encode (meshIndexRat zs))))
          rw [hEq]
          exact hhigh
        · change pv.Holds (semanticPrimeSentence left
            (Nat.pair n (Encodable.encode (meshIndexRat zs))))
          simpa only [decodedQuotationRat_encode] using
            (semanticRegistryProductExtensionWorld_downward_two_prefixes
            (schema := left) (n := n)
            (za := Encodable.encode (meshIndexRat zs))
            (zb := Encodable.encode (meshIndexRat zs'))
            (limitA := semanticRegistryProductLimit
              (semanticProductJob left right n 1 r zs zt))
            (limitB := semanticRegistryProductLimit
              (semanticProductJob left right n 0 r zs' zt'))
            (fuelA := fuel) (fuelB := fuel') base v₀ hv₀
            hleftCur hleft'
            (semanticRegistryProductLimit_job_n left right n 1 r zs zt)
            (semanticRegistryProductLimit_job_n left right n 0 r zs' zt')
            (semanticRegistryProductLimit_job_left left right n 1 r zs zt)
            (semanticRegistryProductLimit_job_left left right n 0 r zs' zt')
            (by simpa [decodedQuotationRat_encode] using hLt)
            (by simpa [decodedQuotationRat_encode] using hhigh))
      · right
        have hhigh : pv.Holds (semanticPrimeSentence right
            (Nat.pair n (Encodable.encode (meshIndexRat zt')))) :=
          (semanticRegistryProductExtensionWorld_leaf base sv right _ hright_ne).2 hrs
        rcases htle.eq_or_lt with hEq | hLt
        · change pv.Holds (semanticPrimeSentence right
            (Nat.pair n (Encodable.encode (meshIndexRat zt))))
          rw [hEq]
          exact hhigh
        · change pv.Holds (semanticPrimeSentence right
            (Nat.pair n (Encodable.encode (meshIndexRat zt))))
          simpa only [decodedQuotationRat_encode] using
            (semanticRegistryProductExtensionWorld_downward_two_prefixes
            (schema := right) (n := n)
            (za := Encodable.encode (meshIndexRat zt))
            (zb := Encodable.encode (meshIndexRat zt'))
            (limitA := semanticRegistryProductLimit
              (semanticProductJob left right n 1 r zs zt))
            (limitB := semanticRegistryProductLimit
              (semanticProductJob left right n 0 r zs' zt'))
            (fuelA := fuel) (fuelB := fuel') base v₀ hv₀
            hrightCur hright'
            (semanticRegistryProductLimit_job_n left right n 1 r zs zt)
            (semanticRegistryProductLimit_job_n left right n 0 r zs' zt')
            (semanticRegistryProductLimit_job_right left right n 1 r zs zt)
            (semanticRegistryProductLimit_job_right left right n 0 r zs' zt')
            (by simpa [decodedQuotationRat_encode] using hLt)
            (by simpa [decodedQuotationRat_encode] using hhigh))
  · exact PCWorld.holds_top _
  · exact (semanticRegistryProductExtensionWorld_productAtom base sv left right n r).2
      (Or.inl hr)
  · exact PCWorld.holds_top _

lemma semanticRegistryProductExtensionWorld_holds_defSentence {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) (v₀ : PCWorld)
    (hv₀ : v₀.ConsistentWithTheory DP) (q : ℕ) :
    (semanticRegistryProductExtensionWorld base
      (semanticSourceExtensionWorld v₀)).Holds
        (semanticRegistryProductDefSentence base q) := by
  let e := q.unpair.1
  let fuel := q.unpair.2
  let left := e.unpair.1
  let right := e.unpair.2.unpair.1
  let limit := semanticRegistryProductLimit e
  let guard := (left.unpair.1 == 0) && (right.unpair.1 == 0) &&
    semanticSourcePrefixValidAtFuel base left limit fuel &&
    semanticSourcePrefixValidAtFuel base right limit fuel
  cases hg : guard with
  | false =>
      change (semanticRegistryProductExtensionWorld base
        (semanticSourceExtensionWorld v₀)).Holds
          (bif guard then semanticProductDefSentence e else ⊤)
      rw [hg]
      exact PCWorld.holds_top _
  | true =>
      have hg' : ((left.unpair.1 = 0 ∧ right.unpair.1 = 0) ∧
          semanticSourcePrefixValidAtFuel base left limit fuel = true) ∧
          semanticSourcePrefixValidAtFuel base right limit fuel = true := by
        simpa only [guard, Bool.and_eq_true, beq_iff_eq] using hg
      change (semanticRegistryProductExtensionWorld base
        (semanticSourceExtensionWorld v₀)).Holds
          (bif guard then semanticProductDefSentence e else ⊤)
      rw [hg]
      rw [semanticProductDefSentence]
      exact semanticRegistryProductExtensionWorld_holds_schema base v₀ hv₀
        e.unpair.1 e.unpair.2.unpair.1 e.unpair.2.unpair.2.unpair.1
        e.unpair.2.unpair.2.unpair.2.unpair.1
        (decodedQuotationRat e.unpair.2.unpair.2.unpair.2.unpair.2.unpair.1)
        e.unpair.2.unpair.2.unpair.2.unpair.2.unpair.2.unpair.1
        e.unpair.2.unpair.2.unpair.2.unpair.2.unpair.2.unpair.2 fuel
        (by simpa [left] using hg'.1.1.1) (by simpa [right] using hg'.1.1.2)
        (by simpa [left, right, limit, semanticRegistryProductLimit,
          semanticProductJob, decodedQuotationRat_encode] using hg'.1.2)
        (by simpa [left, right, limit, semanticRegistryProductLimit,
          semanticProductJob, decodedQuotationRat_encode] using hg'.2)

/-- The registry-guarded product process has an explicit model over every model of its
fixed base process. -/
theorem semanticRegistryProductDP_hworld {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) (v₀ : PCWorld)
    (hv₀ : v₀.ConsistentWithTheory DP) :
    (semanticRegistryProductExtensionWorld base
      (semanticSourceExtensionWorld v₀)).ConsistentWithTheory
        (semanticRegistryProductDP base) := by
  intro k φ hφ
  obtain ⟨q, rfl⟩ := semanticRegistryProductStageList_exists base
    (List.mem_toFinset.mp hφ)
  exact semanticRegistryProductExtensionWorld_holds_defSentence base v₀ hv₀ q

/-- Adding product atoms preserves every universal source-definition clause. -/
lemma semanticRegistryProductExtensionWorld_holds_sourceDef {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) (v₀ : PCWorld) (e : ℕ) :
    (semanticRegistryProductExtensionWorld base
      (semanticSourceExtensionWorld v₀)).Holds (semanticSourceDefSentence e) := by
  unfold semanticSourceDefSentence
  by_cases hschema : e.unpair.1.unpair.1 = 0
  · rw [if_pos hschema]
    cases hemit : semanticSourceSentenceAtFuel e.unpair.1 e.unpair.2.unpair.1
        e.unpair.2.unpair.2.unpair.2 with
    | none => exact PCWorld.holds_top _
    | some φ =>
        change (semanticRegistryProductExtensionWorld base
          (semanticSourceExtensionWorld v₀)).Holds
            (if semanticPrimeFreshSentenceB φ then
              if e.unpair.2.unpair.2.unpair.1 = 0 then
                φ 🡒 semanticPrimeSentence e.unpair.1 e.unpair.2.unpair.1
              else semanticPrimeSentence e.unpair.1 e.unpair.2.unpair.1 🡒 φ
            else ⊤)
        by_cases hfreshB : semanticPrimeFreshSentenceB φ = true
        · rw [if_pos hfreshB]
          have hfresh := (semanticPrimeFreshSentenceB_eq_true φ).1 hfreshB
          have hformula := semanticRegistryProductExtensionWorld_holds_fresh base
            (semanticSourceExtensionWorld v₀) hfresh
          have hsourceFormula := semanticSourceExtensionWorld_holds_fresh v₀ hfresh
          have hleaf := semanticRegistryProductExtensionWorld_leaf base
            (semanticSourceExtensionWorld v₀) e.unpair.1 e.unpair.2.unpair.1 (by omega)
          have hsource := semanticSourceExtensionWorld_leaf_iff v₀ e.unpair.1
            e.unpair.2.unpair.1 e.unpair.2.unpair.2.unpair.2 hschema hemit hfresh
          by_cases hdir : e.unpair.2.unpair.2.unpair.1 = 0
          · rw [if_pos hdir]
            intro h
            exact hleaf.mpr (hsource.mpr (hsourceFormula.mp (hformula.mp h)))
          · rw [if_neg hdir]
            intro h
            exact hformula.mpr (hsourceFormula.mpr (hsource.mp (hleaf.mp h)))
        · rw [if_neg hfreshB]
          exact PCWorld.holds_top _
  · rw [if_neg hschema]
    exact PCWorld.holds_top _

theorem semanticSourceRegistryProductDP_hworld {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) (v₀ : PCWorld)
    (hv₀ : v₀.ConsistentWithTheory DP) :
    (semanticRegistryProductExtensionWorld base
      (semanticSourceExtensionWorld v₀)).ConsistentWithTheory
        (semanticSourceDP.union (semanticRegistryProductDP base)) := by
  intro k φ hφ
  rw [DeductiveProcess.union_stage, Finset.mem_union] at hφ
  rcases hφ with hsource | hproduct
  · obtain ⟨e, rfl⟩ := semanticSourceStageList_exists (List.mem_toFinset.mp hsource)
    exact semanticRegistryProductExtensionWorld_holds_sourceDef base v₀ e
  · exact semanticRegistryProductDP_hworld base v₀ hv₀ k φ hproduct

/-- The complete registry substrate over a fixed base process. -/
def semanticRegistryClosureDP {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) : DeductiveProcess :=
  (DP.union semanticSourceDP).union (semanticRegistryProductDP base)

noncomputable def semanticRegistryClosureDPComputation {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) :
    DeductiveProcessComputation (semanticRegistryClosureDP base) :=
  (base.union semanticSourceDP_computable.nonemptyComputation.some).union
    (semanticRegistryProductDP_computable base).nonemptyComputation.some

theorem semanticRegistryClosureDP_hworld {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) (v₀ : PCWorld)
    (hv₀ : v₀.ConsistentWithTheory DP)
    (hDPfresh : ∀ k φ, φ ∈ DP.D k → SemanticPrimeFreshSentence φ) :
    (semanticRegistryProductExtensionWorld base
      (semanticSourceExtensionWorld v₀)).ConsistentWithTheory
        (semanticRegistryClosureDP base) := by
  intro k φ hφ
  rw [semanticRegistryClosureDP, DeductiveProcess.union_stage, Finset.mem_union,
    DeductiveProcess.union_stage, Finset.mem_union] at hφ
  rcases hφ with (hbase | hsource) | hproduct
  · exact (semanticRegistryProductExtensionWorld_holds_fresh base
      (semanticSourceExtensionWorld v₀) (hDPfresh k φ hbase)).mpr
        ((semanticSourceExtensionWorld_holds_fresh v₀ (hDPfresh k φ hbase)).mpr
          (hv₀ k φ hbase))
  · obtain ⟨e, rfl⟩ := semanticSourceStageList_exists (List.mem_toFinset.mp hsource)
    exact semanticRegistryProductExtensionWorld_holds_sourceDef base v₀ e
  · exact semanticRegistryProductDP_hworld base v₀ hv₀ k φ hproduct

/-- Canonical theorem/source/exact-product process, fixed from `T` alone. -/
noncomputable def theoremSemanticRegistryProductDP
    (T : ArithmeticTheory) [T.Δ₁] [ISigma 1 ⪯ T]
    [T.SoundOnHierarchy SigmaSymbol.sigma 1] :
    DeductiveProcess :=
  semanticRegistryClosureDP
    ((theoremDP_computable T).nonemptyComputation.some)

noncomputable def theoremSemanticRegistryProductDPComputation
    (T : ArithmeticTheory) [T.Δ₁] [ISigma 1 ⪯ T]
    [T.SoundOnHierarchy SigmaSymbol.sigma 1] :
    DeductiveProcessComputation (theoremSemanticRegistryProductDP T) :=
  semanticRegistryClosureDPComputation
    ((theoremDP_computable T).nonemptyComputation.some)

theorem theoremSemanticRegistryProductDP_hworld
    (T : ArithmeticTheory) [T.Δ₁] [ISigma 1 ⪯ T]
    [T.SoundOnHierarchy SigmaSymbol.sigma 1] :
    (semanticRegistryProductExtensionWorld
      ((theoremDP_computable T).nonemptyComputation.some)
      (semanticSourceExtensionWorld (provabilityWorld T))).ConsistentWithTheory
        (theoremSemanticRegistryProductDP T) :=
  semanticRegistryClosureDP_hworld
    ((theoremDP_computable T).nonemptyComputation.some) (provabilityWorld T)
    (theoremDP_hworld T) (theoremDP_semanticPrimeFresh T)

/-! ## Quotation-aware fixed substrate -/

noncomputable def theoremQuoteBaseDP
    (T : ArithmeticTheory) [T.Δ₁] [ISigma 1 ⪯ T]
    [T.SoundOnHierarchy SigmaSymbol.sigma 1] : DeductiveProcess :=
  (theoremDP T).union semanticQuoteDP

noncomputable def theoremQuoteBaseDPComputation
    (T : ArithmeticTheory) [T.Δ₁] [ISigma 1 ⪯ T]
    [T.SoundOnHierarchy SigmaSymbol.sigma 1] :
    DeductiveProcessComputation (theoremQuoteBaseDP T) :=
  ((theoremDP_computable T).nonemptyComputation.some).union
    semanticQuoteDP_computable.nonemptyComputation.some

noncomputable def theoremQuoteSemanticRegistryProductDP
    (T : ArithmeticTheory) [T.Δ₁] [ISigma 1 ⪯ T]
    [T.SoundOnHierarchy SigmaSymbol.sigma 1] : DeductiveProcess :=
  semanticRegistryClosureDP (theoremQuoteBaseDPComputation T)

noncomputable def theoremQuoteSemanticRegistryProductDPComputation
    (T : ArithmeticTheory) [T.Δ₁] [ISigma 1 ⪯ T]
    [T.SoundOnHierarchy SigmaSymbol.sigma 1] :
    DeductiveProcessComputation (theoremQuoteSemanticRegistryProductDP T) :=
  semanticRegistryClosureDPComputation (theoremQuoteBaseDPComputation T)

private noncomputable abbrev theoremQuoteRegistryWorld
    (T : ArithmeticTheory) [T.Δ₁] [ISigma 1 ⪯ T]
    [T.SoundOnHierarchy SigmaSymbol.sigma 1] : PCWorld :=
  semanticRegistryProductExtensionWorld (theoremQuoteBaseDPComputation T)
    (semanticSourceExtensionWorld (theoremQuoteCertifiedProductWorld T))

lemma theoremQuoteRegistryWorld_quoteLeaf
    (T : ArithmeticTheory) [T.Δ₁] [ISigma 1 ⪯ T]
    [T.SoundOnHierarchy SigmaSymbol.sigma 1] (code input : ℕ) :
    (theoremQuoteRegistryWorld T).Holds (semanticQuoteLeaf code input) ↔
      (theoremQuoteCertifiedProductWorld T).Holds (semanticQuoteLeaf code input) := by
  change (semanticRegistryProductExtensionWorld (theoremQuoteBaseDPComputation T)
      (semanticSourceExtensionWorld (theoremQuoteCertifiedProductWorld T))).Holds
        (semanticPrimeSentence (semanticQuoteSchema code) input) ↔ _
  rw [semanticRegistryProductExtensionWorld_leaf
    (theoremQuoteBaseDPComputation T)
    (semanticSourceExtensionWorld (theoremQuoteCertifiedProductWorld T))
    (semanticQuoteSchema code) input (by simp [semanticQuoteSchema])]
  change semanticSourceExtensionWorld (theoremQuoteCertifiedProductWorld T)
      (semanticPrimeCode (semanticQuoteSchema code) input) ↔
    theoremQuoteCertifiedProductWorld T
      (semanticPrimeCode (semanticQuoteSchema code) input)
  simp [semanticSourceExtensionWorld, semanticPrimeCode, semanticQuoteSchema]

lemma theoremQuoteRegistryWorld_quoteAtom
    (T : ArithmeticTheory) [T.Δ₁] [ISigma 1 ⪯ T]
    [T.SoundOnHierarchy SigmaSymbol.sigma 1] (w : ℕ) :
    (theoremQuoteRegistryWorld T).Holds (quoteAtom w) ↔
      (theoremQuoteCertifiedProductWorld T).Holds (quoteAtom w) := by
  change semanticRegistryProductExtensionWorld (theoremQuoteBaseDPComputation T)
      (semanticSourceExtensionWorld (theoremQuoteCertifiedProductWorld T))
        (quotationClaimCode universalQuotePos universalQuoteNeg w) ↔
    theoremQuoteCertifiedProductWorld T
      (quotationClaimCode universalQuotePos universalQuoteNeg w)
  rw [semanticRegistryProductExtensionWorld_agree]
  · apply semanticSourceExtensionWorld_agree
    simp [quotationClaimCode, semanticPrimeTag]
  · simp [quotationClaimCode, semanticPrimeTag]

lemma theoremQuoteRegistryWorld_consistent_quote
    (T : ArithmeticTheory) [T.Δ₁] [ISigma 1 ⪯ T]
    [T.SoundOnHierarchy SigmaSymbol.sigma 1] :
    (theoremQuoteRegistryWorld T).ConsistentWithTheory semanticQuoteDP := by
  intro k φ hφ
  obtain ⟨e, rfl⟩ := exists_of_mem_semanticQuoteStageList
    (List.mem_toFinset.mp hφ)
  rw [semanticQuoteDefSentence]
  by_cases hkind : e.unpair.1 = 0
  · rw [if_pos hkind]
    intro hbase
    exact (theoremQuoteRegistryWorld_quoteLeaf T _ _).mpr
      ((theoremQuoteCertifiedProductWorld_quote T _ _).mpr
        ((theoremQuoteCertifiedProductWorld_quoteAtom T _).mp
          ((theoremQuoteRegistryWorld_quoteAtom T _).mp hbase)))
  · rw [if_neg hkind]
    intro hleaf
    exact (theoremQuoteRegistryWorld_quoteAtom T _).mpr
      ((theoremQuoteCertifiedProductWorld_quoteAtom T _).mpr
        ((theoremQuoteCertifiedProductWorld_quote T _ _).mp
          ((theoremQuoteRegistryWorld_quoteLeaf T _ _).mp hleaf)))

lemma theoremQuoteCertifiedProductWorld_consistent_base
    (T : ArithmeticTheory) [T.Δ₁] [ISigma 1 ⪯ T]
    [T.SoundOnHierarchy SigmaSymbol.sigma 1] :
    (theoremQuoteCertifiedProductWorld T).ConsistentWithTheory
      (theoremQuoteBaseDP T) := by
  intro k φ hφ
  rw [theoremQuoteBaseDP, DeductiveProcess.union_stage, Finset.mem_union] at hφ
  rcases hφ with htheorem | hquote
  · exact theoremQuoteCertifiedProductWorld_consistent_theorem T k φ htheorem
  · exact theoremQuoteCertifiedProductWorld_consistent_quote T k φ hquote

lemma theoremQuoteRegistryWorld_consistent_theorem
    (T : ArithmeticTheory) [T.Δ₁] [ISigma 1 ⪯ T]
    [T.SoundOnHierarchy SigmaSymbol.sigma 1] :
    (theoremQuoteRegistryWorld T).ConsistentWithTheory (theoremDP T) := by
  intro k φ hφ
  have hfresh := theoremDP_semanticPrimeFresh T k φ hφ
  exact (semanticRegistryProductExtensionWorld_holds_fresh
      (theoremQuoteBaseDPComputation T)
      (semanticSourceExtensionWorld (theoremQuoteCertifiedProductWorld T)) hfresh).mpr
    ((semanticSourceExtensionWorld_holds_fresh
      (theoremQuoteCertifiedProductWorld T) hfresh).mpr
        (theoremQuoteCertifiedProductWorld_consistent_theorem T k φ hφ))

/-- Joint non-vacuity of theorem, quotation, certified source interpretation, and
registry-guarded exact products, all fixed before the eventual source and market. -/
theorem theoremQuoteSemanticRegistryProductDP_hworld
    (T : ArithmeticTheory) [T.Δ₁] [ISigma 1 ⪯ T]
    [T.SoundOnHierarchy SigmaSymbol.sigma 1] :
    (theoremQuoteRegistryWorld T).ConsistentWithTheory
      (theoremQuoteSemanticRegistryProductDP T) := by
  intro k φ hφ
  rw [theoremQuoteSemanticRegistryProductDP, semanticRegistryClosureDP,
    DeductiveProcess.union_stage, Finset.mem_union,
    DeductiveProcess.union_stage, Finset.mem_union] at hφ
  rcases hφ with (hbase | hsource) | hproduct
  · rw [theoremQuoteBaseDP, DeductiveProcess.union_stage, Finset.mem_union] at hbase
    rcases hbase with htheorem | hquote
    · exact theoremQuoteRegistryWorld_consistent_theorem T k φ htheorem
    · exact theoremQuoteRegistryWorld_consistent_quote T k φ hquote
  · obtain ⟨e, rfl⟩ := semanticSourceStageList_exists (List.mem_toFinset.mp hsource)
    exact semanticRegistryProductExtensionWorld_holds_sourceDef
      (theoremQuoteBaseDPComputation T) (theoremQuoteCertifiedProductWorld T) e
  · exact semanticRegistryProductDP_hworld (theoremQuoteBaseDPComputation T)
      (theoremQuoteCertifiedProductWorld T)
      (theoremQuoteCertifiedProductWorld_consistent_base T) k φ hproduct

/-! ## Exact CCEE over certified factors -/

private lemma theoremQuoteRegistry_consistent_base
    {T : ArithmeticTheory} [T.Δ₁] [ISigma 1 ⪯ T]
    [T.SoundOnHierarchy SigmaSymbol.sigma 1] {v : PCWorld}
    (hv : v.ConsistentWithTheory (theoremQuoteSemanticRegistryProductDP T)) :
    v.ConsistentWithTheory (theoremQuoteBaseDP T) :=
  PCWorld.consistentWithTheory_union_left
    (PCWorld.consistentWithTheory_union_left hv)

private lemma theoremQuoteRegistry_consistent_source
    {T : ArithmeticTheory} [T.Δ₁] [ISigma 1 ⪯ T]
    [T.SoundOnHierarchy SigmaSymbol.sigma 1] {v : PCWorld}
    (hv : v.ConsistentWithTheory (theoremQuoteSemanticRegistryProductDP T)) :
    v.ConsistentWithTheory semanticSourceDP :=
  PCWorld.consistentWithTheory_union_right
    (PCWorld.consistentWithTheory_union_left hv)

private lemma theoremQuoteRegistry_consistent_product
    {T : ArithmeticTheory} [T.Δ₁] [ISigma 1 ⪯ T]
    [T.SoundOnHierarchy SigmaSymbol.sigma 1] {v : PCWorld}
    (hv : v.ConsistentWithTheory (theoremQuoteSemanticRegistryProductDP T)) :
    v.ConsistentWithTheory
      (semanticRegistryProductDP (theoremQuoteBaseDPComputation T)) :=
  PCWorld.consistentWithTheory_union_right hv

/-- Exact CCEE after all three LUV families have entered through the executable certified
source registry.  Source valuedness and exact left multiplication are internal. -/
theorem lic_no_expected_net_update_conditional_registryCertified
    {T : ArithmeticTheory} [T.Δ₁] [ISigma 1 ⪯ T]
    [T.SoundOnHierarchy SigmaSymbol.sigma 1]
    {P : History} [IsLogicalInductor P (theoremQuoteSemanticRegistryProductDP T)]
    (f : DeferralFunction)
    (X W Z' : CertifiedSourceLUVSeq (theoremQuoteBaseDP T)) (w : ℕ → ℚ)
    (weight_mem : ∀ n, 0 ≤ w n ∧ w n ≤ 1)
    (weight_generable : PGenerableRat P w)
    (weight_value : ∀ n (v : PCWorld),
      v.ConsistentWithTheory (theoremQuoteBaseDP T) →
      v.ValuesAt (W.toLUV n) (w (f n)))
    (right_value : ∀ n (v : PCWorld),
      v.ConsistentWithTheory (theoremQuoteBaseDP T) →
      v.ValuesAt (Z'.toLUV n)
        ((X.toPresented.toLUV n).expect P (f n) * w (f n))) :
    (fun n => (semanticProductLUV X.toPresented W.toPresented n).expect P n) ≈ₙ
      fun n => (Z'.toPresented.toLUV n).expect P n := by
  refine lic_no_expected_net_update_conditional_ofRepresentation
    (DP := theoremQuoteSemanticRegistryProductDP T) f X.toPresented.toLUV
    (semanticProductLUV X.toPresented W.toPresented) Z'.toPresented.toLUV w
    weight_mem weight_generable X.toPresented.threshold_codes
    (semanticProductLUV_rpnThresholdCodeSeq X.toPresented W.toPresented)
    Z'.toPresented.threshold_codes (fun _ => 0) tendsto_const_nhds
    (fun n v hv => ?_) (fun n v hv x hx => ?_) (fun n v hv => ?_)
    (fun n => ⟨theoremQuoteRegistryWorld T,
      theoremQuoteSemanticRegistryProductDP_hworld T n⟩)
  · obtain ⟨x, hx⟩ := X.source_valued n v (theoremQuoteRegistry_consistent_base hv)
    exact ⟨x, (certifiedSource_valuesAt_iff X n x v
      (theoremQuoteRegistry_consistent_source hv)).2 hx⟩
  · refine ⟨x * (w (f n) : ℝ), ?_, by simp⟩
    apply semanticRegistryProductLUV_valuesAt (theoremQuoteBaseDPComputation T)
      (theoremQuoteRegistry_consistent_product hv) X W n hx
    exact (certifiedSource_valuesAt_iff W n (w (f n)) v
      (theoremQuoteRegistry_consistent_source hv)).2
        (weight_value n v (theoremQuoteRegistry_consistent_base hv))
  · exact (certifiedSource_valuesAt_iff Z' n _ v
      (theoremQuoteRegistry_consistent_source hv)).2
        (right_value n v (theoremQuoteRegistry_consistent_base hv))

private noncomputable abbrev theoremQuoteSemanticRegistryProductLIA
    (T : ArithmeticTheory) [T.Δ₁] [ISigma 1 ⪯ T]
    [T.SoundOnHierarchy SigmaSymbol.sigma 1] :
    IsLogicalInductor (liaHistory (theoremQuoteSemanticRegistryProductDP T))
      (theoremQuoteSemanticRegistryProductDP T) :=
  LIA_is_logical_inductor _
    (theoremQuoteSemanticRegistryProductDPComputation T).toComputable

theorem lic_no_expected_net_update_conditional_registryCertified_closed
    (T : ArithmeticTheory) [T.Δ₁] [ISigma 1 ⪯ T]
    [T.SoundOnHierarchy SigmaSymbol.sigma 1]
    (f : DeferralFunction)
    (X W Z' : CertifiedSourceLUVSeq (theoremQuoteBaseDP T)) (w : ℕ → ℚ)
    (weight_mem : ∀ n, 0 ≤ w n ∧ w n ≤ 1)
    (weight_generable : PGenerableRat
      (liaHistory (theoremQuoteSemanticRegistryProductDP T)) w)
    (weight_value : ∀ n (v : PCWorld),
      v.ConsistentWithTheory (theoremQuoteBaseDP T) →
      v.ValuesAt (W.toLUV n) (w (f n)))
    (right_value : ∀ n (v : PCWorld),
      v.ConsistentWithTheory (theoremQuoteBaseDP T) →
      v.ValuesAt (Z'.toLUV n)
        ((X.toPresented.toLUV n).expect
          (liaHistory (theoremQuoteSemanticRegistryProductDP T)) (f n) * w (f n))) :
    (fun n => (semanticProductLUV X.toPresented W.toPresented n).expect
      (liaHistory (theoremQuoteSemanticRegistryProductDP T)) n) ≈ₙ
      fun n => (Z'.toPresented.toLUV n).expect
        (liaHistory (theoremQuoteSemanticRegistryProductDP T)) n := by
  haveI := theoremQuoteSemanticRegistryProductLIA T
  exact lic_no_expected_net_update_conditional_registryCertified
    f X W Z' w weight_mem weight_generable weight_value right_value

#print axioms semanticRegistryProductDP_computable
#print axioms semanticRegistryProductLUV_valuesAt
#print axioms semanticRegistryProductDP_hworld
#print axioms theoremSemanticRegistryProductDP_hworld
#print axioms theoremQuoteSemanticRegistryProductDP_hworld
#print axioms lic_no_expected_net_update_conditional_registryCertified_closed

end LogicalInduction
