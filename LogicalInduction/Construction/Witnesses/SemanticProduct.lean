import LogicalInduction.Construction.Witnesses.SemanticPrime
import LogicalInduction.Construction.Witnesses.ProductDefinition

/-!
# Fixed semantic-prime product closure

`thm:ccee`'s exact product mathematics in source-independent form: the semantic-prime
counterpart of `ProductDefinition.lean`'s fresh-atom construction, and the shared closure the
`SemanticCertifiedProduct`, `SemanticRegistryProduct` and `SemanticJoint` lanes are built on.

The key move is that a product handle carries the schemas of *both* factors in its own name
(`semanticProductSchema left right = Nat.pair 1 (Nat.pair left right)`, tag `1` of the
semantic schema language), so one deductive process can enumerate the defining clauses for
*every* product before a market, source LUV, weight or deferral is chosen.

## Objects

`semanticProductSchema`, `semanticProductAtom`, `semanticProductLUV`,
`semanticProductSchemaInstance` (the three clause kinds — positive at `r ≤ s·t`, negative at
`s·t ≤ r`, and the `r < 0` axiom), `semanticProductJob`, `semanticProductDefSentence`,
`semanticProductStageList`, `semanticProductDP`, `semanticProductWorld`.

The clause family is `ProductDefinition.productSchemaInstance` with the three threshold
lookups replaced by their self-describing semantic-prime counterparts; the factors are
mesh-indexed `⟨k,i⟩` for the same reason (`meshIndexRat`), so the emitter is derivable rather
than assumed.

## Main results

`semanticProductDefSentence_computable` / `semanticProductDP_computable` (`def:dedproc` for
the closure); `semanticProductWorld_holds_schema` and `semanticProductWorld_productAtom` (the
canonical satisfying world, which `SemanticCertifiedProduct` reuses); and
`semanticProductLUV_rpnThresholdCodeSeq` (`def:ec` for the product family, consumed by
`SemanticCertifiedProduct` and `SemanticRegistryProduct`).

The reflection lemmas the downstream lanes consume are `semanticProductDefSentence_job`,
`holds_semanticProduct_pos`, `not_holds_semanticProduct_neg` and `holds_semanticProduct_below`,
read off at their job codes: a completed world pins `semanticProductAtom left right n r` to
exactly `x·c > r` by density of ℚ in the two factors, with no slack and no positivity
hypothesis on the right factor.

## Disjointness

`PresentedLUVSeq.schema_ne_product` — a leaf presentation lives on tag `0` and so cannot
collide with the tag-`1` product constructor.  `eventAtom_atomCodes_ne_semanticPrimeTag` — the
ordinary theorem stream never uses the semantic-prime atom tag, which is what lets the two
processes be unioned; `SemanticSourceDP` and `SemanticCertifiedProduct` consume it.

Design choices: `dd:mesh` is *not* paid here — this is the exact product, and the mesh index
is only how nonnegative rational factors are named; `dd:quote-code` for the handle.
-/

namespace LogicalInduction

open LO LO.Propositional LO.FirstOrder LO.FirstOrder.Arithmetic

-- Keep the pairing decoder opaque while elaborating fixed job syntax.
attribute [local irreducible] Nat.sqrt

/-! ## The product handle -/

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

/-! ## Disjointness from the theorem stream -/

/-- A leaf presentation cannot collide with the product constructor. -/
lemma PresentedLUVSeq.schema_ne_product (X : PresentedLUVSeq) (right : ℕ) :
    X.thresholdSchema ≠ semanticProductSchema X.thresholdSchema right := by
  intro h
  have hx := X.source_schema
  rw [h] at hx
  simp [semanticProductSchema] at hx

/-- The ordinary theorem stream never uses the semantic-prime atom tag, which is what lets it
be unioned with the semantic closure. -/
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

/-! ## The defining clause family -/

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

/-- Inversion of the stage list: every sentence in a stage is one decoded job.  This is what
an `hworld` obligation over `semanticProductDP` is discharged through, together with
`semanticProductWorld_holds_schema`. -/
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

/-! ## Computability of the closure -/

set_option maxHeartbeats 4000000 in
/-- Decoding a job code into its clause is computable: every projection is `Primrec` and the
three clause shapes are assembled from fixed atom pairings. -/
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
  have hq : Primrec fun e : ℕ =>
      decodedQuotationRat e.unpair.2.unpair.2.unpair.2.unpair.2.unpair.1 :=
    decodedQuotationRat_prim.comp hcr
  have hs : Primrec fun e : ℕ =>
      meshIndexRat e.unpair.2.unpair.2.unpair.2.unpair.2.unpair.2.unpair.1 :=
    meshIndexRat_prim.comp hzs
  have ht : Primrec fun e : ℕ =>
      meshIndexRat e.unpair.2.unpair.2.unpair.2.unpair.2.unpair.2.unpair.2 :=
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
        (Encodable.encode
          (meshIndexRat e.unpair.2.unpair.2.unpair.2.unpair.2.unpair.2.unpair.1)))) :=
    hatom.comp (hl.pair (Primrec₂.natPair.comp hn (Primrec.encode.comp hs)))
  have hright : Primrec fun e : ℕ => Encodable.encode
      (semanticPrimeSentence e.unpair.2.unpair.1 (Nat.pair e.unpair.2.unpair.2.unpair.1
        (Encodable.encode
          (meshIndexRat e.unpair.2.unpair.2.unpair.2.unpair.2.unpair.2.unpair.2)))) :=
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
/-- `def:dedproc` for the fixed closure: the whole semantic product process is computable.
`semanticProductDP` is public and `SemanticJoint.lean` unions it, so this is the certificate a
client supplies to compile it. -/
lemma semanticProductDP_computable : ComputableDeductiveProcess semanticProductDP := by
  have hlist : Computable semanticProductStageList := by
    have hstep : Computable fun p : ℕ × List Sentence =>
        semanticProductDefSentence (p.1 + 1) :: p.2 :=
      Computable.list_cons.comp
        (semanticProductDefSentence_computable.comp
          (Primrec.succ.to_comp.comp Computable.fst))
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

/-! ## The canonical satisfying world -/

open Classical in
/-- The canonical world of the fixed closure: it affirms a semantic-prime handle exactly when
the handle is a product atom whose threshold is negative, and nothing else.  This is the least
assignment satisfying every clause of `semanticProductSchemaInstance` at once
(`semanticProductWorld_holds_schema`), and it is what `SemanticCertifiedProduct`'s own
`hworld` is built from. -/
noncomputable def semanticProductWorld : PCWorld := fun a =>
  if a.unpair.1 = semanticPrimeTag ∧ a.unpair.2.unpair.1.unpair.1 = 1 then
    decodedQuotationRat a.unpair.2.unpair.2.unpair.2 < 0
  else False

/-- The canonical world affirms no handle at a nonnegative threshold. -/
lemma semanticProductWorld_nonneg (schema n : ℕ) (q : ℚ) (hq : 0 ≤ q) :
    ¬ semanticProductWorld.Holds
      (semanticPrimeSentence schema (Nat.pair n (Encodable.encode q))) := by
  change ¬ semanticProductWorld
    (semanticPrimeCode schema (Nat.pair n (Encodable.encode q)))
  simp only [semanticProductWorld, semanticPrimeCode, Nat.unpair_pair,
    decodedQuotationRat_encode]
  split <;> simp_all

/-- On product atoms it is exactly the `r < 0` axiom. -/
lemma semanticProductWorld_productAtom (left right n : ℕ) (r : ℚ) :
    semanticProductWorld.Holds (semanticProductAtom left right n r) ↔ r < 0 := by
  change semanticProductWorld
    (semanticPrimeCode (semanticProductSchema left right) (Nat.pair n (Encodable.encode r))) ↔ _
  simp [semanticProductWorld, semanticPrimeCode, semanticProductSchema,
    decodedQuotationRat_encode]

/-- **The canonical world satisfies every clause**, whatever the kind, threshold and mesh
indices — so the closure is non-vacuous by construction. -/
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

/-! ## Reading the clauses off their job codes -/

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
    (hX : v.Holds
      (semanticPrimeSentence left (Nat.pair n (Encodable.encode (meshIndexRat zs)))))
    (hW : v.Holds
      (semanticPrimeSentence right (Nat.pair n (Encodable.encode (meshIndexRat zt))))) :
    v.Holds (semanticProductAtom left right n r) := by
  have h := holds_semanticProductDefSentence hv (semanticProductJob left right n 0 r zs zt)
  rw [semanticProductDefSentence_job, semanticProductSchemaInstance,
    if_pos rfl, if_pos hst] at h
  exact h ⟨hX, hW⟩

lemma not_holds_semanticProduct_neg {v : PCWorld}
    (hv : v.ConsistentWithTheory semanticProductDP) (left right n : ℕ) {r : ℚ} {zs zt : ℕ}
    (hst : meshIndexRat zs * meshIndexRat zt ≤ r)
    (hX : ¬ v.Holds
      (semanticPrimeSentence left (Nat.pair n (Encodable.encode (meshIndexRat zs)))))
    (hW : ¬ v.Holds
      (semanticPrimeSentence right (Nat.pair n (Encodable.encode (meshIndexRat zt))))) :
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

/-! ## `def:ec` for semantic products -/

/-- The product handle's name at the packed mesh index `⟨n,⟨k,i⟩⟩` is emitted under a
polynomial fuel bound, by reducing `i/k` at runtime under a fixed atom shell. -/
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
      ((PolyFueled.const (semanticProductSchema left right)).pair
        (hn.pair meshPF)))).succ_comp
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

/-- The whole-value threshold certificate for a semantic product family. -/
lemma semanticProductLUV_polyThresholdCodeSeq (X W : PresentedLUVSeq) :
    LUV.PolyThresholdCodeSeq (semanticProductLUV X W) := by
  obtain ⟨c, hc⟩ :=
    semanticProductAtom_mesh_encode_polyFueled X.thresholdSchema W.thresholdSchema
  exact ⟨c, hc.of_eq (fun m => by rw [semanticProductLUV_gt])⟩

/-- **`def:ec` for semantic products.**  The token-metered threshold interface the downstream
product lanes consume. -/
lemma semanticProductLUV_rpnThresholdCodeSeq (X W : PresentedLUVSeq) :
    LUV.RpnThresholdCodeSeq (semanticProductLUV X W) :=
  LUV.RpnThresholdCodeSeq.ofPolyThresholdCodeSeq
    (semanticProductLUV_polyThresholdCodeSeq X W)

end LogicalInduction
