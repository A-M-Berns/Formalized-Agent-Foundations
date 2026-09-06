import LogicalInduction.Construction.SemanticExtension.Prime
import LogicalInduction.Construction.Quotation.ProductDefinition
import LogicalInduction.Construction.SemanticExtension.Quote

/-!
# The fixed semantic-prime product closure, and factor ownership

`thm:ccee`'s exact product mathematics in source-independent form: the semantic-prime
counterpart of `Construction/Quotation/ProductDefinition.lean`'s fresh-atom construction,
together with the two obstructions that force factor-schema ownership and the gates that
answer them.  Nothing here is a paper node.

The key move is that a product handle carries the schemas of *both* factors in its own name
(`semanticProductSchema left right = Nat.pair 1 (Nat.pair left right)`, tag `1` of the
semantic schema language), so one deductive process can enumerate the defining clauses for
*every* product before a market, source LUV, weight or deferral is chosen.

## The unrestricted closure

`semanticProductSchema`, `semanticProductAtom`, `semanticProductLUV`,
`semanticProductSchemaInstance` (the three clause kinds — positive at `r ≤ s·t`, negative at
`s·t ≤ r`, and the `r < 0` axiom), `semanticProductJob`, `semanticProductDefSentence`,
`semanticProductStageList`, `semanticProductDP`, `semanticProductWorld`.  The reflection
lemmas the downstream lanes consume are `semanticProductDefSentence_job`,
`holds_semanticProduct_pos`, `not_holds_semanticProduct_neg` and
`holds_semanticProduct_below`: a completed world pins `semanticProductAtom left right n r` to
exactly `x·c > r` by density of ℚ in the two factors, with no slack and no positivity
hypothesis on the right factor.  `dd:mesh` is *not* paid here — this is the exact product, and
the mesh index is only how nonnegative rational factors are named; `dd:quote-code` names the
handle.

## Why that closure cannot stand alone

Syntactic separation blocks the self-referential source diagonal of
`Construction/SemanticExtension/Prime.lean`, but it does not by itself make a universal
product closure jointly satisfiable with an interpreter for every fresh emitter: product
clauses require their factor leaves to behave as coherent rational cuts, and neither
freshness nor efficient emission secures that.  Two finite, kernel-checked counterexamples say so.

* `semanticProductDP_no_increasing_factor_assignment` — the universal product clauses cannot
  be satisfied by a factor family that is false at `0` and true at `1`, a pattern no genuine
  `[0,1]` rational cut has.  `semanticFreshIncreasingLUVSeq` is the witness family:
  syntactically fresh and efficiently emitted, yet malformed in exactly that way, giving
  `semanticFreshIncreasing_not_jointly_reflected`.
* `theorem_quote_product_not_jointly_satisfiable` — `theoremDP`, `semanticQuoteDP` and a
  schema-unrestricted `semanticProductDP` have no joint completed world, because the quote
  interpreter interprets every partial-recursive Boolean selector while the product closure
  treats every schema as a factor.

## The certified-factor closure

Product-clause activation is therefore made to depend on factor-schema ownership, with the
exact product mathematics unchanged.  `certifiedProductJobOwned` is decidable and asks that
both factor schemas sit in tag `0`, the namespace reserved for proof-carrying source/cut
presentations, so quote aliases on tag `2` cannot become product factors.
`semanticCertifiedProductDefSentence` guards the exact clause by that test (returning the
inert top otherwise); `semanticCertifiedProductDP` builds the process and
`theoremQuoteCertifiedProductWorld` is the joint world it and the quote interpreter share.

## Admitting a quotation factor

Tag `2` is admitted separately, and executably.  A certified paper source carries its own
cut-proof program, whereas a deferred weight already has the repository's
`RationalQuoteCode`, and the quote process identifies its leaves with old quotation atoms; the
only coherence the exact product needs from such a factor is downward closure on each finite
rational-query prefix, bounds coming separately from `RationalQuoteCode.value_mem`.  The gate
is `semanticQuoteFactorPrefixValidAtFuel`, built from `semanticSentenceSeenAtFuel`,
`semanticQuoteFactorClaim`/`…Link`, `…EvidenceAtFuel`, `…DownwardAtFuel` and the three nested
prefix quantifiers; it is decidable (`…PrefixValidAtFuel_computable`), clock-monotone
(`…_mono`), sound (`…_downward`) and eventually complete for a total `[0,1]`
`RationalQuoteCode` (`rationalQuote_semanticQuoteFactorPrefix_eventually{,_of_subprocess}`).
For `r < s`, downward closure follows from either the positive claim at `r` or the negative
claim at `s`; a malformed selector is never trusted for wearing tag `2`.  The
`_of_subprocess` form is the general one — it asks only that the base process contain the
canonical theorem/quotation stages — and the fixed-base form is its instance.

The tag-`0` counterpart of these gates is `Construction/SemanticExtension/Source.lean`; the
process that runs both of them on each product job is
`Construction/SemanticExtension/Registry.lean`.
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
`semanticProductDP` is public and the certified closure below unions it, so this is the
certificate a client supplies to compile it. -/
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
(`semanticProductWorld_holds_schema`), and it is what the certified closure
`semanticCertifiedProductDP`'s own `hworld` is built from. -/
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
polynomial fuel bound: the shared `gcd`-reduced quotient emitter `encode_natDiv_polyFueled`
for `i/k`, under a fixed atom shell. -/
lemma semanticProductAtom_mesh_encode_polyFueled (left right : ℕ) :
    ∃ c, PolyFueled c (fun m => Encodable.encode (semanticProductAtom left right m.unpair.1
      ((m.unpair.2.unpair.2 : ℚ) / (m.unpair.2.unpair.1 : ℚ)))) := by
  have hn := PolyFueled.left
  have hk := PolyFueled.left.comp PolyFueled.right
  have hi := PolyFueled.right.comp PolyFueled.right
  obtain ⟨cmesh, meshPF⟩ := encode_natDiv_polyFueled hi hk
  have fullPF := ((PolyFueled.const 1).pair
    ((PolyFueled.const semanticPrimeTag).pair
      ((PolyFueled.const (semanticProductSchema left right)).pair
        (hn.pair meshPF)))).succ_comp
  refine ⟨_, fullPF.of_eq (fun m => ?_)⟩
  conv_rhs =>
    rw [semanticProductAtom, semanticPrimeSentence, semanticPrimeCode, encode_atom]

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
(`semanticCertifiedProductDP`, below).
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

namespace LogicalInduction

open LO LO.Propositional LO.FirstOrder LO.FirstOrder.Arithmetic

attribute [local irreducible] Nat.sqrt

/-! ## Factor-schema ownership -/

/-- Whether a product job's two factor schemas belong to the certified source namespace. -/
def certifiedProductJobOwned (e : ℕ) : Prop :=
  e.unpair.1.unpair.1 = 0 ∧ e.unpair.2.unpair.1.unpair.1 = 0

instance (e : ℕ) : Decidable (certifiedProductJobOwned e) := by
  unfold certifiedProductJobOwned
  exact instDecidableAnd

/-! ## The guarded product process -/

/-- Guard the existing exact clause by certified factor ownership. -/
def semanticCertifiedProductDefSentence (e : ℕ) : Sentence :=
  if certifiedProductJobOwned e then semanticProductDefSentence e else ⊤

/-- The guarded clause list published by stage `k`: one clause per product job `e ≤ k`. -/
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

/-! ## Exact multiplication for certified factors -/

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
    (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] :
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

/-- The joint fixed process, chosen from `T` before any source, market, weight, or
deferral. -/
noncomputable def theoremQuoteCertifiedProductDP
    (T : ArithmeticTheory) [T.Δ₁] [Entailment.Consistent T] :
    DeductiveProcess :=
  ((theoremDP T).union semanticQuoteDP).union semanticCertifiedProductDP

/-- The named stage program of `theoremQuoteCertifiedProductDP`, the union of the three
component programs. -/
noncomputable def theoremQuoteCertifiedProductDPComputation
    (T : ArithmeticTheory) [T.Δ₁] [Entailment.Consistent T] :
    DeductiveProcessComputation (theoremQuoteCertifiedProductDP T) :=
  (((theoremDP_computable T).nonemptyComputation.some).union
    semanticQuoteDP_computable.nonemptyComputation.some).union
      semanticCertifiedProductDP_computable.nonemptyComputation.some

/-- Joint non-vacuity of the fixed theorem, quotation, and certified-product substrate. -/
lemma theoremQuoteCertifiedProductDP_hworld
    (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] :
    (theoremQuoteCertifiedProductWorld T).ConsistentWithTheory
      (theoremQuoteCertifiedProductDP T) := by
  intro n φ hφ
  rw [theoremQuoteCertifiedProductDP, DeductiveProcess.union_stage,
    Finset.mem_union, DeductiveProcess.union_stage, Finset.mem_union] at hφ
  rcases hφ with (htheorem | hquote) | hproduct
  · exact theoremQuoteCertifiedProductWorld_consistent_theorem T n φ htheorem
  · exact theoremQuoteCertifiedProductWorld_consistent_quote T n φ hquote
  · exact theoremQuoteCertifiedProductWorld_consistent_product T n φ hproduct

/-! ## Exact conditional expectation over the joint process -/

/-- Exact multiplication enters the generic CCEE theorem over the jointly non-vacuous
theorem/quote/certified-product process.  The remaining presentation premises are kept
explicit here; the proof-carrying source interpreter is responsible for discharging them. -/
lemma lic_no_expected_net_update_conditional_certifiedSemantic
    {T : ArithmeticTheory} [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]
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
    (T : ArithmeticTheory) [T.Δ₁] [Entailment.Consistent T] :
    IsLogicalInductor (liaHistory (theoremQuoteCertifiedProductDP T))
      (theoremQuoteCertifiedProductDP T) :=
  LIA_is_logical_inductor _ (theoremQuoteCertifiedProductDPComputation T).toComputable

/-- The generalized semantic-extension form of `thm:ccee`, over the joint
theorem/quote/certified-product process, in constructed-inductor form.  The paper rendering
is `lic_no_expected_net_update_conditional_paperLUV_closed` over the shared market; this
endpoint keeps its presentation premises explicit because it quantifies over an arbitrary
`PresentedLUVSeq` pair. -/
lemma lic_no_expected_net_update_conditional_certifiedSemantic_closed
    (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]
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

end LogicalInduction

namespace LogicalInduction

open LO LO.Propositional LO.FirstOrder LO.FirstOrder.Arithmetic

attribute [local irreducible] Nat.sqrt

/-! ## Bounded literal search in a computable process -/

/-- Bounded search for a literal sentence in a fixed computable process. -/
def semanticSentenceSeenAtFuel {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) (φ : Sentence) (fuel : ℕ) : Bool :=
  (List.range (fuel + 1)).any fun k =>
    match base.stageAtFuel fuel k with
    | some stage => decide (φ ∈ stage)
    | none => false

private lemma listRangeAny_prim' {α : Type} [Primcodable α]
    {bound : α → ℕ} {test : α → ℕ → Bool}
    (hbound : Primrec bound) (htest : Primrec₂ test) :
    Primrec fun a => (List.range (bound a + 1)).any (test a) := by
  have hrange : Primrec fun a => List.range (bound a + 1) :=
    Primrec.list_range.comp (Primrec.nat_add.comp hbound (Primrec.const 1))
  have hstep : Primrec₂ fun (a : α) (q : ℕ × Bool) => test a q.1 || q.2 :=
    (Primrec.dom_bool₂ (· || ·)).comp₂
      (htest.comp₂ Primrec₂.left (Primrec.fst.comp₂ Primrec₂.right))
      (Primrec.snd.comp₂ Primrec₂.right)
  exact (Primrec.list_foldr hrange (Primrec.const false) hstep).of_eq fun a => by
    induction List.range (bound a + 1) with
    | nil => rfl
    | cons x xs ih => simp [List.any, ih]

lemma semanticSentenceSeenAtFuel_prim {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) :
    Primrec fun p : Sentence × ℕ => semanticSentenceSeenAtFuel base p.1 p.2 := by
  let P := Sentence × ℕ
  have hbound : Primrec fun p : P => p.2 := Primrec.snd
  have htest : Primrec₂ fun (p : P) (k : ℕ) =>
      match base.stageAtFuel p.2 k with
      | some stage => decide (p.1 ∈ stage)
      | none => false := by
    let Q := P × ℕ
    have hstage : Primrec fun q : Q => base.stageAtFuel q.1.2 q.2 :=
      (processStageAtFuel_prim base).comp
        (Primrec.snd.comp Primrec.fst) Primrec.snd
    have hmem : Primrec₂ fun (q : Q) (stage : Finset Sentence) =>
        decide (q.1.1 ∈ stage) :=
      (sentenceMemSupport_prim.comp₂ Primrec₂.right
        (Primrec.fst.comp₂ (Primrec.fst.comp₂ Primrec₂.left))).decide
    exact (Primrec.option_casesOn hstage (Primrec.const false) hmem).to₂.of_eq fun p k => by
      cases base.stageAtFuel p.2 k <;> simp
  exact listRangeAny_prim' hbound htest

lemma semanticSentenceSeenAtFuel_iff {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) (φ : Sentence) (fuel : ℕ) :
    semanticSentenceSeenAtFuel base φ fuel = true ↔
      ∃ k ≤ fuel, ∃ stage,
        base.stageAtFuel fuel k = some stage ∧ φ ∈ stage := by
  rw [semanticSentenceSeenAtFuel, List.any_eq_true]
  simp only [List.mem_range, Nat.lt_add_one_iff]
  constructor
  · rintro ⟨k, hk, h⟩
    cases hs : base.stageAtFuel fuel k with
    | none => simp [hs] at h
    | some stage => exact ⟨k, hk, stage, hs, by simpa [hs] using h⟩
  · rintro ⟨k, hk, stage, hs, hmem⟩
    exact ⟨k, hk, by simp [hs, hmem]⟩

lemma semanticSentenceSeenAtFuel_mono {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) {φ : Sentence} {fuel fuel' : ℕ}
    (hff : fuel ≤ fuel')
    (h : semanticSentenceSeenAtFuel base φ fuel = true) :
    semanticSentenceSeenAtFuel base φ fuel' = true := by
  obtain ⟨k, hk, stage, hs, hmem⟩ :=
    (semanticSentenceSeenAtFuel_iff base φ fuel).1 h
  exact (semanticSentenceSeenAtFuel_iff base φ fuel').2
    ⟨k, hk.trans hff, stage, base.stageAtFuel_mono hff hs, hmem⟩

lemma semanticSentenceSeenAtFuel_sound {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) {φ : Sentence} {fuel : ℕ}
    (h : semanticSentenceSeenAtFuel base φ fuel = true) :
    ∃ k, φ ∈ DP.D k := by
  obtain ⟨k, _, stage, hs, hmem⟩ :=
    (semanticSentenceSeenAtFuel_iff base φ fuel).1 h
  exact ⟨k, base.stageAtFuel_sound hs ▸ hmem⟩

lemma semanticSentenceSeenAtFuel_eventually {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) {φ : Sentence} {k : ℕ}
    (hmem : φ ∈ DP.D k) : ∃ fuel, semanticSentenceSeenAtFuel base φ fuel = true := by
  obtain ⟨f, hf⟩ := base.stageAtFuel_complete k
  let fuel := max f k
  refine ⟨fuel, (semanticSentenceSeenAtFuel_iff base φ fuel).2 ?_⟩
  exact ⟨k, by simp [fuel], DP.D k,
    base.stageAtFuel_mono (by simp [fuel]) hf, hmem⟩

/-! ## The quotation claim and its definitional link -/

/-- The old quotation claim corresponding to a tag-`2` leaf threshold. -/
noncomputable def semanticQuoteFactorClaim (schema n z : ℕ) (positive : Bool) : Sentence :=
  let atom := quoteAtom (Nat.pair schema.unpair.2
    (Nat.pair n (Encodable.encode (decodedQuotationRat z))))
  bif positive then atom else ∼atom

/-- The fixed quote-leaf direction needed to turn an exposed old quotation literal into
the corresponding semantic fact (positive), or conversely (negative). -/
noncomputable def semanticQuoteFactorLink (schema n z : ℕ) (positive : Bool) : Sentence :=
  let input := Nat.pair n (Encodable.encode (decodedQuotationRat z))
  semanticQuoteDefSentence
    (Nat.pair (bif positive then 0 else 1) (Nat.pair schema.unpair.2 input))

/-! ## The bounded evidence and the finite prefix -/

/-- Both the quotation claim and its definitional link have appeared by this clock. -/
noncomputable def semanticQuoteFactorEvidenceAtFuel {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP)
    (schema fuel n z : ℕ) (positive : Bool) : Bool :=
  semanticSentenceSeenAtFuel base (semanticQuoteFactorClaim schema n z positive) fuel &&
    semanticSentenceSeenAtFuel base (semanticQuoteFactorLink schema n z positive) fuel

attribute [local irreducible] semanticQuoteFactorClaim semanticQuoteFactorLink
  semanticQuoteFactorEvidenceAtFuel

/-- For `r < s`, downward closure is witnessed by the positive claim at `r` or the negative
claim at `s`; trivially true otherwise. -/
noncomputable def semanticQuoteFactorDownwardAtFuel {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP)
    (schema fuel n zr zs : ℕ) : Bool :=
  if decodedQuotationRat zr < decodedQuotationRat zs then
    semanticQuoteFactorEvidenceAtFuel base schema fuel n zr true ||
      semanticQuoteFactorEvidenceAtFuel base schema fuel n zs false
  else true

/-- Inclusive bounded conjunction over the right-threshold coordinate. -/
noncomputable def semanticQuoteFactorZsValid {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) (schema fuel n zr limit : ℕ) : Bool :=
  (List.range (limit + 1)).all fun zs =>
    semanticQuoteFactorDownwardAtFuel base schema fuel n zr zs

/-- Inclusive bounded conjunction over the left-threshold coordinate. -/
noncomputable def semanticQuoteFactorZrValid {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP)
    (schema limit fuel n : ℕ) : Bool :=
  (List.range (limit + 1)).all fun zr =>
    semanticQuoteFactorZsValid base schema fuel n zr limit

/-- Inclusive bounded conjunction over the source index. -/
noncomputable def semanticQuoteFactorNValid {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP)
    (schema limit fuel : ℕ) : Bool :=
  (List.range (limit + 1)).all fun n =>
    semanticQuoteFactorZrValid base schema limit fuel n

/-- Every pairwise downward query through `limit` is justified by an exposed quotation
claim.  Bounds are supplied separately by `RationalQuoteCode.value_mem`; exact product
closure only needs this downward compatibility. -/
noncomputable def semanticQuoteFactorPrefixValidAtFuel {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP)
    (schema limit fuel : ℕ) : Bool :=
  (schema.unpair.1 == 2) &&
    semanticQuoteFactorNValid base schema limit fuel

/-! ## Decidability of the gate -/

private lemma sentenceNeg_computable : Computable fun φ : Sentence => ∼φ := by
  have h : Primrec fun φ : Sentence => ∼φ := by
    apply Primrec.encode_iff.mp
    exact (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 2)
      (Primrec₂.natPair.comp Primrec.encode (Primrec.const 1)))).of_eq fun _ => rfl
  exact h.to_comp

lemma semanticQuoteFactorClaim_computable :
    Computable fun p : ((ℕ × ℕ) × ℕ) × Bool =>
      semanticQuoteFactorClaim p.1.1.1 p.1.1.2 p.1.2 p.2 := by
  let P := ((ℕ × ℕ) × ℕ) × Bool
  have hschema : Computable fun p : P => p.1.1.1 :=
    (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).to_comp
  have hn : Computable fun p : P => p.1.1.2 :=
    (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)).to_comp
  have hz : Computable fun p : P => p.1.2 :=
    (Primrec.snd.comp Primrec.fst).to_comp
  have hpositive : Computable fun p : P => p.2 := Computable.snd
  have hcode : Computable fun p : P => p.1.1.1.unpair.2 :=
    (Primrec.snd.comp Primrec.unpair).to_comp.comp hschema
  have hrat : Computable fun p : P => decodedQuotationRat p.1.2 :=
    decodedQuotationRat_prim.to_comp.comp hz
  have hinput : Computable fun p : P => Nat.pair p.1.1.2
      (Encodable.encode (decodedQuotationRat p.1.2)) :=
    Primrec₂.natPair.to_comp.comp hn (Computable.encode.comp hrat)
  have hatom : Computable fun p : P => quoteAtom
      (Nat.pair p.1.1.1.unpair.2
        (Nat.pair p.1.1.2 (Encodable.encode (decodedQuotationRat p.1.2)))) :=
    quoteAtom_computable.comp (Primrec₂.natPair.to_comp.comp hcode hinput)
  exact (Computable.cond hpositive hatom (sentenceNeg_computable.comp hatom)).of_eq
    fun p => by cases p.2 <;> rw [semanticQuoteFactorClaim]

lemma semanticQuoteFactorLink_computable :
    Computable fun p : ((ℕ × ℕ) × ℕ) × Bool =>
      semanticQuoteFactorLink p.1.1.1 p.1.1.2 p.1.2 p.2 := by
  let P := ((ℕ × ℕ) × ℕ) × Bool
  have hschema : Computable fun p : P => p.1.1.1 :=
    (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).to_comp
  have hn : Computable fun p : P => p.1.1.2 :=
    (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)).to_comp
  have hz : Computable fun p : P => p.1.2 :=
    (Primrec.snd.comp Primrec.fst).to_comp
  have hcode : Computable fun p : P => p.1.1.1.unpair.2 :=
    (Primrec.snd.comp Primrec.unpair).to_comp.comp hschema
  have hinput : Computable fun p : P => Nat.pair p.1.1.2
      (Encodable.encode (decodedQuotationRat p.1.2)) :=
    Primrec₂.natPair.to_comp.comp hn
      (Computable.encode.comp (decodedQuotationRat_prim.to_comp.comp hz))
  have hkind : Computable fun p : P => bif p.2 then 0 else 1 :=
    (Computable.cond Computable.snd (Computable.const 0) (Computable.const 1)).of_eq
      fun p => by cases p.2 <;> rfl
  have hjob : Computable fun p : P => Nat.pair (bif p.2 then 0 else 1)
      (Nat.pair p.1.1.1.unpair.2
        (Nat.pair p.1.1.2 (Encodable.encode (decodedQuotationRat p.1.2)))) :=
    Primrec₂.natPair.to_comp.comp hkind
      (Primrec₂.natPair.to_comp.comp hcode hinput)
  exact (semanticQuoteDefSentence_computable.comp hjob).of_eq fun p => by
    rw [semanticQuoteFactorLink]

set_option maxHeartbeats 2000000 in
lemma semanticQuoteFactorEvidenceAtFuel_computable {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) :
    Computable fun p : ((((ℕ × ℕ) × ℕ) × ℕ) × Bool) =>
      semanticQuoteFactorEvidenceAtFuel base p.1.1.1.1 p.1.1.1.2
        p.1.1.2 p.1.2 p.2 := by
  let P := ((((ℕ × ℕ) × ℕ) × ℕ) × Bool)
  have hschema : Computable fun p : P => p.1.1.1.1 :=
    (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))).to_comp
  have hfuel : Computable fun p : P => p.1.1.1.2 :=
    (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))).to_comp
  have hn : Computable fun p : P => p.1.1.2 :=
    (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)).to_comp
  have hz : Computable fun p : P => p.1.2 :=
    (Primrec.snd.comp Primrec.fst).to_comp
  have hpositive : Computable fun p : P => p.2 := Computable.snd
  have hclaim : Computable fun p : P =>
      semanticQuoteFactorClaim p.1.1.1.1 p.1.1.2 p.1.2 p.2 :=
    semanticQuoteFactorClaim_computable.comp
      (((hschema.pair hn).pair hz).pair hpositive)
  have hlink : Computable fun p : P =>
      semanticQuoteFactorLink p.1.1.1.1 p.1.1.2 p.1.2 p.2 :=
    semanticQuoteFactorLink_computable.comp
      (((hschema.pair hn).pair hz).pair hpositive)
  have hclaimSeen : Computable fun p : P => semanticSentenceSeenAtFuel base
      (semanticQuoteFactorClaim p.1.1.1.1 p.1.1.2 p.1.2 p.2) p.1.1.1.2 :=
    semanticSentenceSeenAtFuel_prim base |>.to_comp.comp (hclaim.pair hfuel)
  have hlinkSeen : Computable fun p : P => semanticSentenceSeenAtFuel base
      (semanticQuoteFactorLink p.1.1.1.1 p.1.1.2 p.1.2 p.2) p.1.1.1.2 :=
    semanticSentenceSeenAtFuel_prim base |>.to_comp.comp (hlink.pair hfuel)
  exact ((Primrec.dom_bool₂ (· && ·)).to_comp.comp hclaimSeen hlinkSeen).of_eq
    fun p => by rw [semanticQuoteFactorEvidenceAtFuel]

set_option maxHeartbeats 2000000 in
lemma semanticQuoteFactorDownwardAtFuel_computable {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) :
    Computable fun p : ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) =>
      semanticQuoteFactorDownwardAtFuel base
        p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.1.2 p.2 := by
  let P := ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ)
  have hschema : Computable fun p : P => p.1.1.1.1 :=
    (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))).to_comp
  have hfuel : Computable fun p : P => p.1.1.1.2 :=
    (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))).to_comp
  have hn : Computable fun p : P => p.1.1.2 :=
    (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)).to_comp
  have hzr : Computable fun p : P => p.1.2 := (Primrec.snd.comp Primrec.fst).to_comp
  have hzs : Computable fun p : P => p.2 := Computable.snd
  have hr : Computable fun p : P => decodedQuotationRat p.1.2 :=
    decodedQuotationRat_prim.to_comp.comp hzr
  have hs : Computable fun p : P => decodedQuotationRat p.2 :=
    decodedQuotationRat_prim.to_comp.comp hzs
  have hlt : Computable fun p : P => decide
      (decodedQuotationRat p.1.2 < decodedQuotationRat p.2) := by
    have hle : Computable fun p : P => decide
        (decodedQuotationRat p.2 ≤ decodedQuotationRat p.1.2) :=
      ratLE_prim.decide.to_comp.comp hs hr
    exact ((Primrec.dom_bool Bool.not).to_comp.comp hle).of_eq fun p => by
      by_cases h : decodedQuotationRat p.2 ≤ decodedQuotationRat p.1.2
      · have hnlt : ¬ decodedQuotationRat p.1.2 < decodedQuotationRat p.2 := not_lt_of_ge h
        simp [h, hnlt]
      · have hlt : decodedQuotationRat p.1.2 < decodedQuotationRat p.2 := lt_of_not_ge h
        simp [h, hlt]
  have hevidence (positive : Bool) (z : P → ℕ) (hz : Computable z) :
      Computable fun p : P => semanticQuoteFactorEvidenceAtFuel base
        p.1.1.1.1 p.1.1.1.2 p.1.1.2 (z p) positive :=
    semanticQuoteFactorEvidenceAtFuel_computable base |>.comp
      ((((hschema.pair hfuel).pair hn).pair hz).pair (Computable.const positive))
  have hbody : Computable fun p : P =>
      semanticQuoteFactorEvidenceAtFuel base p.1.1.1.1 p.1.1.1.2
          p.1.1.2 p.1.2 true ||
        semanticQuoteFactorEvidenceAtFuel base p.1.1.1.1 p.1.1.1.2
          p.1.1.2 p.2 false :=
    (Primrec.dom_bool₂ (· || ·)).to_comp.comp
      (hevidence true _ hzr) (hevidence false _ hzs)
  exact (Computable.cond hlt hbody (Computable.const true)).of_eq fun p => by
    simp only [semanticQuoteFactorDownwardAtFuel]
    by_cases h : decodedQuotationRat p.1.2 < decodedQuotationRat p.2 <;> simp [h]

private lemma listRangeAll_computable {P : Type*} [Primcodable P]
    {bound : P → ℕ} {test : P → ℕ → Bool}
    (hbound : Computable bound) (htest : Computable₂ test) :
    Computable fun p => (List.range (bound p + 1)).all (test p) := by
  have hbase : Computable fun p : P => test p 0 :=
    htest.comp Computable.id (Computable.const 0)
  have hstep : Computable₂ fun (p : P) (q : ℕ × Bool) =>
      q.2 && test p (q.1 + 1) := by
    exact (Primrec.dom_bool₂ (· && ·)).to_comp.comp
      (Computable.snd.comp Computable.snd)
      (htest.comp (Computable.fst)
        (Computable.succ.comp (Computable.fst.comp Computable.snd))) |>.to₂
  refine (Computable.nat_rec hbound hbase hstep).of_eq fun p => ?_
  induction bound p with
  | zero => simp
  | succ k ih => simp [List.range_succ, List.all_append, ih, Bool.and_assoc]

set_option maxHeartbeats 2000000 in
lemma semanticQuoteFactorPrefixValidAtFuel_computable {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) :
    Computable fun p : (ℕ × ℕ) × ℕ =>
      semanticQuoteFactorPrefixValidAtFuel base p.1.1 p.1.2 p.2 := by
  have hdown := semanticQuoteFactorDownwardAtFuel_computable base
  have hzs : Computable fun p : ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) =>
      semanticQuoteFactorZsValid base p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.1.2 p.2 := by
    apply listRangeAll_computable Computable.snd
    have hpack : Computable fun a : (((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) =>
        (a.1.1, a.2) := (Computable.fst.comp Computable.fst).pair Computable.snd
    exact hdown.comp hpack
  have hzr : Computable fun p : (((ℕ × ℕ) × ℕ) × ℕ) =>
      semanticQuoteFactorZrValid base p.1.1.1 p.2 p.1.1.2 p.1.2 := by
    apply listRangeAll_computable Computable.snd
    have hpack : Computable fun a : ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) =>
        ((a.1.1, a.2), a.1.2) :=
      ((Computable.fst.comp Computable.fst).pair Computable.snd).pair
        (Computable.snd.comp Computable.fst)
    exact hzs.comp hpack
  have hn : Computable fun p : ((ℕ × ℕ) × ℕ) =>
      semanticQuoteFactorNValid base p.1.1 p.2 p.1.2 := by
    apply listRangeAll_computable Computable.snd
    have hpack : Computable fun a : (((ℕ × ℕ) × ℕ) × ℕ) =>
        ((a.1.1, a.2), a.1.2) :=
      ((Computable.fst.comp Computable.fst).pair Computable.snd).pair
        (Computable.snd.comp Computable.fst)
    exact hzr.comp hpack
  have htag : Computable fun p : (ℕ × ℕ) × ℕ => p.1.1.unpair.1 == 2 :=
    (Primrec.eq.comp
      (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.const 2)).decide.to_comp
  have hn' : Computable fun p : (ℕ × ℕ) × ℕ =>
      semanticQuoteFactorNValid base p.1.1 p.1.2 p.2 :=
    hn.comp (((Computable.fst.comp Computable.fst).pair Computable.snd).pair
      (Computable.snd.comp Computable.fst))
  exact ((Primrec.dom_bool₂ (· && ·)).to_comp.comp htag hn').of_eq fun _ => rfl

/-! ## Clock monotonicity -/

private lemma listAll_mono_fuel {P : Type*} {test : P → ℕ → Bool}
    (hmono : ∀ p {f g}, f ≤ g → test p f = true → test p g = true)
    (xs : List P) {f g : ℕ} (hfg : f ≤ g)
    (h : xs.all fun p => test p f) : xs.all (fun p => test p g) := by
  rw [List.all_eq_true] at h ⊢
  intro p hp
  exact hmono p hfg (h p hp)

private lemma listAll_eventually {P : Type*} {test : P → ℕ → Bool}
    (hmono : ∀ p {f g}, f ≤ g → test p f = true → test p g = true)
    (heventual : ∀ p, ∃ f, test p f = true) :
    ∀ xs : List P, ∃ f, xs.all (fun p => test p f) = true := by
  intro xs
  induction xs with
  | nil => exact ⟨0, by simp⟩
  | cons p ps ih =>
      obtain ⟨fp, hfp⟩ := heventual p
      obtain ⟨fs, hfs⟩ := ih
      refine ⟨max fp fs, ?_⟩
      simp only [List.all_cons, Bool.and_eq_true]
      exact ⟨hmono p (le_max_left _ _) hfp,
        listAll_mono_fuel hmono ps (le_max_right _ _) hfs⟩

lemma semanticQuoteFactorDownwardAtFuel_mono {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) (schema n zr zs : ℕ)
    {fuel fuel' : ℕ} (hff : fuel ≤ fuel')
    (h : semanticQuoteFactorDownwardAtFuel base schema fuel n zr zs = true) :
    semanticQuoteFactorDownwardAtFuel base schema fuel' n zr zs = true := by
  by_cases hrs : decodedQuotationRat zr < decodedQuotationRat zs
  · simp only [semanticQuoteFactorDownwardAtFuel, semanticQuoteFactorEvidenceAtFuel,
      if_pos hrs, Bool.or_eq_true, Bool.and_eq_true] at h ⊢
    rcases h with h | h
    · exact Or.inl ⟨semanticSentenceSeenAtFuel_mono base hff h.1,
        semanticSentenceSeenAtFuel_mono base hff h.2⟩
    · exact Or.inr ⟨semanticSentenceSeenAtFuel_mono base hff h.1,
        semanticSentenceSeenAtFuel_mono base hff h.2⟩
  · simp [semanticQuoteFactorDownwardAtFuel, hrs]

private lemma semanticQuoteFactorZsValid_mono {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) (schema n zr limit : ℕ)
    {fuel fuel' : ℕ} (hff : fuel ≤ fuel')
    (h : semanticQuoteFactorZsValid base schema fuel n zr limit = true) :
    semanticQuoteFactorZsValid base schema fuel' n zr limit = true := by
  exact listAll_mono_fuel
    (fun zs _ _ hfg hz => semanticQuoteFactorDownwardAtFuel_mono
      base schema n zr zs hfg hz) _ hff h

private lemma semanticQuoteFactorZrValid_mono {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) (schema limit n : ℕ)
    {fuel fuel' : ℕ} (hff : fuel ≤ fuel')
    (h : semanticQuoteFactorZrValid base schema limit fuel n = true) :
    semanticQuoteFactorZrValid base schema limit fuel' n = true := by
  exact listAll_mono_fuel
    (fun zr _ _ hfg hz => semanticQuoteFactorZsValid_mono
      base schema n zr limit hfg hz) _ hff h

lemma semanticQuoteFactorPrefixValidAtFuel_mono {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) (schema limit : ℕ)
    {fuel fuel' : ℕ} (hff : fuel ≤ fuel')
    (h : semanticQuoteFactorPrefixValidAtFuel base schema limit fuel = true) :
    semanticQuoteFactorPrefixValidAtFuel base schema limit fuel' = true := by
  obtain ⟨htag, hN⟩ : (schema.unpair.1 == 2) = true ∧
      semanticQuoteFactorNValid base schema limit fuel = true := by
    simpa [semanticQuoteFactorPrefixValidAtFuel] using h
  rw [semanticQuoteFactorPrefixValidAtFuel, Bool.and_eq_true]
  refine ⟨htag, ?_⟩
  rw [semanticQuoteFactorNValid, List.all_eq_true] at hN ⊢
  intro n hn
  rw [semanticQuoteFactorZrValid, List.all_eq_true] at ⊢
  intro zr hzr
  rw [semanticQuoteFactorZsValid, List.all_eq_true] at ⊢
  intro zs hzs
  exact semanticQuoteFactorDownwardAtFuel_mono base schema n zr zs hff
    (by
      have hNn := hN n hn
      rw [semanticQuoteFactorZrValid, List.all_eq_true] at hNn
      have hzrFuel := hNn zr hzr
      rw [semanticQuoteFactorZsValid, List.all_eq_true] at hzrFuel
      exact hzrFuel zs hzs)

lemma semanticQuoteFactorPrefixValidAtFuel_downward {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) {schema limit fuel n zr zs : ℕ}
    (h : semanticQuoteFactorPrefixValidAtFuel base schema limit fuel = true)
    (hn : n ≤ limit) (hr : zr ≤ limit) (hs : zs ≤ limit) :
    semanticQuoteFactorDownwardAtFuel base schema fuel n zr zs = true := by
  have hnmem : n ∈ List.range (limit + 1) := by simpa using hn
  have hrmem : zr ∈ List.range (limit + 1) := by simpa using hr
  have hsmem : zs ∈ List.range (limit + 1) := by simpa using hs
  have hpair : (schema.unpair.1 == 2) = true ∧
      semanticQuoteFactorNValid base schema limit fuel = true := by
    simpa [semanticQuoteFactorPrefixValidAtFuel] using h
  obtain ⟨_, hN⟩ := hpair
  rw [semanticQuoteFactorNValid, List.all_eq_true] at hN
  have hzrFuel := hN n hnmem
  rw [semanticQuoteFactorZrValid, List.all_eq_true] at hzrFuel
  have hzsFuel := hzrFuel zr hrmem
  rw [semanticQuoteFactorZsValid, List.all_eq_true] at hzsFuel
  exact hzsFuel zs hsmem

/-! ## Completeness for every rational quote code -/

/-- The quotation-factor completeness argument works in any fixed computable base which
contains the canonical theorem/quotation stages. -/
lemma rationalQuote_semanticQuoteFactorDownward_eventually_of_subprocess
    (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T]
    {DP : DeductiveProcess} (base : DeductiveProcessComputation DP)
    (hsub : ∀ k phi, phi ∈ (theoremQuoteBaseDP T).D k → phi ∈ DP.D k)
    {value : ℕ → ℚ} (q : RationalQuoteCode T value)
    (n zr zs : ℕ) :
    ∃ fuel, semanticQuoteFactorDownwardAtFuel base
      (semanticQuoteSchema q.code) fuel n zr zs = true := by
  by_cases hrs : decodedQuotationRat zr < decodedQuotationRat zs
  · by_cases hrv : decodedQuotationRat zr < value n
    · obtain ⟨k, hk⟩ := (quotationPresentation T).quote_positive_enters q.code
          (Nat.pair n (Encodable.encode (decodedQuotationRat zr)))
          (q.pos_complete n _ hrv)
      have hbase : semanticQuoteFactorClaim (semanticQuoteSchema q.code) n zr true ∈
          DP.D k := hsub k _ (by
        change _ ∈ (theoremDP T).D k ∪ semanticQuoteDP.D k
        apply Finset.mem_union_left
        simpa [semanticQuoteFactorClaim, semanticQuoteSchema, Nat.unpair_pair] using hk)
      obtain ⟨fuel, hfuel⟩ := semanticSentenceSeenAtFuel_eventually base hbase
      let e := Nat.pair 0 (Nat.pair q.code
        (Nat.pair n (Encodable.encode (decodedQuotationRat zr))))
      have hlinkBase : semanticQuoteFactorLink (semanticQuoteSchema q.code) n zr true ∈
          DP.D e := hsub e _ (by
        change _ ∈ (theoremDP T).D e ∪ semanticQuoteDP.D e
        apply Finset.mem_union_right
        change _ ∈ (semanticQuoteStageList e).toFinset
        simpa [semanticQuoteFactorLink, semanticQuoteSchema, e] using
          (List.mem_toFinset.mpr (mem_semanticQuoteStageList (le_refl e))))
      obtain ⟨linkFuel, hlinkFuel⟩ := semanticSentenceSeenAtFuel_eventually base hlinkBase
      let common := max fuel linkFuel
      have hc := semanticSentenceSeenAtFuel_mono base
        (Nat.le_max_left fuel linkFuel) hfuel
      have hl := semanticSentenceSeenAtFuel_mono base
        (Nat.le_max_right fuel linkFuel) hlinkFuel
      exact ⟨common, by
        simp only [semanticQuoteFactorDownwardAtFuel, semanticQuoteFactorEvidenceAtFuel,
          if_pos hrs, Bool.or_eq_true, Bool.and_eq_true]
        exact Or.inl ⟨hc, hl⟩⟩
    · have hvs : value n < decodedQuotationRat zs :=
        lt_of_le_of_lt (not_lt.mp hrv) hrs
      obtain ⟨k, hk⟩ := (quotationPresentation T).quote_negative_refutes q.code
          (Nat.pair n (Encodable.encode (decodedQuotationRat zs)))
          (q.neg_complete n _ hvs)
      have hbase : semanticQuoteFactorClaim (semanticQuoteSchema q.code) n zs false ∈
          DP.D k := hsub k _ (by
        change _ ∈ (theoremDP T).D k ∪ semanticQuoteDP.D k
        apply Finset.mem_union_left
        simpa [semanticQuoteFactorClaim, semanticQuoteSchema, Nat.unpair_pair] using hk)
      obtain ⟨fuel, hfuel⟩ := semanticSentenceSeenAtFuel_eventually base hbase
      let e := Nat.pair 1 (Nat.pair q.code
        (Nat.pair n (Encodable.encode (decodedQuotationRat zs))))
      have hlinkBase : semanticQuoteFactorLink (semanticQuoteSchema q.code) n zs false ∈
          DP.D e := hsub e _ (by
        change _ ∈ (theoremDP T).D e ∪ semanticQuoteDP.D e
        apply Finset.mem_union_right
        change _ ∈ (semanticQuoteStageList e).toFinset
        simpa [semanticQuoteFactorLink, semanticQuoteSchema, e] using
          (List.mem_toFinset.mpr (mem_semanticQuoteStageList (le_refl e))))
      obtain ⟨linkFuel, hlinkFuel⟩ := semanticSentenceSeenAtFuel_eventually base hlinkBase
      let common := max fuel linkFuel
      have hc := semanticSentenceSeenAtFuel_mono base
        (Nat.le_max_left fuel linkFuel) hfuel
      have hl := semanticSentenceSeenAtFuel_mono base
        (Nat.le_max_right fuel linkFuel) hlinkFuel
      exact ⟨common, by
        simp only [semanticQuoteFactorDownwardAtFuel, semanticQuoteFactorEvidenceAtFuel,
          if_pos hrs, Bool.or_eq_true, Bool.and_eq_true]
        exact Or.inr ⟨hc, hl⟩⟩
  · exact ⟨0, by simp [semanticQuoteFactorDownwardAtFuel, hrs]⟩

/-- The fixed-base instance of the completeness argument. -/
lemma rationalQuote_semanticQuoteFactorDownward_eventually
    (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T]
    {value : ℕ → ℚ} (q : RationalQuoteCode T value)
    (n zr zs : ℕ) :
    ∃ fuel, semanticQuoteFactorDownwardAtFuel (theoremQuoteBaseDPComputation T)
      (semanticQuoteSchema q.code) fuel n zr zs = true :=
  rationalQuote_semanticQuoteFactorDownward_eventually_of_subprocess T
    (theoremQuoteBaseDPComputation T) (fun _ _ h => h) q n zr zs

set_option maxHeartbeats 2000000 in
lemma rationalQuote_semanticQuoteFactorPrefix_eventually_of_subprocess
    (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T]
    {DP : DeductiveProcess} (base : DeductiveProcessComputation DP)
    (hsub : ∀ k phi, phi ∈ (theoremQuoteBaseDP T).D k → phi ∈ DP.D k)
    {value : ℕ → ℚ} (q : RationalQuoteCode T value) (limit : ℕ) :
    ∃ fuel, semanticQuoteFactorPrefixValidAtFuel base
      (semanticQuoteSchema q.code) limit fuel = true := by
  have hzs (n zr : ℕ) : ∃ fuel,
      semanticQuoteFactorZsValid base (semanticQuoteSchema q.code)
        fuel n zr limit = true := by
    simpa [semanticQuoteFactorZsValid] using
      (listAll_eventually (test := fun zs fuel =>
        semanticQuoteFactorDownwardAtFuel base
          (semanticQuoteSchema q.code) fuel n zr zs)
        (fun zs _ _ hfg h => semanticQuoteFactorDownwardAtFuel_mono
          base _ _ _ _ hfg h)
        (fun zs => rationalQuote_semanticQuoteFactorDownward_eventually_of_subprocess
          T base hsub q n zr zs)
        (List.range (limit + 1)))
  have hzr (n : ℕ) : ∃ fuel,
      semanticQuoteFactorZrValid base (semanticQuoteSchema q.code)
        limit fuel n = true := by
    apply listAll_eventually
        (test := fun zr fuel => semanticQuoteFactorZsValid
          base (semanticQuoteSchema q.code) fuel n zr limit)
        _ (hzs n) (List.range (limit + 1))
    intro zr f g hfg h
    exact semanticQuoteFactorZsValid_mono base
      (semanticQuoteSchema q.code) n zr limit hfg h
  obtain ⟨fuel, hfuel⟩ := listAll_eventually
    (test := fun n fuel => semanticQuoteFactorZrValid
      base (semanticQuoteSchema q.code) limit fuel n)
    (fun n _ _ hfg h => semanticQuoteFactorZrValid_mono
      base (semanticQuoteSchema q.code) limit n hfg h)
    hzr (List.range (limit + 1))
  refine ⟨fuel, ?_⟩
  rw [semanticQuoteFactorPrefixValidAtFuel, Bool.and_eq_true]
  exact ⟨by simp [semanticQuoteSchema], by
    rw [semanticQuoteFactorNValid, List.all_eq_true]
    exact List.all_eq_true.mp hfuel⟩

/-- The fixed-base instance of the finite-prefix completeness argument. -/
lemma rationalQuote_semanticQuoteFactorPrefix_eventually
    (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T]
    {value : ℕ → ℚ} (q : RationalQuoteCode T value) (limit : ℕ) :
    ∃ fuel, semanticQuoteFactorPrefixValidAtFuel (theoremQuoteBaseDPComputation T)
      (semanticQuoteSchema q.code) limit fuel = true :=
  rationalQuote_semanticQuoteFactorPrefix_eventually_of_subprocess T
    (theoremQuoteBaseDPComputation T) (fun _ _ h => h) q limit

end LogicalInduction
