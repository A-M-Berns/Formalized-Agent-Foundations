import LogicalInduction.Construction.Witnesses.CertifiedSource

/-!
# Executable registry checks for certified semantic sources

`CertifiedSourceLUVSeq` is the paper-facing metatheoretic package.  This file begins the
fixed, object-level registry which can recognize such packages without inspecting their
Lean proofs.  A tag-`0` semantic schema carries two ordinary program codes: an arbitrary
rational threshold emitter and a cut-certificate stage finder.  The checker below runs
both programs for bounded fuel, decodes the emitted sentence, verifies old-language
ownership, and confirms the requested cut law in an actually decoded base-process stage.

Timeouts, malformed outputs, invalid cut queries, and non-source schemas all return
`none`.  Thus this is suitable as the local admission test used by a later universal
dovetailing deductive process.
-/

namespace LogicalInduction

open LO LO.Propositional

attribute [local irreducible] Nat.sqrt

/-! ## Decoding the self-describing schema -/

/-- The emitter program named by a tag-`0` semantic schema. -/
def semanticSourceEmitterCode (schema : ℕ) : Nat.Partrec.Code :=
  Denumerable.ofNat Nat.Partrec.Code schema.unpair.2.unpair.1

/-- The cut-certificate stage finder named by a tag-`0` semantic schema. -/
def semanticSourceCertificateCode (schema : ℕ) : Nat.Partrec.Code :=
  Denumerable.ofNat Nat.Partrec.Code schema.unpair.2.unpair.2

@[simp] lemma certified_thresholdSchema_emitterCode {DP : DeductiveProcess}
    (X : CertifiedSourceLUVSeq DP) :
    semanticSourceEmitterCode X.thresholdSchema = X.emitterCode := by
  simp [semanticSourceEmitterCode, CertifiedSourceLUVSeq.thresholdSchema,
    semanticEmitterSchema, semanticSourceSchema]

@[simp] lemma certified_thresholdSchema_certificateCode {DP : DeductiveProcess}
    (X : CertifiedSourceLUVSeq DP) :
    semanticSourceCertificateCode X.thresholdSchema = X.cut_certificate.stageCode := by
  simp [semanticSourceCertificateCode, CertifiedSourceLUVSeq.thresholdSchema,
    semanticEmitterSchema, semanticSourceSchema]

/-! ## Bounded source execution -/

/-- Run and decode a schema's threshold emitter for bounded fuel. -/
def semanticSourceSentenceAtFuel (schema input fuel : ℕ) : Option Sentence :=
  (Nat.Partrec.Code.evaln fuel (semanticSourceEmitterCode schema) input).bind
    (Encodable.decode (α := Sentence))

/-- Run a schema's cut-certificate program for bounded fuel. -/
def semanticSourceStageIndexAtFuel (schema job fuel : ℕ) : Option ℕ :=
  Nat.Partrec.Code.evaln fuel (semanticSourceCertificateCode schema) job

/-- Executable old-language ownership test. -/
def semanticPrimeFreshSentenceB (φ : Sentence) : Bool :=
  decide (((sentenceAtomOccurrences φ).filter
    (fun a => a.unpair.1 = semanticPrimeTag)).length = 0)

private lemma sentenceAtomCodes_eq_atoms (φ : Sentence) :
    sentenceAtomCodes φ = φ.atoms := by
  induction φ using Formula.rec' with
  | hfalsum => rfl
  | hatom _ => rfl
  | himp φ ψ ihφ ihψ => simp [sentenceAtomCodes_imp, Sentence.atoms, ihφ, ihψ]
  | hand φ ψ ihφ ihψ => simp [sentenceAtomCodes_and, Sentence.atoms, ihφ, ihψ]
  | hor φ ψ ihφ ihψ => simp [sentenceAtomCodes_or, Sentence.atoms, ihφ, ihψ]

@[simp] lemma semanticPrimeFreshSentenceB_eq_true (φ : Sentence) :
    semanticPrimeFreshSentenceB φ = true ↔ SemanticPrimeFreshSentence φ := by
  simp [semanticPrimeFreshSentenceB, SemanticPrimeFreshSentence,
    List.length_eq_zero_iff, List.filter_eq_nil_iff, mem_sentenceAtomOccurrences,
    sentenceAtomCodes_eq_atoms]

/-! The bounded registry operations are primitive recursive.  These lemmas are kept
separate so the eventual universal DP can reuse them without unfolding the verifier. -/

lemma semanticSourceEmitterCode_prim : Primrec semanticSourceEmitterCode := by
  exact (Primrec.ofNat Nat.Partrec.Code).comp
    (Primrec.fst.comp (Primrec.unpair.comp
      (Primrec.snd.comp Primrec.unpair)))

lemma semanticSourceCertificateCode_prim : Primrec semanticSourceCertificateCode := by
  exact (Primrec.ofNat Nat.Partrec.Code).comp
    (Primrec.snd.comp (Primrec.unpair.comp
      (Primrec.snd.comp Primrec.unpair)))

lemma semanticSourceSentenceAtFuel_prim : Primrec fun p : (ℕ × ℕ) × ℕ =>
    semanticSourceSentenceAtFuel p.1.1 p.1.2 p.2 := by
  have heval : Primrec fun p : (ℕ × ℕ) × ℕ =>
      Nat.Partrec.Code.evaln p.2 (semanticSourceEmitterCode p.1.1) p.1.2 :=
    Nat.Partrec.Code.primrec_evaln.comp
      ((Primrec.snd.pair (semanticSourceEmitterCode_prim.comp
        (Primrec.fst.comp Primrec.fst))).pair (Primrec.snd.comp Primrec.fst))
  exact (Primrec.option_bind heval
    ((Primrec.decode.comp Primrec.snd).to₂)).of_eq fun _ => rfl

lemma semanticSourceStageIndexAtFuel_prim : Primrec fun p : (ℕ × ℕ) × ℕ =>
    semanticSourceStageIndexAtFuel p.1.1 p.1.2 p.2 := by
  exact Nat.Partrec.Code.primrec_evaln.comp
    ((Primrec.snd.pair (semanticSourceCertificateCode_prim.comp
      (Primrec.fst.comp Primrec.fst))).pair (Primrec.snd.comp Primrec.fst))

lemma semanticPrimeFreshSentenceB_prim : Primrec semanticPrimeFreshSentenceB := by
  have hbad : PrimrecPred fun a : ℕ => a.unpair.1 = semanticPrimeTag :=
    Primrec.eq.comp (Primrec.fst.comp Primrec.unpair)
      (Primrec.const semanticPrimeTag)
  have hfiltered : Primrec fun φ : Sentence =>
      (sentenceAtomOccurrences φ).filter
        (fun a => a.unpair.1 = semanticPrimeTag) :=
    (Primrec.listFilter hbad).comp sentenceAtomOccurrences_prim
  have hzero : PrimrecPred fun φ : Sentence =>
      ((sentenceAtomOccurrences φ).filter
        (fun a => a.unpair.1 = semanticPrimeTag)).length = 0 :=
    Primrec.eq.comp (Primrec.list_length.comp hfiltered) (Primrec.const 0)
  exact hzero.decide.of_eq fun _ => rfl

private def freshSourceSentence (φ : Sentence) : Option Sentence :=
  if semanticPrimeFreshSentenceB φ then some φ else none

private def freshNegSourceSentence (φ : Sentence) : Option Sentence :=
  if semanticPrimeFreshSentenceB φ then some (∼φ) else none

private def freshImpSourceSentence (φr φs : Sentence) : Option Sentence :=
  if semanticPrimeFreshSentenceB φr && semanticPrimeFreshSentenceB φs then
    some (φs 🡒 φr)
  else none

private lemma sentenceNeg_prim : Primrec fun φ : Sentence => ∼φ := by
  apply Primrec.encode_iff.mp
  exact (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 2)
    (Primrec₂.natPair.comp Primrec.encode (Primrec.const 1)))).of_eq fun _ => rfl

private lemma sentenceImp_prim : Primrec₂ fun φ ψ : Sentence => φ 🡒 ψ := by
  apply Primrec₂.encode_iff.mp
  exact (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 2)
    (Primrec₂.natPair.comp
      (Primrec.encode.comp Primrec.fst)
      (Primrec.encode.comp Primrec.snd)))).to₂.of_eq fun _ _ => rfl

private lemma freshSourceSentence_prim : Primrec freshSourceSentence := by
  have hp : PrimrecPred fun φ : Sentence => semanticPrimeFreshSentenceB φ = true :=
    Primrec.eq.comp semanticPrimeFreshSentenceB_prim (Primrec.const true)
  exact (Primrec.ite hp Primrec.option_some (Primrec.const none)).of_eq fun _ => rfl

private lemma freshNegSourceSentence_prim : Primrec freshNegSourceSentence := by
  have hp : PrimrecPred fun φ : Sentence => semanticPrimeFreshSentenceB φ = true :=
    Primrec.eq.comp semanticPrimeFreshSentenceB_prim (Primrec.const true)
  exact (Primrec.ite hp (Primrec.option_some.comp sentenceNeg_prim)
    (Primrec.const none)).of_eq fun _ => rfl

private lemma freshImpSourceSentence_prim : Primrec₂ freshImpSourceSentence := by
  have hp : PrimrecPred fun p : Sentence × Sentence =>
      semanticPrimeFreshSentenceB p.1 = true ∧
        semanticPrimeFreshSentenceB p.2 = true :=
    (Primrec.eq.comp (semanticPrimeFreshSentenceB_prim.comp Primrec.fst)
      (Primrec.const true)).and
    (Primrec.eq.comp (semanticPrimeFreshSentenceB_prim.comp Primrec.snd)
      (Primrec.const true))
  exact (Primrec.ite hp
    (Primrec.option_some.comp (sentenceImp_prim.comp Primrec.snd Primrec.fst))
    (Primrec.const none)).to₂.of_eq fun φr φs => by
      by_cases hr : semanticPrimeFreshSentenceB φr = true <;>
        by_cases hs : semanticPrimeFreshSentenceB φs = true <;>
        simp [freshImpSourceSentence, hr, hs]

/-- Decode a rational payload, using the repository's harmless zero default. -/
private abbrev sourceRat (z : ℕ) : ℚ := decodedQuotationRat z

/-- Reconstruct the cut law requested by `job`, using bounded calls to the named emitter.

The result includes only syntactically valid bound/downward queries, and every decoded
source sentence must pass the old-language ownership check. -/
def semanticSourceCutLawAtFuel (schema job fuel : ℕ) : Option Sentence :=
  let tag := job.unpair.1
  let payload := job.unpair.2
  let n := payload.unpair.1
  if tag = 0 then
    let r := sourceRat payload.unpair.2
    if r < 0 then do
      let φ ← semanticSourceSentenceAtFuel schema
        (Nat.pair n (Encodable.encode r)) fuel
      freshSourceSentence φ
    else none
  else if tag = 1 then
    let r := sourceRat payload.unpair.2
    if 1 < r then do
      let φ ← semanticSourceSentenceAtFuel schema
        (Nat.pair n (Encodable.encode r)) fuel
      freshNegSourceSentence φ
    else none
  else if tag = 2 then
    let r := sourceRat payload.unpair.2.unpair.1
    let s := sourceRat payload.unpair.2.unpair.2
    if r < s then do
      let φr ← semanticSourceSentenceAtFuel schema
        (Nat.pair n (Encodable.encode r)) fuel
      let φs ← semanticSourceSentenceAtFuel schema
        (Nat.pair n (Encodable.encode s)) fuel
      freshImpSourceSentence φr φs
    else none
  else none

lemma semanticSourceCutLawAtFuel_prim : Primrec fun p : (ℕ × ℕ) × ℕ =>
    semanticSourceCutLawAtFuel p.1.1 p.1.2 p.2 := by
  let P := (ℕ × ℕ) × ℕ
  let hschema : Primrec fun p : P => p.1.1 := Primrec.fst.comp Primrec.fst
  let hjob : Primrec fun p : P => p.1.2 := Primrec.snd.comp Primrec.fst
  let hfuel : Primrec fun p : P => p.2 := Primrec.snd
  let htag : Primrec fun p : P => p.1.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp hjob)
  let hpayload : Primrec fun p : P => p.1.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp hjob)
  let hn : Primrec fun p : P => p.1.2.unpair.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp hpayload)
  let hr : Primrec fun p : P => sourceRat p.1.2.unpair.2.unpair.2 :=
    decodedQuotationRat_prim.comp (Primrec.snd.comp (Primrec.unpair.comp hpayload))
  let hdownPayload : Primrec fun p : P => p.1.2.unpair.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp hpayload)
  let hdr : Primrec fun p : P => sourceRat p.1.2.unpair.2.unpair.2.unpair.1 :=
    decodedQuotationRat_prim.comp
      (Primrec.fst.comp (Primrec.unpair.comp hdownPayload))
  let hds : Primrec fun p : P => sourceRat p.1.2.unpair.2.unpair.2.unpair.2 :=
    decodedQuotationRat_prim.comp
      (Primrec.snd.comp (Primrec.unpair.comp hdownPayload))
  have sourceAt {q : P → ℚ} (hq : Primrec q) :
      Primrec fun p : P => semanticSourceSentenceAtFuel p.1.1
        (Nat.pair p.1.2.unpair.2.unpair.1 (Encodable.encode (q p))) p.2 := by
    have hinput : Primrec fun p : P =>
        Nat.pair p.1.2.unpair.2.unpair.1 (Encodable.encode (q p)) :=
      Primrec₂.natPair.comp hn (Primrec.encode.comp hq)
    exact semanticSourceSentenceAtFuel_prim.comp
      ((hschema.pair hinput).pair hfuel)
  have hsourceR := sourceAt hr
  have hsourceDR := sourceAt hdr
  have hsourceDS := sourceAt hds
  have hbelowOut : Primrec fun p : P =>
      (semanticSourceSentenceAtFuel p.1.1
        (Nat.pair p.1.2.unpair.2.unpair.1
          (Encodable.encode (sourceRat p.1.2.unpair.2.unpair.2))) p.2).bind
        freshSourceSentence :=
    Primrec.option_bind hsourceR
      ((freshSourceSentence_prim.comp Primrec.snd).to₂)
  have haboveOut : Primrec fun p : P =>
      (semanticSourceSentenceAtFuel p.1.1
        (Nat.pair p.1.2.unpair.2.unpair.1
          (Encodable.encode (sourceRat p.1.2.unpair.2.unpair.2))) p.2).bind
        freshNegSourceSentence :=
    Primrec.option_bind hsourceR
      ((freshNegSourceSentence_prim.comp Primrec.snd).to₂)
  have hdownOut : Primrec fun p : P =>
      (semanticSourceSentenceAtFuel p.1.1
        (Nat.pair p.1.2.unpair.2.unpair.1
          (Encodable.encode (sourceRat p.1.2.unpair.2.unpair.2.unpair.1))) p.2).bind
        fun φr =>
          (semanticSourceSentenceAtFuel p.1.1
            (Nat.pair p.1.2.unpair.2.unpair.1
              (Encodable.encode (sourceRat p.1.2.unpair.2.unpair.2.unpair.2))) p.2).bind
            fun φs => freshImpSourceSentence φr φs := by
    let Q := P × Sentence
    have hsourceDSQ : Primrec fun q : Q =>
        semanticSourceSentenceAtFuel q.1.1.1
          (Nat.pair q.1.1.2.unpair.2.unpair.1
            (Encodable.encode (sourceRat q.1.1.2.unpair.2.unpair.2.unpair.2))) q.1.2 :=
      hsourceDS.comp Primrec.fst
    have hcombine : Primrec₂ fun (q : Q) (φs : Sentence) =>
        freshImpSourceSentence q.2 φs :=
      freshImpSourceSentence_prim.comp₂
        (Primrec.snd.comp₂ Primrec₂.left) Primrec₂.right
    have hinner : Primrec₂ fun (p : P) (φr : Sentence) =>
        (semanticSourceSentenceAtFuel p.1.1
          (Nat.pair p.1.2.unpair.2.unpair.1
            (Encodable.encode (sourceRat p.1.2.unpair.2.unpair.2.unpair.2))) p.2).bind
          fun φs => freshImpSourceSentence φr φs :=
      (Primrec.option_bind hsourceDSQ hcombine).to₂
    exact Primrec.option_bind hsourceDR hinner
  have htagEq (k : ℕ) : PrimrecPred fun p : P => p.1.2.unpair.1 = k :=
    Primrec.eq.comp htag (Primrec.const k)
  have hbelowValid : PrimrecPred fun p : P =>
      sourceRat p.1.2.unpair.2.unpair.2 < 0 :=
    (ratLE_prim.comp (Primrec.const 0) hr).not.of_eq fun p => by
      simp only [not_le]
  have haboveValid : PrimrecPred fun p : P =>
      1 < sourceRat p.1.2.unpair.2.unpair.2 :=
    (ratLE_prim.comp hr (Primrec.const 1)).not.of_eq fun p => by
      simp only [not_le]
  have hdownValid : PrimrecPred fun p : P =>
      sourceRat p.1.2.unpair.2.unpair.2.unpair.1 <
        sourceRat p.1.2.unpair.2.unpair.2.unpair.2 :=
    (ratLE_prim.comp hds hdr).not.of_eq fun p => by
      simp only [not_le]
  have hbelow := Primrec.ite hbelowValid hbelowOut (Primrec.const none)
  have habove := Primrec.ite haboveValid haboveOut (Primrec.const none)
  have hdown := Primrec.ite hdownValid hdownOut (Primrec.const none)
  exact (Primrec.ite (htagEq 0) hbelow
    (Primrec.ite (htagEq 1) habove
      (Primrec.ite (htagEq 2) hdown (Primrec.const none)))).of_eq fun _ => rfl

/-- Full bounded admission check for one cut-law query.

Besides reconstructing the law, the checker requires the certificate program to name a
base-process stage which really contains that law. -/
def semanticSourceCheckedLawAtFuel {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) (schema job fuel : ℕ) : Option Sentence :=
  if schema.unpair.1 = 0 then do
    let law ← semanticSourceCutLawAtFuel schema job fuel
    let stageIndex ← semanticSourceStageIndexAtFuel schema job fuel
    let stage ← base.stageAtFuel fuel stageIndex
    if law ∈ stage then some law else none
  else none

private def keepLawIfMem (law : Sentence) (stage : Finset Sentence) : Option Sentence :=
  if law ∈ stage then some law else none

private lemma keepLawIfMem_prim : Primrec₂ keepLawIfMem := by
  have hp : PrimrecPred fun p : Sentence × Finset Sentence => p.1 ∈ p.2 :=
    sentenceMemSupport_prim.comp₂ Primrec₂.right Primrec₂.left
  exact (Primrec.ite hp
    (Primrec.option_some.comp Primrec.fst) (Primrec.const none)).to₂.of_eq
      fun _ _ => rfl

/-- The full bounded admission checker is primitive recursive for every fixed computable
base process.  This is the executable gate needed by a single universal source DP. -/
theorem semanticSourceCheckedLawAtFuel_prim {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) :
    Primrec fun p : (ℕ × ℕ) × ℕ =>
      semanticSourceCheckedLawAtFuel base p.1.1 p.1.2 p.2 := by
  let P := (ℕ × ℕ) × ℕ
  have hcut : Primrec fun p : P =>
      semanticSourceCutLawAtFuel p.1.1 p.1.2 p.2 :=
    semanticSourceCutLawAtFuel_prim
  have hstageIndex : Primrec fun p : P =>
      semanticSourceStageIndexAtFuel p.1.1 p.1.2 p.2 :=
    semanticSourceStageIndexAtFuel_prim
  let Q := P × Sentence
  have hstageIndexQ : Primrec fun q : Q =>
      semanticSourceStageIndexAtFuel q.1.1.1 q.1.1.2 q.1.2 :=
    hstageIndex.comp Primrec.fst
  let R := Q × ℕ
  have hstage : Primrec fun z : R => base.stageAtFuel z.1.1.2 z.2 :=
    processStageAtFuel_prim base |>.comp
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd
  have hkeep : Primrec₂ fun (z : R) (stage : Finset Sentence) =>
      keepLawIfMem z.1.2 stage :=
    keepLawIfMem_prim.comp₂
      (Primrec.snd.comp₂ (Primrec.fst.comp₂ Primrec₂.left)) Primrec₂.right
  have hstageBind : Primrec fun z : R =>
      (base.stageAtFuel z.1.1.2 z.2).bind fun stage =>
        keepLawIfMem z.1.2 stage :=
    Primrec.option_bind hstage hkeep
  have hindexBind : Primrec₂ fun (p : P) (law : Sentence) =>
      (semanticSourceStageIndexAtFuel p.1.1 p.1.2 p.2).bind fun stageIndex =>
        (base.stageAtFuel p.2 stageIndex).bind fun stage =>
          keepLawIfMem law stage :=
    (Primrec.option_bind hstageIndexQ
      ((hstageBind.comp (Primrec.fst.pair Primrec.snd)).to₂)).to₂
  have hbody : Primrec fun p : P =>
      (semanticSourceCutLawAtFuel p.1.1 p.1.2 p.2).bind fun law =>
        (semanticSourceStageIndexAtFuel p.1.1 p.1.2 p.2).bind fun stageIndex =>
          (base.stageAtFuel p.2 stageIndex).bind fun stage =>
            keepLawIfMem law stage :=
    Primrec.option_bind hcut hindexBind
  have hsource : PrimrecPred fun p : P => p.1.1.unpair.1 = 0 :=
    Primrec.eq.comp
      (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.const 0)
  exact (Primrec.ite hsource hbody (Primrec.const none)).of_eq fun _ => rfl

/-! ## Checker soundness -/

/-- A successful registry check can only return a theorem in the actual fixed base
deductive process. -/
theorem semanticSourceCheckedLawAtFuel_mem {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) {schema job fuel : ℕ} {law : Sentence}
    (h : semanticSourceCheckedLawAtFuel base schema job fuel = some law) :
    ∃ k, law ∈ DP.D k := by
  unfold semanticSourceCheckedLawAtFuel at h
  split at h <;> try contradiction
  obtain ⟨law', hLaw, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨k, hk, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨stage, hstage, h⟩ := Option.bind_eq_some_iff.mp h
  split at h <;> try contradiction
  rename_i hmem
  simp only [Option.some.injEq] at h
  subst law
  exact ⟨k, base.stageAtFuel_sound hstage ▸ hmem⟩

/-- A successful check necessarily belongs to the source-schema namespace. -/
theorem semanticSourceCheckedLawAtFuel_source {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) {schema job fuel : ℕ} {law : Sentence}
    (h : semanticSourceCheckedLawAtFuel base schema job fuel = some law) :
    schema.unpair.1 = 0 := by
  simp only [semanticSourceCheckedLawAtFuel] at h
  split at h
  · assumption
  · contradiction

/-! ## Completeness for genuine certified packages -/

lemma evaln_decode_sentence_eventually (code : Nat.Partrec.Code)
    (input : ℕ) (φ : Sentence) (h : Encodable.encode φ ∈ code.eval input) :
    ∃ fuel, (code.evaln fuel input).bind (Encodable.decode (α := Sentence)) = some φ := by
  obtain ⟨fuel, hfuel⟩ := Nat.Partrec.Code.evaln_complete.mp h
  refine ⟨fuel, ?_⟩
  rw [show code.evaln fuel input = some (Encodable.encode φ) from hfuel]
  simp

/-- Every valid lower-bound certificate query of a genuine source eventually passes the
fixed executable checker. -/
theorem certified_below_eventually_checked {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) (X : CertifiedSourceLUVSeq DP)
    (n : ℕ) (r : ℚ) (hr : (r : ℝ) < 0) :
    ∃ fuel, semanticSourceCheckedLawAtFuel base X.thresholdSchema
      (sourceCutBelowJob n r) fuel = some ((X.toLUV n).gt r) := by
  obtain ⟨fe, he⟩ := evaln_decode_sentence_eventually X.emitterCode
    (Nat.pair n (Encodable.encode r)) ((X.toLUV n).gt r) (X.emitter_spec n r)
  obtain ⟨k, hkCode, hkLaw⟩ := X.cut_certificate.below n r hr
  obtain ⟨fc, hc⟩ := Nat.Partrec.Code.evaln_complete.mp hkCode
  obtain ⟨fs, hs⟩ := base.stageAtFuel_complete k
  let fuel := max fe (max fc fs)
  have he' : semanticSourceSentenceAtFuel X.thresholdSchema
      (Nat.pair n (Encodable.encode r)) fuel = some ((X.toLUV n).gt r) := by
    rw [semanticSourceSentenceAtFuel, certified_thresholdSchema_emitterCode]
    obtain ⟨out, hout, hdecode⟩ := Option.bind_eq_some_iff.mp he
    exact Option.bind_eq_some_iff.mpr ⟨out,
      Nat.Partrec.Code.evaln_mono (Nat.le_max_left _ _) hout, hdecode⟩
  have hc' : semanticSourceStageIndexAtFuel X.thresholdSchema
      (sourceCutBelowJob n r) fuel = some k := by
    rw [semanticSourceStageIndexAtFuel, certified_thresholdSchema_certificateCode]
    exact Nat.Partrec.Code.evaln_mono (le_trans (Nat.le_max_left _ _)
      (Nat.le_max_right _ _)) hc
  have hs' : base.stageAtFuel fuel k = some (DP.D k) :=
    base.stageAtFuel_mono (le_trans (Nat.le_max_right _ _)
      (Nat.le_max_right _ _)) hs
  have hrq : r < 0 := by exact_mod_cast hr
  have hfresh : semanticPrimeFreshSentenceB ((X.toLUV n).gt r) = true :=
    (semanticPrimeFreshSentenceB_eq_true _).2 (X.old_language n r)
  refine ⟨fuel, ?_⟩
  rw [semanticSourceCheckedLawAtFuel, if_pos X.thresholdSchema_source]
  have hcut : semanticSourceCutLawAtFuel X.thresholdSchema
      (sourceCutBelowJob n r) fuel = some ((X.toLUV n).gt r) := by
    simp [semanticSourceCutLawAtFuel, sourceCutBelowJob,
      decodedQuotationRat_encode, hrq, he', hfresh, freshSourceSentence]
  rw [hcut, hc']
  change (base.stageAtFuel fuel k).bind
    (fun stage => if (X.toLUV n).gt r ∈ stage then some ((X.toLUV n).gt r) else none) =
      some ((X.toLUV n).gt r)
  rw [hs']
  simp [hkLaw]

/-- Every valid upper-bound certificate query of a genuine source eventually passes the
fixed executable checker. -/
theorem certified_above_eventually_checked {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) (X : CertifiedSourceLUVSeq DP)
    (n : ℕ) (r : ℚ) (hr : 1 < (r : ℝ)) :
    ∃ fuel, semanticSourceCheckedLawAtFuel base X.thresholdSchema
      (sourceCutAboveJob n r) fuel = some (∼(X.toLUV n).gt r) := by
  obtain ⟨fe, he⟩ := evaln_decode_sentence_eventually X.emitterCode
    (Nat.pair n (Encodable.encode r)) ((X.toLUV n).gt r) (X.emitter_spec n r)
  obtain ⟨k, hkCode, hkLaw⟩ := X.cut_certificate.above n r hr
  obtain ⟨fc, hc⟩ := Nat.Partrec.Code.evaln_complete.mp hkCode
  obtain ⟨fs, hs⟩ := base.stageAtFuel_complete k
  let fuel := max fe (max fc fs)
  have he' : semanticSourceSentenceAtFuel X.thresholdSchema
      (Nat.pair n (Encodable.encode r)) fuel = some ((X.toLUV n).gt r) := by
    rw [semanticSourceSentenceAtFuel, certified_thresholdSchema_emitterCode]
    obtain ⟨out, hout, hdecode⟩ := Option.bind_eq_some_iff.mp he
    exact Option.bind_eq_some_iff.mpr ⟨out,
      Nat.Partrec.Code.evaln_mono (Nat.le_max_left _ _) hout, hdecode⟩
  have hc' : semanticSourceStageIndexAtFuel X.thresholdSchema
      (sourceCutAboveJob n r) fuel = some k := by
    rw [semanticSourceStageIndexAtFuel, certified_thresholdSchema_certificateCode]
    exact Nat.Partrec.Code.evaln_mono (le_trans (Nat.le_max_left _ _)
      (Nat.le_max_right _ _)) hc
  have hs' : base.stageAtFuel fuel k = some (DP.D k) :=
    base.stageAtFuel_mono (le_trans (Nat.le_max_right _ _)
      (Nat.le_max_right _ _)) hs
  have hrq : 1 < r := by exact_mod_cast hr
  have hfresh : semanticPrimeFreshSentenceB ((X.toLUV n).gt r) = true :=
    (semanticPrimeFreshSentenceB_eq_true _).2 (X.old_language n r)
  refine ⟨fuel, ?_⟩
  rw [semanticSourceCheckedLawAtFuel, if_pos X.thresholdSchema_source]
  have hcut : semanticSourceCutLawAtFuel X.thresholdSchema
      (sourceCutAboveJob n r) fuel = some (∼(X.toLUV n).gt r) := by
    simp [semanticSourceCutLawAtFuel, sourceCutAboveJob,
      decodedQuotationRat_encode, hrq, he', hfresh, freshNegSourceSentence]
  rw [hcut, hc']
  change (base.stageAtFuel fuel k).bind
    (fun stage => if (∼(X.toLUV n).gt r) ∈ stage then some (∼(X.toLUV n).gt r) else none) =
      some (∼(X.toLUV n).gt r)
  rw [hs']
  simp [hkLaw]

/-- Every valid downward-closure certificate query of a genuine source eventually passes
the fixed executable checker. -/
theorem certified_downward_eventually_checked {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) (X : CertifiedSourceLUVSeq DP)
    (n : ℕ) (r s : ℚ) (hrs : r < s) :
    ∃ fuel, semanticSourceCheckedLawAtFuel base X.thresholdSchema
      (sourceCutDownwardJob n r s) fuel =
        some ((X.toLUV n).gt s 🡒 (X.toLUV n).gt r) := by
  obtain ⟨fer, her⟩ := evaln_decode_sentence_eventually X.emitterCode
    (Nat.pair n (Encodable.encode r)) ((X.toLUV n).gt r) (X.emitter_spec n r)
  obtain ⟨fes, hes⟩ := evaln_decode_sentence_eventually X.emitterCode
    (Nat.pair n (Encodable.encode s)) ((X.toLUV n).gt s) (X.emitter_spec n s)
  obtain ⟨k, hkCode, hkLaw⟩ := X.cut_certificate.downward n r s hrs
  obtain ⟨fc, hc⟩ := Nat.Partrec.Code.evaln_complete.mp hkCode
  obtain ⟨fst, hst⟩ := base.stageAtFuel_complete k
  let fuel := max fer (max fes (max fc fst))
  have her' : semanticSourceSentenceAtFuel X.thresholdSchema
      (Nat.pair n (Encodable.encode r)) fuel = some ((X.toLUV n).gt r) := by
    rw [semanticSourceSentenceAtFuel, certified_thresholdSchema_emitterCode]
    obtain ⟨out, hout, hdecode⟩ := Option.bind_eq_some_iff.mp her
    exact Option.bind_eq_some_iff.mpr ⟨out,
      Nat.Partrec.Code.evaln_mono (Nat.le_max_left _ _) hout, hdecode⟩
  have hes' : semanticSourceSentenceAtFuel X.thresholdSchema
      (Nat.pair n (Encodable.encode s)) fuel = some ((X.toLUV n).gt s) := by
    rw [semanticSourceSentenceAtFuel, certified_thresholdSchema_emitterCode]
    obtain ⟨out, hout, hdecode⟩ := Option.bind_eq_some_iff.mp hes
    exact Option.bind_eq_some_iff.mpr ⟨out,
      Nat.Partrec.Code.evaln_mono (le_trans (Nat.le_max_left _ _)
        (Nat.le_max_right _ _)) hout, hdecode⟩
  have hc' : semanticSourceStageIndexAtFuel X.thresholdSchema
      (sourceCutDownwardJob n r s) fuel = some k := by
    rw [semanticSourceStageIndexAtFuel, certified_thresholdSchema_certificateCode]
    exact Nat.Partrec.Code.evaln_mono
      (le_trans (le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
        (Nat.le_max_right _ _)) hc
  have hst' : base.stageAtFuel fuel k = some (DP.D k) :=
    base.stageAtFuel_mono
      (le_trans (le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
        (Nat.le_max_right _ _)) hst
  have hfreshr : semanticPrimeFreshSentenceB ((X.toLUV n).gt r) = true :=
    (semanticPrimeFreshSentenceB_eq_true _).2 (X.old_language n r)
  have hfreshs : semanticPrimeFreshSentenceB ((X.toLUV n).gt s) = true :=
    (semanticPrimeFreshSentenceB_eq_true _).2 (X.old_language n s)
  refine ⟨fuel, ?_⟩
  rw [semanticSourceCheckedLawAtFuel, if_pos X.thresholdSchema_source]
  have hcut : semanticSourceCutLawAtFuel X.thresholdSchema
      (sourceCutDownwardJob n r s) fuel =
        some ((X.toLUV n).gt s 🡒 (X.toLUV n).gt r) := by
    simp [semanticSourceCutLawAtFuel, sourceCutDownwardJob,
      decodedQuotationRat_encode, hrs, her', hes', hfreshr, hfreshs,
      freshImpSourceSentence]
  rw [hcut, hc']
  change (base.stageAtFuel fuel k).bind
    (fun stage => if ((X.toLUV n).gt s 🡒 (X.toLUV n).gt r) ∈ stage then
      some ((X.toLUV n).gt s 🡒 (X.toLUV n).gt r) else none) =
        some ((X.toLUV n).gt s 🡒 (X.toLUV n).gt r)
  rw [hst']
  simp [hkLaw]

/-! ## Finite-prefix admission

The universal product process cannot safely activate an entire schema after finitely
observing an infinite cut certificate.  Instead it activates successively larger finite
query prefixes.  Each prefix checks every source formula for old-language ownership, both
bounds where applicable, and downward closure between every pair of thresholds in the
prefix. -/

/-- Has a fresh decoded source formula for this query appeared by the supplied clock? -/
def semanticSourceFreshSeen (schema n z fuel : ℕ) : Bool :=
  (List.range (fuel + 1)).any fun f =>
    match semanticSourceSentenceAtFuel schema
        (Nat.pair n (Encodable.encode (decodedQuotationRat z))) f with
    | some φ => semanticPrimeFreshSentenceB φ
    | none => false

/-- Has one fully checked cut-law query appeared by the supplied clock? -/
def semanticSourceLawSeen {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) (schema job fuel : ℕ) : Bool :=
  (List.range (fuel + 1)).any fun f =>
    (semanticSourceCheckedLawAtFuel base schema job f).isSome

/-- All executable evidence required to expose query indices at most `prefix`. -/
def semanticSourcePrefixValidAtFuel {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) (schema limit fuel : ℕ) : Bool :=
  (List.range (limit + 1)).all fun n =>
    (List.range (limit + 1)).all fun zr =>
      let r := decodedQuotationRat zr
      semanticSourceFreshSeen schema n zr fuel &&
      (if r < 0 then
        semanticSourceLawSeen base schema (sourceCutBelowJob n r) fuel else true) &&
      (if 1 < r then
        semanticSourceLawSeen base schema (sourceCutAboveJob n r) fuel else true) &&
      (List.range (limit + 1)).all fun zs =>
        let s := decodedQuotationRat zs
        if r < s then
          semanticSourceLawSeen base schema (sourceCutDownwardJob n r s) fuel
        else true

lemma semanticSourceFreshSeen_iff (schema n z fuel : ℕ) :
    semanticSourceFreshSeen schema n z fuel = true ↔
      ∃ f ≤ fuel, ∃ φ,
        semanticSourceSentenceAtFuel schema
          (Nat.pair n (Encodable.encode (decodedQuotationRat z))) f = some φ ∧
        SemanticPrimeFreshSentence φ := by
  rw [semanticSourceFreshSeen, List.any_eq_true]
  simp only [List.mem_range, Nat.lt_add_one_iff]
  constructor
  · rintro ⟨f, hf, h⟩
    cases hemit : semanticSourceSentenceAtFuel schema
        (Nat.pair n (Encodable.encode (decodedQuotationRat z))) f with
    | none => simp [hemit] at h
    | some φ =>
        exact ⟨f, hf, φ, hemit,
          (semanticPrimeFreshSentenceB_eq_true φ).1 (by simpa [hemit] using h)⟩
  · rintro ⟨f, hf, φ, hemit, hfresh⟩
    exact ⟨f, hf, by simp [hemit, (semanticPrimeFreshSentenceB_eq_true φ).2 hfresh]⟩

lemma semanticSourceLawSeen_iff {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) (schema job fuel : ℕ) :
    semanticSourceLawSeen base schema job fuel = true ↔
      ∃ f ≤ fuel, ∃ law,
        semanticSourceCheckedLawAtFuel base schema job f = some law := by
  rw [semanticSourceLawSeen, List.any_eq_true]
  simp only [List.mem_range, Nat.lt_add_one_iff]
  constructor
  · rintro ⟨f, hf, hsome⟩
    cases h : semanticSourceCheckedLawAtFuel base schema job f with
    | none => simp [h] at hsome
    | some law => exact ⟨f, hf, law, h⟩
  · rintro ⟨f, hf, law, hlaw⟩
    exact ⟨f, hf, by simp [hlaw]⟩

/-- Prefix validity exposes freshness for every admitted source query. -/
theorem semanticSourcePrefixValidAtFuel_fresh {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) {schema limit fuel n z : ℕ}
    (hvalid : semanticSourcePrefixValidAtFuel base schema limit fuel = true)
    (hn : n ≤ limit) (hz : z ≤ limit) :
    semanticSourceFreshSeen schema n z fuel = true := by
  rw [semanticSourcePrefixValidAtFuel, List.all_eq_true] at hvalid
  have hnmem : n ∈ List.range (limit + 1) := by simp [hn]
  have hzmem : z ∈ List.range (limit + 1) := by simp [hz]
  have h := List.all_eq_true.mp (hvalid n hnmem) z hzmem
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1

/-- Prefix validity exposes every applicable pairwise downward law. -/
theorem semanticSourcePrefixValidAtFuel_downward {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) {schema limit fuel n zr zs : ℕ}
    (hvalid : semanticSourcePrefixValidAtFuel base schema limit fuel = true)
    (hn : n ≤ limit) (hzr : zr ≤ limit) (hzs : zs ≤ limit)
    (hrs : decodedQuotationRat zr < decodedQuotationRat zs) :
    semanticSourceLawSeen base schema
      (sourceCutDownwardJob n (decodedQuotationRat zr) (decodedQuotationRat zs)) fuel = true := by
  rw [semanticSourcePrefixValidAtFuel, List.all_eq_true] at hvalid
  have hnmem : n ∈ List.range (limit + 1) := by simp [hn]
  have hzrmem : zr ∈ List.range (limit + 1) := by simp [hzr]
  have hzsmem : zs ∈ List.range (limit + 1) := by simp [hzs]
  have h := List.all_eq_true.mp (hvalid n hnmem) zr hzrmem
  simp only [Bool.and_eq_true] at h
  have hlast := h.2
  have hz := List.all_eq_true.mp hlast zs hzsmem
  simpa [hrs] using hz

#print axioms semanticSourceCheckedLawAtFuel_prim
#print axioms semanticSourceCheckedLawAtFuel_mem
#print axioms certified_downward_eventually_checked

end LogicalInduction
