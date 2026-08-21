import LogicalInduction.Construction.Witnesses.PaperCutLawDP
import LogicalInduction.Construction.Witnesses.CertifiedSource
import LogicalInduction.Construction.Witnesses.SemanticQuoteFactor

/-!
# Paper-facing first-order source LUVs

This file turns the old-language first-order boundary into the existing executable
`CertifiedSourceLUVSeq` ABI.  A source supplies an efficient total formula compiler and
old-theory proofs of the three rational-cut laws.  The fixed `paperBaseDP` publishes those
laws, while a generic partial-recursive search extracts the stage program required by the
semantic registry.

No source family occurs in `paperBaseDP` or its computation.
-/

namespace LogicalInduction

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open LO.Propositional

/-! ## A reusable executable stage finder -/

private def sentenceStageGuard {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) (target : ℕ → Sentence)
    (job fuel : ℕ) : Option ℕ :=
  if semanticSentenceSeenAtFuel base (target job) fuel then some fuel else none

private lemma sentenceStageGuard_prim {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) (target : ℕ → Sentence)
    (htarget : Primrec target) :
    Primrec fun p : ℕ × ℕ => sentenceStageGuard base target p.1 p.2 := by
  have hseen : Primrec fun p : ℕ × ℕ =>
      semanticSentenceSeenAtFuel base (target p.1) p.2 :=
    (semanticSentenceSeenAtFuel_prim base).comp
      ((htarget.comp Primrec.fst).pair Primrec.snd)
  exact (Primrec.ite (Primrec.eq.comp hseen (Primrec.const true))
    (Primrec.option_some.comp Primrec.snd)
    (Primrec.const (none : Option ℕ))).of_eq fun p => by
      cases h : semanticSentenceSeenAtFuel base (target p.1) p.2 <;>
        simp [sentenceStageGuard, h]

/-- A program which searches the fixed computation for the requested public sentence. -/
noncomputable def sentenceStageCode {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) (target : ℕ → Sentence)
    (htarget : Primrec target) : Nat.Partrec.Code := by
  have hpart : Partrec fun job =>
      Nat.rfindOpt (sentenceStageGuard base target job) :=
    Partrec.rfindOpt (sentenceStageGuard_prim base target htarget).to₂.to_comp
  exact Classical.choose (Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hpart))

private lemma sentenceStageCode_eval {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) (target : ℕ → Sentence)
    (htarget : Primrec target) :
    Nat.Partrec.Code.eval (sentenceStageCode base target htarget) =
      fun job => Nat.rfindOpt (sentenceStageGuard base target job) := by
  unfold sentenceStageCode
  exact Classical.choose_spec (Nat.Partrec.Code.exists_code.mp
    (Partrec.nat_iff.mp
      (Partrec.rfindOpt (sentenceStageGuard_prim base target htarget).to₂.to_comp)))

/-- Whenever a target sentence occurs in the fixed process, the finder returns a stage
which contains it. -/
lemma sentenceStageCode_complete {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) (target : ℕ → Sentence)
    (htarget : Primrec target) (job : ℕ)
    (hmem : ∃ k, target job ∈ DP.D k) :
    ∃ k, k ∈ (sentenceStageCode base target htarget).eval job ∧
      target job ∈ DP.D k := by
  obtain ⟨stage, hstage⟩ := hmem
  obtain ⟨fuel, hfuel⟩ := semanticSentenceSeenAtFuel_eventually base hstage
  have hdom : (Nat.rfindOpt (sentenceStageGuard base target job)).Dom := by
    rw [Nat.rfindOpt_dom]
    exact ⟨fuel, fuel, by simp [sentenceStageGuard, hfuel]⟩
  let out := (Nat.rfindOpt (sentenceStageGuard base target job)).get hdom
  have hout : out ∈ Nat.rfindOpt (sentenceStageGuard base target job) :=
    Part.get_mem hdom
  obtain ⟨foundFuel, hfound⟩ := Nat.rfindOpt_spec hout
  have hfoundEq : foundFuel = out := by
    have hp : semanticSentenceSeenAtFuel base (target job) foundFuel = true ∧
        foundFuel = out := by
      simpa [sentenceStageGuard] using hfound
    exact hp.2
  have hseen : semanticSentenceSeenAtFuel base (target job) foundFuel = true := by
    have hp : semanticSentenceSeenAtFuel base (target job) foundFuel = true ∧
        foundFuel = out := by
      simpa [sentenceStageGuard] using hfound
    exact hp.1
  obtain ⟨k, hk, stage', hstage', htargetMem⟩ :=
    (semanticSentenceSeenAtFuel_iff base (target job) foundFuel).1 hseen
  refine ⟨foundFuel, ?_, DP.mono_le hk (base.stageAtFuel_sound hstage' ▸ htargetMem)⟩
  rw [sentenceStageCode_eval]
  rw [hfoundEq]
  exact hout

/-! ## Faithful paper source object -/

variable (T : ArithmeticTheory)

/-- A paper-facing e.c. sequence of genuine `[0,1]` LUVs.

The formula family lives in the old first-order language by type.  `formulaCode` is the
total efficient threshold compiler.  The remaining fields are object-level proofs in the
old theory, exactly the consequences of the paper's unique `[0,1]`-valuedness premise
needed by the propositional LUV ABI. -/
structure PaperSourceLUVSeq (T : ArithmeticTheory) [T.Δ₁] where
  thresholdFormula : ℕ → ℚ → ArithmeticProposition
  formulaCode : ℕ → ℕ
  formulaCode_prim : Primrec formulaCode
  formulaCode_spec : ∀ n r,
    formulaCode (Nat.pair n (Encodable.encode r)) =
      Encodable.encode (thresholdFormula n r)
  threshold_codes : LUV.RpnThresholdCodeSeq
    (fun n => ⟨fun r => paperPrimeDecompose (thresholdFormula n r)⟩)
  below_provable : ∀ (n : ℕ) (r : ℚ), (r : ℝ) < 0 →
    Bootstrapping.Provable T (Encodable.encode (thresholdFormula n r))
  above_provable : ∀ (n : ℕ) (r : ℚ), 1 < (r : ℝ) →
    Bootstrapping.Provable T (Encodable.encode (∼thresholdFormula n r))
  downward_provable : ∀ (n : ℕ) (r s : ℚ), r < s →
    Bootstrapping.Provable T
      (Encodable.encode (thresholdFormula n s 🡒 thresholdFormula n r))

namespace PaperSourceLUVSeq

variable {T : ArithmeticTheory} [T.Δ₁]

def toLUV (X : PaperSourceLUVSeq T) : ℕ → LUV :=
  fun n => ⟨fun r => paperPrimeDecompose (X.thresholdFormula n r)⟩

@[simp] lemma toLUV_gt (X : PaperSourceLUVSeq T) (n : ℕ) (r : ℚ) :
    (X.toLUV n).gt r = paperPrimeDecompose (X.thresholdFormula n r) := rfl

lemma old_language (X : PaperSourceLUVSeq T) : SemanticPrimeFreshLUVSeq X.toLUV := by
  intro n r
  exact paperPrimeDecompose_semanticPrimeFresh _

def publicSentenceCode (X : PaperSourceLUVSeq T) (job : ℕ) : ℕ :=
  paperPrimeDecomposeCode (X.formulaCode job)

lemma publicSentenceCode_prim (X : PaperSourceLUVSeq T) :
    Primrec X.publicSentenceCode :=
  paperPrimeDecomposeCode_prim.comp X.formulaCode_prim

noncomputable def publicSentence (X : PaperSourceLUVSeq T) (job : ℕ) : Sentence :=
  (Encodable.decode (α := Sentence) (X.publicSentenceCode job)).getD ⊤

lemma publicSentence_prim (X : PaperSourceLUVSeq T) :
    Primrec X.publicSentence := by
  exact (Primrec.option_getD.comp
    (Primrec.decode.comp X.publicSentenceCode_prim)
    (Primrec.const (⊤ : Sentence))).of_eq fun _ => rfl

@[simp] lemma publicSentence_spec (X : PaperSourceLUVSeq T) (n : ℕ) (r : ℚ) :
    X.publicSentence (Nat.pair n (Encodable.encode r)) = (X.toLUV n).gt r := by
  simp [publicSentence, publicSentenceCode, X.formulaCode_spec,
    paperPrimeDecomposeCode_spec]

noncomputable def emitterCode (X : PaperSourceLUVSeq T) : Nat.Partrec.Code := by
  exact Classical.choose (Nat.Partrec.Code.exists_code.mp
    (Nat.Partrec.of_primrec (Primrec.nat_iff.mp X.publicSentenceCode_prim)))

lemma emitterCode_spec (X : PaperSourceLUVSeq T) (n : ℕ) (r : ℚ) :
    Encodable.encode ((X.toLUV n).gt r) ∈
      X.emitterCode.eval (Nat.pair n (Encodable.encode r)) := by
  have hcode := Classical.choose_spec (Nat.Partrec.Code.exists_code.mp
    (Nat.Partrec.of_primrec (Primrec.nat_iff.mp X.publicSentenceCode_prim)))
  rw [emitterCode, hcode]
  simp [publicSentenceCode, X.formulaCode_spec, paperPrimeDecomposeCode_spec]

private noncomputable def cutTarget (X : PaperSourceLUVSeq T) (job : ℕ) : Sentence :=
  let payload := job.unpair.2
  let n := payload.unpair.1
  if job.unpair.1 = 0 then
    X.publicSentence payload
  else if job.unpair.1 = 1 then
    ∼X.publicSentence payload
  else if job.unpair.1 = 2 then
    let rCode := payload.unpair.2.unpair.1
    let sCode := payload.unpair.2.unpair.2
    let rJob := Nat.pair n rCode
    let sJob := Nat.pair n sCode
    X.publicSentence sJob 🡒 X.publicSentence rJob
  else ⊤

private lemma cutTarget_prim (X : PaperSourceLUVSeq T) :
    Primrec X.cutTarget := by
  let htag : Primrec fun job : ℕ => job.unpair.1 := Primrec.fst.comp Primrec.unpair
  let hpayload : Primrec fun job : ℕ => job.unpair.2 := Primrec.snd.comp Primrec.unpair
  let hn : Primrec fun job : ℕ => job.unpair.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp hpayload)
  let hrCode : Primrec fun job : ℕ => job.unpair.2.unpair.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp
      (Primrec.snd.comp (Primrec.unpair.comp hpayload)))
  let hsCode : Primrec fun job : ℕ => job.unpair.2.unpair.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp
      (Primrec.snd.comp (Primrec.unpair.comp hpayload)))
  have htagEq (k : ℕ) : PrimrecPred fun job : ℕ => job.unpair.1 = k :=
    Primrec.eq.comp htag (Primrec.const k)
  have hbase : Primrec fun job : ℕ => X.publicSentence job.unpair.2 :=
    X.publicSentence_prim.comp hpayload
  have hneg : Primrec fun job : ℕ => ∼X.publicSentence job.unpair.2 := by
    apply Primrec.encode_iff.mp
    exact (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 2)
      (Primrec₂.natPair.comp (Primrec.encode.comp hbase)
        (Primrec.const (Encodable.encode (⊥ : Sentence)))))).of_eq fun _ => rfl
  have hrJob : Primrec fun job : ℕ => Nat.pair job.unpair.2.unpair.1
      job.unpair.2.unpair.2.unpair.1 := Primrec₂.natPair.comp hn hrCode
  have hsJob : Primrec fun job : ℕ => Nat.pair job.unpair.2.unpair.1
      job.unpair.2.unpair.2.unpair.2 := Primrec₂.natPair.comp hn hsCode
  have himp : Primrec fun job : ℕ =>
      X.publicSentence (Nat.pair job.unpair.2.unpair.1 job.unpair.2.unpair.2.unpair.2) 🡒
        X.publicSentence (Nat.pair job.unpair.2.unpair.1
          job.unpair.2.unpair.2.unpair.1) := by
    apply Primrec.encode_iff.mp
    exact (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 2)
      (Primrec₂.natPair.comp
        (Primrec.encode.comp (X.publicSentence_prim.comp hsJob))
        (Primrec.encode.comp (X.publicSentence_prim.comp hrJob))))).of_eq fun _ => rfl
  exact (Primrec.ite (htagEq 0) hbase
    (Primrec.ite (htagEq 1) hneg
      (Primrec.ite (htagEq 2) himp (Primrec.const (⊤ : Sentence))))).of_eq fun _ => rfl

private lemma cutTarget_below (X : PaperSourceLUVSeq T) (n : ℕ) (r : ℚ) :
    X.cutTarget (sourceCutBelowJob n r) = (X.toLUV n).gt r := by
  simp [cutTarget, sourceCutBelowJob, publicSentence_spec]

private lemma cutTarget_above (X : PaperSourceLUVSeq T) (n : ℕ) (r : ℚ) :
    X.cutTarget (sourceCutAboveJob n r) = ∼(X.toLUV n).gt r := by
  simp [cutTarget, sourceCutAboveJob, publicSentence_spec]

private lemma cutTarget_downward (X : PaperSourceLUVSeq T) (n : ℕ) (r s : ℚ) :
    X.cutTarget (sourceCutDownwardJob n r s) =
      ((X.toLUV n).gt s 🡒 (X.toLUV n).gt r) := by
  simp [cutTarget, sourceCutDownwardJob, publicSentence_spec]

private lemma mem_paperBase_theory [𝗜𝚺₁ ⪯ T]
    [T.SoundOnHierarchy 𝚺 1] {φ : Sentence}
    (h : ∃ k, φ ∈ (paperTheoryDP T).D k) :
    ∃ k, φ ∈ (paperBaseDP T).D k := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, by simp [paperBaseDP, theoremPaperDP, hk]⟩

private lemma mem_paperBase_cut [𝗜𝚺₁ ⪯ T]
    [T.SoundOnHierarchy 𝚺 1] {φ : Sentence}
    (h : ∃ k, φ ∈ (paperCutLawDP T).D k) :
    ∃ k, φ ∈ (paperBaseDP T).D k := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, by simp [paperBaseDP, hk]⟩

noncomputable def cutCertificate [𝗜𝚺₁ ⪯ T]
    [T.SoundOnHierarchy 𝚺 1] (X : PaperSourceLUVSeq T) :
    SourceCutCertificate (paperBaseDP T) X.toLUV where
  stageCode := sentenceStageCode (paperBaseDPComputation T) X.cutTarget
    X.cutTarget_prim
  below n r hr := by
    have hmem : ∃ k, X.cutTarget (sourceCutBelowJob n r) ∈
        (paperBaseDP T).D k := by
      rw [X.cutTarget_below]
      exact mem_paperBase_theory
        (paperTheoryDP_covers_provable T _ (X.below_provable n r hr))
    obtain ⟨k, hkcode, hk⟩ := sentenceStageCode_complete
      (paperBaseDPComputation T) X.cutTarget X.cutTarget_prim
      (sourceCutBelowJob n r) hmem
    exact ⟨k, hkcode, X.cutTarget_below n r ▸ hk⟩
  above n r hr := by
    have hmem : ∃ k, X.cutTarget (sourceCutAboveJob n r) ∈
        (paperBaseDP T).D k := by
      rw [X.cutTarget_above]
      exact mem_paperBase_cut
        (paperCutLawDP_covers_upper T _ (X.above_provable n r hr))
    obtain ⟨k, hkcode, hk⟩ := sentenceStageCode_complete
      (paperBaseDPComputation T) X.cutTarget X.cutTarget_prim
      (sourceCutAboveJob n r) hmem
    exact ⟨k, hkcode, X.cutTarget_above n r ▸ hk⟩
  downward n r s hrs := by
    have hmem : ∃ k, X.cutTarget (sourceCutDownwardJob n r s) ∈
        (paperBaseDP T).D k := by
      rw [X.cutTarget_downward]
      exact mem_paperBase_cut
        (paperCutLawDP_covers_downward T _ _ (X.downward_provable n r s hrs))
    obtain ⟨k, hkcode, hk⟩ := sentenceStageCode_complete
      (paperBaseDPComputation T) X.cutTarget X.cutTarget_prim
      (sourceCutDownwardJob n r s) hmem
    exact ⟨k, hkcode, X.cutTarget_downward n r s ▸ hk⟩

/-- Compilation from the paper-facing old-language source object to the existing checked
semantic-registry ABI. -/
noncomputable def toCertified [𝗜𝚺₁ ⪯ T]
    [T.SoundOnHierarchy 𝚺 1] (X : PaperSourceLUVSeq T) :
    CertifiedSourceLUVSeq (paperBaseDP T) where
  toLUV := X.toLUV
  threshold_codes := X.threshold_codes
  emitterCode := X.emitterCode
  emitter_spec := X.emitterCode_spec
  old_language := X.old_language
  cut_certificate := X.cutCertificate

lemma source_valued [𝗜𝚺₁ ⪯ T]
    [T.SoundOnHierarchy 𝚺 1] (X : PaperSourceLUVSeq T)
    (n : ℕ) (v : PCWorld) (hv : v.ConsistentWithTheory (paperBaseDP T)) :
    ∃ x : ℝ, v.ValuesAt (X.toLUV n) x :=
  X.toCertified.source_valued n v hv

#print axioms sentenceStageCode_complete
#print axioms PaperSourceLUVSeq.toCertified
#print axioms PaperSourceLUVSeq.source_valued

end PaperSourceLUVSeq

end LogicalInduction
