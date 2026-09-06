import LogicalInduction.Construction.SemanticExtension.Product
import LogicalInduction.Framework.Expectations

/-!
# Proof-carrying source admission: the certificate, its checker and the universal interpreter

The tag-`0` half of the semantic extension: what a source LUV family must carry to be
admitted as a product factor, the object-level test that recognizes such a package without
inspecting its Lean proofs, and the single fixed universal process that interprets what an
admitted emitter writes.  Construction machinery for `thm:ccee` (tex:2068) at an arbitrary
e.c. source family; no paper node of its own.

## The certificate boundary

The paper's first-order definition of a `[0,1]` LUV supplies more than efficient threshold
emission: in every completed theory world its rational thresholds form a bounded downward
cut.  `RationalCutAt` isolates exactly that semantic payload at the existing propositional
ABI, and `RationalCutAt.exists_valuesAt` proves the payload sufficient to recover the
repository's `PCWorld.ValuesAt` interface, including genuinely undecided cuts.

A caller-supplied Lean proof of `RationalCutAt` is not an acceptable fixed-process
certificate, because the deductive process cannot inspect a proof chosen after the process;
that is why `SourceCutCertificate` carries a *program* instead, and why the three soundness
clauses are stated against every completed base-theory world.

* Job codings `sourceCutBelowJob` / `sourceCutAboveJob` / `sourceCutDownwardJob` pack the
  certificate queries; `SourceCutCertificate.rationalCutAt` and `.valuesAt` run that payload
  back through `RationalCutAt.exists_valuesAt`, so a checked certificate discharges the
  `source_valued` premise of closed CCEE.
* `CertifiedSourceLUVSeq DP` is the paper-facing source package: efficient threshold codes, a
  total emitter program, pre-extension vocabulary ownership (`SemanticPrimeFreshLUVSeq`), and
  the cut certificate.  Unlike `PresentedLUVSeq` it assumes no semantic-prime reflection.
* `thresholdSchema` gives the compact self-describing schema number that stores both programs,
  and `toPresented` wraps the family under it as a `PresentedLUVSeq`, using the handle family
  `semanticHandleLUVSeq` and its certificate from
  `Construction/SemanticExtension/Prime.lean`.
* `semanticFreshIncreasing_no_cutCertificate` is the admission test's negative side: the
  malformed fresh increasing family of `Construction/SemanticExtension/Product.lean` carries no cut
  certificate over any non-vacuous base process.

## The executable registry check

The object-level admission test runs those programs under bounded fuel.  The self-describing
schema is a tag-`0` semantic schema naming two `Nat.Partrec.Code`s,
`semanticSourceEmitterCode` (an arbitrary rational threshold emitter) and
`semanticSourceCertificateCode` (a cut-certificate stage finder).  Bounded execution is
`semanticSourceSentenceAtFuel`, `semanticSourceStageIndexAtFuel` and the decidable
old-language ownership test `semanticPrimeFreshSentenceB` with its
`SemanticPrimeFreshSentence` characterization.  The checker itself is
`semanticSourceCutLawAtFuel`, which reconstructs the requested cut law (below, above or
downward), and `semanticSourceCheckedLawAtFuel`, which additionally demands that the
certificate name a decoded base stage actually containing it; soundness is
`semanticSourceCheckedLawAtFuel_mem` / `_source` / `semanticSourceCheckedDownward_spec`, and
completeness for genuine certified packages is the
`certified_{below,above,downward}_eventually_checked` family.

Admission is by successively larger finite query prefixes, never by finitely observing an
infinite certificate: `semanticSourcePrefixValidAtFuel` with its `_prim` / `_mono` / `_fresh`
/ `_downward` accessors, and `certifiedSourcePrefix_eventually_valid` for completeness.
Timeouts, malformed output, invalid queries and non-source schemas all return `none`, which
is what makes the gate safe to run universally over program codes.

## The universal interpreter

`semanticSourceDefinitionJob`, `semanticSourceDefSentence` (one bounded definition clause),
`semanticSourceStageList`, `semanticSourceDP` and the canonical extension world
`semanticSourceExtensionWorld` form the single fixed universal source process.  Its main
results are `semanticSourceDP_computable`; `semanticSourceDP_hworld`, which exhibits an
explicit completed world over *every* base world, so no consistency premise hides in source
reflection; `semanticSourceSentenceAtFuel_reflected`; and the two transport lemmas
`certifiedSource_threshold_reflected` and `certifiedSource_valuesAt_iff`.

The separation of concerns it rests on: the process is a conservative definitional
interpreter for old-language emitter output, and nothing more.  Malformed but fresh emitters
cannot make it inconsistent, because every activated tag-`0` leaf is merely identified with
one old-language sentence.

## A design fact about the two negation ABIs

Recorded here because it constrains what an old-language emitter may assume about the
sentences it interprets.  Prime decomposition (`paperPrimeDecompose`) preserves truth, but
FAF's public negation is an implication into `⊥`, so it does **not** commute with first-order
NNF negation by definitional equality: `paperPublicNegCode (paperPrimeDecomposeCode c)` is not
the decomposition of the first-order negation code of `c`, and likewise for implication.  A
process that wants the public negation and the public implication of decomposed sentences must
therefore publish them *literally*, from an r.e. gate that tests `T`-provability of the
corresponding first-order `∼φ` or `upper 🡒 lower`.  The gap is an artifact of the two negation
ABIs, not of the arithmetic: it costs an extra published clause per event, and nothing else in
this development depends on closing it.

The results here are consumed by `Construction/SemanticExtension/LanguageCopy.lean` and
`Construction/SemanticExtension/Registry.lean`.
-/

namespace LogicalInduction

/-! ## Executable cut certificates

The certificate is code-bearing.  `stageCode` is a repository program which, for each
requested cut law, returns a stage of the already-fixed base deductive process containing
that law.  A universal source registry runs this code and checks finite-stage membership; it
does not inspect the accompanying Lean correctness proof.
-/

/-- Packed certificate query for the lower-bound law at source index `n`, threshold `r`. -/
def sourceCutBelowJob (n : ℕ) (r : ℚ) : ℕ :=
  Nat.pair 0 (Nat.pair n (Encodable.encode r))

/-- Packed certificate query for the upper-bound law at source index `n`, threshold `r`. -/
def sourceCutAboveJob (n : ℕ) (r : ℚ) : ℕ :=
  Nat.pair 1 (Nat.pair n (Encodable.encode r))

/-- Packed certificate query for downward closure from `s` to `r`. -/
def sourceCutDownwardJob (n : ℕ) (r s : ℚ) : ℕ :=
  Nat.pair 2 (Nat.pair n (Nat.pair (Encodable.encode r) (Encodable.encode s)))

/-- Object-level evidence that the base process proves all rational-cut laws for `X`.

The returned stage is executable data.  The three soundness fields are metatheoretic
verification of that data, analogous to the `code_spec` field of the repository's other
certified computations. -/
structure SourceCutCertificate (DP : DeductiveProcess) (X : ℕ → LUV) where
  stageCode : Nat.Partrec.Code
  below : ∀ (n : ℕ) (r : ℚ), (r : ℝ) < 0 →
    ∃ k, k ∈ stageCode.eval (sourceCutBelowJob n r) ∧ (X n).gt r ∈ DP.D k
  above : ∀ (n : ℕ) (r : ℚ), 1 < (r : ℝ) →
    ∃ k, k ∈ stageCode.eval (sourceCutAboveJob n r) ∧ (∼(X n).gt r) ∈ DP.D k
  downward : ∀ (n : ℕ) (r s : ℚ), r < s →
    ∃ k, k ∈ stageCode.eval (sourceCutDownwardJob n r s) ∧
      ((X n).gt s 🡒 (X n).gt r) ∈ DP.D k

namespace SourceCutCertificate

variable {DP : DeductiveProcess} {X : ℕ → LUV}

/-- A checked executable certificate makes every completed base-theory world see a bounded
downward cut. -/
lemma rationalCutAt (C : SourceCutCertificate DP X) {v : PCWorld}
    (hv : v.ConsistentWithTheory DP) (n : ℕ) : v.RationalCutAt (X n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    obtain ⟨k, _, hk⟩ := C.below n r hr
    exact hv k _ hk
  · intro r hr
    obtain ⟨k, _, hk⟩ := C.above n r hr
    exact (PCWorld.holds_neg v _).mp (hv k _ hk)
  · intro r s hrs hs
    obtain ⟨k, _, hk⟩ := C.downward n r s hrs
    exact (hv k _ hk) hs

/-- Consequently executable cut certification discharges the actual `source_valued`
premise used by closed CCEE. -/
lemma valuesAt (C : SourceCutCertificate DP X) {v : PCWorld}
    (hv : v.ConsistentWithTheory DP) (n : ℕ) : ∃ x : ℝ, v.ValuesAt (X n) x :=
  (C.rationalCutAt hv n).exists_valuesAt

end SourceCutCertificate

/-! ## Certified source LUV sequences -/

/-- The local paper-facing source representation at the current propositional ABI.

It retains efficient emission, carries the executable cut proof program, and records
pre-extension vocabulary ownership.  The latter is a theorem about the emitted syntax;
the universal registry must enforce it by decoding the emitter output before activation.
Unlike `PresentedLUVSeq`, this object does not assume semantic-prime reflection. -/
structure CertifiedSourceLUVSeq (DP : DeductiveProcess) where
  toLUV : ℕ → LUV
  threshold_codes : LUV.RpnThresholdCodeSeq toLUV
  /-- Total compiler for arbitrary rational threshold queries.  The paper supplies this by
  syntactically substituting the rational into the e.c.-emitted one-variable LUV formula;
  `RpnThresholdCodeSeq` separately certifies polynomial emission on the expectation grids. -/
  emitterCode : Nat.Partrec.Code
  emitter_spec : ∀ (n : ℕ) (r : ℚ),
    Encodable.encode ((toLUV n).gt r) ∈
      emitterCode.eval (Nat.pair n (Encodable.encode r))
  old_language : SemanticPrimeFreshLUVSeq toLUV
  cut_certificate : SourceCutCertificate DP toLUV

namespace CertifiedSourceLUVSeq

variable {DP : DeductiveProcess}

/-- The faithful source object internally supplies completed-world valuedness. -/
lemma source_valued (X : CertifiedSourceLUVSeq DP) (n : ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory DP) : ∃ x : ℝ, v.ValuesAt (X.toLUV n) x :=
  X.cut_certificate.valuesAt hv n

/-- The self-describing source schema stores both executable programs: efficient threshold
emission and cut-certificate stage lookup. -/
noncomputable def thresholdSchema (X : CertifiedSourceLUVSeq DP) : ℕ :=
  semanticEmitterSchema (Nat.pair
    (Encodable.encode X.emitterCode)
    (Encodable.encode X.cut_certificate.stageCode))

@[simp] lemma thresholdSchema_source (X : CertifiedSourceLUVSeq DP) :
    X.thresholdSchema.unpair.1 = 0 := by
  simp [thresholdSchema]

/-- Canonical compact wrapper.  Reflection is deliberately outside this object's scope: it
is the business of the universal verifier and process below. -/
noncomputable def toPresented (X : CertifiedSourceLUVSeq DP) : PresentedLUVSeq where
  thresholdSchema := X.thresholdSchema
  source_schema := X.thresholdSchema_source
  toLUV := semanticHandleLUVSeq X.thresholdSchema
  threshold_codes := semanticHandleLUVSeq_rpnThresholdCodeSeq X.thresholdSchema
  threshold_named := fun _ _ => rfl

@[simp] lemma toPresented_gt (X : CertifiedSourceLUVSeq DP) (n : ℕ) (r : ℚ) :
    ((X.toPresented.toLUV n).gt r) =
      semanticPrimeSentence X.thresholdSchema (Nat.pair n (Encodable.encode r)) := rfl

end CertifiedSourceLUVSeq

/-! ## Negative admission test -/

/-- The malformed fresh increasing family cannot carry an executable cut certificate for
any non-vacuous base process.  This is the registry-level rejection counterpart of
`semanticFreshIncreasing_not_jointly_reflected`. -/
lemma semanticFreshIncreasing_no_cutCertificate (DP : DeductiveProcess)
    (hworld : ∃ v : PCWorld, v.ConsistentWithTheory DP) :
    SourceCutCertificate DP semanticFreshIncreasingLUVSeq → False := by
  intro C
  obtain ⟨v, hv⟩ := hworld
  have hcut := C.rationalCutAt hv 0
  have hone : v.Holds ((semanticFreshIncreasingLUVSeq 0).gt 1) := by
    simp [semanticFreshIncreasingLUVSeq_gt, PCWorld.Holds,
      LO.Propositional.Formula.Boolean.val]
  have hzero := hcut.downward 0 1 (by norm_num) hone
  simpa [semanticFreshIncreasingLUVSeq_gt, PCWorld.Holds,
    LO.Propositional.Formula.Boolean.val] using hzero

end LogicalInduction

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

/-! ## Primitive recursiveness of the bounded operations

Stated separately from the verifier so that `semanticSourceDP`'s computability proof reuses
them without unfolding it. -/

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

lemma freshImpSourceSentence_eq_some_of_fresh {φr φs : Sentence}
    (hφr : SemanticPrimeFreshSentence φr)
    (hφs : SemanticPrimeFreshSentence φs) :
    freshImpSourceSentence φr φs = some (φs 🡒 φr) := by
  simp [freshImpSourceSentence, (semanticPrimeFreshSentenceB_eq_true φr).2 hφr,
    (semanticPrimeFreshSentenceB_eq_true φs).2 hφs]

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

/-! ## Reconstructing a cut law -/

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

/-- Decode a successful raw downward-law reconstruction, independently of how the law
will later be certified. -/
lemma semanticSourceCutLawAtFuel_downward_spec {schema fuel n : ℕ} {r s : ℚ}
    {law : Sentence} (hrs : r < s)
    (h : semanticSourceCutLawAtFuel schema
      (sourceCutDownwardJob n r s) fuel = some law) :
    ∃ φr φs,
      semanticSourceSentenceAtFuel schema
        (Nat.pair n (Encodable.encode r)) fuel = some φr ∧
      semanticSourceSentenceAtFuel schema
        (Nat.pair n (Encodable.encode s)) fuel = some φs ∧
      SemanticPrimeFreshSentence φr ∧ SemanticPrimeFreshSentence φs ∧
      law = (φs 🡒 φr) := by
  unfold semanticSourceCutLawAtFuel at h
  simp only [sourceCutDownwardJob, Nat.unpair_pair,
    if_neg (by decide : ¬(2 : ℕ) = 0), if_neg (by decide : ¬(2 : ℕ) = 1),
    decodedQuotationRat_encode, if_pos hrs] at h
  obtain ⟨φr, hφr, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨φs, hφs, h⟩ := Option.bind_eq_some_iff.mp h
  unfold freshImpSourceSentence at h
  by_cases hfr : semanticPrimeFreshSentenceB φr = true <;>
    by_cases hfs : semanticPrimeFreshSentenceB φs = true <;>
    simp [hfr, hfs] at h
  subst law
  exact ⟨φr, φs, hφr, hφs,
    (semanticPrimeFreshSentenceB_eq_true φr).1 hfr,
    (semanticPrimeFreshSentenceB_eq_true φs).1 hfs, rfl⟩

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

/-! ## The full admission check -/

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
lemma semanticSourceCheckedLawAtFuel_prim {DP : DeductiveProcess}
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
lemma semanticSourceCheckedLawAtFuel_mem {DP : DeductiveProcess}
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
lemma semanticSourceCheckedLawAtFuel_source {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) {schema job fuel : ℕ} {law : Sentence}
    (h : semanticSourceCheckedLawAtFuel base schema job fuel = some law) :
    schema.unpair.1 = 0 := by
  simp only [semanticSourceCheckedLawAtFuel] at h
  split at h
  · assumption
  · contradiction

/-- A successful downward-law check exposes the two uniquely emitted fresh formulas and
the exact implication checked against the base process. -/
lemma semanticSourceCheckedDownward_spec {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) {schema fuel n : ℕ} {r s : ℚ}
    {law : Sentence} (hrs : r < s)
    (h : semanticSourceCheckedLawAtFuel base schema
      (sourceCutDownwardJob n r s) fuel = some law) :
    ∃ φr φs,
      semanticSourceSentenceAtFuel schema
        (Nat.pair n (Encodable.encode r)) fuel = some φr ∧
      semanticSourceSentenceAtFuel schema
        (Nat.pair n (Encodable.encode s)) fuel = some φs ∧
      SemanticPrimeFreshSentence φr ∧ SemanticPrimeFreshSentence φs ∧
      law = (φs 🡒 φr) := by
  have hsource := semanticSourceCheckedLawAtFuel_source base h
  unfold semanticSourceCheckedLawAtFuel at h
  rw [if_pos hsource] at h
  obtain ⟨law', hcut, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨stageIndex, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨stage, _, h⟩ := Option.bind_eq_some_iff.mp h
  split at h <;> try contradiction
  simp only [Option.some.injEq] at h
  subst law'
  unfold semanticSourceCutLawAtFuel at hcut
  simp only [sourceCutDownwardJob, Nat.unpair_pair, if_neg (by decide : ¬(2 : ℕ) = 0),
    if_neg (by decide : ¬(2 : ℕ) = 1), if_pos rfl,
    decodedQuotationRat_encode, if_pos hrs] at hcut
  obtain ⟨φr, hφr, hcut⟩ := Option.bind_eq_some_iff.mp hcut
  obtain ⟨φs, hφs, hcut⟩ := Option.bind_eq_some_iff.mp hcut
  unfold freshImpSourceSentence at hcut
  by_cases hfr : semanticPrimeFreshSentenceB φr = true <;>
    by_cases hfs : semanticPrimeFreshSentenceB φs = true <;>
    simp [hfr, hfs] at hcut
  subst law
  exact ⟨φr, φs, hφr, hφs,
    (semanticPrimeFreshSentenceB_eq_true φr).1 hfr,
    (semanticPrimeFreshSentenceB_eq_true φs).1 hfs, rfl⟩

/-! ## Completeness for genuine certified packages -/

/-- A program that converges to the code of a sentence decodes to that sentence at some
finite fuel. -/
lemma evaln_decode_sentence_eventually (code : Nat.Partrec.Code)
    (input : ℕ) (φ : Sentence) (h : Encodable.encode φ ∈ code.eval input) :
    ∃ fuel, (code.evaln fuel input).bind (Encodable.decode (α := Sentence)) = some φ := by
  obtain ⟨fuel, hfuel⟩ := Nat.Partrec.Code.evaln_complete.mp h
  refine ⟨fuel, ?_⟩
  rw [show code.evaln fuel input = some (Encodable.encode φ) from hfuel]
  simp

/-- Every valid lower-bound certificate query of a genuine source eventually passes the
fixed executable checker. -/
lemma certified_below_eventually_checked {DP : DeductiveProcess}
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
lemma certified_above_eventually_checked {DP : DeductiveProcess}
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
lemma certified_downward_eventually_checked {DP : DeductiveProcess}
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

/-- Pairwise downward checks for one source index and one left threshold. -/
def semanticSourceDownwardPrefixValidAtFuel {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP)
    (schema limit fuel n zr : ℕ) : Bool :=
  (List.range (limit + 1)).all fun zs =>
    let r := decodedQuotationRat zr
    let s := decodedQuotationRat zs
    if r < s then
      semanticSourceLawSeen base schema (sourceCutDownwardJob n r s) fuel
    else true

/-- Freshness, bounds, and all downward checks for one threshold query. -/
def semanticSourceThresholdPrefixValidAtFuel {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP)
    (schema limit fuel n zr : ℕ) : Bool :=
  let r := decodedQuotationRat zr
  semanticSourceFreshSeen schema n zr fuel &&
  (if r < 0 then
    semanticSourceLawSeen base schema (sourceCutBelowJob n r) fuel else true) &&
  (if 1 < r then
    semanticSourceLawSeen base schema (sourceCutAboveJob n r) fuel else true) &&
  semanticSourceDownwardPrefixValidAtFuel base schema limit fuel n zr

/-- All executable evidence required to expose query indices at most `limit`. -/
def semanticSourcePrefixValidAtFuel {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) (schema limit fuel : ℕ) : Bool :=
  (List.range (limit + 1)).all fun n =>
    (List.range (limit + 1)).all fun zr =>
      semanticSourceThresholdPrefixValidAtFuel base schema limit fuel n zr

/-- The bounded-search `Primrec` combinator: a disjunction over an inclusive index range
whose bound and test are primitive recursive is primitive recursive. -/
lemma listRangeAny_prim {α : Type} [Primcodable α]
    {bound : α → ℕ} {test : α → ℕ → Bool}
    (hbound : Primrec bound) (htest : Primrec₂ test) :
    Primrec fun a => (List.range (bound a + 1)).any (test a) := by
  have hrange : Primrec fun a => List.range (bound a + 1) :=
    Primrec.list_range.comp
      (Primrec.nat_add.comp hbound (Primrec.const 1))
  have hstep : Primrec₂ fun (a : α) (q : ℕ × Bool) => test a q.1 || q.2 :=
    (Primrec.dom_bool₂ (· || ·)).comp₂
      (htest.comp₂ Primrec₂.left (Primrec.fst.comp₂ Primrec₂.right))
      (Primrec.snd.comp₂ Primrec₂.right)
  exact (Primrec.list_foldr hrange (Primrec.const false) hstep).of_eq fun a => by
    induction List.range (bound a + 1) with
    | nil => rfl
    | cons x xs ih => simp [List.any, ih]

/-- The bounded-check `Primrec` combinator: the conjunction counterpart of
`listRangeAny_prim`. -/
lemma listRangeAll_prim {α : Type} [Primcodable α]
    {bound : α → ℕ} {test : α → ℕ → Bool}
    (hbound : Primrec bound) (htest : Primrec₂ test) :
    Primrec fun a => (List.range (bound a + 1)).all (test a) := by
  have hrange : Primrec fun a => List.range (bound a + 1) :=
    Primrec.list_range.comp
      (Primrec.nat_add.comp hbound (Primrec.const 1))
  have hstep : Primrec₂ fun (a : α) (q : ℕ × Bool) => test a q.1 && q.2 :=
    (Primrec.dom_bool₂ (· && ·)).comp₂
      (htest.comp₂ Primrec₂.left (Primrec.fst.comp₂ Primrec₂.right))
      (Primrec.snd.comp₂ Primrec₂.right)
  exact (Primrec.list_foldr hrange (Primrec.const true) hstep).of_eq fun a => by
    induction List.range (bound a + 1) with
    | nil => rfl
    | cons x xs ih => simp [List.all, ih]

lemma semanticSourceFreshSeen_prim : Primrec fun p : ((ℕ × ℕ) × ℕ) × ℕ =>
    semanticSourceFreshSeen p.1.1.1 p.1.1.2 p.1.2 p.2 := by
  let P := ((ℕ × ℕ) × ℕ) × ℕ
  have hschema : Primrec fun p : P => p.1.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hn : Primrec fun p : P => p.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hz : Primrec fun p : P => p.1.2 := Primrec.snd.comp Primrec.fst
  have hr : Primrec fun p : P => decodedQuotationRat p.1.2 :=
    decodedQuotationRat_prim.comp hz
  have hinput : Primrec fun p : P =>
      Nat.pair p.1.1.2 (Encodable.encode (decodedQuotationRat p.1.2)) :=
    Primrec₂.natPair.comp hn (Primrec.encode.comp hr)
  have htest : Primrec₂ fun (p : P) (f : ℕ) =>
      match semanticSourceSentenceAtFuel p.1.1.1
          (Nat.pair p.1.1.2 (Encodable.encode (decodedQuotationRat p.1.2))) f with
      | some φ => semanticPrimeFreshSentenceB φ
      | none => false := by
    let Q := P × ℕ
    have hs : Primrec fun q : Q => semanticSourceSentenceAtFuel q.1.1.1.1
        (Nat.pair q.1.1.1.2 (Encodable.encode (decodedQuotationRat q.1.1.2))) q.2 :=
      semanticSourceSentenceAtFuel_prim.comp
        (((hschema.comp Primrec.fst).pair (hinput.comp Primrec.fst)).pair Primrec.snd)
    exact (Primrec.option_casesOn hs (Primrec.const false)
      ((semanticPrimeFreshSentenceB_prim.comp Primrec.snd).to₂)).to₂.of_eq
        fun p f => by
          cases semanticSourceSentenceAtFuel p.1.1.1
            (Nat.pair p.1.1.2 (Encodable.encode (decodedQuotationRat p.1.2))) f <;> rfl
  exact listRangeAny_prim Primrec.snd htest

lemma semanticSourceLawSeen_prim {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) :
    Primrec fun p : (ℕ × ℕ) × ℕ =>
      semanticSourceLawSeen base p.1.1 p.1.2 p.2 := by
  let P := (ℕ × ℕ) × ℕ
  have hpack : Primrec (fun q : P × ℕ =>
      (((q.1.1.1, q.1.1.2), q.2) : (ℕ × ℕ) × ℕ)) := by
    exact ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).pair Primrec.snd
  have hcheck : Primrec₂ fun (p : P) (f : ℕ) =>
      semanticSourceCheckedLawAtFuel base p.1.1 p.1.2 f :=
    ((semanticSourceCheckedLawAtFuel_prim base).comp hpack).to₂.of_eq fun _ _ => rfl
  have htest : Primrec₂ fun (p : P) (f : ℕ) =>
      (semanticSourceCheckedLawAtFuel base p.1.1 p.1.2 f).isSome :=
    Primrec.option_isSome.comp₂ hcheck
  exact listRangeAny_prim Primrec.snd htest

set_option maxHeartbeats 2000000 in
lemma semanticSourceDownwardPrefixValidAtFuel_prim {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) :
    Primrec fun p : ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) =>
      semanticSourceDownwardPrefixValidAtFuel base
        p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.1.2 p.2 := by
  let P := ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ)
  have hschema : Primrec fun p : P => p.1.1.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have hlimit : Primrec fun p : P => p.1.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have hfuel : Primrec fun p : P => p.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hn : Primrec fun p : P => p.1.2 := Primrec.snd.comp Primrec.fst
  have hzr : Primrec fun p : P => p.2 := Primrec.snd
  have hr : Primrec fun p : P => decodedQuotationRat p.2 :=
    decodedQuotationRat_prim.comp hzr
  have htest : Primrec₂ fun (p : P) (zs : ℕ) =>
      if decodedQuotationRat p.2 < decodedQuotationRat zs then
        semanticSourceLawSeen base p.1.1.1.1
          (sourceCutDownwardJob p.1.2 (decodedQuotationRat p.2)
            (decodedQuotationRat zs)) p.1.1.2
      else true := by
    let Q := P × ℕ
    have hs : Primrec fun q : Q => decodedQuotationRat q.2 :=
      decodedQuotationRat_prim.comp Primrec.snd
    have hjob : Primrec fun q : Q => sourceCutDownwardJob q.1.1.2
        (decodedQuotationRat q.1.2) (decodedQuotationRat q.2) := by
      unfold sourceCutDownwardJob
      exact Primrec₂.natPair.comp (Primrec.const 2)
        (Primrec₂.natPair.comp (hn.comp Primrec.fst)
          (Primrec₂.natPair.comp
            (Primrec.encode.comp (hr.comp Primrec.fst))
            (Primrec.encode.comp hs)))
    have hpack : Primrec fun q : Q =>
        ((q.1.1.1.1.1, sourceCutDownwardJob q.1.1.2
          (decodedQuotationRat q.1.2) (decodedQuotationRat q.2)), q.1.1.1.2) :=
      ((hschema.comp Primrec.fst).pair hjob).pair (hfuel.comp Primrec.fst)
    have hseen : Primrec fun q : Q => semanticSourceLawSeen base q.1.1.1.1.1
        (sourceCutDownwardJob q.1.1.2 (decodedQuotationRat q.1.2)
          (decodedQuotationRat q.2)) q.1.1.1.2 :=
      (semanticSourceLawSeen_prim base).comp hpack
    have hlt : PrimrecPred fun q : Q =>
        decodedQuotationRat q.1.2 < decodedQuotationRat q.2 :=
      (ratLE_prim.comp hs (hr.comp Primrec.fst)).not.of_eq fun _ => by simp [not_le]
    exact (Primrec.ite hlt hseen (Primrec.const true)).to₂
  exact listRangeAll_prim hlimit htest

set_option maxHeartbeats 2000000 in
lemma semanticSourceThresholdPrefixValidAtFuel_prim {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) :
    Primrec fun p : ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) =>
      semanticSourceThresholdPrefixValidAtFuel base
        p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.1.2 p.2 := by
  let P := ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ)
  have hschema : Primrec fun p : P => p.1.1.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have hfuel : Primrec fun p : P => p.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hn : Primrec fun p : P => p.1.2 := Primrec.snd.comp Primrec.fst
  have hzr : Primrec fun p : P => p.2 := Primrec.snd
  have hr : Primrec fun p : P => decodedQuotationRat p.2 :=
    decodedQuotationRat_prim.comp hzr
  have hfreshPack : Primrec fun p : P =>
      (((p.1.1.1.1, p.1.2), p.2), p.1.1.2) :=
    ((hschema.pair hn).pair hzr).pair hfuel
  have hfresh : Primrec fun p : P =>
      semanticSourceFreshSeen p.1.1.1.1 p.1.2 p.2 p.1.1.2 :=
    semanticSourceFreshSeen_prim.comp hfreshPack
  have hbelowJob : Primrec fun p : P => sourceCutBelowJob p.1.2
      (decodedQuotationRat p.2) := by
    unfold sourceCutBelowJob
    exact Primrec₂.natPair.comp (Primrec.const 0)
      (Primrec₂.natPair.comp hn (Primrec.encode.comp hr))
  have haboveJob : Primrec fun p : P => sourceCutAboveJob p.1.2
      (decodedQuotationRat p.2) := by
    unfold sourceCutAboveJob
    exact Primrec₂.natPair.comp (Primrec.const 1)
      (Primrec₂.natPair.comp hn (Primrec.encode.comp hr))
  have hbelowPack : Primrec fun p : P =>
      ((p.1.1.1.1, sourceCutBelowJob p.1.2 (decodedQuotationRat p.2)), p.1.1.2) :=
    (hschema.pair hbelowJob).pair hfuel
  have habovePack : Primrec fun p : P =>
      ((p.1.1.1.1, sourceCutAboveJob p.1.2 (decodedQuotationRat p.2)), p.1.1.2) :=
    (hschema.pair haboveJob).pair hfuel
  have hbelowSeen : Primrec fun p : P => semanticSourceLawSeen base p.1.1.1.1
      (sourceCutBelowJob p.1.2 (decodedQuotationRat p.2)) p.1.1.2 :=
    (semanticSourceLawSeen_prim base).comp hbelowPack
  have haboveSeen : Primrec fun p : P => semanticSourceLawSeen base p.1.1.1.1
      (sourceCutAboveJob p.1.2 (decodedQuotationRat p.2)) p.1.1.2 :=
    (semanticSourceLawSeen_prim base).comp habovePack
  have hbelowPred : PrimrecPred fun p : P => decodedQuotationRat p.2 < 0 :=
    (ratLE_prim.comp (Primrec.const 0) hr).not.of_eq fun _ => by simp [not_le]
  have habovePred : PrimrecPred fun p : P => 1 < decodedQuotationRat p.2 :=
    (ratLE_prim.comp hr (Primrec.const 1)).not.of_eq fun _ => by simp [not_le]
  have hbelow : Primrec fun p : P =>
      if decodedQuotationRat p.2 < 0 then
        semanticSourceLawSeen base p.1.1.1.1
          (sourceCutBelowJob p.1.2 (decodedQuotationRat p.2)) p.1.1.2
      else true :=
    Primrec.ite hbelowPred hbelowSeen (Primrec.const true)
  have habove : Primrec fun p : P =>
      if 1 < decodedQuotationRat p.2 then
        semanticSourceLawSeen base p.1.1.1.1
          (sourceCutAboveJob p.1.2 (decodedQuotationRat p.2)) p.1.1.2
      else true :=
    Primrec.ite habovePred haboveSeen (Primrec.const true)
  have hdown : Primrec fun p : P =>
      semanticSourceDownwardPrefixValidAtFuel base p.1.1.1.1 p.1.1.1.2
        p.1.1.2 p.1.2 p.2 :=
    semanticSourceDownwardPrefixValidAtFuel_prim base
  have hand {a b : P → Bool} (ha : Primrec a) (hb : Primrec b) :
      Primrec fun p : P => a p && b p :=
    (Primrec.dom_bool₂ (· && ·)).comp ha hb
  exact hand (hand (hand hfresh hbelow) habove) hdown |>.of_eq fun _ => rfl

set_option maxHeartbeats 2000000 in
lemma semanticSourcePrefixValidAtFuel_prim {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) :
    Primrec fun p : (ℕ × ℕ) × ℕ =>
      semanticSourcePrefixValidAtFuel base p.1.1 p.1.2 p.2 := by
  let P := (ℕ × ℕ) × ℕ
  have hlimit : Primrec fun p : P => p.1.2 := Primrec.snd.comp Primrec.fst
  have hinner : Primrec₂ fun (p : P) (n : ℕ) =>
      (List.range (p.1.2 + 1)).all fun zr =>
        semanticSourceThresholdPrefixValidAtFuel base p.1.1 p.1.2 p.2 n zr := by
    let Q := P × ℕ
    have hlimitQ : Primrec fun q : Q => q.1.1.2 := hlimit.comp Primrec.fst
    have htest : Primrec₂ fun (q : Q) (zr : ℕ) =>
        semanticSourceThresholdPrefixValidAtFuel base
          q.1.1.1 q.1.1.2 q.1.2 q.2 zr := by
      have hpack : Primrec fun z : Q × ℕ =>
          ((((z.1.1.1.1, z.1.1.1.2), z.1.1.2), z.1.2), z.2) := by
        exact (((((Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))).pair
          (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))).pair
          (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).pair
          (Primrec.snd.comp Primrec.fst)).pair Primrec.snd)
      exact ((semanticSourceThresholdPrefixValidAtFuel_prim base).comp hpack).to₂.of_eq
        fun _ _ => rfl
    exact (listRangeAll_prim hlimitQ htest).to₂
  exact listRangeAll_prim hlimit hinner

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

lemma semanticSourceFreshSeen_mono {schema n z fuel fuel' : ℕ}
    (hff : fuel ≤ fuel')
    (h : semanticSourceFreshSeen schema n z fuel = true) :
    semanticSourceFreshSeen schema n z fuel' = true := by
  obtain ⟨f, hf, φ, hemit, hfresh⟩ :=
    (semanticSourceFreshSeen_iff schema n z fuel).1 h
  exact (semanticSourceFreshSeen_iff schema n z fuel').2
    ⟨f, hf.trans hff, φ, hemit, hfresh⟩

lemma semanticSourceLawSeen_mono {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) {schema job fuel fuel' : ℕ}
    (hff : fuel ≤ fuel')
    (h : semanticSourceLawSeen base schema job fuel = true) :
    semanticSourceLawSeen base schema job fuel' = true := by
  obtain ⟨f, hf, law, hlaw⟩ :=
    (semanticSourceLawSeen_iff base schema job fuel).1 h
  exact (semanticSourceLawSeen_iff base schema job fuel').2
    ⟨f, hf.trans hff, law, hlaw⟩

/-- Pointwise eventual truth over a finite list combines into one common clock, given
monotonicity in the clock. -/
lemma listAll_eventually_of_mono {l : List ℕ} {test : ℕ → ℕ → Bool}
    (hmono : ∀ x {fuel fuel'}, fuel ≤ fuel' → test x fuel = true →
      test x fuel' = true)
    (heventual : ∀ x ∈ l, ∃ fuel, test x fuel = true) :
    ∃ fuel, l.all (fun x => test x fuel) = true := by
  induction l with
  | nil => exact ⟨0, rfl⟩
  | cons x xs ih =>
      obtain ⟨fx, hfx⟩ := heventual x (by simp)
      obtain ⟨fs, hfs⟩ := ih (fun y hy => heventual y (by simp [hy]))
      refine ⟨max fx fs, ?_⟩
      rw [List.all_cons, Bool.and_eq_true]
      exact ⟨hmono x (Nat.le_max_left _ _) hfx, by
        rw [List.all_eq_true] at hfs ⊢
        intro y hy
        exact hmono y (Nat.le_max_right _ _) (hfs y hy)⟩

lemma certifiedSourceFreshSeen_eventually {DP : DeductiveProcess}
    (X : CertifiedSourceLUVSeq DP) (n z : ℕ) :
    ∃ fuel, semanticSourceFreshSeen X.thresholdSchema n z fuel = true := by
  let r := decodedQuotationRat z
  obtain ⟨fuel, hemit⟩ := evaln_decode_sentence_eventually X.emitterCode
    (Nat.pair n (Encodable.encode r)) ((X.toLUV n).gt r) (X.emitter_spec n r)
  have hemit' : semanticSourceSentenceAtFuel X.thresholdSchema
      (Nat.pair n (Encodable.encode r)) fuel = some ((X.toLUV n).gt r) := by
    simpa [semanticSourceSentenceAtFuel, certified_thresholdSchema_emitterCode] using hemit
  exact ⟨fuel, (semanticSourceFreshSeen_iff X.thresholdSchema n z fuel).2
    ⟨fuel, le_rfl, (X.toLUV n).gt r, hemit', X.old_language n r⟩⟩

lemma certifiedSourceBelowSeen_eventually {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) (X : CertifiedSourceLUVSeq DP)
    (n : ℕ) (r : ℚ) (hr : (r : ℝ) < 0) :
    ∃ fuel, semanticSourceLawSeen base X.thresholdSchema
      (sourceCutBelowJob n r) fuel = true := by
  obtain ⟨fuel, h⟩ := certified_below_eventually_checked base X n r hr
  exact ⟨fuel, (semanticSourceLawSeen_iff base X.thresholdSchema
    (sourceCutBelowJob n r) fuel).2 ⟨fuel, le_rfl, (X.toLUV n).gt r, h⟩⟩

lemma certifiedSourceAboveSeen_eventually {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) (X : CertifiedSourceLUVSeq DP)
    (n : ℕ) (r : ℚ) (hr : 1 < (r : ℝ)) :
    ∃ fuel, semanticSourceLawSeen base X.thresholdSchema
      (sourceCutAboveJob n r) fuel = true := by
  obtain ⟨fuel, h⟩ := certified_above_eventually_checked base X n r hr
  exact ⟨fuel, (semanticSourceLawSeen_iff base X.thresholdSchema
    (sourceCutAboveJob n r) fuel).2 ⟨fuel, le_rfl, ∼(X.toLUV n).gt r, h⟩⟩

lemma certifiedSourceDownwardSeen_eventually {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) (X : CertifiedSourceLUVSeq DP)
    (n : ℕ) (r s : ℚ) (hrs : r < s) :
    ∃ fuel, semanticSourceLawSeen base X.thresholdSchema
      (sourceCutDownwardJob n r s) fuel = true := by
  obtain ⟨fuel, h⟩ := certified_downward_eventually_checked base X n r s hrs
  exact ⟨fuel, (semanticSourceLawSeen_iff base X.thresholdSchema
    (sourceCutDownwardJob n r s) fuel).2
      ⟨fuel, le_rfl, (X.toLUV n).gt s 🡒 (X.toLUV n).gt r, h⟩⟩

lemma semanticSourceDownwardPrefixValidAtFuel_mono {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP)
    {schema limit n zr fuel fuel' : ℕ} (hff : fuel ≤ fuel')
    (h : semanticSourceDownwardPrefixValidAtFuel base schema limit fuel n zr = true) :
    semanticSourceDownwardPrefixValidAtFuel base schema limit fuel' n zr = true := by
  rw [semanticSourceDownwardPrefixValidAtFuel, List.all_eq_true] at h ⊢
  intro zs hzs
  have hz := h zs hzs
  by_cases hrs : decodedQuotationRat zr < decodedQuotationRat zs
  · simpa [hrs] using semanticSourceLawSeen_mono base hff (by simpa [hrs] using hz)
  · simpa [hrs]

lemma certifiedSourceDownwardPrefix_eventually {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) (X : CertifiedSourceLUVSeq DP)
    (limit n zr : ℕ) :
    ∃ fuel, semanticSourceDownwardPrefixValidAtFuel base X.thresholdSchema
      limit fuel n zr = true := by
  let test : ℕ → ℕ → Bool := fun zs fuel =>
    if decodedQuotationRat zr < decodedQuotationRat zs then
      semanticSourceLawSeen base X.thresholdSchema
        (sourceCutDownwardJob n (decodedQuotationRat zr) (decodedQuotationRat zs)) fuel
    else true
  have hmono : ∀ zs {fuel fuel'}, fuel ≤ fuel' → test zs fuel = true →
      test zs fuel' = true := by
    intro zs fuel fuel' hff h
    by_cases hrs : decodedQuotationRat zr < decodedQuotationRat zs
    · simpa [test, hrs] using semanticSourceLawSeen_mono base hff (by simpa [test, hrs] using h)
    · simp [test, hrs]
  have heventual : ∀ zs ∈ List.range (limit + 1), ∃ fuel, test zs fuel = true := by
    intro zs _
    by_cases hrs : decodedQuotationRat zr < decodedQuotationRat zs
    · obtain ⟨fuel, h⟩ := certifiedSourceDownwardSeen_eventually base X n _ _ hrs
      exact ⟨fuel, by simpa [test, hrs] using h⟩
    · exact ⟨0, by simp [test, hrs]⟩
  simpa [semanticSourceDownwardPrefixValidAtFuel, test] using
    (listAll_eventually_of_mono hmono heventual)

lemma semanticSourceThresholdPrefixValidAtFuel_mono {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP)
    {schema limit n zr fuel fuel' : ℕ} (hff : fuel ≤ fuel')
    (h : semanticSourceThresholdPrefixValidAtFuel base schema limit fuel n zr = true) :
    semanticSourceThresholdPrefixValidAtFuel base schema limit fuel' n zr = true := by
  rw [semanticSourceThresholdPrefixValidAtFuel] at h ⊢
  simp only [Bool.and_eq_true] at h ⊢
  refine ⟨⟨⟨semanticSourceFreshSeen_mono hff h.1.1.1, ?_⟩, ?_⟩,
    semanticSourceDownwardPrefixValidAtFuel_mono base hff h.2⟩
  · by_cases hr : decodedQuotationRat zr < 0
    · simpa [hr] using semanticSourceLawSeen_mono base hff (by simpa [hr] using h.1.1.2)
    · simp [hr]
  · by_cases hr : 1 < decodedQuotationRat zr
    · simpa [hr] using semanticSourceLawSeen_mono base hff (by simpa [hr] using h.1.2)
    · simp [hr]

lemma semanticSourcePrefixValidAtFuel_mono {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP)
    {schema limit fuel fuel' : ℕ} (hff : fuel ≤ fuel')
    (h : semanticSourcePrefixValidAtFuel base schema limit fuel = true) :
    semanticSourcePrefixValidAtFuel base schema limit fuel' = true := by
  rw [semanticSourcePrefixValidAtFuel, List.all_eq_true] at h ⊢
  intro n hn
  rw [List.all_eq_true]
  intro zr hzr
  exact semanticSourceThresholdPrefixValidAtFuel_mono base hff
    (List.all_eq_true.mp (h n hn) zr hzr)

lemma certifiedSourceThresholdPrefix_eventually {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) (X : CertifiedSourceLUVSeq DP)
    (limit n zr : ℕ) :
    ∃ fuel, semanticSourceThresholdPrefixValidAtFuel base X.thresholdSchema
      limit fuel n zr = true := by
  let r := decodedQuotationRat zr
  obtain ⟨ffresh, hfresh⟩ := certifiedSourceFreshSeen_eventually X n zr
  obtain ⟨fbelow, hbelow⟩ : ∃ fuel,
      (if r < 0 then semanticSourceLawSeen base X.thresholdSchema
        (sourceCutBelowJob n r) fuel else true) = true := by
    by_cases hr : r < 0
    · have hrR : (r : ℝ) < 0 := by exact_mod_cast hr
      obtain ⟨fuel, h⟩ := certifiedSourceBelowSeen_eventually base X n r hrR
      exact ⟨fuel, by simpa [hr] using h⟩
    · exact ⟨0, by simp [hr]⟩
  obtain ⟨fabove, habove⟩ : ∃ fuel,
      (if 1 < r then semanticSourceLawSeen base X.thresholdSchema
        (sourceCutAboveJob n r) fuel else true) = true := by
    by_cases hr : 1 < r
    · have hrR : 1 < (r : ℝ) := by exact_mod_cast hr
      obtain ⟨fuel, h⟩ := certifiedSourceAboveSeen_eventually base X n r hrR
      exact ⟨fuel, by simpa [hr] using h⟩
    · exact ⟨0, by simp [hr]⟩
  obtain ⟨fdown, hdown⟩ := certifiedSourceDownwardPrefix_eventually base X limit n zr
  let fuel := max ffresh (max fbelow (max fabove fdown))
  have hffresh : ffresh ≤ fuel := by simp [fuel]
  have hffbelow : fbelow ≤ fuel := by simp [fuel]
  have hffabove : fabove ≤ fuel := by simp [fuel]
  have hffdown : fdown ≤ fuel := by simp [fuel]
  have hfresh' := semanticSourceFreshSeen_mono hffresh hfresh
  have hbelow' : (if r < 0 then semanticSourceLawSeen base X.thresholdSchema
      (sourceCutBelowJob n r) fuel else true) = true := by
    by_cases hr : r < 0
    · simp only [if_pos hr]
      exact semanticSourceLawSeen_mono base hffbelow (by simpa [hr] using hbelow)
    · simp [hr]
  have habove' : (if 1 < r then semanticSourceLawSeen base X.thresholdSchema
      (sourceCutAboveJob n r) fuel else true) = true := by
    by_cases hr : 1 < r
    · simp only [if_pos hr]
      exact semanticSourceLawSeen_mono base hffabove (by simpa [hr] using habove)
    · simp [hr]
  have hdown' := semanticSourceDownwardPrefixValidAtFuel_mono base hffdown hdown
  refine ⟨fuel, ?_⟩
  rw [semanticSourceThresholdPrefixValidAtFuel]
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨hfresh', hbelow'⟩, habove'⟩, hdown'⟩

/-- Every finite prefix of every certified source is eventually admitted by the fixed
executable registry. -/
lemma certifiedSourcePrefix_eventually_valid {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) (X : CertifiedSourceLUVSeq DP)
    (limit : ℕ) :
    ∃ fuel, semanticSourcePrefixValidAtFuel base X.thresholdSchema limit fuel = true := by
  let row : ℕ → ℕ → Bool := fun n fuel =>
    (List.range (limit + 1)).all fun zr =>
      semanticSourceThresholdPrefixValidAtFuel base X.thresholdSchema limit fuel n zr
  have hrowMono : ∀ n {fuel fuel'}, fuel ≤ fuel' → row n fuel = true →
      row n fuel' = true := by
    intro n fuel fuel' hff h
    simp only [row, List.all_eq_true] at h ⊢
    intro zr hzr
    exact semanticSourceThresholdPrefixValidAtFuel_mono base hff (h zr hzr)
  have hrowEventually : ∀ n ∈ List.range (limit + 1), ∃ fuel, row n fuel = true := by
    intro n _
    obtain ⟨fuel, hfuel⟩ := listAll_eventually_of_mono
      (l := List.range (limit + 1))
      (test := fun zr fuel => semanticSourceThresholdPrefixValidAtFuel
        base X.thresholdSchema limit fuel n zr)
      (fun zr _ _ hff h => semanticSourceThresholdPrefixValidAtFuel_mono base hff h)
      (by
        intro zr _
        exact certifiedSourceThresholdPrefix_eventually base X limit n zr)
    exact ⟨fuel, by simpa [row] using hfuel⟩
  obtain ⟨fuel, hfuel⟩ := listAll_eventually_of_mono
    (l := List.range (limit + 1)) (test := row) hrowMono hrowEventually
  refine ⟨fuel, ?_⟩
  rw [semanticSourcePrefixValidAtFuel, List.all_eq_true]
  intro n hn
  exact List.all_eq_true.mp hfuel n hn

/-- Prefix validity exposes freshness for every admitted source query: the accessor for the
freshness conjunct, paired with `semanticSourcePrefixValidAtFuel_downward` below. -/
lemma semanticSourcePrefixValidAtFuel_fresh {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) {schema limit fuel n z : ℕ}
    (hvalid : semanticSourcePrefixValidAtFuel base schema limit fuel = true)
    (hn : n ≤ limit) (hz : z ≤ limit) :
    semanticSourceFreshSeen schema n z fuel = true := by
  rw [semanticSourcePrefixValidAtFuel, List.all_eq_true] at hvalid
  have hnmem : n ∈ List.range (limit + 1) := by simp [hn]
  have hzmem : z ∈ List.range (limit + 1) := by simp [hz]
  have h := List.all_eq_true.mp (hvalid n hnmem) z hzmem
  rw [semanticSourceThresholdPrefixValidAtFuel] at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1

/-- Prefix validity exposes every applicable pairwise downward law. -/
lemma semanticSourcePrefixValidAtFuel_downward {DP : DeductiveProcess}
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
  rw [semanticSourceThresholdPrefixValidAtFuel,
    semanticSourceDownwardPrefixValidAtFuel] at h
  simp only [Bool.and_eq_true] at h
  have hlast := h.2
  have hz := List.all_eq_true.mp hlast zs hzsmem
  simpa [hrs] using hz

end LogicalInduction

namespace LogicalInduction

open LO LO.Propositional LO.FirstOrder LO.FirstOrder.Arithmetic

attribute [local irreducible] Nat.sqrt

/-! ## The universal definition clauses -/

/-- A universal source-definition job packs schema, input, direction, and bounded fuel. -/
def semanticSourceDefinitionJob (schema input direction fuel : ℕ) : ℕ :=
  Nat.pair schema (Nat.pair input (Nat.pair direction fuel))

/-- One bounded source-definition clause.  All failures are harmless tautologies. -/
def semanticSourceDefSentence (e : ℕ) : Sentence :=
  let schema := e.unpair.1
  let input := e.unpair.2.unpair.1
  let direction := e.unpair.2.unpair.2.unpair.1
  let fuel := e.unpair.2.unpair.2.unpair.2
  if schema.unpair.1 = 0 then
    match semanticSourceSentenceAtFuel schema input fuel with
    | some φ =>
        if semanticPrimeFreshSentenceB φ then
          if direction = 0 then φ 🡒 semanticPrimeSentence schema input
          else semanticPrimeSentence schema input 🡒 φ
        else ⊤
    | none => ⊤
  else ⊤

/-- Stage `k` as a list: every definition clause with index at most `k`, newest first. -/
def semanticSourceStageList : ℕ → List Sentence
  | 0 => [semanticSourceDefSentence 0]
  | k + 1 => semanticSourceDefSentence (k + 1) :: semanticSourceStageList k

lemma mem_semanticSourceStageList {e k : ℕ} (h : e ≤ k) :
    semanticSourceDefSentence e ∈ semanticSourceStageList k := by
  induction k with
  | zero => simp [semanticSourceStageList, Nat.le_zero.mp h]
  | succ k ih =>
      rcases Nat.lt_or_ge e (k + 1) with hlt | hge
      · exact List.mem_cons_of_mem _ (ih (Nat.lt_succ_iff.mp hlt))
      · have he : e = k + 1 := le_antisymm h hge
        simp [semanticSourceStageList, he]

lemma semanticSourceStageList_exists {φ : Sentence} {k : ℕ}
    (h : φ ∈ semanticSourceStageList k) :
    ∃ e, φ = semanticSourceDefSentence e := by
  induction k with
  | zero => exact ⟨0, by simpa [semanticSourceStageList] using h⟩
  | succ k ih =>
      rcases List.mem_cons.mp h with h | h
      · exact ⟨k + 1, h⟩
      · exact ih h

/-! ## The process, and its program -/

/-- The single universal source process.  It contains no chosen source, market, weight,
or deferral data. -/
def semanticSourceDP : DeductiveProcess where
  D k := (semanticSourceStageList k).toFinset
  mono k := by
    intro φ hφ
    simp only [List.mem_toFinset] at hφ ⊢
    exact List.mem_cons_of_mem _ hφ

private lemma semanticSourceImp_prim : Primrec₂ fun φ ψ : Sentence => φ 🡒 ψ := by
  apply Primrec₂.encode_iff.mp
  exact (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 2)
    (Primrec₂.natPair.comp
      (Primrec.encode.comp Primrec.fst)
      (Primrec.encode.comp Primrec.snd)))).to₂.of_eq fun _ _ => rfl

lemma semanticSourceDefSentence_prim : Primrec semanticSourceDefSentence := by
  have hschema : Primrec fun e : ℕ => e.unpair.1 := Primrec.fst.comp Primrec.unpair
  have hrest : Primrec fun e : ℕ => e.unpair.2 := Primrec.snd.comp Primrec.unpair
  have hinput : Primrec fun e : ℕ => e.unpair.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp hrest)
  have htail : Primrec fun e : ℕ => e.unpair.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp hrest)
  have hdirection : Primrec fun e : ℕ => e.unpair.2.unpair.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp htail)
  have hfuel : Primrec fun e : ℕ => e.unpair.2.unpair.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp htail)
  have hsentence : Primrec fun e : ℕ =>
      semanticSourceSentenceAtFuel e.unpair.1 e.unpair.2.unpair.1
        e.unpair.2.unpair.2.unpair.2 :=
    semanticSourceSentenceAtFuel_prim.comp ((hschema.pair hinput).pair hfuel)
  have hleaf : Primrec fun e : ℕ =>
      semanticPrimeSentence e.unpair.1 e.unpair.2.unpair.1 := by
    apply Primrec.encode_iff.mp
    exact semanticPrimeSentence_encode_prim.comp (hschema.pair hinput)
  have hsome : Primrec₂ fun (e : ℕ) (φ : Sentence) =>
      if semanticPrimeFreshSentenceB φ then
        if e.unpair.2.unpair.2.unpair.1 = 0 then
          φ 🡒 semanticPrimeSentence e.unpair.1 e.unpair.2.unpair.1
        else semanticPrimeSentence e.unpair.1 e.unpair.2.unpair.1 🡒 φ
      else ⊤ := by
    let Q := ℕ × Sentence
    have hfresh : PrimrecPred fun q : Q => semanticPrimeFreshSentenceB q.2 = true :=
      Primrec.eq.comp (semanticPrimeFreshSentenceB_prim.comp Primrec.snd)
        (Primrec.const true)
    have hdir : PrimrecPred fun q : Q => q.1.unpair.2.unpair.2.unpair.1 = 0 :=
      Primrec.eq.comp (hdirection.comp Primrec.fst) (Primrec.const 0)
    have hleafQ : Primrec fun q : Q =>
        semanticPrimeSentence q.1.unpair.1 q.1.unpair.2.unpair.1 :=
      hleaf.comp Primrec.fst
    have hforward : Primrec fun q : Q =>
        q.2 🡒 semanticPrimeSentence q.1.unpair.1 q.1.unpair.2.unpair.1 :=
      semanticSourceImp_prim.comp Primrec.snd hleafQ
    have hbackward : Primrec fun q : Q =>
        semanticPrimeSentence q.1.unpair.1 q.1.unpair.2.unpair.1 🡒 q.2 :=
      semanticSourceImp_prim.comp hleafQ Primrec.snd
    exact (Primrec.ite hfresh (Primrec.ite hdir hforward hbackward)
      (Primrec.const (⊤ : Sentence))).to₂.of_eq fun _ _ => rfl
  have hdecoded : Primrec fun e : ℕ =>
      match semanticSourceSentenceAtFuel e.unpair.1 e.unpair.2.unpair.1
          e.unpair.2.unpair.2.unpair.2 with
      | some φ =>
          if semanticPrimeFreshSentenceB φ then
            if e.unpair.2.unpair.2.unpair.1 = 0 then
              φ 🡒 semanticPrimeSentence e.unpair.1 e.unpair.2.unpair.1
            else semanticPrimeSentence e.unpair.1 e.unpair.2.unpair.1 🡒 φ
          else ⊤
      | none => ⊤ :=
    (Primrec.option_casesOn hsentence (Primrec.const (⊤ : Sentence)) hsome).of_eq
      fun e => by
        cases h : (semanticSourceSentenceAtFuel e.unpair.1
          e.unpair.2.unpair.1 e.unpair.2.unpair.2.unpair.2) <;> simp
  have hsource : PrimrecPred fun e : ℕ => e.unpair.1.unpair.1 = 0 :=
    Primrec.eq.comp (Primrec.fst.comp (Primrec.unpair.comp hschema))
      (Primrec.const 0)
  exact (Primrec.ite hsource hdecoded (Primrec.const (⊤ : Sentence))).of_eq
    fun e => by simp [semanticSourceDefSentence]

/-- The universal source interpreter is a computable deductive process. -/
lemma semanticSourceDP_computable : ComputableDeductiveProcess semanticSourceDP := by
  have hlist : Computable semanticSourceStageList := by
    have hstep : Computable fun p : ℕ × List Sentence =>
        semanticSourceDefSentence (p.1 + 1) :: p.2 :=
      Computable.list_cons.comp
        (semanticSourceDefSentence_prim.to_comp.comp
          (Primrec.succ.to_comp.comp Computable.fst)) Computable.snd
    refine (Computable.nat_rec Computable.id
      (Computable.const [semanticSourceDefSentence 0])
      (hstep.comp₂ Computable.snd.to₂)).of_eq (fun k => ?_)
    induction k with
    | zero => rfl
    | succ k ih => simpa [semanticSourceStageList] using ih
  have hkey : Computable fun k => Encodable.encode
      ((sentenceDedup (semanticSourceStageList k)).insertionSort sentenceCodeLE) :=
    Computable.encode.comp
      ((sentenceInsertionSort_prim.comp sentenceDedup_prim).to_comp.comp hlist)
  obtain ⟨code, hcode⟩ := Nat.Partrec.Code.exists_code.mp
    (Partrec.nat_iff.mp hkey)
  refine ⟨code, fun k => ?_⟩
  rw [hcode]
  exact Part.mem_some_iff.mpr (encode_toFinset_eq (semanticSourceStageList k))

/-! ## The canonical extension world -/

/-- Bounded runs of one named emitter cannot decode to two different sentences. -/
lemma semanticSourceSentenceAtFuel_unique {schema input fuel fuel' : ℕ}
    {φ ψ : Sentence}
    (hφ : semanticSourceSentenceAtFuel schema input fuel = some φ)
    (hψ : semanticSourceSentenceAtFuel schema input fuel' = some ψ) : φ = ψ := by
  unfold semanticSourceSentenceAtFuel at hφ hψ
  obtain ⟨outφ, houtφ, hdecodeφ⟩ := Option.bind_eq_some_iff.mp hφ
  obtain ⟨outψ, houtψ, hdecodeψ⟩ := Option.bind_eq_some_iff.mp hψ
  have hmemφ := Nat.Partrec.Code.evaln_sound houtφ
  have hmemψ := Nat.Partrec.Code.evaln_sound houtψ
  have hout : outφ = outψ := Part.mem_unique hmemφ hmemψ
  subst outψ
  rw [hdecodeφ] at hdecodeψ
  exact Option.some.inj hdecodeψ

/-- Extend an arbitrary base world by interpreting each successfully emitted fresh
tag-`0` source leaf as the base-world truth of its unique emitted sentence. -/
noncomputable def semanticSourceExtensionWorld (v₀ : PCWorld) : PCWorld := by
  classical
  exact fun a =>
    if a.unpair.1 = semanticPrimeTag ∧ a.unpair.2.unpair.1.unpair.1 = 0 then
      ∃ fuel φ,
        semanticSourceSentenceAtFuel a.unpair.2.unpair.1 a.unpair.2.unpair.2 fuel = some φ ∧
          SemanticPrimeFreshSentence φ ∧ v₀.Holds φ
    else v₀ a

lemma semanticSourceExtensionWorld_agree (v₀ : PCWorld) {a : ℕ}
    (ha : a.unpair.1 ≠ semanticPrimeTag) :
    semanticSourceExtensionWorld v₀ a ↔ v₀ a := by
  simp [semanticSourceExtensionWorld, ha]

lemma semanticSourceExtensionWorld_holds_fresh (v₀ : PCWorld) {φ : Sentence}
    (hφ : SemanticPrimeFreshSentence φ) :
    (semanticSourceExtensionWorld v₀).Holds φ ↔ v₀.Holds φ :=
  PCWorld.holds_congr_atomCodes φ
    (fun a ha => semanticSourceExtensionWorld_agree v₀ (hφ a ha))

lemma semanticSourceExtensionWorld_leaf (v₀ : PCWorld)
    (schema input : ℕ) (hschema : schema.unpair.1 = 0) :
    (semanticSourceExtensionWorld v₀).Holds (semanticPrimeSentence schema input) ↔
      ∃ fuel φ, semanticSourceSentenceAtFuel schema input fuel = some φ ∧
        SemanticPrimeFreshSentence φ ∧ v₀.Holds φ := by
  change semanticSourceExtensionWorld v₀ (semanticPrimeCode schema input) ↔ _
  simp [semanticSourceExtensionWorld, semanticPrimeCode, hschema]

lemma semanticSourceExtensionWorld_leaf_iff (v₀ : PCWorld)
    (schema input fuel : ℕ) (hschema : schema.unpair.1 = 0) {φ : Sentence}
    (hemit : semanticSourceSentenceAtFuel schema input fuel = some φ)
    (hfresh : SemanticPrimeFreshSentence φ) :
    (semanticSourceExtensionWorld v₀).Holds (semanticPrimeSentence schema input) ↔
      v₀.Holds φ := by
  rw [semanticSourceExtensionWorld_leaf v₀ schema input hschema]
  constructor
  · rintro ⟨fuel', ψ, hψ, _, hholds⟩
    simpa [semanticSourceSentenceAtFuel_unique hψ hemit] using hholds
  · intro hholds
    exact ⟨fuel, φ, hemit, hfresh, hholds⟩

/-- Any downward law admitted by the executable registry is semantically valid between
the corresponding source leaves in the canonical extension of a base model. -/
lemma semanticSourceExtensionWorld_downward_of_seen {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) (v₀ : PCWorld)
    (hv₀ : v₀.ConsistentWithTheory DP) {schema n fuel : ℕ} {r s : ℚ}
    (hrs : r < s)
    (hseen : semanticSourceLawSeen base schema
      (sourceCutDownwardJob n r s) fuel = true) :
    (semanticSourceExtensionWorld v₀).Holds
      (semanticPrimeSentence schema (Nat.pair n (Encodable.encode s))) →
    (semanticSourceExtensionWorld v₀).Holds
      (semanticPrimeSentence schema (Nat.pair n (Encodable.encode r))) := by
  obtain ⟨f, _, law, hchecked⟩ :=
    (semanticSourceLawSeen_iff base schema (sourceCutDownwardJob n r s) fuel).1 hseen
  obtain ⟨φr, φs, hφr, hφs, hfr, hfs, rfl⟩ :=
    semanticSourceCheckedDownward_spec base hrs hchecked
  have hsource := semanticSourceCheckedLawAtFuel_source base hchecked
  obtain ⟨k, hk⟩ := semanticSourceCheckedLawAtFuel_mem base hchecked
  have hbase : v₀.Holds (φs 🡒 φr) := hv₀ k _ hk
  intro hs
  have hs₀ : v₀.Holds φs :=
    (semanticSourceExtensionWorld_leaf_iff v₀ schema _ f hsource hφs hfs).mp hs
  exact (semanticSourceExtensionWorld_leaf_iff v₀ schema _ f hsource hφr hfr).mpr
    (hbase hs₀)

/-! ## Explicit non-vacuity -/

/-- Every source-definition clause is true in the canonical extension world. -/
lemma semanticSourceExtensionWorld_holds_defSentence (v₀ : PCWorld) (e : ℕ) :
    (semanticSourceExtensionWorld v₀).Holds (semanticSourceDefSentence e) := by
  unfold semanticSourceDefSentence
  by_cases hschema : e.unpair.1.unpair.1 = 0
  · rw [if_pos hschema]
    cases hemit : (semanticSourceSentenceAtFuel e.unpair.1 e.unpair.2.unpair.1
        e.unpair.2.unpair.2.unpair.2) with
    | none =>
        change (semanticSourceExtensionWorld v₀).Holds (⊤ : Sentence)
        exact PCWorld.holds_top _
    | some φ =>
        change (semanticSourceExtensionWorld v₀).Holds
          (if semanticPrimeFreshSentenceB φ then
            if e.unpair.2.unpair.2.unpair.1 = 0 then
              φ 🡒 semanticPrimeSentence e.unpair.1 e.unpair.2.unpair.1
            else semanticPrimeSentence e.unpair.1 e.unpair.2.unpair.1 🡒 φ
          else ⊤)
        by_cases hfreshB : semanticPrimeFreshSentenceB φ = true
        · rw [if_pos hfreshB]
          have hfresh : SemanticPrimeFreshSentence φ :=
            (semanticPrimeFreshSentenceB_eq_true φ).1 hfreshB
          have hleaf := semanticSourceExtensionWorld_leaf_iff v₀
            e.unpair.1 e.unpair.2.unpair.1 e.unpair.2.unpair.2.unpair.2
            hschema hemit hfresh
          have hformula := semanticSourceExtensionWorld_holds_fresh v₀ hfresh
          by_cases hdir : e.unpair.2.unpair.2.unpair.1 = 0
          · rw [if_pos hdir]
            intro h
            exact hleaf.mpr (hformula.mp h)
          · rw [if_neg hdir]
            intro h
            exact hformula.mpr (hleaf.mp h)
        · rw [if_neg hfreshB]
          exact PCWorld.holds_top _
  · rw [if_neg hschema]
    exact PCWorld.holds_top _

/-- The fixed universal source process has an explicit completed world over every base
world; no consistency premise is hidden in source reflection. -/
lemma semanticSourceDP_hworld (v₀ : PCWorld) :
    (semanticSourceExtensionWorld v₀).ConsistentWithTheory semanticSourceDP := by
  intro k φ hφ
  obtain ⟨e, rfl⟩ := semanticSourceStageList_exists (List.mem_toFinset.mp hφ)
  exact semanticSourceExtensionWorld_holds_defSentence v₀ e

/-! ## The theorem-plus-source process

The union offered to clients as a named package: a canonical process, its certified program,
and its explicit completed world.  Nothing downstream prices against it, by the design
decision recorded in the module header. -/

/-- Conservative combination with any base process whose stages stay in the old language. -/
lemma semanticSourceExtensionWorld_consistentWith_union
    (B : DeductiveProcess) (v₀ : PCWorld)
    (hBfresh : ∀ k φ, φ ∈ B.D k → SemanticPrimeFreshSentence φ)
    (hv₀ : v₀.ConsistentWithTheory B) :
    (semanticSourceExtensionWorld v₀).ConsistentWithTheory
      (B.union semanticSourceDP) := by
  intro k
  refine ((semanticSourceExtensionWorld v₀).consistentWith_union_iff
    B semanticSourceDP k).mpr ⟨?_, semanticSourceDP_hworld v₀ k⟩
  intro φ hφ
  exact (semanticSourceExtensionWorld_holds_fresh v₀ (hBfresh k φ hφ)).mpr
    (hv₀ k φ hφ)

/-- The canonical source-aware theory process is fixed from `T` alone. -/
noncomputable def theoremSemanticSourceDP (T : ArithmeticTheory) [T.Δ₁]
    [Entailment.Consistent T] : DeductiveProcess :=
  (theoremDP T).union semanticSourceDP

/-- The certified program for `theoremSemanticSourceDP`, the union of `theoremDP`'s own
program and `semanticSourceDP`'s. -/
noncomputable def theoremSemanticSourceDPComputation (T : ArithmeticTheory)
    [T.Δ₁] [Entailment.Consistent T] :
    DeductiveProcessComputation (theoremSemanticSourceDP T) :=
  ((theoremDP_computable T).nonemptyComputation.some).union
    semanticSourceDP_computable.nonemptyComputation.some

lemma theoremDP_semanticPrimeFresh (T : ArithmeticTheory) [T.Δ₁]
    [Entailment.Consistent T] (k : ℕ) (φ : Sentence) (hφ : φ ∈ (theoremDP T).D k) :
    SemanticPrimeFreshSentence φ := by
  simp only [theoremDP, theoremStage, Finset.mem_image, Finset.mem_filter,
    Finset.mem_range] at hφ
  obtain ⟨e, _, rfl⟩ := hφ
  exact eventAtom_atomCodes_ne_semanticPrimeTag e

/-- Explicit non-vacuity of the fixed theorem-plus-source process. -/
lemma theoremSemanticSourceDP_hworld (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T]
    [Entailment.Consistent T] :
    (semanticSourceExtensionWorld (provabilityWorld T)).ConsistentWithTheory
      (theoremSemanticSourceDP T) :=
  semanticSourceExtensionWorld_consistentWith_union (theoremDP T)
    (provabilityWorld T) (theoremDP_semanticPrimeFresh T) (theoremDP_hworld T)

lemma semanticSourceDefSentence_mem_stage (e : ℕ) :
    semanticSourceDefSentence e ∈ semanticSourceDP.D e :=
  List.mem_toFinset.mpr (mem_semanticSourceStageList (le_refl e))

lemma holds_semanticSourceDefSentence {v : PCWorld}
    (hv : v.ConsistentWithTheory semanticSourceDP) (e : ℕ) :
    v.Holds (semanticSourceDefSentence e) :=
  hv e _ (semanticSourceDefSentence_mem_stage e)

lemma semanticSourceDefSentence_job (schema input direction fuel : ℕ) :
    semanticSourceDefSentence
      (semanticSourceDefinitionJob schema input direction fuel) =
      if schema.unpair.1 = 0 then
        match semanticSourceSentenceAtFuel schema input fuel with
        | some φ =>
            if semanticPrimeFreshSentenceB φ then
              if direction = 0 then φ 🡒 semanticPrimeSentence schema input
              else semanticPrimeSentence schema input 🡒 φ
            else ⊤
        | none => ⊤
      else ⊤ := by
  simp [semanticSourceDefSentence, semanticSourceDefinitionJob]

/-! ## Threshold reflection for certified sources -/

/-- Any successfully decoded fresh source sentence is reflected by its semantic handle in
every completed world of the one fixed process. -/
lemma semanticSourceSentenceAtFuel_reflected {v : PCWorld}
    (hv : v.ConsistentWithTheory semanticSourceDP)
    (schema input fuel : ℕ) (hschema : schema.unpair.1 = 0)
    {φ : Sentence} (hemit : semanticSourceSentenceAtFuel schema input fuel = some φ)
    (hfresh : SemanticPrimeFreshSentence φ) :
    v.Holds (semanticPrimeSentence schema input) ↔ v.Holds φ := by
  have hfreshB : semanticPrimeFreshSentenceB φ = true :=
    (semanticPrimeFreshSentenceB_eq_true φ).2 hfresh
  constructor
  · have h := holds_semanticSourceDefSentence hv
      (semanticSourceDefinitionJob schema input 1 fuel)
    rw [semanticSourceDefSentence_job, if_pos hschema, hemit] at h
    simp [hfreshB] at h
    exact h
  · have h := holds_semanticSourceDefSentence hv
      (semanticSourceDefinitionJob schema input 0 fuel)
    rw [semanticSourceDefSentence_job, if_pos hschema, hemit] at h
    simp [hfreshB] at h
    exact h

/-- Every proof-carrying paper source has exact threshold reflection through its canonical
compact wrapper. -/
lemma certifiedSource_threshold_reflected {DP : DeductiveProcess}
    (X : CertifiedSourceLUVSeq DP) (n : ℕ) (r : ℚ) (v : PCWorld)
    (hv : v.ConsistentWithTheory semanticSourceDP) :
    v.Holds ((X.toPresented.toLUV n).gt r) ↔ v.Holds ((X.toLUV n).gt r) := by
  obtain ⟨fuel, hfuel⟩ := evaln_decode_sentence_eventually X.emitterCode
    (Nat.pair n (Encodable.encode r)) ((X.toLUV n).gt r) (X.emitter_spec n r)
  apply semanticSourceSentenceAtFuel_reflected hv X.thresholdSchema
    (Nat.pair n (Encodable.encode r)) fuel X.thresholdSchema_source
  · simpa [semanticSourceSentenceAtFuel, certified_thresholdSchema_emitterCode] using hfuel
  · exact X.old_language n r

/-- Exact threshold reflection transfers the repository's `ValuesAt` relation both ways. -/
lemma certifiedSource_valuesAt_iff {DP : DeductiveProcess}
    (X : CertifiedSourceLUVSeq DP) (n : ℕ) (x : ℝ) (v : PCWorld)
    (hv : v.ConsistentWithTheory semanticSourceDP) :
    v.ValuesAt (X.toPresented.toLUV n) x ↔ v.ValuesAt (X.toLUV n) x := by
  constructor
  · rintro ⟨hx0, hx1, hx⟩
    exact ⟨hx0, hx1, fun r => by rw [← certifiedSource_threshold_reflected X n r v hv]; exact hx r⟩
  · rintro ⟨hx0, hx1, hx⟩
    exact ⟨hx0, hx1, fun r => by rw [certifiedSource_threshold_reflected X n r v hv]; exact hx r⟩

end LogicalInduction
