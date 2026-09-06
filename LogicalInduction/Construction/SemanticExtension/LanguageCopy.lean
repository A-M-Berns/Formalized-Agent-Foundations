import LogicalInduction.Construction.SemanticExtension.Prime
import LogicalInduction.Construction.Paper.FiniteEntailment
import LogicalInduction.Construction.SemanticExtension.Source

/-!
# The fixed old-language copy, and admission of a source through it

The vocabulary-ownership answer to the obstruction of
`Construction/SemanticExtension/Prime.lean` — one fixed renaming, chosen independently of
any source family, market, weight or deferral — the
certificate-free admission gate stated over it, and the compiler that admits a caller's
existing RPN threshold certificate.  Construction machinery for `thm:ccee`; no paper node.

## The renaming

A flat source may already mention the atoms later used as semantic handles, so the extension
first moves the whole pre-extension vocabulary out of the way, deliberately carrying no axiom
identifying a renamed atom with its original.

* `oldLanguageTag = 6` is this module's row in the global atom-payload allocation table
  (`ComputationClaimKind.godelCode`); `oldAtom`, `liftSentence`, `liftLUV`, `liftDP` and
  `pullOldWorld` are the renaming and its inverse reading.
* Transport laws — `sentenceAtomCodes_liftSentence`, `holds_liftSentence_iff`,
  `liftLUV_valuesAt_iff`, `consistentWith_liftDP_iff`, `consistentWithTheory_liftDP_iff` —
  are exact, in both directions.
* Disjointness: `eventAtom_atomCodes_ne_oldLanguageTag` and `theoremDP_oldLanguageFresh` show
  the established theorem/event vocabulary never uses tag `6`.
* `liftSentenceCode` is the executable numeric counterpart, proved primitive recursive by
  course-of-values recursion, giving `liftDPComputation` and `liftDP_computable`.
* `liftLUV_holds_downward_of_valued` and `liftLUV_downward_eventually_stageEntails` derive the
  rational downward-cut law that exact mesh multiplication needs from the paper-facing
  valuedness premise alone, with no caller-supplied cut certificate.

"Old language" here names the pre-extension propositional vocabulary.

## Entailment-gated admission

The certificate-free gate for tag-`0` sources, parallel to the certificate-carrying gate in
`Construction/SemanticExtension/Source.lean`.  What distinguishes it: the witness carries no
proof object and no source-specific process, only clocks for the universal emitter and for the
already-fixed base process, plus a base stage index.  It accepts exactly when exhaustive
finite propositional evaluation (`stageEntails`) verifies that the decoded base stage entails
the emitted law.

The objects are `entailedSourceLawEvidenceAt`, `entailedSourceLawSeen` (dovetailed over packed
witnesses), and the three nested prefix predicates
`entailedSourceDownwardPrefixValidAtFuel`, `entailedSourceThresholdPrefixValidAtFuel` and
`entailedSourcePrefixValidAtFuel`; each is primitive recursive.  Soundness is
`entailedSourceLawEvidenceAt_sound` (accepted evidence holds in every completed base world),
completeness `entailedSourceLawSeen_eventually` (every emitted law that is a completed-base
consequence is eventually admitted, via
`DeductiveProcess.stageEntails_complete_of_semantic`), with
`entailedSourcePrefixValidAtFuel_downward` and
`semanticSourceExtensionWorld_downward_of_entailedSeen`.

Exact product consistency uses only freshness and pairwise downward closure; bounds are
supplied separately by the `ValuesAt` hypotheses at the point where multiplication is
reflected.  `entailedSourceLawSeen` is made `local irreducible` before the prefix predicates
so that their `Primrec` elaboration matches structurally rather than by reduction.

## Compiling an existing RPN source into the registry

The last section admits a caller's *existing* token-metered RPN threshold certificate
(`LUV.RpnThresholdCodeSeq X`) into the fixed old-language registry, so that the exact product
of `thm:ccee` accepts an arbitrary threshold-only source.  It defines
`liftedRpnSourceSentence`, the represented sentence at an arbitrary rational query;
`liftedRpnMeshQuery`, the conversion into the `⟨n,⟨k,i⟩⟩` ABI of `RpnThresholdCodeSeq`;
`liftedRpnSourceCode`, the total emitter program extracted from the caller's certificate; and
`liftedRpnSourceSchema`, its self-describing tag-`0` schema.

No new efficiency premise is added to the caller: the exact product needs only nonnegative
rational thresholds, every nonnegative reduced rational is already one of the `i/k` queries
`RpnThresholdCodeSeq` certifies, and negative queries receive the canonical true sentence `⊤`.
The main results are `liftedRpnSource_reflected` — exact reflection of the internally lifted
source through the one fixed universal source interpreter — and
`liftedRpnSourcePrefix_eventually_valid`, that every finite registry prefix is eventually
validated, which is the hypothesis the registry gate consumes;
`liftedRpnSourceSentence_fresh` separates every derived sentence from the extension
vocabulary.  The emitter code is *data* inside a universal tag-`0` schema; the semantic
process is never specialized to `X`, which is what keeps the deductive process fixed from `T`
before a source is chosen.

Consumed by `Construction/SemanticExtension/Registry.lean` and
`Construction/SemanticExtension/Endpoints.lean`, where
`liftedRpnSource_factor_eventually` turns these into admission of the source as an exact
product factor, and thence `lic_no_expected_net_update_conditional_exact_canonical`.
-/

namespace LogicalInduction

open LO LO.Propositional LO.FirstOrder LO.FirstOrder.Arithmetic

/-! ## The fixed renaming -/

/-- Reserved outer tag for the fixed copy of the pre-extension propositional language.
See the global atom-payload allocation table at `ComputationClaimKind.godelCode`. -/
def oldLanguageTag : ℕ := 6

/-- The atom injection into the fixed old-language namespace. -/
def oldAtom (a : ℕ) : ℕ := Nat.pair oldLanguageTag a

/-- Syntactically rename every atom into the fixed old-language namespace. -/
def liftSentence (phi : Sentence) : Sentence :=
  phi⟦fun a => Formula.atom (oldAtom a)⟧

/-- Atom support of the renamed sentence is exactly the image of the original support. -/
@[simp] lemma sentenceAtomCodes_liftSentence (phi : Sentence) :
    sentenceAtomCodes (liftSentence phi) =
      (sentenceAtomCodes phi).image oldAtom := by
  induction phi using Formula.rec' with
  | hfalsum => rfl
  | hatom a => simp [liftSentence, Formula.subst]
  | himp phi psi ihphi ihpsi =>
      change sentenceAtomCodes (liftSentence phi) ∪
        sentenceAtomCodes (liftSentence psi) = _
      rw [ihphi, ihpsi, sentenceAtomCodes_imp, Finset.image_union]
  | hand phi psi ihphi ihpsi =>
      change sentenceAtomCodes (liftSentence phi) ∪
        sentenceAtomCodes (liftSentence psi) = _
      rw [ihphi, ihpsi, sentenceAtomCodes_and, Finset.image_union]
  | hor phi psi ihphi ihpsi =>
      change sentenceAtomCodes (liftSentence phi) ∪
        sentenceAtomCodes (liftSentence psi) = _
      rw [ihphi, ihpsi, sentenceAtomCodes_or, Finset.image_union]

/-! ## Transport laws -/

/-- Read the old-language namespace of a world as a world on the original language. -/
def pullOldWorld (v : PCWorld) : PCWorld := fun a => v (oldAtom a)

/-- Truth commutes exactly with the fixed atom injection. -/
@[simp] lemma holds_liftSentence_iff (v : PCWorld) (phi : Sentence) :
    v.Holds (liftSentence phi) ↔ (pullOldWorld v).Holds phi := by
  induction phi with
  | atom a => rfl
  | falsum => rfl
  | imp phi psi ihphi ihpsi => exact imp_congr ihphi ihpsi
  | and phi psi ihphi ihpsi => exact and_congr ihphi ihpsi
  | or phi psi ihphi ihpsi => exact or_congr ihphi ihpsi

/-- The fixed old-language copy of a threshold presentation. -/
def liftLUV (X : LUV) : LUV where
  gt r := liftSentence (X.gt r)

/-- World-side LUV values are invariant under the fixed representation change. -/
@[simp] lemma liftLUV_valuesAt_iff (v : PCWorld) (X : LUV) (x : ℝ) :
    v.ValuesAt (liftLUV X) x ↔ (pullOldWorld v).ValuesAt X x := by
  simp only [PCWorld.ValuesAt, liftLUV, holds_liftSentence_iff]

/-- Rename every stage of a process into the fixed old-language namespace. -/
def liftDP (DP : DeductiveProcess) : DeductiveProcess where
  D n := (DP.D n).image liftSentence
  mono n phi hphi := by
    rw [Finset.mem_image] at hphi ⊢
    obtain ⟨psi, hpsi, rfl⟩ := hphi
    exact ⟨psi, DP.mono n hpsi, rfl⟩

/-- Finite-stage consistency transfers exactly through the fixed renaming. -/
lemma consistentWith_liftDP_iff (v : PCWorld) (DP : DeductiveProcess) (n : ℕ) :
    v.ConsistentWith ((liftDP DP).D n) ↔
      (pullOldWorld v).ConsistentWith (DP.D n) := by
  constructor
  · intro hv phi hphi
    exact (holds_liftSentence_iff v phi).mp
      (hv _ (Finset.mem_image.mpr ⟨phi, hphi, rfl⟩))
  · intro hv phi hphi
    change phi ∈ (DP.D n).image liftSentence at hphi
    rw [Finset.mem_image] at hphi
    obtain ⟨psi, hpsi, rfl⟩ := hphi
    exact (holds_liftSentence_iff v psi).mpr (hv psi hpsi)

/-- Completed-theory consistency transfers exactly through the fixed renaming. -/
lemma consistentWithTheory_liftDP_iff (v : PCWorld) (DP : DeductiveProcess) :
    v.ConsistentWithTheory (liftDP DP) ↔
      (pullOldWorld v).ConsistentWithTheory DP := by
  simp only [PCWorld.ConsistentWithTheory, consistentWith_liftDP_iff]

/-! ## Vocabulary disjointness -/

/-- The established theorem/event vocabulary does not use the reserved old-copy tag. -/
lemma eventAtom_atomCodes_ne_oldLanguageTag (e : ℕ) :
    ∀ a ∈ sentenceAtomCodes (eventAtom e), a.unpair.1 ≠ oldLanguageTag := by
  intro a ha
  rcases h : e.unpair.1 with _ | _ | _ | _ | _ | _ | m
  all_goals simp only [eventAtom, h, sentenceAtomCodes_neg] at ha
  · exact fun hc => by
      simp [sentenceAtomCodes_computationClaimSentence _ a ha, haltingClaim,
        ComputationClaimKind.godelCode, oldLanguageTag] at hc
  · exact fun hc => by
      simp [sentenceAtomCodes_computationClaimSentence _ a ha, haltingClaim,
        ComputationClaimKind.godelCode, oldLanguageTag] at hc
  · exact fun hc => by
      simp [sentenceAtomCodes_computationClaimSentence _ a ha, boundedHaltingClaim,
        ComputationClaimKind.godelCode, oldLanguageTag] at hc
  · exact fun hc => by
      simp [sentenceAtomCodes_computationClaimSentence _ a ha, boundedHaltingClaim,
        ComputationClaimKind.godelCode, oldLanguageTag] at hc
  · exact fun hc => by
      simp [sentenceAtomCodes_quoteAtom _ a ha, oldLanguageTag] at hc
  · exact fun hc => by
      simp [sentenceAtomCodes_quoteAtom _ a ha, oldLanguageTag] at hc
  · simp at ha

lemma theoremDP_oldLanguageFresh (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T]
    (k : ℕ) (phi : Sentence) (hphi : phi ∈ (theoremDP T).D k) :
    ∀ a ∈ sentenceAtomCodes phi, a.unpair.1 ≠ oldLanguageTag := by
  simp only [theoremDP, theoremStage, Finset.mem_image, Finset.mem_filter,
    Finset.mem_range] at hphi
  obtain ⟨e, _, rfl⟩ := hphi
  exact eventAtom_atomCodes_ne_oldLanguageTag e

/-! ## Executable syntax lift -/

private def publicBotCode : ℕ := Encodable.encode (⊥ : Sentence)

private lemma encode_sentence_eq_toNat (phi : Sentence) :
    Encodable.encode phi = LO.Propositional.Formula.toNat phi := rfl

/-- Numeric implementation of `liftSentence`.  Invalid codes receive the harmless
sentence `⊥`; the fixed process only calls this on certified sentence codes. -/
def liftSentenceCode : ℕ → ℕ
  | 0 => publicBotCode
  | e + 1 =>
      let tag := e.unpair.1
      let payload := e.unpair.2
      if tag = 0 then publicBotCode
      else if tag = 1 then Nat.pair 1 (oldAtom payload) + 1
      else if tag = 2 then Nat.pair 2
        (Nat.pair (liftSentenceCode payload.unpair.1)
          (liftSentenceCode payload.unpair.2)) + 1
      else if tag = 3 then Nat.pair 3
        (Nat.pair (liftSentenceCode payload.unpair.1)
          (liftSentenceCode payload.unpair.2)) + 1
      else if tag = 4 then Nat.pair 4
        (Nat.pair (liftSentenceCode payload.unpair.1)
          (liftSentenceCode payload.unpair.2)) + 1
      else publicBotCode
termination_by n => n
decreasing_by
  all_goals
    exact Nat.lt_succ_iff.mpr <| le_trans
      (by first | exact Nat.unpair_left_le _ | exact Nat.unpair_right_le _)
      (Nat.unpair_right_le _)

@[simp] lemma liftSentenceCode_spec (phi : Sentence) :
    liftSentenceCode (Encodable.encode phi) =
      Encodable.encode (liftSentence phi) := by
  induction phi <;>
    simp_all [encode_sentence_eq_toNat, liftSentenceCode, liftSentence,
      Formula.subst, oldAtom, publicBotCode, LO.Propositional.Formula.toNat]

private def liftSentenceCodeSucc (prior : List ℕ) (e : ℕ) : ℕ :=
  let tag := e.unpair.1
  let payload := e.unpair.2
  let left := prior.getD payload.unpair.1 publicBotCode
  let right := prior.getD payload.unpair.2 publicBotCode
  if tag = 0 then publicBotCode
  else if tag = 1 then Nat.pair 1 (oldAtom payload) + 1
  else if tag = 2 then Nat.pair 2 (Nat.pair left right) + 1
  else if tag = 3 then Nat.pair 3 (Nat.pair left right) + 1
  else if tag = 4 then Nat.pair 4 (Nat.pair left right) + 1
  else publicBotCode

private lemma liftSentenceCodeSucc_prim : Primrec₂ liftSentenceCodeSucc := by
  let tag : List ℕ × ℕ → ℕ := fun p => p.2.unpair.1
  let payload : List ℕ × ℕ → ℕ := fun p => p.2.unpair.2
  let left : List ℕ × ℕ → ℕ := fun p =>
    p.1.getD p.2.unpair.2.unpair.1 publicBotCode
  let right : List ℕ × ℕ → ℕ := fun p =>
    p.1.getD p.2.unpair.2.unpair.2 publicBotCode
  have htag : Primrec tag := Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)
  have hpayload : Primrec payload := Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)
  have hleft : Primrec left := (Primrec.list_getD publicBotCode).comp Primrec.fst
    (Primrec.fst.comp (Primrec.unpair.comp hpayload))
  have hright : Primrec right := (Primrec.list_getD publicBotCode).comp Primrec.fst
    (Primrec.snd.comp (Primrec.unpair.comp hpayload))
  have pairSucc (k : ℕ) (x : List ℕ × ℕ → ℕ) (hx : Primrec x) :
      Primrec fun p => Nat.pair k (x p) + 1 :=
    (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const k) hx)).of_eq fun _ => rfl
  have hbinary (k : ℕ) : Primrec fun p =>
      Nat.pair k (Nat.pair (left p) (right p)) + 1 :=
    pairSucc k _ (Primrec₂.natPair.comp hleft hright)
  have hatom : Primrec fun p : List ℕ × ℕ =>
      Nat.pair 1 (oldAtom (payload p)) + 1 := by
    exact pairSucc 1 _
      (Primrec₂.natPair.comp (Primrec.const oldLanguageTag) hpayload)
  have htagEq (k : ℕ) : PrimrecPred fun p : List ℕ × ℕ => tag p = k :=
    Primrec.eq.comp htag (Primrec.const k)
  have h4 := Primrec.ite (htagEq 4) (hbinary 4) (Primrec.const publicBotCode)
  have h3 := Primrec.ite (htagEq 3) (hbinary 3) h4
  have h2 := Primrec.ite (htagEq 2) (hbinary 2) h3
  have h1 := Primrec.ite (htagEq 1) hatom h2
  exact (Primrec.ite (htagEq 0) (Primrec.const publicBotCode) h1).to₂.of_eq
    fun prior e => by
      simp only [liftSentenceCodeSucc, tag, payload, left, right]

private def liftSentenceCodeStep (prior : List ℕ) : ℕ :=
  prior.length.casesOn publicBotCode (liftSentenceCodeSucc prior)

private lemma liftSentenceCodeStep_prim : Primrec liftSentenceCodeStep := by
  exact (Primrec.nat_casesOn Primrec.list_length (Primrec.const publicBotCode)
    liftSentenceCodeSucc_prim).of_eq fun prior => by
      simp only [liftSentenceCodeStep]

private lemma liftSentenceCodeHistory_getD {n k : ℕ} (hk : k < n) :
    ((List.range n).map liftSentenceCode).getD k publicBotCode =
      liftSentenceCode k := by
  have hzero : liftSentenceCode 0 = publicBotCode := by
    simp [liftSentenceCode]
  rw [← hzero, List.getD_map]
  simp [hk]

private lemma liftSentenceCodeStep_history (n : ℕ) :
    liftSentenceCodeStep ((List.range n).map liftSentenceCode) =
      liftSentenceCode n := by
  cases n with
  | zero => simp [liftSentenceCodeStep, liftSentenceCode]
  | succ e =>
      let payload := e.unpair.2
      have hleft : payload.unpair.1 < e + 1 := Nat.lt_succ_iff.mpr <|
        le_trans (Nat.unpair_left_le _) (Nat.unpair_right_le _)
      have hright : payload.unpair.2 < e + 1 := Nat.lt_succ_iff.mpr <|
        le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le _)
      simp only [liftSentenceCodeStep, List.length_map, List.length_range]
      by_cases h2 : e.unpair.1 = 2
      · simp only [liftSentenceCodeSucc, h2, ↓reduceIte]
        rw [liftSentenceCode]
        simp only [h2, ↓reduceIte]
        rw [liftSentenceCodeHistory_getD hleft,
          liftSentenceCodeHistory_getD hright]
      by_cases h3 : e.unpair.1 = 3
      · simp only [liftSentenceCodeSucc, h3, ↓reduceIte]
        rw [liftSentenceCode]
        simp only [h3, ↓reduceIte]
        rw [liftSentenceCodeHistory_getD hleft,
          liftSentenceCodeHistory_getD hright]
      by_cases h4 : e.unpair.1 = 4
      · simp only [liftSentenceCodeSucc, h4, ↓reduceIte]
        rw [liftSentenceCode]
        simp only [h4, ↓reduceIte]
        rw [liftSentenceCodeHistory_getD hleft,
          liftSentenceCodeHistory_getD hright]
      · simp [liftSentenceCodeSucc, liftSentenceCode, h2, h3, h4]

/-- The fixed sentence renaming is primitive recursive on Foundation's sentence type. -/
lemma liftSentenceCode_prim : Primrec liftSentenceCode := by
  have hstep : Primrec₂ fun (_ : Unit) (prior : List ℕ) =>
      some (liftSentenceCodeStep prior) :=
    Primrec₂.option_some_iff.mpr (liftSentenceCodeStep_prim.comp Primrec₂.right)
  have hrec := Primrec.nat_strong_rec (fun (_ : Unit) n => liftSentenceCode n)
    hstep (fun _ n => by simpa using congrArg some (liftSentenceCodeStep_history n))
  exact (hrec.comp (Primrec.const ()) Primrec.id).of_eq fun _ => rfl

lemma liftSentence_primrec : Primrec liftSentence := by
  apply Primrec.encode_iff.mp
  exact (liftSentenceCode_prim.comp Primrec.encode).of_eq liftSentenceCode_spec

private lemma liftFinset_primrec :
    Primrec fun D : Finset Sentence => D.image liftSentence := by
  apply Primrec.encode_iff.mp
  have hlist : Primrec fun D : Finset Sentence =>
      (stageSort D).map liftSentence :=
    Primrec.list_map stageSort_prim
      (liftSentence_primrec.comp Primrec₂.right)
  have hcanonical : Primrec fun D : Finset Sentence =>
      ((sentenceDedup ((stageSort D).map liftSentence)).insertionSort
        sentenceCodeLE) :=
    sentenceInsertionSort_prim.comp (sentenceDedup_prim.comp hlist)
  exact (Primrec.encode.comp hcanonical).of_eq fun D => by
    rw [← encode_toFinset_eq]
    congr 1
    ext phi
    simp [stageSort]

/-- A named computation for the fixed renamed copy of any named computable process. -/
noncomputable def liftDPComputation {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) :
    DeductiveProcessComputation (liftDP DP) := by
  have hpart : Partrec fun n => base.code.eval n :=
    Nat.Partrec.Code.eval_part.comp (Computable.const base.code) Computable.id
  have hstageCode : Computable fun n => Encodable.encode (DP.D n) :=
    hpart.of_eq fun n => Part.eq_some_iff.mpr (base.code_spec n)
  have hstage : Computable fun n => DP.D n :=
    Computable.encode_iff.mp hstageCode
  have hlifted : Computable fun n =>
      Encodable.encode ((liftDP DP).D n) :=
    Computable.encode.comp (liftFinset_primrec.to_comp.comp hstage)
  let hex := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hlifted)
  let code := Classical.choose hex
  have hcode := Classical.choose_spec hex
  refine ⟨code, fun n => ?_⟩
  rw [hcode]
  exact Part.mem_some _

/-- Computability of the fixed old-language copy: the renamed copy of a named computable
process is computable.  A general fact about `liftDP` rather than a step of any one
construction, so it has no consumer in the repository. -/
lemma liftDP_computable {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) :
    ComputableDeductiveProcess (liftDP DP) :=
  (liftDPComputation base).toComputable

/-! ## Cut laws derived from the paper-facing valuedness premise -/

/-- Valuedness alone entails every rational downward-cut law needed by exact mesh
multiplication. -/
lemma liftLUV_holds_downward_of_valued {DP : DeductiveProcess} {X : LUV}
    (source_valued : ∀ v : PCWorld,
      v.ConsistentWithTheory DP → ∃ x, v.ValuesAt X x)
    {v : PCWorld} (hv : v.ConsistentWithTheory (liftDP DP))
    {r s : ℚ} (hrs : r < s) :
    v.Holds ((liftLUV X).gt s 🡒 (liftLUV X).gt r) := by
  obtain ⟨x, hx⟩ := source_valued (pullOldWorld v)
    ((consistentWithTheory_liftDP_iff v DP).mp hv)
  have hxlift : v.ValuesAt (liftLUV X) x :=
    (liftLUV_valuesAt_iff v X x).mpr hx
  intro hs
  by_cases hrx : (r : ℝ) < x
  · exact (hxlift.2.2 r).1 hrx
  · have hxs : x < (s : ℝ) := lt_of_le_of_lt (le_of_not_gt hrx) (by exact_mod_cast hrs)
    exact ((hxlift.2.2 s).2 hxs hs).elim

/-- The semantic downward law is eventually accepted by the executable checker, with no
caller-supplied cut certificate.  The stage-level form of
`liftLUV_holds_downward_of_valued`, stated for a registry that checks entailment at a stage;
no consumer in the repository takes this form. -/
lemma liftLUV_downward_eventually_stageEntails {DP : DeductiveProcess} {X : LUV}
    (source_valued : ∀ v : PCWorld,
      v.ConsistentWithTheory DP → ∃ x, v.ValuesAt X x)
    {r s : ℚ} (hrs : r < s) :
    ∃ k, stageEntails ((liftDP DP).D k)
      ((liftLUV X).gt s 🡒 (liftLUV X).gt r) = true := by
  apply DeductiveProcess.stageEntails_complete_of_semantic
  intro v hv
  exact liftLUV_holds_downward_of_valued source_valued hv hrs

end LogicalInduction

namespace LogicalInduction

open LO LO.Propositional

/-! ## The bounded entailment check -/

/-- One bounded certificate-free source-law check.  The packed witness contains emitter
fuel, base-program fuel, and base stage index. -/
def entailedSourceLawEvidenceAt {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) (schema job witness : ℕ) : Bool :=
  let emitterFuel := witness.unpair.1
  let baseFuel := witness.unpair.2.unpair.1
  let stage := witness.unpair.2.unpair.2
  match semanticSourceCutLawAtFuel schema job emitterFuel,
      base.stageAtFuel baseFuel stage with
  | some law, some D => stageEntails D law
  | _, _ => false

private def entailedSourceOptions :
    Option Sentence × Option (Finset Sentence) → Bool
  | (some law, some D) => stageEntails D law
  | _ => false

private lemma entailedSourceOptions_prim : Primrec entailedSourceOptions := by
  have hinnerRaw := Primrec.option_casesOn Primrec.snd (Primrec.const false)
      ((stageEntails_primrec.comp
        (Primrec₂.pair.comp₂ Primrec₂.right
          (Primrec.fst.comp₂ Primrec₂.left))).to₂.of_eq fun _ _ => rfl)
  have hinner1 : Primrec fun q : Sentence × Option (Finset Sentence) =>
      match q.2 with
      | some D => stageEntails D q.1
      | none => false := hinnerRaw.of_eq fun q => by cases q.2 <;> rfl
  have hinner : Primrec₂ fun (law : Sentence) (oD : Option (Finset Sentence)) =>
      match oD with
      | some D => stageEntails D law
      | none => false := hinner1.to₂
  exact (Primrec.option_casesOn Primrec.fst (Primrec.const false)
    (hinner.comp₂ Primrec₂.right
      (Primrec.snd.comp₂ Primrec₂.left))).of_eq fun p => by
      rcases p with ⟨olaw, oD⟩
      cases olaw <;> cases oD <;> rfl

set_option maxHeartbeats 4000000 in
lemma entailedSourceLawEvidenceAt_prim {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) :
    Primrec fun p : (ℕ × ℕ) × ℕ =>
      entailedSourceLawEvidenceAt base p.1.1 p.1.2 p.2 := by
  let P := (ℕ × ℕ) × ℕ
  have hschema : Primrec fun p : P => p.1.1 := Primrec.fst.comp Primrec.fst
  have hjob : Primrec fun p : P => p.1.2 := Primrec.snd.comp Primrec.fst
  have hemitterFuel : Primrec fun p : P => p.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)
  have htail : Primrec fun p : P => p.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)
  have hbaseFuel : Primrec fun p : P => p.2.unpair.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp htail)
  have hstage : Primrec fun p : P => p.2.unpair.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp htail)
  have hlaw : Primrec fun p : P =>
      semanticSourceCutLawAtFuel p.1.1 p.1.2 p.2.unpair.1 :=
    semanticSourceCutLawAtFuel_prim.comp
      ((hschema.pair hjob).pair hemitterFuel)
  have hbase : Primrec fun p : P =>
      base.stageAtFuel p.2.unpair.2.unpair.1 p.2.unpair.2.unpair.2 :=
    (processStageAtFuel_prim base).comp hbaseFuel hstage
  exact (entailedSourceOptions_prim.comp (hlaw.pair hbase)).of_eq fun p => by
    simp only [entailedSourceLawEvidenceAt]
    cases semanticSourceCutLawAtFuel p.1.1 p.1.2 p.2.unpair.1 <;>
      cases base.stageAtFuel p.2.unpair.2.unpair.1 p.2.unpair.2.unpair.2 <;> rfl

/-! ## Dovetailing over witnesses -/

/-- Dovetail the bounded evidence over all packed clock/stage witnesses. -/
def entailedSourceLawSeen {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) (schema job fuel : ℕ) : Bool :=
  (List.range (fuel + 1)).any fun witness =>
    entailedSourceLawEvidenceAt base schema job witness

lemma entailedSourceLawSeen_prim {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) :
    Primrec fun p : (ℕ × ℕ) × ℕ =>
      entailedSourceLawSeen base p.1.1 p.1.2 p.2 := by
  let P := (ℕ × ℕ) × ℕ
  have htest : Primrec₂ fun (p : P) (witness : ℕ) =>
      entailedSourceLawEvidenceAt base p.1.1 p.1.2 witness := by
    have hpack : Primrec fun q : P × ℕ =>
        ((q.1.1.1, q.1.1.2), q.2) :=
      ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).pair Primrec.snd
    exact ((entailedSourceLawEvidenceAt_prim base).comp hpack).to₂
  exact listRangeAny_prim Primrec.snd htest

lemma entailedSourceLawSeen_iff {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) (schema job fuel : ℕ) :
    entailedSourceLawSeen base schema job fuel = true ↔
      ∃ witness ≤ fuel,
        entailedSourceLawEvidenceAt base schema job witness = true := by
  rw [entailedSourceLawSeen, List.any_eq_true]
  simp only [List.mem_range, Nat.lt_add_one_iff]

lemma entailedSourceLawSeen_mono {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) {schema job fuel fuel' : ℕ}
    (hff : fuel ≤ fuel')
    (h : entailedSourceLawSeen base schema job fuel = true) :
    entailedSourceLawSeen base schema job fuel' = true := by
  obtain ⟨w, hw, he⟩ := (entailedSourceLawSeen_iff base schema job fuel).1 h
  exact (entailedSourceLawSeen_iff base schema job fuel').2
    ⟨w, hw.trans hff, he⟩

/-! ## Soundness and completeness of the gate -/

/-- Accepted evidence is semantically sound in every completed base world. -/
lemma entailedSourceLawEvidenceAt_sound {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) {schema job witness : ℕ}
    (h : entailedSourceLawEvidenceAt base schema job witness = true) :
    ∃ law,
      semanticSourceCutLawAtFuel schema job witness.unpair.1 = some law ∧
      ∀ v : PCWorld, v.ConsistentWithTheory DP → v.Holds law := by
  unfold entailedSourceLawEvidenceAt at h
  cases hlaw : semanticSourceCutLawAtFuel schema job witness.unpair.1 with
  | none => simp [hlaw] at h
  | some law =>
      cases hstage : base.stageAtFuel witness.unpair.2.unpair.1
          witness.unpair.2.unpair.2 with
      | none => simp [hlaw, hstage] at h
      | some D =>
          refine ⟨law, rfl, fun v hv => ?_⟩
          have hD : D = DP.D witness.unpair.2.unpair.2 :=
            base.stageAtFuel_sound hstage
          exact (stageEntails_eq_true_iff D law).1 (by simpa [hlaw, hstage] using h)
            v (by simpa [hD] using hv witness.unpair.2.unpair.2)

/-- Any emitted source law which is a completed-base consequence is eventually admitted.
No proof object or source-specific process is supplied to the checker. -/
lemma entailedSourceLawSeen_eventually {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) {schema job : ℕ} {law : Sentence}
    (hemit : ∃ emitterFuel,
      semanticSourceCutLawAtFuel schema job emitterFuel = some law)
    (hsemantic : ∀ v : PCWorld,
      v.ConsistentWithTheory DP → v.Holds law) :
    ∃ fuel, entailedSourceLawSeen base schema job fuel = true := by
  obtain ⟨emitterFuel, hemit⟩ := hemit
  obtain ⟨stage, hentails⟩ :=
    DeductiveProcess.stageEntails_complete_of_semantic DP law hsemantic
  obtain ⟨baseFuel, hstage⟩ := base.stageAtFuel_complete stage
  let witness := Nat.pair emitterFuel (Nat.pair baseFuel stage)
  refine ⟨witness, (entailedSourceLawSeen_iff base schema job witness).2
    ⟨witness, le_rfl, ?_⟩⟩
  simp [entailedSourceLawEvidenceAt, witness, hemit, hstage, hentails]

/-! ## Finite coherent-source prefixes

Exact product consistency uses only freshness and pairwise downward closure.  Bounds are
provided by the `ValuesAt` hypotheses at the point where multiplication is reflected. -/

/-- Pairwise downward checks for one source index and one left threshold. -/
def entailedSourceDownwardPrefixValidAtFuel {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP)
    (schema limit fuel n zr : ℕ) : Bool :=
  (List.range (limit + 1)).all fun zs =>
    let r := decodedQuotationRat zr
    let s := decodedQuotationRat zs
    if r < s then
      entailedSourceLawSeen base schema (sourceCutDownwardJob n r s) fuel
    else true

/-- Freshness and all downward checks for one threshold query. -/
def entailedSourceThresholdPrefixValidAtFuel {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP)
    (schema limit fuel n zr : ℕ) : Bool :=
  semanticSourceFreshSeen schema n zr fuel &&
    entailedSourceDownwardPrefixValidAtFuel base schema limit fuel n zr

/-- All executable evidence required to expose query indices at most `limit`. -/
def entailedSourcePrefixValidAtFuel {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) (schema limit fuel : ℕ) : Bool :=
  (List.range (limit + 1)).all fun n =>
    (List.range (limit + 1)).all fun zr =>
      entailedSourceThresholdPrefixValidAtFuel base schema limit fuel n zr

attribute [local irreducible] entailedSourceLawSeen

set_option maxHeartbeats 8000000 in
lemma entailedSourceDownwardPrefixValidAtFuel_prim {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) :
    Primrec fun p : ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) =>
      entailedSourceDownwardPrefixValidAtFuel base
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
        entailedSourceLawSeen base p.1.1.1.1
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
    have hseen : Primrec fun q : Q => entailedSourceLawSeen base q.1.1.1.1.1
        (sourceCutDownwardJob q.1.1.2 (decodedQuotationRat q.1.2)
          (decodedQuotationRat q.2)) q.1.1.1.2 :=
      (entailedSourceLawSeen_prim base).comp hpack
    have hlt : PrimrecPred fun q : Q =>
        decodedQuotationRat q.1.2 < decodedQuotationRat q.2 :=
      (ratLE_prim.comp hs (hr.comp Primrec.fst)).not.of_eq fun _ => by simp [not_le]
    exact (Primrec.ite hlt hseen (Primrec.const true)).to₂
  exact listRangeAll_prim hlimit htest

lemma entailedSourceThresholdPrefixValidAtFuel_prim {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) :
    Primrec fun p : ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) =>
      entailedSourceThresholdPrefixValidAtFuel base
        p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.1.2 p.2 := by
  let P := ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ)
  have hfreshPack : Primrec fun p : P =>
      (((p.1.1.1.1, p.1.2), p.2), p.1.1.2) :=
    (((Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))).pair
      (Primrec.snd.comp Primrec.fst)).pair Primrec.snd).pair
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have hfresh : Primrec fun p : P =>
      semanticSourceFreshSeen p.1.1.1.1 p.1.2 p.2 p.1.1.2 :=
    semanticSourceFreshSeen_prim.comp hfreshPack
  have hdown := entailedSourceDownwardPrefixValidAtFuel_prim base
  exact ((Primrec.dom_bool₂ (· && ·)).comp hfresh hdown).of_eq fun _ => rfl

set_option maxHeartbeats 2000000 in
lemma entailedSourcePrefixValidAtFuel_prim {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) :
    Primrec fun p : (ℕ × ℕ) × ℕ =>
      entailedSourcePrefixValidAtFuel base p.1.1 p.1.2 p.2 := by
  let P := (ℕ × ℕ) × ℕ
  have hlimit : Primrec fun p : P => p.1.2 := Primrec.snd.comp Primrec.fst
  have hinner : Primrec₂ fun (p : P) (n : ℕ) =>
      (List.range (p.1.2 + 1)).all fun zr =>
        entailedSourceThresholdPrefixValidAtFuel base p.1.1 p.1.2 p.2 n zr := by
    let Q := P × ℕ
    have hlimitQ : Primrec fun q : Q => q.1.1.2 := hlimit.comp Primrec.fst
    have htest : Primrec₂ fun (q : Q) (zr : ℕ) =>
        entailedSourceThresholdPrefixValidAtFuel base
          q.1.1.1 q.1.1.2 q.1.2 q.2 zr := by
      have hpack : Primrec fun z : Q × ℕ =>
          ((((z.1.1.1.1, z.1.1.1.2), z.1.1.2), z.1.2), z.2) :=
        (((((Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))).pair
          (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))).pair
          (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).pair
          (Primrec.snd.comp Primrec.fst)).pair Primrec.snd)
      exact ((entailedSourceThresholdPrefixValidAtFuel_prim base).comp hpack).to₂.of_eq
        fun _ _ => rfl
    exact (listRangeAll_prim hlimitQ htest).to₂
  exact listRangeAll_prim hlimit hinner

/-! ## Prefix accessors and clock monotonicity -/

/-- Prefix validity exposes freshness for every admitted source query: the accessor for the
freshness conjunct, paired with `entailedSourcePrefixValidAtFuel_downward` below. -/
lemma entailedSourcePrefixValidAtFuel_fresh {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) {schema limit fuel n z : ℕ}
    (hvalid : entailedSourcePrefixValidAtFuel base schema limit fuel = true)
    (hn : n ≤ limit) (hz : z ≤ limit) :
    semanticSourceFreshSeen schema n z fuel = true := by
  rw [entailedSourcePrefixValidAtFuel, List.all_eq_true] at hvalid
  have h := List.all_eq_true.mp (hvalid n (by simp [hn])) z (by simp [hz])
  rw [entailedSourceThresholdPrefixValidAtFuel] at h
  simp only [Bool.and_eq_true] at h
  exact h.1

lemma entailedSourcePrefixValidAtFuel_downward {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) {schema limit fuel n zr zs : ℕ}
    (hvalid : entailedSourcePrefixValidAtFuel base schema limit fuel = true)
    (hn : n ≤ limit) (hzr : zr ≤ limit) (hzs : zs ≤ limit)
    (hrs : decodedQuotationRat zr < decodedQuotationRat zs) :
    entailedSourceLawSeen base schema
      (sourceCutDownwardJob n (decodedQuotationRat zr) (decodedQuotationRat zs)) fuel = true := by
  rw [entailedSourcePrefixValidAtFuel, List.all_eq_true] at hvalid
  have h := List.all_eq_true.mp (hvalid n (by simp [hn])) zr (by simp [hzr])
  rw [entailedSourceThresholdPrefixValidAtFuel] at h
  simp only [Bool.and_eq_true] at h
  have hdown := h.2
  rw [entailedSourceDownwardPrefixValidAtFuel, List.all_eq_true] at hdown
  simpa [hrs] using hdown zs (by simp [hzs])

lemma entailedSourceDownwardPrefixValidAtFuel_mono {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP)
    {schema limit n zr fuel fuel' : ℕ} (hff : fuel ≤ fuel')
    (h : entailedSourceDownwardPrefixValidAtFuel base schema limit fuel n zr = true) :
    entailedSourceDownwardPrefixValidAtFuel base schema limit fuel' n zr = true := by
  rw [entailedSourceDownwardPrefixValidAtFuel, List.all_eq_true] at h ⊢
  intro zs hzs
  by_cases hrs : decodedQuotationRat zr < decodedQuotationRat zs
  · simpa [hrs] using entailedSourceLawSeen_mono base hff (by simpa [hrs] using h zs hzs)
  · simp [hrs]

lemma entailedSourceThresholdPrefixValidAtFuel_mono {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP)
    {schema limit n zr fuel fuel' : ℕ} (hff : fuel ≤ fuel')
    (h : entailedSourceThresholdPrefixValidAtFuel base schema limit fuel n zr = true) :
    entailedSourceThresholdPrefixValidAtFuel base schema limit fuel' n zr = true := by
  rw [entailedSourceThresholdPrefixValidAtFuel] at h ⊢
  simp only [Bool.and_eq_true] at h ⊢
  exact ⟨semanticSourceFreshSeen_mono hff h.1,
    entailedSourceDownwardPrefixValidAtFuel_mono base hff h.2⟩

lemma entailedSourcePrefixValidAtFuel_mono {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP)
    {schema limit fuel fuel' : ℕ} (hff : fuel ≤ fuel')
    (h : entailedSourcePrefixValidAtFuel base schema limit fuel = true) :
    entailedSourcePrefixValidAtFuel base schema limit fuel' = true := by
  rw [entailedSourcePrefixValidAtFuel, List.all_eq_true] at h ⊢
  intro n hn
  rw [List.all_eq_true]
  intro zr hzr
  exact entailedSourceThresholdPrefixValidAtFuel_mono base hff
    (List.all_eq_true.mp (h n hn) zr hzr)

/-! ## Soundness in the canonical extension world -/

/-- Entailment-gated downward evidence is sound in the canonical source extension. -/
lemma semanticSourceExtensionWorld_downward_of_entailedSeen {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) (v₀ : PCWorld)
    (hv₀ : v₀.ConsistentWithTheory DP) {schema n fuel : ℕ} {r s : ℚ}
    (hsource : schema.unpair.1 = 0) (hrs : r < s)
    (hseen : entailedSourceLawSeen base schema
      (sourceCutDownwardJob n r s) fuel = true) :
    (semanticSourceExtensionWorld v₀).Holds
      (semanticPrimeSentence schema (Nat.pair n (Encodable.encode s))) →
    (semanticSourceExtensionWorld v₀).Holds
      (semanticPrimeSentence schema (Nat.pair n (Encodable.encode r))) := by
  obtain ⟨witness, _, hevidence⟩ :=
    (entailedSourceLawSeen_iff base schema (sourceCutDownwardJob n r s) fuel).1 hseen
  obtain ⟨law, hlaw, hsemantic⟩ := entailedSourceLawEvidenceAt_sound base hevidence
  obtain ⟨φr, φs, hφr, hφs, hfr, hfs, rfl⟩ :=
    semanticSourceCutLawAtFuel_downward_spec hrs hlaw
  have himp : v₀.Holds (φs 🡒 φr) := hsemantic v₀ hv₀
  intro hs
  have hs₀ : v₀.Holds φs :=
    (semanticSourceExtensionWorld_leaf_iff v₀ schema _ witness.unpair.1
      hsource hφs hfs).mp hs
  exact (semanticSourceExtensionWorld_leaf_iff v₀ schema _ witness.unpair.1
    hsource hφr hfr).mpr (himp hs₀)

/-- Pointwise eventual threshold admission combines into one finite-prefix clock. -/
lemma entailedSourcePrefix_eventually_of_threshold
    {DP : DeductiveProcess} (base : DeductiveProcessComputation DP)
    (schema limit : ℕ)
    (heventual : ∀ n zr, ∃ fuel,
      entailedSourceThresholdPrefixValidAtFuel base schema limit fuel n zr = true) :
    ∃ fuel, entailedSourcePrefixValidAtFuel base schema limit fuel = true := by
  let row : ℕ → ℕ → Bool := fun n fuel =>
    (List.range (limit + 1)).all fun zr =>
      entailedSourceThresholdPrefixValidAtFuel base schema limit fuel n zr
  have rowMono : ∀ n {fuel fuel'}, fuel ≤ fuel' → row n fuel = true →
      row n fuel' = true := by
    intro n fuel fuel' hff h
    change (List.range (limit + 1)).all (fun zr =>
      entailedSourceThresholdPrefixValidAtFuel base schema limit fuel n zr) = true at h
    change (List.range (limit + 1)).all (fun zr =>
      entailedSourceThresholdPrefixValidAtFuel base schema limit fuel' n zr) = true
    rw [List.all_eq_true] at h ⊢
    intro zr hzr
    exact entailedSourceThresholdPrefixValidAtFuel_mono base hff (h zr hzr)
  have rowEventually : ∀ n ∈ List.range (limit + 1),
      ∃ fuel, row n fuel = true := by
    intro n _
    exact listAll_eventually_of_mono
      (l := List.range (limit + 1))
      (fun zr _ _ hff h => entailedSourceThresholdPrefixValidAtFuel_mono base hff h)
      (fun zr _ => heventual n zr)
  obtain ⟨fuel, hfuel⟩ := listAll_eventually_of_mono rowMono rowEventually
  refine ⟨fuel, ?_⟩
  rw [entailedSourcePrefixValidAtFuel, List.all_eq_true]
  exact List.all_eq_true.mp hfuel

end LogicalInduction

namespace LogicalInduction

open LO LO.Propositional

-- Both registry predicates are `List.range` dovetails.
-- The proofs below reach them only through their monotonicity and characterization
-- lemmas, so keeping the ranges opaque stops `simp` unfolding a dovetail inside the
-- eventual-validity inductions.
attribute [local irreducible] entailedSourceLawSeen
attribute [local irreducible] entailedSourcePrefixValidAtFuel

/-! ## The lifted source sentence and its query ABI -/

/-- The source sentence represented at an arbitrary rational query.  Negative thresholds
use `⊤`; nonnegative thresholds are the fixed old-language copy of the caller's source. -/
def liftedRpnSourceSentence (X : ℕ → LUV) (n : ℕ) (r : ℚ) : Sentence :=
  if r < 0 then ⊤ else liftSentence ((X n).gt r)

/-- Convert a canonical rational query to the `⟨n,⟨k,i⟩⟩` ABI of
`RpnThresholdCodeSeq`. -/
def liftedRpnMeshQuery (input : ℕ) : ℕ :=
  let n := input.unpair.1
  let r := decodedQuotationRat input.unpair.2
  let z := Encodable.encode r
  Nat.pair n (Nat.pair z.unpair.2 z.unpair.1.div2)

/-- The query conversion is primitive recursive. -/
lemma liftedRpnMeshQuery_prim : Primrec liftedRpnMeshQuery := by
  have hn : Primrec fun input : ℕ => input.unpair.1 := Primrec.fst.comp Primrec.unpair
  have hz : Primrec fun input : ℕ => Encodable.encode
      (decodedQuotationRat input.unpair.2) :=
    Primrec.encode.comp (decodedQuotationRat_prim.comp
      (Primrec.snd.comp Primrec.unpair))
  have hk : Primrec fun input : ℕ =>
      (Encodable.encode (decodedQuotationRat input.unpair.2)).unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp hz)
  have hi : Primrec fun input : ℕ =>
      (Encodable.encode (decodedQuotationRat input.unpair.2)).unpair.1.div2 :=
    Primrec.nat_div2.comp (Primrec.fst.comp (Primrec.unpair.comp hz))
  exact (Primrec₂.natPair.comp hn (Primrec₂.natPair.comp hk hi)).of_eq fun _ => rfl

private lemma nonnegative_rat_mesh (r : ℚ) (hr : 0 ≤ r) :
    ((r.num.natAbs : ℚ) / (r.den : ℚ)) = r := by
  have hn : 0 ≤ r.num := Rat.num_nonneg.mpr hr
  rw [Nat.cast_natAbs, abs_of_nonneg hn]
  exact Rat.num_div_den r

/-- **The ABI specification**: at a nonnegative query the conversion preserves the LUV
index and the rational `i/k` it names. -/
lemma liftedRpnMeshQuery_spec (n : ℕ) (r : ℚ) (hr : 0 ≤ r) :
    (liftedRpnMeshQuery (Nat.pair n (Encodable.encode r))).unpair.1 = n ∧
    (((liftedRpnMeshQuery (Nat.pair n (Encodable.encode r))).unpair.2.unpair.2 : ℚ) /
      ((liftedRpnMeshQuery (Nat.pair n (Encodable.encode r))).unpair.2.unpair.1 : ℚ)) = r := by
  constructor
  · simp [liftedRpnMeshQuery]
  · simp only [liftedRpnMeshQuery, Nat.unpair_pair, decodedQuotationRat_encode]
    rw [encode_rat_eq]
    simp only [Nat.unpair_pair]
    have hn : 0 ≤ r.num := Rat.num_nonneg.mpr hr
    have hencode : (Encodable.encode r.num).div2 = r.num.natAbs := by
      obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le hn
      rw [hm]
      simp [encode_int_natCast]
    rw [hencode]
    exact nonnegative_rat_mesh r hr

private def liftedRpnSourceOutput (X : ℕ → LUV) (input : ℕ) : ℕ :=
  if decodedQuotationRat input.unpair.2 < 0 then
    Encodable.encode (⊤ : Sentence)
  else
    liftSentenceCode (Encodable.encode ((X (liftedRpnMeshQuery input).unpair.1).gt
      (((liftedRpnMeshQuery input).unpair.2.unpair.2 : ℚ) /
        ((liftedRpnMeshQuery input).unpair.2.unpair.1 : ℚ))))

private lemma liftedRpnSourceOutput_computable {X : ℕ → LUV}
    (hX : LUV.RpnThresholdCodeSeq X) : Computable (liftedRpnSourceOutput X) := by
  let sourceOutput : ℕ → ℕ := fun m => Encodable.encode ((X m.unpair.1).gt
    ((m.unpair.2.unpair.2 : ℚ) / (m.unpair.2.unpair.1 : ℚ)))
  have hpart : Partrec fun m => (rpnThresholdSourceCode hX).eval m :=
    Nat.Partrec.Code.eval_part.comp
      (Computable.const (rpnThresholdSourceCode hX)) Computable.id
  have hsource : Computable sourceOutput :=
    hpart.of_eq fun m => Part.eq_some_iff.mpr (rpnThresholdSourceCode_spec hX m)
  have hr : Primrec fun input : ℕ => decodedQuotationRat input.unpair.2 :=
    decodedQuotationRat_prim.comp (Primrec.snd.comp Primrec.unpair)
  have hneg : Computable fun input : ℕ => decide
      (decodedQuotationRat input.unpair.2 < 0) :=
    ((ratLE_prim.comp (Primrec.const 0) hr).not.of_eq fun _ => by simp [not_le]).decide.to_comp
  have hlift : Computable fun input : ℕ => liftSentenceCode
      (sourceOutput (liftedRpnMeshQuery input)) :=
    liftSentenceCode_prim.to_comp.comp
      (hsource.comp liftedRpnMeshQuery_prim.to_comp)
  exact (Computable.cond hneg (Computable.const (Encodable.encode (⊤ : Sentence)))
    hlift).of_eq fun input => by
      by_cases h : decodedQuotationRat input.unpair.2 < 0 <;>
        simp [liftedRpnSourceOutput, sourceOutput, h]

/-! ## The extracted emitter and its schema -/

/-- The total emitter program extracted from the caller's existing token-metered RPN
certificate.  The code is data inside a universal tag-`0` schema; the semantic process is
not specialized to `X`. -/
noncomputable def liftedRpnSourceCode {X : ℕ → LUV}
    (hX : LUV.RpnThresholdCodeSeq X) : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp
    (Partrec.nat_iff.mp (liftedRpnSourceOutput_computable hX)))

/-- **The emitter specification**: the extracted program emits the intended represented
sentence at every rational query. -/
lemma liftedRpnSourceCode_spec {X : ℕ → LUV}
    (hX : LUV.RpnThresholdCodeSeq X) (n : ℕ) (r : ℚ) :
    Encodable.encode (liftedRpnSourceSentence X n r) ∈
      (liftedRpnSourceCode hX).eval (Nat.pair n (Encodable.encode r)) := by
  have hcode := Classical.choose_spec (Nat.Partrec.Code.exists_code.mp
    (Partrec.nat_iff.mp (liftedRpnSourceOutput_computable hX)))
  rw [liftedRpnSourceCode, hcode]
  apply Part.mem_some_iff.mpr
  by_cases hr : r < 0
  · simp [liftedRpnSourceOutput, liftedRpnSourceSentence, hr]
  · have hr0 : 0 ≤ r := le_of_not_gt hr
    obtain ⟨hn, hmesh⟩ := liftedRpnMeshQuery_spec n r hr0
    simp only [liftedRpnSourceOutput, Nat.unpair_pair, decodedQuotationRat_encode,
      if_neg hr, liftedRpnSourceSentence]
    rw [liftSentenceCode_spec]
    rw [hn, hmesh]

/-- Self-describing tag-`0` schema for the derived emitter.  The second payload is a
harmless placeholder: entailment-gated admission never executes a source certificate. -/
noncomputable def liftedRpnSourceSchema {X : ℕ → LUV}
    (hX : LUV.RpnThresholdCodeSeq X) : ℕ :=
  semanticEmitterSchema (Nat.pair (Encodable.encode (liftedRpnSourceCode hX)) 0)

/-- The derived schema carries the source tag `0`. -/
@[simp] lemma liftedRpnSourceSchema_source {X : ℕ → LUV}
    (hX : LUV.RpnThresholdCodeSeq X) : (liftedRpnSourceSchema hX).unpair.1 = 0 := by
  simp [liftedRpnSourceSchema]

/-- The universal interpreter reads the extracted program back out of the schema. -/
@[simp] lemma liftedRpnSourceSchema_emitterCode {X : ℕ → LUV}
    (hX : LUV.RpnThresholdCodeSeq X) :
    semanticSourceEmitterCode (liftedRpnSourceSchema hX) = liftedRpnSourceCode hX := by
  simp [semanticSourceEmitterCode, liftedRpnSourceSchema, semanticEmitterSchema,
    semanticSourceSchema]

/-- Every derived source sentence is separated from the semantic extension namespace. -/
lemma liftedRpnSourceSentence_fresh (X : ℕ → LUV) (n : ℕ) (r : ℚ) :
    SemanticPrimeFreshSentence (liftedRpnSourceSentence X n r) := by
  by_cases hr : r < 0
  · simp [liftedRpnSourceSentence, hr, SemanticPrimeFreshSentence,
      sentenceAtomCodes_verum]
  · intro a ha
    rw [liftedRpnSourceSentence, if_neg hr, sentenceAtomCodes_liftSentence] at ha
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp ha
    have haold : (oldAtom b).unpair.1 = oldLanguageTag := by simp [oldAtom]
    simpa [haold, oldLanguageTag, semanticPrimeTag]

/-! ## Reflection through the universal interpreter -/

/-- Exact reflection of the internally lifted source through the one fixed universal
source interpreter. -/
lemma liftedRpnSource_reflected {X : ℕ → LUV} (hX : LUV.RpnThresholdCodeSeq X)
    (n : ℕ) (r : ℚ) (v : PCWorld)
    (hv : v.ConsistentWithTheory semanticSourceDP) :
    v.Holds (semanticPrimeSentence (liftedRpnSourceSchema hX)
      (Nat.pair n (Encodable.encode r))) ↔
      v.Holds (liftedRpnSourceSentence X n r) := by
  obtain ⟨fuel, heval⟩ := Nat.Partrec.Code.evaln_complete.mp
    (liftedRpnSourceCode_spec hX n r)
  apply semanticSourceSentenceAtFuel_reflected hv (liftedRpnSourceSchema hX)
    (Nat.pair n (Encodable.encode r)) fuel (liftedRpnSourceSchema_source hX)
  · rw [semanticSourceSentenceAtFuel, liftedRpnSourceSchema_emitterCode]
    rw [show Nat.Partrec.Code.evaln fuel (liftedRpnSourceCode hX)
      (Nat.pair n (Encodable.encode r)) =
        some (Encodable.encode (liftedRpnSourceSentence X n r)) from heval]
    simp
  · exact liftedRpnSourceSentence_fresh X n r

/-- Emission is monotone in the interpreter's fuel. -/
lemma semanticSourceSentenceAtFuel_mono {schema input fuel fuel' : ℕ}
    (hff : fuel ≤ fuel') {phi : Sentence}
    (h : semanticSourceSentenceAtFuel schema input fuel = some phi) :
    semanticSourceSentenceAtFuel schema input fuel' = some phi := by
  unfold semanticSourceSentenceAtFuel at h ⊢
  cases he : Nat.Partrec.Code.evaln fuel (semanticSourceEmitterCode schema) input with
  | none => simp [he] at h
  | some out =>
      have he' := Nat.Partrec.Code.evaln_mono hff (Option.mem_def.mpr he)
      rw [show Nat.Partrec.Code.evaln fuel' (semanticSourceEmitterCode schema) input =
        some out from he']
      simpa [he] using h

/-- Enough fuel eventually emits the represented sentence at any one query. -/
lemma liftedRpnSourceSentenceAtFuel_eventually {X : ℕ → LUV}
    (hX : LUV.RpnThresholdCodeSeq X) (n : ℕ) (r : ℚ) :
    ∃ fuel, semanticSourceSentenceAtFuel (liftedRpnSourceSchema hX)
      (Nat.pair n (Encodable.encode r)) fuel =
        some (liftedRpnSourceSentence X n r) := by
  obtain ⟨fuel, hfuel⟩ := evaln_decode_sentence_eventually
    (liftedRpnSourceCode hX) (Nat.pair n (Encodable.encode r))
    (liftedRpnSourceSentence X n r) (liftedRpnSourceCode_spec hX n r)
  refine ⟨fuel, ?_⟩
  simpa [semanticSourceSentenceAtFuel, liftedRpnSourceSchema_emitterCode] using hfuel

/-- Enough fuel eventually witnesses the freshness of the sentence at any one query. -/
lemma liftedRpnSourceFreshSeen_eventually {X : ℕ → LUV}
    (hX : LUV.RpnThresholdCodeSeq X) (n z : ℕ) :
    ∃ fuel, semanticSourceFreshSeen (liftedRpnSourceSchema hX) n z fuel = true := by
  obtain ⟨fuel, hemit⟩ := liftedRpnSourceSentenceAtFuel_eventually hX n
    (decodedQuotationRat z)
  exact ⟨fuel, (semanticSourceFreshSeen_iff _ _ _ _).2
    ⟨fuel, le_rfl, liftedRpnSourceSentence X n (decodedQuotationRat z), hemit,
      liftedRpnSourceSentence_fresh X n _⟩⟩

/-! ## Registry-prefix validity -/

/-- Enough fuel eventually witnesses one downward cut law `X n > s ⊢ X n > r` for `r < s`.
The hypotheses are the ones the registry gate carries: every `X n` is valued in every
world consistent with `DP`, and every world consistent with the base process is consistent
with the lifted copy of `DP`. -/
lemma liftedRpnSourceLawSeen_eventually {DP Base : DeductiveProcess}
    (base : DeductiveProcessComputation Base) {X : ℕ → LUV}
    (hX : LUV.RpnThresholdCodeSeq X)
    (source_valued : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      ∃ x, v.ValuesAt (X n) x)
    (base_lifted : ∀ v : PCWorld, v.ConsistentWithTheory Base →
      v.ConsistentWithTheory (liftDP DP))
    (n : ℕ) {r s : ℚ} (hrs : r < s) :
    ∃ fuel, entailedSourceLawSeen base (liftedRpnSourceSchema hX)
      (sourceCutDownwardJob n r s) fuel = true := by
  obtain ⟨fr, hfr⟩ := liftedRpnSourceSentenceAtFuel_eventually hX n r
  obtain ⟨fs, hfs⟩ := liftedRpnSourceSentenceAtFuel_eventually hX n s
  let emitterFuel := max fr fs
  have hfr' : semanticSourceSentenceAtFuel (liftedRpnSourceSchema hX)
      (Nat.pair n (Encodable.encode r)) emitterFuel =
        some (liftedRpnSourceSentence X n r) :=
    semanticSourceSentenceAtFuel_mono (by simp [emitterFuel]) hfr
  have hfs' : semanticSourceSentenceAtFuel (liftedRpnSourceSchema hX)
      (Nat.pair n (Encodable.encode s)) emitterFuel =
        some (liftedRpnSourceSentence X n s) :=
    semanticSourceSentenceAtFuel_mono (by simp [emitterFuel]) hfs
  let law := liftedRpnSourceSentence X n s 🡒 liftedRpnSourceSentence X n r
  have hemit : semanticSourceCutLawAtFuel (liftedRpnSourceSchema hX)
      (sourceCutDownwardJob n r s) emitterFuel = some law := by
    simp only [semanticSourceCutLawAtFuel, sourceCutDownwardJob, Nat.unpair_pair,
      if_neg (by decide : ¬(2 : ℕ) = 0), if_neg (by decide : ¬(2 : ℕ) = 1),
      decodedQuotationRat_encode, if_pos hrs]
    rw [hfr', hfs']
    change _ = some (liftedRpnSourceSentence X n s 🡒
      liftedRpnSourceSentence X n r)
    exact freshImpSourceSentence_eq_some_of_fresh
      (liftedRpnSourceSentence_fresh X n r)
      (liftedRpnSourceSentence_fresh X n s)
  apply entailedSourceLawSeen_eventually base ⟨emitterFuel, hemit⟩
  intro v hv
  by_cases hr : r < 0
  · simp only [law, liftedRpnSourceSentence, if_pos hr]
    intro _
    exact PCWorld.holds_top v
  · have hs : ¬s < 0 := by linarith
    simpa [law, liftedRpnSourceSentence, hr, hs, liftLUV] using
      (liftLUV_holds_downward_of_valued
        (X := X n) (source_valued n) (base_lifted v hv) hrs)

private lemma liftedListAll_eventually_of_mono {l : List ℕ}
    {test : ℕ → ℕ → Bool}
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

set_option maxHeartbeats 8000000 in
/-- **Prefix validity**: every finite registry prefix is eventually validated, which is
what the registry gate consumes to admit the lifted source as a certified factor. -/
lemma liftedRpnSourcePrefix_eventually_valid {DP Base : DeductiveProcess}
    (base : DeductiveProcessComputation Base) {X : ℕ → LUV}
    (hX : LUV.RpnThresholdCodeSeq X)
    (source_valued : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      ∃ x, v.ValuesAt (X n) x)
    (base_lifted : ∀ v : PCWorld, v.ConsistentWithTheory Base →
      v.ConsistentWithTheory (liftDP DP))
    (limit : ℕ) :
    ∃ fuel, entailedSourcePrefixValidAtFuel base
      (liftedRpnSourceSchema hX) limit fuel = true := by
  have thresholdEventually (n zr : ℕ) : ∃ fuel,
      entailedSourceThresholdPrefixValidAtFuel base
        (liftedRpnSourceSchema hX) limit fuel n zr = true := by
    obtain ⟨ffresh, hfresh⟩ := liftedRpnSourceFreshSeen_eventually hX n zr
    let test : ℕ → ℕ → Bool := fun zs fuel =>
      if decodedQuotationRat zr < decodedQuotationRat zs then
        entailedSourceLawSeen base (liftedRpnSourceSchema hX)
          (sourceCutDownwardJob n (decodedQuotationRat zr)
            (decodedQuotationRat zs)) fuel
      else true
    have htestMono : ∀ zs {fuel fuel'}, fuel ≤ fuel' → test zs fuel = true →
        test zs fuel' = true := by
      intro zs fuel fuel' hff h
      by_cases hrs : decodedQuotationRat zr < decodedQuotationRat zs
      · simpa [test, hrs] using entailedSourceLawSeen_mono base hff
          (by simpa [test, hrs] using h)
      · simp [test, hrs]
    have htestEventually : ∀ zs ∈ List.range (limit + 1),
        ∃ fuel, test zs fuel = true := by
      intro zs _
      by_cases hrs : decodedQuotationRat zr < decodedQuotationRat zs
      · obtain ⟨fuel, h⟩ := liftedRpnSourceLawSeen_eventually base hX
          source_valued base_lifted n hrs
        exact ⟨fuel, by simpa [test, hrs] using h⟩
      · exact ⟨0, by simp [test, hrs]⟩
    obtain ⟨fdown, hdown⟩ := liftedListAll_eventually_of_mono
      htestMono htestEventually
    let fuel := max ffresh fdown
    refine ⟨fuel, ?_⟩
    rw [entailedSourceThresholdPrefixValidAtFuel, Bool.and_eq_true]
    refine ⟨semanticSourceFreshSeen_mono (Nat.le_max_left _ _) hfresh, ?_⟩
    change (List.range (limit + 1)).all (fun zs =>
      if decodedQuotationRat zr < decodedQuotationRat zs then
        entailedSourceLawSeen base (liftedRpnSourceSchema hX)
          (sourceCutDownwardJob n (decodedQuotationRat zr)
            (decodedQuotationRat zs)) fdown
      else true) = true at hdown
    rw [entailedSourceDownwardPrefixValidAtFuel, List.all_eq_true]
    rw [List.all_eq_true] at hdown
    intro zs hzs
    exact htestMono zs (Nat.le_max_right _ _) (hdown zs hzs)
  exact entailedSourcePrefix_eventually_of_threshold base
    (liftedRpnSourceSchema hX) limit thresholdEventually

end LogicalInduction
