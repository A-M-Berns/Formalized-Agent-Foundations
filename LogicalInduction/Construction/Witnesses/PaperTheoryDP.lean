import LogicalInduction.Construction.Witnesses.PaperFirstOrderCompiler
import LogicalInduction.Construction.Witnesses.ComputationDP
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Coding
import Foundation.FirstOrder.Completeness.CounterModel

/-!
# A fixed public process for first-order theorems

This file connects Foundation's encoded proof system to the tag-`7` public-language
boundary.  The process is fixed by the arithmetic theory alone: it dovetails over every
encoded provable first-order proposition and publishes its prime decomposition.  In
particular, later source LUVs provide proof codes to this already-fixed process rather than
adding source-dependent axioms.
-/

namespace LogicalInduction

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open LO.Propositional

variable (T : ArithmeticTheory)

/-- The r.e. event predicate for the universal first-order theorem stream. -/
def paperTheoremFires [T.Δ₁] (formulaCode : ℕ) : Prop :=
  Bootstrapping.Provable T formulaCode

lemma paperTheoremFires_re [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1] :
    REPred (paperTheoremFires T) := by
  apply re_iff_sigma1.mpr
  change 𝚺₁-Predicate fun formulaCode : ℕ => Bootstrapping.Provable T formulaCode
  definability

/-- Decode the numeric compiler's output, with a harmless false default on impossible
malformed output. -/
def paperTheoremSentence (formulaCode : ℕ) : Sentence :=
  (Encodable.decode (α := Sentence) (paperPrimeDecomposeCode formulaCode)).getD ⊥

@[simp] lemma paperTheoremSentence_spec (φ : ArithmeticProposition) :
    paperTheoremSentence (Encodable.encode φ) = paperPrimeDecompose φ := by
  unfold paperTheoremSentence
  rw [show paperPrimeDecomposeCode (Encodable.encode φ) =
    Encodable.encode (paperPrimeDecompose φ) from paperPrimeDecomposeCode_spec φ]
  simp

lemma paperTheoremSentence_prim : Primrec paperTheoremSentence := by
  exact (Primrec.option_getD.comp
    (Primrec.decode.comp paperPrimeDecomposeCode_prim)
    (Primrec.const (⊥ : Sentence))).of_eq fun _ => rfl

/-- A partial-recursive semi-decider for the universal theorem events. -/
lemma exists_paperTheoremCode [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1] :
    ∃ code : Nat.Partrec.Code,
      ∀ formulaCode, (code.eval formulaCode).Dom ↔ paperTheoremFires T formulaCode := by
  obtain ⟨f, hf, hfP⟩ := REPred.iff'.mp (paperTheoremFires_re T)
  obtain ⟨code, hcode⟩ := Nat.Partrec.Code.exists_code.mp
    (Partrec.nat_iff.mp (hf.map (Computable.const (0 : ℕ)).to₂))
  refine ⟨code, fun formulaCode => ?_⟩
  rw [hcode]
  exact (hfP formulaCode).symm

/-! ## Assignment-level soundness

Foundation proof codes target `ArithmeticProposition`, whose free-variable type is `ℕ`.
The theorem process therefore uses the stronger and natural soundness fact that every
proved proposition is true under every assignment in every model of `T`.
-/

lemma derivation2_evalf_of_model
    {M : Type*} [Nonempty M] [Structure ℒₒᵣ M]
    (hT : M ↓[ℒₒᵣ] ⊧* T) {Γ : Finset ArithmeticProposition}
    (d : T ⟹₂ Γ) (f : ℕ → M) : ∃ φ ∈ Γ, φ.Evalf f := by
  rcases LO.FirstOrder.Derivation2.toProofData d with ⟨A, hA, b⟩
  obtain ⟨φ, hmem, htruth⟩ := LO.FirstOrder.Derivation.sound f b
  simp only [List.mem_append] at hmem
  rcases hmem with hΓ | hneg
  · exact ⟨φ, by simpa using hΓ, htruth⟩
  · exfalso
    have hex : ∃ ψ ∈ A, (ψ : ArithmeticProposition) = ∼φ := by
      simpa [LO.FirstOrder.Sequent.embed] using hneg
    rcases hex with ⟨ψ, hψ, hcoe⟩
    have hψT : ψ.Realize M := by
      exact hT.models _ (hA ψ hψ)
    have hnψ : ¬ψ.Realize M := by
      intro hψtrue
      have hcoetrue : (ψ : ArithmeticProposition).Evalf f := by
        simpa using hψtrue
      rw [hcoe] at hcoetrue
      have hnφ : ¬φ.Evalf f := by simpa using hcoetrue
      exact hnφ htruth
    exact hnψ hψT

lemma provable_proposition_evalf_of_model
    [T.Δ₁]
    {M : Type*} [Nonempty M] [Structure ℒₒᵣ M]
    (hT : M ↓[ℒₒᵣ] ⊧* T) (f : ℕ → M) {φ : ArithmeticProposition}
    (hφ : Bootstrapping.Provable T (Encodable.encode φ)) : φ.Evalf f := by
  have hquote : Bootstrapping.Provable T (⌜φ⌝ : ℕ) := by
    simpa [LO.FirstOrder.Semiformula.quote_eq_encode] using hφ
  have hsound : Nonempty (T ⟹₂ ({φ} : Finset ArithmeticProposition)) := by
    exact ⟨Bootstrapping.Provable.sound2 (T := T) hquote⟩
  rcases hsound with ⟨d⟩
  obtain ⟨ψ, hψ, htruth⟩ := derivation2_evalf_of_model T hT d f
  have : ψ = φ := by simpa using hψ
  simpa [this] using htruth

/-! ## The fixed dovetailed process -/

open Classical in
noncomputable def paperTheoremStage (code : Nat.Partrec.Code) (k : ℕ) : Finset Sentence :=
  ((Finset.range (k + 1)).filter
    (fun e => (Nat.Partrec.Code.evaln k code e).isSome = true)).image paperTheoremSentence

lemma paperTheoremStage_mono (code : Nat.Partrec.Code) (k : ℕ) :
    paperTheoremStage code k ⊆ paperTheoremStage code (k + 1) := by
  classical
  intro φ hφ
  simp only [paperTheoremStage, Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hφ ⊢
  obtain ⟨e, ⟨he, hsome⟩, rfl⟩ := hφ
  exact ⟨e, ⟨by omega, evaln_isSome_mono (Nat.le_succ k) hsome⟩, rfl⟩

/-- The fixed public process enumerating decompositions of all `T`-provable first-order
propositions. -/
noncomputable def paperTheoryDP [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1] :
    DeductiveProcess where
  D := paperTheoremStage (exists_paperTheoremCode T).choose
  mono := paperTheoremStage_mono _

lemma paperTheoryDP_covers [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]
    {formulaCode : ℕ} (hfire : paperTheoremFires T formulaCode) :
    ∃ k, paperTheoremSentence formulaCode ∈ (paperTheoryDP T).D k := by
  classical
  set code := (exists_paperTheoremCode T).choose
  have hdom : (code.eval formulaCode).Dom :=
    ((exists_paperTheoremCode T).choose_spec formulaCode).mpr hfire
  obtain ⟨out, hout⟩ := Part.dom_iff_mem.mp hdom
  obtain ⟨fuel, hfuel⟩ := Nat.Partrec.Code.evaln_complete.mp hout
  refine ⟨max formulaCode fuel, ?_⟩
  simp only [paperTheoryDP, paperTheoremStage, Finset.mem_image,
    Finset.mem_filter, Finset.mem_range]
  refine ⟨formulaCode, ⟨by omega, ?_⟩, rfl⟩
  exact evaln_isSome_mono (le_max_right formulaCode fuel)
    (Option.isSome_iff_exists.mpr ⟨out, hfuel⟩)

lemma paperTheoryDP_covers_provable [T.Δ₁] [𝗜𝚺₁ ⪯ T]
    [T.SoundOnHierarchy 𝚺 1] (φ : ArithmeticProposition)
    (hφ : Bootstrapping.Provable T (Encodable.encode φ)) :
    ∃ k, paperPrimeDecompose φ ∈ (paperTheoryDP T).D k := by
  simpa using paperTheoryDP_covers T (formulaCode := Encodable.encode φ) hφ

lemma paperTheoremStage_eq_toFinset (c : Nat.Partrec.Code) (n : ℕ) :
    paperTheoremStage c n =
      ((List.range (n + 1)).filterMap
        (fun e => if (Nat.Partrec.Code.evaln n c e).isSome = true then
          some (paperTheoremSentence e) else none)).toFinset := by
  classical
  ext φ
  simp only [paperTheoremStage, Finset.mem_image, Finset.mem_filter, Finset.mem_range,
    List.mem_toFinset, List.mem_filterMap, List.mem_range]
  constructor
  · rintro ⟨e, ⟨he, hsome⟩, rfl⟩
    exact ⟨e, he, by rw [if_pos hsome]⟩
  · rintro ⟨e, he, hcond⟩
    by_cases hs : (Nat.Partrec.Code.evaln n c e).isSome = true
    · rw [if_pos hs] at hcond
      exact ⟨e, ⟨he, hs⟩, Option.some_inj.mp hcond⟩
    · rw [if_neg hs] at hcond
      exact absurd hcond (by simp)

lemma paperTheoremStage_encode_prim (c : Nat.Partrec.Code) :
    Primrec (fun n => Encodable.encode (paperTheoremStage c n)) := by
  have hevaln : Primrec (fun p : ℕ × ℕ =>
      (Nat.Partrec.Code.evaln p.1 c p.2).isSome) :=
    Primrec.option_isSome.comp
      (Nat.Partrec.Code.primrec_evaln.comp
        ((Primrec.fst.pair (Primrec.const c)).pair Primrec.snd))
  have hguncur : Primrec (fun p : ℕ × ℕ =>
      if (Nat.Partrec.Code.evaln p.1 c p.2).isSome = true then
        some (paperTheoremSentence p.2) else (none : Option Sentence)) := by
    have hb : Primrec (fun p : ℕ × ℕ =>
        bif (Nat.Partrec.Code.evaln p.1 c p.2).isSome then
          some (paperTheoremSentence p.2) else (none : Option Sentence)) :=
      Primrec.cond hevaln
        (Primrec.option_some.comp (paperTheoremSentence_prim.comp Primrec.snd))
        (Primrec.const (none : Option Sentence))
    exact hb.of_eq fun p => by
      cases (Nat.Partrec.Code.evaln p.1 c p.2).isSome <;> simp
  have hlist : Primrec (fun n : ℕ => (List.range (n + 1)).filterMap
      (fun e => if (Nat.Partrec.Code.evaln n c e).isSome = true then
        some (paperTheoremSentence e) else none)) :=
    Primrec.listFilterMap (Primrec.list_range.comp Primrec.succ) hguncur.to₂
  have hkey : (fun n => Encodable.encode (paperTheoremStage c n)) =
      (fun n => Encodable.encode
        ((sentenceDedup ((List.range (n + 1)).filterMap
          (fun e => if (Nat.Partrec.Code.evaln n c e).isSome = true then
            some (paperTheoremSentence e) else none))).insertionSort sentenceCodeLE)) := by
    funext n
    rw [paperTheoremStage_eq_toFinset, encode_toFinset_eq]
  rw [hkey]
  exact Primrec.encode.comp
    (sentenceInsertionSort_prim.comp (sentenceDedup_prim.comp hlist))

lemma paperTheoryDP_computable [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1] :
    ComputableDeductiveProcess (paperTheoryDP T) := by
  obtain ⟨code, hcode⟩ := Nat.Partrec.Code.exists_code.mp
    (Nat.Partrec.of_primrec
      (Primrec.nat_iff.mp
        (paperTheoremStage_encode_prim (exists_paperTheoremCode T).choose)))
  refine ⟨code, fun n => ?_⟩
  rw [hcode]
  exact Part.mem_some _

/-! ## Non-vacuity -/

lemma paperFormulaCode_has_proposition {formulaCode : ℕ}
    (hwf : Bootstrapping.IsFormula ℒₒᵣ formulaCode) :
    ∃ φ : ArithmeticProposition, Encodable.encode φ = formulaCode := by
  rcases hwf.sound with ⟨φ, hφ⟩
  exact ⟨φ, by simpa [LO.FirstOrder.Semiformula.quote_eq_encode] using hφ⟩

lemma paperTheoremFires_has_proposition [T.Δ₁] [𝗜𝚺₁ ⪯ T]
    [T.SoundOnHierarchy 𝚺 1] {formulaCode : ℕ}
    (hfire : paperTheoremFires T formulaCode) :
    ∃ φ : ArithmeticProposition, Encodable.encode φ = formulaCode ∧
      Bootstrapping.Provable T (Encodable.encode φ) := by
  rcases hfire with ⟨d, hd⟩
  have hwf : Bootstrapping.IsFormula ℒₒᵣ formulaCode := by
    simpa [Bootstrapping.Proof] using hd.isFormulaSet
  rcases paperFormulaCode_has_proposition hwf with ⟨φ, hcode⟩
  refine ⟨φ, hcode, ?_⟩
  rw [hcode]
  exact ⟨d, hd⟩

/-- Every first-order model of `T` induces a completed public world for the fixed theorem
process. -/
lemma paperTheoryDP_hworld_of_model [T.Δ₁] [𝗜𝚺₁ ⪯ T]
    [T.SoundOnHierarchy 𝚺 1]
    {M : Type*} [Nonempty M] [Structure ℒₒᵣ M]
    (hT : M ↓[ℒₒᵣ] ⊧* T) (f : ℕ → M) :
    (paperPrimeWorld M f).ConsistentWithTheory (paperTheoryDP T) := by
  intro k φ hφ
  simp only [paperTheoryDP, paperTheoremStage, Finset.mem_image,
    Finset.mem_filter, Finset.mem_range] at hφ
  obtain ⟨formulaCode, ⟨-, hsome⟩, rfl⟩ := hφ
  have hfire : paperTheoremFires T formulaCode := by
    obtain ⟨out, hout⟩ := Option.isSome_iff_exists.mp hsome
    exact ((exists_paperTheoremCode T).choose_spec formulaCode).mp
      (Part.dom_iff_mem.mpr ⟨out, Nat.Partrec.Code.evaln_sound hout⟩)
  obtain ⟨ψ, hcode, hprov⟩ := paperTheoremFires_has_proposition T hfire
  rw [← hcode, paperTheoremSentence_spec,
    paperPrimeWorld_holds_decompose M f]
  exact provable_proposition_evalf_of_model T hT f hprov

/-- Completeness turns the already-proved consistency of the arithmetic base into an
explicit completed world.  Thus the universal theorem stream is not merely syntactically
computable; it is non-vacuous. -/
lemma paperTheoryDP_nonvacuous [T.Δ₁] [𝗜𝚺₁ ⪯ T]
    [T.SoundOnHierarchy 𝚺 1] :
    ∃ v : PCWorld, v.ConsistentWithTheory (paperTheoryDP T) := by
  have hs : LO.FirstOrder.Satisfiable T :=
    LO.FirstOrder.Theory.small_satisfiable_of_consistent (T := T) inferInstance
  rcases LO.FirstOrder.satisfiable_iff.mp hs with ⟨M, hMne, hMstr, hT⟩
  letI : Nonempty M := hMne
  letI : Structure ℒₒᵣ M := hMstr
  let f : ℕ → M := fun _ => Classical.choice hMne
  exact ⟨paperPrimeWorld M f, paperTheoryDP_hworld_of_model T hT f⟩

/-! ## Joint compatibility with the established theorem stream -/

lemma eventAtom_atomCodes_ne_paperPrimeTag (e : ℕ) :
    ∀ a ∈ sentenceAtomCodes (eventAtom e), a.unpair.1 ≠ paperPrimeTag := by
  intro a ha
  rcases h : e.unpair.1 with _ | _ | _ | _ | _ | _ | _ | _ | m
  all_goals simp only [eventAtom, h, sentenceAtomCodes_neg] at ha
  · exact fun hc => by
      simp [sentenceAtomCodes_computationClaimSentence _ a ha, haltingClaim,
        ComputationClaimKind.godelCode, paperPrimeTag] at hc
  · exact fun hc => by
      simp [sentenceAtomCodes_computationClaimSentence _ a ha, haltingClaim,
        ComputationClaimKind.godelCode, paperPrimeTag] at hc
  · exact fun hc => by
      simp [sentenceAtomCodes_computationClaimSentence _ a ha, boundedHaltingClaim,
        ComputationClaimKind.godelCode, paperPrimeTag] at hc
  · exact fun hc => by
      simp [sentenceAtomCodes_computationClaimSentence _ a ha, boundedHaltingClaim,
        ComputationClaimKind.godelCode, paperPrimeTag] at hc
  · exact fun hc => by
      simp [sentenceAtomCodes_computationClaimSentence _ a ha, inconsistencyClaim,
        ComputationClaimKind.godelCode, paperPrimeTag] at hc
  · exact fun hc => by
      simp [sentenceAtomCodes_computationClaimSentence _ a ha, consistencyClaim,
        ComputationClaimKind.godelCode, paperPrimeTag] at hc
  · exact fun hc => by
      simp [sentenceAtomCodes_quoteAtom _ a ha, paperPrimeTag] at hc
  · exact fun hc => by
      simp [sentenceAtomCodes_quoteAtom _ a ha, paperPrimeTag] at hc
  · simp at ha

open Classical in
noncomputable def paperTheoryExtensionWorld
    (T : ArithmeticTheory) (M : Type*) [Nonempty M] [Structure ℒₒᵣ M]
    (f : ℕ → M) : PCWorld := fun a =>
  if a.unpair.1 = paperPrimeTag then paperPrimeWorld M f a else provabilityWorld T a

lemma paperTheoryExtensionWorld_agree_base
    (T : ArithmeticTheory) (M : Type*) [Nonempty M] [Structure ℒₒᵣ M]
    (f : ℕ → M) {a : ℕ} (ha : a.unpair.1 ≠ paperPrimeTag) :
    paperTheoryExtensionWorld T M f a ↔ provabilityWorld T a := by
  simp [paperTheoryExtensionWorld, ha]

lemma paperTheoryExtensionWorld_agree_paper
    (T : ArithmeticTheory) (M : Type*) [Nonempty M] [Structure ℒₒᵣ M]
    (f : ℕ → M) {a : ℕ} (ha : a.unpair.1 = paperPrimeTag) :
    paperTheoryExtensionWorld T M f a ↔ paperPrimeWorld M f a := by
  simp [paperTheoryExtensionWorld, ha]

lemma paperTheoryExtensionWorld_holds_base_iff
    (T : ArithmeticTheory) (M : Type*) [Nonempty M] [Structure ℒₒᵣ M]
    (f : ℕ → M) {φ : Sentence}
    (hφ : ∀ a ∈ sentenceAtomCodes φ, a.unpair.1 ≠ paperPrimeTag) :
    (paperTheoryExtensionWorld T M f).Holds φ ↔ (provabilityWorld T).Holds φ :=
  PCWorld.holds_congr_atomCodes φ fun a ha =>
    paperTheoryExtensionWorld_agree_base T M f (hφ a ha)

lemma paperTheoryExtensionWorld_holds_paper_iff
    (T : ArithmeticTheory) (M : Type*) [Nonempty M] [Structure ℒₒᵣ M]
    (f : ℕ → M) (φ : ArithmeticProposition) :
    (paperTheoryExtensionWorld T M f).Holds (paperPrimeDecompose φ) ↔
      (paperPrimeWorld M f).Holds (paperPrimeDecompose φ) :=
  PCWorld.holds_congr_atomCodes (paperPrimeDecompose φ) fun a ha =>
    paperTheoryExtensionWorld_agree_paper T M f (paperPrimeDecompose_atom_tag φ a ha)

/-- The paper theorem stream is added before any source, market, weight, or deferral is
chosen. -/
noncomputable def theoremPaperDP [T.Δ₁] [𝗜𝚺₁ ⪯ T]
    [T.SoundOnHierarchy 𝚺 1] : DeductiveProcess :=
  (theoremDP T).union (paperTheoryDP T)

noncomputable def theoremPaperDPComputation [T.Δ₁] [𝗜𝚺₁ ⪯ T]
    [T.SoundOnHierarchy 𝚺 1] : DeductiveProcessComputation (theoremPaperDP T) :=
  ((theoremDP_computable T).nonemptyComputation.some).union
    (paperTheoryDP_computable T).nonemptyComputation.some

lemma theoremPaperDP_hworld_of_model [T.Δ₁] [𝗜𝚺₁ ⪯ T]
    [T.SoundOnHierarchy 𝚺 1]
    {M : Type*} [Nonempty M] [Structure ℒₒᵣ M]
    (hT : M ↓[ℒₒᵣ] ⊧* T) (f : ℕ → M) :
    (paperTheoryExtensionWorld T M f).ConsistentWithTheory (theoremPaperDP T) := by
  intro k φ hφ
  rw [theoremPaperDP, DeductiveProcess.union_stage, Finset.mem_union] at hφ
  rcases hφ with hbase | hpaper
  · apply (paperTheoryExtensionWorld_holds_base_iff T M f fun a ha => ?_).mpr
      (theoremDP_hworld T k φ hbase)
    simp only [theoremDP, theoremStage, Finset.mem_image, Finset.mem_filter,
      Finset.mem_range] at hbase
    obtain ⟨e, _, rfl⟩ := hbase
    exact eventAtom_atomCodes_ne_paperPrimeTag e a ha
  · simp only [paperTheoryDP, paperTheoremStage, Finset.mem_image,
      Finset.mem_filter, Finset.mem_range] at hpaper
    obtain ⟨formulaCode, ⟨-, hsome⟩, rfl⟩ := hpaper
    have hfire : paperTheoremFires T formulaCode := by
      obtain ⟨out, hout⟩ := Option.isSome_iff_exists.mp hsome
      exact ((exists_paperTheoremCode T).choose_spec formulaCode).mp
        (Part.dom_iff_mem.mpr ⟨out, Nat.Partrec.Code.evaln_sound hout⟩)
    obtain ⟨ψ, hcode, hprov⟩ := paperTheoremFires_has_proposition T hfire
    rw [← hcode, paperTheoremSentence_spec,
      paperTheoryExtensionWorld_holds_paper_iff T M f,
      paperPrimeWorld_holds_decompose M f]
    exact provable_proposition_evalf_of_model T hT f hprov

lemma theoremPaperDP_nonvacuous [T.Δ₁] [𝗜𝚺₁ ⪯ T]
    [T.SoundOnHierarchy 𝚺 1] :
    ∃ v : PCWorld, v.ConsistentWithTheory (theoremPaperDP T) := by
  have hs : LO.FirstOrder.Satisfiable T :=
    LO.FirstOrder.Theory.small_satisfiable_of_consistent (T := T) inferInstance
  rcases LO.FirstOrder.satisfiable_iff.mp hs with ⟨M, hMne, hMstr, hT⟩
  letI : Nonempty M := hMne
  letI : Structure ℒₒᵣ M := hMstr
  let f : ℕ → M := fun _ => Classical.choice hMne
  exact ⟨paperTheoryExtensionWorld T M f, theoremPaperDP_hworld_of_model T hT f⟩

#print axioms paperTheoremSentence_spec
#print axioms paperTheoremSentence_prim
#print axioms provable_proposition_evalf_of_model
#print axioms paperTheoryDP_computable
#print axioms paperTheoryDP_hworld_of_model
#print axioms paperTheoryDP_nonvacuous
#print axioms theoremPaperDPComputation
#print axioms theoremPaperDP_nonvacuous

end LogicalInduction
