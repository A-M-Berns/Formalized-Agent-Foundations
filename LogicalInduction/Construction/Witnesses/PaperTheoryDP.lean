import LogicalInduction.Construction.Witnesses.PaperFirstOrderCompiler
import LogicalInduction.Construction.Witnesses.ComputationDP
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Coding
import Foundation.FirstOrder.Bootstrapping.DerivabilityCondition.D1
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

lemma paperTheoremFires_re [T.Δ₁] :
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
lemma exists_paperTheoremCode [T.Δ₁] :
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
noncomputable def paperTheoryDP [T.Δ₁] :
    DeductiveProcess where
  D := paperTheoremStage (exists_paperTheoremCode T).choose
  mono := paperTheoremStage_mono _

lemma paperTheoryDP_covers [T.Δ₁]
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

lemma paperTheoryDP_covers_provable [T.Δ₁] (φ : ArithmeticProposition)
    (hφ : Bootstrapping.Provable T (Encodable.encode φ)) :
    ∃ k, paperPrimeDecompose φ ∈ (paperTheoryDP T).D k := by
  simpa using paperTheoryDP_covers T (formulaCode := Encodable.encode φ) hφ

/-- Ordinary object-level provability is the public interface to the fixed theorem
process; encoded provability remains only an implementation detail of its enumerator. -/
lemma paperTheoryDP_covers_outer_provable [T.Δ₁] (φ : ArithmeticSentence) (hφ : T ⊢ φ) :
    ∃ k, paperPrimeDecompose φ ∈ (paperTheoryDP T).D k := by
  have hquote : Bootstrapping.Provable T (⌜φ⌝ : ℕ) :=
    Bootstrapping.provable_iff_provable.mpr hφ
  apply paperTheoryDP_covers_provable T φ
  have hencode : Encodable.encode (φ : ArithmeticProposition) = (⌜φ⌝ : ℕ) := by
    simpa using (LO.FirstOrder.Sentence.quote_eq_encode (V := ℕ) φ).symm
  rw [hencode]
  exact hquote

/-- Every completed public world of `paperTheoryDP T` holds the prime decomposition of
each ordinary theorem of `T`. -/
lemma PCWorld.holds_paperPrimeDecompose_of_provable [T.Δ₁] (v : PCWorld)
    (hv : v.ConsistentWithTheory (paperTheoryDP T))
    (φ : ArithmeticSentence) (hφ : T ⊢ φ) :
    v.Holds (paperPrimeDecompose φ) := by
  obtain ⟨k, hk⟩ := paperTheoryDP_covers_outer_provable T φ hφ
  exact hv k _ hk

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

lemma paperTheoryDP_computable [T.Δ₁] :
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

lemma paperTheoremFires_has_proposition [T.Δ₁] {formulaCode : ℕ}
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
lemma paperTheoryDP_hworld_of_model [T.Δ₁]
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

lemma paperTheoryDP_atom_tag [T.Δ₁] {k : ℕ} {sentence : Sentence}
    (hsentence : sentence ∈ (paperTheoryDP T).D k) {a : ℕ}
    (ha : a ∈ sentenceAtomCodes sentence) : a.unpair.1 = paperPrimeTag := by
  simp only [paperTheoryDP, paperTheoremStage, Finset.mem_image,
    Finset.mem_filter, Finset.mem_range] at hsentence
  obtain ⟨formulaCode, ⟨-, hsome⟩, rfl⟩ := hsentence
  have hfire : paperTheoremFires T formulaCode := by
    obtain ⟨out, hout⟩ := Option.isSome_iff_exists.mp hsome
    exact ((exists_paperTheoremCode T).choose_spec formulaCode).mp
      (Part.dom_iff_mem.mpr ⟨out, Nat.Partrec.Code.evaln_sound hout⟩)
  obtain ⟨φ, hcode, -⟩ := paperTheoremFires_has_proposition T hfire
  rw [← hcode, paperTheoremSentence_spec] at ha
  exact paperPrimeDecompose_atom_tag φ a ha

/-- Completeness turns the already-proved consistency of the arithmetic base into an
explicit completed world.  Thus the universal theorem stream is not merely syntactically
computable; it is non-vacuous. -/
lemma paperTheoryDP_nonvacuous [T.Δ₁] [Entailment.Consistent T] :
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
  rcases h : e.unpair.1 with _ | _ | _ | _ | _ | _ | m
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

/-! ## The single paper-facing market

The paper fixes **one** deductive process `𝔻` and prices everything against the one market
`𝕡` the construction builds over it.  `paperDP` is that process: the union of the
computation/quotation literal stream (`theoremDP`) with the `Θ`-complete first-order
theorem stream (`paperTheoryDP`).  Every canonical endpoint of the self-reference
(`thm:ref`, `thm:lp`, `thm:st`, `thm:epr`, `thm:er`, `thm:cee`, `thm:ceu`), conditioning
(`thm:scon`), feedback (`thm:wub`, `thm:wubaff`, `thm:wubexp`) and meta-learning
(`thm:halts`, `thm:loops`, `thm:dontwait`, `thm:pac`, `thm:pazfc`, `thm:incons`) families
is stated over `liaHistory (paperDP T)`.

The two component streams remain named because they are *construction ingredients*, not
alternative markets: the quotation presentation and the represented-claim coverage are
proved of a component and lifted here monotonically, and the semantic-lifted `thm:ccee`
lane keeps its own base process by ruling.  No canonical endpoint is stated at a
component. -/

/-- The paper theorem stream is added before any source, market, weight, or deferral is
chosen. -/
noncomputable def paperDP [T.Δ₁] : DeductiveProcess :=
  (theoremDP T).union (paperTheoryDP T)

/-- The literal stream is a substage of the single market's process. -/
lemma theoremDP_subset_paperDP [T.Δ₁] (k : ℕ) :
    (theoremDP T).D k ⊆ (paperDP T).D k := by
  rw [paperDP, DeductiveProcess.union_stage]
  exact Finset.subset_union_left

/-- The first-order theorem stream is a substage of the single market's process. -/
lemma paperTheoryDP_subset_paperDP [T.Δ₁] (k : ℕ) :
    (paperTheoryDP T).D k ⊆ (paperDP T).D k := by
  rw [paperDP, DeductiveProcess.union_stage]
  exact Finset.subset_union_right

/-- Coverage lifts from the first-order theorem stream to the single market. -/
lemma paperDP_covers_of_paperTheoryDP [T.Δ₁] {φ : Sentence}
    (h : ∃ k, φ ∈ (paperTheoryDP T).D k) : ∃ k, φ ∈ (paperDP T).D k :=
  h.imp fun k hk => paperTheoryDP_subset_paperDP T k hk

noncomputable def paperDPComputation [T.Δ₁] :
    DeductiveProcessComputation (paperDP T) :=
  ((theoremDP_computable T).nonemptyComputation.some).union
    (paperTheoryDP_computable T).nonemptyComputation.some

lemma paperDP_hworld_of_model [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]
    {M : Type*} [Nonempty M] [Structure ℒₒᵣ M]
    (hT : M ↓[ℒₒᵣ] ⊧* T) (f : ℕ → M) :
    (paperTheoryExtensionWorld T M f).ConsistentWithTheory (paperDP T) := by
  intro k φ hφ
  rw [paperDP, DeductiveProcess.union_stage, Finset.mem_union] at hφ
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

lemma paperDP_nonvacuous [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] :
    ∃ v : PCWorld, v.ConsistentWithTheory (paperDP T) := by
  have hs : LO.FirstOrder.Satisfiable T :=
    LO.FirstOrder.Theory.small_satisfiable_of_consistent (T := T) inferInstance
  rcases LO.FirstOrder.satisfiable_iff.mp hs with ⟨M, hMne, hMstr, hT⟩
  letI : Nonempty M := hMne
  letI : Structure ℒₒᵣ M := hMstr
  let f : ℕ → M := fun _ => Classical.choice hMne
  exact ⟨paperTheoryExtensionWorld T M f, paperDP_hworld_of_model T hT f⟩

/-! ### The market data every endpoint over `paperDP` consumes -/

/-- The single market's process is computable: the union of the two stage programs. -/
lemma paperDP_computable [T.Δ₁] : ComputableDeductiveProcess (paperDP T) :=
  (paperDPComputation T).toComputable

/-- **Market non-vacuity (`hworld`) for the single market.**  Every stage has a consistent
world, from consistency of `T` alone (via satisfiability); this is the stage-indexed form
the quotation and meta-learning endpoints take. -/
lemma paperDP_hworld [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] (n : ℕ) :
    ∃ v : PCWorld, v.ConsistentWith ((paperDP T).D n) := by
  obtain ⟨v, hv⟩ := paperDP_nonvacuous T
  exact ⟨v, hv n⟩

/-- **The quotation presentation over the single market**, lifted from the literal stream.
Every field is either theory-side or an "enters some stage" claim, so the lift is the
monotone one; only the stage program is supplied afresh.
Paper node: `thm:ref` -/
noncomputable def paperQuotationPresentation [T.Δ₁] :
    QuotationTheoryPresentation (paperDP T) T :=
  (quotationPresentation T).mono (theoremDP_subset_paperDP T) (paperDPComputation T)

/-- The constructed inductor instance for the single market, reused by every endpoint. -/
noncomputable abbrev paperLIA [T.Δ₁] :
    IsLogicalInductor (liaHistory (paperDP T)) (paperDP T) :=
  LIA_is_logical_inductor (paperDP T) (paperDP_computable T)

/-- A named exact market program for the single market, used to build its own quote codes
and its paradox-resistance diagonal.
Paper node: `thm:lia` -/
noncomputable def paperMarketComputation [T.Δ₁] :
    MarketComputation (liaHistory (paperDP T)) :=
  liaMarketComputation (paperDP T) (paperDP_computable T)

#print axioms paperTheoremSentence_spec
#print axioms paperTheoremSentence_prim
#print axioms provable_proposition_evalf_of_model
#print axioms paperTheoryDP_computable
#print axioms paperTheoryDP_hworld_of_model
#print axioms paperTheoryDP_nonvacuous
#print axioms paperDPComputation
#print axioms paperDP_nonvacuous
#print axioms paperDP_computable
#print axioms paperDP_hworld
#print axioms paperQuotationPresentation
#print axioms paperMarketComputation

end LogicalInduction
