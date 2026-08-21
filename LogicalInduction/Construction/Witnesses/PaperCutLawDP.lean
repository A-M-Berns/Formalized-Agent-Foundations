import LogicalInduction.Construction.Witnesses.PaperTheoryDP
import LogicalInduction.Construction.Witnesses.SemanticSourceDP

/-!
# Exact public cut laws from first-order proofs

Prime decomposition preserves truth but, because FAF's public negation is an implication to
false, it does not commute with first-order NNF negation by definitional equality.  This
fixed process closes precisely that ABI gap.  It checks provability of `¬φ` or `φ → ψ` in
the old first-order theory and publishes the corresponding *literal public* negation or
implication between prime decompositions.

The process is universal and fixed by `T`; no source family occurs in its definition.
-/

namespace LogicalInduction

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open LO.Propositional

variable (T : ArithmeticTheory)

/-- Upper-cut event for a threshold formula code. -/
def paperUpperEvent (formulaCode : ℕ) : ℕ := Nat.pair 0 formulaCode

/-- Downward-cut event, with lower threshold first and upper threshold second. -/
def paperDownwardEvent (lowerCode upperCode : ℕ) : ℕ :=
  Nat.pair 1 (Nat.pair lowerCode upperCode)

def paperCutLawFires [T.Δ₁] (e : ℕ) : Prop :=
  if e.unpair.1 = 0 then
    Bootstrapping.IsFormula ℒₒᵣ e.unpair.2 ∧
      Bootstrapping.Provable T (paperFirstOrderNegCode e.unpair.2)
  else if e.unpair.1 = 1 then
    Bootstrapping.IsFormula ℒₒᵣ e.unpair.2.unpair.1 ∧
      Bootstrapping.IsFormula ℒₒᵣ e.unpair.2.unpair.2 ∧
      Bootstrapping.Provable T
        (paperFirstOrderImpCode e.unpair.2.unpair.2 e.unpair.2.unpair.1)
  else False

private lemma paperProvableCode_re [T.Δ₁] [𝗜𝚺₁ ⪯ T]
    [T.SoundOnHierarchy 𝚺 1] :
    REPred fun formulaCode : ℕ => Bootstrapping.Provable T formulaCode := by
  apply re_iff_sigma1.mpr
  definability

private lemma paperIsFormulaCode_re :
    REPred fun formulaCode : ℕ => Bootstrapping.IsFormula ℒₒᵣ formulaCode := by
  apply re_iff_sigma1.mpr
  change 𝚺₁-Predicate fun formulaCode : ℕ =>
    Bootstrapping.IsSemiformula ℒₒᵣ 0 formulaCode
  definability

lemma paperCutLawFires_re [T.Δ₁] [𝗜𝚺₁ ⪯ T]
    [T.SoundOnHierarchy 𝚺 1] : REPred (paperCutLawFires T) := by
  have htag (k : ℕ) : REPred fun e : ℕ => e.unpair.1 = k :=
    ComputablePred.to_re
      (Primrec.eq.comp (Primrec.fst.comp Primrec.unpair) (Primrec.const k)).computablePred
  have hpayload : Computable fun e : ℕ => e.unpair.2 :=
    (Primrec.snd.comp Primrec.unpair).to_comp
  have hlower : Computable fun e : ℕ => e.unpair.2.unpair.1 :=
    (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))).to_comp
  have hupper : Computable fun e : ℕ => e.unpair.2.unpair.2 :=
    (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))).to_comp
  have hwf0 := REPred.comp hpayload paperIsFormulaCode_re
  have hneg := REPred.comp
    (paperFirstOrderNegCode_prim.comp (Primrec.snd.comp Primrec.unpair)).to_comp
    (paperProvableCode_re T)
  have hwfLower := REPred.comp hlower paperIsFormulaCode_re
  have hwfUpper := REPred.comp hupper paperIsFormulaCode_re
  have himpMap : Computable fun e : ℕ =>
      paperFirstOrderImpCode e.unpair.2.unpair.2 e.unpair.2.unpair.1 :=
    (paperFirstOrderImpCode_prim.comp
      (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
      (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))).to_comp
  have himp := REPred.comp himpMap (paperProvableCode_re T)
  have hre := (((htag 0).and (hwf0.and hneg)).or
    ((htag 1).and (hwfLower.and (hwfUpper.and himp))))
  exact REPred.of_eq hre fun e => by
    by_cases h0 : e.unpair.1 = 0
    · simp [paperCutLawFires, h0]
    by_cases h1 : e.unpair.1 = 1
    · simp [paperCutLawFires, h1]
    · simp [paperCutLawFires, h0, h1]

def paperCutLawSentenceCode (e : ℕ) : ℕ :=
  if e.unpair.1 = 0 then
    paperPublicNegCode (paperPrimeDecomposeCode e.unpair.2)
  else if e.unpair.1 = 1 then
    paperPublicImpCode
      (paperPrimeDecomposeCode e.unpair.2.unpair.2)
      (paperPrimeDecomposeCode e.unpair.2.unpair.1)
  else Encodable.encode (⊤ : Sentence)

def paperCutLawSentence (e : ℕ) : Sentence :=
  (Encodable.decode (α := Sentence) (paperCutLawSentenceCode e)).getD ⊤

@[simp] lemma paperCutLawSentence_upper (φ : ArithmeticProposition) :
    paperCutLawSentence (paperUpperEvent (Encodable.encode φ)) =
      ∼paperPrimeDecompose φ := by
  simp [paperCutLawSentence, paperCutLawSentenceCode, paperUpperEvent,
    paperPrimeDecomposeCode_spec, paperPublicNegCode_spec]

@[simp] lemma paperCutLawSentence_downward
    (lower upper : ArithmeticProposition) :
    paperCutLawSentence
      (paperDownwardEvent (Encodable.encode lower) (Encodable.encode upper)) =
      (paperPrimeDecompose upper 🡒 paperPrimeDecompose lower) := by
  simp [paperCutLawSentence, paperCutLawSentenceCode, paperDownwardEvent,
    paperPrimeDecomposeCode_spec, paperPublicImpCode_spec]

lemma paperCutLawSentenceCode_prim : Primrec paperCutLawSentenceCode := by
  let htag : Primrec fun e : ℕ => e.unpair.1 := Primrec.fst.comp Primrec.unpair
  let hpayload : Primrec fun e : ℕ => e.unpair.2 := Primrec.snd.comp Primrec.unpair
  let hlower : Primrec fun e : ℕ => e.unpair.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp hpayload)
  let hupper : Primrec fun e : ℕ => e.unpair.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp hpayload)
  have htagEq (k : ℕ) : PrimrecPred fun e : ℕ => e.unpair.1 = k :=
    Primrec.eq.comp htag (Primrec.const k)
  have hneg : Primrec fun e : ℕ =>
      paperPublicNegCode (paperPrimeDecomposeCode e.unpair.2) :=
    (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 2)
      (Primrec₂.natPair.comp (paperPrimeDecomposeCode_prim.comp hpayload)
        (Primrec.const (Encodable.encode (⊥ : Sentence)))))).of_eq fun _ => rfl
  have himp : Primrec fun e : ℕ =>
      paperPublicImpCode (paperPrimeDecomposeCode e.unpair.2.unpair.2)
        (paperPrimeDecomposeCode e.unpair.2.unpair.1) :=
    paperPublicImpCode_prim.comp
      (paperPrimeDecomposeCode_prim.comp hupper)
      (paperPrimeDecomposeCode_prim.comp hlower)
  exact (Primrec.ite (htagEq 0) hneg
    (Primrec.ite (htagEq 1) himp (Primrec.const (Encodable.encode (⊤ : Sentence))))).of_eq
      fun _ => rfl

lemma paperCutLawSentence_prim : Primrec paperCutLawSentence := by
  exact (Primrec.option_getD.comp
    (Primrec.decode.comp paperCutLawSentenceCode_prim)
    (Primrec.const (⊤ : Sentence))).of_eq fun _ => rfl

lemma exists_paperCutLawCode [T.Δ₁] [𝗜𝚺₁ ⪯ T]
    [T.SoundOnHierarchy 𝚺 1] :
    ∃ code : Nat.Partrec.Code, ∀ e, (code.eval e).Dom ↔ paperCutLawFires T e := by
  obtain ⟨f, hf, hfP⟩ := REPred.iff'.mp (paperCutLawFires_re T)
  obtain ⟨code, hcode⟩ := Nat.Partrec.Code.exists_code.mp
    (Partrec.nat_iff.mp (hf.map (Computable.const (0 : ℕ)).to₂))
  refine ⟨code, fun e => ?_⟩
  rw [hcode]
  exact (hfP e).symm

open Classical in
noncomputable def paperCutLawStage (code : Nat.Partrec.Code) (k : ℕ) : Finset Sentence :=
  ((Finset.range (k + 1)).filter
    (fun e => (Nat.Partrec.Code.evaln k code e).isSome = true)).image paperCutLawSentence

lemma paperCutLawStage_mono (code : Nat.Partrec.Code) (k : ℕ) :
    paperCutLawStage code k ⊆ paperCutLawStage code (k + 1) := by
  classical
  intro φ hφ
  simp only [paperCutLawStage, Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hφ ⊢
  obtain ⟨e, ⟨he, hsome⟩, rfl⟩ := hφ
  exact ⟨e, ⟨by omega, evaln_isSome_mono (Nat.le_succ k) hsome⟩, rfl⟩

noncomputable def paperCutLawDP [T.Δ₁] [𝗜𝚺₁ ⪯ T]
    [T.SoundOnHierarchy 𝚺 1] : DeductiveProcess where
  D := paperCutLawStage (exists_paperCutLawCode T).choose
  mono := paperCutLawStage_mono _

lemma paperCutLawDP_covers [T.Δ₁] [𝗜𝚺₁ ⪯ T]
    [T.SoundOnHierarchy 𝚺 1] {e : ℕ} (hfire : paperCutLawFires T e) :
    ∃ k, paperCutLawSentence e ∈ (paperCutLawDP T).D k := by
  classical
  set code := (exists_paperCutLawCode T).choose
  have hdom : (code.eval e).Dom := (exists_paperCutLawCode T).choose_spec e |>.mpr hfire
  obtain ⟨out, hout⟩ := Part.dom_iff_mem.mp hdom
  obtain ⟨fuel, hfuel⟩ := Nat.Partrec.Code.evaln_complete.mp hout
  refine ⟨max e fuel, ?_⟩
  simp only [paperCutLawDP, paperCutLawStage, Finset.mem_image,
    Finset.mem_filter, Finset.mem_range]
  refine ⟨e, ⟨by omega, ?_⟩, rfl⟩
  exact evaln_isSome_mono (le_max_right e fuel)
    (Option.isSome_iff_exists.mpr ⟨out, hfuel⟩)

lemma paperCutLawStage_eq_toFinset (c : Nat.Partrec.Code) (n : ℕ) :
    paperCutLawStage c n =
      ((List.range (n + 1)).filterMap
        (fun e => if (Nat.Partrec.Code.evaln n c e).isSome = true then
          some (paperCutLawSentence e) else none)).toFinset := by
  classical
  ext φ
  simp only [paperCutLawStage, Finset.mem_image, Finset.mem_filter, Finset.mem_range,
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

lemma paperCutLawStage_encode_prim (c : Nat.Partrec.Code) :
    Primrec (fun n => Encodable.encode (paperCutLawStage c n)) := by
  have hevaln : Primrec fun p : ℕ × ℕ =>
      (Nat.Partrec.Code.evaln p.1 c p.2).isSome :=
    Primrec.option_isSome.comp
      (Nat.Partrec.Code.primrec_evaln.comp
        ((Primrec.fst.pair (Primrec.const c)).pair Primrec.snd))
  have hguncur : Primrec fun p : ℕ × ℕ =>
      if (Nat.Partrec.Code.evaln p.1 c p.2).isSome = true then
        some (paperCutLawSentence p.2) else (none : Option Sentence) := by
    have hb := Primrec.cond hevaln
      (Primrec.option_some.comp (paperCutLawSentence_prim.comp Primrec.snd))
      (Primrec.const (none : Option Sentence))
    exact hb.of_eq fun p => by
      cases (Nat.Partrec.Code.evaln p.1 c p.2).isSome <;> simp
  have hlist : Primrec fun n : ℕ => (List.range (n + 1)).filterMap
      (fun e => if (Nat.Partrec.Code.evaln n c e).isSome = true then
        some (paperCutLawSentence e) else none) :=
    Primrec.listFilterMap (Primrec.list_range.comp Primrec.succ) hguncur.to₂
  have hkey : (fun n => Encodable.encode (paperCutLawStage c n)) =
      (fun n => Encodable.encode
        ((sentenceDedup ((List.range (n + 1)).filterMap
          (fun e => if (Nat.Partrec.Code.evaln n c e).isSome = true then
            some (paperCutLawSentence e) else none))).insertionSort sentenceCodeLE)) := by
    funext n
    rw [paperCutLawStage_eq_toFinset, encode_toFinset_eq]
  rw [hkey]
  exact Primrec.encode.comp
    (sentenceInsertionSort_prim.comp (sentenceDedup_prim.comp hlist))

lemma paperCutLawDP_computable [T.Δ₁] [𝗜𝚺₁ ⪯ T]
    [T.SoundOnHierarchy 𝚺 1] : ComputableDeductiveProcess (paperCutLawDP T) := by
  obtain ⟨code, hcode⟩ := Nat.Partrec.Code.exists_code.mp
    (Nat.Partrec.of_primrec
      (Primrec.nat_iff.mp
        (paperCutLawStage_encode_prim (exists_paperCutLawCode T).choose)))
  refine ⟨code, fun n => ?_⟩
  rw [hcode]
  exact Part.mem_some _

/-! ## Coverage and model soundness -/

private lemma paperFormulaEncode_isFormula (φ : ArithmeticProposition) :
    Bootstrapping.IsFormula ℒₒᵣ (Encodable.encode φ) := by
  simpa [LO.FirstOrder.Semiformula.quote_eq_encode] using
    (LO.FirstOrder.Semiformula.quote_isSemiformula₀ (V := ℕ) φ)

private lemma eq_paperUpperEvent_of_code {e : ℕ} (h0 : e.unpair.1 = 0)
    {φ : ArithmeticProposition} (hcode : Encodable.encode φ = e.unpair.2) :
    e = paperUpperEvent (Encodable.encode φ) := by
  calc
    e = Nat.pair e.unpair.1 e.unpair.2 := (Nat.pair_unpair e).symm
    _ = Nat.pair 0 (Encodable.encode φ) := by rw [h0, hcode]
    _ = paperUpperEvent (Encodable.encode φ) := rfl

private lemma eq_paperDownwardEvent_of_codes {e : ℕ} (h1 : e.unpair.1 = 1)
    {lower upper : ArithmeticProposition}
    (hlower : Encodable.encode lower = e.unpair.2.unpair.1)
    (hupper : Encodable.encode upper = e.unpair.2.unpair.2) :
    e = paperDownwardEvent (Encodable.encode lower) (Encodable.encode upper) := by
  calc
    e = Nat.pair e.unpair.1 e.unpair.2 := (Nat.pair_unpair e).symm
    _ = Nat.pair 1 (Nat.pair (Encodable.encode lower) (Encodable.encode upper)) := by
      rw [h1, hlower, hupper, Nat.pair_unpair]
    _ = paperDownwardEvent (Encodable.encode lower) (Encodable.encode upper) := rfl

lemma paperCutLawDP_covers_upper [T.Δ₁] [𝗜𝚺₁ ⪯ T]
    [T.SoundOnHierarchy 𝚺 1] (φ : ArithmeticProposition)
    (hprov : Bootstrapping.Provable T (Encodable.encode (∼φ))) :
    ∃ k, (∼paperPrimeDecompose φ) ∈ (paperCutLawDP T).D k := by
  have hfire : paperCutLawFires T (paperUpperEvent (Encodable.encode φ)) := by
    simp [paperCutLawFires, paperUpperEvent, paperFirstOrderNegCode_spec, hprov,
      paperFormulaEncode_isFormula]
  simpa using paperCutLawDP_covers T hfire

lemma paperCutLawDP_covers_downward [T.Δ₁] [𝗜𝚺₁ ⪯ T]
    [T.SoundOnHierarchy 𝚺 1] (lower upper : ArithmeticProposition)
    (hprov : Bootstrapping.Provable T (Encodable.encode (upper 🡒 lower))) :
    ∃ k, (paperPrimeDecompose upper 🡒 paperPrimeDecompose lower) ∈
      (paperCutLawDP T).D k := by
  have hfire : paperCutLawFires T
      (paperDownwardEvent (Encodable.encode lower) (Encodable.encode upper)) := by
    simp [paperCutLawFires, paperDownwardEvent, paperFirstOrderImpCode_spec, hprov,
      paperFormulaEncode_isFormula]
  simpa using paperCutLawDP_covers T hfire

lemma paperCutLawDP_hworld_of_model [T.Δ₁] [𝗜𝚺₁ ⪯ T]
    [T.SoundOnHierarchy 𝚺 1]
    {M : Type*} [Nonempty M] [Structure ℒₒᵣ M]
    (hT : M ↓[ℒₒᵣ] ⊧* T) (f : ℕ → M) :
    (paperPrimeWorld M f).ConsistentWithTheory (paperCutLawDP T) := by
  intro k sentence hsentence
  simp only [paperCutLawDP, paperCutLawStage, Finset.mem_image,
    Finset.mem_filter, Finset.mem_range] at hsentence
  obtain ⟨e, ⟨-, hsome⟩, rfl⟩ := hsentence
  have hfire : paperCutLawFires T e := by
    obtain ⟨out, hout⟩ := Option.isSome_iff_exists.mp hsome
    exact ((exists_paperCutLawCode T).choose_spec e).mp
      (Part.dom_iff_mem.mpr ⟨out, Nat.Partrec.Code.evaln_sound hout⟩)
  by_cases h0 : e.unpair.1 = 0
  · simp only [paperCutLawFires, h0, ↓reduceIte] at hfire
    rcases paperFormulaCode_has_proposition hfire.1 with ⟨φ, hcode⟩
    have hprov : Bootstrapping.Provable T (Encodable.encode (∼φ)) := by
      rw [← hcode] at hfire
      simpa [paperFirstOrderNegCode_spec] using hfire.2
    have hnφ := provable_proposition_evalf_of_model T hT f hprov
    have hnEval : ¬φ.Evalf f := by simpa using hnφ
    rw [eq_paperUpperEvent_of_code h0 hcode]
    rw [paperCutLawSentence_upper]
    exact fun hholds => hnEval ((paperPrimeWorld_holds_decompose M f φ).mp hholds)
  · have h1 : e.unpair.1 = 1 := by
      by_contra hne
      simp [paperCutLawFires, h0, hne] at hfire
    simp only [paperCutLawFires, h1, ↓reduceIte] at hfire
    rcases paperFormulaCode_has_proposition hfire.1 with ⟨lower, hlower⟩
    rcases paperFormulaCode_has_proposition hfire.2.1 with ⟨upper, hupper⟩
    have hprov : Bootstrapping.Provable T (Encodable.encode (upper 🡒 lower)) := by
      rw [← hlower, ← hupper] at hfire
      simpa [paperFirstOrderImpCode_spec] using hfire.2.2
    have himp := provable_proposition_evalf_of_model T hT f hprov
    have himpEval : upper.Evalf f → lower.Evalf f := by simpa using himp
    rw [eq_paperDownwardEvent_of_codes h1 hlower hupper]
    rw [paperCutLawSentence_downward]
    intro hupperHolds
    exact (paperPrimeWorld_holds_decompose M f lower).mpr
      (himpEval ((paperPrimeWorld_holds_decompose M f upper).mp hupperHolds))

lemma paperCutLawSentence_atom_tag_of_fire [T.Δ₁] {e a : ℕ}
    (hfire : paperCutLawFires T e)
    (ha : a ∈ sentenceAtomCodes (paperCutLawSentence e)) :
    a.unpair.1 = paperPrimeTag := by
  by_cases h0 : e.unpair.1 = 0
  · simp only [paperCutLawFires, h0, ↓reduceIte] at hfire
    rcases paperFormulaCode_has_proposition hfire.1 with ⟨φ, hcode⟩
    rw [eq_paperUpperEvent_of_code h0 hcode, paperCutLawSentence_upper,
      sentenceAtomCodes_neg] at ha
    exact paperPrimeDecompose_atom_tag φ a ha
  · have h1 : e.unpair.1 = 1 := by
      by_contra hne
      simp [paperCutLawFires, h0, hne] at hfire
    simp only [paperCutLawFires, h1, ↓reduceIte] at hfire
    rcases paperFormulaCode_has_proposition hfire.1 with ⟨lower, hlower⟩
    rcases paperFormulaCode_has_proposition hfire.2.1 with ⟨upper, hupper⟩
    rw [eq_paperDownwardEvent_of_codes h1 hlower hupper,
      paperCutLawSentence_downward] at ha
    rw [sentenceAtomCodes_imp] at ha
    rcases Finset.mem_union.mp ha with ha | ha
    · exact paperPrimeDecompose_atom_tag upper a ha
    · exact paperPrimeDecompose_atom_tag lower a ha

/-! ## The fixed paper-facing base process -/

noncomputable def paperBaseDP [T.Δ₁] [𝗜𝚺₁ ⪯ T]
    [T.SoundOnHierarchy 𝚺 1] : DeductiveProcess :=
  (theoremPaperDP T).union (paperCutLawDP T)

noncomputable def paperBaseDPComputation [T.Δ₁] [𝗜𝚺₁ ⪯ T]
    [T.SoundOnHierarchy 𝚺 1] : DeductiveProcessComputation (paperBaseDP T) :=
  (theoremPaperDPComputation T).union
    (paperCutLawDP_computable T).nonemptyComputation.some

lemma paperBaseDP_hworld_of_model [T.Δ₁] [𝗜𝚺₁ ⪯ T]
    [T.SoundOnHierarchy 𝚺 1]
    {M : Type*} [Nonempty M] [Structure ℒₒᵣ M]
    (hT : M ↓[ℒₒᵣ] ⊧* T) (f : ℕ → M) :
    (paperTheoryExtensionWorld T M f).ConsistentWithTheory (paperBaseDP T) := by
  intro k sentence hsentence
  rw [paperBaseDP, DeductiveProcess.union_stage, Finset.mem_union] at hsentence
  rcases hsentence with hbase | hcut
  · exact theoremPaperDP_hworld_of_model T hT f k sentence hbase
  · apply (PCWorld.holds_congr_atomCodes sentence fun a ha =>
      paperTheoryExtensionWorld_agree_paper T M f ?_).mpr
      (paperCutLawDP_hworld_of_model T hT f k sentence hcut)
    simp only [paperCutLawDP, paperCutLawStage, Finset.mem_image,
      Finset.mem_filter, Finset.mem_range] at hcut
    obtain ⟨e, ⟨-, hsome⟩, rfl⟩ := hcut
    apply paperCutLawSentence_atom_tag_of_fire T ?_ ha
    obtain ⟨out, hout⟩ := Option.isSome_iff_exists.mp hsome
    exact ((exists_paperCutLawCode T).choose_spec e).mp
      (Part.dom_iff_mem.mpr ⟨out, Nat.Partrec.Code.evaln_sound hout⟩)

lemma paperBaseDP_nonvacuous [T.Δ₁] [𝗜𝚺₁ ⪯ T]
    [T.SoundOnHierarchy 𝚺 1] :
    ∃ v : PCWorld, v.ConsistentWithTheory (paperBaseDP T) := by
  have hs : LO.FirstOrder.Satisfiable T :=
    LO.FirstOrder.Theory.small_satisfiable_of_consistent (T := T) inferInstance
  rcases LO.FirstOrder.satisfiable_iff.mp hs with ⟨M, hMne, hMstr, hT⟩
  letI : Nonempty M := hMne
  letI : Structure ℒₒᵣ M := hMstr
  let f : ℕ → M := fun _ => Classical.choice hMne
  exact ⟨paperTheoryExtensionWorld T M f, paperBaseDP_hworld_of_model T hT f⟩

lemma paperBaseDP_semanticPrimeFresh [T.Δ₁] [𝗜𝚺₁ ⪯ T]
    [T.SoundOnHierarchy 𝚺 1] (k : ℕ) (sentence : Sentence)
    (hsentence : sentence ∈ (paperBaseDP T).D k) :
    SemanticPrimeFreshSentence sentence := by
  intro a ha
  rw [paperBaseDP, DeductiveProcess.union_stage, Finset.mem_union] at hsentence
  rcases hsentence with hbase | hcut
  · rw [theoremPaperDP, DeductiveProcess.union_stage, Finset.mem_union] at hbase
    rcases hbase with htheorem | hpaper
    · exact theoremDP_semanticPrimeFresh T k sentence htheorem a ha
    · have htag := paperTheoryDP_atom_tag T hpaper ha
      simp [htag, paperPrimeTag, semanticPrimeTag]
  · simp only [paperCutLawDP, paperCutLawStage, Finset.mem_image,
      Finset.mem_filter, Finset.mem_range] at hcut
    obtain ⟨e, ⟨-, hsome⟩, rfl⟩ := hcut
    have hfire : paperCutLawFires T e := by
      obtain ⟨out, hout⟩ := Option.isSome_iff_exists.mp hsome
      exact ((exists_paperCutLawCode T).choose_spec e).mp
        (Part.dom_iff_mem.mpr ⟨out, Nat.Partrec.Code.evaln_sound hout⟩)
    have htag := paperCutLawSentence_atom_tag_of_fire T hfire ha
    simp [htag, paperPrimeTag, semanticPrimeTag]

#print axioms paperCutLawFires_re
#print axioms paperCutLawSentence_prim
#print axioms paperCutLawDP_computable
#print axioms paperCutLawDP_hworld_of_model
#print axioms paperBaseDPComputation
#print axioms paperBaseDP_nonvacuous
#print axioms paperBaseDP_semanticPrimeFresh

end LogicalInduction
