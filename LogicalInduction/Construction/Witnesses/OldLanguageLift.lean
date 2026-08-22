import LogicalInduction.Construction.Witnesses.SemanticSource
import LogicalInduction.Construction.Witnesses.FiniteEntailment

/-!
# A fixed old-language copy

The semantic-prime obstruction is a vocabulary-ownership obstruction: a flat source may
already mention the atoms later used as semantic handles.  This file supplies one fixed
renaming, chosen independently of any source family, market, weight, or deferral.  There
are deliberately no axioms identifying the renamed atoms with their original names.
-/

namespace LogicalInduction

open LO LO.Propositional

/-- Reserved outer tag for the fixed copy of the pre-extension propositional language. -/
def oldLanguageTag : ℕ := 8

/-- The atom injection into the fixed old-language namespace. -/
def oldAtom (a : ℕ) : ℕ := Nat.pair oldLanguageTag a

/-- Syntactically rename every atom into the fixed old-language namespace. -/
def liftSentence (phi : Sentence) : Sentence :=
  phi⟦fun a => Formula.atom (oldAtom a)⟧

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

/-- Pointwise fixed old-language copy of a source sequence. -/
def liftLUVSeq (X : ℕ → LUV) : ℕ → LUV := fun n => liftLUV (X n)

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

/-- Lifted atoms cannot collide with semantic-prime atoms. -/
lemma oldAtom_ne_semanticPrimeCode (a schema input : ℕ) :
    oldAtom a ≠ semanticPrimeCode schema input := by
  intro h
  have := congrArg (fun n : ℕ => n.unpair.1) h
  simp [oldAtom, oldLanguageTag, semanticPrimeCode, semanticPrimeTag] at this

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

/-- Computability of the fixed old-language copy. -/
lemma liftDP_computable {DP : DeductiveProcess}
    (base : DeductiveProcessComputation DP) :
    ComputableDeductiveProcess (liftDP DP) :=
  (liftDPComputation base).toComputable

/-! ## Cut laws derived from the paper-facing valuedness premise -/

/-- Valuedness over the original process automatically gives the lower bound law in the
fixed renamed copy. -/
lemma liftLUV_holds_below_zero_of_valued {DP : DeductiveProcess} {X : LUV}
    (source_valued : ∀ v : PCWorld,
      v.ConsistentWithTheory DP → ∃ x, v.ValuesAt X x)
    {v : PCWorld} (hv : v.ConsistentWithTheory (liftDP DP))
    {r : ℚ} (hr : r < 0) :
    v.Holds ((liftLUV X).gt r) := by
  obtain ⟨x, hx⟩ := source_valued (pullOldWorld v)
    ((consistentWithTheory_liftDP_iff v DP).mp hv)
  exact (liftLUV_valuesAt_iff v X x).mpr hx |>.2.2 r |>.1
    (lt_of_lt_of_le (by exact_mod_cast hr) hx.1)

/-- Valuedness over the original process automatically gives the upper bound law in the
fixed renamed copy. -/
lemma liftLUV_not_holds_above_one_of_valued {DP : DeductiveProcess} {X : LUV}
    (source_valued : ∀ v : PCWorld,
      v.ConsistentWithTheory DP → ∃ x, v.ValuesAt X x)
    {v : PCWorld} (hv : v.ConsistentWithTheory (liftDP DP))
    {r : ℚ} (hr : 1 < r) :
    ¬v.Holds ((liftLUV X).gt r) := by
  obtain ⟨x, hx⟩ := source_valued (pullOldWorld v)
    ((consistentWithTheory_liftDP_iff v DP).mp hv)
  exact (liftLUV_valuesAt_iff v X x).mpr hx |>.2.2 r |>.2
    (lt_of_le_of_lt hx.2.1 (by exact_mod_cast hr))

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
caller-supplied cut certificate. -/
lemma liftLUV_downward_eventually_stageEntails {DP : DeductiveProcess} {X : LUV}
    (source_valued : ∀ v : PCWorld,
      v.ConsistentWithTheory DP → ∃ x, v.ValuesAt X x)
    {r s : ℚ} (hrs : r < s) :
    ∃ k, stageEntails ((liftDP DP).D k)
      ((liftLUV X).gt s 🡒 (liftLUV X).gt r) = true := by
  apply DeductiveProcess.stageEntails_complete_of_semantic
  intro v hv
  exact liftLUV_holds_downward_of_valued source_valued hv hrs

#print axioms holds_liftSentence_iff
#print axioms liftLUV_valuesAt_iff
#print axioms consistentWithTheory_liftDP_iff
#print axioms liftSentence_primrec
#print axioms liftDP_computable
#print axioms liftLUV_holds_downward_of_valued
#print axioms liftLUV_downward_eventually_stageEntails

end LogicalInduction
