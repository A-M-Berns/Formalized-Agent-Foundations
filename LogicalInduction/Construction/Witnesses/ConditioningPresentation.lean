import LogicalInduction.Construction.Witnesses.BoundedEvaluation
import LogicalInduction.Properties.Conditioning

/-!
# Concrete finite-stage presentation for Closure Under Conditioning

This file constructs the `ConditioningPresentation` that `thm:scon` takes as input, so
that no caller has to assume one.  The condition on day `n` is the canonical finite
conjunction of the extra deductive stage; its Boolean semantics and the computation of the
union process are derived here.  Polynomial naming is supplied by an operational
certificate for the extra process: the certificate contains one program that emits the
actual conjunction code with polynomial fuel, rather than treating the semantic stage
function as a polynomial oracle.
-/

namespace LogicalInduction

open LO.Propositional

/-! ### Canonical finite conjunction -/

/-- The sentence asserting every member of a finite deductive stage.  `Finset.conj` uses
the code-canonical `Finset` order, and the empty conjunction is `⊤`. -/
noncomputable def deductiveStageCondition (stage : Finset Sentence) : Sentence := stage.conj

@[simp] theorem PCWorld.holds_deductiveStageCondition
    (v : PCWorld) (stage : Finset Sentence) :
    v.Holds (deductiveStageCondition stage) ↔ v.ConsistentWith stage := by
  have hlist (l : List Sentence) :
      LO.Propositional.Formula.Boolean.val v l.conj₂ ↔
        ∀ φ ∈ l, LO.Propositional.Formula.Boolean.val v φ := by
    induction l using List.induction_with_singleton' <;>
      simp_all [LO.Propositional.Formula.Boolean.val]
  simpa [deductiveStageCondition, PCWorld.Holds, PCWorld.ConsistentWith,
    Finset.conj] using hlist stage.toList

/-! ### Canonical encoded union

The stock `Finset Sentence` encoding is the encoding of its code-sorted list.  The LIA
compiler already proves primitive-recursive code sorting and duplicate removal.  We expose
one normalizer built from those existing pieces and use it after pairing two stage outputs.
-/

/-- Code-sorted duplicate-free union of two encoded sentence lists.  Malformed list codes
decode as the empty list; certified deductive-process outputs always take the valid branch. -/
def sentenceFinsetUnionNorm (z : ℕ) : ℕ :=
  let left := (Encodable.decode (α := List Sentence) z.unpair.1).getD []
  let right := (Encodable.decode (α := List Sentence) z.unpair.2).getD []
  Encodable.encode <|
    (sentenceDedup (left ++ right)).insertionSort sentenceCodeLE

lemma sentenceFinsetUnionNorm_prim : Primrec sentenceFinsetUnionNorm := by
  have hleft : Primrec fun z : ℕ ↦
      (Encodable.decode (α := List Sentence) z.unpair.1).getD [] :=
    Primrec.option_getD.comp
      (Primrec.decode.comp (Primrec.fst.comp Primrec.unpair)) (Primrec.const [])
  have hright : Primrec fun z : ℕ ↦
      (Encodable.decode (α := List Sentence) z.unpair.2).getD [] :=
    Primrec.option_getD.comp
      (Primrec.decode.comp (Primrec.snd.comp Primrec.unpair)) (Primrec.const [])
  have happend : Primrec fun z : ℕ ↦
      (Encodable.decode (α := List Sentence) z.unpair.1).getD [] ++
        (Encodable.decode (α := List Sentence) z.unpair.2).getD [] :=
    Primrec.list_append.comp hleft hright
  exact (Primrec.encode.comp
    (sentenceInsertionSort_prim.comp (sentenceDedup_prim.comp happend))).of_eq
      fun z ↦ by rfl

lemma sentenceFinsetUnionNorm_spec (left right : Finset Sentence) :
    sentenceFinsetUnionNorm
        (Nat.pair (Encodable.encode left) (Encodable.encode right)) =
      Encodable.encode (left ∪ right) := by
  let canonical :=
    (sentenceDedup (stageSort left ++ stageSort right)).insertionSort sentenceCodeLE
  have hnodup : canonical.Nodup :=
    (List.perm_insertionSort sentenceCodeLE _).nodup_iff.mpr
      (sentenceDedup_nodup (stageSort left ++ stageSort right))
  have hsorted : canonical.Pairwise sentenceCodeLE :=
    List.pairwise_insertionSort sentenceCodeLE _
  have htoFinset : canonical.toFinset = left ∪ right := by
    ext φ
    simp [canonical]
  have hsort : (left ∪ right).sort sentenceCodeLE = canonical := by
    rw [← htoFinset]
    exact (List.toFinset_sort (r := sentenceCodeLE) hnodup).mpr hsorted
  simp only [sentenceFinsetUnionNorm, Nat.unpair_pair]
  rw [encode_eq_encode_stageSort left, encode_eq_encode_stageSort right]
  simp only [Encodable.encodek, Option.getD_some]
  calc
    Encodable.encode
        ((sentenceDedup (stageSort left ++ stageSort right)).insertionSort
          sentenceCodeLE) = Encodable.encode canonical := rfl
    _ = Encodable.encode ((left ∪ right).sort sentenceCodeLE) :=
      congrArg Encodable.encode hsort.symm
    _ = Encodable.encode (left ∪ right) :=
      (encode_eq_encode_stageSort (left ∪ right)).symm

/-- One fixed partial-recursive program normalizes a pair of encoded stages to their
encoded union. -/
lemma exists_sentenceFinsetUnionCode :
    ∃ code : Nat.Partrec.Code, ∀ left right : Finset Sentence,
      Encodable.encode (left ∪ right) ∈
        code.eval (Nat.pair (Encodable.encode left) (Encodable.encode right)) := by
  obtain ⟨code, hcode⟩ := Nat.Partrec.Code.exists_code.mp
    (Nat.Partrec.of_primrec (Primrec.nat_iff.mp sentenceFinsetUnionNorm_prim))
  refine ⟨code, fun left right ↦ ?_⟩
  rw [hcode]
  exact Part.mem_some_iff.mpr (sentenceFinsetUnionNorm_spec left right).symm

/-- Stagewise union computation obtained by explicitly pairing the two certified stage
programs and applying the canonical finite-set union normalizer. -/
noncomputable def DeductiveProcessComputation.union
    {DP extra : DeductiveProcess}
    (base : DeductiveProcessComputation DP)
    (more : DeductiveProcessComputation extra) :
    DeductiveProcessComputation (DP.union extra) := by
  classical
  choose unionCode hunion using exists_sentenceFinsetUnionCode
  refine ⟨unionCode.comp (base.code.pair more.code), fun n ↦ ?_⟩
  have hbase : base.code.eval n = Part.some (Encodable.encode (DP.D n)) :=
    Part.eq_some_iff.mpr (base.code_spec n)
  have hmore : more.code.eval n = Part.some (Encodable.encode (extra.D n)) :=
    Part.eq_some_iff.mpr (more.code_spec n)
  have hnormalized : unionCode.eval
      (Nat.pair (Encodable.encode (DP.D n)) (Encodable.encode (extra.D n))) =
        Part.some (Encodable.encode (DP.D n ∪ extra.D n)) :=
    Part.eq_some_iff.mpr (hunion (DP.D n) (extra.D n))
  simp [Nat.Partrec.Code.eval, hbase, hmore, hnormalized, Seq.seq]

lemma DeductiveProcessComputation.union_toComputable
    {DP extra : DeductiveProcess}
    (base : DeductiveProcessComputation DP)
    (more : DeductiveProcessComputation extra) :
    ComputableDeductiveProcess (DP.union extra) :=
  (base.union more).toComputable

/-! ### Public presentation constructor -/

/-- Honest operational input for efficient condition naming.  The ordinary stage program
is retained for the union construction.  `condition_codes` says the *actual* finite
conjunctions form an 𝓔𝓒 sentence sequence (`def:ec`, symbol-metered); it assumes no
prices, trades, wealth bound, exploitation fact, or logical-inductor conclusion.

This strengthening is necessary: `ComputableDeductiveProcess` alone promises termination
but no efficiency bound.  Metering **symbols** rather than the whole pair-code value is
what keeps the growing form realizable: `deductiveStageCondition (extra.D n)` is a
conjunction of `|extra.D n|` sentences, so it is deep, and its pair code is exponential
in its symbol count.
Paper node: `thm:scon`, `def:ec` -/
structure CompactConditioningProcessComputation (extra : DeductiveProcess)
    extends DeductiveProcessComputation extra where
  condition_codes : RpnSentenceCodes fun n ↦ deductiveStageCondition (extra.D n)

/-- **Inhabitation only, and degenerate.**  The compact operational interface is inhabited by
the constantly empty deductive process, whose stage program and empty-conjunction program
are both literal constant programs.  This says the interface's fields are satisfiable and
nothing more: at `extra.D n = ∅` the adjoined condition is the empty conjunction `⊤` and
`DP.union extra = DP`, so instantiating the growing form of `thm:scon` here restates the
unconditioned theorem.  It is **not** evidence that the growing endpoint has content; the
witness that carries that burden is `growingCompactConditioningProcessComputation` below,
put to work in `exists_growing_conditioned_machine_inductor`. -/
lemma compactConditioningProcessComputation_nonempty :
    ∃ extra : DeductiveProcess,
      Nonempty (CompactConditioningProcessComputation extra) := by
  let extra : DeductiveProcess :=
    { D := fun _ ↦ ∅
      mono := fun _ φ hφ ↦ by simp at hφ }
  refine ⟨extra, ⟨{
    code := Nat.Partrec.Code.const (Encodable.encode (∅ : Finset Sentence))
    code_spec := fun n ↦ by simp [extra]
    condition_codes := RpnSentenceCodes.ofPolySentenceCodes
      ⟨_, (PolyFueled.const
        (Encodable.encode (deductiveStageCondition (∅ : Finset Sentence)))).of_eq
          (fun n ↦ by simp [extra])⟩ }⟩⟩

/-- Construct the exact syntax/semantics presentation used by `thm:scon` from operational
programs for the base process and the compact extra process.
Paper node: `thm:scon` -/
noncomputable def conditioningPresentationOfComputations
    {DP extra : DeductiveProcess}
    (base : DeductiveProcessComputation DP)
    (more : CompactConditioningProcessComputation extra) :
    ConditioningPresentation DP extra where
  condition n := deductiveStageCondition (extra.D n)
  condition_codes := more.condition_codes
  holds_condition n v := v.holds_deductiveStageCondition (extra.D n)
  combined_computable := base.union_toComputable more.toDeductiveProcessComputation

/-! ### A genuinely growing extra process

`compactConditioningProcessComputation_nonempty` above shows only that the interface is
*inhabited*: its witness has `extra.D n = ∅` at every stage, so the adjoined condition is
the empty conjunction `⊤` and `DP.union extra = DP`.  That witness is therefore no evidence
that the growing form of `thm:scon` says anything, and it is not cited as such.

The process below is the honest one.  It reveals `atom 0` on day `0` and adds `atom 1` from
day `1` on, so its stages are nonempty, they *strictly grow*, and the condition sequence
`n ↦ ⋀ (extra.D n)` genuinely changes with `n`: `atom 0` at day `0` and a two-conjunct
conjunction thereafter.  Its condition-code certificate is a two-way dispatch of constant
sentence-block streams, which is what keeps this witness cheap.

It is an *eventually constant* growing process, and deliberately so.  An unboundedly growing
one — say `extra.D n = {atom 0, …, atom (n-1)}` — is not reachable at this cost: the
`n`-conjunct condition has code exponential in its symbol count, so the whole-value
interface `PolySentenceCodes` is unavailable by construction, and the symbol-metered route
`RpnSentenceCodes.ofCanonical` needs a variable-width *conjunction* block combinator
(`RpnSentenceCodes.bigOr` is the disjunction analogue, and `Finset.conj` is `conj₂` of the
`toList`, which has no `⊤` terminator to close the chain on) together with an emitter for
the `Finset.toList` order.  Neither exists here.
-/

/-- The atoms adjoined by `growingConditionProcess`. -/
def growingConditionAtom (i : ℕ) : Sentence := LO.Propositional.Formula.atom i

lemma growingConditionAtom_zero_ne_one :
    growingConditionAtom 0 ≠ growingConditionAtom 1 := by
  simp [growingConditionAtom]

/-- A strictly growing extra deductive process: `{atom 0}` on day `0`, `{atom 0, atom 1}`
from day `1` on. -/
def growingConditionProcess : DeductiveProcess where
  D := fun n =>
    if n = 0 then {growingConditionAtom 0}
    else {growingConditionAtom 0, growingConditionAtom 1}
  mono := by
    intro n
    cases n with
    | zero => simp
    | succ m => simp

@[simp] lemma growingConditionProcess_zero :
    growingConditionProcess.D 0 = {growingConditionAtom 0} := rfl

@[simp] lemma growingConditionProcess_succ (n : ℕ) :
    growingConditionProcess.D (n + 1) =
      {growingConditionAtom 0, growingConditionAtom 1} := rfl

/-- The stages strictly grow: the adjoined theory is not constant. 
Paper node: `thm:scon` -/
lemma growingConditionProcess_ssubset :
    growingConditionProcess.D 0 ⊂ growingConditionProcess.D 1 := by
  rw [growingConditionProcess_zero, show (1 : ℕ) = 0 + 1 from rfl,
    growingConditionProcess_succ]
  refine Finset.ssubset_iff_of_subset (by simp) |>.mpr ⟨growingConditionAtom 1, by simp, ?_⟩
  simp [Ne.symm growingConditionAtom_zero_ne_one]

lemma growingConditionProcess_nonempty (n : ℕ) :
    (growingConditionProcess.D n).Nonempty := by
  cases n <;> simp

private lemma growingConditionProcess_primrec :
    Primrec fun n : ℕ => Encodable.encode (growingConditionProcess.D n) := by
  classical
  have h : Primrec fun n : ℕ =>
      if n = 0 then Encodable.encode ({growingConditionAtom 0} : Finset Sentence)
      else Encodable.encode
        ({growingConditionAtom 0, growingConditionAtom 1} : Finset Sentence) :=
    Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 0))
      (Primrec.const _) (Primrec.const _)
  exact h.of_eq fun n => by
    cases n with
    | zero => simp
    | succ m => simp

private lemma exists_growingConditionProcessCode :
    ∃ code : Nat.Partrec.Code, ∀ n,
      Encodable.encode (growingConditionProcess.D n) ∈ code.eval n := by
  obtain ⟨code, hcode⟩ := Nat.Partrec.Code.exists_code.mp
    (Nat.Partrec.of_primrec (Primrec.nat_iff.mp growingConditionProcess_primrec))
  exact ⟨code, fun n => by rw [hcode]; exact Part.mem_some_iff.mpr rfl⟩

/-- The strictly growing process is computable, by a two-way dispatch between two constant
stage codes. 
Paper node: `thm:scon` -/
noncomputable def growingConditionProcessComputation :
    DeductiveProcessComputation growingConditionProcess :=
  ⟨exists_growingConditionProcessCode.choose,
    exists_growingConditionProcessCode.choose_spec⟩

private lemma growingConditionProcess_condition_codes :
    RpnSentenceCodes fun n => deductiveStageCondition (growingConditionProcess.D n) :=
  (RpnSentenceCodes.ifZero
      (RpnSentenceCodes.const
        (deductiveStageCondition ({growingConditionAtom 0} : Finset Sentence)))
      (RpnSentenceCodes.const (deductiveStageCondition
        ({growingConditionAtom 0, growingConditionAtom 1} : Finset Sentence)))
      PolyFueled.id).of_eq (fun n => by
    cases n with
    | zero => simp
    | succ m => simp)

/-- **`N+` witness with content.**  The compact conditioning interface is inhabited by a
process whose stages are nonempty and strictly growing, so the growing form of `thm:scon`
instantiated here adjoins a real, changing condition rather than the empty conjunction. 
Paper node: `thm:scon` -/
noncomputable def growingCompactConditioningProcessComputation :
    CompactConditioningProcessComputation growingConditionProcess where
  toDeductiveProcessComputation := growingConditionProcessComputation
  condition_codes := growingConditionProcess_condition_codes

/-- The day-`0` condition is the atom itself. -/
lemma deductiveStageCondition_growing_zero :
    deductiveStageCondition (growingConditionProcess.D 0) = growingConditionAtom 0 := by
  simp [deductiveStageCondition, Finset.conj]

/-- From day `1` on the condition is a genuine two-conjunct conjunction.  The conjuncts are
`atom 0` and `atom 1` in whatever order `Finset.toList` produces; only the shape matters
here. -/
lemma deductiveStageCondition_growing_succ (n : ℕ) :
    ∃ x y : Sentence,
      deductiveStageCondition (growingConditionProcess.D (n + 1)) = x ⋏ y := by
  classical
  have hcard : (growingConditionProcess.D (n + 1)).card = 2 := by
    rw [growingConditionProcess_succ,
      Finset.card_insert_of_notMem (by simp [growingConditionAtom_zero_ne_one]),
      Finset.card_singleton]
  have hlen : (growingConditionProcess.D (n + 1)).toList.length = 2 := by
    rw [Finset.length_toList, hcard]
  obtain ⟨x, y, hxy⟩ := List.length_eq_two.mp hlen
  exact ⟨x, y, by rw [deductiveStageCondition, Finset.conj, hxy]; rfl⟩

/-- **No stage's condition is the empty conjunction.**  This is the property the degenerate
inhabitant fails: at `extra.D n = ∅` every condition is `⊤`, and conditioning on `⊤` is not
conditioning. 
Paper node: `thm:scon` -/
lemma deductiveStageCondition_growing_ne_top (n : ℕ) :
    deductiveStageCondition (growingConditionProcess.D n) ≠ ⊤ := by
  cases n with
  | zero => rw [deductiveStageCondition_growing_zero]; simp [growingConditionAtom]
  | succ m =>
      obtain ⟨x, y, hxy⟩ := deductiveStageCondition_growing_succ m
      rw [hxy]
      simp

/-- **The condition sequence genuinely changes with the stage.**  Day `0` names a single
atom; every later day names a two-conjunct conjunction.  Together with
`deductiveStageCondition_growing_ne_top` this is what makes the growing form of `thm:scon`
say something about *growing* conditioning when instantiated here. 
Paper node: `thm:scon` -/
lemma deductiveStageCondition_growing_ne :
    deductiveStageCondition (growingConditionProcess.D 0) ≠
      deductiveStageCondition (growingConditionProcess.D 1) := by
  obtain ⟨x, y, hxy⟩ := deductiveStageCondition_growing_succ 0
  rw [deductiveStageCondition_growing_zero, show (1 : ℕ) = 0 + 1 from rfl, hxy]
  simp [growingConditionAtom]

/-! ### Fixed-condition presentation -/

/-- The constant deductive process containing one fixed conditioning sentence. -/
def fixedConditionProcess (ψ : Sentence) : DeductiveProcess where
  D := fun _ => {ψ}
  mono := fun _ _ hφ => hφ

/-- Adjoin one fixed sentence to every stage of a deductive process. -/
def DeductiveProcess.adjoinSentence (DP : DeductiveProcess) (ψ : Sentence) :
    DeductiveProcess :=
  DP.union (fixedConditionProcess ψ)

/-- Exact constant-time computation of the one-sentence deductive process. -/
def fixedConditionProcessComputation (ψ : Sentence) :
    DeductiveProcessComputation (fixedConditionProcess ψ) where
  code := Nat.Partrec.Code.const (Encodable.encode ({ψ} : Finset Sentence))
  code_spec := fun _ => by simp [fixedConditionProcess]

/-- The fixed-condition instance of the shared `thm:scon` presentation.
Paper node: `thm:scon` -/
noncomputable def fixedConditioningPresentation
    {DP : DeductiveProcess} (base : DeductiveProcessComputation DP)
    (ψ : Sentence) :
    ConditioningPresentation DP (fixedConditionProcess ψ) where
  condition := fun _ => ψ
  condition_codes :=
    RpnSentenceCodes.ofPolySentenceCodes
      ⟨Nat.Partrec.Code.const (Encodable.encode ψ),
        (PolyFueled.const (Encodable.encode ψ)).of_eq (fun _ => rfl)⟩
  holds_condition := by
    intro n v
    simp [fixedConditionProcess, PCWorld.ConsistentWith]
  combined_computable :=
    base.union_toComputable (fixedConditionProcessComputation ψ)

/-- Closure under conditioning with the presentation argument discharged by the concrete
finite-conjunction and union construction above.
Paper node: `thm:scon` -/
theorem lic_conditioned_gated_ofComputations
    (P : History) (DP extra : DeductiveProcess) [IsLogicalInductor P DP]
    (base : DeductiveProcessComputation DP)
    (more : CompactConditioningProcessComputation extra) {epsilon : ℚ}
    (W : GatedConditioningOperationalWitness P DP extra
      (conditioningPresentationOfComputations base more) epsilon) :
    IsLogicalInductor
      (conditionedHistory P (fun n ↦ deductiveStageCondition (extra.D n)))
      (DP.union extra) :=
  lic_conditioned_gated P DP extra
    (conditioningPresentationOfComputations base more) W

#print axioms PCWorld.holds_deductiveStageCondition
#print axioms DeductiveProcessComputation.union
#print axioms compactConditioningProcessComputation_nonempty
#print axioms conditioningPresentationOfComputations
#print axioms fixedConditioningPresentation
#print axioms growingConditionProcessComputation
#print axioms growingCompactConditioningProcessComputation
#print axioms growingConditionProcess_ssubset
#print axioms deductiveStageCondition_growing_ne
#print axioms deductiveStageCondition_growing_ne_top
#print axioms lic_conditioned_gated_ofComputations

end LogicalInduction
