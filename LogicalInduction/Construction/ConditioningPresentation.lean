import LogicalInduction.Construction.M7Witnesses
import LogicalInduction.Properties.Conditioning

/-!
# Concrete finite-stage presentation for Closure Under Conditioning

This file constructs `M7-SCON-PRESENTATION`.  The condition on day `n` is the canonical
finite conjunction of the extra deductive stage.  Its Boolean semantics and the computation
of the union process are derived here.  Polynomial naming is supplied by an operational
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

theorem sentenceFinsetUnionNorm_prim : Primrec sentenceFinsetUnionNorm := by
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

theorem sentenceFinsetUnionNorm_spec (left right : Finset Sentence) :
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
theorem exists_sentenceFinsetUnionCode :
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

theorem DeductiveProcessComputation.union_toComputable
    {DP extra : DeductiveProcess}
    (base : DeductiveProcessComputation DP)
    (more : DeductiveProcessComputation extra) :
    ComputableDeductiveProcess (DP.union extra) :=
  (base.union more).toComputable

/-! ### Public presentation constructor -/

/-- Honest operational input for polynomial condition naming.  The ordinary stage program
is retained for the union construction.  `condition_code_poly` says a single program emits
the code of the *actual* finite conjunction within polynomial fuel; it assumes no prices,
trades, wealth bound, exploitation fact, or logical-inductor conclusion.

This strengthening is necessary: `ComputableDeductiveProcess` alone promises termination
but no polynomial runtime or output-size bound. -/
structure CompactConditioningProcessComputation (extra : DeductiveProcess)
    extends DeductiveProcessComputation extra where
  condition_code : Nat.Partrec.Code
  condition_code_poly : PolyFueled condition_code
    (fun n ↦ Encodable.encode (deductiveStageCondition (extra.D n)))

/-- `N+` witness: the compact operational interface is inhabited by the constantly empty
deductive process.  Its stage program and empty-conjunction program are both literal
constant programs. -/
theorem compactConditioningProcessComputation_nonempty :
    ∃ extra : DeductiveProcess,
      Nonempty (CompactConditioningProcessComputation extra) := by
  let extra : DeductiveProcess :=
    { D := fun _ ↦ ∅
      mono := fun _ φ hφ ↦ by simp at hφ }
  refine ⟨extra, ⟨{
    code := Nat.Partrec.Code.const (Encodable.encode (∅ : Finset Sentence))
    code_spec := fun n ↦ by simp [extra]
    condition_code := Nat.Partrec.Code.const
      (Encodable.encode (deductiveStageCondition (∅ : Finset Sentence)))
    condition_code_poly := (PolyFueled.const
      (Encodable.encode (deductiveStageCondition (∅ : Finset Sentence)))).of_eq
        (fun n ↦ by simp [extra]) }⟩⟩

/-- Construct the exact syntax/semantics presentation used by `thm:scon` from operational
programs for the base process and the compact extra process. -/
noncomputable def conditioningPresentationOfComputations
    {DP extra : DeductiveProcess}
    (base : DeductiveProcessComputation DP)
    (more : CompactConditioningProcessComputation extra) :
    ConditioningPresentation DP extra where
  condition n := deductiveStageCondition (extra.D n)
  condition_codes := ⟨more.condition_code, more.condition_code_poly⟩
  holds_condition n v := v.holds_deductiveStageCondition (extra.D n)
  combined_computable := base.union_toComputable more.toDeductiveProcessComputation

/-- Closure under conditioning with the presentation argument discharged by the concrete
finite-conjunction and union construction above. -/
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
#print axioms lic_conditioned_gated_ofComputations

end LogicalInduction
