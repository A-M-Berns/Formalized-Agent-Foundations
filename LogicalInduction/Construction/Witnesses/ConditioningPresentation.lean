import LogicalInduction.Construction.Witnesses.BoundedEvaluation
import LogicalInduction.Properties.Conditioning

/-!
# Concrete presentations for Closure Under Conditioning

`thm:scon` takes a `ConditioningPresentation` as data.  This file constructs one in three
forms, so that no caller of `lic_conditioned` / `lic_conditioned_machine` has to assume one.

**Shared machinery.**  `deductiveStageCondition` is the canonical finite conjunction of a
deductive stage under the code-canonical `Finset` order (empty conjunction `⊤`), with its
exact Boolean semantics `PCWorld.holds_deductiveStageCondition`;
`sentenceFinsetUnionNorm` and `sentenceListFinsetNorm` are the primitive-recursive
normalizers behind `DeductiveProcessComputation.union`, which computes the union process a
presentation must certify.

**Form 1, fixed condition** (`fixedConditionProcess`, `fixedConditioningPresentation`): the
paper's `Θ ∪ {ψ}` case, tex:6124.

**Form 2, compact growing** (`CompactConditioningProcessComputation`,
`conditioningPresentationOfComputations`, `lic_conditioned_gated_ofComputations`): the
certificate carries a program emitting the actual conjunction code at the write-out class
`BigSentenceCodes`, so a stage condition's Gödel code may be exponential in the day.  The
certificate is destructured as emission data by `CondStep.machineSentenceBlocks_of_big`.

**Form 3, prefix conjunctions from an arbitrary e.c. sequence** (`prefixProcess`,
`prefixProcessComputation`, `prefixConditioningPresentation`): the paper's own quantifier
for the growing form (tex:1613-1618, appendix tex:6126), with write-out efficiency of the
conditions derived from `BigSentenceCodes ψ` through `BigSentenceCodes.bigAnd`.  It is
consumed by `ConditioningCompile.lic_conditioned_growing_machine_ofSequence`.

**One design fact.**  In form 3 the condition is written in index order through the free
`condition` field of `ConditioningPresentation`, not through
`deductiveStageCondition (extra.D n) = (extra.D n).toList.conj₂`: the `Finset.toList` order
is recoverable only from exponential Gödel codes, `conj₂` is not permutation-invariant, and
the index order the emitter needs is erased by the `Finset`.  The `Finset` process is kept
only for the order-insensitive `holds_condition` and for the union computation.

**Non-vacuity.**  `growingCompactConditioningProcessComputation` adjoins stages that are
nonempty and strictly grow (`growingConditionProcess_ssubset`,
`deductiveStageCondition_growing_ne`, `deductiveStageCondition_growing_ne_top`), so the
growing form says something; `compactConditioningProcessComputation_nonempty` is
inhabitation only and carries no such content.
-/

namespace LogicalInduction

open LO.Propositional

/-! ## Canonical finite conjunction -/

/-- The sentence asserting every member of a finite deductive stage.  `Finset.conj` uses
the code-canonical `Finset` order, and the empty conjunction is `⊤`. -/
noncomputable def deductiveStageCondition (stage : Finset Sentence) : Sentence := stage.conj

/-- A world satisfies a stage's canonical conjunction exactly when it is consistent with
that stage.  This is the exact Boolean semantics the `holds_condition` field of every
presentation in this file is discharged by. -/
@[simp] lemma PCWorld.holds_deductiveStageCondition
    (v : PCWorld) (stage : Finset Sentence) :
    v.Holds (deductiveStageCondition stage) ↔ v.ConsistentWith stage := by
  have hlist (l : List Sentence) :
      LO.Propositional.Formula.Boolean.val v l.conj₂ ↔
        ∀ φ ∈ l, LO.Propositional.Formula.Boolean.val v φ := by
    induction l using List.induction_with_singleton' <;>
      simp_all [LO.Propositional.Formula.Boolean.val]
  simpa [deductiveStageCondition, PCWorld.Holds, PCWorld.ConsistentWith,
    Finset.conj] using hlist stage.toList

/-! ## Canonical encoded union

The stock `Finset Sentence` encoding is the encoding of its code-sorted list.  The LIA
compiler already proves primitive-recursive code sorting and duplicate removal, and one
normalizer built from those pieces is applied after pairing two stage outputs.
-/

/-- Code-sorted duplicate-free union of two encoded sentence lists.  Malformed list codes
decode as the empty list; certified deductive-process outputs always take the valid branch. -/
def sentenceFinsetUnionNorm (z : ℕ) : ℕ :=
  let left := (Encodable.decode (α := List Sentence) z.unpair.1).getD []
  let right := (Encodable.decode (α := List Sentence) z.unpair.2).getD []
  Encodable.encode <|
    (sentenceDedup (left ++ right)).insertionSort sentenceCodeLE

/-- The union normalizer is primitive recursive. -/
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

/-- On a pair of encoded finite stages the normalizer computes the code of their union. -/
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

/-- The union of two computable deductive processes is a computable deductive process. -/
lemma DeductiveProcessComputation.union_toComputable
    {DP extra : DeductiveProcess}
    (base : DeductiveProcessComputation DP)
    (more : DeductiveProcessComputation extra) :
    ComputableDeductiveProcess (DP.union extra) :=
  (base.union more).toComputable

/-! ## The compact operational interface and its presentation -/

/-- Honest operational input for efficient condition naming.  The ordinary stage program
is retained for the union construction.  `condition_codes` says the *actual* finite
conjunctions are efficiently nameable; it assumes no prices, trades, wealth bound,
exploitation fact, or logical-inductor conclusion.

This strengthening is necessary: `ComputableDeductiveProcess` alone promises termination
but no efficiency bound.  Metering **tokens** rather than the whole pair-code value is
what keeps the growing form realizable: `deductiveStageCondition (extra.D n)` is a
conjunction of `|extra.D n|` sentences, so it is deep, and its pair code is exponential
in its symbol count.

This field is at `def:ec`'s own class, the write-out `BigSentenceCodes`: it bounds only
the number of digits a poly-time writer must emit and places no bound whatever on a
token's value, so a stage condition's Gödel code may be exponential in the day.  The
token-metered `RpnSentenceCodes` is a sufficient subclass, embedded by
`BigSentenceCodes.ofRpnSentenceCodes`, and is what the cheap witnesses in this file
happen to build; nothing on the `thm:scon` lane requires it.

The certificate is consumed as **emission data**, not as an opaque predicate:
`CondStep.machineSentenceBlocks_of_big` destructures it, clocks the digitization of its
block stream through `BigTokenStream.digitizeStream`, and runs
`TraderMachine.traderOutput`.  The digit clamp there is the identity because the clamped
object is a list of base-4 digits and terminators (`CondStep.mem_digitize_le_four`) — not
because token values are bounded — which is exactly why the write-out class suffices.
Paper node: `thm:scon`, `def:ec` -/
structure CompactConditioningProcessComputation (extra : DeductiveProcess)
    extends DeductiveProcessComputation extra where
  condition_codes : BigSentenceCodes fun n ↦ deductiveStageCondition (extra.D n)

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
    condition_codes := BigSentenceCodes.ofPolySentenceCodes
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

/-! ## A genuinely growing extra process

`compactConditioningProcessComputation_nonempty` above is inhabitation only, and degenerate
for the reason recorded at that lemma.  The process below carries the non-vacuity burden
instead: it reveals `atom 0` on day `0` and adds `atom 1` from day `1` on, so its stages are
nonempty, they *strictly grow*, and the condition sequence `n ↦ ⋀ (extra.D n)` changes with
`n` — `atom 0` at day `0`, a two-conjunct conjunction thereafter.  Its condition-code
certificate is a two-way dispatch of constant sentence-block streams, which is what keeps
this witness cheap.

The witness is eventually constant, for cheapness alone.  An unboundedly growing prefix
process `n ↦ {ψ₀, …, ψₙ}` over an arbitrary e.c. sequence is reachable: see `prefixProcess`
/ `prefixConditioningPresentation` below and the arbitrary-e.c.-sequence endpoint
`ConditioningCompile.lic_conditioned_growing_machine_ofSequence`
(`Construction/Machine/CondEndpoints.lean`).  The write-out class places no bound on a
condition's code value, so a condition whose code is exponential in its symbol count is
admissible, and `BigSentenceCodes.bigAnd` (`Framework/WriteOut.lean`) writes a
variable-width conjunction, closing the fold on the three-token `⊤ = [2, 0, 0]` terminator.

That combinator does not rescue the `deductiveStageCondition (extra.D n) =
(extra.D n).toList.conj₂` route used by `CompactConditioningProcessComputation`; the prefix
presentation writes the condition in index order through the free `condition` field
instead, for the reason recorded at the prefix-conjunction section below.
-/

/-- The atoms adjoined by `growingConditionProcess`. -/
def growingConditionAtom (i : ℕ) : Sentence := LO.Propositional.Formula.atom i

/-- The two adjoined atoms are distinct, which is what makes the growing stages strict. -/
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
    BigSentenceCodes fun n => deductiveStageCondition (growingConditionProcess.D n) :=
  (BigSentenceCodes.ifZero
      (BigSentenceCodes.const
        (deductiveStageCondition ({growingConditionAtom 0} : Finset Sentence)))
      (BigSentenceCodes.const (deductiveStageCondition
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

/-! ## Prefix conjunctions from an arbitrary e.c. sentence sequence

This form reaches the paper's own quantifier for the growing form of `thm:scon`
(tex:1613-1618, appendix tex:6126): the paper starts from an **arbitrary efficiently
computable individual-sentence sequence** `⟨ψ⟩` and conditions on the prefix conjunctions
`ψ₀ ⋏ ⋯ ⋏ ψₙ`.  `BigSentenceCodes.bigAnd` (`Framework/WriteOut.lean`) supplies
`BigSentenceCodes ψ → BigSentenceCodes (n ↦ ⋀_{i≤n} ψᵢ)`, so the write-out efficiency of
the growing conditions is derived from `BigSentenceCodes ψ` rather than taken as data.

Two design points make this go through where the `deductiveStageCondition` /
`CompactConditioningProcessComputation` route does not.  The condition sentence is written
in **index order** — `sentenceConjunction ((range (n+1)).map ψ)`, the poly-emittable shape
`bigAnd` produces — through the *free* `condition` field of `ConditioningPresentation`; and
the `Finset` prefix process is kept only for `holds_condition` (a set-membership fact,
insensitive to order and duplicates) and for the union computation.  Routing the condition
through `deductiveStageCondition (extra.D n) = (extra.D n).toList.conj₂` instead is not
poly-writable for a growing family: the `Finset.toList` order is recoverable only from
exponential Gödel codes and `conj₂` is not permutation-invariant, so the index order the
emitter needs is erased by the `Finset`. -/

/-- Primrec renaming of a sentence *list* to the Gödel code of the finite set it spans:
dedup, then code-sort, then encode.  The list-input analogue of `sentenceFinsetUnionNorm`,
used to compute the prefix process's stage codes from `(range (n+1)).map ψ`. -/
def sentenceListFinsetNorm (l : List Sentence) : ℕ :=
  Encodable.encode ((sentenceDedup l).insertionSort sentenceCodeLE)

/-- The list-input normalizer is primitive recursive. -/
lemma sentenceListFinsetNorm_prim : Primrec sentenceListFinsetNorm :=
  Primrec.encode.comp (sentenceInsertionSort_prim.comp sentenceDedup_prim)

/-- The normalizer computes the code of the finite set a sentence list spans. -/
lemma sentenceListFinsetNorm_spec (l : List Sentence) :
    sentenceListFinsetNorm l = Encodable.encode l.toFinset := by
  let canonical := (sentenceDedup l).insertionSort sentenceCodeLE
  have hnodup : canonical.Nodup :=
    (List.perm_insertionSort sentenceCodeLE _).nodup_iff.mpr (sentenceDedup_nodup l)
  have hsorted : canonical.Pairwise sentenceCodeLE :=
    List.pairwise_insertionSort sentenceCodeLE _
  have htoFinset : canonical.toFinset = l.toFinset := by
    ext φ; simp [canonical, mem_sentenceDedup]
  have hsort : l.toFinset.sort sentenceCodeLE = canonical := by
    rw [← htoFinset]
    exact (List.toFinset_sort (r := sentenceCodeLE) hnodup).mpr hsorted
  rw [sentenceListFinsetNorm, encode_eq_encode_stageSort l.toFinset, stageSort, hsort]

/-- The prefix deductive process of a sentence sequence: stage `n` is the finite set
`{ψ₀, …, ψₙ}`.  Its condition (below) is the prefix conjunction `ψ₀ ⋏ ⋯ ⋏ ψₙ`.
Paper node: `thm:scon` -/
def prefixProcess (ψ : ℕ → Sentence) : DeductiveProcess where
  D n := ((List.range (n + 1)).map ψ).toFinset
  mono n := by
    intro φ hφ
    simp only [List.mem_toFinset, List.mem_map, List.mem_range] at hφ ⊢
    obtain ⟨i, hi, rfl⟩ := hφ
    exact ⟨i, by omega, rfl⟩

/-- The prefix process's stage codes are primitive recursive: dedup-and-sort the list
`(range (n+1)).map ψ`, whose elements come from the primitive-recursive naming program
extracted from the write-out certificate `hψ` (`BigSentenceCodes.primrec`). -/
private lemma exists_prefixProcessCode (ψ : ℕ → Sentence) (hψ : BigSentenceCodes ψ) :
    ∃ code : Nat.Partrec.Code, ∀ n,
      Encodable.encode ((prefixProcess ψ).D n) ∈ code.eval n := by
  have hψp : Primrec ψ := Primrec.encode_iff.mp hψ.primrec
  have hrange : Primrec fun n : ℕ => List.range (n + 1) :=
    Primrec.list_range.comp (Primrec.nat_add.comp Primrec.id (Primrec.const 1))
  have hlist : Primrec fun n : ℕ => (List.range (n + 1)).map ψ :=
    Primrec.list_map hrange (hψp.comp Primrec.snd).to₂
  have hstage : Primrec fun n : ℕ =>
      sentenceListFinsetNorm ((List.range (n + 1)).map ψ) :=
    sentenceListFinsetNorm_prim.comp hlist
  obtain ⟨code, hcode⟩ := Nat.Partrec.Code.exists_code.mp
    (Nat.Partrec.of_primrec (Primrec.nat_iff.mp hstage))
  exact ⟨code, fun n => by
    rw [hcode]
    exact Part.mem_some_iff.mpr (sentenceListFinsetNorm_spec _).symm⟩

/-- The prefix process is computable, by the code extracted above.
Paper node: `thm:scon` -/
noncomputable def prefixProcessComputation (ψ : ℕ → Sentence) (hψ : BigSentenceCodes ψ) :
    DeductiveProcessComputation (prefixProcess ψ) :=
  ⟨(exists_prefixProcessCode ψ hψ).choose, (exists_prefixProcessCode ψ hψ).choose_spec⟩

/-- **Prefix-conjunction presentation.**  From `BigSentenceCodes ψ` alone, the growing
`thm:scon` presentation whose condition on day `n` is `ψ₀ ⋏ ⋯ ⋏ ψₙ` (index order, with a
harmless `⊤` tail from the empty-fold terminator), certified efficiently nameable by
`BigSentenceCodes.bigAnd`.  This is the presentation the arbitrary-e.c.-sequence endpoint
`lic_conditioned_growing_machine_ofSequence` consumes.
Paper node: `thm:scon` -/
noncomputable def prefixConditioningPresentation
    {DP : DeductiveProcess} (base : DeductiveProcessComputation DP)
    (ψ : ℕ → Sentence) (hψ : BigSentenceCodes ψ) :
    ConditioningPresentation DP (prefixProcess ψ) where
  condition n := sentenceConjunction ((List.range (n + 1)).map ψ)
  condition_codes :=
    (BigSentenceCodes.bigAnd (D := fun _ j => ψ j)
        (hψ.comp PolyFueled.right) (hcnt := PolyFueled.id.succ_comp)).of_eq (fun z => by rfl)
  holds_condition n v := by
    simp only [prefixProcess, holds_sentenceConjunction, PCWorld.ConsistentWith,
      List.mem_toFinset]
  combined_computable := base.union_toComputable (prefixProcessComputation ψ hψ)

/-! ## Fixed-condition presentation -/

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
    BigSentenceCodes.ofPolySentenceCodes
      ⟨Nat.Partrec.Code.const (Encodable.encode ψ),
        (PolyFueled.const (Encodable.encode ψ)).of_eq (fun _ => rfl)⟩
  holds_condition := by
    intro n v
    simp [fixedConditionProcess, PCWorld.ConsistentWith]
  combined_computable :=
    base.union_toComputable (fixedConditionProcessComputation ψ)

/-! ## The endpoint with the presentation discharged -/

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

end LogicalInduction
