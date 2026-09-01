import LogicalInduction.Construction.Witnesses.LUVArithmetic
import LogicalInduction.Construction.Witnesses.ComputationDP
import LogicalInduction.Properties.ExpectationProperties

/-!
# Deriving the LUV presentation interfaces from certified arithmetic (F7, item 3)

`Framework/Expectations.lean` and `Properties/ExpectationProperties.lean` state the world–value
coherence of LUVs as **caller-supplied hypotheses** — `PCWorld.ValuesAt`, `WorldValued`, and
`ExactTheoryPresentation` — with no arithmetic content behind them.  This file derives them
from a certified LUV syntax instead of assuming them.

This file does exactly that for the `dd:luv-arith` class (`LUVArithmetic.lean`).  The one
remaining premise is `ArithmeticLUVPresentation`: that the deductive process **reveals** the
`Θ`-provable threshold literals — the direct analogue of `ComputationSyntax`'s
`ComputationTheoryPresentation` for the halting tail, and the same honestly-disclosed boundary
(the audit accepts that boundary for the computation tail; here it is strictly stronger than the
former raw `ExactTheoryPresentation` hypothesis, because the threshold truth is now pinned by
`Θ`-provability of a decidable predicate).

Given that premise, `ExactTheoryPresentation` — and hence `WorldValued` and `ValuesAt` — is a
**theorem**, via `threshold_holds_iff`: every world consistent with the process holds `⌜X_i > r⌝`
exactly when the rational `r` is below the standard value `num i / den i`, with no nonstandard
slack (the decidable-threshold collapse of `def:luv`'s roundabout supremum).
-/

namespace LogicalInduction

open LO.FirstOrder LO.FirstOrder.Arithmetic

namespace ComputableLUV

variable (L : ComputableLUV)

/-- Recover a computable-function LUV's family index from its threshold naming (`gt 0` is the
atom `⌜X_i > 0⌝`, whose code carries `i`).  A LUV outside the `toLUV` image tags to `0`. -/
def _root_.LogicalInduction.LUV.tagIndex (X : LUV) : ℕ :=
  match X.gt 0 with
  | LO.Propositional.Formula.atom m => codeIdx m
  | _ => 0

@[simp] lemma toLUV_tagIndex (i : ℕ) : (toLUV i).tagIndex = i := by
  simp [LUV.tagIndex, toLUV_gt, thresholdSentence, codeIdx_thresholdCode]

/-! ## The DP-reveals-provable-thresholds premise -/

/-- **`ArithmeticLUVPresentation`** — the residual background-theory premise for the LUV tail,
mirroring `ComputationTheoryPresentation`.  It says the deductive process reveals the
`Θ`-provable positive threshold literals and the `Θ`-provable refutations, translating the
first-order threshold schemas into the public propositional threshold atoms.
Paper node: `def:luv` -/
structure _root_.LogicalInduction.ArithmeticLUVPresentation
    (L : ComputableLUV) (DP : DeductiveProcess) (T : ArithmeticTheory)
    [RepresentsComputations T] where
  threshold_enters : ∀ (i : ℕ) (r : ℚ),
    T ⊢ (L.thresholdSchema T)/[‘↑(thresholdCode i r)’] →
      ∃ k, thresholdSentence i r ∈ DP.D k
  threshold_refutes : ∀ (i : ℕ) (r : ℚ),
    T ⊢ ∼((L.thresholdSchema T)/[‘↑(thresholdCode i r)’]) →
      ∃ k, (∼ thresholdSentence i r) ∈ DP.D k

variable {L}

/-- **The world-value collapse.**  For a theory representing computations whose provable
thresholds the process reveals, every consistent world holds `⌜X_i > r⌝` exactly when `r` is
below the standard rational value — the decidable-threshold discharge of `def:luv`'s world
value.  Both directions run on the paper's own premise: no soundness assumption. -/
theorem threshold_holds_iff {DP : DeductiveProcess} {T : ArithmeticTheory}
    [𝗥₀ ⪯ T] [RepresentsComputations T]
    (pres : ArithmeticLUVPresentation L DP T) {v : PCWorld}
    (hv : v.ConsistentWithTheory DP) (i : ℕ) (r : ℚ) :
    v.Holds (thresholdSentence i r) ↔ (r : ℝ) < (L.value i : ℝ) := by
  constructor
  · intro hHolds
    by_contra hcon
    have hnlt : ¬ r < L.value i := fun h => hcon (by exact_mod_cast h)
    obtain ⟨k, hk⟩ := pres.threshold_refutes i r (L.threshold_refutable i r hnlt)
    have hneg : v.Holds (∼ thresholdSentence i r) := hv k _ hk
    rw [holds_not] at hneg
    exact hneg hHolds
  · intro hlt
    have hltq : r < L.value i := by exact_mod_cast hlt
    obtain ⟨k, hk⟩ := pres.threshold_enters i r (L.threshold_provable i r hltq)
    exact hv k _ hk

/-! ## Deriving `ExactTheoryPresentation` -/

/-- **`ExactTheoryPresentation` is derived, not assumed.**  For any LUV-combination
sequence all of whose LUVs are `dd:luv-arith` LUVs, the interface is constructed from the
certified threshold arithmetic and the process-reveals-provable premise, so no caller
supplies it. -/
noncomputable def exactTheoryPresentation_ofArithmetic
    {DP : DeductiveProcess} {T : ArithmeticTheory}
    [𝗥₀ ⪯ T] [RepresentsComputations T]
    (pres : ArithmeticLUVPresentation L DP T)
    (As : ℕ → LUVCombination)
    (hAs : ∀ n, ∀ p ∈ (As n).terms, ∃ i, p.2 = toLUV i) :
    LUVCombination.ExactTheoryPresentation As DP where
  value _ X := (L.value X.tagIndex : ℝ)
  value_mem := by
    intro n p hp
    obtain ⟨i, hi⟩ := hAs n p hp
    simp only [hi, toLUV_tagIndex]
    exact ⟨by exact_mod_cast L.value_nonneg i, by exact_mod_cast L.value_le_one i⟩
  threshold_iff := by
    intro n v hv p hp r
    obtain ⟨i, hi⟩ := hAs n p hp
    simp only [hi, toLUV_tagIndex, toLUV_gt]
    exact threshold_holds_iff pres hv i r

/-- `WorldValued` is likewise derived (through `ExactTheoryPresentation`). -/
lemma worldValued_ofArithmetic
    {DP : DeductiveProcess} {T : ArithmeticTheory}
    [𝗥₀ ⪯ T] [RepresentsComputations T]
    (pres : ArithmeticLUVPresentation L DP T)
    (As : ℕ → LUVCombination)
    (hAs : ∀ n, ∀ p ∈ (As n).terms, ∃ i, p.2 = toLUV i) :
    LUVCombination.WorldValued As DP :=
  (exactTheoryPresentation_ofArithmetic pres As hAs).toWorldValued

/-- Single-LUV `PCWorld.ValuesAt` is derived: a consistent world values `X_i` at its standard
rational value. -/
lemma valuesAt_ofArithmetic
    {DP : DeductiveProcess} {T : ArithmeticTheory}
    [𝗥₀ ⪯ T] [RepresentsComputations T]
    (pres : ArithmeticLUVPresentation L DP T)
    {v : PCWorld} (hv : v.ConsistentWithTheory DP) (i : ℕ) :
    v.ValuesAt (toLUV i) (L.value i : ℝ) := by
  refine ⟨by exact_mod_cast L.value_nonneg i, by exact_mod_cast L.value_le_one i, ?_⟩
  intro r
  rw [toLUV_gt]
  constructor
  · intro hr; exact (threshold_holds_iff pres hv i r).2 hr
  · intro hr hHolds
    have := (threshold_holds_iff pres hv i r).1 hHolds
    exact absurd this (not_lt.mpr (le_of_lt hr))

end ComputableLUV

end LogicalInduction
