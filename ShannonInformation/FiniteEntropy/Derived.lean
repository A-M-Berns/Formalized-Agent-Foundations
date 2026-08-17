/-
Copyright (c) 2026 Formalized Agent Foundations contributors.
Released under Apache 2.0 license.

This module is **FAF-authored**, mathematics included; see the header of
`ShannonInformation/FiniteEntropy/Summable.lean`.
-/
module

public import PFR.ForMathlib.Entropy.Basic
public import ShannonInformation.FiniteEntropy.ChainRule
public import ShannonInformation.FiniteEntropy.Inequalities

/-!
# The derived corpus at `FiniteEntropyOf`

Phases 2 and 3 of `Condensation/notes/finite-range-generalization-plan.md` moved the
*load-bearing* vendored theorems off `FiniteRange` — the chain rules
(`ShannonInformation/FiniteEntropy/ChainRule.lean`) and subadditivity with its equality case
(`ShannonInformation/FiniteEntropy/Inequalities.lean`).  This module is Phase 4a's mopping
up: the rest of `PFR/ForMathlib/Entropy/Basic.lean`'s `FiniteRange`-gated statements, each of
which is a rewrite chain over those two.  **There is no new mathematics here**; if a proof
below is longer than five lines it is transcribing PFR's.

## What is *not* here, and why

Several facts a reader might expect to find restated are absent because PFR's own versions
carry **no** `FiniteRange` hypothesis — they need only `Countable` and
`MeasurableSingletonClass` on the value type, which a finite-entropy variable has anyway.
They are re-used verbatim, never re-proved, and citing the `ProbabilityTheory` name is the
right thing to do:

| already general upstream | statement |
| --- | --- |
| `ProbabilityTheory.entropy_nonneg` | `0 ≤ H[X]` |
| `ProbabilityTheory.condEntropy_nonneg` | `0 ≤ H[X \| Y]` |
| `ProbabilityTheory.entropy_congr`, `.IdentDistrib.entropy_congr` | a.e.-equal / identically distributed variables |
| `ProbabilityTheory.entropy_comm`, `.condEntropy_comm`, `.mutualInfo_comm`, `.condMutualInfo_comm` | symmetry |
| `ProbabilityTheory.entropy_assoc` | `H[⟨⟨X, Y⟩, Z⟩] = H[⟨X, ⟨Y, Z⟩⟩]` |
| `ProbabilityTheory.entropy_comp_of_injective` | `H[f ∘ X] = H[X]` for injective `f` |
| `ProbabilityTheory.condEntropy_comp_of_injective` | `H[f ∘ X \| Y] = H[X \| Y]` for injective `f` |
| `ProbabilityTheory.entropy_prod_comp` | `H[⟨X, f ∘ X⟩] = H[X]` |
| `ProbabilityTheory.entropy_cond_eq_sum` | the fibrewise entropy as a `tsum` |
| `ProbabilityTheory.mutualInfo_def`, `.condMutualInfo_def`, `.condMutualInfo_eq_integral_mutualInfo` | definitional unfoldings |
| `ProbabilityTheory.IdentDistrib.mutualInfo_eq` | identically distributed pairs |

`ProbabilityTheory.entropy_le_log_card` is likewise free of `FiniteRange`, but only because
it asks for `Fintype S` instead, which is strictly stronger; there is nothing to generalize.

Also absent: `ProbabilityTheory.condEntropy_of_injective` (the per-fibre-injective
`H[f (Y, X) \| Y] = H[X \| Y]`), `.mutualInfo_const`, `.const_of_nonpos_entropy`,
`.condMutualInfo_of_inj`/`_of_inj'`/`_of_inj_map`, `.mutual_comp_comp_le`,
`.condMutual_comp_comp_le`, `.IndepFun.condEntropy_eq_entropy` and `.ent_of_cond_indep`.
Each is `FiniteRange`-gated upstream and each would generalize by the same one-screen rewrite
chain as its neighbours below; they are left out only because no consumer has asked, and
adding one is a ten-minute exercise, not a research problem.

## Main results

* data processing — `entropy_comp_le` (`H[f ∘ X] ≤ H[X]`), `entropy_of_comp_eq_of_comp`,
  `condEntropy_comp_ge` (`H[Y | f ∘ X] ≥ H[Y | X]`), `mutual_comp_le`;
* conditional entropy under maps — `condEntropy_comp_self` (`H[X | f ∘ X] = H[X] - H[f ∘ X]`),
  `condEntropy_of_injective'`;
* mutual information — `mutualInfo_eq_entropy_sub_condEntropy` and its primed twin,
  `condMutualInfo_eq'`;
* invariance — `IdentDistrib.condEntropy_eq`.

`condMutualInfo_eq` (`I[X : Y | Z] = H[X | Z] + H[Y | Z] - H[⟨X, Y⟩ | Z]`) belongs to this
corpus mathematically but lives in `ChainRule.lean`, because it is the splitting of
`condMutualInfo`'s defining Bochner integral and so rests on that module's
`integrable_entropy_cond`, which `Inequalities.lean` in turn consumes.

## Namespace hazard

Every declaration here shadows a same-named `ProbabilityTheory` declaration.  Lean resolves an
ambiguous overload by *elaboration success*, not by the enclosing namespace, so a bare name can
silently pick PFR's `FiniteRange` version even inside `namespace ShannonInformation`.  Write
the fully qualified name whenever both surfaces are open; `ShannonInformation/API.lean` carries
the "which version to cite" table.

## Measure hypothesis

Statements are at `[IsZeroOrProbabilityMeasure μ]` throughout, which is at least as general as
PFR's counterpart in every case (`IsProbabilityMeasure` is an instance of it, so a call site
that had the narrower hypothesis still elaborates).  Three of PFR's — `mutual_comp_le`,
`condEntropy_comp_self` and `IdentDistrib.condEntropy_eq` — are stated at
`IsProbabilityMeasure` upstream and are genuinely weakened here.
-/

@[expose] public section

open Function MeasureTheory ProbabilityTheory Real

namespace ShannonInformation

/-! ### Data processing -/

section DataProcessing

variable {Ω S U : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace U]
  [Countable S] [MeasurableSingletonClass S] [Countable U] [MeasurableSingletonClass U]
  {X : Ω → S}

/-- **Data-processing inequality for entropy**: `H[f ∘ X] ≤ H[X]`.

This is `ProbabilityTheory.entropy_comp_le` with `[FiniteRange X]` replaced by
`[FiniteEntropyOf X μ]`.  To upgrade to equality see `entropy_of_comp_eq_of_comp` or the
already-general `ProbabilityTheory.entropy_comp_of_injective`. -/
lemma entropy_comp_le (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ] (hX : Measurable X)
    (f : S → U) [FiniteEntropyOf X μ] :
    H[f ∘ X ; μ] ≤ H[X ; μ] := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp [entropy_zero_measure]
  have hf : Measurable f := measurable_of_countable f
  have hfX : Measurable (f ∘ X) := hf.comp hX
  haveI : FiniteEntropyOf (f ∘ X) μ := finiteEntropyOf_comp hX hf
  have h : H[X ; μ] = H[⟨X, f ∘ X⟩ ; μ] := by
    refine (ProbabilityTheory.entropy_comp_of_injective μ hX (fun x ↦ (x, f x)) ?_).symm
    intro x y hxy
    simp only [Prod.mk.injEq] at hxy
    exact hxy.1
  rw [h, chain_rule μ hX hfX]
  simp only [le_add_iff_nonneg_right]
  exact condEntropy_nonneg X (f ∘ X) μ

/-- **A Schröder–Bernstein theorem for entropy**: two variables that are functions of each
other have the same entropy.

This is `ProbabilityTheory.entropy_of_comp_eq_of_comp` at `FiniteEntropyOf`. -/
lemma entropy_of_comp_eq_of_comp {T : Type*} [MeasurableSpace T] [Countable T]
    [MeasurableSingletonClass T] {Y : Ω → T} (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) (f : S → T) (g : T → S) (h1 : Y = f ∘ X)
    (h2 : X = g ∘ Y) [FiniteEntropyOf X μ] [FiniteEntropyOf Y μ] :
    H[X ; μ] = H[Y ; μ] := by
  have h3 : H[X ; μ] ≤ H[Y ; μ] := by
    rw [h2]; exact ShannonInformation.entropy_comp_le μ hY _
  have h4 : H[Y ; μ] ≤ H[X ; μ] := by
    rw [h1]; exact ShannonInformation.entropy_comp_le μ hX _
  linarith

end DataProcessing

/-! ### Conditional entropy under a map -/

section CondEntropyComp

variable {Ω S U : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace U]
  [Countable S] [MeasurableSingletonClass S] [Countable U] [MeasurableSingletonClass U]
  {X : Ω → S}

/-- **`H[X | f ∘ X] = H[X] - H[f ∘ X]`.**  This is `ProbabilityTheory.condEntropy_comp_self`
at `FiniteEntropyOf`, and at `IsZeroOrProbabilityMeasure` rather than PFR's
`IsProbabilityMeasure`. -/
lemma condEntropy_comp_self (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ] (hX : Measurable X)
    {f : S → U} (hf : Measurable f) [FiniteEntropyOf X μ] :
    H[X | f ∘ X ; μ] = H[X ; μ] - H[f ∘ X ; μ] := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp [entropy_zero_measure, condEntropy_zero_measure]
  haveI : FiniteEntropyOf (f ∘ X) μ := finiteEntropyOf_comp hX hf
  rw [chain_rule'' μ hX (hf.comp hX), entropy_prod_comp hX _ f]

/-- **`H[X | f ∘ Y] = H[X | Y]` for injective `f`.**  This is
`ProbabilityTheory.condEntropy_of_injective'` at `FiniteEntropyOf`. -/
lemma condEntropy_of_injective' {T : Type*} [MeasurableSpace T] [Countable T]
    [MeasurableSingletonClass T] {Y : Ω → T} (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) (f : T → U) (hf : Injective f)
    (hfY : Measurable (f ∘ Y)) [FiniteEntropyOf X μ] [FiniteEntropyOf Y μ] :
    H[X | f ∘ Y ; μ] = H[X | Y ; μ] := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp [condEntropy_zero_measure]
  haveI : FiniteEntropyOf (f ∘ Y) μ := finiteEntropyOf_comp hY (measurable_of_countable f)
  rw [chain_rule'' μ hX hY, chain_rule'' μ hX hfY, chain_rule' μ hX hY, chain_rule' μ hX hfY]
  congr 1
  · congr 1
    exact condEntropy_comp_of_injective μ hY f hf
  exact entropy_comp_of_injective μ hY f hf

end CondEntropyComp

/-! ### Mutual information -/

section MutualInfo

variable {Ω S T : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]
  [Countable S] [MeasurableSingletonClass S] [Countable T] [MeasurableSingletonClass T]
  {X : Ω → S} {Y : Ω → T}

/-- **`I[X : Y] = H[X] - H[X | Y]`.**  This is
`ProbabilityTheory.mutualInfo_eq_entropy_sub_condEntropy` at `FiniteEntropyOf`. -/
lemma mutualInfo_eq_entropy_sub_condEntropy (hX : Measurable X) (hY : Measurable Y)
    (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ] [FiniteEntropyOf X μ] [FiniteEntropyOf Y μ] :
    I[X : Y ; μ] = H[X ; μ] - H[X | Y ; μ] := by
  rw [mutualInfo_def, chain_rule μ hX hY]
  abel

/-- **`I[X : Y] = H[Y] - H[Y | X]`.**  This is
`ProbabilityTheory.mutualInfo_eq_entropy_sub_condEntropy'` at `FiniteEntropyOf`. -/
lemma mutualInfo_eq_entropy_sub_condEntropy' (hX : Measurable X) (hY : Measurable Y)
    (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ] [FiniteEntropyOf X μ] [FiniteEntropyOf Y μ] :
    I[X : Y ; μ] = H[Y ; μ] - H[Y | X ; μ] := by
  rw [mutualInfo_comm hX hY,
    ShannonInformation.mutualInfo_eq_entropy_sub_condEntropy hY hX μ]

end MutualInfo

/-! ### Data processing for conditional entropy and mutual information

`condEntropy_comp_ge` is the only statement in this module whose proof is not a two-line
rewrite: it needs `entropy_submodular`, which is `Inequalities.lean`'s deepest result. -/

section CondDataProcessing

variable {Ω S T U : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]
  [MeasurableSpace U] [Countable S] [MeasurableSingletonClass S] [Countable T]
  [MeasurableSingletonClass T] [Countable U] [MeasurableSingletonClass U]
  {X : Ω → S} {Y : Ω → T}

/-- **Data-processing inequality for conditional entropy**: `H[Y | f ∘ X] ≥ H[Y | X]`.

This is `ProbabilityTheory.condEntropy_comp_ge` at `FiniteEntropyOf`.  To upgrade to equality
see `condEntropy_of_injective'`. -/
lemma condEntropy_comp_ge (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ] (hX : Measurable X)
    (hY : Measurable Y) (f : S → U) [FiniteEntropyOf X μ] [FiniteEntropyOf Y μ] :
    H[Y | f ∘ X ; μ] ≥ H[Y | X ; μ] := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp [condEntropy_zero_measure]
  have hfX : Measurable (f ∘ X) := (measurable_of_countable f).comp hX
  haveI : FiniteEntropyOf (f ∘ X) μ := finiteEntropyOf_comp hX (measurable_of_countable f)
  haveI : FiniteEntropyOf (⟨X, f ∘ X⟩ : Ω → S × U) μ := finiteEntropyOf_pair hX hfX
  have h_joint : H[⟨Y, ⟨X, f ∘ X⟩⟩ ; μ] = H[⟨Y, X⟩ ; μ] := by
    change H[(fun p : T × S ↦ (p.1, (p.2, f p.2))) ∘ ⟨Y, X⟩ ; μ] = H[⟨Y, X⟩ ; μ]
    refine entropy_comp_of_injective μ (hY.prodMk hX) _ (fun p q h ↦ ?_)
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.1 h.2.1
  rw [chain_rule'' μ hY hX, ← entropy_prod_comp hX μ f, ← h_joint,
    ← chain_rule'' μ hY (hX.prodMk hfX)]
  exact ShannonInformation.entropy_submodular hY hX hfX

/-- **Data-processing inequality for mutual information**: `I[f ∘ X : Y] ≤ I[X : Y]`.

This is `ProbabilityTheory.mutual_comp_le` at `FiniteEntropyOf`, and at
`IsZeroOrProbabilityMeasure` rather than PFR's `IsProbabilityMeasure`. -/
lemma mutual_comp_le (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ] (hX : Measurable X)
    (hY : Measurable Y) (f : S → U) [FiniteEntropyOf X μ] [FiniteEntropyOf Y μ] :
    I[f ∘ X : Y ; μ] ≤ I[X : Y ; μ] := by
  have hfX : Measurable (f ∘ X) := (measurable_of_countable f).comp hX
  haveI : FiniteEntropyOf (f ∘ X) μ := by
    rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
    · rw [FiniteEntropyOf, Measure.map_zero]; exact finiteEntropyMeasure_zero
    exact finiteEntropyOf_comp hX (measurable_of_countable f)
  rw [mutualInfo_comm hfX hY, mutualInfo_comm hX hY,
    ShannonInformation.mutualInfo_eq_entropy_sub_condEntropy hY hfX μ,
    ShannonInformation.mutualInfo_eq_entropy_sub_condEntropy hY hX μ]
  gcongr
  exact ShannonInformation.condEntropy_comp_ge μ hX hY f

end CondDataProcessing

/-! ### Conditional mutual information -/

section CondMutualInfo

variable {Ω S T U : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]
  [MeasurableSpace U] [Countable S] [MeasurableSingletonClass S] [Countable T]
  [MeasurableSingletonClass T] [Countable U] [MeasurableSingletonClass U]
  {X : Ω → S} {Y : Ω → T} {Z : Ω → U}

/-- **`I[X : Y | Z] = H[X | Z] - H[X | ⟨Y, Z⟩]`.**  This is
`ProbabilityTheory.condMutualInfo_eq'` at `FiniteEntropyOf`.  Its unprimed companion
`ShannonInformation.condMutualInfo_eq` lives in `ChainRule.lean`. -/
lemma condMutualInfo_eq' (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ] [FiniteEntropyOf X μ] [FiniteEntropyOf Y μ]
    [FiniteEntropyOf Z μ] :
    I[X : Y | Z ; μ] = H[X | Z ; μ] - H[X | ⟨Y, Z⟩ ; μ] := by
  rw [ShannonInformation.condMutualInfo_eq hX hY hZ μ, cond_chain_rule μ hX hY hZ]
  ring

end CondMutualInfo

/-! ### Invariance under identical distribution -/

section IdentDistrib

variable {Ω Ω' S T : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace S]
  [MeasurableSpace T] [Countable S] [MeasurableSingletonClass S] [Countable T]
  [MeasurableSingletonClass T]

/-- **Two pairs with the same joint law have the same conditional entropy.**

This is `ProbabilityTheory.IdentDistrib.condEntropy_eq` at `FiniteEntropyOf`.

**Dot notation does not reach this lemma.**  `h.condEntropy_eq` on
`h : ProbabilityTheory.IdentDistrib _ _ _ _` resolves in the *head symbol's* namespace,
`ProbabilityTheory`, so it always finds PFR's `FiniteRange` version.  Write
`ShannonInformation.IdentDistrib.condEntropy_eq h ...` in full. -/
lemma IdentDistrib.condEntropy_eq {X : Ω → S} {Y : Ω → T} {μ : Measure Ω} {μ' : Measure Ω'}
    {X' : Ω' → S} {Y' : Ω' → T} [IsZeroOrProbabilityMeasure μ] [IsZeroOrProbabilityMeasure μ']
    (hX : Measurable X) (hY : Measurable Y) (hX' : Measurable X') (hY' : Measurable Y')
    (h : ProbabilityTheory.IdentDistrib (⟨X, Y⟩) (⟨X', Y'⟩) μ μ') [FiniteEntropyOf X μ]
    [FiniteEntropyOf Y μ] [FiniteEntropyOf X' μ'] [FiniteEntropyOf Y' μ'] :
    H[X | Y ; μ] = H[X' | Y' ; μ'] := by
  have hYY' : ProbabilityTheory.IdentDistrib Y Y' μ μ' := h.comp measurable_snd
  rw [chain_rule'' μ hX hY, chain_rule'' μ' hX' hY', h.entropy_congr, hYY'.entropy_congr]

end IdentDistrib

end ShannonInformation
