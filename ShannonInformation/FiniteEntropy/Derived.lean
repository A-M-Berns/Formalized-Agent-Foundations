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
`H[f (Y, X) \| Y] = H[X \| Y]`), `.condMutualInfo_of_inj`/`_of_inj'`/`_of_inj_map`,
`.mutual_comp_comp_le`, `.condMutual_comp_comp_le` and `.ent_of_cond_indep`.
Each is `FiniteRange`-gated upstream and each would generalize by the same one-screen rewrite
chain as its neighbours below; they are left out only because no consumer has asked, and
adding one is a ten-minute exercise, not a research problem.

## Main results

* data processing — `entropy_comp_le` (`H[f ∘ X] ≤ H[X]`), `entropy_of_comp_eq_of_comp`,
  `condEntropy_comp_ge` (`H[Y | f ∘ X] ≥ H[Y | X]`), `mutual_comp_le`;
* conditional entropy under maps — `condEntropy_comp_self` (`H[X | f ∘ X] = H[X] - H[f ∘ X]`),
  `condEntropy_of_injective'`;
* almost-sure constancy — `const_of_nonpos_entropy` (`H[X] ≤ 0` forces some value to have
  full mass);
* mutual information — `mutualInfo_eq_entropy_sub_condEntropy` and its primed twin,
  `mutualInfo_const` (`I[X : c] = 0`), `IndepFun.condEntropy_eq_entropy`
  (`H[X | Y] = H[X]` for independent `X`, `Y`), `condMutualInfo_eq'`;
* invariance — `IdentDistrib.condEntropy_eq`;
* backward closure — `finiteEntropyMeasure_of_injective` (finite entropy passes back along
  an injective measurable relabelling; the one closure statement that runs against the
  arrows of `Defs.lean`).

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

## One genuine strengthening

`const_of_nonpos_entropy` is the single statement below that asks for *more* than its vendored
twin: PFR's needs only `MeasurableSingletonClass S`, ours also needs `Countable S`.  That is
forced, not laziness.  `FiniteRange X` makes `μ.map X` atomic for free, whereas
`FiniteEntropyOf X μ` does not: on `S = ℝ` with `μ.map X` Lebesgue on `[0, 1]` every singleton
is null, so the entropy series is identically `0` — summable, with sum `0` — and yet no value
of `X` carries positive mass.  Without `Countable S` the conclusion is false.  Every consumer
already carries `Countable S`; see the class's own header for why the countability conjunct of
PFR's unused `FiniteEntropy` was dropped in favour of a `Countable` value type.
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

/-! ### Almost-sure constancy

The only statement in this module that is not a rewrite chain: PFR routes
`const_of_nonpos_entropy` through `prob_ge_exp_neg_entropy'`, whose proof is a finite-sum
argument over `FiniteRange.toFinset X`, so there is nothing to transport.  The countable
replacement is direct — a nonnegative summable family summing to `0` is identically `0`, and
`negMulLog` vanishes on `[0, 1]` only at the endpoints. -/

section Constancy

variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [Countable S]
  [MeasurableSingletonClass S] {X : Ω → S} {μ : Measure Ω}

/-- **A variable of non-positive entropy is almost surely constant**: some value carries all
the mass.

This is `ProbabilityTheory.const_of_nonpos_entropy` with `[FiniteRange X]` replaced by
`[FiniteEntropyOf X μ]` *and* `[Countable S]` added.  The extra countability is not slack:
`FiniteRange X` forces `μ.map X` to be atomic, `FiniteEntropyOf X μ` does not, and for a
non-atomic law the entropy series is identically `0` while no value has positive mass.  See
this module's header.

Since `0 ≤ H[X]` always (`ProbabilityTheory.entropy_nonneg`), the hypothesis is equivalent to
`H[X ; μ] = 0`; it is stated at `≤ 0` to match PFR and to save consumers an `le_of_eq`. -/
lemma const_of_nonpos_entropy [IsProbabilityMeasure μ] (hX : Measurable X)
    [FiniteEntropyOf X μ] (hent : H[X ; μ] ≤ 0) :
    ∃ s : S, μ.real (X ⁻¹' {s}) = 1 := by
  haveI : IsProbabilityMeasure (μ.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  have hnn : ∀ x : S, 0 ≤ negMulLog ((μ.map X).real {x}) := fun x ↦
    negMulLog_nonneg measureReal_nonneg (measureReal_singleton_le_one _ x)
  have hsum : Summable fun x : S ↦ negMulLog ((μ.map X).real {x}) :=
    FiniteEntropyOf.summable μ hX
  -- the entropy series is a nonnegative sum pinned to `0`, hence termwise `0`
  have hzero : ∑' x : S, negMulLog ((μ.map X).real {x}) = 0 := by
    have h1 : H[X ; μ] = ∑' x : S, negMulLog ((μ.map X).real {x}) := entropy_eq_sum μ
    have h2 : (0 : ℝ) ≤ ∑' x : S, negMulLog ((μ.map X).real {x}) := tsum_nonneg hnn
    linarith [h1 ▸ hent]
  have hterm : ∀ x : S, negMulLog ((μ.map X).real {x}) = 0 := fun x ↦
    le_antisymm (hzero ▸ hsum.le_tsum x fun j _ ↦ hnn j) (hnn x)
  -- countability of `S` is what produces a value of positive mass
  obtain ⟨x, hx⟩ : ∃ x : S, (μ.map X).real {x} ≠ 0 := by
    by_contra hcon
    have hcover : (⋃ x : S, ({x} : Set S)) = Set.univ :=
      Set.eq_univ_of_forall fun y ↦ Set.mem_iUnion.2 ⟨y, rfl⟩
    have huniv : (μ.map X) Set.univ = 0 := by
      rw [← hcover]
      refine measure_iUnion_null fun x ↦ ?_
      have hx0 : (μ.map X).real {x} = 0 := not_not.1 fun hx ↦ hcon ⟨x, hx⟩
      rwa [Measure.real, ENNReal.toReal_eq_zero_iff, or_iff_left (measure_ne_top _ _)] at hx0
    simp at huniv
  refine ⟨x, ?_⟩
  have hone : (μ.map X).real {x} = 1 := by
    have hx0 := hterm x
    rw [Real.negMulLog, neg_mul, neg_eq_zero, mul_eq_zero] at hx0
    rcases hx0 with h | h
    · exact absurd h hx
    · rcases Real.log_eq_zero.1 h with h | h | h
      · exact absurd h hx
      · exact h
      · linarith [(measureReal_nonneg : (0 : ℝ) ≤ (μ.map X).real {x})]
  rwa [map_measureReal_apply hX (MeasurableSet.singleton x)] at hone

end Constancy

/-! ### Finite entropy passes back along an injection

The closure lemmas of `Defs.lean` all go *forward* along a map (`finiteEntropyMeasure_map`,
`finiteEntropyOf_pair`, …).  This is the one backward direction that is true without
qualification: an injective measurable relabelling loses no entropy, so if the image law has
finite entropy then so does the source.

The consumer is the fibre product of `Condensation/Amalgamation.lean`, which embeds in a
product of two finite-entropy spaces; it is stated here rather than in `Defs.lean` only
because it arrived later. -/

section Injective

variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]

/-- **Finite entropy transfers back along an injection.**  If `f` is injective and `f ∘ id`
— that is, `f` read as a variable on `(Ω, μ)` — has finite entropy, then `μ` itself has.

This is `H[X] = H[f ∘ X]` for injective `f` in its summability form: the entropy series of
`μ` is the entropy series of `μ.map f` composed with `f`, and a subfamily of a summable
nonnegative family is summable. -/
lemma finiteEntropyMeasure_of_injective [Countable Ω] [MeasurableSingletonClass Ω]
    [MeasurableSingletonClass S] {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → S}
    (hf : Measurable f) (hinj : Function.Injective f) [FiniteEntropyOf f μ] :
    FiniteEntropyMeasure μ := by
  haveI : IsProbabilityMeasure (μ.map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
  refine FiniteEntropyMeasure.of_summable_real ?_
  have hsum : Summable fun s ↦ negMulLog ((μ.map f).real {s}) :=
    FiniteEntropyMeasure.summable_real _
  refine (hsum.comp_injective hinj).congr fun ω ↦ ?_
  have hpre : f ⁻¹' {f ω} = {ω} := by
    ext ω'
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun h ↦ hinj h, fun h ↦ by rw [h]⟩
  simp only [Function.comp_apply]
  rw [map_measureReal_apply hf (MeasurableSet.singleton (f ω)), hpre]

end Injective

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

/-- **A variable carries no information about a constant**: `I[X : fun _ ↦ c] = 0`.

This is `ProbabilityTheory.mutualInfo_const` at `FiniteEntropyOf`.  Only `X` needs the
hypothesis: the constant is `FiniteRange` outright, so `finiteEntropy_of_finiteRange`
supplies its instance and it is never asked of a caller. -/
lemma mutualInfo_const (hX : Measurable X) (c : T) {μ : Measure Ω}
    [IsZeroOrProbabilityMeasure μ] [FiniteEntropyOf X μ] :
    I[X : fun _ ↦ c ; μ] = 0 := by
  haveI : FiniteEntropyOf (fun _ : Ω ↦ c) μ := finiteEntropy_of_finiteRange μ
  exact (ShannonInformation.mutualInfo_eq_zero hX measurable_const).2 (indepFun_const c)

/-- **Conditioning on an independent variable changes nothing**: `H[X | Y] = H[X]` when
`X ⟂ Y`.  This is `ProbabilityTheory.IndepFun.condEntropy_eq_entropy` at `FiniteEntropyOf`.

**Dot notation does not reach this lemma.**  `h.condEntropy_eq_entropy` on
`h : ProbabilityTheory.IndepFun _ _ _` resolves in the head symbol's namespace,
`ProbabilityTheory`, so it always finds PFR's `FiniteRange` version.  Write
`ShannonInformation.IndepFun.condEntropy_eq_entropy h …` in full — the same hazard as
`IdentDistrib.condEntropy_eq` below. -/
lemma IndepFun.condEntropy_eq_entropy {μ : Measure Ω} (h : ProbabilityTheory.IndepFun X Y μ)
    (hX : Measurable X) (hY : Measurable Y) [IsZeroOrProbabilityMeasure μ]
    [FiniteEntropyOf X μ] [FiniteEntropyOf Y μ] :
    H[X | Y ; μ] = H[X ; μ] := by
  have h0 := (ShannonInformation.mutualInfo_eq_zero hX hY).mpr h
  rw [ShannonInformation.mutualInfo_eq_entropy_sub_condEntropy hX hY μ] at h0
  linarith

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
