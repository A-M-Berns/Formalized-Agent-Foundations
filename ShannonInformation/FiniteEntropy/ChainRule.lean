/-
Copyright (c) 2026 Formalized Agent Foundations contributors.
Released under Apache 2.0 license.

This module is **FAF-authored**, mathematics included; see the header of
`ShannonInformation/FiniteEntropy/Summable.lean`.
-/
module

public import PFR.ForMathlib.Entropy.Basic
public import ShannonInformation.FiniteEntropy.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# The chain rule under `FiniteEntropyOf`

PFR states `H[⟨X, Y⟩] = H[Y] + H[X | Y]` under `[FiniteRange X] [FiniteRange Y]`
(`ProbabilityTheory.chain_rule` and its two primed siblings) and proves it by routing
through the *kernel* layer: `entropy_eq_kernel_entropy`, `Kernel.chain_rule`,
`Kernel.entropy_compProd`.  For the measure-level statement that detour is pure overhead —
the kernel involved is a constant kernel over `Unit`.  This module proves all five chain
rules — `chain_rule`, `chain_rule'`, `chain_rule''`, `cond_chain_rule`, `cond_chain_rule'` —
at `FiniteEntropyOf`, with no kernels anywhere: the whole content is
`ShannonInformation.tsum_negMulLog_eq_add` (the *local* chain rule of
`FiniteEntropy/Summable.lean`) applied fibrewise and summed with `Summable.tsum_prod`.

## The Bochner trap, and how it is closed

`condEntropy X Y μ` is a **Bochner integral**, `(μ.map Y)[fun y ↦ H[X | Y ← y ; μ]]`, and
Lean's Bochner integral is `0` on a non-integrable integrand.  So a `condEntropy` statement
whose integrand is not known to be integrable can be silently vacuous — the exact twin of
the `∑' = 0`-on-non-summable trap that `FiniteEntropyMeasure` exists to close.

Integrability is therefore never a hypothesis here.  `integrable_entropy_cond` **derives**
it, via the fibre identity `measureReal_mul_entropy_cond`,
which exhibits `y ↦ (μ.map Y).real {y} * H[X | Y ← y ; μ]` as a difference of two summable
families.  Every user-facing statement below takes `[FiniteEntropyOf X μ]` and
`[FiniteEntropyOf Y μ]` and manufactures the pair instance with Phase 1's
`finiteEntropyOf_pair`.

## Main results

* `condEntropy_eq_tsum` — `H[X | Y ; μ] = ∑' y, (μ.map Y).real {y} * H[X | Y ← y ; μ]`,
  the countable analogue of PFR's `condEntropy_eq_sum`.
* `chain_rule'`, `chain_rule`, `chain_rule''` — the three shapes PFR carries, with primes
  preserved so that a reader can match them one-for-one against
  `PFR/ForMathlib/Entropy/Basic.lean`.
* `cond_chain_rule'`, `cond_chain_rule` — the conditional forms.  These need no new
  analysis: three applications of `chain_rule''` plus one relabelling of a triple by
  `ProbabilityTheory.entropy_comp_of_injective`, which is hypothesis-free.
* `condMutualInfo_eq` — `I[X : Y | Z] = H[X | Z] + H[Y | Z] - H[⟨X, Y⟩ | Z]`.  Despite the
  name this is *not* a chain rule but the splitting of `condMutualInfo`'s defining Bochner
  integral into three, which is exactly the operation `integrable_entropy_cond` licenses;
  it lives here because that lemma does.  See the note on its hypotheses below.

Every *chain rule* below is stated over `[IsZeroOrProbabilityMeasure μ]`, exactly as PFR's
are (the zero measure is a one-line `simp` in each).  The integrability and summability
lemmas — `measureReal_mul_entropy_cond`, `summable_measureReal_mul_entropy_cond`,
`integrable_entropy_cond` — stay at `[IsProbabilityMeasure μ]`: the local chain rule needs a
genuine normalisation, and at the zero measure there is nothing to say.

## Naming, and the two-chain-rules fork

After this module the import surface carries *two* chain rules: PFR's
`ProbabilityTheory.chain_rule` at `FiniteRange` and `ShannonInformation.chain_rule` at
`FiniteEntropyOf`.  They are the same fact with different hypotheses, so nothing here is
ever declared in `ProbabilityTheory`, and every proof below that cites the narrow version —
none do — would have to say so explicitly.

Swapping one for the other at a call site is **not** purely a change of namespace, and it is
worth knowing which parts are not:

* an ambiguous bare name is resolved by *elaboration success*, not by the enclosing
  namespace, so a client with both surfaces open can silently get PFR's version — write the
  fully qualified name;
* the argument lists differ in where `μ` sits and whether it is explicit, because these
  statements were written to their own proofs' convenience rather than transcribed;
* `condMutualInfo_eq` below asks for `FiniteEntropyOf` on all three variables where PFR asks
  for `FiniteRange` on one.

`ShannonInformation/API.lean`'s "which version to cite" table is the canonical record.  See
also `Condensation/notes/finite-range-generalization-plan.md` §5.
-/

@[expose] public section

open Function MeasureTheory ProbabilityTheory Real
open scoped ENNReal

namespace ShannonInformation

variable {Ω S T U : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]
  [MeasurableSpace U]

/-! ### Integrability on a countable discrete space

The one general fact needed to get from a Bochner integral to a `tsum` and back.  Mathlib's
`MeasureTheory.integral_countable` converts an integral to a sum *given* integrability;
`integrable_of_summable_measureReal_mul_norm` is the converse direction, and it is what
keeps integrability a derived fact rather than a hypothesis. -/

/-- On a countable space with measurable singletons, a function is integrable as soon as
the family of its point-mass-weighted norms is summable.

This is `MeasureTheory.integrable_sum_dirac_iff` transported along
`MeasureTheory.Measure.sum_smul_dirac`. -/
lemma integrable_of_summable_measureReal_mul_norm [Countable S] [MeasurableSingletonClass S]
    {μ : Measure S} [IsFiniteMeasure μ] {f : S → ℝ}
    (h : Summable fun s ↦ μ.real {s} * ‖f s‖) : Integrable f μ := by
  rw [← μ.sum_smul_dirac]
  exact integrable_sum_dirac (x := id) (fun s ↦ measure_ne_top μ _) (by simpa [Measure.real] using h)

/-! ### The conditional law of `X` given `Y = y`

Its point masses are the joint point masses divided by the mass of the fibre.  Everything
downstream is this identity plus the local chain rule. -/

/-- The point masses of `(μ[|Y ← y]).map X` are the joint point masses of `⟨Y, X⟩`
normalised by the mass of `{Y = y}`.

When `(μ.map Y).real {y} = 0` both sides are `0`: the left because `μ[|Y ← y]` is then the
zero measure, the right because division by zero is zero. -/
lemma map_cond_measureReal_singleton [MeasurableSingletonClass S] [MeasurableSingletonClass T]
    {X : Ω → S} {Y : Ω → T} (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) (y : T)
    (x : S) :
    ((μ[|Y ← y]).map X).real {x} = (μ.map (⟨Y, X⟩ : Ω → T × S)).real {(y, x)} / (μ.map Y).real {y} := by
  have hpre : (⟨Y, X⟩ : Ω → T × S) ⁻¹' {(y, x)} = Y ⁻¹' {y} ∩ X ⁻¹' {x} := by
    ext ω; simp [Prod.ext_iff, and_comm]
  rw [map_measureReal_apply hX (measurableSet_singleton x),
    cond_real_apply (hY (measurableSet_singleton y)),
    map_measureReal_apply (hY.prodMk hX) (measurableSet_singleton (y, x)),
    map_measureReal_apply hY (measurableSet_singleton y), hpre, div_eq_inv_mul]

/-! ### The fibre identity

`b y * H[X | Y ← y] = (the `y`-row of the joint entropy series) - negMulLog (b y)`.

This is `ShannonInformation.tsum_negMulLog_eq_add` — the local chain rule — rearranged, and
it is the entire mathematical content of the module.  Summing it over `y` gives the chain
rule; reading it as a difference of two summable families gives integrability. -/

section Fibre

variable [Countable S] [MeasurableSingletonClass S] [MeasurableSingletonClass T]
  {X : Ω → S} {Y : Ω → T} {μ : Measure Ω}

omit [Countable S] in
/-- The rows of the joint point-mass family are summable. -/
private lemma summable_joint_row [Countable T]
    (μ : Measure Ω) [IsFiniteMeasure μ] (y : T) :
    Summable fun x ↦ (μ.map (⟨Y, X⟩ : Ω → T × S)).real {(y, x)} := by
  haveI : IsFiniteMeasure (μ.map (⟨Y, X⟩ : Ω → T × S)) := Measure.isFiniteMeasure_map _ _
  exact (summable_measureReal_singleton (μ.map (⟨Y, X⟩ : Ω → T × S))).prod_factor y

/-- The `y`-th row of the joint point-mass family sums to the mass of `{Y = y}`. -/
private lemma tsum_joint_row [Countable T] (hX : Measurable X) (hY : Measurable Y)
    (μ : Measure Ω) [IsFiniteMeasure μ] (y : T) :
    (∑' x, (μ.map (⟨Y, X⟩ : Ω → T × S)).real {(y, x)}) = (μ.map Y).real {y} := by
  haveI : IsFiniteMeasure (μ.map (⟨Y, X⟩ : Ω → T × S)) := Measure.isFiniteMeasure_map _ _
  have hmap : (μ.map (⟨Y, X⟩ : Ω → T × S)).map Prod.fst = μ.map Y := by
    rw [Measure.map_map measurable_fst (hY.prodMk hX)]; rfl
  rw [← measureReal_map_fst_singleton (μ.map (⟨Y, X⟩ : Ω → T × S)) y, hmap]

/-- **The fibre identity.**  The `y`-row of the joint entropy series splits into the mass
term `negMulLog ((μ.map Y).real {y})` and the mass times the conditional entropy.

This is the local chain rule `ShannonInformation.tsum_negMulLog_eq_add`, transported to the
measure layer by `map_cond_measureReal_singleton`.  The degenerate fibres — those of mass
`0`, where `μ[|Y ← y]` is the zero measure and `H[X | Y ← y ; μ] = 0` — are handled
separately, since the local chain rule needs a positive row mass. -/
lemma measureReal_mul_entropy_cond [Countable T] (hX : Measurable X) (hY : Measurable Y)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hent : Summable fun q : T × S ↦ negMulLog ((μ.map (⟨Y, X⟩ : Ω → T × S)).real {q})) (y : T) :
    (μ.map Y).real {y} * H[X | Y ← y ; μ]
      = (∑' x, negMulLog ((μ.map (⟨Y, X⟩ : Ω → T × S)).real {(y, x)}))
          - negMulLog ((μ.map Y).real {y}) := by
  have hrow : Summable fun x ↦ (μ.map (⟨Y, X⟩ : Ω → T × S)).real {(y, x)} := summable_joint_row μ y
  have hrowsum : (∑' x, (μ.map (⟨Y, X⟩ : Ω → T × S)).real {(y, x)}) = (μ.map Y).real {y} :=
    tsum_joint_row hX hY μ y
  have hr0 : ∀ x, (0 : ℝ) ≤ (μ.map (⟨Y, X⟩ : Ω → T × S)).real {(y, x)} := fun _ ↦ measureReal_nonneg
  rcases eq_or_lt_of_le (measureReal_nonneg : (0 : ℝ) ≤ (μ.map Y).real {y}) with hb0 | hbpos
  · -- degenerate fibre: every joint mass in the row vanishes
    have hzero : ∀ x, (μ.map (⟨Y, X⟩ : Ω → T × S)).real {(y, x)} = 0 := by
      intro x
      refine le_antisymm ?_ (hr0 x)
      have hle := hrow.le_tsum x fun j _ ↦ hr0 j
      rwa [hrowsum, ← hb0] at hle
    have hcond : H[X | Y ← y ; μ] = 0 :=
      ProbabilityTheory.condEntropy_eq_zero (X := X) hY μ y hb0.symm
    simp [hcond, ← hb0, hzero]
  · have hbmap : (μ.map Y).real {y} = μ.real (Y ⁻¹' {y}) :=
      map_measureReal_apply hY (measurableSet_singleton y)
    haveI : IsProbabilityMeasure (μ[|Y ← y]) :=
      cond_isProbabilityMeasure_of_real (by rw [← hbmap]; exact ne_of_gt hbpos)
    have hpos : 0 < ∑' x, (μ.map (⟨Y, X⟩ : Ω → T × S)).real {(y, x)} := by rw [hrowsum]; exact hbpos
    have hentropy : H[X | Y ← y ; μ]
        = ∑' x, negMulLog ((μ.map (⟨Y, X⟩ : Ω → T × S)).real {(y, x)} / (μ.map Y).real {y}) := by
      rw [ProbabilityTheory.entropy_eq_sum]
      exact tsum_congr fun x ↦ by rw [map_cond_measureReal_singleton hX hY μ y x]
    have hlocal : (∑' x, negMulLog ((μ.map (⟨Y, X⟩ : Ω → T × S)).real {(y, x)}))
        = negMulLog ((μ.map Y).real {y})
          + (μ.map Y).real {y}
            * ∑' x, negMulLog ((μ.map (⟨Y, X⟩ : Ω → T × S)).real {(y, x)} / (μ.map Y).real {y}) := by
      have h := tsum_negMulLog_eq_add (fun x ↦ (μ.map (⟨Y, X⟩ : Ω → T × S)).real {(y, x)}) hr0 hrow
        (hent.prod_factor y) hpos
      simpa only [hrowsum] using h
    rw [hentropy, hlocal]
    ring

end Fibre

/-! ### `condEntropy` as a `tsum`

PFR's `condEntropy_eq_sum` is a `Finset` sum over `FiniteRange.toFinset Y`.  Its countable
analogue is a `tsum`, and it costs an integrability obligation that `FiniteRange` made
free.  That obligation is discharged here, not assumed. -/

section CondEntropy

variable [Countable S] [MeasurableSingletonClass S] [Countable T] [MeasurableSingletonClass T]
  {X : Ω → S} {Y : Ω → T} {μ : Measure Ω}

/-- The weighted conditional entropies form a summable family: by the fibre identity they
are the difference of the row sums of the joint entropy series (summable by
`Summable.prod`) and the entropy series of `Y` (summable by `FiniteEntropyOf Y μ`). -/
lemma summable_measureReal_mul_entropy_cond (hX : Measurable X) (hY : Measurable Y)
    (μ : Measure Ω) [IsProbabilityMeasure μ] [FiniteEntropyOf X μ] [FiniteEntropyOf Y μ] :
    Summable fun y ↦ (μ.map Y).real {y} * H[X | Y ← y ; μ] := by
  haveI : FiniteEntropyOf (⟨Y, X⟩ : Ω → T × S) μ := finiteEntropyOf_pair hY hX
  haveI : IsProbabilityMeasure (μ.map (⟨Y, X⟩ : Ω → T × S)) :=
    Measure.isProbabilityMeasure_map (hY.prodMk hX).aemeasurable
  haveI : IsProbabilityMeasure (μ.map Y) := Measure.isProbabilityMeasure_map hY.aemeasurable
  have hent : Summable fun q : T × S ↦ negMulLog ((μ.map (⟨Y, X⟩ : Ω → T × S)).real {q}) :=
    FiniteEntropyMeasure.summable_real _
  have hY' : Summable fun y ↦ negMulLog ((μ.map Y).real {y}) :=
    FiniteEntropyMeasure.summable_real _
  refine (hent.prod.sub hY').congr fun y ↦ ?_
  exact (measureReal_mul_entropy_cond hX hY μ hent y).symm

/-- **Integrability of the conditional-entropy integrand**, derived — never assumed.

Without this, `condEntropy_eq_tsum` and everything below it could be silently vacuous:
Lean's Bochner integral is `0` on a non-integrable integrand. -/
lemma integrable_entropy_cond (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω)
    [IsProbabilityMeasure μ] [FiniteEntropyOf X μ] [FiniteEntropyOf Y μ] :
    Integrable (fun y ↦ H[X | Y ← y ; μ]) (μ.map Y) := by
  haveI : IsProbabilityMeasure (μ.map Y) := Measure.isProbabilityMeasure_map hY.aemeasurable
  refine integrable_of_summable_measureReal_mul_norm ?_
  refine (summable_measureReal_mul_entropy_cond hX hY μ).congr fun y ↦ ?_
  rw [Real.norm_of_nonneg (entropy_nonneg _ _)]

/-- **`H[X | Y] = ∑' y, P[Y = y] * H[X | Y ← y]`.**  The countable analogue of PFR's
`ProbabilityTheory.condEntropy_eq_sum`. -/
lemma condEntropy_eq_tsum (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω)
    [IsZeroOrProbabilityMeasure μ] [FiniteEntropyOf X μ] [FiniteEntropyOf Y μ] :
    H[X | Y ; μ] = ∑' y, (μ.map Y).real {y} * H[X | Y ← y ; μ] := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp
  rw [condEntropy_def, integral_countable (integrable_entropy_cond hX hY μ)]
  exact tsum_congr fun y ↦ by rw [smul_eq_mul]

end CondEntropy

/-! ### The chain rules -/

section ChainRule

variable [Countable S] [MeasurableSingletonClass S] [Countable T] [MeasurableSingletonClass T]
  {X : Ω → S} {Y : Ω → T} {μ : Measure Ω}

/-- **`H[X | Y] = H[⟨X, Y⟩] - H[Y]`.**  PFR's `chain_rule''`, at `FiniteEntropyOf`. -/
lemma chain_rule'' (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ] (hX : Measurable X)
    (hY : Measurable Y) [FiniteEntropyOf X μ] [FiniteEntropyOf Y μ] :
    H[X | Y ; μ] = H[⟨X, Y⟩ ; μ] - H[Y ; μ] := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp
  haveI : FiniteEntropyOf (⟨Y, X⟩ : Ω → T × S) μ := finiteEntropyOf_pair hY hX
  haveI : IsProbabilityMeasure (μ.map (⟨Y, X⟩ : Ω → T × S)) :=
    Measure.isProbabilityMeasure_map (hY.prodMk hX).aemeasurable
  haveI : IsProbabilityMeasure (μ.map Y) := Measure.isProbabilityMeasure_map hY.aemeasurable
  have hent : Summable fun q : T × S ↦ negMulLog ((μ.map (⟨Y, X⟩ : Ω → T × S)).real {q}) :=
    FiniteEntropyMeasure.summable_real _
  have hY' : Summable fun y ↦ negMulLog ((μ.map Y).real {y}) :=
    FiniteEntropyMeasure.summable_real _
  calc H[X | Y ; μ] = ∑' y, (μ.map Y).real {y} * H[X | Y ← y ; μ] :=
        condEntropy_eq_tsum hX hY μ
    _ = ∑' y, ((∑' x, negMulLog ((μ.map (⟨Y, X⟩ : Ω → T × S)).real {(y, x)}))
          - negMulLog ((μ.map Y).real {y})) :=
        tsum_congr fun y ↦ measureReal_mul_entropy_cond hX hY μ hent y
    _ = (∑' y, ∑' x, negMulLog ((μ.map (⟨Y, X⟩ : Ω → T × S)).real {(y, x)}))
          - ∑' y, negMulLog ((μ.map Y).real {y}) := hent.prod.tsum_sub hY'
    _ = H[⟨Y, X⟩ ; μ] - H[Y ; μ] := by
        rw [ProbabilityTheory.entropy_eq_sum, ProbabilityTheory.entropy_eq_sum, hent.tsum_prod]
    _ = H[⟨X, Y⟩ ; μ] - H[Y ; μ] := by rw [ProbabilityTheory.entropy_comm hY hX]

/-- **`H[⟨X, Y⟩] = H[Y] + H[X | Y]`.**  PFR's `chain_rule`, at `FiniteEntropyOf`. -/
lemma chain_rule (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ] (hX : Measurable X)
    (hY : Measurable Y) [FiniteEntropyOf X μ] [FiniteEntropyOf Y μ] :
    H[⟨X, Y⟩ ; μ] = H[Y ; μ] + H[X | Y ; μ] := by
  rw [chain_rule'' μ hX hY]
  ring

/-- **`H[⟨X, Y⟩] = H[X] + H[Y | X]`.**  PFR's `chain_rule'`, at `FiniteEntropyOf`. -/
lemma chain_rule' (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ] (hX : Measurable X)
    (hY : Measurable Y) [FiniteEntropyOf X μ] [FiniteEntropyOf Y μ] :
    H[⟨X, Y⟩ ; μ] = H[X ; μ] + H[Y | X ; μ] := by
  rw [ProbabilityTheory.entropy_comm hX hY, chain_rule μ hY hX]

/-- `H[X | Y] = H[⟨X, Y⟩] - H[Y]`, spelled as PFR spells the corollary. -/
lemma condEntropy_eq_entropy_pair_sub (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) [FiniteEntropyOf X μ] [FiniteEntropyOf Y μ] :
    H[X | Y ; μ] = H[⟨X, Y⟩ ; μ] - H[Y ; μ] := chain_rule'' μ hX hY

end ChainRule

/-! ### The conditional chain rules

No new analysis: `H[⟨X, Y⟩ | Z] = H[⟨⟨X, Y⟩, Z⟩] - H[Z]` and its two companions, plus the
observation that `⟨⟨X, Y⟩, Z⟩` and `⟨Y, ⟨X, Z⟩⟩` are the same triple relabelled — which
`ProbabilityTheory.entropy_comp_of_injective` settles with no finiteness hypothesis at
all. -/

section CondChainRule

variable [Countable S] [MeasurableSingletonClass S] [Countable T] [MeasurableSingletonClass T]
  [Countable U] [MeasurableSingletonClass U] {X : Ω → S} {Y : Ω → T} {Z : Ω → U} {μ : Measure Ω}

/-- Relabelling a triple does not change its entropy: `H[⟨Y, ⟨X, Z⟩⟩] = H[⟨⟨X, Y⟩, Z⟩]`. -/
private lemma entropy_triple_swap (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (μ : Measure Ω) : H[⟨Y, ⟨X, Z⟩⟩ ; μ] = H[⟨⟨X, Y⟩, Z⟩ ; μ] := by
  have hinj : Function.Injective (fun p : (S × T) × U ↦ (p.1.2, (p.1.1, p.2))) := by
    rintro ⟨⟨a, b⟩, c⟩ ⟨⟨a', b'⟩, c'⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨hb, ha, hc⟩ := h
    simp [ha, hb, hc]
  change H[(fun p : (S × T) × U ↦ (p.1.2, (p.1.1, p.2))) ∘ ⟨⟨X, Y⟩, Z⟩ ; μ] = _
  exact ProbabilityTheory.entropy_comp_of_injective μ ((hX.prodMk hY).prodMk hZ) _ hinj

/-- **`H[⟨X, Y⟩ | Z] = H[X | Z] + H[Y | ⟨X, Z⟩]`.**  PFR's `cond_chain_rule'`, at
`FiniteEntropyOf`. -/
lemma cond_chain_rule' (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ] (hX : Measurable X)
    (hY : Measurable Y) (hZ : Measurable Z) [FiniteEntropyOf X μ] [FiniteEntropyOf Y μ]
    [FiniteEntropyOf Z μ] :
    H[⟨X, Y⟩ | Z ; μ] = H[X | Z ; μ] + H[Y | ⟨X, Z⟩ ; μ] := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp
  haveI : FiniteEntropyOf (⟨X, Y⟩ : Ω → S × T) μ := finiteEntropyOf_pair hX hY
  haveI : FiniteEntropyOf (⟨X, Z⟩ : Ω → S × U) μ := finiteEntropyOf_pair hX hZ
  rw [chain_rule'' μ (hX.prodMk hY) hZ, chain_rule'' μ hX hZ,
    chain_rule'' μ hY (hX.prodMk hZ), entropy_triple_swap hX hY hZ]
  ring

/-- **`H[⟨X, Y⟩ | Z] = H[Y | Z] + H[X | ⟨Y, Z⟩]`.**  PFR's `cond_chain_rule`, at
`FiniteEntropyOf`. -/
lemma cond_chain_rule (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ] (hX : Measurable X)
    (hY : Measurable Y) (hZ : Measurable Z) [FiniteEntropyOf X μ] [FiniteEntropyOf Y μ]
    [FiniteEntropyOf Z μ] :
    H[⟨X, Y⟩ | Z ; μ] = H[Y | Z ; μ] + H[X | ⟨Y, Z⟩ ; μ] := by
  rw [ProbabilityTheory.condEntropy_comm hX hY μ, cond_chain_rule' μ hY hX hZ]

end CondChainRule

/-! ### Splitting `condMutualInfo`'s defining integral

`ProbabilityTheory.condMutualInfo X Y Z μ` is *defined* as
`(μ.map Z)[fun z ↦ H[X | Z ← z ; μ] + H[Y | Z ← z ; μ] - H[⟨X, Y⟩ | Z ← z ; μ]]`, so
`I[X : Y | Z] = H[X | Z] + H[Y | Z] - H[⟨X, Y⟩ | Z]` is nothing but `∫ (f + g - h) =
∫ f + ∫ g - ∫ h`.  That step is exactly what needs integrability of the three integrands,
which is `integrable_entropy_cond` — hence this lemma's home in this module rather than in
`Inequalities.lean`, whose conditional bounds consume it. -/

section CondMutualInfo

variable [Countable S] [MeasurableSingletonClass S] [Countable T] [MeasurableSingletonClass T]
  [Countable U] [MeasurableSingletonClass U] {X : Ω → S} {Y : Ω → T} {Z : Ω → U}

/-- **`I[X : Y | Z] = H[X | Z] + H[Y | Z] - H[⟨X, Y⟩ | Z]`.**  PFR's
`ProbabilityTheory.condMutualInfo_eq`, at `FiniteEntropyOf`.

**Hypothesis note.**  PFR's version asks only for `[FiniteRange Z]`, because its proof runs
through the kernel layer, where the three conditional entropies are read off a single
`condDistrib` and never have to be integrated separately.  This proof splits the defining
integral instead, so it needs each of the three integrands to be integrable, i.e. a
finite-entropy hypothesis on `X` and on `Y` as well.  That is a genuine (small) strengthening
relative to the vendored statement, and the only place in the layer where the `FiniteRange`
version is not a pointwise weakening of this one. -/
lemma condMutualInfo_eq (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ] [FiniteEntropyOf X μ] [FiniteEntropyOf Y μ]
    [FiniteEntropyOf Z μ] :
    I[X : Y | Z ; μ] = H[X | Z ; μ] + H[Y | Z ; μ] - H[⟨X, Y⟩ | Z ; μ] := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp [condMutualInfo_def, condEntropy_def]
  haveI : FiniteEntropyOf (⟨X, Y⟩ : Ω → S × T) μ := finiteEntropyOf_pair hX hY
  have hi1 : Integrable (fun z ↦ H[X | Z ← z ; μ]) (μ.map Z) := integrable_entropy_cond hX hZ μ
  have hi2 : Integrable (fun z ↦ H[Y | Z ← z ; μ]) (μ.map Z) := integrable_entropy_cond hY hZ μ
  have hi3 : Integrable (fun z ↦ H[⟨X, Y⟩ | Z ← z ; μ]) (μ.map Z) :=
    integrable_entropy_cond (hX.prodMk hY) hZ μ
  have hi12 : Integrable (fun z ↦ H[X | Z ← z ; μ] + H[Y | Z ← z ; μ]) (μ.map Z) := hi1.add hi2
  simp only [condMutualInfo_def, condEntropy_def]
  rw [integral_sub hi12 hi3, integral_add hi1 hi2]

end CondMutualInfo

end ShannonInformation
