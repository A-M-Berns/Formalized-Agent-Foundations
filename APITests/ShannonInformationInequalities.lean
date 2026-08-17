import ShannonInformation.API
import ShannonInformation.FiniteEntropy.Inequalities
import ShannonInformation.FiniteEntropy.Examples

/-! # Client-style tests for the finite-entropy inequality layer

`ShannonInformation/FiniteEntropy/Inequalities.lean` restates subadditivity, mutual-information
nonnegativity and the independence equality case over `FiniteEntropyOf` rather than
`FiniteRange`.  This file checks the two things a restatement has to earn:

* **nothing regressed** — for `Fintype`-valued variables the new statements apply with their
  instance arguments discharged by `infer_instance`, exactly as the vendored `FiniteRange`
  versions do;
* **something was gained** — the statements apply to a genuinely infinite-range pair.  The
  witness is two independent copies of the geometric law on `ℕ` from
  `ShannonInformation/FiniteEntropy/Examples.lean`, carried on the product measure; its mutual
  information is computed to be `0` and its joint entropy to be `4 * log 2`, neither of which
  is reachable through any `FiniteRange` instance.

Every declaration used from the layer is named in full (`ShannonInformation.…`): the vendored
`ProbabilityTheory` namespace has same-named `FiniteRange` versions, and a test that silently
resolved to those would test nothing. -/

open MeasureTheory ProbabilityTheory Real
open ShannonInformation (geom entropy_geom)

namespace APITests.ShannonInformationInequalities

/-! ### Regression: `Fintype`-valued variables still work with no user input -/

section Finite

variable {Ω S T U : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]
  [MeasurableSpace U] [Fintype S] [MeasurableSingletonClass S] [Fintype T]
  [MeasurableSingletonClass T] {X : Ω → S} {Y : Ω → T} {Z : Ω → U} {μ : Measure Ω}
  [IsProbabilityMeasure μ]

example (hX : Measurable X) (hY : Measurable Y) : H[⟨X, Y⟩ ; μ] ≤ H[X ; μ] + H[Y ; μ] :=
  ShannonInformation.entropy_pair_le_add hX hY

example (hX : Measurable X) (hY : Measurable Y) : 0 ≤ I[X : Y ; μ] :=
  ShannonInformation.mutualInfo_nonneg hX hY

example (hX : Measurable X) (hY : Measurable Y) : 0 ≤ I[X : Y | Z ; μ] :=
  ShannonInformation.condMutualInfo_nonneg hX hY

example (hX : Measurable X) (hY : Measurable Y) :
    I[X : Y ; μ] = 0 ↔ IndepFun X Y μ :=
  ShannonInformation.mutualInfo_eq_zero hX hY

example (hX : Measurable X) (hY : Measurable Y) : H[X | Y ; μ] ≤ H[X ; μ] :=
  ShannonInformation.condEntropy_le_entropy hX hY

variable [Fintype U] [MeasurableSingletonClass U]

example (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) :
    H[X | ⟨Y, Z⟩ ; μ] ≤ H[X | Z ; μ] :=
  ShannonInformation.entropy_submodular hX hY hZ

example (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) :
    H[⟨X, ⟨Y, Z⟩⟩ ; μ] + H[Z ; μ] ≤ H[⟨X, Z⟩ ; μ] + H[⟨Y, Z⟩ ; μ] :=
  ShannonInformation.entropy_triple_add_entropy_le hX hY hZ

example (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) :
    I[X : Y | Z ; μ] = 0 ↔ CondIndepFun X Y Z μ :=
  ShannonInformation.condMutualInfo_eq_zero hX hY hZ

end Finite

/-! ### The gain: an infinite-range independent pair

`geom` is `Geometric(1/2)` on `ℕ`; `geomPair` is a pair of independent copies of it, realised
as the product measure on `ℕ × ℕ` with the two coordinate projections as the variables. -/

/-- Two independent copies of the geometric witness. -/
noncomputable def geomPair : Measure (ℕ × ℕ) := geom.prod geom

instance : IsProbabilityMeasure geomPair := by unfold geomPair; infer_instance

lemma map_fst_geomPair : geomPair.map Prod.fst = geom := by
  rw [geomPair, Measure.map_fst_prod, measure_univ, one_smul]

lemma map_snd_geomPair : geomPair.map Prod.snd = geom := by
  rw [geomPair, Measure.map_snd_prod, measure_univ, one_smul]

instance finiteEntropyOf_fst :
    ShannonInformation.FiniteEntropyOf (Prod.fst : ℕ × ℕ → ℕ) geomPair := by
  rw [ShannonInformation.FiniteEntropyOf, map_fst_geomPair]
  infer_instance

instance finiteEntropyOf_snd :
    ShannonInformation.FiniteEntropyOf (Prod.snd : ℕ × ℕ → ℕ) geomPair := by
  rw [ShannonInformation.FiniteEntropyOf, map_snd_geomPair]
  infer_instance

/-- Neither coordinate has finite range, so no vendored `FiniteRange` theorem applies to this
pair. -/
lemma not_finiteRange_fst : ¬ FiniteRange (Prod.fst : ℕ × ℕ → ℕ) := fun h ↦ by
  have hr : Set.range (Prod.fst : ℕ × ℕ → ℕ) = Set.univ :=
    Set.range_eq_univ.2 Prod.fst_surjective
  exact Set.infinite_univ (hr ▸ h.finite)

/-- The two coordinates are independent — this is the product measure, not an assumption. -/
lemma indepFun_geomPair : IndepFun (Prod.fst : ℕ × ℕ → ℕ) Prod.snd geomPair :=
  indepFun_prod (X := (id : ℕ → ℕ)) (Y := (id : ℕ → ℕ)) measurable_id measurable_id

/-- Each marginal entropy is the witness' `2 * log 2`. -/
lemma entropy_fst_geomPair : H[(Prod.fst : ℕ × ℕ → ℕ) ; geomPair] = 2 * Real.log 2 := by
  have h : Hm[geom] = 2 * Real.log 2 := by
    rw [← Measure.map_id (μ := geom)]; exact entropy_geom
  rw [entropy_def, map_fst_geomPair]; exact h

lemma entropy_snd_geomPair : H[(Prod.snd : ℕ × ℕ → ℕ) ; geomPair] = 2 * Real.log 2 := by
  have h : Hm[geom] = 2 * Real.log 2 := by
    rw [← Measure.map_id (μ := geom)]; exact entropy_geom
  rw [entropy_def, map_snd_geomPair]; exact h

/-- **`I[X : Y] = 0` at infinite range.**  The `⟸` direction of the equality case, applied to a
pair that `FiniteRange` cannot reach. -/
lemma mutualInfo_geomPair : I[(Prod.fst : ℕ × ℕ → ℕ) : Prod.snd ; geomPair] = 0 :=
  (ShannonInformation.mutualInfo_eq_zero measurable_fst measurable_snd).mpr indepFun_geomPair

/-- **`H[X, Y] = H[X] + H[Y]` at infinite range**, and the value is computed: `4 * log 2`. -/
lemma entropy_pair_geomPair :
    H[⟨(Prod.fst : ℕ × ℕ → ℕ), Prod.snd⟩ ; geomPair] = 4 * Real.log 2 := by
  rw [(ShannonInformation.entropy_pair_eq_add measurable_fst measurable_snd).mpr
    indepFun_geomPair, entropy_fst_geomPair, entropy_snd_geomPair]
  ring

/-- The `⟹` direction has content too: the pair really is independent *because* the entropies
add, read off the same equivalence. -/
example : IndepFun (Prod.fst : ℕ × ℕ → ℕ) Prod.snd geomPair :=
  (ShannonInformation.entropy_pair_eq_add measurable_fst measurable_snd).mp
    (by rw [entropy_pair_geomPair, entropy_fst_geomPair, entropy_snd_geomPair]; ring)

/-- Subadditivity is available on the same pair, and here it is tight. -/
example : H[⟨(Prod.fst : ℕ × ℕ → ℕ), Prod.snd⟩ ; geomPair]
    ≤ H[(Prod.fst : ℕ × ℕ → ℕ) ; geomPair] + H[(Prod.snd : ℕ × ℕ → ℕ) ; geomPair] :=
  ShannonInformation.entropy_pair_le_add measurable_fst measurable_snd

/-! ### The conditional layer on the same infinite-range witness

`triv` is a constant variable, so it has finite range; the point of these is that `X` and `Y`
do not, which is exactly what stops the vendored statements from applying. -/

/-- A constant variable to condition on. -/
def triv : ℕ × ℕ → Unit := fun _ ↦ ()

example : H[(Prod.fst : ℕ × ℕ → ℕ) | (Prod.snd : ℕ × ℕ → ℕ) ; geomPair]
    ≤ H[(Prod.fst : ℕ × ℕ → ℕ) ; geomPair] :=
  ShannonInformation.condEntropy_le_entropy measurable_fst measurable_snd

example : 0 ≤ I[(Prod.fst : ℕ × ℕ → ℕ) : (Prod.snd : ℕ × ℕ → ℕ) | triv ; geomPair] :=
  ShannonInformation.condMutualInfo_nonneg measurable_fst measurable_snd

example : H[(Prod.fst : ℕ × ℕ → ℕ) | ⟨(Prod.snd : ℕ × ℕ → ℕ), triv⟩ ; geomPair]
    ≤ H[(Prod.fst : ℕ × ℕ → ℕ) | triv ; geomPair] :=
  ShannonInformation.entropy_submodular measurable_fst measurable_snd measurable_const

example :
    H[⟨(Prod.fst : ℕ × ℕ → ℕ), ⟨(Prod.snd : ℕ × ℕ → ℕ), triv⟩⟩ ; geomPair] + H[triv ; geomPair]
      ≤ H[⟨(Prod.fst : ℕ × ℕ → ℕ), triv⟩ ; geomPair]
        + H[⟨(Prod.snd : ℕ × ℕ → ℕ), triv⟩ ; geomPair] :=
  ShannonInformation.entropy_triple_add_entropy_le measurable_fst measurable_snd measurable_const

example : I[(Prod.fst : ℕ × ℕ → ℕ) : (Prod.snd : ℕ × ℕ → ℕ) | triv ; geomPair] = 0
    ↔ CondIndepFun (Prod.fst : ℕ × ℕ → ℕ) Prod.snd triv geomPair :=
  ShannonInformation.condMutualInfo_eq_zero measurable_fst measurable_snd measurable_const

/-- Conditioning keeps the witness inside the class. -/
example (z : ℕ) :
    ShannonInformation.FiniteEntropyOf (Prod.fst : ℕ × ℕ → ℕ)
      (geomPair[|(Prod.snd : ℕ × ℕ → ℕ) ⁻¹' {z}]) :=
  ShannonInformation.finiteEntropyOf_cond (Z := (Prod.snd : ℕ × ℕ → ℕ)) measurable_fst z

end APITests.ShannonInformationInequalities
