/-
Copyright (c) 2026 Formalized Agent Foundations contributors.
Released under Apache 2.0 license.

This module is **FAF-authored**, mathematics included; see the header of
`ShannonInformation/FiniteEntropy/Summable.lean`.
-/
module

public import PFR.ForMathlib.Entropy.Measure
public import PFR.ForMathlib.FiniteRange.Defs
public import ShannonInformation.FiniteEntropy.Summable
public import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Finite entropy as a typeclass

`FiniteRange X` — the hypothesis the vendored PFR theorems are stated over — is a genuine
mathematical restriction: a geometric variable on `ℕ` is countable-discrete with perfectly
finite entropy and has infinite range (`ShannonInformation/SCOPE.md` §2).  This module
introduces the weaker hypothesis those theorems ought eventually to be stated over, and
proves that it is (a) implied by `FiniteRange`, so nothing currently provable stops being
provable, and (b) closed under the operations a formalization actually performs on random
variables.

## Main definitions

* `FiniteEntropyMeasure μ` — the series defining `Hm[μ]` converges.  The summand is
  `measureEntropy`'s summand **verbatim**, normalisation included, so
  `FiniteEntropyMeasure μ` says exactly "`Hm[μ]` is a real sum rather than the junk value
  `0` that `∑'` returns on a non-summable family".
* `FiniteEntropyOf X μ` — `X`'s law has finite entropy.

## Main results

* `finiteEntropy_of_finiteSupport`, `finiteEntropy_of_finiteRange` — instances, so the
  whole existing `FiniteRange` instance graph (`PFR.ForMathlib.FiniteRange.Defs`: `Finite`
  codomains, constants, `f ∘ X`, `X ∘ f`, pairs, `mul`/`div`/`inv`/`zpow`/`finprod`) feeds
  this class for free.
* `finiteEntropyMeasure_map` — the workhorse closure lemma: pushing a finite-entropy law
  forward along a measurable map keeps it finite-entropy.  Marginals of a pair and
  functions of a variable are both instances of it.
* `finiteEntropyMeasure_prod`, `finiteEntropyOf_pair` — a pair of finite-entropy variables
  has finite entropy.
* `finiteEntropyOf_pullback` — finite entropy is a property of the law, so it transports
  along any measure-preserving map.

The **finite** product closure — a whole finite family of finite-entropy variables — is
`finiteEntropyOf_pi` in `ShannonInformation/FiniteEntropy/Pi.lean`, which iterates the pair
closure below.  It is stated for a `Fintype` index and must stay that way: countable
products genuinely fail (take `X n` independent with `H[X n] = 1` for every `n`; each is
finite-entropy, the joint over all of `ℕ` is not).  See the source comment there.

## Relation to PFR's unused `FiniteEntropy`

`PFR.ForMathlib.Entropy.Measure` carries an unused `FiniteEntropy : Measure S → Prop`
(around line 100 of that file) with two differences.  It spells the summand with `.toReal`
on the `ℝ≥0∞` measure rather than with `Measure.real`; those are the same function, and
`Measure.real` is the idiom the rest of the file uses.  And it carries an extra conjunct
`∃ A : Set S, Countable A ∧ μ Aᶜ = 0`.  That conjunct is dropped here: for our consumers
the *value type* is already `Countable` — a typeclass hypothesis on essentially every
vendored entropy statement — so it is redundant and only makes the class harder to
instantiate.  A consumer needing an uncountable value type with countable support should
carry it as a separate hypothesis.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

namespace ShannonInformation

variable {Ω S T U : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]
  [MeasurableSpace U]

/-- A measure has **finite entropy** when the series defining `Hm[μ]` actually converges.

The summand tracks `ProbabilityTheory.measureEntropy`'s summand verbatim, `(μ Set.univ)⁻¹ •`
normalisation included, so no bridge is needed between this class and the entropy it is
about.  For a probability measure `FiniteEntropyMeasure.summable_real` strips the
normalisation. -/
class FiniteEntropyMeasure (μ : Measure S) : Prop where
  summable : Summable fun s ↦ negMulLog (((μ Set.univ)⁻¹ • μ).real {s})

/-- A random variable has finite entropy when its law does.  An `abbrev`, so that instance
search sees through it to `FiniteEntropyMeasure (μ.map X)`. -/
abbrev FiniteEntropyOf (X : Ω → S) (μ : Measure Ω) : Prop := FiniteEntropyMeasure (μ.map X)

/-! ### Unfolding the class for a probability measure -/

lemma FiniteEntropyMeasure.summable_real (μ : Measure S) [IsProbabilityMeasure μ]
    [h : FiniteEntropyMeasure μ] : Summable fun s ↦ negMulLog (μ.real {s}) := by
  simpa using h.summable

lemma FiniteEntropyMeasure.of_summable_real {μ : Measure S} [IsProbabilityMeasure μ]
    (h : Summable fun s ↦ negMulLog (μ.real {s})) : FiniteEntropyMeasure μ := ⟨by simpa using h⟩

/-- For a probability measure, finite entropy is exactly summability of the entropy series
of `μ`'s point masses.  (Not `Iff.rfl`: the class tracks `measureEntropy`'s normalised
summand, which for a probability measure `simp` collapses to the unnormalised one.) -/
lemma finiteEntropyMeasure_iff (μ : Measure S) [IsProbabilityMeasure μ] :
    FiniteEntropyMeasure μ ↔ Summable fun s ↦ negMulLog (μ.real {s}) :=
  ⟨fun h ↦ FiniteEntropyMeasure.summable_real (h := h) μ,
    FiniteEntropyMeasure.of_summable_real⟩

/-- The series that `ProbabilityTheory.entropy_eq_sum` writes `H[X ; μ]` as converges.

There is no `entropy_eq_tsum` in this layer because there is nothing to add: PFR's
`ProbabilityTheory.entropy_eq_sum` already states
`H[X ; μ] = ∑' x, negMulLog ((μ.map X).real {x})` for any
`[IsZeroOrProbabilityMeasure μ]`.  This lemma supplies the missing half — that under
`FiniteEntropyOf` that `∑'` is a genuine sum rather than the junk value `0` that `∑'`
returns on a non-summable family. -/
lemma FiniteEntropyOf.summable {X : Ω → S} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hX : Measurable X) [FiniteEntropyOf X μ] :
    Summable fun x ↦ negMulLog ((μ.map X).real {x}) := by
  haveI : IsProbabilityMeasure (μ.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  exact FiniteEntropyMeasure.summable_real _

/-! ### Instances: `FiniteSupport` and `FiniteRange` both give finite entropy -/

instance (priority := 100) finiteEntropy_of_finiteSupport (μ : Measure S) [FiniteSupport μ] :
    FiniteEntropyMeasure μ := by
  classical
  haveI : FiniteSupport ((μ Set.univ)⁻¹ • μ) := finiteSupport_of_mul _
  refine ⟨summable_of_ne_finset_zero (s := ((μ Set.univ)⁻¹ • μ).support) fun s hs ↦ ?_⟩
  simp only [mem_support, ne_eq, not_not] at hs
  simp [Measure.real, hs]

instance (priority := 100) finiteEntropy_of_finiteRange [MeasurableSingletonClass S]
    {X : Ω → S} (μ : Measure Ω) [FiniteRange X] : FiniteEntropyOf X μ := by
  haveI : FiniteSupport (μ.map X) := ⟨FiniteRange.toFinset X, FiniteRange.ae_mem_toFinset μ X⟩
  infer_instance

/-! ### Measure-theoretic bookkeeping

Three small facts about point masses on a countable space.  They exist so that the closure
proofs can hand a plain family `p : S → ℝ` to `ShannonInformation.FiniteEntropy.Summable`
and never touch a measure again. -/

section Bookkeeping

variable [MeasurableSingletonClass S]

/-- The point masses of a finite measure form a summable family. -/
lemma summable_measureReal_singleton (μ : Measure S) [IsFiniteMeasure μ] :
    Summable fun s ↦ μ.real {s} := by
  classical
  refine summable_of_sum_le (c := μ.real Set.univ) (fun s ↦ measureReal_nonneg) fun F ↦ ?_
  rw [sum_measureReal_singleton]
  exact measureReal_mono (Set.subset_univ _)

/-- The point masses of a probability measure sum to at most `1`.  (Equality can fail: the
measure may put mass on a non-atomic part.) -/
lemma tsum_measureReal_singleton_le_one (μ : Measure S) [IsProbabilityMeasure μ] :
    ∑' s, μ.real {s} ≤ 1 := by
  classical
  refine Real.tsum_le_of_sum_le (fun s ↦ measureReal_nonneg) fun F ↦ ?_
  rw [sum_measureReal_singleton]
  simp

omit [MeasurableSingletonClass S] in
/-- A point mass of a probability measure is at most `1`. -/
lemma measureReal_singleton_le_one (μ : Measure S) [IsProbabilityMeasure μ] (s : S) :
    μ.real {s} ≤ 1 := by
  simp

/-- A point mass of a pushforward is the sum of the point masses over its fibre. -/
lemma measureReal_map_singleton_eq_tsum_fiber [Countable S] [MeasurableSingletonClass U]
    (μ : Measure S) [IsFiniteMeasure μ] {f : S → U} (hf : Measurable f) (u : U) :
    (μ.map f).real {u} = ∑' s : (f ⁻¹' {u} : Set S), μ.real {(s : S)} := by
  rw [map_measureReal_apply hf (measurableSet_singleton u)]
  simp only [Measure.real]
  rw [← ENNReal.tsum_toReal_eq fun _ ↦ measure_ne_top _ _]
  congr 1
  simpa using
    (tsum_measure_preimage_singleton (μ := μ) (s := f ⁻¹' {u}) (f := id) (Set.to_countable _)
      fun y _ ↦ (measurableSet_singleton y).preimage measurable_id).symm

end Bookkeeping

/-- A point mass of the first marginal is the sum of the joint point masses over the fibre.
The `Prod.fst` case of `measureReal_map_singleton_eq_tsum_fiber`, restated with the fibre
identified with `T` so that product-summability lemmas apply to it. -/
lemma measureReal_map_fst_singleton [MeasurableSingletonClass S] [MeasurableSingletonClass T]
    [Countable T] (ρ : Measure (S × T)) [IsFiniteMeasure ρ] (x : S) :
    (ρ.map Prod.fst).real {x} = ∑' y, ρ.real {(x, y)} := by
  rw [map_measureReal_apply measurable_fst (measurableSet_singleton x)]
  simp only [Measure.real]
  rw [measure_preimage_fst_singleton_eq_tsum, ENNReal.tsum_toReal_eq fun _ ↦ measure_ne_top _ _]

/-- The `Prod.snd` twin of `measureReal_map_fst_singleton`. -/
lemma measureReal_map_snd_singleton [MeasurableSingletonClass S] [MeasurableSingletonClass T]
    [Countable S] (ρ : Measure (S × T)) [IsFiniteMeasure ρ] (y : T) :
    (ρ.map Prod.snd).real {y} = ∑' x, ρ.real {(x, y)} := by
  rw [map_measureReal_apply measurable_snd (measurableSet_singleton y)]
  simp only [Measure.real]
  rw [measure_preimage_snd_singleton_eq_tsum, ENNReal.tsum_toReal_eq fun _ ↦ measure_ne_top _ _]

/-! ### Closure at the level of laws -/

/-- **Pushforward closure.**  A measurable image of a finite-entropy law has finite entropy.

This is `H[f ∘ X] ≤ H[X]` in its summability form, and it is the lemma every other closure
statement below (bar the pair) is an instance of. -/
lemma finiteEntropyMeasure_map [Countable S] [MeasurableSingletonClass S]
    [MeasurableSingletonClass U] (μ : Measure S) [IsProbabilityMeasure μ]
    [FiniteEntropyMeasure μ] {f : S → U} (hf : Measurable f) :
    FiniteEntropyMeasure (μ.map f) := by
  haveI : IsProbabilityMeasure (μ.map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
  refine FiniteEntropyMeasure.of_summable_real ?_
  have h := summable_negMulLog_tsum_fiber (p := fun s ↦ μ.real {s})
    (fun s ↦ measureReal_nonneg) (summable_measureReal_singleton μ)
    (tsum_measureReal_singleton_le_one μ) (FiniteEntropyMeasure.summable_real μ) f
  simpa only [measureReal_map_singleton_eq_tsum_fiber μ hf] using h

/-- **Pair closure at the level of laws.**  If both marginals of a law on `S × T` have
finite entropy, so does the law.

The proof is the termwise bound `negMulLog_le_add_of_le` summed over `S × T`.  The same
inequality, evaluated rather than merely bounded, is subadditivity `H[⟨X, Y⟩] ≤ H[X] + H[Y]`;
that evaluation is deferred to the phase of the generalization that needs it. -/
lemma finiteEntropyMeasure_prod [Countable S] [MeasurableSingletonClass S] [Countable T]
    [MeasurableSingletonClass T] (ρ : Measure (S × T)) [IsProbabilityMeasure ρ]
    [FiniteEntropyMeasure (ρ.map Prod.fst)] [FiniteEntropyMeasure (ρ.map Prod.snd)] :
    FiniteEntropyMeasure ρ := by
  haveI hfst : IsProbabilityMeasure (ρ.map Prod.fst) :=
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  haveI hsnd : IsProbabilityMeasure (ρ.map Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  set a : S → ℝ := fun x ↦ (ρ.map Prod.fst).real {x} with ha
  set b : T → ℝ := fun y ↦ (ρ.map Prod.snd).real {y} with hb
  set r : S × T → ℝ := fun q ↦ ρ.real {q} with hr
  have hr0 : ∀ q, 0 ≤ r q := fun _ ↦ measureReal_nonneg
  have ha0 : ∀ x, 0 ≤ a x := fun _ ↦ measureReal_nonneg
  have hb0 : ∀ y, 0 ≤ b y := fun _ ↦ measureReal_nonneg
  have ha1 : ∀ x, a x ≤ 1 := fun x ↦ measureReal_singleton_le_one _ x
  have hb1 : ∀ y, b y ≤ 1 := fun y ↦ measureReal_singleton_le_one _ y
  have hra : ∀ q : S × T, r q ≤ a q.1 := by
    intro q
    rw [ha]
    simp only
    rw [map_measureReal_apply measurable_fst (measurableSet_singleton q.1)]
    exact measureReal_mono (by simp)
  have hrb : ∀ q : S × T, r q ≤ b q.2 := by
    intro q
    rw [hb]
    simp only
    rw [map_measureReal_apply measurable_snd (measurableSet_singleton q.2)]
    exact measureReal_mono (by simp)
  have hsumr : Summable r := summable_measureReal_singleton ρ
  have hsuma : Summable a := summable_measureReal_singleton _
  have hsumb : Summable b := summable_measureReal_singleton _
  have hmarga : ∀ x, ∑' y, r (x, y) = a x := fun x ↦ (measureReal_map_fst_singleton ρ x).symm
  have hmargb : ∀ y, ∑' x, r (x, y) = b y := fun y ↦ (measureReal_map_snd_singleton ρ y).symm
  have henta : Summable fun x ↦ negMulLog (a x) := FiniteEntropyMeasure.summable_real _
  have hentb : Summable fun y ↦ negMulLog (b y) := FiniteEntropyMeasure.summable_real _
  -- the three summable families dominating the joint entropy series
  have hF1 : Summable fun q : S × T ↦ -(r q * Real.log (a q.1)) := by
    refine (summable_prod_of_nonneg fun q ↦ ?_).mpr ⟨fun x ↦ ?_, ?_⟩
    · exact neg_nonneg.2 (mul_nonpos_of_nonneg_of_nonpos (hr0 q)
        (Real.log_nonpos (ha0 _) (ha1 _)))
    · exact ((hsumr.prod_factor x).mul_right (Real.log (a x))).neg
    · have : ∀ x, (∑' y, -(r (x, y) * Real.log (a x))) = negMulLog (a x) := by
        intro x
        rw [tsum_neg, (hsumr.prod_factor x).tsum_mul_right, hmarga x, negMulLog]
        ring
      simpa only [this] using henta
  have hfibb : ∀ y, Summable fun x ↦ r (x, y) := fun y ↦ by
    simpa using hsumr.prod_symm.prod_factor y
  have hF2 : Summable fun q : S × T ↦ -(r q * Real.log (b q.2)) := by
    have hswap : Summable fun q : T × S ↦ -(r (q.2, q.1) * Real.log (b q.1)) := by
      refine (summable_prod_of_nonneg fun q ↦ ?_).mpr ⟨fun y ↦ ?_, ?_⟩
      · exact neg_nonneg.2 (mul_nonpos_of_nonneg_of_nonpos (hr0 _)
          (Real.log_nonpos (hb0 _) (hb1 _)))
      · exact ((hfibb y).mul_right (Real.log (b y))).neg
      · have hval : ∀ y, (∑' x, -(r (x, y) * Real.log (b y))) = negMulLog (b y) := by
          intro y
          rw [tsum_neg, (hfibb y).tsum_mul_right, hmargb y, negMulLog]
          ring
        simpa only [hval] using hentb
    exact hswap.prod_symm
  have hF3 : Summable fun q : S × T ↦ a q.1 * b q.2 := hsuma.mul_of_nonneg hsumb ha0 hb0
  have hsum : Summable fun q : S × T ↦
      -(r q * Real.log (a q.1)) + -(r q * Real.log (b q.2)) + (a q.1 * b q.2 - r q) :=
    (hF1.add hF2).add (hF3.sub hsumr)
  refine FiniteEntropyMeasure.of_summable_real
    (Summable.of_nonneg_of_le (fun q ↦ ?_) (fun q ↦ ?_) hsum)
  · exact negMulLog_nonneg (hr0 q) ((hra q).trans (ha1 _))
  · exact negMulLog_le_add_of_le (hr0 q) (hra q) (hrb q)

/-! ### Closure at the level of random variables -/

section Closure

variable {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- Finite entropy is a property of the *law*, so it transports along any measure-preserving
map with no hypotheses on the value type at all. -/
lemma finiteEntropyOf_pullback {Λ : Type*} [MeasurableSpace Λ] {ν : Measure Λ} {pr : Λ → Ω}
    {X : Ω → S} (hpr : MeasurePreserving pr ν μ) (hX : Measurable X) [FiniteEntropyOf X μ] :
    FiniteEntropyOf (X ∘ pr) ν := by
  have h : ν.map (X ∘ pr) = μ.map X := by
    rw [← Measure.map_map hX hpr.measurable, hpr.map_eq]
  rw [FiniteEntropyOf, h]
  infer_instance

variable [Countable S] [MeasurableSingletonClass S]

/-- A function of a finite-entropy variable has finite entropy. -/
lemma finiteEntropyOf_comp [MeasurableSingletonClass U] {X : Ω → S} (hX : Measurable X)
    {f : S → U} (hf : Measurable f) [FiniteEntropyOf X μ] : FiniteEntropyOf (f ∘ X) μ := by
  haveI : IsProbabilityMeasure (μ.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  rw [FiniteEntropyOf, ← Measure.map_map hf hX]
  exact finiteEntropyMeasure_map _ hf

variable [Countable T] [MeasurableSingletonClass T]

/-- The first marginal of a finite-entropy pair has finite entropy (`H[X] ≤ H[⟨X, Y⟩]`). -/
lemma finiteEntropyOf_fst {X : Ω → S} {Y : Ω → T} (hX : Measurable X) (hY : Measurable Y)
    [FiniteEntropyOf (fun ω ↦ (X ω, Y ω)) μ] : FiniteEntropyOf X μ := by
  haveI hXY : Measurable fun ω ↦ (X ω, Y ω) := hX.prodMk hY
  haveI : IsProbabilityMeasure (μ.map fun ω ↦ (X ω, Y ω)) :=
    Measure.isProbabilityMeasure_map hXY.aemeasurable
  have h : μ.map X = (μ.map fun ω ↦ (X ω, Y ω)).map Prod.fst := by
    rw [Measure.map_map measurable_fst hXY]; rfl
  rw [FiniteEntropyOf, h]
  exact finiteEntropyMeasure_map _ measurable_fst

/-- The second marginal of a finite-entropy pair has finite entropy. -/
lemma finiteEntropyOf_snd {X : Ω → S} {Y : Ω → T} (hX : Measurable X) (hY : Measurable Y)
    [FiniteEntropyOf (fun ω ↦ (X ω, Y ω)) μ] : FiniteEntropyOf Y μ := by
  haveI hXY : Measurable fun ω ↦ (X ω, Y ω) := hX.prodMk hY
  haveI : IsProbabilityMeasure (μ.map fun ω ↦ (X ω, Y ω)) :=
    Measure.isProbabilityMeasure_map hXY.aemeasurable
  have h : μ.map Y = (μ.map fun ω ↦ (X ω, Y ω)).map Prod.snd := by
    rw [Measure.map_map measurable_snd hXY]; rfl
  rw [FiniteEntropyOf, h]
  exact finiteEntropyMeasure_map _ measurable_snd

/-- A pair of finite-entropy variables has finite entropy. -/
lemma finiteEntropyOf_pair {X : Ω → S} {Y : Ω → T} (hX : Measurable X) (hY : Measurable Y)
    [FiniteEntropyOf X μ] [FiniteEntropyOf Y μ] :
    FiniteEntropyOf (fun ω ↦ (X ω, Y ω)) μ := by
  haveI hXY : Measurable fun ω ↦ (X ω, Y ω) := hX.prodMk hY
  haveI : IsProbabilityMeasure (μ.map fun ω ↦ (X ω, Y ω)) :=
    Measure.isProbabilityMeasure_map hXY.aemeasurable
  have h1 : (μ.map fun ω ↦ (X ω, Y ω)).map Prod.fst = μ.map X := by
    rw [Measure.map_map measurable_fst hXY]; rfl
  have h2 : (μ.map fun ω ↦ (X ω, Y ω)).map Prod.snd = μ.map Y := by
    rw [Measure.map_map measurable_snd hXY]; rfl
  haveI : FiniteEntropyMeasure ((μ.map fun ω ↦ (X ω, Y ω)).map Prod.fst) := h1 ▸ ‹_›
  haveI : FiniteEntropyMeasure ((μ.map fun ω ↦ (X ω, Y ω)).map Prod.snd) := h2 ▸ ‹_›
  exact finiteEntropyMeasure_prod _

end Closure

end ShannonInformation
