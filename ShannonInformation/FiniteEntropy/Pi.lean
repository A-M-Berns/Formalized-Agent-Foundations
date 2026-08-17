/-
Copyright (c) 2026 Formalized Agent Foundations contributors.
Released under Apache 2.0 license.

This module is **FAF-authored**, mathematics included; see the header of
`ShannonInformation/FiniteEntropy/Summable.lean`.
-/
module

public import ShannonInformation.FiniteEntropy.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Finite entropy is closed under finite products

`ShannonInformation/FiniteEntropy/Defs.lean` closes `FiniteEntropyOf` under pairing.  This
module iterates that closure to a *finite family* `X : ∀ i : I, Ω → R i`, which is the shape
Condensation's Definition 3.1 speaks of.

## Main results

* `finiteEntropyOf_measurableEquiv` — finite entropy transports along a measurable
  equivalence of the value type (both directions, via `e.symm`).
* `finiteEntropyOf_piFin` — the `Fin n`-indexed dependent product closure, proved by
  induction on `n` with `MeasurableEquiv.piFinSuccAbove` splitting off coordinate `0`.
* `finiteEntropyOf_pi` — the same for an arbitrary `Fintype` index, transported along
  `Fintype.equivFin`.

## The index must stay finite

The bound iterated here is subadditivity, `H[⟨X, Y⟩] ≤ H[X] + H[Y]`, and `n` applications
of it cost a factor of `n`.  There is no countable analogue: see the source comment at
`finiteEntropyOf_pi` for the counterexample that rules one out.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real

namespace ShannonInformation

variable {Ω S U : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace U]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Finite entropy is a property of the value type only up to measurable equivalence.**
Relabelling the values of a finite-entropy variable by a measurable equivalence keeps it
finite-entropy.  For the converse, apply this to `e.symm`. -/
lemma finiteEntropyOf_measurableEquiv [Countable S] [MeasurableSingletonClass S]
    [MeasurableSingletonClass U] {X : Ω → S} (hX : Measurable X) (e : S ≃ᵐ U)
    [FiniteEntropyOf X μ] : FiniteEntropyOf (fun ω ↦ e (X ω)) μ :=
  finiteEntropyOf_comp hX e.measurable

/-- The induction carrying `finiteEntropyOf_piFin`.  The family `R` and its instances sit
under the `∀` so that `induction n` may vary them; `finiteEntropyOf_piFin` is the same
statement with the binders back in their usual places. -/
private lemma finiteEntropyOf_piFin_aux (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) :
    ∀ {R : Fin n → Type*} [∀ i, MeasurableSpace (R i)] [∀ i, Countable (R i)]
      [∀ i, MeasurableSingletonClass (R i)] {X : ∀ i, Ω → R i}, (∀ i, Measurable (X i)) →
      (∀ i, FiniteEntropyOf (X i) μ) → FiniteEntropyOf (fun ω i ↦ X i ω) μ := by
  induction n with
  | zero =>
    intro R _ _ _ X _ _
    haveI : Finite (∀ i : Fin 0, R i) := Finite.of_subsingleton
    infer_instance
  | succ n ih =>
    intro R _ _ _ X hX hfe
    haveI hY : FiniteEntropyOf (X 0) μ := hfe 0
    haveI hZ : FiniteEntropyOf (fun ω j ↦ X ((0 : Fin (n + 1)).succAbove j) ω) μ :=
      ih (fun j ↦ hX _) (fun j ↦ hfe _)
    have hZm : Measurable fun ω j ↦ X ((0 : Fin (n + 1)).succAbove j) ω :=
      measurable_pi_lambda _ fun j ↦ hX _
    haveI := finiteEntropyOf_pair (μ := μ) (hX 0) hZm
    have hpair : Measurable fun ω ↦ (X 0 ω, fun j ↦ X ((0 : Fin (n + 1)).succAbove j) ω) :=
      (hX 0).prodMk hZm
    have key : (fun ω i ↦ X i ω) = (MeasurableEquiv.piFinSuccAbove R 0).symm ∘
        fun ω ↦ (X 0 ω, fun j ↦ X ((0 : Fin (n + 1)).succAbove j) ω) := by
      funext ω
      simp only [Function.comp_apply, MeasurableEquiv.piFinSuccAbove_symm_apply]
      exact (Fin.insertNth_self_removeNth 0 fun i ↦ X i ω).symm
    rw [show (fun ω i ↦ X i ω) = _ from key]
    exact finiteEntropyOf_comp hpair (MeasurableEquiv.piFinSuccAbove R 0).symm.measurable

/-- **Finite product closure, `Fin n` index.**  A tuple of finitely many finite-entropy
variables has finite entropy.  The proof splits off coordinate `0` with
`MeasurableEquiv.piFinSuccAbove` and applies `finiteEntropyOf_pair`, so it is exactly `n`
applications of subadditivity. -/
lemma finiteEntropyOf_piFin {n : ℕ} {R : Fin n → Type*} [∀ i, MeasurableSpace (R i)]
    [∀ i, Countable (R i)] [∀ i, MeasurableSingletonClass (R i)] {X : ∀ i, Ω → R i}
    (hX : ∀ i, Measurable (X i)) [hfe : ∀ i, FiniteEntropyOf (X i) μ] :
    FiniteEntropyOf (fun ω i ↦ X i ω) μ :=
  finiteEntropyOf_piFin_aux μ n hX hfe

-- The `Fintype I` hypothesis below is not an artefact of the proof and must not be weakened
-- to `Countable I`.  Take `X n` independent with `H[X n] = 1` for every `n : ℕ`: each `X n`
-- is finite-entropy, yet the joint `fun ω n ↦ X n ω` has entropy `∑' n, 1 = ∞`, so it is
-- not finite-entropy.  Finite entropy is therefore genuinely *not* closed under countable
-- products, and `finiteEntropyOf_pi` must never be "generalized" to `Π i : ι` for countable
-- `ι`.  (The consumers need only the finite case: Condensation's Definition 3.1 speaks of a
-- finite family of random variables.)

/-- **Finite product closure.**  A finite family of finite-entropy random variables has a
finite-entropy joint.

`Fintype I` is essential, not incidental — see the comment above this declaration for the
countable counterexample. -/
lemma finiteEntropyOf_pi {I : Type*} [Fintype I] {R : I → Type*} [∀ i, MeasurableSpace (R i)]
    [∀ i, Countable (R i)] [∀ i, MeasurableSingletonClass (R i)] {X : ∀ i, Ω → R i}
    (hX : ∀ i, Measurable (X i)) [∀ i, FiniteEntropyOf (X i) μ] :
    FiniteEntropyOf (fun ω i ↦ X i ω) μ := by
  set e := Fintype.equivFin I with he
  set E := MeasurableEquiv.piCongrLeft R e.symm with hE
  haveI : FiniteEntropyOf (fun ω (k : Fin (Fintype.card I)) ↦ X (e.symm k) ω) μ :=
    finiteEntropyOf_piFin (fun k ↦ hX _)
  have hm : Measurable fun ω (k : Fin (Fintype.card I)) ↦ X (e.symm k) ω :=
    measurable_pi_lambda _ fun k ↦ hX _
  have key : (fun ω i ↦ X i ω) =
      E ∘ fun ω (k : Fin (Fintype.card I)) ↦ X (e.symm k) ω := by
    funext ω
    exact (E.apply_symm_apply fun i ↦ X i ω).symm
  rw [show (fun ω i ↦ X i ω) = _ from key]
  exact finiteEntropyOf_comp hm E.measurable

end ShannonInformation
