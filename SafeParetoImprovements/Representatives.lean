import SafeParetoImprovements.Correspondence
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Representatives as a probability model, and the realization of "with certainty"

The paper models the representatives' play `Π(Γ)` as a random variable and reads "with
certainty" as probability one.  `Representatives N 𝒜` is that model: one probability
space on which every `Π(Γ)` is defined (`dd:representatives`), i.e. a `Play` family
together with a probability measure.  The only measurability asked for is that each
fiber `{ω | Π(Γ)(ω) = a}` is measurable — exactly what probabilities of outcomes,
supports, expectations of payoffs and conditioning on `Π(Γ) = a` (§5) need, and nothing
more.

## Realization of the certainty interface (`dd:certainty`)

§3–§4 are stated for an arbitrary certainty filter.  This file shows that the paper's
notion — "with probability one" — satisfies that interface and is recovered *exactly*:

* `ae μ` is a filter, non-degenerate for a probability measure (`ae_neBot`);
* at `L = ae μ`, "with certainty" is `∀ᵐ ω ∂μ` and "with positive probability" is
  `μ {ω | …} ≠ 0` (`frequently_ae_iff`);
* Definitions 1 and 3 at `L = ae μ` unfold to the printed statements
  (`isSPI_iff`, `isStrictSPI_iff`, `corresponds_iff`).

These are realization statements — iffs between the abstract notion and the concrete
one — not second copies of the theorems; the theorems have one declaration each, in
`Correspondence.lean`, and apply here by instantiation.
-/

namespace SafeParetoImprovements

open Filter MeasureTheory
open scoped SetRel

universe u v w

/-- The representatives, modelled probabilistically (§3, `dd:representatives`): a
probability space `(Ω, μ)`, a `Play` family on it (`play Γ ω` is `Π(Γ)` at `ω`), and
measurability of each outcome fiber.  Nothing else is assumed of the representatives;
Assumptions 1 and 2 are separate predicates (`Assumptions.lean`). -/
structure Representatives (N : Type u) (𝒜 : N → Type v) where
  /-- The sample space. -/
  Ω : Type w
  [mΩ : MeasurableSpace Ω]
  /-- The probability measure. -/
  μ : Measure Ω
  [prob : IsProbabilityMeasure μ]
  /-- The play family `Γ ↦ Π(Γ)`. -/
  toPlay : Play N 𝒜 Ω
  /-- Each fiber `{ω | Π(Γ)(ω) = a}` is measurable. -/
  measurableSet_fiber : ∀ (Γ : Game N 𝒜) (a : ∀ i, 𝒜 i), MeasurableSet {ω | toPlay.play Γ ω = a}

attribute [instance] Representatives.mΩ Representatives.prob

namespace Representatives

variable {N : Type u} {𝒜 : N → Type v} (R : Representatives.{u, v, w} N 𝒜)

/-- `Π(Γ)` at `ω`. -/
abbrev play (Γ : Game N 𝒜) (ω : R.Ω) : ∀ i, 𝒜 i := R.toPlay.play Γ ω

/-- The paper's certainty filter: "with certainty" is "with probability one". -/
abbrev certainty : Filter R.Ω := ae R.μ

/-- The paper's certainty is non-degenerate: a probability-one statement is not also
probability-zero.  This is the `[L.NeBot]` hypothesis of the strictness results. -/
instance : (R.certainty).NeBot := IsProbabilityMeasure.ae_neBot

/-- **Realization, certainty**: at the paper's instance, "`P` with certainty" is
`∀ᵐ ω ∂μ, P ω`. -/
theorem eventually_certainty_iff (P : R.Ω → Prop) :
    (∀ᶠ ω in R.certainty, P ω) ↔ ∀ᵐ ω ∂R.μ, P ω := Iff.rfl

/-- **Realization, positive probability**: at the paper's instance, "`P` with positive
probability" is `μ {ω | P ω} ≠ 0`. -/
theorem frequently_certainty_iff (P : R.Ω → Prop) :
    (∃ᶠ ω in R.certainty, P ω) ↔ R.μ {ω | P ω} ≠ 0 := frequently_ae_iff

/-- **Realization of Definition 1** at the paper's instance: `Γs` is an SPI on `Γ` iff it
is a subset game and `u(Π(Γs)) ≥ u(Π(Γ))` almost surely. -/
theorem isSPI_iff (Γ Γs : Game N 𝒜) :
    R.toPlay.IsSPI R.certainty Γ Γs ↔
      Γs.IsSubsetGameOf Γ ∧ ∀ᵐ ω ∂R.μ, Γ.u (R.play Γ ω) ≤ Γ.u (R.play Γs ω) := Iff.rfl

/-- **Realization of Definition 1 (strictness)** at the paper's instance: a strict SPI is
an SPI with some player `i` for whom `uᵢ(Π(Γs)) > uᵢ(Π(Γ))` has positive probability. -/
theorem isStrictSPI_iff (Γ Γs : Game N 𝒜) :
    R.toPlay.IsStrictSPI R.certainty Γ Γs ↔
      R.toPlay.IsSPI R.certainty Γ Γs ∧
        ∃ i, R.μ {ω | Γ.u (R.play Γ ω) i < Γ.u (R.play Γs ω) i} ≠ 0 := by
  simp only [Play.IsStrictSPI, frequently_certainty_iff]

/-- **Realization of Definition 3** at the paper's instance: `Γ ∼_Φ Γ'` iff
`Π(Γ') ∈ Φ(Π(Γ))` almost surely. -/
theorem corresponds_iff (Γ Γ' : Game N 𝒜) (Φ : SetRel (∀ i, 𝒜 i) (∀ i, 𝒜 i)) :
    R.toPlay.Corresponds R.certainty Γ Γ' Φ ↔ ∀ᵐ ω ∂R.μ, R.play Γ ω ~[Φ] R.play Γ' ω :=
  Iff.rfl

/-- The **support** of `Π(Γ)`: the outcomes played with positive probability.  Load-bearing
for Algorithm 1, Proposition 12, Lemma 13, Corollary 14 and Theorem 15 (§5). -/
def support (Γ : Game N 𝒜) : Set (∀ i, 𝒜 i) := {a | R.μ {ω | R.play Γ ω = a} ≠ 0}

lemma support_subset_profiles (Γ : Game N 𝒜) : R.support Γ ⊆ Γ.profiles := by
  intro a ha
  by_contra hna
  apply ha
  have : {ω | R.play Γ ω = a} = ∅ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro rfl
    exact hna (R.toPlay.mem Γ ω)
  simp [this]

end Representatives

end SafeParetoImprovements
