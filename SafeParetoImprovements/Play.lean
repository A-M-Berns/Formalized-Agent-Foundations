import SafeParetoImprovements.Game
import Mathlib.Order.Filter.Basic

/-!
# Representatives' play and safe Pareto improvements (§3, Definitions 1–2)

The paper writes `Π(Γ)` for "the outcome that arises if the representatives play `Γ`",
models each `Π(Γ)` as a random variable, and then compares `Π(Γ)` with `Π(Γs)` *at the
same sample point* ("`u(Π(Γs)) ≥ u(Π(Γ))` with certainty").  That comparison only makes
sense if all the `Π(Γ)` are jointly distributed, so the object the paper is really
working with is a **random solver**: a sample point `ω` is one complete way the
representatives could behave, a function from games to outcomes, and `Π(Γ)` is that
behaviour evaluated at `Γ` (`dd:representatives`).  `Play N 𝒜 Ω` is that object with the
probability measure left off.

**Certainty is a parameter** (`dd:certainty`).  Every argument in §3–§4 uses only two
facts about "with certainty": a certain statement stays certain when weakened, and two
certain statements are certain together.  Those are the axioms of a `Filter`, so the
definitions and results of §3–§4 are stated for an arbitrary filter `L` on the sample
space — "with certainty" is `∀ᶠ ω in L`, "with positive probability" is `∃ᶠ ω in L` —
and the paper's own instance, "with probability one" for a probability measure `μ`, is
the almost-everywhere filter `ae μ`, realized in `Representatives.lean`.  Other instances
the paper's footnote 2 describes (dominance across a *set* of possible models, no
probabilities: the top filter on the set of solvers) come by instantiation.  Paper-node
statements at this level are therefore *strengthened* relative to the printed ones; the
docstrings say so.

The play family asks nothing of the representatives beyond returning an outcome of the
game they are handed.  Assumptions 1 and 2 (§4.4) are separate predicates; "under
Assumptions 1 and 2" is a quantifier over play families satisfying them.
-/

namespace SafeParetoImprovements

open Filter

universe u v w

variable {N : Type u} {𝒜 : N → Type v} {Ω : Type w}

/-- The representatives' play, as a random solver with the measure left off: `play Γ ω`
is the outcome `Π(Γ)` at the sample point `ω`.  The only constraint is the paper's "by
definition of `Π`, `Π(Γ') ∈ A'`": the outcome is a profile of the game played.  Membership
is required *everywhere*, not almost surely — it is the codomain of the paper's random
variable, not a property of it (`dd:representatives`). -/
structure Play (N : Type u) (𝒜 : N → Type v) (Ω : Type w) where
  /-- `Π(Γ)` at the sample point `ω`. -/
  play : Game N 𝒜 → Ω → (∀ i, 𝒜 i)
  /-- `Π(Γ) ∈ A`. -/
  mem : ∀ Γ ω, play Γ ω ∈ Γ.profiles

namespace Play

variable (X : Play N 𝒜 Ω) (L : Filter Ω)

/-- `Γs` is a **safe Pareto improvement (SPI)** on `Γ`: `Γs` is a subset game of `Γ` and
`u(Π(Γs)) ≥ u(Π(Γ))` with certainty, where `u` is the *original* game's payoff
(the subset game's own payoffs `uˢ` play no role here) and `≥` is the pointwise
(Pareto) order on payoff vectors, allowing equality.  Stated for an arbitrary certainty
filter `L`; the paper's statement is the instance `L = ae μ` (`dd:certainty`).

Paper node: `Definition 1` -/
def IsSPI (Γ Γs : Game N 𝒜) : Prop :=
  Γs.IsSubsetGameOf Γ ∧ ∀ᶠ ω in L, Γ.u (X.play Γ ω) ≤ Γ.u (X.play Γs ω)

/-- `Γs` is a **strict SPI** on `Γ`: an SPI such that for some player `i`,
`uᵢ(Π(Γs)) > uᵢ(Π(Γ))` with positive probability.  The paper prints the strictness clause
as `uᵢ(Π(Γs)) > uᵢ(Π(Γs))` (erratum D1); the second occurrence must be `Π(Γ)`.  "With
positive probability" is `∃ᶠ ω in L`, which at `L = ae μ` is `μ {…} ≠ 0`
(`Representatives.lean`).

Paper node: `Definition 1` -/
def IsStrictSPI (Γ Γs : Game N 𝒜) : Prop :=
  X.IsSPI L Γ Γs ∧ ∃ i, ∃ᶠ ω in L, Γ.u (X.play Γ ω) i < Γ.u (X.play Γs ω) i

lemma IsStrictSPI.isSPI {Γ Γs : Game N 𝒜} (h : X.IsStrictSPI L Γ Γs) : X.IsSPI L Γ Γs := h.1

/-- Every game is an SPI on itself (the paper allows `y = y'`). -/
lemma isSPI_self (Γ : Game N 𝒜) : X.IsSPI L Γ Γ :=
  ⟨Game.IsSubsetGameOf.refl Γ, Eventually.of_forall fun _ => le_rfl⟩

end Play

namespace Game

/-- A subset game `Γs = (Aˢ, uˢ)` of `Γ = (A, u)` is **unilateral** if for all but one
player `i`, `Aˢᵢ = Aᵢ` and `uˢᵢ = uᵢ`.  The payoff equality is agreement on the profiles
of `Γs` — the two functions have different domains, which is what forces
`dd:total-utility`'s reading of equality.

Paper node: `Definition 2` -/
def Unilateral (Γ Γs : Game N 𝒜) : Prop :=
  Γs.IsSubsetGameOf Γ ∧
    ∃ i, ∀ j, j ≠ i → Γs.S j = Γ.S j ∧ ∀ a ∈ Γs.profiles, Γs.u a j = Γ.u a j

end Game

namespace Play

variable (X : Play N 𝒜 Ω) (L : Filter Ω)

/-- A **unilateral SPI**: a unilateral subset game that is an SPI.

Paper node: `Definition 2` -/
def IsUnilateralSPI (Γ Γs : Game N 𝒜) : Prop :=
  Γ.Unilateral Γs ∧ X.IsSPI L Γ Γs

end Play

end SafeParetoImprovements
