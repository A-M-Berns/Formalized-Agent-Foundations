import EconCSLib.GameTheory.StrategicGame.Dominance
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Order.Basic

/-!
# Games over a fixed action universe (§2)

The paper's *n*-player normal-form game is a tuple `(A, u)` with `A = A₁ × ⋯ × Aₙ` a
product of finite action sets and `u : A → ℝⁿ`.  A *subset game* of `(A, u)` is any
`(A', u')` with `A'ᵢ ⊆ Aᵢ` for every `i`, with `u'` unconstrained.  The paper never says
what the elements of the `Aᵢ` are (footnote 6 leaves this open on purpose); here every
game a given set of representatives can be asked to play lives over one fixed
*per-player action universe* `𝒜 : N → Type*` (`dd:universe`), and a game is a choice of
a finite nonempty subset of each `𝒜 i` together with a payoff function.

**Read this before comparing two games.**  `Game.u` is total on universe profiles, so
Lean's `=` on `Game` is **not** the paper's equality of games: two `Game`s can differ only
at profiles outside their common action sets and be the same game in the paper's sense.
The paper's own conventions force the "equal on the smaller game's profiles" reading —
Definition 2 writes `uˢᵢ = uᵢ` for functions with *different* domains — so the paper's
equality is `Game.EqOn`, defined below, and it is what every paper-facing statement uses
(`dd:total-utility`).  Never write `Γ = Γ'` for two games on the paper's behalf.

The game-theoretic vocabulary of §2 (strict dominance, and later best response, Nash
equilibrium, mixed strategies) is *not* re-defined here.  `Game.toStrategic` maps a game
to EconCSLib's `StrategicGame` — the universe with the payoff forgotten is the ambient
object, ours is a choice of finite subsets of it with its own payoff — and each notion is
EconCSLib's notion on the bridged game, characterized by a lemma that reads as the paper's
sentence (`strictlyDominates_iff`).
-/

namespace SafeParetoImprovements

open StrategicGame

universe u v

/-- An *n*-player normal-form game over the action universe `𝒜` (§2): a finite nonempty
action set `S i ⊆ 𝒜 i` for each player and a payoff function on profiles.  `u` is total
on universe profiles; only its values on `profiles` are meaningful (`dd:total-utility`,
`Game.EqOn`).  Finiteness and nonemptiness are the paper's standing assumptions (payoff
matrices; `Π(Γ) ∈ A` needs `A ≠ ∅`). -/
structure Game (N : Type u) (𝒜 : N → Type v) where
  /-- Player `i`'s action set `Aᵢ`. -/
  S : ∀ i, Finset (𝒜 i)
  /-- Every action set is nonempty. -/
  nonempty : ∀ i, (S i).Nonempty
  /-- The payoff function `u : A → ℝⁿ`, curried as `u a i`. -/
  u : (∀ i, 𝒜 i) → N → ℝ

variable {N : Type u} {𝒜 : N → Type v}

namespace Game

variable (Γ : Game N 𝒜)

/-- The outcomes (strategy profiles) `A = A₁ × ⋯ × Aₙ` of `Γ`, as a set of universe
profiles. -/
def profiles : Set (∀ i, 𝒜 i) := {a | ∀ i, a i ∈ Γ.S i}

@[simp] lemma mem_profiles {a : ∀ i, 𝒜 i} : a ∈ Γ.profiles ↔ ∀ i, a i ∈ Γ.S i := Iff.rfl

/-- `A` as a `Finset`, when the player set is finite. -/
def profilesFinset [Fintype N] [DecidableEq N] : Finset (∀ i, 𝒜 i) := Fintype.piFinset Γ.S

@[simp] lemma mem_profilesFinset [Fintype N] [DecidableEq N] {a : ∀ i, 𝒜 i} :
    a ∈ Γ.profilesFinset ↔ a ∈ Γ.profiles := by
  simp [profilesFinset, Fintype.mem_piFinset, profiles]

lemma profiles_nonempty : Γ.profiles.Nonempty :=
  ⟨fun i => (Γ.nonempty i).choose, fun i => (Γ.nonempty i).choose_spec⟩

/-- Player `i`'s payoff at the outcome `a`, `uᵢ(a)`. -/
abbrev payoff (a : ∀ i, 𝒜 i) (i : N) : ℝ := Γ.u a i

/-- The paper's **equality of games**: same action sets, and payoffs agree on the
profiles of the game (`dd:total-utility`).  This — not Lean's `=` — is what "the two
resulting games are not equal" (Definition 5) and every other comparison of games in the
paper means. -/
def EqOn (Γ Γ' : Game N 𝒜) : Prop :=
  Γ.S = Γ'.S ∧ ∀ a ∈ Γ.profiles, ∀ i, Γ.u a i = Γ'.u a i

lemma EqOn.refl (Γ : Game N 𝒜) : Γ.EqOn Γ := ⟨rfl, fun _ _ _ => rfl⟩

lemma EqOn.symm {Γ Γ' : Game N 𝒜} (h : Γ.EqOn Γ') : Γ'.EqOn Γ :=
  ⟨h.1.symm, fun a ha i => (h.2 a (by simpa [profiles, h.1] using ha) i).symm⟩

lemma EqOn.trans {Γ Γ' Γ'' : Game N 𝒜} (h : Γ.EqOn Γ') (h' : Γ'.EqOn Γ'') : Γ.EqOn Γ'' :=
  ⟨h.1.trans h'.1, fun a ha i =>
    (h.2 a ha i).trans (h'.2 a (by simpa [profiles, h.1] using ha) i)⟩

/-- `Γ'` is a **subset game** of `Γ` (§2): `A'ᵢ ⊆ Aᵢ` for every player.  The payoffs of
`Γ'` are unconstrained — "a subset game may assign different utilities to outcomes than
the original game". -/
def IsSubsetGameOf (Γ' Γ : Game N 𝒜) : Prop := ∀ i, Γ'.S i ⊆ Γ.S i

lemma IsSubsetGameOf.refl (Γ : Game N 𝒜) : Γ.IsSubsetGameOf Γ := fun _ => Finset.Subset.refl _

lemma IsSubsetGameOf.trans {Γ Γ' Γ'' : Game N 𝒜} (h : Γ.IsSubsetGameOf Γ')
    (h' : Γ'.IsSubsetGameOf Γ'') : Γ.IsSubsetGameOf Γ'' := fun i => (h i).trans (h' i)

lemma IsSubsetGameOf.profiles_subset {Γ' Γ : Game N 𝒜} (h : Γ'.IsSubsetGameOf Γ) :
    Γ'.profiles ⊆ Γ.profiles := fun _ ha i => h i (ha i)

/-- The game with action sets `T` and the *same* payoff function as `Γ`, written
`(T, u|_T)` in the paper.  This is the form Assumption 1 produces.

The constructor itself permits an arbitrary nonempty `T`: it is a **subset game** of `Γ`
only when `T i ⊆ Γ.S i` for every player, which is the hypothesis of
`restrict_isSubsetGameOf` and is not part of the definition. -/
def restrict (T : ∀ i, Finset (𝒜 i)) (hT : ∀ i, (T i).Nonempty) : Game N 𝒜 :=
  { S := T, nonempty := hT, u := Γ.u }

@[simp] lemma restrict_S (T : ∀ i, Finset (𝒜 i)) (hT) : (Γ.restrict T hT).S = T := rfl
@[simp] lemma restrict_u (T : ∀ i, Finset (𝒜 i)) (hT) : (Γ.restrict T hT).u = Γ.u := rfl

lemma restrict_isSubsetGameOf (T : ∀ i, Finset (𝒜 i)) (hT) (h : ∀ i, T i ⊆ Γ.S i) :
    (Γ.restrict T hT).IsSubsetGameOf Γ := h

/-- The game `(A₋ᵢ, Aᵢ − {ã}, u|…)` of Assumption 1: remove the single action `ã` of
player `i`.  Nonemptiness of the remaining set is a hypothesis (Assumption 1 supplies it:
`ã` is dominated *by some other strategy in `Aᵢ`*). -/
def erase [DecidableEq N] [∀ i, DecidableEq (𝒜 i)] (i : N) (ã : 𝒜 i)
    (h : ((Γ.S i).erase ã).Nonempty) : Game N 𝒜 :=
  Γ.restrict (Function.update Γ.S i ((Γ.S i).erase ã)) (by
    intro j
    by_cases hj : j = i
    · subst hj; simpa using h
    · simpa [Function.update_of_ne hj] using Γ.nonempty j)

lemma erase_isSubsetGameOf [DecidableEq N] [∀ i, DecidableEq (𝒜 i)] (i : N) (ã : 𝒜 i)
    (h : ((Γ.S i).erase ã).Nonempty) : (Γ.erase i ã h).IsSubsetGameOf Γ := by
  intro j
  by_cases hj : j = i
  · subst hj; simp [erase]; exact Finset.erase_subset _ _
  · simp [erase, Function.update_of_ne hj]

/-! ### Pareto vocabulary on payoff vectors (§2)

A payoff vector is `y : N → ℝ`, and the paper's `y ≥ y'` ("`y` is a Pareto improvement
on `y'`", *allowing* `y = y'`) is Mathlib's pointwise order on functions; "strict Pareto
improvement" (at least one inequality strict) is Mathlib's `<` on functions
(`Pi.lt_def`).  Neither is re-defined.  Only the relative optimality notion needs a
name. -/

/-- `y` is **Pareto-optimal relative to `T ⊆ ℝⁿ`** (§2): no element of `T` strictly
Pareto-dominates `y`. -/
def ParetoOptimalIn (y : N → ℝ) (T : Set (N → ℝ)) : Prop := ¬ ∃ y' ∈ T, y < y'

/-! ### The bridge to EconCSLib -/

/-- `Γ` as an EconCSLib `StrategicGame`: player `i`'s strategy type is the subtype of
`𝒜 i` cut out by `Γ.S i`, and the payoff is `Γ.u` on the underlying universe profile.
Every game-theoretic notion this formalization uses is EconCSLib's notion on this game,
characterized by a lemma in the paper's set-based vocabulary. -/
abbrev toStrategic : StrategicGame N ℝ where
  strategy i := ↥(Γ.S i)
  payoff a j := Γ.u (fun i => (a i : 𝒜 i)) j

/-- The universe profile underlying a profile of the bridged game. -/
def ofStrategicProfile (σ : Γ.toStrategic.Profile) : ∀ i, 𝒜 i := fun i => (σ i : 𝒜 i)

@[simp] lemma ofStrategicProfile_apply (σ : Γ.toStrategic.Profile) (i : N) :
    Γ.ofStrategicProfile σ i = (σ i : 𝒜 i) := rfl

lemma ofStrategicProfile_mem (σ : Γ.toStrategic.Profile) : Γ.ofStrategicProfile σ ∈ Γ.profiles :=
  fun i => (σ i).2

/-- A universe profile in `Γ.profiles`, as a profile of the bridged game. -/
def toStrategicProfile (a : ∀ i, 𝒜 i) (ha : a ∈ Γ.profiles) : Γ.toStrategic.Profile :=
  fun i => ⟨a i, ha i⟩

@[simp] lemma ofStrategicProfile_toStrategicProfile (a : ∀ i, 𝒜 i) (ha : a ∈ Γ.profiles) :
    Γ.ofStrategicProfile (Γ.toStrategicProfile a ha) = a := rfl

@[simp] lemma toStrategic_payoff (σ : Γ.toStrategic.Profile) (j : N) :
    Γ.toStrategic.payoff σ j = Γ.u (Γ.ofStrategicProfile σ) j := rfl

lemma ofStrategicProfile_deviate [DecidableEq N] (σ : Γ.toStrategic.Profile) (i : N)
    (s : Γ.toStrategic.strategy i) :
    Γ.ofStrategicProfile (deviate σ i s) = Function.update (Γ.ofStrategicProfile σ) i (s : 𝒜 i) := by
  funext j
  simp only [ofStrategicProfile]
  exact Function.apply_update (fun k (x : ↥(Γ.S k)) => (x : 𝒜 k)) σ i s j

/-! ### Strict dominance (§2) -/

/-- `a` **strictly dominates** `a'` for player `i` in `Γ` (§2): both are actions of `i`,
and `uᵢ(a, a₋ᵢ) > uᵢ(a', a₋ᵢ)` for every `a₋ᵢ`.  Defined as EconCSLib's
`StrictlyDominates` on the bridged game; `strictlyDominates_iff` is the paper's
sentence. -/
def StrictlyDominates [DecidableEq N] (i : N) (a a' : 𝒜 i) : Prop :=
  ∃ (ha : a ∈ Γ.S i) (ha' : a' ∈ Γ.S i),
    _root_.StrictlyDominates Γ.toStrategic i ⟨a, ha⟩ ⟨a', ha'⟩

/-- The paper's definition of strict dominance, read off the bridge.  Quantifying over
whole profiles `b ∈ A` and overwriting `i`'s coordinate is the same as quantifying over
`a₋ᵢ ∈ A₋ᵢ`, because every `a₋ᵢ` extends to a profile (action sets are nonempty). -/
lemma strictlyDominates_iff [DecidableEq N] (i : N) (a a' : 𝒜 i) :
    Γ.StrictlyDominates i a a' ↔
      a ∈ Γ.S i ∧ a' ∈ Γ.S i ∧
        ∀ b ∈ Γ.profiles, Γ.u (Function.update b i a') i < Γ.u (Function.update b i a) i := by
  have key : ∀ (σ : Γ.toStrategic.Profile) (s : Γ.toStrategic.strategy i),
      Γ.toStrategic.payoff (deviate σ i s) i =
        Γ.u (Function.update (Γ.ofStrategicProfile σ) i (s : 𝒜 i)) i := by
    intro σ s
    rw [← ofStrategicProfile_deviate]
    rfl
  constructor
  · rintro ⟨ha, ha', h⟩
    refine ⟨ha, ha', fun b hb => ?_⟩
    have := h (Γ.toStrategicProfile b hb)
    rwa [key, key, ofStrategicProfile_toStrategicProfile] at this
  · rintro ⟨ha, ha', h⟩
    refine ⟨ha, ha', fun σ => ?_⟩
    have := h (Γ.ofStrategicProfile σ) (Γ.ofStrategicProfile_mem σ)
    rwa [key, key]

/-- `a` is a **strictly dominated** action of player `i` in `Γ`: some other action of `i`
strictly dominates it. -/
def IsStrictlyDominated [DecidableEq N] (i : N) (a : 𝒜 i) : Prop :=
  ∃ a', Γ.StrictlyDominates i a' a

lemma IsStrictlyDominated.mem [DecidableEq N] {i : N} {a : 𝒜 i}
    (h : Γ.IsStrictlyDominated i a) : a ∈ Γ.S i := by
  obtain ⟨_, _, ha, _⟩ := h; exact ha

/-- A dominating action is a *different* action, so the erased set stays nonempty: this
is the nonemptiness Assumption 1's `Aᵢ − {ãᵢ}` needs. -/
lemma IsStrictlyDominated.erase_nonempty [DecidableEq N] [∀ i, DecidableEq (𝒜 i)]
    {i : N} {a : 𝒜 i} (h : Γ.IsStrictlyDominated i a) : ((Γ.S i).erase a).Nonempty := by
  obtain ⟨a', ha', ha, hlt⟩ := h
  refine ⟨a', Finset.mem_erase.2 ⟨?_, ha'⟩⟩
  rintro rfl
  obtain ⟨b, hb⟩ := Γ.profiles_nonempty
  exact lt_irrefl _ (hlt (Γ.toStrategicProfile b hb))

/-- `Γ` **contains no strictly dominated actions** ("fully reduced", §4.4.2). -/
def Reduced [DecidableEq N] : Prop := ∀ i (a : 𝒜 i), ¬ Γ.IsStrictlyDominated i a

/-- Strict dominance sees only the action sets and the payoffs *on outcomes*
(`strictlyDominates_iff`), so it transports along the paper's equality of games. -/
lemma strictlyDominates_of_eqOn [DecidableEq N] {Γ Γ' : Game N 𝒜} (h : Γ.EqOn Γ')
    {i : N} {a a' : 𝒜 i} (hd : Γ.StrictlyDominates i a a') :
    Γ'.StrictlyDominates i a a' := by
  have hS : ∀ j, Γ.S j = Γ'.S j := congrFun h.1
  rw [strictlyDominates_iff] at hd ⊢
  obtain ⟨ha, ha', hlt⟩ := hd
  refine ⟨by rw [← hS i]; exact ha, by rw [← hS i]; exact ha', fun b hb => ?_⟩
  have hb' : b ∈ Γ.profiles := fun j => by rw [hS j]; exact hb j
  have hmem : ∀ c ∈ Γ.S i, Function.update b i c ∈ Γ.profiles := by
    intro c hc j
    rcases eq_or_ne j i with rfl | hj
    · simpa using hc
    · rw [Function.update_of_ne hj]; exact hb' j
  rw [← h.2 _ (hmem a' ha'), ← h.2 _ (hmem a ha)]
  exact hlt b hb'

/-- Being fully reduced is a property of the paper's game, not of the presentation:
`EqOn`-equal games have the same strictly dominated actions. -/
lemma EqOn.reduced_iff [DecidableEq N] {Γ Γ' : Game N 𝒜} (h : Γ.EqOn Γ') :
    Γ.Reduced ↔ Γ'.Reduced :=
  ⟨fun hr i a ha => hr i a (ha.imp fun _ => strictlyDominates_of_eqOn h.symm),
   fun hr i a ha => hr i a (ha.imp fun _ => strictlyDominates_of_eqOn h)⟩

end Game

end SafeParetoImprovements
