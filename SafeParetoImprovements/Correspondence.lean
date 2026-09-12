import SafeParetoImprovements.Play
import Mathlib.Data.Rel

/-!
# Outcome correspondence (§4.1–§4.3)

## Multivalued functions (§4.1)

A multivalued function `Φ : M ⊸ N` sends each `m` to a set `Φ(m) ⊆ N`; it is the same
data as a relation, and Mathlib's `SetRel M N` (a set of pairs, `m ~[Φ] n` for
`(m, n) ∈ Φ`) is used directly rather than re-defined.  The dictionary:

| paper                         | here                                            |
|-------------------------------|-------------------------------------------------|
| `n ∈ Φ(m)`                    | `m ~[Φ] n`                                      |
| `Φ(m)` as a set               | `Φ.image {m}`                                   |
| `Φ(Q)` for `Q ⊆ M`            | `Φ.image Q`                                     |
| `id_M` (the paper's `id_A`)   | `Game.partialId` (partial identity on `A`)      |
| `all_{M,N} : m ↦ N`           | `Set.univ` (or `M ×ˢ N` on the typed sets)      |
| `Φ⁻¹`                         | `Φ.inv`                                         |
| `Ψ ∘ Φ` (first `Φ`, then `Ψ`) | `Φ ○ Ψ` — **Mathlib composes diagrammatically** |
| single-valued                 | `∀ a ∈ Γ.profiles, ∃! b, a ~[Φ] b`              |

The reversal of composition order is the one thing to keep in mind when reading Lemma 2.3
against the paper.  A second thing: the paper's `id_A : A ⊸ A` is the identity on the
*outcomes of the game*, not on the ambient universe of profiles.  That is
`Game.partialId`, which relates `a` to `a` exactly for `a ∈ A`; Mathlib's `SetRel.id` is
the universe identity and is a strictly larger relation (`dd:universe`), so Lemma 2.1 is
stated with `Game.partialId`.

## Outcome correspondence (§4.2–§4.3)

`Γ ∼_Φ Γ'` (Definition 3) is a statement about the representatives: with certainty,
`Π(Γ') ∈ Φ(Π(Γ))`.  It is stated for a `Play` family and an arbitrary certainty filter
(`dd:certainty`); Lemma 2 and Theorem 3 are proved at that generality, which is exactly
the generality their printed proofs already have.
-/

namespace SafeParetoImprovements

open Filter SetRel

universe u v w

variable {N : Type u} {𝒜 : N → Type v} {Ω : Type w}

/-- The paper's `all_{A,A'} : a ↦ A'`, typed on the profiles of two games: every outcome
of `Γ` is sent to every outcome of `Γ'`. -/
def Game.allRel (Γ Γ' : Game N 𝒜) : SetRel (∀ i, 𝒜 i) (∀ i, 𝒜 i) :=
  Γ.profiles ×ˢ Γ'.profiles

/-- The **partial identity** on the outcomes of `G`, the paper's `id_A : A ⊸ A`: `a ~ b`
iff `a ∈ A_G` and `b = a`.  This is the correspondence of Lemma 2.1, and it is also the
composite of Assumption 1's correspondences along an elimination chain ending at `G`, in
either direction. -/
def Game.partialId (G : Game N 𝒜) : SetRel (∀ i, 𝒜 i) (∀ i, 𝒜 i) :=
  {p | p.1 ∈ G.profiles ∧ p.2 = p.1}

@[simp] lemma Game.mem_partialId (G : Game N 𝒜) (a b : ∀ i, 𝒜 i) :
    a ~[G.partialId] b ↔ a ∈ G.profiles ∧ b = a := Iff.rfl

namespace Play

variable (X : Play N 𝒜 Ω) (L : Filter Ω)

/-- **Outcome correspondence** `Γ ∼_Φ Γ'`: with certainty, `Π(Γ') ∈ Φ(Π(Γ))`.  A statement
about the representatives, not about the games.  Stated for an arbitrary certainty filter
`L` (`dd:certainty`); the paper's statement is the instance `L = ae μ`.

Paper node: `Definition 3` -/
def Corresponds (Γ Γ' : Game N 𝒜) (Φ : SetRel (∀ i, 𝒜 i) (∀ i, 𝒜 i)) : Prop :=
  ∀ᶠ ω in L, X.play Γ ω ~[Φ] X.play Γ' ω

/-! ### Lemma 2 — the basic facts about `∼`

All seven items hold for every filter; the printed proofs use nothing else.  Items 1 and
5 are the ones that use the play family's membership constraint `Π(Γ) ∈ A`: item 1
because the paper's `id_A` is the *partial* identity on the outcomes of `Γ`
(`Game.partialId`), so reflexivity says exactly `∀ᶠ ω in L, X.play Γ ω ∈ Γ.profiles`; item
5 because `all_{A,A'}` is typed on both games' outcomes. -/

variable {X L}

/-- Lemma 2.1, **reflexivity**: `Γ ∼_{id_A} Γ`, where `id_A` is the identity on the
outcomes of `Γ` (`Game.partialId`), not the identity on the ambient profile universe.

Paper node: `Lemma 2` -/
theorem corresponds_id (X : Play N 𝒜 Ω) (L : Filter Ω) (Γ : Game N 𝒜) :
    X.Corresponds L Γ Γ Γ.partialId :=
  Eventually.of_forall fun ω => ⟨X.mem Γ ω, rfl⟩

/-- Lemma 2.2, **symmetry**: if `Γ ∼_Φ Γ'` then `Γ' ∼_{Φ⁻¹} Γ`.

Paper node: `Lemma 2` -/
theorem Corresponds.inv {Γ Γ' : Game N 𝒜} {Φ : SetRel (∀ i, 𝒜 i) (∀ i, 𝒜 i)}
    (h : X.Corresponds L Γ Γ' Φ) : X.Corresponds L Γ' Γ Φ.inv :=
  h.mono fun _ hω => hω

/-- Lemma 2.3, **transitivity**: if `Γ ∼_Φ Γ'` and `Γ' ∼_Ψ Γ''` then `Γ ∼_{Ψ ∘ Φ} Γ''`.
The paper's `Ψ ∘ Φ` is Mathlib's `Φ ○ Ψ`.

Paper node: `Lemma 2` -/
theorem Corresponds.trans {Γ Γ' Γ'' : Game N 𝒜} {Φ Ψ : SetRel (∀ i, 𝒜 i) (∀ i, 𝒜 i)}
    (h : X.Corresponds L Γ Γ' Φ) (h' : X.Corresponds L Γ' Γ'' Ψ) :
    X.Corresponds L Γ Γ'' (Φ ○ Ψ) :=
  (h.and h').mono fun _ ⟨hω, hω'⟩ => ⟨_, hω, hω'⟩

/-- Lemma 2.4, **weakening**: if `Γ ∼_Φ Γ'` and `Φ(a) ⊆ Ξ(a)` for every *outcome* `a` of
`Γ`, then `Γ ∼_Ξ Γ'`.  The containment is required only at the outcomes of `Γ`, which is
what the paper prints ("for all `a ∈ A`") and all its proof uses; `mono_rel'` is the
global-containment corollary.

Paper node: `Lemma 2` -/
theorem Corresponds.mono_rel {Γ Γ' : Game N 𝒜} {Φ Ξ : SetRel (∀ i, 𝒜 i) (∀ i, 𝒜 i)}
    (h : X.Corresponds L Γ Γ' Φ)
    (hΦΞ : ∀ a ∈ Γ.profiles, ∀ b, a ~[Φ] b → a ~[Ξ] b) : X.Corresponds L Γ Γ' Ξ :=
  h.mono fun ω hω => hΦΞ _ (X.mem Γ ω) _ hω

/-- Lemma 2.4 with containment of `Φ` in `Ξ` everywhere, not only at the outcomes of
`Γ`; the form that is usually convenient in Lean. -/
lemma Corresponds.mono_rel' {Γ Γ' : Game N 𝒜} {Φ Ξ : SetRel (∀ i, 𝒜 i) (∀ i, 𝒜 i)}
    (h : X.Corresponds L Γ Γ' Φ) (hΦΞ : Φ ⊆ Ξ) : X.Corresponds L Γ Γ' Ξ :=
  h.mono_rel fun _ _ _ hω => hΦΞ hω

/-- Lemma 2.5, the **trivial correspondence**: `Γ ∼_{all_{A,A'}} Γ'` always.  This is the
one item that uses `Π(Γ') ∈ A'` (item 1 uses the membership constraint too, but only for
`Γ`; see the section note).

Paper node: `Lemma 2` -/
theorem corresponds_allRel (X : Play N 𝒜 Ω) (L : Filter Ω) (Γ Γ' : Game N 𝒜) :
    X.Corresponds L Γ Γ' (Γ.allRel Γ') :=
  Eventually.of_forall fun ω => ⟨X.mem Γ ω, X.mem Γ' ω⟩

/-- Lemma 2.6, **elimination**: if `Γ ∼_Φ Γ'` and `Φ(a) = ∅`, then `Π(Γ) ≠ a` with
certainty.

Paper node: `Lemma 2` -/
theorem Corresponds.ne_of_at_eq_empty {Γ Γ' : Game N 𝒜} {Φ : SetRel (∀ i, 𝒜 i) (∀ i, 𝒜 i)}
    (h : X.Corresponds L Γ Γ' Φ) {a : ∀ i, 𝒜 i} (ha : Φ.image {a} = ∅) :
    ∀ᶠ ω in L, X.play Γ ω ≠ a :=
  h.mono fun ω hω heq => by
    have : X.play Γ' ω ∈ Φ.image {a} := ⟨a, rfl, heq ▸ hω⟩
    simp [ha] at this

/-- Lemma 2.7, **elimination in the target**: if `Γ ∼_Φ Γ'` and `Φ⁻¹(a') = ∅`, then
`Π(Γ') ≠ a'` with certainty.  (The printed proof cites "reflexivity (Lemma 2.1)" where it
uses symmetry, Lemma 2.2 — erratum D4.)

Paper node: `Lemma 2` -/
theorem Corresponds.ne_of_inv_at_eq_empty {Γ Γ' : Game N 𝒜}
    {Φ : SetRel (∀ i, 𝒜 i) (∀ i, 𝒜 i)} (h : X.Corresponds L Γ Γ' Φ) {a' : ∀ i, 𝒜 i}
    (ha' : Φ.inv.image {a'} = ∅) : ∀ᶠ ω in L, X.play Γ' ω ≠ a' :=
  h.inv.ne_of_at_eq_empty ha'

/-! ### Pareto-improving correspondence and Theorem 3 (§4.3) -/

variable (X L)

/-- `Φ` is a **Pareto-improving outcome correspondence** from `Γ` to its subset game
`Γs`: `Γ ∼_Φ Γs`, and `u(aˢ) ≥ u(a)` (the *original* payoff `u`, pointwise) for every
outcome `a` of `Γ` and every `aˢ ∈ Φ(a)`.  The paper's typing `Φ : A ⊸ Aˢ` is a
requirement on the supplied `Φ`, not merely a restriction of the payoff obligation, and
is carried by the field `typed`: `Φ` relates only outcomes of `Γ` to outcomes of `Γs`.
(The printed definition writes `Γ ∼_Φ Γ'` for `Γ ∼_Φ Γˢ` and types `Φ` with an ordinary
arrow — erratum D2.)

`typed` is the *last* field so that the other two keep their order and meaning; an
anonymous constructor must supply all three.

Paper node: `Definition 4` -/
structure ParetoImprovingCorrespondence (Γ Γs : Game N 𝒜)
    (Φ : SetRel (∀ i, 𝒜 i) (∀ i, 𝒜 i)) : Prop where
  corresponds : X.Corresponds L Γ Γs Φ
  improving : ∀ a ∈ Γ.profiles, ∀ b ∈ Γs.profiles, a ~[Φ] b → Γ.u a ≤ Γ.u b
  typed : Φ ⊆ Γ.profiles ×ˢ Γs.profiles

/-- **Theorem 3**: a subset game `Γs` of `Γ` is an SPI on `Γ` if and only if there is a
Pareto-improving outcome correspondence from `Γ` to `Γs`.  The correspondence in the
forward direction is the paper's `a ↦ {aˢ ∈ Aˢ | u(aˢ) ≥ u(a)}`.  Holds for every
certainty filter (`dd:certainty`).

Paper node: `Theorem 3` -/
theorem isSPI_iff_exists_paretoImprovingCorrespondence {Γ Γs : Game N 𝒜}
    (hsub : Γs.IsSubsetGameOf Γ) :
    X.IsSPI L Γ Γs ↔
      ∃ Φ : SetRel (∀ i, 𝒜 i) (∀ i, 𝒜 i), X.ParetoImprovingCorrespondence L Γ Γs Φ := by
  constructor
  · rintro ⟨-, h⟩
    refine ⟨{p | p.1 ∈ Γ.profiles ∧ p.2 ∈ Γs.profiles ∧ Γ.u p.1 ≤ Γ.u p.2},
      ?_, fun a _ b _ hΦ => hΦ.2.2, fun p hp => ⟨hp.1, hp.2.1⟩⟩
    exact h.mono fun ω hω => ⟨X.mem Γ ω, X.mem Γs ω, hω⟩
  · rintro ⟨Φ, hΦ⟩
    exact ⟨hsub, hΦ.corresponds.mono fun ω hω =>
      hΦ.improving _ (X.mem Γ ω) _ (X.mem Γs ω) hω⟩

end Play

end SafeParetoImprovements
