import SafeParetoImprovements.Correspondence

/-!
# Relations on games built from outcome correspondence (§4.2, prose after Lemma 2)

`∼` is indexed by a correspondence function, so it is not itself a relation on games.
The paper obtains genuine relations by quantifying the function away:

* an **equivalence relation** `R`: `(Γ, Γ') ∈ R` iff there is a single-valued bijection
  `Φ` with `Γ ∼_Φ Γ'` — reflexive, symmetric and transitive by footnote 3 (the identity
  is a single-valued bijection; so is the inverse of one; so is the composite of two);
* a **preorder** `⪰`: `Γ ⪰ Γ'` iff `Γ ∼_Φ Γ'` for a `Φ` that "always increases every
  player's utilities".

The preorder needs a payoff function to say "increases".  Two subset games of a base game
`Γ₀` are compared under `Γ₀`'s payoffs — that is the situation of the SPI selection
problem (§6), where the candidates are SPIs of one base game and the original players
compare them with their own utilities — so the preorder is stated relative to a base
game, and `Γ₀ ⪰ Γˢ` for a subset game `Γˢ` is exactly "`Γˢ` is an SPI on `Γ₀`" by
Theorem 3.  Nothing here is numbered in the paper; these are carriers for unnumbered
prose.

Footnote 5's remark is also here: an outcome that Pareto-dominates every other outcome
makes every singleton subset game on it an SPI, with no assumption on the
representatives (Lemma 2.5 with Theorem 3).
-/

namespace SafeParetoImprovements

open Filter Set
open scoped SetRel

universe u v w

variable {N : Type u} {𝒜 : N → Type v} {Ω : Type w}

/-- A correspondence `Φ : A ⊸ A'` is a **single-valued bijection** between the outcomes
of `Γ` and those of `Γ'`: the graph of a bijection `A → A'`. -/
def Game.IsSingleValuedBijection (Γ Γ' : Game N 𝒜) (Φ : SetRel (∀ i, 𝒜 i) (∀ i, 𝒜 i)) :
    Prop :=
  ∃ f : (∀ i, 𝒜 i) → (∀ i, 𝒜 i), BijOn f Γ.profiles Γ'.profiles ∧
    Φ = {p | p.1 ∈ Γ.profiles ∧ p.2 = f p.1}

namespace Play

variable (X : Play N 𝒜 Ω) (L : Filter Ω)

/-- The equivalence relation `R` of §4.2: `Γ` and `Γ'` correspond along some
single-valued bijection. -/
def BijEquiv (Γ Γ' : Game N 𝒜) : Prop :=
  ∃ Φ, Γ.IsSingleValuedBijection Γ' Φ ∧ X.Corresponds L Γ Γ' Φ

variable {X L}

lemma bijEquiv_refl (Γ : Game N 𝒜) : X.BijEquiv L Γ Γ := by
  refine ⟨{p | p.1 ∈ Γ.profiles ∧ p.2 = p.1}, ⟨id, bijOn_id _, rfl⟩, ?_⟩
  exact Eventually.of_forall fun ω => ⟨X.mem Γ ω, rfl⟩

lemma BijEquiv.symm {Γ Γ' : Game N 𝒜} (h : X.BijEquiv L Γ Γ') :
    X.BijEquiv L Γ' Γ := by
  haveI : Nonempty (∀ i, 𝒜 i) := ⟨Γ.profiles_nonempty.choose⟩
  obtain ⟨Φ, ⟨f, hf, rfl⟩, hc⟩ := h
  refine ⟨{p | p.1 ∈ Γ'.profiles ∧ p.2 = Function.invFunOn f Γ.profiles p.1},
    ⟨Function.invFunOn f Γ.profiles, (bijOn_comm hf.invOn_invFunOn.symm).1 hf, rfl⟩, ?_⟩
  refine hc.mono fun ω hω => ⟨X.mem Γ' ω, ?_⟩
  obtain ⟨ha, hb⟩ := hω
  dsimp only at ha hb ⊢
  rw [hb]
  exact (hf.invOn_invFunOn.1 ha).symm

lemma BijEquiv.trans {Γ Γ' Γ'' : Game N 𝒜} (h : X.BijEquiv L Γ Γ') (h' : X.BijEquiv L Γ' Γ'') :
    X.BijEquiv L Γ Γ'' := by
  obtain ⟨Φ, ⟨f, hf, rfl⟩, hc⟩ := h
  obtain ⟨Ψ, ⟨g, hg, rfl⟩, hc'⟩ := h'
  refine ⟨{p | p.1 ∈ Γ.profiles ∧ p.2 = g (f p.1)}, ⟨g ∘ f, hg.comp hf, rfl⟩, ?_⟩
  refine (hc.and hc').mono fun ω hω => ?_
  obtain ⟨⟨ha, hb⟩, ⟨-, hc''⟩⟩ := hω
  dsimp only at ha hb hc'' ⊢
  exact ⟨ha, by rw [hc'', hb]⟩

/-- `R` is an equivalence relation (footnote 3). -/
lemma bijEquiv_equivalence : Equivalence (X.BijEquiv L) :=
  ⟨bijEquiv_refl, BijEquiv.symm, BijEquiv.trans⟩

variable (X L)

/-- The preorder `⪰` of §4.2, relative to a base game `Γ₀` whose payoffs measure
"increases": `Γ ⪰ Γ'` iff `Γ ∼_Φ Γ'` for some `Φ` that never decreases any player's
`Γ₀`-payoff. -/
def Improves (Γ₀ Γ Γ' : Game N 𝒜) : Prop :=
  ∃ Φ : SetRel (∀ i, 𝒜 i) (∀ i, 𝒜 i), X.Corresponds L Γ Γ' Φ ∧
    ∀ a b, a ~[Φ] b → Γ₀.u a ≤ Γ₀.u b

variable {X L}

lemma improves_refl (Γ₀ Γ : Game N 𝒜) : X.Improves L Γ₀ Γ Γ :=
  ⟨Γ.partialId, corresponds_id X L Γ, fun a b h => by
    have hb : b = a := h.2
    rw [hb]⟩

lemma Improves.trans {Γ₀ Γ Γ' Γ'' : Game N 𝒜} (h : X.Improves L Γ₀ Γ Γ')
    (h' : X.Improves L Γ₀ Γ' Γ'') : X.Improves L Γ₀ Γ Γ'' := by
  obtain ⟨Φ, hc, hΦ⟩ := h
  obtain ⟨Ψ, hc', hΨ⟩ := h'
  exact ⟨Φ ○ Ψ, hc.trans hc', fun a c ⟨b, hab, hbc⟩ => (hΦ a b hab).trans (hΨ b c hbc)⟩

/-- `⪰` is a preorder: reflexive and transitive (but not symmetric or antisymmetric). -/
lemma improves_preorder (Γ₀ : Game N 𝒜) :
    (∀ Γ, X.Improves L Γ₀ Γ Γ) ∧
      ∀ Γ Γ' Γ'', X.Improves L Γ₀ Γ Γ' → X.Improves L Γ₀ Γ' Γ'' → X.Improves L Γ₀ Γ Γ'' :=
  ⟨improves_refl Γ₀, fun _ _ _ h h' => h.trans h'⟩

/-- For a subset game `Γs` of `Γ`, `Γ ⪰ Γs` (relative to `Γ`) is exactly "`Γs` is an SPI
on `Γ`" (Theorem 3). -/
lemma improves_self_iff_isSPI {Γ Γs : Game N 𝒜} (hsub : Γs.IsSubsetGameOf Γ) :
    X.Improves L Γ Γ Γs ↔ X.IsSPI L Γ Γs := by
  constructor
  · rintro ⟨Φ, hc, hΦ⟩
    exact ⟨hsub, hc.mono fun ω hω => hΦ _ _ hω⟩
  · intro h
    obtain ⟨Φ, hΦ⟩ := (X.isSPI_iff_exists_paretoImprovingCorrespondence L hsub).1 h
    exact ⟨Φ, hΦ.corresponds,
      fun a b hab => hΦ.improving a (hΦ.typed hab).1 b (hΦ.typed hab).2 hab⟩

/-- **Footnote 5**: if an outcome `a` of `Γ` Pareto-dominates every outcome of `Γ`, then
any subset game whose only outcome is `a` is an SPI on `Γ`, with no assumption on the
representatives (Lemma 2.5 with Theorem 3). -/
lemma isSPI_of_paretoDominant {Γ Γs : Game N 𝒜} (hsub : Γs.IsSubsetGameOf Γ) {a : ∀ i, 𝒜 i}
    (hdom : ∀ b ∈ Γ.profiles, Γ.u b ≤ Γ.u a) (hs : Γs.profiles = {a}) : X.IsSPI L Γ Γs := by
  refine (X.isSPI_iff_exists_paretoImprovingCorrespondence L hsub).2
    ⟨Γ.allRel Γs, corresponds_allRel X L Γ Γs, fun b hb c hc _ => ?_, fun _ hp => hp⟩
  rw [hs, Set.mem_singleton_iff] at hc
  rw [hc]
  exact hdom b hb

end Play

end SafeParetoImprovements
