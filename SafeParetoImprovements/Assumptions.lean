import SafeParetoImprovements.Isomorphism

/-!
# Assumptions 1 and 2 about the representatives (§4.4)

The paper's two behavioural assumptions, as predicates on a play family and a certainty
filter.  Nothing in `Play` or `Representatives` builds them in; "under Assumptions 1
and 2, …" is a universal quantifier over play families satisfying both.

* **Assumption 1 (elimination):** representatives never play a strictly dominated action,
  and removing one does not change how they play.  Formally `Γ ∼_Φ (A₋ᵢ, Aᵢ − {ãᵢ}, u|…)`
  with `Φ(ãᵢ, a₋ᵢ) = ∅` and `Φ(a) = {a}` otherwise.  The paper's clause "where
  `A₁, …, Aₙ` are pairwise disjoint" exists so that `(ãᵢ, a₋ᵢ)` is unambiguous; over a
  per-player universe it holds automatically (`dd:universe`).  Strict dominance is by a
  *pure* strategy, as in §2; §4.4.4 discusses and rejects the alternatives.
* **Assumption 2 (isomorphism):** two games *without strictly dominated actions* that are
  isomorphic are played isomorphically, via **some** isomorphism.  The existential is
  essential — Rock–Paper–Scissors is isomorphic to itself by rotation — and it is what
  makes Lemma 4 load-bearing: the paper's "`Γ ∼_Φ Γ'` by Assumption 2" is shorthand for
  "`Φ` is an isomorphism, hence by Assumption 2 *some* isomorphism `Ψ` has `Γ ∼_Ψ Γ'`",
  and Lemma 4 transfers Pareto-improvingness from `Φ` to `Ψ`
  (`exists_paretoImproving_corresponds_of_assumption2`).

Both are read literally, "for every game, with certainty" (the weaker of the two
quantifier orders; the solver-wise reading is stronger, and the book model of §4.4.3
satisfies both).  Quantification is over games over the fixed universe.
-/

namespace SafeParetoImprovements

open Filter
open scoped SetRel

universe u v w

variable {N : Type u} {𝒜 : N → Type v} {Ω : Type w}

/-- The correspondence of Assumption 1: `Φ(ãᵢ, a₋ᵢ) = ∅` and `Φ(a) = {a}` whenever
`aᵢ ≠ ãᵢ`. -/
def Game.elimRel (Γ : Game N 𝒜) (i : N) (ã : 𝒜 i) : SetRel (∀ i, 𝒜 i) (∀ i, 𝒜 i) :=
  {p | p.1 ∈ Γ.profiles ∧ p.1 i ≠ ã ∧ p.2 = p.1}

@[simp] lemma Game.mem_elimRel (Γ : Game N 𝒜) (i : N) (ã : 𝒜 i) (a b : ∀ i, 𝒜 i) :
    a ~[Γ.elimRel i ã] b ↔ a ∈ Γ.profiles ∧ a i ≠ ã ∧ b = a := Iff.rfl

namespace Play

variable [DecidableEq N] (X : Play N 𝒜 Ω) (L : Filter Ω)

/-- **Assumption 1**: for every game `Γ`, player `i` and action `ãᵢ` strictly dominated by
another action in `Aᵢ`, `Γ ∼_Φ (A₋ᵢ, Aᵢ − {ãᵢ}, u|…)` with `Φ(ãᵢ, a₋ᵢ) = ∅` and
`Φ(a) = {a}` otherwise.  Stated for a certainty filter (`dd:certainty`).

Paper node: `Assumption 1` -/
def SatisfiesA1 [∀ i, DecidableEq (𝒜 i)] : Prop :=
  ∀ (Γ : Game N 𝒜) (i : N) (ã : 𝒜 i) (h : Γ.IsStrictlyDominated i ã),
    X.Corresponds L Γ (Γ.erase i ã h.erase_nonempty) (Γ.elimRel i ã)

/-- **Assumption 2**: if `Γ` and `Γ'` contain no strictly dominated actions and are
isomorphic, then there *exists* an isomorphism `Φ` with `Γ ∼_Φ Γ'`.  Stated for a
certainty filter (`dd:certainty`).

Paper node: `Assumption 2` -/
def SatisfiesA2 : Prop :=
  ∀ Γ Γ' : Game N 𝒜, Γ.Reduced → Γ'.Reduced → Γ.Isomorphic Γ' →
    ∃ φ : GameIso Γ Γ', X.Corresponds L Γ Γ' φ.rel

variable {X L}

/-- Under Assumption 1 the representatives never play a strictly dominated action
(Lemma 2.6 applied to Assumption 1's correspondence). -/
lemma SatisfiesA1.ne_of_isStrictlyDominated [∀ i, DecidableEq (𝒜 i)] (hA1 : X.SatisfiesA1 L)
    (Γ : Game N 𝒜)
    {i : N} {ã : 𝒜 i} (h : Γ.IsStrictlyDominated i ã) :
    ∀ᶠ ω in L, X.play Γ ω i ≠ ã :=
  (hA1 Γ i ã h).mono fun _ hω => hω.2.1

/-- Under Assumption 1, removing a strictly dominated action does not change the
representatives' play. -/
lemma SatisfiesA1.play_erase [∀ i, DecidableEq (𝒜 i)] (hA1 : X.SatisfiesA1 L) (Γ : Game N 𝒜)
    {i : N} {ã : 𝒜 i}
    (h : Γ.IsStrictlyDominated i ã) :
    ∀ᶠ ω in L, X.play (Γ.erase i ã h.erase_nonempty) ω = X.play Γ ω :=
  (hA1 Γ i ã h).mono fun _ hω => hω.2.2

/-- The **lax use of Assumption 2** (the paragraph after Lemma 4): if `Γ` and `Γ'` are
fully reduced and *some* isomorphism `Γ → Γ'` is Pareto-improving, then under Assumption 2
there is a Pareto-improving isomorphism `Ψ` with `Γ ∼_Ψ Γ'`, i.e. a Pareto-improving
outcome correspondence in the sense of Definition 4.  No subset-game hypothesis is taken
or needed: the paper's uses (§4.4.2, Proposition 6) have the isomorphism between two full
reductions, neither of which is a subset game of the other. -/
lemma exists_paretoImproving_corresponds_of_assumption2 [Fintype N]
    (hA2 : X.SatisfiesA2 L) {Γ Γ' : Game N 𝒜} (hΓ : Γ.Reduced) (hΓ' : Γ'.Reduced)
    (φ : GameIso Γ Γ') (hφ : φ.ParetoImproving) :
    ∃ ψ : GameIso Γ Γ', ψ.ParetoImproving ∧ X.Corresponds L Γ Γ' ψ.rel := by
  obtain ⟨ψ, hψ⟩ := hA2 Γ Γ' hΓ hΓ' ⟨φ⟩
  exact ⟨ψ, GameIso.paretoImproving_of_paretoImproving φ ψ hφ, hψ⟩

omit [DecidableEq N] in
/-- A Pareto-improving isomorphism whose relation the representatives follow is a
Pareto-improving outcome correspondence (Definition 4). -/
lemma paretoImprovingCorrespondence_of_iso {Γ Γ' : Game N 𝒜} (ψ : GameIso Γ Γ')
    (hψ : ψ.ParetoImproving) (hc : X.Corresponds L Γ Γ' ψ.rel) :
    X.ParetoImprovingCorrespondence L Γ Γ' ψ.rel :=
  { corresponds := hc
    improving := fun a _ b _ hab => by
      obtain ⟨ha, rfl⟩ := (ψ.mem_rel a b).1 hab
      exact hψ a ha
    typed := fun p hp => ⟨hp.1, hp.2 ▸ ψ.map_mem hp.1⟩ }

/-- **Assumption 2 forbids a strict SPI between two *reduced* presentations of the same
game** (R1-F01).  `Play` is deliberately a larger class than the paper's `Π`: the paper's
payoff function is defined only on `A`, so `Π` cannot depend on off-domain payoff values,
whereas a `Play` family may distinguish two games that are equal in the paper's sense
(`Game.EqOn`).  Every paper node here quantifies universally over the play family, so the
larger class only *strengthens* those statements; and the phenomenon the extra freedom
allows -- one presentation being a strict SPI on another -- is ruled out for
`EqOn`-equal **reduced** presentations, because every isomorphism between `EqOn`-equal
games preserves payoffs (`GameIso.payoff_eq_of_eqOn`).

The reducedness qualification is not decoration: Assumption 2 is a hypothesis *about
games without strictly dominated actions* and says nothing whatever about a non-reduced
`EqOn`-equal pair, on which a `Play` family may still exhibit the phenomenon.  Only one
of the two reducedness hypotheses is taken, since `EqOn` transports it
(`Game.EqOn.reduced_iff`).

The book witness is `EqOn`-invariant in exactly this sense: it plays two `EqOn`-equal
games through the same page, so no `EqOn`-difference is visible in payoff terms. -/
lemma SatisfiesA2.not_isStrictSPI_of_eqOn [Fintype N] (hA2 : X.SatisfiesA2 L)
    {Γ Γ' : Game N 𝒜} (h : Γ.EqOn Γ') (hΓ : Γ.Reduced) :
    ¬ X.IsStrictSPI L Γ Γ' := by
  rcases L.eq_or_neBot with rfl | hne
  · rintro ⟨-, i, hfreq⟩
    simp at hfreq
  · rintro ⟨-, i, hstrict⟩
    obtain ⟨φ, hc⟩ := hA2 Γ Γ' hΓ (h.reduced_iff.1 hΓ) ⟨GameIso.ofEqOn h⟩
    obtain ⟨ω, hlt, hω⟩ := (hstrict.and_eventually hc).exists
    obtain ⟨hmem, hmap⟩ := (φ.mem_rel _ _).1 hω
    rw [hmap, GameIso.payoff_eq_of_eqOn h φ hmem i] at hlt
    exact lt_irrefl _ hlt

end Play

end SafeParetoImprovements
