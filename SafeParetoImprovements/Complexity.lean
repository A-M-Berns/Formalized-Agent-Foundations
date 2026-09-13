import SafeParetoImprovements.Derivation
import SafeParetoImprovements.PerfectCoordination
import Mathlib.Data.Fintype.CardEmbedding

/-!
# Certificates for the SPI decision problems (§4.6, Appendix D.2)

The membership half of Theorem 9 and the search bound of Proposition 10, carried as the
*qualified* nodes of `dd:complexity` (RULING 6; design note `notes/complexity-layer.md`).
What is rendered is the mathematics of Propositions 23–26: each of the four SPI decision
problems of Definition 5 is equivalent to the existence of a **certificate** — one
injection `Φᵢ : Aʳᵉᵈᵢ ↪ Aᵢ` per player from the fully reduced game back into the original
one — passing the checks the appendix's algorithms perform, and the certificates form a
finite type of cardinality at most `m ^ l` (`m = Σᵢ |Aᵢ|`, `l = Σᵢ |Aʳᵉᵈᵢ|`).  What is
**not** rendered, at every node that prints it, is the complexity-class or running-time
clause ("non-deterministic polynomial time", "`O(m^l)`", "NP-complete"): the paper fixes no
cost model beyond explicit payoff matrices, and no exact-tier claim is attached to a
certificate substitute.  Lemma 27 (Cook, via [12]) is cited and not carried.

Two things the paper's algorithms leave implicit are made explicit here.  The printed
omnilateral algorithm (D.2.1) performs no non-triviality check, so the identity
injections always make it return *True* although the game they build is `reduce Γ` itself
(erratum D17); `Certificate.Nontrivial` is the missing check, in the repaired reading of
Definition 5's item 1 (`dd:nontrivial`).  And the unilateral algorithm's correctness proof
says "we can assume `Γˢ,ʳᵉᵈ` and `Γˢ` have the same action sets for Player `i`"; the Lean
proof does not assume it but transfers the elimination chain (`Game.ElimStar.transfer`).

* `Game.Certificate`, `Certificate.map`, `Certificate.image`, `Certificate.game`,
  `Certificate.iso` — the certificate and the paper's `Γˢ`, an exact copy of `reduce Γ`.
* `Certificate.ParetoImproving`, `StrictlyParetoImproving`, `Nontrivial` — the checks.
* `Game.spiDecision_iff_certificate`, `strictSPIDecision_iff_certificate` — Proposition 23.
* `Certificate.unilateralGame`, `Affine`, `ReducesToImage`;
  `Game.unilateralSPIDecision_iff_certificate`, `strictUnilateralSPIDecision_iff_certificate`
  — Proposition 25.
* `Game.card_certificate_le`, `card_unilateralCertificate_le` — the search bounds of
  Propositions 24 and 26, i.e. Proposition 10.
* `Game.ElimStar.transfer` — the elimination chain of a game transfers to the game with one
  player's action set cut down to what survives, whatever that player's payoffs become.
-/

namespace SafeParetoImprovements

open Set
open scoped SetRel

universe u v

variable {N : Type u} {𝒜 : N → Type v}

noncomputable section

namespace Game

/-! ### Transferring an elimination chain across a change of one player's actions -/

section transfer

/-- The game with the action sets of `Γ₁` and the payoffs of `Γ'`. -/
def withPayoffs (Γ₁ Γ' : Game N 𝒜) : Game N 𝒜 where
  S := Γ₁.S
  nonempty := Γ₁.nonempty
  u := Γ'.u

@[simp] lemma withPayoffs_S (Γ₁ Γ' : Game N 𝒜) : (Γ₁.withPayoffs Γ').S = Γ₁.S := rfl
@[simp] lemma withPayoffs_u (Γ₁ Γ' : Game N 𝒜) : (Γ₁.withPayoffs Γ').u = Γ'.u := rfl

variable [DecidableEq N] [∀ i, DecidableEq (𝒜 i)]

/-- **Transfer of an elimination chain.**  Let `Γ →* Γ₁` by iterated elimination, and let
`Γ'` agree with `Γ` on every player other than `i` (same action sets, same payoffs on the
profiles of `Γ'`) while player `i`'s action set in `Γ'` is exactly what survives in `Γ₁`.
Then `Γ' →* (Γ₁ with the payoffs of Γ')`: each step of the chain that removes an action of
some `j ≠ i` still applies, since `j`'s dominator is untouched and only has fewer opponent
profiles to beat, and the steps removing player `i`'s own actions are simply absent.
Player `i`'s payoffs in `Γ'` are unconstrained — this is what makes the unilateral
algorithm's "`uˢᵢ` arbitrary off `Φ(Aʳᵉᵈ)`" harmless (Proposition 25). -/
lemma ElimStar.transfer {Γ Γ₁ : Game N 𝒜} (h : Γ.ElimStar Γ₁) (Γ' : Game N 𝒜) (i : N)
    (hS : ∀ j, j ≠ i → Γ'.S j = Γ.S j) (hSi : Γ'.S i = Γ₁.S i)
    (hu : ∀ b ∈ Γ'.profiles, ∀ j, j ≠ i → Γ'.u b j = Γ.u b j) :
    Γ'.ElimStar (Γ₁.withPayoffs Γ') := by
  induction h using Relation.ReflTransGen.head_induction_on generalizing Γ' with
  | refl =>
    have : Γ₁.withPayoffs Γ' = Γ' := by
      have hSeq : Γ₁.S = Γ'.S := by
        funext j
        by_cases hj : j = i
        · subst hj; exact hSi.symm
        · exact (hS j hj).symm
      cases Γ₁; cases Γ'
      simp only [withPayoffs, Game.mk.injEq, and_true]
      exact hSeq
    rw [this]
    exact Relation.ReflTransGen.refl
  | @head Γ G hΓG hG ih =>
    obtain ⟨j, x, hx, rfl⟩ := hΓG
    have hsub : Γ'.IsSubsetGameOf Γ := by
      intro k
      by_cases hk : k = i
      · subst hk; rw [hSi]
        exact (Game.ElimStar.isSubsetGameOf hG k).trans (Γ.erase_isSubsetGameOf j x _ k)
      · rw [hS k hk]
    by_cases hji : j = i
    · subst hji
      refine ih Γ' (fun k hk => ?_) ?_ hu
      · rw [hS k hk, Γ.erase_S_of_ne _ _ _ hk]
      · exact hSi
    · -- the removed action belongs to another player: the same step applies in `Γ'`
      obtain ⟨y, hy⟩ := hx
      rw [strictlyDominates_iff] at hy
      obtain ⟨hy, hxm, hlt⟩ := hy
      have hx' : Γ'.IsStrictlyDominated j x := by
        refine ⟨y, ?_⟩
        rw [strictlyDominates_iff]
        refine ⟨by rw [hS j hji]; exact hy, by rw [hS j hji]; exact hxm, fun b hb => ?_⟩
        have hb' : b ∈ Γ.profiles := hsub.profiles_subset hb
        have hmem : ∀ z ∈ Γ'.S j, Function.update b j z ∈ Γ'.profiles := by
          intro z hz k
          by_cases hk : k = j
          · subst hk; simpa using hz
          · rw [Function.update_of_ne hk]; exact hb k
        rw [hu _ (hmem y (by rw [hS j hji]; exact hy)) j hji,
          hu _ (hmem x (by rw [hS j hji]; exact hxm)) j hji]
        exact hlt b hb'
      have hne : ((Γ'.S j).erase x).Nonempty := hx'.erase_nonempty
      refine Relation.ReflTransGen.head ⟨j, x, hx', rfl⟩ (ih (Γ'.erase j x hne) (fun k hk => ?_) ?_
        fun b hb k hk => ?_)
      · by_cases hkj : k = j
        · subst hkj; rw [Γ'.erase_S_self, Γ.erase_S_self, hS k hk]
        · rw [Γ'.erase_S_of_ne _ _ _ hkj, Γ.erase_S_of_ne _ _ _ hkj, hS k hk]
      · rw [Γ'.erase_S_of_ne _ _ _ (Ne.symm hji), hSi]
      · rw [Γ'.erase_u, Γ.erase_u]
        exact hu b ((Γ'.erase_isSubsetGameOf j x hne).profiles_subset hb) k hk

/-- **Eliminating a dominated set at once.**  If every action outside the target sets
`T j ⊆ Γ.S j` is strictly dominated by an action *inside* `T j`, then iterated elimination
takes `Γ` to the game with action sets `T`: remove the outside actions one at a time; each
dominator survives, and dominance persists in subset games (`strictlyDominates_of_subset`). -/
lemma elimStar_of_dominated [Fintype N] (Γ : Game N 𝒜) (T : ∀ j, Finset (𝒜 j))
    (hne : ∀ j, (T j).Nonempty) (hT : ∀ j, T j ⊆ Γ.S j)
    (hdom : ∀ j, ∀ x ∈ Γ.S j, x ∉ T j → ∃ y ∈ T j, Γ.StrictlyDominates j y x) :
    Γ.ElimStar ⟨T, hne, Γ.u⟩ := by
  suffices ∀ m, ∀ Γ : Game N 𝒜, Γ.size = m → (∀ j, T j ⊆ Γ.S j) →
      (∀ j, ∀ x ∈ Γ.S j, x ∉ T j → ∃ y ∈ T j, Γ.StrictlyDominates j y x) →
      Γ.ElimStar ⟨T, hne, Γ.u⟩ from this _ Γ rfl hT hdom
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro Γ hm hT hdom
    by_cases hall : ∀ j, Γ.S j = T j
    · have : (⟨T, hne, Γ.u⟩ : Game N 𝒜) = Γ := by
        cases Γ
        simp only [Game.mk.injEq, and_true]
        exact (funext hall).symm
      rw [this]
      exact Relation.ReflTransGen.refl
    · push Not at hall
      obtain ⟨j, hj⟩ := hall
      obtain ⟨x, hx, hxT⟩ : ∃ x ∈ Γ.S j, x ∉ T j := by
        by_contra h
        push Not at h
        exact hj (Finset.Subset.antisymm h (hT j))
      obtain ⟨y, -, hyx⟩ := hdom j x hx hxT
      have hd : Γ.IsStrictlyDominated j x := ⟨y, hyx⟩
      have hne' := hd.erase_nonempty
      have hsub := Γ.erase_isSubsetGameOf j x hne'
      have hmemT : ∀ k, ∀ z ∈ T k, z ∈ (Γ.erase j x hne').S k := by
        intro k z hz
        by_cases hk : k = j
        · subst hk
          rw [Γ.erase_S_self]
          exact Finset.mem_erase.2 ⟨fun h => hxT (h ▸ hz), hT k hz⟩
        · rw [Γ.erase_S_of_ne _ _ _ hk]
          exact hT k hz
      refine Relation.ReflTransGen.head ⟨j, x, hd, rfl⟩ ?_
      exact ih _ (hm ▸ Γ.size_erase_lt j x hne' hx) (Γ.erase j x hne') rfl
        (fun k z hz => hmemT k z hz) fun k z hz hzT => by
          obtain ⟨w, hwT, hwz⟩ := hdom k z (hsub k hz) hzT
          exact ⟨w, hwT, strictlyDominates_of_subset hsub rfl hwz (hmemT k w hwT) hz⟩

end transfer

variable [Fintype N] [DecidableEq N] [∀ i, DecidableEq (𝒜 i)]

/-! ### Certificates -/

/-- A **certificate** for the SPI decision problems of `Γ` (Appendix D.2): one injection
`Φᵢ : Aʳᵉᵈᵢ ↪ Aᵢ` per player, from the fully reduced game back into the original one.
This is what the non-deterministic algorithms of Propositions 23 and 25 guess and what the
deterministic searches of Propositions 24 and 26 enumerate; it is a finite type
(`card_certificate_le`). -/
abbrev Certificate (Γ : Game N 𝒜) : Type max u v :=
  ∀ i, {x // x ∈ Γ.reduce.S i} ↪ {x // x ∈ Γ.S i}

namespace Certificate

variable {Γ : Game N 𝒜} (c : Γ.Certificate)

/-- `Φᵢ` as a function on the universe of player `i`: the certificate's injection on
`Aʳᵉᵈᵢ`, the identity elsewhere. -/
def toFun (i : N) (x : 𝒜 i) : 𝒜 i :=
  if h : x ∈ Γ.reduce.S i then (c i ⟨x, h⟩).1 else x

lemma toFun_of_mem {i : N} {x : 𝒜 i} (h : x ∈ Γ.reduce.S i) :
    c.toFun i x = (c i ⟨x, h⟩).1 := by
  simp [toFun, h]

lemma toFun_mem {i : N} {x : 𝒜 i} (h : x ∈ Γ.reduce.S i) : c.toFun i x ∈ Γ.S i := by
  rw [c.toFun_of_mem h]; exact (c i ⟨x, h⟩).2

lemma injOn (i : N) : InjOn (c.toFun i) (Γ.reduce.S i) := by
  intro x hx y hy hxy
  rw [c.toFun_of_mem hx, c.toFun_of_mem hy] at hxy
  have := (c i).injective (Subtype.ext hxy)
  exact congrArg Subtype.val this

/-- `Φ(a) = (Φ₁(a₁), …, Φₙ(aₙ))`. -/
def map (a : ∀ i, 𝒜 i) : ∀ i, 𝒜 i := fun i => c.toFun i (a i)

/-- The image `Φᵢ(Aʳᵉᵈᵢ)`, player `i`'s action set in the certificate's game. -/
def image (i : N) : Finset (𝒜 i) := (Γ.reduce.S i).image (c.toFun i)

lemma image_subset (i : N) : c.image i ⊆ Γ.S i := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
  exact c.toFun_mem hx

lemma image_nonempty (i : N) : (c.image i).Nonempty :=
  (Γ.reduce.nonempty i).image _

lemma map_mem {a : ∀ i, 𝒜 i} (ha : a ∈ Γ.reduce.profiles) : ∀ i, c.map a i ∈ c.image i :=
  fun i => Finset.mem_image.2 ⟨a i, ha i, rfl⟩

lemma image_eq_map_S (i : N) : (c.image i : Set (𝒜 i)) = c.toFun i '' (Γ.reduce.S i) := by
  simp [image, Finset.coe_image]

/-- The inverse of `Φᵢ` on its image (`Φᵢ⁻¹`, chosen on `Aʳᵉᵈᵢ`). -/
noncomputable def inv (i : N) (y : 𝒜 i) : 𝒜 i :=
  haveI : Nonempty (𝒜 i) := Γ.nonempty_universe i
  Function.invFunOn (c.toFun i) (Γ.reduce.S i) y

lemma inv_toFun {i : N} {x : 𝒜 i} (hx : x ∈ Γ.reduce.S i) : c.inv i (c.toFun i x) = x :=
  haveI : Nonempty (𝒜 i) := Γ.nonempty_universe i
  (c.injOn i).leftInvOn_invFunOn hx

lemma inv_mem {i : N} {y : 𝒜 i} (hy : y ∈ c.image i) : c.inv i y ∈ Γ.reduce.S i := by
  haveI : Nonempty (𝒜 i) := Γ.nonempty_universe i
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
  rw [c.inv_toFun hx]; exact hx

lemma toFun_inv {i : N} {y : 𝒜 i} (hy : y ∈ c.image i) : c.toFun i (c.inv i y) = y := by
  haveI : Nonempty (𝒜 i) := Γ.nonempty_universe i
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
  rw [c.inv_toFun hx]

/-- `Φ⁻¹(aˢ)`, coordinatewise. -/
noncomputable def invMap (b : ∀ i, 𝒜 i) : ∀ i, 𝒜 i := fun i => c.inv i (b i)

lemma invMap_map {a : ∀ i, 𝒜 i} (ha : a ∈ Γ.reduce.profiles) : c.invMap (c.map a) = a := by
  funext i; exact c.inv_toFun (ha i)

lemma map_invMap {b : ∀ i, 𝒜 i} (hb : ∀ i, b i ∈ c.image i) : c.map (c.invMap b) = b := by
  funext i; exact c.toFun_inv (hb i)

/-- The paper's `Γˢ` (D.2.1): action sets `Φᵢ(Aʳᵉᵈᵢ)`, payoffs `uˢ(aˢ) = u(Φ⁻¹(aˢ))`.  `u`
is total on the universe (`dd:total-utility`); only the values on the profiles matter. -/
noncomputable def game : Game N 𝒜 where
  S := c.image
  nonempty := c.image_nonempty
  u b := Γ.u (c.invMap b)

@[simp] lemma game_S : c.game.S = c.image := rfl
@[simp] lemma game_u (b : ∀ i, 𝒜 i) : c.game.u b = Γ.u (c.invMap b) := rfl

lemma game_isSubsetGameOf : c.game.IsSubsetGameOf Γ := c.image_subset

/-- `Φ` is a game isomorphism `reduce Γ ≅ Γˢ` with scale `1` and shift `0`. -/
noncomputable def iso : GameIso Γ.reduce c.game where
  toFun := c.toFun
  bijOn i := by
    refine ⟨fun x hx => Finset.mem_image.2 ⟨x, hx, rfl⟩, c.injOn i, fun y hy => ?_⟩
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
    exact ⟨x, hx, rfl⟩
  scale _ := 1
  scale_pos _ := one_pos
  shift _ := 0
  affine a ha i := by
    show Γ.reduce.u a i = 1 * Γ.u (c.invMap (c.map a)) i + 0
    rw [c.invMap_map ha, Game.reduce_u, one_mul, add_zero]

/-- **Check 1 of the algorithms**: `Φ` is Pareto-improving as judged by `Γ`'s own payoffs,
`u(a) ≤ u(Φ(a))` at every outcome of `reduce Γ`. -/
def ParetoImproving : Prop := ∀ a ∈ Γ.reduce.profiles, Γ.u a ≤ Γ.u (c.map a)

/-- Check 1, strict: Pareto-improving and strictly so at some surviving outcome. -/
def StrictlyParetoImproving : Prop :=
  c.ParetoImproving ∧ ∃ a ∈ Γ.reduce.profiles, Γ.u a < Γ.u (c.map a)

/-- **The non-triviality check** the printed algorithm omits (erratum D17): the certificate
moves some player's reduced action set, `Φᵢ(Aʳᵉᵈᵢ) ≠ Aʳᵉᵈᵢ` (Definition 5, item 1, in the
repaired reading `dd:nontrivial`).  The identity certificate fails it. -/
def Nontrivial : Prop := ∃ i, c.image i ≠ Γ.reduce.S i

lemma paretoImproving_iff : c.ParetoImproving ↔ c.iso.ParetoImproving := by
  simp only [ParetoImproving, GameIso.ParetoImproving, Game.reduce_u]; rfl

lemma strictlyParetoImproving_iff :
    c.StrictlyParetoImproving ↔ c.iso.StrictlyParetoImproving := by
  simp only [StrictlyParetoImproving, GameIso.StrictlyParetoImproving, Game.reduce_u,
    c.paretoImproving_iff]; rfl

lemma game_reduced : c.game.Reduced := Reduced.of_iso c.iso Γ.reduce_reduced

lemma game_reduce : c.game.reduce = c.game := Game.reduce_of_reduced c.game_reduced

/-- The certificate's game is an exact copy of `reduce Γ` (`Game.ExactCopy`). -/
lemma exactCopy_game : Γ.reduce.ExactCopy c.game := ⟨c.iso, fun _ => rfl, fun _ => rfl⟩

/-- The **identity certificate**: every player keeps her reduced actions.  It is
Pareto-improving (`refl_paretoImproving`) and the printed algorithm of D.2.1 accepts it,
but it is trivial (`not_refl_nontrivial`): the game it builds is `reduce Γ` itself.  This
is erratum D17 as a Lean fact. -/
def refl (Γ : Game N 𝒜) : Γ.Certificate := fun i =>
  ⟨fun x => ⟨x.1, Γ.reduce_isSubsetGameOf i x.2⟩, fun x y h => by
    apply Subtype.ext
    have := congrArg Subtype.val h
    exact this⟩

lemma refl_toFun (Γ : Game N 𝒜) {i : N} {x : 𝒜 i} (hx : x ∈ Γ.reduce.S i) :
    (refl Γ).toFun i x = x := by
  rw [toFun_of_mem _ hx]; rfl

lemma refl_map (Γ : Game N 𝒜) {a : ∀ i, 𝒜 i} (ha : a ∈ Γ.reduce.profiles) : (refl Γ).map a = a :=
  funext fun i => refl_toFun Γ (ha i)

lemma refl_image (Γ : Game N 𝒜) (i : N) : (refl Γ).image i = Γ.reduce.S i := by
  ext x
  simp only [image, Finset.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩; rw [refl_toFun Γ hy]; exact hy
  · intro hx; exact ⟨x, hx, refl_toFun Γ hx⟩

lemma refl_paretoImproving (Γ : Game N 𝒜) : (refl Γ).ParetoImproving := fun a ha => by
  rw [refl_map Γ ha]

lemma not_refl_nontrivial (Γ : Game N 𝒜) : ¬ (refl Γ).Nontrivial := by
  rintro ⟨i, hi⟩; exact hi (refl_image Γ i)

/-- The certificate read off an isomorphism `reduce Γ ≅ reduce Γs` for a subset game `Γs`:
restrict `Φᵢ` to `Aʳᵉᵈᵢ`. -/
def ofIso {Γs : Game N 𝒜} (hsub : Γs.IsSubsetGameOf Γ) (ψ : GameIso Γ.reduce Γs.reduce) :
    Γ.Certificate := fun i =>
  ⟨fun x => ⟨ψ.toFun i x.1, hsub i (Γs.reduce_isSubsetGameOf i ((ψ.bijOn i).mapsTo x.2))⟩,
    fun x y hxy => Subtype.ext ((ψ.bijOn i).injOn x.2 y.2 (congrArg Subtype.val hxy))⟩

lemma ofIso_toFun {Γs : Game N 𝒜} (hsub : Γs.IsSubsetGameOf Γ) (ψ : GameIso Γ.reduce Γs.reduce)
    {i : N} {x : 𝒜 i} (hx : x ∈ Γ.reduce.S i) : (ofIso hsub ψ).toFun i x = ψ.toFun i x := by
  rw [toFun_of_mem _ hx]; rfl

lemma ofIso_map {Γs : Game N 𝒜} (hsub : Γs.IsSubsetGameOf Γ) (ψ : GameIso Γ.reduce Γs.reduce)
    {a : ∀ i, 𝒜 i} (ha : a ∈ Γ.reduce.profiles) : (ofIso hsub ψ).map a = ψ.map a := by
  funext i; exact ofIso_toFun hsub ψ (ha i)

lemma ofIso_image {Γs : Game N 𝒜} (hsub : Γs.IsSubsetGameOf Γ) (ψ : GameIso Γ.reduce Γs.reduce)
    (i : N) : (ofIso hsub ψ).image i = Γs.reduce.S i := by
  apply Finset.coe_injective
  rw [image_eq_map_S, ← (ψ.bijOn i).image_eq]
  exact Set.image_congr fun x hx => ofIso_toFun hsub ψ hx

lemma ofIso_nontrivial {Γs : Game N 𝒜} (hsub : Γs.IsSubsetGameOf Γ)
    (ψ : GameIso Γ.reduce Γs.reduce) (hne : Γs.reduce.S ≠ Γ.reduce.S) :
    (ofIso hsub ψ).Nontrivial := by
  by_contra h
  simp only [Nontrivial, not_exists, not_not] at h
  exact hne (funext fun i => (ofIso_image hsub ψ i).symm.trans (h i))

/-- The isomorphism `reduce Γ ≅ reduce Γˢ` a certificate provides, `Γˢ` being reduced. -/
def isoReduce : GameIso Γ.reduce c.game.reduce := c.iso.cast rfl c.game_reduce.symm

lemma isoReduce_map (a : ∀ i, 𝒜 i) : c.isoReduce.map a = c.map a := by
  simp [isoReduce, GameIso.cast_map]; rfl

lemma game_reduce_S_ne (h : c.Nontrivial) : c.game.reduce.S ≠ Γ.reduce.S := by
  obtain ⟨i, hi⟩ := h
  intro heq
  apply hi
  rw [← congrFun heq i, c.game_reduce, game_S]

/-! #### The unilateral algorithm (D.2.2) -/

open Classical in
/-- The paper's unilateral candidate `Γˢ = ((A₋ᵢ, Φᵢ(Aʳᵉᵈᵢ)), (u₋ᵢ, uˢᵢ))`: player `i` is
restricted to `Φᵢ(Aʳᵉᵈᵢ)`, every other player keeps `Aⱼ` and `uⱼ`, and `uˢᵢ = uᵢ ∘ Φ⁻¹` on
`Φ(Aʳᵉᵈ)` — "arbitrary" elsewhere in the paper, `uᵢ` here. -/
def unilateralGame (i : N) : Game N 𝒜 where
  S := Function.update Γ.S i (c.image i)
  nonempty j := by
    by_cases hj : j = i
    · subst hj; simpa using c.image_nonempty j
    · simpa [Function.update_of_ne hj] using Γ.nonempty j
  u b := Function.update (Γ.u b) i
    (if ∀ k, b k ∈ c.image k then Γ.u (c.invMap b) i else Γ.u b i)

variable (i : N)

@[simp] lemma unilateralGame_S_self : (c.unilateralGame i).S i = c.image i := by
  simp [unilateralGame]

lemma unilateralGame_S_of_ne {j : N} (hj : j ≠ i) : (c.unilateralGame i).S j = Γ.S j := by
  simp [unilateralGame, Function.update_of_ne hj]

lemma unilateralGame_u_of_ne (b : ∀ k, 𝒜 k) {j : N} (hj : j ≠ i) :
    (c.unilateralGame i).u b j = Γ.u b j := by
  simp [unilateralGame, Function.update_of_ne hj]

lemma unilateralGame_u_self {b : ∀ k, 𝒜 k} (hb : ∀ k, b k ∈ c.image k) :
    (c.unilateralGame i).u b i = Γ.u (c.invMap b) i := by
  simp [unilateralGame, hb]

lemma unilateralGame_isSubsetGameOf : (c.unilateralGame i).IsSubsetGameOf Γ := by
  intro j
  by_cases hj : j = i
  · subst hj; rw [unilateralGame_S_self]; exact c.image_subset j
  · rw [c.unilateralGame_S_of_ne i hj]

/-- The candidate is a unilateral subset game of `Γ` (Definition 2). -/
lemma unilateral_unilateralGame : Γ.Unilateral (c.unilateralGame i) :=
  ⟨c.unilateralGame_isSubsetGameOf i, i, fun _ hj =>
    ⟨c.unilateralGame_S_of_ne i hj, fun b _ => c.unilateralGame_u_of_ne i b hj⟩⟩

/-- **Check 2 of the unilateral algorithm**: every player other than `i` sees `Φ` as a
positive affine change of her own payoffs, `uⱼ(a) = λⱼ uⱼ(Φ(a)) + cⱼ` on `Aʳᵉᵈ` — so that
`Γ`'s payoffs, which she keeps, make `Φ` a game isomorphism onto the candidate. -/
def Affine : Prop :=
  ∀ j, j ≠ i → ∃ l : ℝ, 0 < l ∧ ∃ k : ℝ, ∀ a ∈ Γ.reduce.profiles, Γ.u a j = l * Γ.u (c.map a) j + k

/-- **Check 3 of the unilateral algorithm**: the candidate reduces to the image block
`Φ(Aʳᵉᵈ)`. -/
def ReducesToImage : Prop := (c.unilateralGame i).reduce.S = c.image

/-- The scale `λⱼ` of check 2 (`1` for player `i`). -/
def affineScale (hA : c.Affine i) (j : N) : ℝ :=
  if hj : j = i then 1 else Classical.choose (hA j hj)

/-- The shift `cⱼ` of check 2 (`0` for player `i`). -/
def affineShift (hA : c.Affine i) (j : N) : ℝ :=
  if hj : j = i then 0 else Classical.choose (Classical.choose_spec (hA j hj)).2

lemma affineScale_pos (hA : c.Affine i) (j : N) : 0 < c.affineScale i hA j := by
  unfold affineScale
  split_ifs with hj
  · exact one_pos
  · exact (Classical.choose_spec (hA j hj)).1

lemma affine_spec (hA : c.Affine i) {j : N} (hj : j ≠ i) {a : ∀ k, 𝒜 k}
    (ha : a ∈ Γ.reduce.profiles) :
    Γ.u a j = c.affineScale i hA j * Γ.u (c.map a) j + c.affineShift i hA j := by
  simp only [affineScale, affineShift, dif_neg hj]
  exact (Classical.choose_spec (Classical.choose_spec (hA j hj)).2) a ha

/-- The image block `Φ(Aʳᵉᵈ)` of the unilateral candidate, with the candidate's payoffs:
what check 3 says the candidate reduces to. -/
def imageGame : Game N 𝒜 := ⟨c.image, c.image_nonempty, (c.unilateralGame i).u⟩

@[simp] lemma imageGame_S : (c.imageGame i).S = c.image := rfl
@[simp] lemma imageGame_u : (c.imageGame i).u = (c.unilateralGame i).u := rfl

/-- Check 2 makes `Φ` a game isomorphism from `reduce Γ` onto the image block: scale
`1`/shift `0` for player `i`, the `(λⱼ, cⱼ)` of check 2 for the others. -/
def imageIso (hA : c.Affine i) : GameIso Γ.reduce (c.imageGame i) where
  toFun := c.toFun
  bijOn := c.iso.bijOn
  scale := c.affineScale i hA
  scale_pos := c.affineScale_pos i hA
  shift := c.affineShift i hA
  affine a ha j := by
    rw [Game.reduce_u, imageGame_u]
    by_cases hj : j = i
    · subst hj
      rw [affineScale, affineShift, dif_pos rfl, dif_pos rfl, one_mul, add_zero,
        show (fun k => c.toFun k (a k)) = c.map a from rfl,
        c.unilateralGame_u_self _ (c.map_mem ha), c.invMap_map ha]
    · rw [show (fun k => c.toFun k (a k)) = c.map a from rfl, c.unilateralGame_u_of_ne _ _ hj]
      exact c.affine_spec i hA hj ha

lemma imageGame_reduced (hA : c.Affine i) : (c.imageGame i).Reduced :=
  Reduced.of_iso (c.imageIso i hA) Γ.reduce_reduced

lemma reduce_unilateralGame_eq (hR : c.ReducesToImage i) :
    (c.unilateralGame i).reduce = c.imageGame i := by
  have hu := (c.unilateralGame i).reduce_u
  have hS : (c.unilateralGame i).reduce.S = c.image := hR
  generalize (c.unilateralGame i).reduce = G at hS hu
  cases G
  simp only [imageGame, Game.mk.injEq]
  exact ⟨hS, hu⟩

/-- The isomorphism `reduce Γ ≅ reduce Γˢ` that checks 2 and 3 provide. -/
def unilateralIso (hA : c.Affine i) (hR : c.ReducesToImage i) :
    GameIso Γ.reduce (c.unilateralGame i).reduce :=
  (c.imageIso i hA).cast rfl (c.reduce_unilateralGame_eq i hR).symm

lemma unilateralIso_map (hA : c.Affine i) (hR : c.ReducesToImage i) (a : ∀ k, 𝒜 k) :
    (c.unilateralIso i hA hR).map a = c.map a := by
  rw [unilateralIso, GameIso.cast_map]; rfl

/-- **A sufficient condition for check 3**, the form in which the appendix verifies it:
check 2 holds, and every action of every player `j ≠ i` outside `Φⱼ(Aʳᵉᵈⱼ)` is strictly
dominated in the candidate by an action inside it.  Then the candidate reduces to the
image block, which is reduced because it is isomorphic to `reduce Γ`. -/
lemma reducesToImage_of_dominated (hA : c.Affine i)
    (hdom : ∀ j, j ≠ i → ∀ x ∈ Γ.S j, x ∉ c.image j →
      ∃ y ∈ c.image j, (c.unilateralGame i).StrictlyDominates j y x) :
    c.ReducesToImage i := by
  have hchain : (c.unilateralGame i).ElimStar (c.imageGame i) := by
    refine elimStar_of_dominated _ c.image c.image_nonempty (fun j => ?_) fun j x hx hxI => ?_
    · by_cases hj : j = i
      · subst hj; rw [unilateralGame_S_self]
      · rw [c.unilateralGame_S_of_ne i hj]; exact c.image_subset j
    · by_cases hj : j = i
      · subst hj; rw [unilateralGame_S_self] at hx; exact absurd hx hxI
      · rw [c.unilateralGame_S_of_ne i hj] at hx
        exact hdom j hj x hx hxI
  show (c.unilateralGame i).reduce.S = c.image
  rw [Game.reduce_eq_of_reduced_of_elimStar hchain (c.imageGame_reduced i hA)]
  rfl

lemma unilateralGame_reduce_S_ne (hnt : c.Nontrivial) (hR : c.ReducesToImage i) :
    (c.unilateralGame i).reduce.S ≠ Γ.reduce.S := by
  obtain ⟨j, hj⟩ := hnt
  intro heq
  exact hj ((congrFun hR j).symm.trans (congrFun heq j))

section ofUnilateral

variable {Γs : Game N 𝒜} (hsub : Γs.IsSubsetGameOf Γ) (ψ : GameIso Γ.reduce Γs.reduce)
  (hi : ∀ j, j ≠ i → Γs.S j = Γ.S j ∧ ∀ a ∈ Γs.profiles, Γs.u a j = Γ.u a j)

include hi in
/-- Check 2 holds for the certificate read off an isomorphism onto a unilateral subset
game: the other players keep `Γ`'s payoffs, so `ψ`'s affine constants are theirs. -/
lemma ofIso_affine : (ofIso hsub ψ).Affine i := by
  intro j hj
  refine ⟨ψ.scale j, ψ.scale_pos j, ψ.shift j, fun a ha => ?_⟩
  have h := ψ.affine a ha j
  rw [Game.reduce_u, Game.reduce_u,
    show (fun k => ψ.toFun k (a k)) = ψ.map a from rfl] at h
  rw [h, ofIso_map hsub ψ ha, (hi j hj).2 _
    (Γs.reduce_isSubsetGameOf.profiles_subset (ψ.map_mem ha))]

include hi in
/-- Check 3 holds for the certificate read off an isomorphism onto a unilateral subset
game `Γs`: transfer `Γs →* reduce Γs` to the candidate (`ElimStar.transfer`), then note that
the transferred endpoint is isomorphic to `reduce Γs` by the identity on actions with
player `i`'s payoffs rescaled, hence reduced. -/
lemma ofIso_reducesToImage : (ofIso hsub ψ).ReducesToImage i := by
  set c := ofIso hsub ψ with hc
  have himg : ∀ j, c.image j = Γs.reduce.S j := ofIso_image hsub ψ
  set G := c.unilateralGame i with hG
  have hGsub : G.IsSubsetGameOf Γs := by
    intro j
    by_cases hj : j = i
    · subst hj; rw [hG, unilateralGame_S_self, himg]; exact Γs.reduce_isSubsetGameOf j
    · rw [hG, c.unilateralGame_S_of_ne i hj, (hi j hj).1]
  have hchain : G.ElimStar (Γs.reduce.withPayoffs G) := by
    refine Γs.elimStar_reduce.transfer G i (fun j hj => ?_) ?_ (fun b hb j hj => ?_)
    · rw [hG, c.unilateralGame_S_of_ne i hj, (hi j hj).1]
    · rw [hG, unilateralGame_S_self, himg]
    · rw [hG, c.unilateralGame_u_of_ne i b hj, (hi j hj).2 b (hGsub.profiles_subset hb)]
  -- the endpoint is isomorphic to `reduce Γs`, so it is reduced
  have hmemimg : ∀ b ∈ Γs.reduce.profiles, ∀ k, b k ∈ c.image k := fun b hb k => by
    rw [himg]; exact hb k
  let φ : GameIso (Γs.reduce.withPayoffs G) Γs.reduce :=
    { toFun := fun _ => id
      bijOn := fun j => by simpa using Set.bijOn_id _
      scale := fun j => if j = i then ψ.scale i else 1
      scale_pos := fun j => by split_ifs; exacts [ψ.scale_pos i, one_pos]
      shift := fun j => if j = i then ψ.shift i else 0
      affine := fun b hb j => by
        change G.u b j = (if j = i then ψ.scale i else 1) * Γs.reduce.u (fun k => id (b k)) j +
          (if j = i then ψ.shift i else 0)
        have hb' : b ∈ Γs.reduce.profiles := hb
        by_cases hj : j = i
        · subst hj
          rw [if_pos rfl, if_pos rfl, hG, c.unilateralGame_u_self _ (hmemimg b hb'), Game.reduce_u]
          have hinv : c.invMap b ∈ Γ.reduce.profiles := fun k => c.inv_mem (hmemimg b hb' k)
          have h := ψ.affine _ hinv j
          rw [Game.reduce_u, Game.reduce_u,
            show (fun k => ψ.toFun k (c.invMap b k)) = ψ.map (c.invMap b) from rfl,
            ← ofIso_map hsub ψ hinv, ← hc, c.map_invMap (hmemimg b hb')] at h
          exact h
        · rw [if_neg hj, if_neg hj, one_mul, add_zero, hG, c.unilateralGame_u_of_ne i b hj,
            Game.reduce_u]
          exact ((hi j hj).2 b (Γs.reduce_isSubsetGameOf.profiles_subset hb')).symm }
  have hred : (Γs.reduce.withPayoffs G).Reduced := Reduced.of_iso φ.symm Γs.reduce_reduced
  have := Game.reduce_eq_of_reduced_of_elimStar hchain hred
  show G.reduce.S = c.image
  rw [this, withPayoffs_S]
  exact funext fun j => (himg j).symm

end ofUnilateral

end Certificate

/-! ### Proposition 23: the omnilateral certificate characterizations -/

/-- **Proposition 23** (the omnilateral half of Theorem 9's membership claim; erratum D11
reads its "unilateral" as "omnilateral"): the algorithm of Appendix D.2.1 — reduce `Γ`
fully, guess injections `Φᵢ : Aʳᵉᵈᵢ ↪ Aᵢ`, accept iff `Φ` is Pareto-improving and (the
check the printed algorithm omits, erratum D17) non-trivial — returns *True* iff `Γ` is a
"yes" instance of the SPI decision problem.  The certificate `c` is the guess; the game it
builds is `c.game`, an exact copy of `reduce Γ`.

Qualified node (`dd:complexity`): the printed clause "runs in non-deterministic polynomial
time" is not rendered; the certificate type is finite of size at most `m ^ l`
(`card_certificate_le`), which is the mathematics behind it.

Paper node: `Proposition 23`, `Theorem 9` -/
theorem spiDecision_iff_certificate (Γ : Game N 𝒜) :
    Γ.SPIDecision ↔ ∃ c : Γ.Certificate, c.ParetoImproving ∧ c.Nontrivial := by
  constructor
  · rintro ⟨Γs, hsub, hne, hd⟩
    obtain ⟨ψ, hψ⟩ := (exists_paretoImproving_deriv_iff Γ Γs hsub).1 hd
    refine ⟨Certificate.ofIso hsub ψ, fun a ha => ?_, Certificate.ofIso_nontrivial hsub ψ hne⟩
    rw [Certificate.ofIso_map hsub ψ ha]
    have := hψ a ha
    rwa [Game.reduce_u] at this
  · rintro ⟨c, hPI, hnt⟩
    refine ⟨c.game, c.game_isSubsetGameOf, c.game_reduce_S_ne hnt, ?_⟩
    refine (exists_paretoImproving_deriv_iff Γ c.game c.game_isSubsetGameOf).2
      ⟨c.isoReduce, fun a ha => ?_⟩
    rw [c.isoReduce_map, Game.reduce_u]
    exact hPI a ha

/-- **Proposition 23**, strict variant: the same algorithm with "strictly Pareto-improving"
in place of "Pareto-improving" decides the strict SPI decision problem.  Qualified as
`spiDecision_iff_certificate`.

Paper node: `Proposition 23`, `Theorem 9` -/
theorem strictSPIDecision_iff_certificate (Γ : Game N 𝒜) :
    Γ.StrictSPIDecision ↔ ∃ c : Γ.Certificate, c.StrictlyParetoImproving ∧ c.Nontrivial := by
  constructor
  · rintro ⟨Γs, hsub, hne, hd⟩
    obtain ⟨ψ, hψ, a, ha, hlt⟩ := (exists_strictParetoImproving_deriv_iff Γ Γs hsub).1 hd
    refine ⟨Certificate.ofIso hsub ψ, ⟨fun b hb => ?_, a, ha, ?_⟩,
      Certificate.ofIso_nontrivial hsub ψ hne⟩
    · rw [Certificate.ofIso_map hsub ψ hb]
      have := hψ b hb
      rwa [Game.reduce_u] at this
    · rw [Certificate.ofIso_map hsub ψ ha]
      rwa [Game.reduce_u] at hlt
  · rintro ⟨c, ⟨hPI, a, ha, hlt⟩, hnt⟩
    refine ⟨c.game, c.game_isSubsetGameOf, c.game_reduce_S_ne hnt, ?_⟩
    refine (exists_strictParetoImproving_deriv_iff Γ c.game c.game_isSubsetGameOf).2
      ⟨c.isoReduce, fun b hb => ?_, a, ha, ?_⟩
    · rw [c.isoReduce_map, Game.reduce_u]
      exact hPI b hb
    · rw [c.isoReduce_map, Game.reduce_u]
      exact hlt

/-! ### Propositions 24 and 26: the search bound -/

/-- The certificates of `Γ` number at most `m ^ l`, where `m = Σᵢ |Aᵢ|` is the size of `Γ`
and `l = Σᵢ |Aʳᵉᵈᵢ|` the size of its full reduction: there are `mᵢ!/(mᵢ−lᵢ)! ≤ mᵢ^lᵢ ≤ m^lᵢ`
injections for player `i`.  This is the mathematics of the paper's `O(m^l)`. -/
lemma card_certificate_le (Γ : Game N 𝒜) :
    Fintype.card Γ.Certificate ≤ Γ.size ^ Γ.reduce.size := by
  rw [Fintype.card_pi, Game.size, Game.size, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod' fun i _ => ?_
  rw [Fintype.card_embedding_eq, Fintype.card_coe, Fintype.card_coe]
  refine (Nat.descFactorial_le_pow _ _).trans (Nat.pow_le_pow_left ?_ _)
  exact Finset.single_le_sum (f := fun j => (Γ.S j).card) (fun j _ => Nat.zero_le _)
    (Finset.mem_univ i)

/-- **Proposition 24** (and **Proposition 10**, omnilateral case): the (strict) SPI decision
problem is decided by searching the certificates of `Γ`, of which there are at most
`m ^ l`, for one passing the checks of Proposition 23.  Qualified node (`dd:complexity`):
"can be solved in `O(m^l)`" is rendered as the size of the search space together with the
certificate characterization; that each certificate is checked in time polynomial in the
payoff matrices is the clause not rendered.

Paper node: `Proposition 24`, `Proposition 10` -/
theorem spiDecision_search (Γ : Game N 𝒜) :
    (Γ.SPIDecision ↔ ∃ c : Γ.Certificate, c.ParetoImproving ∧ c.Nontrivial) ∧
      (Γ.StrictSPIDecision ↔ ∃ c : Γ.Certificate, c.StrictlyParetoImproving ∧ c.Nontrivial) ∧
      Fintype.card Γ.Certificate ≤ Γ.size ^ Γ.reduce.size :=
  ⟨Γ.spiDecision_iff_certificate, Γ.strictSPIDecision_iff_certificate, Γ.card_certificate_le⟩

/-! ### Proposition 25: the unilateral certificate characterizations -/

/-- **Proposition 25**: the algorithm of Appendix D.2.2 — reduce `Γ` fully, guess a player
`i` and injections `Φⱼ : Aʳᵉᵈⱼ ↪ Aⱼ`, build the candidate `Γˢ = ((A₋ᵢ, Φᵢ(Aʳᵉᵈᵢ)),
(u₋ᵢ, uᵢ ∘ Φ⁻¹))`, and accept iff (1) `Φ` is Pareto-improving, (2) every `j ≠ i` sees `Φ`
as a positive affine change of `uⱼ`, (3) `Γˢ` reduces to `Φ(Aʳᵉᵈ)`, and (the omitted
check, erratum D17) `Φ` is non-trivial — returns *True* iff `Γ` is a "yes" instance of the
unilateral SPI decision problem.  The printed proof's "we can assume `Γˢ,ʳᵉᵈ` and `Γˢ`
have the same action sets for Player `i`" is discharged by `ElimStar.transfer` rather
than assumed.  Qualified node (`dd:complexity`): "runs in non-deterministic polynomial
time" is not rendered.

Paper node: `Proposition 25`, `Theorem 9` -/
theorem unilateralSPIDecision_iff_certificate (Γ : Game N 𝒜) :
    Γ.UnilateralSPIDecision ↔ ∃ (i : N) (c : Γ.Certificate),
      c.ParetoImproving ∧ c.Nontrivial ∧ c.Affine i ∧ c.ReducesToImage i := by
  constructor
  · rintro ⟨Γs, hsub, hne, hd, -, i, hi⟩
    obtain ⟨ψ, hψ⟩ := (exists_paretoImproving_deriv_iff Γ Γs hsub).1 hd
    refine ⟨i, Certificate.ofIso hsub ψ, fun a ha => ?_, Certificate.ofIso_nontrivial hsub ψ hne,
      Certificate.ofIso_affine i hsub ψ hi, Certificate.ofIso_reducesToImage i hsub ψ hi⟩
    rw [Certificate.ofIso_map hsub ψ ha]
    have := hψ a ha
    rwa [Game.reduce_u] at this
  · rintro ⟨i, c, hPI, hnt, hA, hR⟩
    refine ⟨c.unilateralGame i, c.unilateralGame_isSubsetGameOf i,
      c.unilateralGame_reduce_S_ne i hnt hR, ?_, c.unilateral_unilateralGame i⟩
    refine (exists_paretoImproving_deriv_iff Γ _ (c.unilateralGame_isSubsetGameOf i)).2
      ⟨c.unilateralIso i hA hR, fun a ha => ?_⟩
    rw [c.unilateralIso_map, Game.reduce_u]
    exact hPI a ha

/-- **Proposition 25**, strict variant: the same algorithm with check (1) strict decides the
strict unilateral SPI decision problem.  Qualified as `unilateralSPIDecision_iff_certificate`.

Paper node: `Proposition 25`, `Theorem 9` -/
theorem strictUnilateralSPIDecision_iff_certificate (Γ : Game N 𝒜) :
    Γ.StrictUnilateralSPIDecision ↔ ∃ (i : N) (c : Γ.Certificate),
      c.StrictlyParetoImproving ∧ c.Nontrivial ∧ c.Affine i ∧ c.ReducesToImage i := by
  constructor
  · rintro ⟨Γs, hsub, hne, hd, -, i, hi⟩
    obtain ⟨ψ, hψ, a, ha, hlt⟩ := (exists_strictParetoImproving_deriv_iff Γ Γs hsub).1 hd
    refine ⟨i, Certificate.ofIso hsub ψ, ⟨fun b hb => ?_, a, ha, ?_⟩,
      Certificate.ofIso_nontrivial hsub ψ hne,
      Certificate.ofIso_affine i hsub ψ hi, Certificate.ofIso_reducesToImage i hsub ψ hi⟩
    · rw [Certificate.ofIso_map hsub ψ hb]
      have := hψ b hb
      rwa [Game.reduce_u] at this
    · rw [Certificate.ofIso_map hsub ψ ha]
      rwa [Game.reduce_u] at hlt
  · rintro ⟨i, c, ⟨hPI, a, ha, hlt⟩, hnt, hA, hR⟩
    refine ⟨c.unilateralGame i, c.unilateralGame_isSubsetGameOf i,
      c.unilateralGame_reduce_S_ne i hnt hR, ?_, c.unilateral_unilateralGame i⟩
    refine (exists_strictParetoImproving_deriv_iff Γ _ (c.unilateralGame_isSubsetGameOf i)).2
      ⟨c.unilateralIso i hA hR, fun b hb => ?_, a, ha, ?_⟩
    · rw [c.unilateralIso_map, Game.reduce_u]
      exact hPI b hb
    · rw [c.unilateralIso_map, Game.reduce_u]
      exact hlt

/-- The unilateral search space — a player together with a certificate — has at most
`n · m ^ l` elements. -/
lemma card_unilateralCertificate_le (Γ : Game N 𝒜) :
    Fintype.card (N × Γ.Certificate) ≤ Fintype.card N * Γ.size ^ Γ.reduce.size := by
  rw [Fintype.card_prod]
  exact Nat.mul_le_mul_left _ Γ.card_certificate_le

/-- **Proposition 26** (and **Proposition 10**, unilateral case): the (strict) unilateral SPI
decision problem is decided by searching the pairs (player, certificate), of which there
are at most `n · m ^ l`, for one passing the checks of Proposition 25.  Qualified node
(`dd:complexity`) exactly as `spiDecision_search`; the paper's `O(m^l)` absorbs the factor
`n`, and the polynomial cost of the three checks (check 3 is a full reduction) is the
clause not rendered.

Paper node: `Proposition 26`, `Proposition 10` -/
theorem unilateralSPIDecision_search (Γ : Game N 𝒜) :
    (Γ.UnilateralSPIDecision ↔ ∃ (i : N) (c : Γ.Certificate),
        c.ParetoImproving ∧ c.Nontrivial ∧ c.Affine i ∧ c.ReducesToImage i) ∧
      (Γ.StrictUnilateralSPIDecision ↔ ∃ (i : N) (c : Γ.Certificate),
        c.StrictlyParetoImproving ∧ c.Nontrivial ∧ c.Affine i ∧ c.ReducesToImage i) ∧
      Fintype.card (N × Γ.Certificate) ≤ Fintype.card N * Γ.size ^ Γ.reduce.size :=
  ⟨Γ.unilateralSPIDecision_iff_certificate, Γ.strictUnilateralSPIDecision_iff_certificate,
    Γ.card_unilateralCertificate_le⟩

end Game

end

end SafeParetoImprovements
