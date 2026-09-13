import SafeParetoImprovements.Correspondence
import SafeParetoImprovements.Reduction
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Game isomorphism (§2) and Lemma 4

An isomorphism between `Γ = (A, u)` and `Γ' = (A', u')` is, in the paper, an `n`-tuple
of functions `Φᵢ : Aᵢ → A'ᵢ` together with `λ ∈ ℝⁿ₊` and `c ∈ ℝⁿ` such that
`uᵢ(a) = λᵢ u'ᵢ(Φ(a)) + cᵢ` for all `a ∈ A` and all `i`.

Two things the printed definition leaves open are fixed here, and both are forced
(`dd:iso`, errata D5):

* **the `Φᵢ` are bijections `Aᵢ → A'ᵢ`.**  Unstated in §2, but Appendix C's proof of
  Lemma 4 invokes `Φ⁻¹` and "bijectivity of `Φ, Ψ`", Lemma 13's proof relabels along an
  isomorphism, and §4.4.3 composes isomorphisms through inverses.  Without it,
  Assumption 2 would force the representatives of a larger reduced game into the image
  of a smaller one.
* **`λᵢ > 0`**, not `≥ 0`.  With `λᵢ = 0` allowed, "isomorphic" is not symmetric (the
  inverse needs `1/λᵢ`), so the equivalence relation the book construction of §4.4.3
  quotients by would not exist.

The carrier is a structure with the constants as *data* (`scale`, `shift`) rather than
existentially, so that composition and inversion are computations.  `Isomorphic Γ Γ'`
is the paper's "there is an isomorphism".

Lemma 4 is proved through the automorphism `Φ⁻¹ ∘ Ψ` of `Γ` rather than by Appendix
C's direct constants argument: an automorphism of a finite game is payoff-preserving
(`GameIso.payoff_eq_of_self`, the max/min argument), which is the content of "`Φ` and `Ψ`
are isomorphisms relative to the same constants".
-/

namespace SafeParetoImprovements

open Filter Set
open scoped SetRel

universe u v w

variable {N : Type u} {𝒜 : N → Type v}

/-- A game inhabits every player's slice of the action universe: `Aᵢ` is a nonempty subset
of `𝒜 i`.  This is what `Function.invFunOn` needs to invert an isomorphism, so `GameIso.symm`
takes it from the game in scope instead of asking callers for `[∀ i, Nonempty (𝒜 i)]`
(R1-F03, R1-F13).  Not an instance: instance search cannot guess which game to use. -/
lemma Game.nonempty_universe (Γ : Game N 𝒜) (i : N) : Nonempty (𝒜 i) :=
  ⟨(Γ.nonempty i).choose⟩

/-- A **game isomorphism** `Φ : Γ → Γ'` (§2, `dd:iso`): per-player bijections
`Aᵢ → A'ᵢ` (recorded on the whole universe, constrained on `Aᵢ`) and strictly positive
affine constants with `uᵢ(a) = λᵢ · u'ᵢ(Φ(a)) + cᵢ` on the profiles of `Γ`. -/
structure GameIso (Γ Γ' : Game N 𝒜) where
  /-- `Φᵢ`, as a function on the universe of player `i`. -/
  toFun : ∀ i, 𝒜 i → 𝒜 i
  /-- `Φᵢ` restricts to a bijection `Aᵢ → A'ᵢ`. -/
  bijOn : ∀ i, BijOn (toFun i) (Γ.S i : Set (𝒜 i)) (Γ'.S i)
  /-- `λᵢ`. -/
  scale : N → ℝ
  /-- `λᵢ > 0`. -/
  scale_pos : ∀ i, 0 < scale i
  /-- `cᵢ`. -/
  shift : N → ℝ
  /-- `uᵢ(a) = λᵢ u'ᵢ(Φ(a)) + cᵢ` for `a ∈ A`. -/
  affine : ∀ a ∈ Γ.profiles, ∀ i, Γ.u a i = scale i * Γ'.u (fun j => toFun j (a j)) i + shift i

/-- `Γ` and `Γ'` are **isomorphic**: some isomorphism exists. -/
def Game.Isomorphic (Γ Γ' : Game N 𝒜) : Prop := Nonempty (GameIso Γ Γ')

namespace GameIso

variable {Γ Γ' Γ'' : Game N 𝒜}

/-- The action of `Φ` on profiles, `Φ(a) = (Φ₁(a₁), …, Φₙ(aₙ))`. -/
def map (φ : GameIso Γ Γ') (a : ∀ i, 𝒜 i) : ∀ i, 𝒜 i := fun j => φ.toFun j (a j)

@[simp] lemma map_apply (φ : GameIso Γ Γ') (a : ∀ i, 𝒜 i) (j : N) :
    φ.map a j = φ.toFun j (a j) := rfl

lemma map_mem (φ : GameIso Γ Γ') {a : ∀ i, 𝒜 i} (ha : a ∈ Γ.profiles) :
    φ.map a ∈ Γ'.profiles := fun j => (φ.bijOn j).mapsTo (ha j)

lemma affine' (φ : GameIso Γ Γ') {a : ∀ i, 𝒜 i} (ha : a ∈ Γ.profiles) (i : N) :
    Γ.u a i = φ.scale i * Γ'.u (φ.map a) i + φ.shift i := φ.affine a ha i

lemma map_injOn (φ : GameIso Γ Γ') : InjOn φ.map Γ.profiles := by
  intro a ha b hb hab
  funext j
  exact (φ.bijOn j).injOn (ha j) (hb j) (congrFun hab j)

lemma map_surjOn (φ : GameIso Γ Γ') : SurjOn φ.map Γ.profiles Γ'.profiles := by
  intro b hb
  choose a ha using fun j => (φ.bijOn j).surjOn (hb j)
  exact ⟨a, fun j => (ha j).1, funext fun j => (ha j).2⟩

lemma map_bijOn (φ : GameIso Γ Γ') : BijOn φ.map Γ.profiles Γ'.profiles :=
  ⟨fun _ ha => φ.map_mem ha, φ.map_injOn, φ.map_surjOn⟩

/-- `Φ` as a single-valued outcome correspondence `A ⊸ A'`. -/
def rel (φ : GameIso Γ Γ') : SetRel (∀ i, 𝒜 i) (∀ i, 𝒜 i) :=
  {p | p.1 ∈ Γ.profiles ∧ p.2 = φ.map p.1}

@[simp] lemma mem_rel (φ : GameIso Γ Γ') (a b : ∀ i, 𝒜 i) :
    a ~[φ.rel] b ↔ a ∈ Γ.profiles ∧ b = φ.map a := Iff.rfl

/-- The identity isomorphism. -/
def refl (Γ : Game N 𝒜) : GameIso Γ Γ where
  toFun _ := id
  bijOn _ := bijOn_id _
  scale _ := 1
  scale_pos _ := one_pos
  shift _ := 0
  affine _ _ _ := by simp

@[simp] lemma refl_map (Γ : Game N 𝒜) (a : ∀ i, 𝒜 i) : (refl Γ).map a = a := rfl

/-- Two games *equal in the paper's sense* (`Game.EqOn`) are isomorphic by the identity:
same action sets, and the same payoffs where they matter. -/
def ofEqOn {Γ Γ' : Game N 𝒜} (h : Γ.EqOn Γ') : GameIso Γ Γ' where
  toFun _ := id
  bijOn i := by rw [show Γ.S i = Γ'.S i from congrFun h.1 i]; exact bijOn_id _
  scale _ := 1
  scale_pos _ := one_pos
  shift _ := 0
  affine a ha i := by simpa using h.2 a ha i

@[simp] lemma ofEqOn_map {Γ Γ' : Game N 𝒜} (h : Γ.EqOn Γ') (a : ∀ i, 𝒜 i) :
    (ofEqOn h).map a = a := rfl

/-- Composition: first `φ`, then `ψ`. -/
def trans (φ : GameIso Γ Γ') (ψ : GameIso Γ' Γ'') : GameIso Γ Γ'' where
  toFun i := ψ.toFun i ∘ φ.toFun i
  bijOn i := (ψ.bijOn i).comp (φ.bijOn i)
  scale i := φ.scale i * ψ.scale i
  scale_pos i := mul_pos (φ.scale_pos i) (ψ.scale_pos i)
  shift i := φ.scale i * ψ.shift i + φ.shift i
  affine a ha i := by
    rw [φ.affine a ha i, ψ.affine (fun j => φ.toFun j (a j)) (φ.map_mem ha) i]
    simp only [Function.comp]
    ring

@[simp] lemma trans_map (φ : GameIso Γ Γ') (ψ : GameIso Γ' Γ'') (a : ∀ i, 𝒜 i) :
    (φ.trans ψ).map a = ψ.map (φ.map a) := rfl

section inv

/-- The inverse isomorphism, with `Φᵢ⁻¹` chosen on `A'ᵢ` by `invFunOn` and the constants
`1/λᵢ`, `−cᵢ/λᵢ`.  The pointwise nonemptiness `Function.invFunOn` needs is taken from
`Γ` itself (`Game.nonempty_universe`) rather than demanded of the caller. -/
noncomputable def symm (φ : GameIso Γ Γ') : GameIso Γ' Γ :=
  haveI : ∀ i, Nonempty (𝒜 i) := Γ.nonempty_universe
  { toFun := fun i => Function.invFunOn (φ.toFun i) (Γ.S i)
    bijOn := fun i => (bijOn_comm (φ.bijOn i).invOn_invFunOn.symm).1 (φ.bijOn i)
    scale := fun i => (φ.scale i)⁻¹
    scale_pos := fun i => inv_pos.2 (φ.scale_pos i)
    shift := fun i => -(φ.shift i / φ.scale i)
    affine := fun b hb i => by
      have hmem : (fun j => Function.invFunOn (φ.toFun j) (Γ.S j) (b j)) ∈ Γ.profiles := fun j =>
        (φ.bijOn j).surjOn.mapsTo_invFunOn (hb j)
      have hmap : (fun j => φ.toFun j (Function.invFunOn (φ.toFun j) (Γ.S j) (b j))) = b := by
        funext j
        exact (φ.bijOn j).invOn_invFunOn.2 (hb j)
      have h := φ.affine _ hmem i
      rw [hmap] at h
      have hpos := φ.scale_pos i
      rw [h]
      field_simp
      ring }

lemma symm_map_map (φ : GameIso Γ Γ') {a : ∀ i, 𝒜 i} (ha : a ∈ Γ.profiles) :
    φ.symm.map (φ.map a) = a := by
  haveI : ∀ i, Nonempty (𝒜 i) := Γ.nonempty_universe
  funext j
  exact (φ.bijOn j).invOn_invFunOn.1 (ha j)

lemma map_symm_map (φ : GameIso Γ Γ') {b : ∀ i, 𝒜 i} (hb : b ∈ Γ'.profiles) :
    φ.map (φ.symm.map b) = b := by
  haveI : ∀ i, Nonempty (𝒜 i) := Γ.nonempty_universe
  funext j
  exact (φ.bijOn j).invOn_invFunOn.2 (hb j)

/-- The coordinate-level form of `map_symm_map`: `Φᵢ(Φᵢ⁻¹(x)) = x` for `x ∈ A'ᵢ`. -/
lemma toFun_symm_toFun (φ : GameIso Γ Γ') {i : N} {x : 𝒜 i} (hx : x ∈ Γ'.S i) :
    φ.toFun i (φ.symm.toFun i x) = x := by
  haveI : ∀ i, Nonempty (𝒜 i) := Γ.nonempty_universe
  exact (φ.bijOn i).invOn_invFunOn.2 hx

/-- `Φᵢ⁻¹` maps `A'ᵢ` into `Aᵢ`. -/
lemma symm_toFun_mem (φ : GameIso Γ Γ') {i : N} {x : 𝒜 i} (hx : x ∈ Γ'.S i) :
    φ.symm.toFun i x ∈ Γ.S i :=
  Finset.mem_coe.1 ((φ.symm.bijOn i).mapsTo (Finset.mem_coe.2 hx))

end inv

/-! ### Automorphisms preserve payoffs

An isomorphism from a finite game to itself has `λᵢ = 1` and `cᵢ = 0` for every player
whose payoff is not constant, hence preserves every payoff: `uᵢ(θ(a)) = uᵢ(a)`.  This is
the "same constants" step of Appendix C. -/

section auto

variable [Fintype N]

/-- An automorphism `θ` of `Γ` preserves payoffs on `A`. -/
lemma payoff_eq_of_self (θ : GameIso Γ Γ) {a : ∀ i, 𝒜 i} (ha : a ∈ Γ.profiles) (i : N) :
    Γ.u (θ.map a) i = Γ.u a i := by
  classical
  have hne : Γ.profilesFinset.Nonempty := by
    obtain ⟨b, hb⟩ := Γ.profiles_nonempty
    exact ⟨b, (Γ.mem_profilesFinset).2 hb⟩
  obtain ⟨aM, haM, hM⟩ := Finset.exists_max_image Γ.profilesFinset (fun b => Γ.u b i) hne
  obtain ⟨am, ham, hm⟩ := Finset.exists_min_image Γ.profilesFinset (fun b => Γ.u b i) hne
  simp only [Game.mem_profilesFinset] at haM ham hM hm
  have hl : 0 < θ.scale i := θ.scale_pos i
  -- `M = λ M + c` for the maximum `M`
  have hM1 : Γ.u aM i ≤ θ.scale i * Γ.u aM i + θ.shift i := by
    have h1 := θ.affine' haM i
    have h2 : Γ.u (θ.map aM) i ≤ Γ.u aM i := hM _ (θ.map_mem haM)
    nlinarith
  have hM2 : θ.scale i * Γ.u aM i + θ.shift i ≤ Γ.u aM i := by
    obtain ⟨b, hb, hbM⟩ := θ.map_surjOn haM
    have h1 := θ.affine' hb i
    rw [hbM] at h1
    have h2 := hM b hb
    linarith
  have hMeq : Γ.u aM i = θ.scale i * Γ.u aM i + θ.shift i := le_antisymm hM1 hM2
  -- `m = λ m + c` for the minimum `m`
  have hm1 : θ.scale i * Γ.u am i + θ.shift i ≤ Γ.u am i := by
    have h1 := θ.affine' ham i
    have h2 : Γ.u am i ≤ Γ.u (θ.map am) i := hm _ (θ.map_mem ham)
    nlinarith
  have hm2 : Γ.u am i ≤ θ.scale i * Γ.u am i + θ.shift i := by
    obtain ⟨b, hb, hbm⟩ := θ.map_surjOn ham
    have h1 := θ.affine' hb i
    rw [hbm] at h1
    have h2 := hm b hb
    linarith
  have hmeq : Γ.u am i = θ.scale i * Γ.u am i + θ.shift i := le_antisymm hm2 hm1
  by_cases hMm : Γ.u aM i = Γ.u am i
  · -- constant payoff on `A`
    have hconst : ∀ b ∈ Γ.profiles, Γ.u b i = Γ.u aM i := fun b hb =>
      le_antisymm (hM b hb) (hMm ▸ hm b hb)
    rw [hconst _ (θ.map_mem ha), hconst _ ha]
  · have hl1 : θ.scale i = 1 := by
      have : (Γ.u aM i - Γ.u am i) * (1 - θ.scale i) = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · exact absurd (sub_eq_zero.1 h) hMm
      · linarith
    have hc0 : θ.shift i = 0 := by rw [hl1] at hMeq; linarith
    have h1 := θ.affine' ha i
    rw [hl1, hc0] at h1
    linarith

/-- **Any** isomorphism between two games that are equal in the paper's sense
(`Game.EqOn`) preserves payoffs: it is an automorphism of `Γ` once the target's action
sets and payoffs are identified with `Γ`'s, so `payoff_eq_of_self` applies.  This is what
makes Assumption 2 forbid a strict SPI between two `EqOn`-equal **reduced** presentations
of one paper game (`Play.SatisfiesA2.not_isStrictSPI_of_eqOn`, R1-F01).  The reducedness
qualification comes from Assumption 2 itself, which is a hypothesis only about games
without strictly dominated actions and constrains no non-reduced pair; this lemma is
unconditional. -/
lemma payoff_eq_of_eqOn (h : Γ.EqOn Γ') (φ : GameIso Γ Γ') {a : ∀ i, 𝒜 i}
    (ha : a ∈ Γ.profiles) (i : N) : Γ.u (φ.map a) i = Γ.u a i := by
  have hprof : Γ'.profiles = Γ.profiles := by ext b; simp [Game.profiles, h.1]
  let θ : GameIso Γ Γ :=
    { toFun := φ.toFun
      bijOn := fun j => by
        nth_rewrite 2 [show Γ.S j = Γ'.S j from congrFun h.1 j]; exact φ.bijOn j
      scale := φ.scale
      scale_pos := φ.scale_pos
      shift := φ.shift
      affine := fun b hb j => by
        have hb' := φ.affine b hb j
        rwa [show Γ'.u (fun k => φ.toFun k (b k)) j = Γ.u (fun k => φ.toFun k (b k)) j from
          (h.2 (φ.map b) (hprof ▸ φ.map_mem hb) j).symm] at hb' }
  exact θ.payoff_eq_of_self ha i

end auto

/-! ### Pareto-improving isomorphisms and Lemma 4 -/

/-- An isomorphism `Φ : Γ → Γ'` into a *subset game* `Γ'` of `Γ` is **Pareto-improving**
if `u(Φ(a)) ≥ u(a)` for every `a ∈ A`, with `u` the payoff of `Γ` (Definition 4 read for
the single-valued correspondence `Φ`). -/
def ParetoImproving (φ : GameIso Γ Γ') : Prop :=
  ∀ a ∈ Γ.profiles, Γ.u a ≤ Γ.u (φ.map a)

/-- **Strictly** Pareto-improving: Pareto-improving, and strict at some outcome. -/
def StrictlyParetoImproving (φ : GameIso Γ Γ') : Prop :=
  φ.ParetoImproving ∧ ∃ a ∈ Γ.profiles, Γ.u a < Γ.u (φ.map a)

section lemma4

variable [Fintype N]

/-- **Lemma 4**: if `Φ` and `Ψ` are isomorphisms between `Γ` and `Γ'` and `Φ` is
Pareto-improving, so is `Ψ`.  (The lemma needs `Γ'` to be a subset game of `Γ` for
"Pareto-improving" to be defined; the printed statement omits this — erratum D2(b).)

Paper node: `Lemma 4` -/
theorem paretoImproving_of_paretoImproving (φ ψ : GameIso Γ Γ') (hφ : φ.ParetoImproving) :
    ψ.ParetoImproving := by
  intro a ha
  -- `θ := Φ⁻¹ ∘ Ψ` is an automorphism of `Γ`, so `u(θ a) = u(a)`; and `Ψ a = Φ (θ a)`.
  let θ : GameIso Γ Γ := ψ.trans φ.symm
  have hθa : θ.map a ∈ Γ.profiles := θ.map_mem ha
  have hΨ : ψ.map a = φ.map (θ.map a) := by
    simp only [θ, trans_map]
    rw [φ.map_symm_map (ψ.map_mem ha)]
  intro i
  calc Γ.u a i = Γ.u (θ.map a) i := (θ.payoff_eq_of_self ha i).symm
    _ ≤ Γ.u (φ.map (θ.map a)) i := hφ _ hθa i
    _ = Γ.u (ψ.map a) i := by rw [hΨ]

/-- **Lemma 4, strict form**: if `Φ` is strictly Pareto-improving, so is `Ψ`.

Paper node: `Lemma 4` -/
theorem strictlyParetoImproving_of_strictlyParetoImproving (φ ψ : GameIso Γ Γ')
    (hφ : φ.StrictlyParetoImproving) : ψ.StrictlyParetoImproving := by
  refine ⟨paretoImproving_of_paretoImproving φ ψ hφ.1, ?_⟩
  obtain ⟨ã, hã, hlt⟩ := hφ.2
  -- take `a := Ψ⁻¹ (Φ ã)`, so that `θ a = ã` for `θ := Φ⁻¹ ∘ Ψ`.
  let θ : GameIso Γ Γ := ψ.trans φ.symm
  refine ⟨ψ.symm.map (φ.map ã), ψ.symm.map_mem (φ.map_mem hã), ?_⟩
  have ha : ψ.symm.map (φ.map ã) ∈ Γ.profiles := ψ.symm.map_mem (φ.map_mem hã)
  have hθ : θ.map (ψ.symm.map (φ.map ã)) = ã := by
    simp only [θ, trans_map]
    rw [ψ.map_symm_map (φ.map_mem hã), φ.symm_map_map hã]
  have hΨ : ψ.map (ψ.symm.map (φ.map ã)) = φ.map ã := ψ.map_symm_map (φ.map_mem hã)
  have hu : Γ.u (ψ.symm.map (φ.map ã)) = Γ.u ã := by
    funext i
    rw [← θ.payoff_eq_of_self ha i, hθ]
  rw [hu, hΨ]
  exact hlt

end lemma4

end GameIso

/-! ### Reducedness transports along an isomorphism

Needed wherever a game is replaced by an isomorphic copy and the copy's play has to be
computed: `Book.playReduced` reduces first, so "the representatives play the token copy"
is only usable once the copy is known to be `Reduced` (§5.1, Lemma 13's relabelling). -/

namespace Game

variable [DecidableEq N] {Γ Γ' : Game N 𝒜}

/-- **Reducedness transports along an isomorphism.**  If `Γ` has no strictly dominated
action and `Φ : Γ → Γ'`, then neither has `Γ'`: pull a dominance in `Γ'` back along `Φ⁻¹`
and use `λᵢ > 0`. -/
lemma Reduced.of_iso (φ : GameIso Γ Γ') (h : Γ.Reduced) : Γ'.Reduced := by
  rintro i a' ⟨b', hd⟩
  rw [Game.strictlyDominates_iff] at hd
  obtain ⟨hb', ha', hlt⟩ := hd
  refine h i (φ.symm.toFun i a') ⟨φ.symm.toFun i b', ?_⟩
  rw [Game.strictlyDominates_iff]
  refine ⟨φ.symm_toFun_mem hb', φ.symm_toFun_mem ha', fun c hc => ?_⟩
  have key : ∀ (x : 𝒜 i), x ∈ Γ'.S i →
      Γ.u (Function.update c i (φ.symm.toFun i x)) i =
        φ.scale i * Γ'.u (Function.update (φ.map c) i x) i + φ.shift i := by
    intro x hx
    have hmem : Function.update c i (φ.symm.toFun i x) ∈ Γ.profiles := by
      intro j
      rcases eq_or_ne j i with rfl | hj
      · simpa using φ.symm_toFun_mem hx
      · rw [Function.update_of_ne hj]; exact hc j
    have hmap : (fun j => φ.toFun j (Function.update c i (φ.symm.toFun i x) j)) =
        Function.update (φ.map c) i x := by
      funext j
      rcases eq_or_ne j i with rfl | hj
      · simpa using φ.toFun_symm_toFun hx
      · simp [GameIso.map, Function.update_of_ne hj]
    have := φ.affine _ hmem i
    rw [hmap] at this
    exact this
  rw [key a' ha', key b' hb']
  have := hlt (φ.map c) (φ.map_mem hc)
  have hs := φ.scale_pos i
  nlinarith

end Game

/-! ### Isomorphisms and the canonical presentation -/

namespace GameIso

variable {Γ Γ' : Game N 𝒜}

/-- An isomorphism between canonical presentations is one between the games: same maps,
same constants, since the canonical presentation agrees with the game on its profiles. -/
def ofCanon (ψ : GameIso Γ.canon Γ'.canon) : GameIso Γ Γ' where
  toFun := ψ.toFun
  bijOn := ψ.bijOn
  scale := ψ.scale
  scale_pos := ψ.scale_pos
  shift := ψ.shift
  affine a ha i := by
    have h := ψ.affine a ha i
    rw [Γ.canon_u_of_mem ha, show (fun j => ψ.toFun j (a j)) = ψ.map a from rfl,
      Γ'.canon_u_of_mem (ψ.map_mem ha)] at h
    exact h

@[simp] lemma ofCanon_map (ψ : GameIso Γ.canon Γ'.canon) (a : ∀ i, 𝒜 i) :
    (ofCanon ψ).map a = ψ.map a := rfl

end GameIso

/-! ### Reduction transports along an isomorphism

An isomorphism `Φ : Γ → Γ'` carries every subset game `G` of `Γ` obtained by elimination
to the subset game `Φ(G)` of `Γ'` (`GameIso.imageGame`), restricts to an isomorphism
`G ≅ Φ(G)` with the same constants (`GameIso.restrict`), and commutes with iterated
elimination: `reduce Γ' = Φ(reduce Γ)` (`GameIso.reduce_eq_imageGame`).  This is what lets
a token copy of a *whole* game be reduced through the copy (Lemma 13's `(Â, û)` is a copy
of `Γ`, not of `reduce Γ`; R7-F02). -/

namespace GameIso

section cast

variable {G₁ G₂ H₁ H₂ : Game N 𝒜}

/-- Transport an isomorphism along equalities of its endpoints. -/
def cast (e : G₁ = G₂) (e' : H₁ = H₂) (φ : GameIso G₁ H₁) : GameIso G₂ H₂ := e ▸ e' ▸ φ

@[simp] lemma cast_map (e : G₁ = G₂) (e' : H₁ = H₂) (φ : GameIso G₁ H₁) :
    (φ.cast e e').map = φ.map := by
  subst e; subst e'; rfl

@[simp] lemma cast_scale (e : G₁ = G₂) (e' : H₁ = H₂) (φ : GameIso G₁ H₁) :
    (φ.cast e e').scale = φ.scale := by
  subst e; subst e'; rfl

@[simp] lemma cast_shift (e : G₁ = G₂) (e' : H₁ = H₂) (φ : GameIso G₁ H₁) :
    (φ.cast e e').shift = φ.shift := by
  subst e; subst e'; rfl

end cast

variable [DecidableEq N] [∀ i, DecidableEq (𝒜 i)] {Γ Γ' : Game N 𝒜} (φ : GameIso Γ Γ')

/-- The image `Φ(G)` of a subset game `G` of `Γ`: the actions `Φᵢ(Gᵢ)`, with `Γ'`'s payoffs. -/
def imageGame (G : Game N 𝒜) : Game N 𝒜 where
  S i := (G.S i).image (φ.toFun i)
  nonempty i := (G.nonempty i).image _
  u := Γ'.u

omit [DecidableEq N] in
@[simp] lemma imageGame_S (G : Game N 𝒜) (i : N) : (φ.imageGame G).S i = (G.S i).image (φ.toFun i) :=
  rfl

omit [DecidableEq N] in
@[simp] lemma imageGame_u (G : Game N 𝒜) : (φ.imageGame G).u = Γ'.u := rfl

omit [DecidableEq N] in
lemma imageGame_isSubsetGameOf {G : Game N 𝒜} (hG : G.IsSubsetGameOf Γ) :
    (φ.imageGame G).IsSubsetGameOf Γ' := by
  intro i x hx
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
  exact (φ.bijOn i).mapsTo (hG i ha)

omit [DecidableEq N] in
lemma imageGame_self : φ.imageGame Γ = Γ' := by
  refine Game.ext' (funext fun i => ?_) rfl
  apply Finset.coe_injective
  rw [imageGame_S, Finset.coe_image]
  exact (φ.bijOn i).image_eq

/-- `Φ` restricted to a subset game `G` of `Γ` carrying `Γ`'s payoffs: an isomorphism
`G ≅ Φ(G)` with the same scales and shifts. -/
def restrict (G : Game N 𝒜) (hG : G.IsSubsetGameOf Γ) (hu : G.u = Γ.u) :
    GameIso G (φ.imageGame G) where
  toFun := φ.toFun
  bijOn i := by
    refine ⟨fun a ha => Finset.mem_coe.2 (Finset.mem_image_of_mem _ ha),
      (φ.bijOn i).injOn.mono (hG i), fun b hb => ?_⟩
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hb)
    exact ⟨a, ha, rfl⟩
  scale := φ.scale
  scale_pos := φ.scale_pos
  shift := φ.shift
  affine a ha i := by
    rw [hu, imageGame_u]
    exact φ.affine a (hG.profiles_subset ha) i

omit [DecidableEq N] in
@[simp] lemma restrict_scale (G : Game N 𝒜) (hG : G.IsSubsetGameOf Γ) (hu : G.u = Γ.u) :
    (φ.restrict G hG hu).scale = φ.scale := rfl

omit [DecidableEq N] in
@[simp] lemma restrict_shift (G : Game N 𝒜) (hG : G.IsSubsetGameOf Γ) (hu : G.u = Γ.u) :
    (φ.restrict G hG hu).shift = φ.shift := rfl

omit [DecidableEq N] in
@[simp] lemma restrict_map (G : Game N 𝒜) (hG : G.IsSubsetGameOf Γ) (hu : G.u = Γ.u)
    (a : ∀ i, 𝒜 i) : (φ.restrict G hG hu).map a = φ.map a := rfl

omit [DecidableEq N] in
@[simp] lemma restrict_toFun (G : Game N 𝒜) (hG : G.IsSubsetGameOf Γ) (hu : G.u = Γ.u) :
    (φ.restrict G hG hu).toFun = φ.toFun := rfl

/-- Strict dominance transports forward along `Φ` on a subset game. -/
lemma strictlyDominates_imageGame {G : Game N 𝒜} (hG : G.IsSubsetGameOf Γ) (hu : G.u = Γ.u)
    {i : N} {a a' : 𝒜 i} (hd : G.StrictlyDominates i a a') :
    (φ.imageGame G).StrictlyDominates i (φ.toFun i a) (φ.toFun i a') := by
  set ψ := φ.restrict G hG hu with hψ
  rw [Game.strictlyDominates_iff] at hd ⊢
  obtain ⟨ha, ha', hlt⟩ := hd
  refine ⟨Finset.mem_image_of_mem _ ha, Finset.mem_image_of_mem _ ha', fun b hb => ?_⟩
  obtain ⟨c, hc, rfl⟩ : ∃ c ∈ G.profiles, ψ.map c = b := by
    refine ⟨ψ.symm.map b, ψ.symm.map_mem hb, ψ.map_symm_map hb⟩
  have key : ∀ x ∈ G.S i, (φ.imageGame G).u (Function.update (ψ.map c) i (φ.toFun i x)) i =
      (G.u (Function.update c i x) i - ψ.shift i) / ψ.scale i := by
    intro x hx
    have hmem : Function.update c i x ∈ G.profiles := by
      intro j
      rcases eq_or_ne j i with rfl | hj
      · simpa using hx
      · rw [Function.update_of_ne hj]; exact hc j
    have hmap : (fun j => ψ.toFun j (Function.update c i x j)) =
        Function.update (ψ.map c) i (φ.toFun i x) := by
      funext j
      rcases eq_or_ne j i with rfl | hj
      · simp [hψ, restrict_toFun]
      · simp [GameIso.map, hψ, restrict_toFun, Function.update_of_ne hj]
    have h := ψ.affine _ hmem i
    rw [hmap] at h
    have hs := ψ.scale_pos i
    rw [h]
    field_simp
    ring
  rw [key a ha, key a' ha']
  have hs := ψ.scale_pos i
  exact div_lt_div_of_pos_right (by linarith [hlt c hc]) hs

lemma imageGame_erase {G : Game N 𝒜} (hG : G.IsSubsetGameOf Γ) {i : N} {a : 𝒜 i}
    (ha : a ∈ G.S i) (h : ((G.S i).erase a).Nonempty)
    (h' : (((φ.imageGame G).S i).erase (φ.toFun i a)).Nonempty) :
    φ.imageGame (G.erase i a h) = (φ.imageGame G).erase i (φ.toFun i a) h' := by
  refine Game.ext' (funext fun j => ?_) rfl
  by_cases hj : j = i
  · subst hj
    rw [imageGame_S, Game.erase_S_self, Game.erase_S_self, imageGame_S]
    ext x
    simp only [Finset.mem_image, Finset.mem_erase]
    constructor
    · rintro ⟨y, ⟨hya, hy⟩, rfl⟩
      exact ⟨fun hxy => hya ((φ.bijOn j).injOn (hG j hy) (hG j ha) hxy), y, hy, rfl⟩
    · rintro ⟨hne, y, hy, rfl⟩
      exact ⟨y, ⟨fun hya => hne (by rw [hya]), hy⟩, rfl⟩
  · rw [imageGame_S, Game.erase_S_of_ne _ _ _ _ hj, Game.erase_S_of_ne _ _ _ _ hj, imageGame_S]

/-- A single elimination transports along `Φ`. -/
lemma elim_imageGame {G G₂ : Game N 𝒜} (hG : G.IsSubsetGameOf Γ) (hu : G.u = Γ.u)
    (h : G.Elim G₂) : (φ.imageGame G).Elim (φ.imageGame G₂) := by
  obtain ⟨i, a, hd, rfl⟩ := h
  obtain ⟨b, hb⟩ := hd
  have hd' : (φ.imageGame G).IsStrictlyDominated i (φ.toFun i a) :=
    ⟨φ.toFun i b, φ.strictlyDominates_imageGame hG hu hb⟩
  refine ⟨i, φ.toFun i a, hd', ?_⟩
  have hmem : a ∈ G.S i := Game.IsStrictlyDominated.mem (Γ := G) ⟨b, hb⟩
  exact φ.imageGame_erase hG hmem _ hd'.erase_nonempty

/-- Iterated elimination transports along `Φ`. -/
lemma elimStar_imageGame {G : Game N 𝒜} (h : Γ.ElimStar G) : Γ'.ElimStar (φ.imageGame G) := by
  have key : (φ.imageGame Γ).ElimStar (φ.imageGame G) := by
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail hchain hstep ih =>
      exact ih.tail (φ.elim_imageGame (Game.ElimStar.isSubsetGameOf hchain)
        (Game.ElimStar.u_eq hchain) hstep)
  have transport : ∀ H : Game N 𝒜, H = Γ' → H.ElimStar (φ.imageGame G) →
      Γ'.ElimStar (φ.imageGame G) := fun H hH hE => hH ▸ hE
  exact transport _ φ.imageGame_self key

/-- **Reduction commutes with isomorphism**: `reduce Γ' = Φ(reduce Γ)`. -/
lemma reduce_eq_imageGame [Fintype N] : Γ'.reduce = φ.imageGame Γ.reduce :=
  Game.reduce_eq_of_reduced_of_elimStar (φ.elimStar_imageGame Γ.elimStar_reduce)
    (Game.Reduced.of_iso (φ.restrict Γ.reduce Γ.reduce_isSubsetGameOf Γ.reduce_u)
      Γ.reduce_reduced)

/-- `Φ` restricted to the reductions: `reduce Γ ≅ reduce Γ'`, with `Φ`'s constants. -/
noncomputable def restrictReduce [Fintype N] : GameIso Γ.reduce Γ'.reduce :=
  (φ.restrict Γ.reduce Γ.reduce_isSubsetGameOf Γ.reduce_u).cast rfl φ.reduce_eq_imageGame.symm

@[simp] lemma restrictReduce_map [Fintype N] (a : ∀ i, 𝒜 i) : φ.restrictReduce.map a = φ.map a := by
  rw [restrictReduce, GameIso.cast_map]; rfl

@[simp] lemma restrictReduce_scale [Fintype N] : φ.restrictReduce.scale = φ.scale := by
  rw [restrictReduce, GameIso.cast_scale]; rfl

@[simp] lemma restrictReduce_shift [Fintype N] : φ.restrictReduce.shift = φ.shift := by
  rw [restrictReduce, GameIso.cast_shift]; rfl

end GameIso

end SafeParetoImprovements
