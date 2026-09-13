import SafeParetoImprovements.Isomorphism
import SafeParetoImprovements.Play
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Topology

/-!
# SPIs under improved coordination — the carriers (§5.1, Lemma 11)

§5 lets the original players hand the representatives a **perfect-coordination token
game** `(Aˢ, uˢ, uᵉ)`: a game `(Aˢ, uˢ)` on fresh token actions, played by the
representatives as usual, together with an assignment `uᵉ` by the original players of a
correlated strategy of the base game — a point of `C(Γ) = u(Δ(A))` — to every token
outcome (extraction l. 1278–1315).  This file carries:

* `Game.feasible` — `C(Γ)`, defined by the paper's formula (payoff vectors of correlated
  strategies) and shown equal to the convex hull of `u(A)` (`dd:feasible`);
* `TokenGame` and Definition 6 (`TokenGame.IsSPI`, `TokenGame.IsStrictSPI`) at the
  certainty-filter level (`dd:certainty`);
* `Game.HasRoomOutside` (with `Game.HasRoom` its `B := Γ.S` case) and the **token copy**
  `Game.tokenCopy`: the paper assumes fresh tokens `Aˢᵢ ∩ Aᵢ = ∅` exist silently; over a
  fixed universe (`dd:universe`) that is a hypothesis on the universe, discharged in
  examples by a universe with spare elements (`dd:room`);
* **Lemma 11** as its mathematical content: `y ∈ C(Γ)` is Pareto-optimal in `C(Γ)` iff the
  paper's linear program has optimum `0`; the "by linear programming, hence in polynomial
  time" clause is not rendered (`dd:complexity`).

The decision problem (Definition 7), Algorithm 1's correctness (Proposition 12), Lemma 13
and Corollary 14 follow in later files of the tranche (`notes/coordination-layer.md`);
Proposition 16 is `Examples/Chicken.lean`.

## `dd:room` in full

The paper assumes silently that fresh token actions `Aˢᵢ` with `Aˢᵢ ∩ Aᵢ = ∅` exist.  Over
a fixed per-player universe (`dd:universe`) that is a property of the *universe*, not of
the game, so it is a hypothesis (`Game.HasRoomOutside`) on §5 constructions and a choice of
universe in §5 examples.  The §5 examples take `𝒜 i := X ⊕ ℕ` with the game's actions in
`inl` and off-profile payoffs `0` (`dd:total-utility`), so freshness confines token sets to
the `inr` copy of `ℕ` and every finite token action set is realized up to relabelling; the
token-game class over that universe is therefore the paper's class, and an impossibility
statement `¬ ∃ T : TokenGame Γ, …` is the paper's impossibility.

**Disclosure:** a universe with only finitely many spare elements would truncate that class
and weaken any such statement — indeed a game using its whole finite universe has
`TokenGame Γ` *empty*, so an impossibility over it is vacuous (round-4 blocker R4-F01).
Where the argument permits, the impossibility is additionally stated label-free, as a fact
about `C(Γ)`-valued random variables, so that it does not depend on how rich the universe
is (`Examples.chicken_no_feasible_dominating_of_mean_cc`).

The predicate is parameterized by the set to *avoid*: every §5 construction tokenizes
`Γ.reduce` (or a subset game) and hands the result back as a `TokenGame Γ`, whose `fresh`
field demands disjointness from `Γ.S i ⊇ Γ.reduce.S i`.  `Γ.reduce.HasRoom` is strictly
weaker than that and does **not** suffice (R4-F01, `dd:room`); the right hypothesis is
`Γ.reduce.HasRoomOutside Γ.S`.
-/

universe u v w

namespace SafeParetoImprovements

open Filter Set

variable {N : Type u} {𝒜 : N → Type v} {Ω : Type w}

namespace Game

variable [Fintype N] [DecidableEq N] (Γ : Game N 𝒜)

/-- A **correlated strategy** of `Γ`: a probability distribution on its outcomes, carried as
a weight function on the universe supported on `Γ.profiles`. -/
structure Correlated where
  /-- `pₐ`. -/
  weight : (∀ i, 𝒜 i) → ℝ
  nonneg : ∀ a, 0 ≤ weight a
  /-- Unplayable profiles carry no weight.  Note this field constrains nothing that
  `Game.feasible` sees — `Correlated.payoff` sums over `Γ.profilesFinset`, so off-profile
  weights never enter — but without it a `Correlated` would not be a distribution on `A`.
  Do not "simplify" it away thinking it is doing work, and do not add a hypothesis
  believing it is missing. -/
  support : ∀ a, a ∉ Γ.profiles → weight a = 0
  sum_eq_one : ∑ a ∈ Γ.profilesFinset, weight a = 1

variable {Γ}

/-- The expected payoff vector `∑ₐ pₐ u(a)` of a correlated strategy. -/
noncomputable def Correlated.payoff (p : Γ.Correlated) : N → ℝ :=
  ∑ a ∈ Γ.profilesFinset, p.weight a • Γ.u a

variable (Γ)

/-- **`C(Γ)`** (extraction l. 1280–1283, `dd:feasible`): the payoff vectors feasible by some
correlated strategy, `u(Δ(A))`. -/
def feasible : Set (N → ℝ) := Set.range (Correlated.payoff (Γ := Γ))

/-- The pure outcome `a` as a correlated strategy. -/
noncomputable def Correlated.pure [DecidableEq (∀ i, 𝒜 i)] {a : ∀ i, 𝒜 i} (ha : a ∈ Γ.profiles) :
    Γ.Correlated where
  weight b := if b = a then 1 else 0
  nonneg b := by split_ifs <;> norm_num
  support b hb := if_neg fun h => hb (by subst h; exact ha)
  sum_eq_one := by
    rw [Finset.sum_ite_eq' Γ.profilesFinset a, if_pos (Γ.mem_profilesFinset.2 ha)]

lemma Correlated.pure_payoff [DecidableEq (∀ i, 𝒜 i)] {a : ∀ i, 𝒜 i} (ha : a ∈ Γ.profiles) :
    (Correlated.pure Γ ha).payoff = Γ.u a := by
  unfold Correlated.payoff Correlated.pure
  simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', if_pos (Γ.mem_profilesFinset.2 ha)]

lemma u_mem_feasible {a : ∀ i, 𝒜 i} (ha : a ∈ Γ.profiles) : Γ.u a ∈ Γ.feasible := by
  classical
  exact ⟨Correlated.pure Γ ha, Correlated.pure_payoff Γ ha⟩

variable {Γ}

/-- Correlated strategies mix. -/
noncomputable def Correlated.mix (p q : Γ.Correlated) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    Γ.Correlated where
  weight a := θ * p.weight a + (1 - θ) * q.weight a
  nonneg a := add_nonneg (mul_nonneg h0 (p.nonneg a)) (mul_nonneg (sub_nonneg.2 h1) (q.nonneg a))
  support a ha := by rw [p.support a ha, q.support a ha, mul_zero, mul_zero, add_zero]
  sum_eq_one := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, p.sum_eq_one, q.sum_eq_one]
    ring

lemma Correlated.mix_payoff (p q : Γ.Correlated) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    (p.mix q h0 h1).payoff = θ • p.payoff + (1 - θ) • q.payoff := by
  unfold Correlated.payoff Correlated.mix
  simp only [Finset.smul_sum, smul_smul, ← Finset.sum_add_distrib, add_smul]

/-! #### Interoperability with Mathlib's standard simplex

A correlated strategy is a point of `stdSimplex ℝ A` on the outcomes `A = Γ.profilesFinset`
(R5-F15): `Correlated.toStdSimplex` restricts the weights to the outcomes, `Correlated.ofStdSimplex`
zero-extends a simplex point to the universe, and the two are inverse (`ofStdSimplex_toStdSimplex`,
`toStdSimplex_ofStdSimplex`), so Mathlib's simplex API (`convex_stdSimplex`, `isCompact_stdSimplex`,
…) is available for `Correlated` without a second representation. -/

/-- The weights of a correlated strategy on the outcomes, as a point of the standard simplex. -/
def Correlated.toStdSimplex (p : Γ.Correlated) : stdSimplex ℝ Γ.profilesFinset :=
  ⟨fun a => p.weight a.1, fun a => p.nonneg a.1, by
    rw [← p.sum_eq_one, ← Finset.sum_coe_sort Γ.profilesFinset]⟩

/-- A point of the standard simplex on the outcomes, zero-extended to the universe. -/
noncomputable def Correlated.ofStdSimplex [DecidableEq (∀ i, 𝒜 i)]
    (f : stdSimplex ℝ Γ.profilesFinset) : Γ.Correlated where
  weight a := if h : a ∈ Γ.profilesFinset then f.1 ⟨a, h⟩ else 0
  nonneg a := by
    split_ifs
    · exact f.2.1 _
    · exact le_rfl
  support a ha := dif_neg fun h => ha (Γ.mem_profilesFinset.1 h)
  sum_eq_one := by
    rw [← f.2.2, ← Finset.sum_coe_sort Γ.profilesFinset]
    exact Finset.sum_congr rfl fun a _ => dif_pos a.2

lemma Correlated.ofStdSimplex_toStdSimplex [DecidableEq (∀ i, 𝒜 i)] (p : Γ.Correlated) :
    Correlated.ofStdSimplex p.toStdSimplex = p := by
  obtain ⟨w, hn, hs, h1⟩ := p
  simp only [Correlated.ofStdSimplex, Correlated.toStdSimplex, Correlated.mk.injEq]
  funext a
  split_ifs with h
  · rfl
  · exact (hs a fun ha => h (Γ.mem_profilesFinset.2 ha)).symm

lemma Correlated.toStdSimplex_ofStdSimplex [DecidableEq (∀ i, 𝒜 i)]
    (f : stdSimplex ℝ Γ.profilesFinset) : (Correlated.ofStdSimplex f).toStdSimplex = f := by
  apply Subtype.ext
  funext a
  exact dif_pos a.2

lemma Correlated.toStdSimplex_injective : Function.Injective (Correlated.toStdSimplex (Γ := Γ)) := by
  classical
  intro p q h
  rw [← Correlated.ofStdSimplex_toStdSimplex p, ← Correlated.ofStdSimplex_toStdSimplex q, h]

variable (Γ)

lemma convex_feasible : Convex ℝ Γ.feasible := by
  rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩ θ η hθ hη hθη
  refine ⟨p.mix q hθ (by linarith), ?_⟩
  rw [Correlated.mix_payoff]
  congr 1
  rw [show 1 - θ = η by linarith]

/-- **`C(Γ)` is the convex hull of `u(A)`** (extraction l. 1292–1294). -/
lemma feasible_eq_convexHull : Γ.feasible = convexHull ℝ (Γ.u '' Γ.profiles) := by
  classical
  apply Subset.antisymm
  · rintro _ ⟨p, rfl⟩
    have h := Finset.centerMass_mem_convexHull (R := ℝ) Γ.profilesFinset (w := p.weight)
      (fun a _ => p.nonneg a) (by rw [p.sum_eq_one]; exact one_pos)
      (z := Γ.u) (s := Γ.u '' Γ.profiles) fun a ha => ⟨a, Γ.mem_profilesFinset.1 ha, rfl⟩
    rwa [Finset.centerMass_eq_of_sum_1 _ _ p.sum_eq_one] at h
  · refine convexHull_min ?_ Γ.convex_feasible
    rintro _ ⟨a, ha, rfl⟩
    exact Γ.u_mem_feasible ha

/-- `C(Γ)` is closed (the convex hull of a finite set). -/
lemma isClosed_feasible (Γ : Game N 𝒜) : IsClosed Γ.feasible := by
  rw [feasible_eq_convexHull]
  exact ((Set.Finite.ofFinset Γ.profilesFinset fun _ => Γ.mem_profilesFinset).image Γ.u).isCompact_convexHull (𝕜 := ℝ) |>.isClosed

/-- `C(Γ)` is compact. -/
lemma isCompact_feasible (Γ : Game N 𝒜) : IsCompact Γ.feasible := by
  rw [feasible_eq_convexHull]
  exact ((Set.Finite.ofFinset Γ.profilesFinset fun _ => Γ.mem_profilesFinset).image Γ.u).isCompact_convexHull (𝕜 := ℝ)

/-- The value of the paper's linear program at a correlated strategy `p` and target `y`
(extraction l. 1366–1381): `∑ᵢ (uᵢ(p) − yᵢ)`. -/
noncomputable def lpObjective (y : N → ℝ) (p : Γ.Correlated) : ℝ :=
  ∑ i, (p.payoff i - y i)

/-- **Lemma 11**, mathematical content: `y` is Pareto-optimal in `C(Γ)` iff the paper's
linear program — maximise `∑ᵢ (uᵢ(p) − yᵢ)` over correlated strategies `p` with
`u(p) ≥ y` — has optimum `0`, i.e. every feasible `p` has objective `0`.  The paper states
it for an arbitrary payoff vector `y ∈ ℝⁿ` (extraction l. 1360–1362), and so does this: no
membership hypothesis is needed or imposed.  Above `C(Γ)` both sides are vacuously true and
below it both are false.  The clause "it can be decided by linear programming and thus in
polynomial time" is not rendered (`dd:complexity`, RULING 6).

Paper node: `Lemma 11` -/
theorem paretoOptimalIn_feasible_iff (y : N → ℝ) :
    Game.ParetoOptimalIn y Γ.feasible ↔
      ∀ p : Γ.Correlated, y ≤ p.payoff → Γ.lpObjective y p = 0 := by
  unfold Game.ParetoOptimalIn
  constructor
  · intro hopt p hp
    unfold lpObjective
    by_contra hne
    have hpos : 0 < ∑ i, (p.payoff i - y i) :=
      lt_of_le_of_ne (Finset.sum_nonneg fun i _ => sub_nonneg.2 (hp i)) (Ne.symm hne)
    rw [Finset.sum_sub_distrib, sub_pos] at hpos
    obtain ⟨i, -, hi⟩ := Finset.exists_lt_of_sum_lt hpos
    exact hopt ⟨p.payoff, ⟨p, rfl⟩, Pi.lt_def.2 ⟨hp, i, hi⟩⟩
  · intro hlp
    rintro ⟨y', ⟨p, rfl⟩, hlt⟩
    obtain ⟨hle, hne⟩ := lt_iff_le_and_ne.1 hlt
    have h0 := hlp p hle
    unfold lpObjective at h0
    have hall : ∀ i, p.payoff i - y i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sub_nonneg.2 (hle i)).1 h0 |> fun h i => h i (Finset.mem_univ i)
    exact hne (funext fun i => (sub_eq_zero.1 (hall i)).symm)

end Game

/-! ### Token games and Definition 6 -/

/-- A **perfect-coordination token game** for `Γ` (extraction l. 1295–1315): a game on
fresh token actions for the representatives, and the original players' assignment `uᵉ` of a
feasible payoff vector of `Γ` to every token outcome. -/
structure TokenGame [Fintype N] [DecidableEq N] (Γ : Game N 𝒜) where
  /-- `(Aˢ, uˢ)`, the game the representatives play. -/
  game : Game N 𝒜
  /-- Tokens are fresh: `Aˢᵢ ∩ Aᵢ = ∅`. -/
  fresh : ∀ i, Disjoint (game.S i) (Γ.S i)
  /-- `uᵉ`, total on universe profiles like every payoff function (`dd:total-utility`). -/
  ue : (∀ i, 𝒜 i) → N → ℝ
  /-- `uᵉ : Aˢ → C(Γ)`. -/
  ue_mem : ∀ a ∈ game.profiles, ue a ∈ Γ.feasible

namespace TokenGame

variable [Fintype N] [DecidableEq N] {Γ : Game N 𝒜} (T : TokenGame Γ) (X : Play N 𝒜 Ω) (L : Filter Ω)

/-- **Definition 6**: `T` is a perfect-coordination SPI for `Γ` if
`uᵉ(Π(Aˢ, uˢ)) ≥ u(Π(Γ))` with certainty.

Paper node: `Definition 6` -/
def IsSPI : Prop := ∀ᶠ ω in L, Γ.u (X.play Γ ω) ≤ T.ue (X.play T.game ω)

/-- **Definition 6**, strict clause: additionally some player gains with positive
probability.

Paper node: `Definition 6` -/
def IsStrictSPI : Prop :=
  T.IsSPI X L ∧ ∃ i, ∃ᶠ ω in L, Γ.u (X.play Γ ω) i < T.ue (X.play T.game ω) i

end TokenGame

/-! ### Room and the token copy -/

namespace Game

variable (Γ : Game N 𝒜)

/-- **Room for tokens outside `B`** (`dd:room`): each player's universe carries an
injective copy of her action set that avoids `B i`.  The paper assumes fresh tokens exist;
over a fixed universe this is a hypothesis, and the set to avoid must be given separately
from the game being copied — every §5 construction tokenizes `Γ.reduce` (or a subset game)
and hands the result back as a `TokenGame Γ`, whose `fresh` field demands disjointness from
`Γ.S i`, not merely from `Γ.reduce.S i` (R4-F01). -/
def HasRoomOutside (B : ∀ i, Finset (𝒜 i)) : Prop :=
  ∀ i, ∃ t : 𝒜 i → 𝒜 i, InjOn t (Γ.S i) ∧ ∀ a ∈ Γ.S i, t a ∉ B i

/-- **Room for tokens** (`dd:room`): the special case of `Game.HasRoomOutside` in which the
avoided set is the game's own action set — enough exactly when the token copy is handed
back as a token game for `Γ` itself. -/
def HasRoom : Prop := Γ.HasRoomOutside Γ.S

lemma hasRoom_iff : Γ.HasRoom ↔ Γ.HasRoomOutside Γ.S := Iff.rfl

variable {B : ∀ i, Finset (𝒜 i)}

/-- A chosen family of token maps. -/
noncomputable def tokenMap (h : Γ.HasRoomOutside B) (i : N) : 𝒜 i → 𝒜 i := (h i).choose

lemma tokenMap_injOn (h : Γ.HasRoomOutside B) (i : N) : InjOn (Γ.tokenMap h i) (Γ.S i) :=
  (h i).choose_spec.1

lemma tokenMap_not_mem (h : Γ.HasRoomOutside B) (i : N) {a : 𝒜 i} (ha : a ∈ Γ.S i) :
    Γ.tokenMap h i a ∉ B i := (h i).choose_spec.2 a ha

/-- The inverse token map on the token set.  Off the tokens it is `Function.invFunOn`'s junk
value, which nothing reads: `tokenCopy.S` is exactly the image, so `untoken` inverts
correctly at every profile (`untoken_tokenMap`), and every consumer of a game's payoffs
(`profiles`, `Correlated`, `feasible`, dominance, `Play.mem`) only evaluates `u` on
profiles. -/
noncomputable def untoken (h : Γ.HasRoomOutside B) (i : N) : 𝒜 i → 𝒜 i :=
  haveI : Nonempty (𝒜 i) := Γ.nonempty_universe i
  Function.invFunOn (Γ.tokenMap h i) (Γ.S i)

variable [∀ i, DecidableEq (𝒜 i)]

/-- **The token copy of `Γ`** (the `(Â, û)` of Lemma 13): the same game on fresh tokens. -/
noncomputable def tokenCopy (h : Γ.HasRoomOutside B) : Game N 𝒜 where
  S i := (Γ.S i).image (Γ.tokenMap h i)
  nonempty i := (Γ.nonempty i).image _
  u b i := Γ.u (fun j => Γ.untoken h j (b j)) i

variable (h : Γ.HasRoomOutside B)

omit [∀ i, DecidableEq (𝒜 i)] in
lemma untoken_tokenMap (i : N) {a : 𝒜 i} (ha : a ∈ Γ.S i) :
    Γ.untoken h i (Γ.tokenMap h i a) = a :=
  haveI : Nonempty (𝒜 i) := Γ.nonempty_universe i
  (Γ.tokenMap_injOn h i).leftInvOn_invFunOn ha

/-- The token copy is fresh for the avoided set `B`. -/
lemma tokenCopy_fresh (i : N) : Disjoint ((Γ.tokenCopy h).S i) (B i) := by
  rw [Finset.disjoint_left]
  intro b hb
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hb
  exact Γ.tokenMap_not_mem h i ha

/-- The natural isomorphism `Γ ≅ tokenCopy Γ`, `a ↦ â`. -/
noncomputable def tokenIso : GameIso Γ (Γ.tokenCopy h) where
  toFun := Γ.tokenMap h
  bijOn i := by
    refine ⟨fun a ha => Finset.mem_coe.2 (Finset.mem_image_of_mem _ ha), Γ.tokenMap_injOn h i, ?_⟩
    intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hb)
    exact ⟨a, ha, rfl⟩
  scale _ := 1
  scale_pos _ := one_pos
  shift _ := 0
  affine a ha i := by
    simp only [tokenCopy, one_mul, add_zero]
    congr 1
    funext j
    rw [Γ.untoken_tokenMap h j (ha j)]

lemma tokenCopy_u_map (a : ∀ i, 𝒜 i) (ha : a ∈ Γ.profiles) :
    (Γ.tokenCopy h).u ((Γ.tokenIso h).map a) = Γ.u a := by
  funext i
  have := (Γ.tokenIso h).affine a ha i
  simp only [tokenIso, one_mul, add_zero] at this
  exact this.symm

end Game

/-! ### An infinite universe has room for anything

The uniform source of room: over `𝒜 i` infinite, *every* finite set can be avoided.  This
is what a §5 construction needing several mutually disjoint copies uses — take the copies
in turn, each avoiding the union of the previous ones — and what the §5 example universes
`X ⊕ ℕ` supply for free. -/

namespace Game

variable (Γ : Game N 𝒜)

lemma hasRoomOutside_of_infinite [∀ i, Infinite (𝒜 i)] (B : ∀ i, Finset (𝒜 i)) :
    Γ.HasRoomOutside B := by
  classical
  intro i
  haveI : Infinite ((↑(B i) : Set (𝒜 i))ᶜ : Set (𝒜 i)) :=
    ((B i).finite_toSet.infinite_compl).to_subtype
  set e : ℕ ↪ ((↑(B i) : Set (𝒜 i))ᶜ : Set (𝒜 i)) := Infinite.natEmbedding _ with he
  set g : {x : 𝒜 i // x ∈ Γ.S i} → 𝒜 i :=
    fun x => (e ((Fintype.equivFin {x : 𝒜 i // x ∈ Γ.S i}) x : ℕ) : 𝒜 i) with hg
  refine ⟨fun a => if ha : a ∈ Γ.S i then g ⟨a, ha⟩ else a, ?_, ?_⟩
  · intro a ha b hb hab
    simp only [dif_pos (Finset.mem_coe.1 ha), dif_pos (Finset.mem_coe.1 hb), hg] at hab
    have h1 := e.injective (Subtype.ext hab)
    have h2 := Fin.val_injective h1
    simpa using (Fintype.equivFin {x : 𝒜 i // x ∈ Γ.S i}).injective h2
  · intro a ha
    simp only [dif_pos ha, hg]
    exact (e _).2

end Game

end SafeParetoImprovements
