import SafeParetoImprovements.Coordination
import SafeParetoImprovements.Derivation
import SafeParetoImprovements.Representatives

/-!
# Finding perfect-coordination SPIs (§5.2): Definition 7, Algorithm 1, Proposition 12

Under Assumptions 1 and 2, the original players can *reassign* the outcomes of the base
game: hand the representatives a fresh exact copy of the game and assign to each token
outcome any feasible payoff vector they like.  This file builds that
reassignment once (`TokenGame.reassign`, `Play.exists_tokenGame_ue_eq`) and uses it for
Proposition 12; Lemma 13 and Corollary 14 (`Characterization.lean`) reuse it.

## Rulings in force

* **RULING 10** — Definition 7 and Proposition 12 are stated *per play family*: the token
  game is built after Assumption 2's isomorphism between `reduce Γ` and its token copy is
  known, and `uᵉ` is defined along that isomorphism (erratum D6).  The paper's Algorithm 1
  takes `supp Π(Γ)` as data, which is the same dependence.
* **RULING 11** — Assumption 1 is hypothesised alongside Assumption 2: Assumption 2 speaks
  only about fully reduced games, and Assumption 1 is what makes `Π(Γ)` the play of
  `reduce Γ`.  The paper writes "under Assumption 2" and works under both throughout.
* **RULING 7** — Definition 7 reads "strict" into its body (erratum D10).
* **`dd:room`** — the token copy needs room outside the base game's action sets
  (`Γ.HasRoom`, i.e. `Γ.HasRoomOutside Γ.S`); the direction of Proposition 12 that
  constructs a token game carries that hypothesis, the direction that reads one off does
  not.
* **`dd:complexity`** — Proposition 12's "in polynomial time" clause is not rendered; the
  node's content is Algorithm 1's correctness as an iff, whose right-hand side is the test
  Algorithm 1 performs (a supported outcome that is Pareto-suboptimal in `C(Γ)`).
-/

universe u v w

namespace SafeParetoImprovements

open Filter Set MeasureTheory

variable {N : Type u} {𝒜 : N → Type v} {Ω : Type w}
variable [Fintype N] [DecidableEq N] [∀ i, DecidableEq (𝒜 i)]

/-! ### Definition 7 -/

namespace Play

variable (X : Play N 𝒜 Ω) (L : Filter Ω)

omit [∀ i, DecidableEq (𝒜 i)] in
/-- **Definition 7** (RULING 7: "strict" read into the body, erratum D10; RULING 10: per
play family): the strict perfect-coordination SPI decision problem asks, for a given game
`Γ`, whether there is a strict perfect-coordination SPI for `Γ`.  The paper prints the
problem's name as "strict full-coordination" and asks the question "under Assumption 2";
the predicate is stated for an arbitrary play family and filter, and Assumption 2 (with
Assumption 1 and room) enters as the hypotheses of Proposition 12
(`Representatives.strictPerfectCoordinationSPIDecision_iff`), which is where the paper
uses it.

Paper node: `Definition 7` -/
def StrictPerfectCoordinationSPIDecision (Γ : Game N 𝒜) : Prop :=
  ∃ T : TokenGame Γ, T.IsStrictSPI X L

end Play

/-! ### Exact copies

Lemma 13 prints `û(â) = u(a)`: the token game it produces is not merely *isomorphic* to the
reduced game, it is a relabelling that keeps the payoffs on the nose.  `Game.ExactCopy` is
that stronger relation — an isomorphism with scale `1` and shift `0` — and it is what the
§5.2/§5.3 constructions actually deliver, since they hand back `Game.tokenCopy` along
`Game.tokenIso`. -/

namespace Game

/-- `Γ'` is an **exact copy** of `Γ`: some game isomorphism `Γ ≅ Γ'` has scale `1` and
shift `0`, so `u'(Φ(a)) = u(a)` at every outcome of `Γ` — the paper's `û(â) = u(a)`. -/
def ExactCopy (Γ Γ' : Game N 𝒜) : Prop :=
  ∃ φ : GameIso Γ Γ', (∀ i, φ.scale i = 1) ∧ ∀ i, φ.shift i = 0

omit [Fintype N] [DecidableEq N] [∀ i, DecidableEq (𝒜 i)] in
lemma ExactCopy.isomorphic {Γ Γ' : Game N 𝒜} (h : Γ.ExactCopy Γ') : Γ.Isomorphic Γ' :=
  ⟨h.choose⟩

omit [Fintype N] [DecidableEq N] [∀ i, DecidableEq (𝒜 i)] in
/-- The payoffs of an exact copy at the relabelled outcome are the original payoffs. -/
lemma ExactCopy.u_map {Γ Γ' : Game N 𝒜} {φ : GameIso Γ Γ'} (hs : ∀ i, φ.scale i = 1)
    (hc : ∀ i, φ.shift i = 0) {a : ∀ i, 𝒜 i} (ha : a ∈ Γ.profiles) : Γ'.u (φ.map a) = Γ.u a := by
  funext i
  have := φ.affine a ha i
  rw [hs i, hc i, one_mul, add_zero] at this
  exact this.symm

omit [Fintype N] [DecidableEq N] in
/-- The token copy is an exact copy: `Game.tokenIso` has scale `1` and shift `0`. -/
lemma exactCopy_tokenCopy (Γ : Game N 𝒜) {B : ∀ i, Finset (𝒜 i)} (h : Γ.HasRoomOutside B) :
    Γ.ExactCopy (Γ.tokenCopy h) :=
  ⟨Γ.tokenIso h, fun _ => rfl, fun _ => rfl⟩

end Game

/-! ### The reassignment construction -/

namespace TokenGame

variable (Γ : Game N 𝒜)

open Classical in
/-- **Reassignment**: a token copy of `Γ` — the paper's `(Â, û)`, every original action and
payoff relabelled onto fresh tokens — played, after its own reduction, through the
isomorphism `ψ : reduce Γ ≅ reduce Â` that Assumption 2 supplies, with `uᵉ := f ∘ ψ⁻¹` on the
reduced token outcomes for a feasible-valued reassignment `f` of the reduced outcomes of `Γ`
(erratum D6, RULING 10).  On the token outcomes eliminated by reduction, which are never
played under Assumption 1, `uᵉ` is the relabelled original payoff `û`. -/
noncomputable def reassign (h : Γ.HasRoom)
    (ψ : GameIso Γ.reduce (Γ.tokenCopy h).reduce)
    (f : (∀ i, 𝒜 i) → N → ℝ) (hf : ∀ a ∈ Γ.reduce.profiles, f a ∈ Γ.feasible) :
    TokenGame Γ where
  game := Γ.tokenCopy h
  fresh i := Γ.tokenCopy_fresh h i
  ue b := if b ∈ (Γ.tokenCopy h).reduce.profiles then f (ψ.symm.map b) else (Γ.tokenCopy h).u b
  ue_mem b hb := by
    split_ifs with hb'
    · exact hf _ (ψ.symm.map_mem hb')
    · refine Γ.u_mem_feasible fun j => ?_
      obtain ⟨a, ha, hab⟩ := Finset.mem_image.1 (hb j)
      show Γ.untoken h j (b j) ∈ Γ.S j
      rw [← hab, Γ.untoken_tokenMap h j ha]
      exact ha

end TokenGame

namespace Play

variable {X : Play N 𝒜 Ω} {L : Filter Ω}

/-- **Reassignment realizes any feasible-valued function of the play**: under Assumptions
1 and 2, with room, for every `f` sending reduced outcomes into `C(Γ)` there is a token
game — an *exact* copy of `Γ` in the sense of `Game.ExactCopy`, the paper's `û(â) = u(a)` —
whose original-player payoff at the representatives' token play is `f` at the
representatives' play of `Γ`, with certainty.  The token game is `TokenGame.reassign`: the
copy `Game.tokenCopy` along `Game.tokenIso` (a relabelling, so scale `1` and shift `0`); by
Assumption 1 the representatives play the copy as they play its reduction,
which is the relabelled `reduce Γ` (`GameIso.reduce_eq_imageGame`), and by Assumption 2 they
play that isomorphically to `reduce Γ` along the isomorphism `uᵉ` is defined with. -/
lemma exists_tokenGame_ue_eq (hA1 : X.SatisfiesA1 L) (hA2 : X.SatisfiesA2 L) (Γ : Game N 𝒜)
    (h : Γ.HasRoom) (f : (∀ i, 𝒜 i) → N → ℝ)
    (hf : ∀ a ∈ Γ.reduce.profiles, f a ∈ Γ.feasible) :
    ∃ T : TokenGame Γ, Γ.ExactCopy T.game ∧
      ∀ᶠ ω in L, T.ue (X.play T.game ω) = f (X.play Γ ω) := by
  obtain ⟨ψ, hψ⟩ := hA2 Γ.reduce (Γ.tokenCopy h).reduce Γ.reduce_reduced
    (Γ.tokenCopy h).reduce_reduced ⟨(Γ.tokenIso h).restrictReduce⟩
  refine ⟨TokenGame.reassign Γ h ψ f hf, Γ.exactCopy_tokenCopy h, ?_⟩
  filter_upwards [hψ, hA1.play_reduce Γ, hA1.play_reduce (Γ.tokenCopy h)] with ω hω hred hredC
  obtain ⟨hmem, hmap⟩ := (ψ.mem_rel _ _).1 hω
  classical
  show (if X.play (Γ.tokenCopy h) ω ∈ (Γ.tokenCopy h).reduce.profiles
      then f (ψ.symm.map (X.play (Γ.tokenCopy h) ω)) else (Γ.tokenCopy h).u (X.play (Γ.tokenCopy h) ω)) =
    f (X.play Γ ω)
  rw [← hredC, hmap, if_pos (ψ.map_mem hmem), ψ.symm_map_map hmem, hred]

end Play

/-! ### Proposition 12 -/

namespace Representatives

variable (R : Representatives.{u, v, w} N 𝒜)

omit [DecidableEq N] [∀ i, DecidableEq (𝒜 i)] in
/-- A positive-probability event meets some supported outcome of `Π(Γ)`. -/
lemma exists_mem_support_of_frequently (Γ : Game N 𝒜) {P : R.Ω → Prop}
    (hP : ∃ᶠ ω in R.certainty, P ω) :
    ∃ a ∈ R.support Γ, ∃ ω, R.play Γ ω = a ∧ P ω := by
  classical
  by_contra hcon
  push Not at hcon
  rw [frequently_certainty_iff] at hP
  apply hP
  have hcover : {ω | P ω} ⊆ ⋃ a ∈ Γ.profilesFinset, {ω | R.play Γ ω = a ∧ P ω} := by
    intro ω hω
    simp only [mem_iUnion, mem_setOf_eq, exists_prop]
    exact ⟨R.play Γ ω, Γ.mem_profilesFinset.2 (R.toPlay.mem Γ ω), rfl, hω⟩
  refine measure_mono_null hcover ((measure_biUnion_null_iff Γ.profilesFinset.countable_toSet).2
    fun a _ => ?_)
  by_cases ha : a ∈ R.support Γ
  · have : {ω | R.play Γ ω = a ∧ P ω} = ∅ := by
      ext ω
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
      exact fun h₁ h₂ => hcon a ha ω h₁ h₂
    rw [this]; exact measure_empty
  · exact measure_mono_null (fun ω hω => hω.1) (not_not.1 ha)

omit [∀ i, DecidableEq (𝒜 i)] in
/-- **Proposition 12, the "only if" direction** (Algorithm 1 is complete): a strict
perfect-coordination SPI exhibits a supported outcome of `Π(Γ)` that is Pareto-suboptimal
in `C(Γ)`.  No assumption on the representatives is needed. -/
lemma exists_support_not_paretoOptimal_of_strictSPI (Γ : Game N 𝒜) {T : TokenGame Γ}
    (hT : T.IsStrictSPI R.toPlay R.certainty) :
    ∃ a ∈ R.support Γ, ¬ Game.ParetoOptimalIn (Γ.u a) Γ.feasible := by
  obtain ⟨hspi, i, hstrict⟩ := hT
  obtain ⟨a, ha, ω, hω, hlt, hle⟩ :=
    R.exists_mem_support_of_frequently Γ (hstrict.and_eventually hspi)
  refine ⟨a, ha, fun hopt => hopt ⟨T.ue (R.play T.game ω),
    T.ue_mem _ (R.toPlay.mem T.game ω), ?_⟩⟩
  rw [← hω]
  exact Pi.lt_def.2 ⟨hle, i, hlt⟩

/-- **Proposition 12, the "if" direction** (Algorithm 1 is sound): under Assumptions 1
and 2, with room for tokens, a supported outcome that is Pareto-suboptimal in `C(Γ)` yields
a strict perfect-coordination SPI — the reassignment that replaces that outcome by a
feasible vector Pareto-dominating it and keeps every other outcome. -/
lemma exists_strictSPI_of_support_not_paretoOptimal (Γ : Game N 𝒜)
    (hA1 : R.toPlay.SatisfiesA1 R.certainty) (hA2 : R.toPlay.SatisfiesA2 R.certainty)
    (h : Γ.HasRoom) {a₀ : ∀ i, 𝒜 i} (ha₀ : a₀ ∈ R.support Γ)
    (hopt : ¬ Game.ParetoOptimalIn (Γ.u a₀) Γ.feasible) :
    ∃ T : TokenGame Γ, T.IsStrictSPI R.toPlay R.certainty := by
  classical
  unfold Game.ParetoOptimalIn at hopt
  push Not at hopt
  obtain ⟨y, hy, hlt⟩ := hopt
  obtain ⟨hle, i, hi⟩ := Pi.lt_def.1 hlt
  set f : (∀ i, 𝒜 i) → N → ℝ := fun a => if a = a₀ then y else Γ.u a with hfdef
  have hf : ∀ a ∈ Γ.reduce.profiles, f a ∈ Γ.feasible := by
    intro a ha
    by_cases hab : a = a₀
    · simp [hfdef, hab, hy]
    · simp only [hfdef, if_neg hab]
      exact Γ.u_mem_feasible (Γ.reduce_isSubsetGameOf.profiles_subset ha)
  obtain ⟨T, -, hT⟩ := Play.exists_tokenGame_ue_eq hA1 hA2 Γ h f hf
  have hge : ∀ a, Γ.u a ≤ f a := by
    intro a
    by_cases hab : a = a₀
    · subst hab; simp [hfdef, hle]
    · simp [hfdef, hab]
  refine ⟨T, ?_, i, ?_⟩
  · filter_upwards [hT] with ω hω
    rw [hω]; exact hge _
  · have hfreq : ∃ᶠ ω in R.certainty, R.play Γ ω = a₀ := (R.frequently_certainty_iff _).2 ha₀
    refine (hfreq.and_eventually hT).mono fun ω ⟨hωa, hωT⟩ => ?_
    have hωa' : R.toPlay.play Γ ω = a₀ := hωa
    rw [hωT, hωa']
    simpa [hfdef] using hi

/-- **Proposition 12** (Algorithm 1's correctness; RULINGS 10, 11; `dd:complexity`): under
Assumptions 1 and 2, with room for tokens, there is a strict perfect-coordination SPI for
`Γ` iff some outcome in the support of `Π(Γ)` is Pareto-suboptimal in `C(Γ)` — which is
what Algorithm 1 tests, one supported outcome at a time, by the linear program of Lemma 11.
The clause "it can be decided in polynomial time" is not rendered.  The "only if" direction
needs neither assumption nor room (`exists_support_not_paretoOptimal_of_strictSPI`).

Paper node: `Proposition 12` -/
theorem strictPerfectCoordinationSPIDecision_iff (Γ : Game N 𝒜)
    (hA1 : R.toPlay.SatisfiesA1 R.certainty) (hA2 : R.toPlay.SatisfiesA2 R.certainty)
    (h : Γ.HasRoom) :
    R.toPlay.StrictPerfectCoordinationSPIDecision R.certainty Γ ↔
      ∃ a ∈ R.support Γ, ¬ Game.ParetoOptimalIn (Γ.u a) Γ.feasible :=
  ⟨fun ⟨_, hT⟩ => R.exists_support_not_paretoOptimal_of_strictSPI Γ hT,
   fun ⟨_, ha, hopt⟩ => R.exists_strictSPI_of_support_not_paretoOptimal Γ hA1 hA2 h ha hopt⟩

end Representatives

end SafeParetoImprovements
