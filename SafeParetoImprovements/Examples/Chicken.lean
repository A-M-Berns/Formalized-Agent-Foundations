import SafeParetoImprovements.Coordination
import SafeParetoImprovements.Book
import SafeParetoImprovements.Examples.TwoPlayer
import SafeParetoImprovements.Examples.Coin

/-!
# Table 7 and Proposition 16: a Pareto improvement that is not safely achievable

The game of Table 7 (extraction l. 1631–1636) reduces by strict dominance to a
Chicken-like `2 × 2` game with the two pure equilibria `(a, b)` and `(b, a)`, worth `(4, 0)`
and `(0, 4)`.  Representatives that play those two outcomes with probability ½ each (a
fair coin through `Book.prescribedRandom`, so Assumptions 1 and 2 hold) earn `(2, 2)` in
expectation, and the outcome `(c, c)` is worth `(3, 3)` to both — a Pareto improvement.  Yet
no perfect-coordination SPI reaches `(3, 3)` in expectation: on each of the two sample
points the token outcome must be worth at least `(4, 0)`, respectively `(0, 4)`, and those
two payoff vectors are Pareto-optimal in `C(Γ)` (every feasible vector satisfies
`100 y₁ + 6 y₂ ≤ 400` and `6 y₁ + 100 y₂ ≤ 400`), so the players' total expected payoff is
at most `4 < 6`.  This is **Proposition 16**, with the paper's own witness (`p = ½`).
-/

namespace SafeParetoImprovements

namespace Examples

open Filter MeasureTheory Two
open scoped ENNReal

/-- The three actions of Table 7. -/
inductive CAct | a | b | c
  deriving DecidableEq, Fintype, Inhabited

/-- Both players choose from `CAct`. -/
abbrev CUniverse : Two → Type := fun _ => CAct

/-- Table 7's payoffs, `chickenPayoff a₁ a₂ i`. -/
def chickenPayoff : CAct → CAct → Two → ℝ
  | .a, .a, _ => -5
  | .a, .b, .one => 4
  | .a, .b, .two => 0
  | .a, .c, .one => 10
  | .a, .c, .two => -100
  | .b, .a, .one => 0
  | .b, .a, .two => 4
  | .b, .b, _ => 1
  | .b, .c, .one => 10
  | .b, .c, .two => -100
  | .c, .a, .one => -100
  | .c, .a, .two => 10
  | .c, .b, .one => -100
  | .c, .b, .two => 10
  | .c, .c, _ => 3

/-- The game of Table 7. -/
def chicken : Game Two CUniverse where
  S _ := Finset.univ
  nonempty _ := ⟨.a, Finset.mem_univ _⟩
  u x i := chickenPayoff (x .one) (x .two) i

namespace chicken

lemma u_apply (x : ∀ i, CUniverse i) (i : Two) :
    chicken.u x i = chickenPayoff (x .one) (x .two) i := rfl

lemma mem_profiles (x : ∀ i, CUniverse i) : x ∈ chicken.profiles := fun _ => Finset.mem_univ _

/-! ### The reduction: `c` is strictly dominated by `a` for both players -/

lemma dom1 : chicken.IsStrictlyDominated .one .c :=
  ⟨.a, (strictlyDominates_one_iff _ _ _).2 ⟨Finset.mem_univ _, Finset.mem_univ _,
    fun x _ => by cases x <;> norm_num [u_apply, chickenPayoff]⟩⟩

/-- After removing player 1's `c`. -/
def g1 : Game Two CUniverse := chicken.erase .one .c dom1.erase_nonempty

lemma g1_u : g1.u = chicken.u := rfl

lemma g1_S_one : g1.S .one = {CAct.a, CAct.b} := by
  show Finset.univ.erase CAct.c = _
  decide

lemma g1_S_two : g1.S .two = Finset.univ := by
  show (chicken.erase .one .c dom1.erase_nonempty).S .two = _
  rw [Game.erase_S_of_ne _ _ _ _ (by decide)]
  rfl

lemma dom2 : g1.IsStrictlyDominated .two .c :=
  ⟨.a, (strictlyDominates_two_iff _ _ _).2 ⟨by rw [g1_S_two]; exact Finset.mem_univ _,
    by rw [g1_S_two]; exact Finset.mem_univ _,
    fun x hx => by
      rw [g1_S_one] at hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> norm_num [g1_u, u_apply, chickenPayoff]⟩⟩

/-- The reduced game: the Chicken-like `{a, b}²`. -/
def reducedChicken : Game Two CUniverse := g1.erase .two .c dom2.erase_nonempty

lemma reducedChicken_u : reducedChicken.u = chicken.u := rfl

lemma reducedChicken_S (i : Two) : reducedChicken.S i = {CAct.a, CAct.b} := by
  cases i
  · show (g1.erase .two .c dom2.erase_nonempty).S .one = _
    rw [Game.erase_S_of_ne _ _ _ _ (by decide), g1_S_one]
  · show (g1.S .two).erase CAct.c = _
    rw [g1_S_two]; decide

lemma reducedChicken_mem_S {i : Two} {x : CAct} :
    x ∈ reducedChicken.S i ↔ x = .a ∨ x = .b := by
  rw [reducedChicken_S]; simp

lemma reducedChicken_reduced : reducedChicken.Reduced := by
  rw [reduced_iff]
  constructor
  · rintro x ⟨x', h⟩
    rw [strictlyDominates_one_iff] at h
    obtain ⟨hx', hx, hlt⟩ := h
    rw [reducedChicken_mem_S] at hx hx'
    rcases hx with rfl | rfl <;> rcases hx' with rfl | rfl
    · exact lt_irrefl _ (hlt .a (reducedChicken_mem_S.2 (Or.inl rfl)))
    · have := hlt .b (reducedChicken_mem_S.2 (Or.inr rfl))
      norm_num [reducedChicken_u, u_apply, chickenPayoff] at this
    · have := hlt .a (reducedChicken_mem_S.2 (Or.inl rfl))
      norm_num [reducedChicken_u, u_apply, chickenPayoff] at this
    · exact lt_irrefl _ (hlt .a (reducedChicken_mem_S.2 (Or.inl rfl)))
  · rintro x ⟨x', h⟩
    rw [strictlyDominates_two_iff] at h
    obtain ⟨hx', hx, hlt⟩ := h
    rw [reducedChicken_mem_S] at hx hx'
    rcases hx with rfl | rfl <;> rcases hx' with rfl | rfl
    · exact lt_irrefl _ (hlt .a (reducedChicken_mem_S.2 (Or.inl rfl)))
    · have := hlt .b (reducedChicken_mem_S.2 (Or.inr rfl))
      norm_num [reducedChicken_u, u_apply, chickenPayoff] at this
    · have := hlt .a (reducedChicken_mem_S.2 (Or.inl rfl))
      norm_num [reducedChicken_u, u_apply, chickenPayoff] at this
    · exact lt_irrefl _ (hlt .a (reducedChicken_mem_S.2 (Or.inl rfl)))

/-- The full reduction of Table 7 is the Chicken-like game. -/
lemma reduce_eq : chicken.reduce = reducedChicken := by
  have e1 : chicken.ElimStar g1 := Relation.ReflTransGen.single ⟨.one, .c, dom1, rfl⟩
  have e2 : chicken.ElimStar reducedChicken := Relation.ReflTransGen.tail e1 ⟨.two, .c, dom2, rfl⟩
  exact Game.reduce_eq_of_reduced_of_elimStar e2 reducedChicken_reduced

/-! ### Two supporting half-planes of `C(Γ)` -/

/-- Every feasible payoff vector satisfies `100 y₁ + 6 y₂ ≤ 400`; hence `(4, 0)` is
Pareto-optimal in `C(Γ)`. -/
lemma feasible_le₁ {y : Two → ℝ} (hy : y ∈ chicken.feasible) : 100 * y .one + 6 * y .two ≤ 400 := by
  rw [Game.feasible_eq_convexHull] at hy
  have hconv : Convex ℝ {y : Two → ℝ | 100 * y .one + 6 * y .two ≤ 400} := by
    intro p hp q hq θ η hθ hη hθη
    simp only [Set.mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hp hq ⊢
    nlinarith
  refine convexHull_min ?_ hconv hy
  rintro _ ⟨x, -, rfl⟩
  simp only [Set.mem_setOf_eq, u_apply]
  rcases x .one with _ | _ | _ <;> rcases x .two with _ | _ | _ <;> norm_num [chickenPayoff]

/-- Every feasible payoff vector satisfies `6 y₁ + 100 y₂ ≤ 400`; hence `(0, 4)` is
Pareto-optimal in `C(Γ)`. -/
lemma feasible_le₂ {y : Two → ℝ} (hy : y ∈ chicken.feasible) : 6 * y .one + 100 * y .two ≤ 400 := by
  rw [Game.feasible_eq_convexHull] at hy
  have hconv : Convex ℝ {y : Two → ℝ | 6 * y .one + 100 * y .two ≤ 400} := by
    intro p hp q hq θ η hθ hη hθη
    simp only [Set.mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hp hq ⊢
    nlinarith
  refine convexHull_min ?_ hconv hy
  rintro _ ⟨x, -, rfl⟩
  simp only [Set.mem_setOf_eq, u_apply]
  rcases x .one with _ | _ | _ <;> rcases x .two with _ | _ | _ <;> norm_num [chickenPayoff]

end chicken

open chicken

/-! ### The representatives: `(a, b)` and `(b, a)` with probability ½ each -/

/-- The two pages: heads plays `(a, b)`, tails `(b, a)`. -/
def chickenPages : Bool → ∀ i, CUniverse i
  | true => pair CAct.a CAct.b
  | false => pair CAct.b CAct.a

lemma chickenPages_mem : ∀ ω, chickenPages ω ∈ reducedChicken.profiles := by
  intro ω i
  cases ω <;> cases i <;> rw [reducedChicken_S] <;> decide

/-- The `ω`-dependent book prescribing `chickenPages` for the class of the reduced game. -/
noncomputable def chickenBook : Book Two CUniverse Bool :=
  Book.prescribedRandom reducedChicken chickenPages_mem

/-- The representatives of Proposition 16: the book on the fair coin. -/
noncomputable def chickenRepresentatives : Representatives.{0, 0, 0} Two CUniverse :=
  chickenBook.toRepresentatives (μ := coin) (fun _ _ => trivial)

lemma chickenRepresentatives_play (ω : Bool) :
    chickenRepresentatives.play chicken ω = chickenPages ω :=
  Book.prescribedRandom_play _ chickenPages_mem chicken chicken.reduce_eq ω

/-- The expected payoff of the default play is `(2, 2)`. -/
lemma chickenRepresentatives_integral (i : Two) :
    ∫ ω, chicken.u (chickenRepresentatives.play chicken ω) i ∂chickenRepresentatives.μ = 2 := by
  simp only [chickenRepresentatives_play]
  show ∫ ω, chicken.u (chickenPages ω) i ∂coin = 2
  rw [integral_coin]
  cases i <;> norm_num [chickenPages, u_apply, chickenPayoff, pair]

/-- **Proposition 16.**  For the game of Table 7 and the representatives playing `(a, b)`
and `(b, a)` with probability ½ each — which satisfy Assumptions 1 and 2 — the outcome
`(c, c)` Pareto-improves on the expected default payoff for both players, yet no
perfect-coordination SPI has expected payoff `u(c, c) = (3, 3)`.

Paper node: `Proposition 16` -/
theorem chicken_no_perfectCoordinationSPI :
    chickenRepresentatives.toPlay.SatisfiesA1 chickenRepresentatives.certainty ∧
    chickenRepresentatives.toPlay.SatisfiesA2 chickenRepresentatives.certainty ∧
    (∀ i, ∫ ω, chicken.u (chickenRepresentatives.play chicken ω) i ∂chickenRepresentatives.μ <
      chicken.u (pair CAct.c CAct.c) i) ∧
    ¬ ∃ T : TokenGame chicken,
      T.IsSPI chickenRepresentatives.toPlay chickenRepresentatives.certainty ∧
      ∀ i, ∫ ω, T.ue (chickenRepresentatives.play T.game ω) i ∂chickenRepresentatives.μ =
        chicken.u (pair CAct.c CAct.c) i := by
  refine ⟨chickenBook.satisfiesA1 _, chickenBook.satisfiesA2 _, fun i => ?_, ?_⟩
  · rw [chickenRepresentatives_integral]
    cases i <;> norm_num [u_apply, chickenPayoff, pair]
  rintro ⟨T, hspi, hE⟩
  -- the SPI inequality holds at both sample points
  have hpt : ∀ ω, chicken.u (chickenPages ω) ≤ T.ue (chickenRepresentatives.play T.game ω) := by
    have h := (ae_coin_iff _).1 hspi
    intro ω
    cases ω
    · simpa [chickenRepresentatives_play] using h.2
    · simpa [chickenRepresentatives_play] using h.1
  -- the token outcomes' values are feasible
  have hfeas : ∀ ω, T.ue (chickenRepresentatives.play T.game ω) ∈ chicken.feasible :=
    fun ω => T.ue_mem _ (chickenRepresentatives.toPlay.mem T.game ω)
  set v : Bool → Two → ℝ := fun ω => T.ue (chickenRepresentatives.play T.game ω) with hv
  -- on heads `v ≥ (4, 0)`, on tails `v ≥ (0, 4)`; with the half-planes, `v₁ + v₂ ≤ 4` on both
  have h₁ : v true .one + v true .two ≤ 4 := by
    have hle := hpt true
    have hf := feasible_le₁ (hfeas true)
    have ha := hle .one; have hb := hle .two
    simp only [chickenPages, u_apply, chickenPayoff, pair] at ha hb
    linarith
  have h₂ : v false .one + v false .two ≤ 4 := by
    have hle := hpt false
    have hf := feasible_le₂ (hfeas false)
    have ha := hle .one; have hb := hle .two
    simp only [chickenPages, u_apply, chickenPayoff, pair] at ha hb
    linarith
  -- but the expectations sum to `6`
  have e₁ := hE .one
  have e₂ := hE .two
  change ∫ ω, v ω .one ∂coin = _ at e₁
  change ∫ ω, v ω .two ∂coin = _ at e₂
  rw [integral_coin] at e₁ e₂
  simp only [u_apply, chickenPayoff, pair] at e₁ e₂
  linarith

end Examples

end SafeParetoImprovements
