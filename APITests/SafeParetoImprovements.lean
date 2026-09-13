import SafeParetoImprovements.API

/-! Client-style smoke tests for the Safe Pareto Improvements API.  These import only
`SafeParetoImprovements.API`, build their own small games, and combine endpoints to prove
facts a downstream project would want — none of them restates a paper node and none uses
the paper's example fixtures. -/

namespace APITests.SafeParetoImprovements

open _root_.SafeParetoImprovements _root_.SafeParetoImprovements.Two
open Filter

/-! ### A client two-player game over `Bool`: a coordination game -/

/-- `(true, true) ↦ (2, 2)`, `(false, false) ↦ (1, 1)`, miscoordination `(0, 0)`. -/
def coordPayoff : Bool → Bool → Two → ℝ
  | true, true, _ => 2
  | false, false, _ => 1
  | _, _, _ => 0

abbrev CUniv : Two → Type := fun _ => Bool

/-- The client's game: both players choose in `Bool`, all actions available. -/
def coord : Game Two CUniv where
  S _ := Finset.univ
  nonempty _ := ⟨true, Finset.mem_univ _⟩
  u x i := coordPayoff (x .one) (x .two) i

lemma coord_u (a b : Bool) (i : Two) : coord.u (pair a b) i = coordPayoff a b i := rfl

/-- No action is strictly dominated: each is the best reply to its copy. -/
lemma coord_reduced : coord.Reduced := by
  rw [reduced_iff]
  refine ⟨fun a => ?_, fun x => ?_⟩
  · refine not_isStrictlyDominated_one_of_bestResponse coord (x := a) (Finset.mem_univ _)
      fun a' _ => ?_
    cases a <;> cases a' <;> simp [coord_u, coordPayoff]
  · refine not_isStrictlyDominated_two_of_bestResponse coord (a := x) (Finset.mem_univ _)
      fun x' _ => ?_
    cases x <;> cases x' <;> simp [coord_u, coordPayoff]

/-- Hence its full reduction is itself. -/
example : coord.reduce = coord := Game.reduce_of_reduced coord_reduced

/-! ### A general client fact from the certificate API

A reduced game whose action sets are whole finite universes has no safe Pareto improvement
in the sense of Definition 5: every certificate is a permutation of the reduced action sets,
so none is non-trivial.  This is *not* a paper node; it is what a client proves by composing
Proposition 23 with the certificate vocabulary. -/
lemma not_spiDecision_of_reduced_univ {N : Type*} {𝒜 : N → Type*} [Fintype N] [DecidableEq N]
    [∀ i, DecidableEq (𝒜 i)] [∀ i, Fintype (𝒜 i)] (Γ : Game N 𝒜) (hred : Γ.Reduced)
    (huniv : ∀ i, Γ.S i = Finset.univ) : ¬ Γ.SPIDecision := by
  rw [Game.spiDecision_iff_certificate]
  rintro ⟨c, -, i, hi⟩
  apply hi
  apply Finset.eq_of_subset_of_card_le
  · intro x _; rw [Game.reduce_of_reduced hred, huniv i]; exact Finset.mem_univ _
  · rw [Game.Certificate.image, Finset.card_image_of_injOn (c.injOn i)]

example : ¬ coord.SPIDecision :=
  not_spiDecision_of_reduced_univ coord coord_reduced fun _ => rfl

/-- Nor a strict, unilateral or strict unilateral one (the implications are on the API). -/
example : ¬ coord.StrictUnilateralSPIDecision := fun h =>
  not_spiDecision_of_reduced_univ coord coord_reduced (fun _ => rfl) h.strict.spi

/-! ### Theorem 3 and the certainty interface on a client play family -/

/-- A client play family on a one-point sample space that always coordinates on `true`
when it can and otherwise picks the first available action. -/
noncomputable def clientPlay : Play Two CUniv Unit where
  play Γ _ := fun i => if true ∈ Γ.S i then true else (Γ.nonempty i).choose
  mem Γ _ i := by
    by_cases h : true ∈ Γ.S i
    · simp [h]
    · simp only [h, if_false]; exact (Γ.nonempty i).choose_spec

/-- Every game is an SPI on itself, and Theorem 3 turns that into a Pareto-improving outcome
correspondence — for any certainty filter. -/
example (L : Filter Unit) : ∃ Φ, clientPlay.ParetoImprovingCorrespondence L coord coord Φ :=
  (clientPlay.isSPI_iff_exists_paretoImprovingCorrespondence L
    (Game.IsSubsetGameOf.refl coord)).1 (clientPlay.isSPI_self L coord)

/-- At the trivial filter `⊥` every SPI statement is vacuous — the API does not hide this:
`Play.IsSPI X ⊥ Γ Γs` holds for every subset game. -/
example (Γs : Game Two CUniv) (h : Γs.IsSubsetGameOf coord) : clientPlay.IsSPI ⊥ coord Γs :=
  ⟨h, Filter.eventually_bot⟩

/-! ### Books: Assumptions 1 and 2 are satisfiable, and soundness gives real SPIs -/

/-- A representatives model satisfying both assumptions exists (the constant book on a
one-point space); soundness then turns any Pareto-improving derivation into an SPI
under probability one. -/
example {Γ Γs : Game Two CUniv} {Φ : SetRel (∀ i, CUniv i) (∀ i, CUniv i)}
    (d : Game.Deriv Γ Γ Γs Φ) (hΦ : Game.ParetoImprovingFor Γ Φ) :
    ∃ R : Representatives.{0, 0, 0} Two CUniv, R.toPlay.IsSPI R.certainty Γ Γs := by
  obtain ⟨R, hA1, hA2⟩ := exists_representatives_satisfiesA1_satisfiesA2 (N := Two) (𝒜 := CUniv)
  exact ⟨R, Play.isSPI_of_deriv hA1 hA2 d hΦ⟩

/-- A book's play family satisfies Assumption 1 for *every* certainty filter, so in particular
it plays a game and its full reduction alike, eventually. -/
example (B : Book Two CUniv Unit) (L : Filter Unit) :
    ∀ᶠ ω in L, B.toPlay.play coord.reduce ω = B.toPlay.play coord ω :=
  (B.satisfiesA1 L).play_reduce coord

/-! ### From graphs to SPIs: the hardness construction as a client tool

Definition 8 → Lemma 28 → Definition 5 → soundness: a subgraph isomorphism between two
client graphs yields, for every representatives model satisfying the assumptions, a genuine
strict unilateral SPI in the constructed two-player game. -/

/-- The client's graphs: the single-edge path on two vertices and the three-cycle on three. -/
def pathTwo : Hardness.Graph 2 := fun i j => decide (i = 0 ∧ j = 1)

def cycleThree : Hardness.Graph 3 := fun i j => decide (j.val = (i.val + 1) % 3)

/-- `0 ↦ 0, 1 ↦ 1` embeds the path into the cycle. -/
lemma pathTwo_embeds : Hardness.SubgraphIsoProblem pathTwo cycleThree :=
  ⟨⟨fun i => ⟨i.val, by omega⟩, fun i j h => Fin.ext (by simpa using congrArg Fin.val h)⟩,
    fun j l _ => by fin_cases j <;> fin_cases l <;> decide⟩

/-- The constructed game, with `ε = 1/8`. -/
noncomputable def hardClient : Game Two (Hardness.HardUniverse 2 3) :=
  Hardness.hardnessGame pathTwo cycleThree (1/8)

/-- Lemma 28 delivers the decision-problem verdict … -/
lemma hardClient_strictUnilateral : hardClient.StrictUnilateralSPIDecision :=
  (Hardness.subgraphIsoProblem_iff_strictUnilateralSPIDecision pathTwo cycleThree (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)).1 pathTwo_embeds

/-- … and soundness turns it into an SPI played under probability one by any representatives
satisfying Assumptions 1 and 2: a unilateral subset game that is a strict SPI. -/
example (R : Representatives Two (Hardness.HardUniverse 2 3))
    (hA1 : R.toPlay.SatisfiesA1 R.certainty) (hA2 : R.toPlay.SatisfiesA2 R.certainty) :
    ∃ Γs, R.toPlay.IsUnilateralSPI R.certainty hardClient Γs := by
  obtain ⟨Γs, -, -, ⟨Φ, d, hΦ, -⟩, huni⟩ := hardClient_strictUnilateral
  exact ⟨Γs, Play.isUnilateralSPI_of_deriv hA1 hA2 huni d hΦ⟩

/-- The instance has `2(2·2+2) + 2(2·3+2) = 28` actions. -/
example : hardClient.size = 28 := by
  simp [hardClient, Hardness.size_hardnessGame]

/-! ### The search space is finite and bounded -/

/-- The client's coordination game has exactly `4` certificates (two permutations per
player), below the bound `4 ^ 4`. -/
example : Fintype.card coord.Certificate ≤ 4 ^ 4 := by
  have h := coord.card_certificate_le
  have h2 : Fintype.card Two = 2 := rfl
  have hs : coord.size = 4 := by simp [Game.size, coord, h2]
  have hr : coord.reduce.size = 4 := by rw [Game.reduce_of_reduced coord_reduced, hs]
  rwa [hs, hr] at h

/-! ### Feasible payoffs and Pareto optimality -/

/-- Every pure outcome's payoff is feasible, and the feasible set is convex: the midpoint of
two pure payoffs is feasible. -/
example : (1 / 2 : ℝ) • coord.u (pair true true) + (1 / 2 : ℝ) • coord.u (pair false false) ∈
    coord.feasible :=
  coord.convex_feasible (coord.u_mem_feasible fun i => Finset.mem_univ _)
    (coord.u_mem_feasible fun i => Finset.mem_univ _) (by norm_num) (by norm_num) (by norm_num)

/-- `(2, 2)` is Pareto-optimal in `C(coord)`: every feasible payoff is a convex combination of
payoffs `≤ (2, 2)`. -/
example : Game.ParetoOptimalIn (coord.u (pair true true)) coord.feasible := by
  rintro ⟨y, hy, hlt⟩
  rw [Game.feasible_eq_convexHull] at hy
  have hle : ∀ z ∈ coord.u '' coord.profiles, z ≤ coord.u (pair true true) := by
    rintro z ⟨a, -, rfl⟩ i
    rw [eq_pair a]
    cases a .one <;> cases a .two <;> cases i <;> simp [coord_u, coordPayoff]
  have hy' : y ≤ coord.u (pair true true) := by
    have hconv : Convex ℝ {z : Two → ℝ | z ≤ coord.u (pair true true)} :=
      convex_Iic (coord.u (pair true true))
    exact (convexHull_min hle hconv) hy
  exact absurd hlt (not_lt_of_ge hy')

/-! ### Threat points are metered by pure guarantees and best responses -/

/-- Player 1's threat point in the coordination game is at most `2` (a best response at
`(true, true)`) and at least `0` (every payoff is nonnegative). -/
example : coord.threatPoint .one ≤ 2 ∧ 0 ≤ coord.threatPoint .one := by
  constructor
  · have := coord.threatPoint_le_of_bestResponse (a := pair true true)
      (fun i => Finset.mem_univ _) .one fun b _ => by
        cases b <;> simp [coord_u, coordPayoff]
    simpa [coord_u, coordPayoff] using this
  · refine coord.le_threatPoint_of_guarantee .one (Finset.mem_univ true) 0 fun s _ => ?_
    rw [eq_pair (coord.ofStrategicProfile s)]
    cases (coord.ofStrategicProfile s) .one <;> cases (coord.ofStrategicProfile s) .two <;>
      simp [coord_u, coordPayoff]

end APITests.SafeParetoImprovements
