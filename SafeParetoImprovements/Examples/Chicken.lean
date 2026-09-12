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

## The universe (`dd:room`, RULING 13)

Table 7's three actions do **not** exhaust the players' universe here: the game lives over
`CUniverse i := CAct ⊕ ℕ`, with the board in the `inl` copy and off-profile payoffs `0`
(`dd:total-utility`).  This is forced.  Over the bare `CAct` the game uses its whole finite
universe, so `TokenGame chicken` is *empty* (freshness contradicts `Game.nonempty`) and the
impossibility clause of Proposition 16 would be vacuously true — the round-4 blocker
R4-F01.  Over `CAct ⊕ ℕ`, freshness confines token action sets to the `inr` copy of `ℕ`, so
every finite token action set is realized up to relabelling (`chickenTokenOfSize`, of every
cardinality) and the class quantified over is the paper's.  The disclosure is written out
in `Coordination.lean`'s `dd:room` paragraph.

Because a universe is a modeling choice, the impossibility is *also* carried in the
label-free form `chicken_no_feasible_dominating_of_mean_cc`, which mentions no tokens at
all: it says that no `C(Γ)`-valued random variable dominating the default play at every
sample point has mean `u(c, c)`.  Proposition 16's negated existential is one `rintro` away
from it, and that form cannot silently become a statement about how rich the universe is.
-/

namespace SafeParetoImprovements

namespace Examples

open Filter MeasureTheory Two
open scoped ENNReal

/-- The three actions of Table 7. -/
inductive CAct | a | b | c
  deriving DecidableEq, Fintype, Inhabited

/-- Both players choose from `CAct ⊕ ℕ`: Table 7's board in the `inl` copy, and infinitely
many spare actions for token games (`dd:room`, RULING 13). -/
abbrev CUniverse : Two → Type := fun _ => CAct ⊕ ℕ

/-- Table 7's payoffs on the board, `chickenPayoff a₁ a₂ i`. -/
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

/-- The board of Table 7 inside the universe: the three real actions. -/
def chickenActions : Finset (CAct ⊕ ℕ) := {Sum.inl CAct.a, Sum.inl CAct.b, Sum.inl CAct.c}

@[simp] lemma mem_chickenActions {x : CAct ⊕ ℕ} :
    x ∈ chickenActions ↔ x = Sum.inl CAct.a ∨ x = Sum.inl CAct.b ∨ x = Sum.inl CAct.c := by
  simp [chickenActions]

/-- Table 7's payoffs on the universe: the printed table on the board, `0` off it
(`dd:total-utility`; off-board payoffs are unobservable, every profile of `chicken` being
a board profile). -/
def chickenPayoff' : CAct ⊕ ℕ → CAct ⊕ ℕ → Two → ℝ
  | Sum.inl p, Sum.inl q, i => chickenPayoff p q i
  | _, _, _ => 0

/-- The game of Table 7. -/
def chicken : Game Two CUniverse where
  S _ := chickenActions
  nonempty _ := ⟨Sum.inl CAct.a, by simp⟩
  u x i := chickenPayoff' (x .one) (x .two) i

namespace chicken

lemma u_apply (x : ∀ i, CUniverse i) (i : Two) :
    chicken.u x i = chickenPayoff' (x .one) (x .two) i := rfl

@[simp] lemma S_eq (i : Two) : chicken.S i = chickenActions := rfl

/-- On the board, `chicken`'s payoffs are exactly Table 7's. -/
lemma u_inl (p q : CAct) (i : Two) :
    chicken.u (pair (Sum.inl p) (Sum.inl q)) i = chickenPayoff p q i := rfl

lemma mem_profiles {x : ∀ i, CUniverse i} :
    x ∈ chicken.profiles ↔ ∀ i, x i ∈ chickenActions := Iff.rfl

/-! ### Room for tokens

`CAct ⊕ ℕ` is infinite, so any finite set of actions can be avoided; in particular the
board can be copied outside itself, which is what a token game for `chicken` needs. -/

lemma hasRoom : chicken.HasRoomOutside chicken.S :=
  chicken.hasRoomOutside_of_infinite _

/-! ### The reduction: `c` is strictly dominated by `a` for both players -/

lemma dom1 : chicken.IsStrictlyDominated .one (Sum.inl CAct.c) :=
  ⟨Sum.inl CAct.a, (strictlyDominates_one_iff _ _ _).2 ⟨by simp, by simp, fun x hx => by
    have hx' : x = Sum.inl CAct.a ∨ x = Sum.inl CAct.b ∨ x = Sum.inl CAct.c :=
      mem_chickenActions.1 hx
    clear hx
    rcases hx' with rfl | rfl | rfl <;> norm_num [u_inl, chickenPayoff]⟩⟩

/-- After removing player 1's `c`. -/
def g1 : Game Two CUniverse := chicken.erase .one (Sum.inl CAct.c) dom1.erase_nonempty

lemma g1_u : g1.u = chicken.u := rfl

lemma g1_S_one : g1.S .one = {Sum.inl CAct.a, Sum.inl CAct.b} := by
  show (chicken.erase .one (Sum.inl CAct.c) dom1.erase_nonempty).S .one = _
  rw [Game.erase_S_self]
  show chickenActions.erase (Sum.inl CAct.c) = _
  ext x
  simp only [Finset.mem_erase, mem_chickenActions, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hne, rfl | rfl | rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd rfl hne
  · rintro (rfl | rfl) <;> exact ⟨by simp, by simp⟩

lemma g1_S_two : g1.S .two = chickenActions := Game.erase_S_of_ne _ _ _ _ (by decide)

lemma dom2 : g1.IsStrictlyDominated .two (Sum.inl CAct.c) :=
  ⟨Sum.inl CAct.a, (strictlyDominates_two_iff _ _ _).2 ⟨by rw [g1_S_two]; simp,
    by rw [g1_S_two]; simp,
    fun x hx => by
      rw [g1_S_one] at hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> norm_num [g1_u, u_inl, chickenPayoff]⟩⟩

/-- The reduced game: the Chicken-like `{a, b}²`. -/
def reducedChicken : Game Two CUniverse := g1.erase .two (Sum.inl CAct.c) dom2.erase_nonempty

lemma reducedChicken_u : reducedChicken.u = chicken.u := rfl

lemma reducedChicken_S (i : Two) :
    reducedChicken.S i = {Sum.inl CAct.a, Sum.inl CAct.b} := by
  cases i
  · rw [show reducedChicken.S .one = g1.S .one from Game.erase_S_of_ne _ _ _ _ (by decide),
      g1_S_one]
  · show (g1.erase .two (Sum.inl CAct.c) dom2.erase_nonempty).S .two = _
    rw [Game.erase_S_self, g1_S_two]
    ext x
    simp only [Finset.mem_erase, mem_chickenActions, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hne, rfl | rfl | rfl⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd rfl hne
    · rintro (rfl | rfl) <;> exact ⟨by simp, by simp⟩

lemma reducedChicken_mem_S {i : Two} {x : CAct ⊕ ℕ} :
    x ∈ reducedChicken.S i ↔ x = Sum.inl CAct.a ∨ x = Sum.inl CAct.b := by
  rw [reducedChicken_S]; simp

lemma reducedChicken_reduced : reducedChicken.Reduced := by
  rw [reduced_iff]
  constructor
  · rintro x ⟨x', h⟩
    rw [strictlyDominates_one_iff] at h
    obtain ⟨hx', hx, hlt⟩ := h
    rw [reducedChicken_mem_S] at hx hx'
    rcases hx with rfl | rfl <;> rcases hx' with rfl | rfl
    · exact lt_irrefl _ (hlt _ (reducedChicken_mem_S.2 (Or.inl rfl)))
    · have := hlt _ (reducedChicken_mem_S.2 (Or.inr rfl))
      norm_num [reducedChicken_u, u_inl, chickenPayoff] at this
    · have := hlt _ (reducedChicken_mem_S.2 (Or.inl rfl))
      norm_num [reducedChicken_u, u_inl, chickenPayoff] at this
    · exact lt_irrefl _ (hlt _ (reducedChicken_mem_S.2 (Or.inl rfl)))
  · rintro x ⟨x', h⟩
    rw [strictlyDominates_two_iff] at h
    obtain ⟨hx', hx, hlt⟩ := h
    rw [reducedChicken_mem_S] at hx hx'
    rcases hx with rfl | rfl <;> rcases hx' with rfl | rfl
    · exact lt_irrefl _ (hlt _ (reducedChicken_mem_S.2 (Or.inl rfl)))
    · have := hlt _ (reducedChicken_mem_S.2 (Or.inr rfl))
      norm_num [reducedChicken_u, u_inl, chickenPayoff] at this
    · have := hlt _ (reducedChicken_mem_S.2 (Or.inl rfl))
      norm_num [reducedChicken_u, u_inl, chickenPayoff] at this
    · exact lt_irrefl _ (hlt _ (reducedChicken_mem_S.2 (Or.inl rfl)))

/-- The full reduction of Table 7 is the Chicken-like game. -/
lemma reduce_eq : chicken.reduce = reducedChicken := by
  have e1 : chicken.ElimStar g1 := Relation.ReflTransGen.single ⟨.one, _, dom1, rfl⟩
  have e2 : chicken.ElimStar reducedChicken :=
    Relation.ReflTransGen.tail e1 ⟨.two, _, dom2, rfl⟩
  exact Game.reduce_eq_of_reduced_of_elimStar e2 reducedChicken_reduced

/-! ### Two supporting half-planes of `C(Γ)`

`Game.feasible_eq_convexHull` reduces each to a check at the generators `u(x)`, `x` a
profile — i.e. at board profiles only, the off-board payoffs never being seen. -/

/-- Every feasible payoff vector satisfies `100 y₁ + 6 y₂ ≤ 400`; hence `(4, 0)` is
Pareto-optimal in `C(Γ)`. -/
lemma feasible_le₁ {y : Two → ℝ} (hy : y ∈ chicken.feasible) :
    100 * y .one + 6 * y .two ≤ 400 := by
  rw [Game.feasible_eq_convexHull] at hy
  have hconv : Convex ℝ {y : Two → ℝ | 100 * y .one + 6 * y .two ≤ 400} := by
    intro p hp q hq θ η hθ hη hθη
    simp only [Set.mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hp hq ⊢
    nlinarith
  refine convexHull_min ?_ hconv hy
  rintro _ ⟨x, hx, rfl⟩
  have h1 := hx .one; have h2 := hx .two
  simp only [S_eq, mem_chickenActions] at h1 h2
  simp only [Set.mem_setOf_eq, u_apply]
  rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 <;>
    rw [h1, h2] <;> norm_num [chickenPayoff', chickenPayoff]

/-- Every feasible payoff vector satisfies `6 y₁ + 100 y₂ ≤ 400`; hence `(0, 4)` is
Pareto-optimal in `C(Γ)`. -/
lemma feasible_le₂ {y : Two → ℝ} (hy : y ∈ chicken.feasible) :
    6 * y .one + 100 * y .two ≤ 400 := by
  rw [Game.feasible_eq_convexHull] at hy
  have hconv : Convex ℝ {y : Two → ℝ | 6 * y .one + 100 * y .two ≤ 400} := by
    intro p hp q hq θ η hθ hη hθη
    simp only [Set.mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hp hq ⊢
    nlinarith
  refine convexHull_min ?_ hconv hy
  rintro _ ⟨x, hx, rfl⟩
  have h1 := hx .one; have h2 := hx .two
  simp only [S_eq, mem_chickenActions] at h1 h2
  simp only [Set.mem_setOf_eq, u_apply]
  rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 <;>
    rw [h1, h2] <;> norm_num [chickenPayoff', chickenPayoff]

end chicken

open chicken

/-! ### The representatives: `(a, b)` and `(b, a)` with probability ½ each -/

/-- The two pages: heads plays `(a, b)`, tails `(b, a)`. -/
def chickenPages : Bool → ∀ i, CUniverse i
  | true => pair (Sum.inl CAct.a) (Sum.inl CAct.b)
  | false => pair (Sum.inl CAct.b) (Sum.inl CAct.a)

lemma chickenPages_mem : ∀ ω, chickenPages ω ∈ reducedChicken.profiles := by
  intro ω i
  cases ω <;> cases i <;> rw [reducedChicken_S] <;> simp [chickenPages, pair]

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
  cases i <;> norm_num [chickenPages, u_inl, chickenPayoff]

/-! ### The label-free kernel of Proposition 16

Nothing in the impossibility argument mentions tokens: it uses only that the improved
payoff vector is feasible at each sample point and dominates the default play there.
Stating it that way first makes the mathematics independent of how rich the action universe
happens to be (`dd:room`), and Proposition 16's negated existential is one `rintro` away.

The hypotheses are satisfiable — `v ω := chicken.u (chickenPages ω)` meets both, with mean
`(2, 2)` — so this is not vacuous. -/

/-- No `C(Γ)`-valued random variable that weakly dominates the default play at every sample
point has mean `u(c, c) = (3, 3)`: on heads it is capped by `100 y₁ + 6 y₂ ≤ 400` and
dominating `(4, 0)`, on tails symmetrically, so its coordinate sum is at most `4` at each
face and at most `4 < 6` in expectation. -/
lemma chicken_no_feasible_dominating_of_mean_cc (v : Bool → Two → ℝ)
    (hfeas : ∀ ω, v ω ∈ chicken.feasible)
    (hdom : ∀ ω, chicken.u (chickenPages ω) ≤ v ω) :
    ¬ ∀ i, ∫ ω, v ω i ∂coin =
      chicken.u (pair (Sum.inl CAct.c) (Sum.inl CAct.c)) i := by
  intro hE
  have h₁ : v true .one + v true .two ≤ 4 := by
    have hle := hdom true
    have hf := feasible_le₁ (hfeas true)
    have ha := hle .one; have hb := hle .two
    simp only [chickenPages, u_inl, chickenPayoff] at ha hb
    linarith
  have h₂ : v false .one + v false .two ≤ 4 := by
    have hle := hdom false
    have hf := feasible_le₂ (hfeas false)
    have ha := hle .one; have hb := hle .two
    simp only [chickenPages, u_inl, chickenPayoff] at ha hb
    linarith
  have e₁ := hE .one
  have e₂ := hE .two
  rw [integral_coin] at e₁ e₂
  simp only [u_inl, chickenPayoff] at e₁ e₂
  linarith

example : ∀ ω, chicken.u (chickenPages ω) ∈ chicken.feasible := by
  intro ω
  exact chicken.u_mem_feasible (fun i => by
    cases ω <;> cases i <;> simp [chickenPages, pair])

/-! ### Proposition 16 -/

/-- **Proposition 16.**  For the game of Table 7 and the representatives playing `(a, b)`
and `(b, a)` with probability ½ each — which satisfy Assumptions 1 and 2 — the outcome
`(c, c)` is an outcome of the game and Pareto-improves on the expected default payoff for
both players, yet no perfect-coordination SPI has expected payoff `u(c, c) = (3, 3)`.

The paper allows any `0 < p ≤ ½` for the probability of each equilibrium; the witness takes
`p = ½`, which is inside that range and is the only value at which the paper's description
determines `Π` completely (for `p < ½` the residual mass `1 − 2p` is assigned to no
outcome).

`Π` is **fixed, and must be**: `chicken_spi_for_other_representatives` exhibits other
Assumption-1/2 representatives over the *same* game for which a perfect-coordination SPI
with expected payoff `(3, 3)` does exist, so the printed existential over `Π` (Table 7's
caption, "depending on `Π`") cannot be turned into a universal.

Integrability is automatic and no hypothesis is needed for it:
`Representatives.integrable_comp_play` — a real function of `Π(Γ)` takes finitely many
values on measurable fibers — so the expectation clause is never satisfiable by Bochner's
junk value `0`.  The impossibility itself is `chicken_no_feasible_dominating_of_mean_cc`,
which mentions no tokens.

Paper node: `Proposition 16` -/
theorem chicken_no_perfectCoordinationSPI :
    chickenRepresentatives.toPlay.SatisfiesA1 chickenRepresentatives.certainty ∧
    chickenRepresentatives.toPlay.SatisfiesA2 chickenRepresentatives.certainty ∧
    (pair (Sum.inl CAct.c) (Sum.inl CAct.c) : ∀ i, CUniverse i) ∈ chicken.profiles ∧
    (∀ i, ∫ ω, chicken.u (chickenRepresentatives.play chicken ω) i ∂chickenRepresentatives.μ <
      chicken.u (pair (Sum.inl CAct.c) (Sum.inl CAct.c)) i) ∧
    ¬ ∃ T : TokenGame chicken,
      T.IsSPI chickenRepresentatives.toPlay chickenRepresentatives.certainty ∧
      ∀ i, ∫ ω, T.ue (chickenRepresentatives.play T.game ω) i ∂chickenRepresentatives.μ =
        chicken.u (pair (Sum.inl CAct.c) (Sum.inl CAct.c)) i := by
  refine ⟨chickenBook.satisfiesA1 _, chickenBook.satisfiesA2 _,
    fun i => by cases i <;> simp [pair], fun i => ?_, ?_⟩
  · rw [chickenRepresentatives_integral]
    cases i <;> norm_num [u_inl, chickenPayoff]
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
  exact chicken_no_feasible_dominating_of_mean_cc
    (fun ω => T.ue (chickenRepresentatives.play T.game ω)) hfeas hpt hE

/-! ### The token-game class over `chicken` is the paper's

Non-vacuity in both directions: token games exist, at every finite size, and Definition 6
holds of some of them and fails of others.  Without these the impossibility clause of
Proposition 16 would be an assertion about an empty or truncated class (R4-F01, R4-F05). -/

/-- A one-token-per-player token game with `uᵉ ≡ u(c, c) = (3, 3)`. -/
noncomputable def chickenToken33 : TokenGame chicken where
  game :=
    { S := fun _ => {Sum.inr 0}
      nonempty := fun _ => ⟨Sum.inr 0, by simp⟩
      u := fun _ _ => 0 }
  fresh i := by
    rw [Finset.disjoint_left]
    intro x hx
    simp only [Finset.mem_singleton] at hx
    subst hx
    simp
  ue := fun _ => chicken.u (pair (Sum.inl CAct.c) (Sum.inl CAct.c))
  ue_mem _ _ := chicken.u_mem_feasible (fun i => by cases i <;> simp [pair])

lemma chickenToken33_ue (b : ∀ i, CUniverse i) :
    chickenToken33.ue b = chicken.u (pair (Sum.inl CAct.c) (Sum.inl CAct.c)) := rfl

lemma nonempty_tokenGame_chicken : Nonempty (TokenGame chicken) := ⟨chickenToken33⟩

/-- Token games of every finite size: the universe has infinite room, so no cardinality of
token action set is missing from the class Proposition 16 quantifies over. -/
noncomputable def chickenTokenOfSize (k : ℕ) : TokenGame chicken where
  game :=
    { S := fun _ => (Finset.range (k + 1)).image Sum.inr
      nonempty := fun _ => ⟨Sum.inr 0, by simp⟩
      u := fun _ _ => 0 }
  fresh i := by
    rw [Finset.disjoint_left]
    intro x hx
    obtain ⟨n, -, rfl⟩ := Finset.mem_image.1 hx
    simp
  ue := fun _ => chicken.u (pair (Sum.inl CAct.c) (Sum.inl CAct.c))
  ue_mem _ _ := chicken.u_mem_feasible (fun i => by cases i <;> simp [pair])

lemma chickenTokenOfSize_card (k : ℕ) (i : Two) :
    ((chickenTokenOfSize k).game.S i).card = k + 1 := by
  show ((Finset.range (k + 1)).image Sum.inr).card = k + 1
  rw [Finset.card_image_of_injective _ Sum.inr_injective, Finset.card_range]

/-- **Definition 6 is not constant-true**: `chickenToken33` is a token game for `chicken`
that is *not* a perfect-coordination SPI, because on heads the default play is worth
`(4, 0)`, which `(3, 3)` does not dominate. -/
lemma chickenToken33_not_isSPI :
    ¬ chickenToken33.IsSPI chickenRepresentatives.toPlay chickenRepresentatives.certainty := by
  intro h
  have h' := ((ae_coin_iff _).1 h).1
  have hp : chickenRepresentatives.toPlay.play chicken true = chickenPages true :=
    chickenRepresentatives_play true
  have hx := h' .one
  rw [hp, chickenToken33_ue] at hx
  simp only [chickenPages, u_inl] at hx
  norm_num [chickenPayoff] at hx

/-! ### Proposition 16 depends on `Π`, and must

The printed statement is existential in `Π` ("depending on `Π`", Table 7's caption).  It has
to be: over the *same* game, the book that prescribes `(b, b)` also satisfies Assumptions 1
and 2, and for it the constant token game `chickenToken33` **is** a perfect-coordination SPI
with expected payoff exactly `(3, 3)`.  A universally quantified reading of Proposition 16
would therefore be false. -/

lemma chickenBB_mem :
    (pair (Sum.inl CAct.b) (Sum.inl CAct.b) : ∀ i, CUniverse i) ∈ reducedChicken.profiles := by
  intro i; cases i <;> rw [reducedChicken_S] <;> simp [pair]

/-- The book prescribing `(b, b)` — worth `(1, 1)` — on every game reducing to the
Chicken-like game. -/
noncomputable def chickenBookBB : Book Two CUniverse Bool :=
  Book.prescribed reducedChicken chickenBB_mem Bool

noncomputable def chickenRepresentativesBB : Representatives.{0, 0, 0} Two CUniverse :=
  chickenBookBB.toRepresentatives (μ := coin) (fun _ _ => trivial)

lemma chickenRepresentativesBB_play (ω : Bool) :
    chickenRepresentativesBB.toPlay.play chicken ω =
      pair (Sum.inl CAct.b) (Sum.inl CAct.b) :=
  Book.prescribed_play reducedChicken chickenBB_mem Bool chicken chicken.reduce_eq ω

/-- **`Π` cannot be universally quantified in Proposition 16.**  For the `(b, b)`-prescribing
representatives — which satisfy Assumptions 1 and 2 by the same book construction — the
constant token game with `uᵉ ≡ (3, 3)` is a perfect-coordination SPI whose expected payoff
is exactly `u(c, c)`. -/
lemma chicken_spi_for_other_representatives :
    chickenRepresentativesBB.toPlay.SatisfiesA1 chickenRepresentativesBB.certainty ∧
    chickenRepresentativesBB.toPlay.SatisfiesA2 chickenRepresentativesBB.certainty ∧
    chickenToken33.IsSPI chickenRepresentativesBB.toPlay chickenRepresentativesBB.certainty ∧
    ∀ i, ∫ ω, chickenToken33.ue
        (chickenRepresentativesBB.toPlay.play chickenToken33.game ω) i
        ∂chickenRepresentativesBB.μ =
      chicken.u (pair (Sum.inl CAct.c) (Sum.inl CAct.c)) i := by
  refine ⟨chickenBookBB.satisfiesA1 _, chickenBookBB.satisfiesA2 _, ?_, ?_⟩
  · refine Filter.Eventually.of_forall fun ω => ?_
    have hp : chickenRepresentativesBB.toPlay.play chicken ω =
        pair (Sum.inl CAct.b) (Sum.inl CAct.b) := chickenRepresentativesBB_play ω
    show chicken.u (chickenRepresentativesBB.toPlay.play chicken ω) ≤ chickenToken33.ue _
    rw [hp, chickenToken33_ue]
    intro i
    cases i <;> norm_num [u_inl, chickenPayoff]
  · intro i
    show ∫ _ω, chickenToken33.ue _ i ∂coin = _
    simp only [chickenToken33_ue]
    rw [integral_coin]
    ring

end Examples

end SafeParetoImprovements
