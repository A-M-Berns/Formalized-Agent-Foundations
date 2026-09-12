import SafeParetoImprovements.Characterization
import SafeParetoImprovements.Examples.DecisionWitnesses

/-!
# Non-vacuity for §5.3: Lemma 13, Corollary 14, and `condExp`

The §5.3 statements of `Characterization.lean` all quantify over Assumptions 1–2, a room
hypothesis and a perfect-coordination SPI.  This file shows that bundle is inhabited, that
Corollary 14's `achievable` is not a singleton, and — the point of `condExp` — that the
conditional expectation is a genuine average rather than a point evaluation.

* **Lemma 13 and Corollary 14 apply** to the conflict game of `TokenWitnesses.lean` with
  the fair-coin book representatives (`conflict_exists_reassignment`,
  `conflict_achievable_eq_improvementSum`, `conflict_isPolytope_achievable`), and to a
  perfect-coordination SPI that is emphatically *not* already a copy of the reduced game:
  `conflictThreeToken` has three actions per player where the base game has two, so it is
  not even isomorphic to the reduction (`conflictThreeToken_not_isomorphic`), and Lemma 13
  turns it into one that is an exact copy with the same expected payoff
  (`conflict_lemma13_at_three`).
* **`achievable` has at least two points** (`conflict_achievable_not_singleton`): the
  strict token game is worth `(1, 1)` and the plain one `(½, ½)`.  The latter value is not
  attained by any token game with a *constant* `uᵉ` (`conflict_plain_not_constant_ue`), so
  Corollary 14's set is genuinely wider than the constant reassignments.
* **`condExp` is a genuine average** (`condExp_genuine_average`, R5-F11).  In every *book*
  model of this development the conditional expectation collapses to a point evaluation,
  because a `Book` page is chosen per isomorphism class of the reduced game and the token
  play is therefore a function of `Π(Γ)`.  That is a property of the book construction, not
  of `Representatives.condExp`: the hand-built family `mixPlay` reads the *size* of the game
  it is handed, so on the (full-measure) fiber `Π(mixBase) = (0,0)` the token payoff still
  varies with `ω`, and `E[uᵉ(Π(Aˢ,uˢ)) | Π(Γ) = (0,0)] = (½, ½)` is a value the integrand
  never takes (`condExp_ne_values`).
-/

namespace SafeParetoImprovements

namespace Examples

open Filter Set MeasureTheory ProbabilityTheory Two

/-! ### Lemma 13 and Corollary 14 on the conflict game -/

/-- **Lemma 13's hypotheses are inhabited**: on the conflict game with the fair-coin book
representatives, the strict perfect-coordination SPI `conflictStrictToken` is replaced by an
exact copy of the reduced game with the same conditional and unconditional expectations. -/
lemma conflict_exists_reassignment :
    ∃ T : TokenGame conflictGame, conflictGame.reduce.ExactCopy T.game ∧
      T.IsSPI conflictRepresentatives.toPlay conflictRepresentatives.certainty ∧
      (∀ a ∈ conflictRepresentatives.support conflictGame,
        conflictRepresentatives.condExp conflictGame a
            (fun ω => T.ue (conflictRepresentatives.play T.game ω)) =
          conflictRepresentatives.condExp conflictGame a
            (fun ω => conflictStrictToken.ue
              (conflictRepresentatives.play conflictStrictToken.game ω))) ∧
      conflictRepresentatives.tokenValue conflictGame T =
        conflictRepresentatives.tokenValue conflictGame conflictStrictToken :=
  conflictRepresentatives.exists_reassignment_condExp_eq conflictGame
    (conflictBook.satisfiesA1 _) (conflictBook.satisfiesA2 _) conflictGame_hasRoom
    conflictStrictToken_isSPI

/-- **Corollary 14's formula is inhabited** on the conflict game. -/
lemma conflict_achievable_eq_improvementSum :
    conflictRepresentatives.achievable conflictGame =
      conflictRepresentatives.improvementSum conflictGame :=
  conflictRepresentatives.achievable_eq_improvementSum conflictGame
    (conflictBook.satisfiesA1 _) (conflictBook.satisfiesA2 _) conflictGame_hasRoom

/-- **Corollary 14's polytope clause is inhabited** on the conflict game. -/
lemma conflict_isPolytope_achievable :
    IsPolytope (conflictRepresentatives.achievable conflictGame) :=
  conflictRepresentatives.isPolytope_achievable conflictGame
    (conflictBook.satisfiesA1 _) (conflictBook.satisfiesA2 _) conflictGame_hasRoom

/-! ### `achievable` is not a singleton -/

/-- The expected token payoff on the fair coin is the average of its two values. -/
lemma conflict_tokenValue (T : TokenGame conflictGame) (i : Two) :
    conflictRepresentatives.tokenValue conflictGame T i =
      2⁻¹ * (T.ue (conflictRepresentatives.play T.game true) i
           + T.ue (conflictRepresentatives.play T.game false) i) := by
  unfold Representatives.tokenValue
  rw [eval_integral
    (fun j => (conflictRepresentatives.integrable_comp_play_pi T.game T.ue _).eval j) i]
  show (∫ ω, T.ue (conflictRepresentatives.play T.game ω) i ∂coin) = _
  rw [integral_coin]

/-- The strict token game is worth `(1, 1)`. -/
lemma conflict_tokenValue_strict (i : Two) :
    conflictRepresentatives.tokenValue conflictGame conflictStrictToken i = 1 := by
  rw [conflict_tokenValue]
  show 2⁻¹ * (conflictStrictUe (conflictRepresentatives.toPlay.play conflictTokenCopy true) i
    + conflictStrictUe (conflictRepresentatives.toPlay.play conflictTokenCopy false) i) = 1
  rw [conflictRepresentatives_play_hat, conflictRepresentatives_play_hat,
    conflictStrictUe_heads, conflictStrictUe_tails]
  show 2⁻¹ * (conflictImproved i + conflictGame.u (conflictPages false) i) = 1
  cases i <;> norm_num [conflictImproved, conflictPages, conflictGame_u_inl, conflictPayoff]

/-- The plain token game is worth the base game's own expectation. -/
lemma conflict_tokenValue_plain_eq (i : Two) :
    conflictRepresentatives.tokenValue conflictGame conflictPlainToken i =
      2⁻¹ * (conflictGame.u (conflictPages true) i + conflictGame.u (conflictPages false) i) := by
  rw [conflict_tokenValue]
  show 2⁻¹ * (conflictGame.u (conflictBookIso.symm.map
      (conflictRepresentatives.toPlay.play conflictTokenCopy true)) i
    + conflictGame.u (conflictBookIso.symm.map
      (conflictRepresentatives.toPlay.play conflictTokenCopy false)) i) = _
  rw [conflictRepresentatives_play_hat, conflictRepresentatives_play_hat,
    conflictBookIso.symm_map_map (conflictPages_mem true),
    conflictBookIso.symm_map_map (conflictPages_mem false)]

/-- The plain token game is worth `(½, ½)`. -/
lemma conflict_tokenValue_plain (i : Two) :
    conflictRepresentatives.tokenValue conflictGame conflictPlainToken i = 2⁻¹ := by
  rw [conflict_tokenValue_plain_eq]
  cases i <;> norm_num [conflictPages, conflictGame_u_inl, conflictPayoff]

/-- **Corollary 14's set is not a singleton**: `(1, 1)` and `(½, ½)` are both safely
achievable on the conflict game. -/
lemma conflict_achievable_not_singleton :
    conflictRepresentatives.tokenValue conflictGame conflictStrictToken ∈
        conflictRepresentatives.achievable conflictGame ∧
      conflictRepresentatives.tokenValue conflictGame conflictPlainToken ∈
        conflictRepresentatives.achievable conflictGame ∧
      conflictRepresentatives.tokenValue conflictGame conflictStrictToken ≠
        conflictRepresentatives.tokenValue conflictGame conflictPlainToken := by
  refine ⟨⟨conflictStrictToken, conflictStrictToken_isSPI, rfl⟩,
    ⟨conflictPlainToken, conflictPlainToken_isSPI, rfl⟩, fun h => ?_⟩
  have := congrFun h Two.one
  rw [conflict_tokenValue_strict, conflict_tokenValue_plain] at this
  norm_num at this

/-- A point of `achievable` that no token game with a *constant* `uᵉ` attains: a constant
`uᵉ` that is a perfect-coordination SPI must already dominate `u(y, y) = (1, 1)`, so its
expected value cannot be the plain token game's `(½, ½)`. -/
lemma conflict_plain_not_constant_ue (T : TokenGame conflictGame) (c : Two → ℝ)
    (hc : ∀ b, T.ue b = c)
    (hspi : T.IsSPI conflictRepresentatives.toPlay conflictRepresentatives.certainty) :
    conflictRepresentatives.tokenValue conflictGame T ≠
      conflictRepresentatives.tokenValue conflictGame conflictPlainToken := by
  intro hval
  have h1 : conflictRepresentatives.tokenValue conflictGame T Two.one = c Two.one := by
    rw [conflict_tokenValue, hc, hc]; ring
  have h2 := ((ae_coin_iff _).1 hspi).2
  rw [conflictRepresentatives_play, hc] at h2
  have h3 : (1 : ℝ) ≤ c Two.one := by
    have := h2 Two.one
    simpa [conflictPages, conflictGame_u_inl, conflictPayoff] using this
  have h4 := congrFun hval Two.one
  rw [h1, conflict_tokenValue_plain] at h4
  rw [h4] at h3
  norm_num at h3

/-! ### A perfect-coordination SPI that is not a copy of the reduction

Lemma 13's content is that an *arbitrary* perfect-coordination SPI can be replaced by an
exact copy of the reduced game.  On the conflict game the two witnesses above are already
built on `conflictTokenCopy`, so they do not exercise that; this one has three actions per
player and is therefore not isomorphic to the two-action reduction. -/

/-- A three-action game on fresh tokens, with all payoffs `0`. -/
def conflictThree : Game Two CGUniverse where
  S _ := {Sum.inr 2, Sum.inr 3, Sum.inr 4}
  nonempty _ := ⟨Sum.inr 2, by simp⟩
  u _ _ := 0

lemma conflictThree_fresh (i : Two) : Disjoint (conflictThree.S i) (conflictGame.S i) := by
  show Disjoint ({Sum.inr 2, Sum.inr 3, Sum.inr 4} : Finset (Bool ⊕ ℕ))
    ({Sum.inl false, Sum.inl true} : Finset (Bool ⊕ ℕ))
  decide

/-- A perfect-coordination SPI on three tokens per player, paying the original players
`u(y, y) = (1, 1)` whatever the representatives do. -/
noncomputable def conflictThreeToken : TokenGame conflictGame where
  game := conflictThree
  fresh := conflictThree_fresh
  ue _ := conflictGame.u (pair (Sum.inl true) (Sum.inl true))
  ue_mem _ _ := conflictGame.u_mem_feasible (conflictPages_mem false)

lemma conflictThreeToken_isSPI :
    conflictThreeToken.IsSPI conflictRepresentatives.toPlay conflictRepresentatives.certainty := by
  refine Filter.Eventually.of_forall fun ω => ?_
  show conflictGame.u (conflictRepresentatives.toPlay.play conflictGame ω) ≤
    conflictGame.u (pair (Sum.inl true) (Sum.inl true))
  rw [conflictRepresentatives_play]
  cases ω <;> intro i <;> cases i <;>
    norm_num [conflictPages, conflictGame_u_inl, conflictPayoff]

/-- `conflictThreeToken.game` is not isomorphic to the reduced base game: a `GameIso` is a
bijection of the action sets, and `3 ≠ 2`. -/
lemma conflictThreeToken_not_isomorphic :
    ¬ conflictGame.reduce.Isomorphic conflictThreeToken.game := by
  rintro ⟨ψ⟩
  have hcard := (ψ.bijOn Two.one).image_eq
  have h1 : conflictGame.reduce = conflictGame := Game.reduce_of_reduced conflictGame_reduced
  have h2 : (conflictGame.S Two.one).card = 2 := by decide
  have h3 : (conflictThree.S Two.one).card = 3 := by decide
  have := congrArg (fun s => s.ncard) hcard
  simp only [Set.InjOn.ncard_image (ψ.bijOn Two.one).injOn, Set.ncard_coe_finset] at this
  rw [h1, h2, show (conflictThreeToken.game).S Two.one = conflictThree.S Two.one from rfl,
    h3] at this
  exact absurd this (by norm_num)

/-- **Lemma 13 does real work**: applied to `conflictThreeToken`, which is *not* a copy of
the reduced game, it returns one that is an exact copy and has the same expected payoff. -/
lemma conflict_lemma13_at_three :
    ∃ T : TokenGame conflictGame, conflictGame.reduce.ExactCopy T.game ∧
      T.IsSPI conflictRepresentatives.toPlay conflictRepresentatives.certainty ∧
      conflictRepresentatives.tokenValue conflictGame T =
        conflictRepresentatives.tokenValue conflictGame conflictThreeToken := by
  obtain ⟨T, hiso, hspi, -, hval⟩ :=
    conflictRepresentatives.exists_reassignment_condExp_eq conflictGame
      (conflictBook.satisfiesA1 _) (conflictBook.satisfiesA2 _) conflictGame_hasRoom
      conflictThreeToken_isSPI
  exact ⟨T, hiso, hspi, hval⟩

/-! ### `condExp` is a genuine average, not a point evaluation

The play family below is *not* a book: it reads the size of the game it is handed.  On the
base game (two actions per player) it always plays the smallest action; on the token game
(three actions) it plays the largest on heads and the smallest on tails.  So the fiber
`Π(base) = (0, 0)` is the whole sample space while the token payoff still varies, and the
conditional expectation there is a strict average (R5-F11). -/

/-- The universe for the averaging witness: `ℕ` for both players. -/
abbrev MixUniverse : Two → Type := fun _ => ℕ

/-- Base game: two actions `{0, 1}` each, `u a = (a₁, a₂)`. -/
def mixBase : Game Two MixUniverse where
  S _ := {0, 1}
  nonempty _ := ⟨0, by simp⟩
  u z i := (z i : ℝ)

/-- The token game the representatives are handed: three fresh actions `{2, 3, 4}`. -/
def mixTok : Game Two MixUniverse where
  S _ := {2, 3, 4}
  nonempty _ := ⟨2, by simp⟩
  u _ _ := 0

/-- A play family that reads the *size* of the game it is handed: on a game with at least
three actions it plays the largest action on heads, otherwise the smallest.  Nothing forbids
this — a `Play` is an arbitrary measurable-fibered selection — and it is exactly what makes
the token play fail to be a function of `Π(mixBase)`. -/
def mixPlay : Play Two MixUniverse Bool where
  play G ω i := if 3 ≤ (G.S i).card ∧ ω = true then (G.S i).max' (G.nonempty i)
                else (G.S i).min' (G.nonempty i)
  mem G ω i := by
    by_cases h : 3 ≤ (G.S i).card ∧ ω = true
    · simp only [if_pos h]; exact Finset.max'_mem _ _
    · simp only [if_neg h]; exact Finset.min'_mem _ _

/-- `mixPlay` on the fair coin. -/
noncomputable def mixRepresentatives : Representatives.{0, 0, 0} Two MixUniverse where
  Ω := Bool
  μ := coin
  toPlay := mixPlay
  measurableSet_fiber _ _ := trivial

lemma mixRepresentatives_play_base (ω : Bool) :
    mixRepresentatives.play mixBase ω = pair 0 0 := by
  funext i
  show (if 3 ≤ (mixBase.S i).card ∧ ω = true then (mixBase.S i).max' (mixBase.nonempty i)
        else (mixBase.S i).min' (mixBase.nonempty i)) = pair 0 0 i
  rw [if_neg (by rintro ⟨h, -⟩; revert h; cases i <;> decide)]
  cases i <;> rfl

lemma mixRepresentatives_play_tok_true : mixRepresentatives.play mixTok true = pair 4 4 := by
  funext i
  show (if 3 ≤ (mixTok.S i).card ∧ true = true then (mixTok.S i).max' (mixTok.nonempty i)
        else (mixTok.S i).min' (mixTok.nonempty i)) = pair 4 4 i
  rw [if_pos (by refine ⟨?_, rfl⟩; cases i <;> decide)]
  cases i <;> rfl

lemma mixRepresentatives_play_tok_false : mixRepresentatives.play mixTok false = pair 2 2 := by
  funext i
  show (if 3 ≤ (mixTok.S i).card ∧ false = true then (mixTok.S i).max' (mixTok.nonempty i)
        else (mixTok.S i).min' (mixTok.nonempty i)) = pair 2 2 i
  rw [if_neg (by rintro ⟨-, h⟩; exact Bool.noConfusion h)]
  cases i <;> rfl

lemma mixBase_mem (a x : ℕ) (ha : a = 0 ∨ a = 1) (hx : x = 0 ∨ x = 1) :
    (pair a x : ∀ i, MixUniverse i) ∈ mixBase.profiles := by
  intro i; cases i
  · show a ∈ ({0, 1} : Finset ℕ); rcases ha with rfl | rfl <;> decide
  · show x ∈ ({0, 1} : Finset ℕ); rcases hx with rfl | rfl <;> decide

/-- A perfect-coordination SPI whose token payoff is *not* determined by `Π(mixBase)`: it
pays `(1, 1)` at the largest token profile and `(0, 0)` otherwise. -/
noncomputable def mixToken : TokenGame mixBase where
  game := mixTok
  fresh i := by
    show Disjoint ({2, 3, 4} : Finset ℕ) ({0, 1} : Finset ℕ)
    decide
  ue b := if b .one = 4 then mixBase.u (pair 1 1) else mixBase.u (pair 0 0)
  ue_mem b _ := by
    by_cases h : b .one = 4
    · rw [if_pos h]; exact mixBase.u_mem_feasible (mixBase_mem 1 1 (Or.inr rfl) (Or.inr rfl))
    · rw [if_neg h]; exact mixBase.u_mem_feasible (mixBase_mem 0 0 (Or.inl rfl) (Or.inl rfl))

lemma mixToken_ue_true :
    mixToken.ue (mixRepresentatives.play mixToken.game true) = mixBase.u (pair 1 1) := by
  show (if (mixRepresentatives.play mixTok true) .one = 4 then mixBase.u (pair 1 1)
        else mixBase.u (pair 0 0)) = mixBase.u (pair 1 1)
  rw [mixRepresentatives_play_tok_true,
    if_pos (show (pair 4 4 : ∀ i, MixUniverse i) Two.one = 4 from rfl)]

lemma mixToken_ue_false :
    mixToken.ue (mixRepresentatives.play mixToken.game false) = mixBase.u (pair 0 0) := by
  show (if (mixRepresentatives.play mixTok false) .one = 4 then mixBase.u (pair 1 1)
        else mixBase.u (pair 0 0)) = mixBase.u (pair 0 0)
  rw [mixRepresentatives_play_tok_false, if_neg (by decide)]

/-- `mixToken` is a perfect-coordination SPI (Definition 6). -/
lemma mixToken_isSPI : mixToken.IsSPI mixRepresentatives.toPlay mixRepresentatives.certainty := by
  refine Filter.Eventually.of_forall fun ω => ?_
  show mixBase.u (mixRepresentatives.play mixBase ω) ≤
    mixToken.ue (mixRepresentatives.play mixTok ω)
  rw [mixRepresentatives_play_base]
  cases ω
  · rw [show mixToken.ue (mixRepresentatives.play mixTok false) = mixBase.u (pair 0 0) from
      mixToken_ue_false]
  · rw [show mixToken.ue (mixRepresentatives.play mixTok true) = mixBase.u (pair 1 1) from
      mixToken_ue_true]
    intro i; cases i <;> · show ((0 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ); norm_num

lemma mixRepresentatives_fiber_base :
    mixRepresentatives.fiber mixBase (pair 0 0) = Set.univ := by
  ext ω; simp [Representatives.fiber, mixRepresentatives_play_base]

lemma mixBase_mem_support : (pair 0 0 : ∀ i, MixUniverse i) ∈ mixRepresentatives.support mixBase := by
  show mixRepresentatives.μ {ω | mixRepresentatives.play mixBase ω = pair 0 0} ≠ 0
  have h : {ω | mixRepresentatives.play mixBase ω = (pair 0 0 : ∀ i, MixUniverse i)} = Set.univ :=
    mixRepresentatives_fiber_base
  rw [h, show mixRepresentatives.μ Set.univ = 1 from measure_univ]
  exact one_ne_zero

/-- **`condExp` is a genuine average, not a point mass** (R5-F11): on the supported fiber
`Π(mixBase) = (0, 0)` — which is the whole sample space — the conditional expectation of the
token payoff is `(½, ½)`, while the token payoff itself only ever takes the values `(0, 0)`
and `(1, 1)`.  Every *book* model of this development collapses `condExp` to a point
evaluation (pages are chosen per isomorphism class, so the token play is a function of
`Π(Γ)`); this hand-built family is the witness that the definition does not. -/
lemma condExp_genuine_average (i : Two) :
    mixRepresentatives.condExp mixBase (pair 0 0)
      (fun ω => mixToken.ue (mixRepresentatives.play mixToken.game ω)) i = 2⁻¹ := by
  have hcond : mixRepresentatives.μ[|mixRepresentatives.fiber mixBase (pair 0 0)]
      = mixRepresentatives.μ := by
    rw [mixRepresentatives_fiber_base, cond_univ]
  unfold Representatives.condExp
  rw [hcond, eval_integral
    (fun j => (mixRepresentatives.integrable_comp_play_pi mixToken.game mixToken.ue _).eval j) i]
  show (∫ ω, mixToken.ue (mixRepresentatives.play mixTok ω) i ∂coin) = 2⁻¹
  rw [integral_coin,
    show mixToken.ue (mixRepresentatives.play mixTok true) = mixBase.u (pair 1 1) from
      mixToken_ue_true,
    show mixToken.ue (mixRepresentatives.play mixTok false) = mixBase.u (pair 0 0) from
      mixToken_ue_false]
  cases i <;> · show 2⁻¹ * (((1 : ℕ) : ℝ) + ((0 : ℕ) : ℝ)) = 2⁻¹; norm_num

/-- The conditional expectation is a value the integrand never takes. -/
lemma condExp_ne_values :
    mixRepresentatives.condExp mixBase (pair 0 0)
        (fun ω => mixToken.ue (mixRepresentatives.play mixToken.game ω)) ≠
      mixToken.ue (mixRepresentatives.play mixToken.game true) ∧
    mixRepresentatives.condExp mixBase (pair 0 0)
        (fun ω => mixToken.ue (mixRepresentatives.play mixToken.game ω)) ≠
      mixToken.ue (mixRepresentatives.play mixToken.game false) := by
  constructor <;> intro h <;> have := congrFun h Two.one <;>
    rw [condExp_genuine_average] at this
  · rw [mixToken_ue_true] at this; revert this; show ¬ (2⁻¹ = ((1 : ℕ) : ℝ)); norm_num
  · rw [mixToken_ue_false] at this; revert this; show ¬ (2⁻¹ = ((0 : ℕ) : ℝ)); norm_num

end Examples

end SafeParetoImprovements
