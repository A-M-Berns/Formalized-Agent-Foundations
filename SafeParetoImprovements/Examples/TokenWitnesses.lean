import SafeParetoImprovements.Coordination
import SafeParetoImprovements.Book
import SafeParetoImprovements.Examples.TwoPlayer
import SafeParetoImprovements.Examples.Coin

/-!
# Definition 6 has inhabitants: a strict perfect-coordination SPI (§5.1)

Proposition 16 (`Examples/Chicken.lean`) says a particular Pareto improvement is *not*
achievable by a perfect-coordination SPI.  This file supplies the other side of Definition 6
— token games that **are** perfect-coordination SPIs, one of them strictly so — so that
`TokenGame.IsSPI` and `TokenGame.IsStrictSPI` are two-sided rather than provably-false
predicates (R4-F05).  Table 7 cannot host the strict witness: there the two default
outcomes are already Pareto-optimal in `C(Γ)`, so no strict improvement exists at all.

The base game `conflictGame` is a reduced `2 × 2` game over `Bool ⊕ ℕ` (`dd:room`), with

|         | `y` | `x` |
|---|---|---|
| **`y`** | `(1, 1)` | `(0, 3)` |
| **`x`** | `(3, 0)` | `(0, 0)` |

reading `x = inl false` (the conflict action) and `y = inl true`.  The representatives are
the fair-coin book playing `(x, x)` and `(y, y)` with probability ½ each, so Assumptions 1
and 2 hold (`Book.satisfiesA1/2`).  The token game is an explicit fresh copy
`conflictTokenCopy` of the base game, reduced by `Game.Reduced.of_iso`, and

* `conflictPlainToken` assigns each token outcome the payoff of the outcome it copies.  It
  is a perfect-coordination SPI with **equality** at every sample point, hence not strict.
* `conflictStrictToken` assigns the same, **except** at the token image of the conflict
  outcome `(x, x)`, where it assigns `u(y, y) = (1, 1)`.  This is the paper's own
  Demand-Game recipe ("`uᵉ = uˢ` except at the conflict outcome", §5.1 l. 1315–1333), and it
  is a *strict* perfect-coordination SPI.

## `uᵉ` is defined along the book's isomorphism (erratum D6, RULING 10)

The representatives play the token copy through the book's chosen translation, so the token
outcome at sample point `ω` is `conflictBookIso.map (conflictPages ω)`, where
`conflictBookIso` is the composite of the two `Game.chosenIso`s (a `Classical.choice`, but a
definable *term*).  `uᵉ` is therefore defined **after** that isomorphism is known — as a
function of `conflictBookIso.symm.map b` — rather than before it.  This is the only reading
under which Definition 6 has non-degenerate witnesses at all: `uᵉ` must be able to name the
token outcome the representatives will actually reach, and which token outcome that is is
decided by the book.  See erratum D6 and RULING 10.

`conflictStrictToken`'s `uᵉ` takes several distinct values (`conflictStrictToken_ue_ne`), so
the witness is not a constant `uᵉ` in disguise: the improvement genuinely depends on the
token outcome.
-/

namespace SafeParetoImprovements

namespace Examples

open Filter MeasureTheory Two

/-- Both players choose from `Bool ⊕ ℕ`: the two board actions in the `inl` copy, and
infinitely many spare actions for token games (`dd:room`). -/
abbrev CGUniverse : Two → Type := fun _ => Bool ⊕ ℕ

/-- `inl false` = `x`, the conflict action; `inl true` = `y`.  Off the board, `0`
(`dd:total-utility`). -/
def conflictPayoff : Bool ⊕ ℕ → Bool ⊕ ℕ → Two → ℝ
  | Sum.inl false, Sum.inl false, _ => 0
  | Sum.inl false, Sum.inl true, .one => 3
  | Sum.inl false, Sum.inl true, .two => 0
  | Sum.inl true, Sum.inl false, .one => 0
  | Sum.inl true, Sum.inl false, .two => 3
  | Sum.inl true, Sum.inl true, _ => 1
  | _, _, _ => 0

/-- The base game: a reduced `2 × 2` game whose conflict outcome `(x, x)` is worth `(0, 0)`,
Pareto-suboptimal in `C(Γ)` (which contains `(1, 1)`). -/
def conflictGame : Game Two CGUniverse where
  S _ := {Sum.inl false, Sum.inl true}
  nonempty _ := ⟨Sum.inl false, by simp⟩
  u z i := conflictPayoff (z .one) (z .two) i

@[simp] lemma conflictGame_S (i : Two) :
    conflictGame.S i = {Sum.inl false, Sum.inl true} := rfl

lemma conflictGame_mem_S {i : Two} {z : Bool ⊕ ℕ} :
    z ∈ conflictGame.S i ↔ z = Sum.inl false ∨ z = Sum.inl true := by simp

lemma conflictGame_u_inl (p q : Bool) (i : Two) :
    conflictGame.u (pair (Sum.inl p) (Sum.inl q)) i = conflictPayoff (Sum.inl p) (Sum.inl q) i :=
  rfl

lemma conflictGame_reduced : conflictGame.Reduced := by
  rw [reduced_iff]
  constructor
  · rintro z ⟨z', h⟩
    rw [strictlyDominates_one_iff] at h
    obtain ⟨hz', hz, hlt⟩ := h
    rw [conflictGame_mem_S] at hz hz'
    rcases hz with rfl | rfl <;> rcases hz' with rfl | rfl
    · exact lt_irrefl _ (hlt _ (conflictGame_mem_S.2 (Or.inl rfl)))
    · have := hlt _ (conflictGame_mem_S.2 (Or.inl rfl))
      norm_num [conflictGame_u_inl, conflictPayoff] at this
    · have := hlt _ (conflictGame_mem_S.2 (Or.inl rfl))
      norm_num [conflictGame_u_inl, conflictPayoff] at this
    · exact lt_irrefl _ (hlt _ (conflictGame_mem_S.2 (Or.inl rfl)))
  · rintro z ⟨z', h⟩
    rw [strictlyDominates_two_iff] at h
    obtain ⟨hz', hz, hlt⟩ := h
    rw [conflictGame_mem_S] at hz hz'
    rcases hz with rfl | rfl <;> rcases hz' with rfl | rfl
    · exact lt_irrefl _ (hlt _ (conflictGame_mem_S.2 (Or.inl rfl)))
    · have := hlt _ (conflictGame_mem_S.2 (Or.inl rfl))
      norm_num [conflictGame_u_inl, conflictPayoff] at this
    · have := hlt _ (conflictGame_mem_S.2 (Or.inl rfl))
      norm_num [conflictGame_u_inl, conflictPayoff] at this
    · exact lt_irrefl _ (hlt _ (conflictGame_mem_S.2 (Or.inl rfl)))

/-! ### An explicit fresh token copy -/

/-- The token map: `x ↦ inr 0`, `y ↦ inr 1`. -/
def conflictTokenFun : Bool ⊕ ℕ → Bool ⊕ ℕ :=
  Sum.elim (fun p => Sum.inr (if p then 1 else 0)) (fun n => Sum.inr (n + 2))

/-- Its inverse on the tokens; the junk value off them is never read (`tokenCopy.S` is the
image, and payoffs are only evaluated at profiles). -/
def conflictUntoken : Bool ⊕ ℕ → Bool ⊕ ℕ :=
  Sum.elim Sum.inl (fun n => if n = 0 then Sum.inl false else Sum.inl true)

/-- The token copy `(Â, û)` of the base game. -/
def conflictTokenCopy : Game Two CGUniverse where
  S _ := {Sum.inr 0, Sum.inr 1}
  nonempty _ := ⟨Sum.inr 0, by simp⟩
  u b i := conflictGame.u (fun j => conflictUntoken (b j)) i

@[simp] lemma conflictTokenCopy_S (i : Two) :
    conflictTokenCopy.S i = {Sum.inr 0, Sum.inr 1} := rfl

/-- The relabelling isomorphism `conflictGame ≅ conflictTokenCopy`. -/
def conflictHatIso : GameIso conflictGame conflictTokenCopy where
  toFun _ := conflictTokenFun
  bijOn i := by
    refine ⟨?_, ?_, ?_⟩
    · intro z hz
      rcases conflictGame_mem_S.1 (Finset.mem_coe.1 hz) with rfl | rfl <;>
        simp [conflictTokenFun]
    · intro z hz w hw hzw
      rcases conflictGame_mem_S.1 (Finset.mem_coe.1 hz) with rfl | rfl <;>
        rcases conflictGame_mem_S.1 (Finset.mem_coe.1 hw) with rfl | rfl <;>
          simp_all [conflictTokenFun]
    · intro w hw
      simp only [conflictTokenCopy_S, Finset.coe_insert, Set.mem_insert_iff,
        Finset.coe_singleton, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl
      · exact ⟨Sum.inl false, by simp, by simp [conflictTokenFun]⟩
      · exact ⟨Sum.inl true, by simp, by simp [conflictTokenFun]⟩
  scale _ := 1
  scale_pos _ := one_pos
  shift _ := 0
  affine z hz i := by
    have h1 := conflictGame_mem_S.1 (hz .one)
    have h2 := conflictGame_mem_S.1 (hz .two)
    show conflictGame.u z i =
      1 * conflictGame.u (fun j => conflictUntoken (conflictTokenFun (z j))) i + 0
    rw [Two.eq_pair z]
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1, h2] <;>
      norm_num [conflictTokenFun, conflictUntoken, pair, conflictGame_u_inl, conflictGame]

lemma conflictTokenCopy_reduced : conflictTokenCopy.Reduced :=
  Game.Reduced.of_iso conflictHatIso conflictGame_reduced

lemma conflictTokenCopy_fresh (i : Two) :
    Disjoint (conflictTokenCopy.S i) (conflictGame.S i) := by
  rw [Finset.disjoint_left]
  intro z hz
  simp only [conflictTokenCopy_S, Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl <;> simp

/-! ### The representatives -/

/-- Heads: the conflict outcome `(x, x)`.  Tails: `(y, y)`. -/
def conflictPages : Bool → ∀ i, CGUniverse i
  | true => pair (Sum.inl false) (Sum.inl false)
  | false => pair (Sum.inl true) (Sum.inl true)

lemma conflictPages_mem : ∀ ω, conflictPages ω ∈ conflictGame.profiles := by
  intro ω i; cases ω <;> cases i <;> simp [conflictPages, pair]

noncomputable def conflictBook : Book Two CGUniverse Bool :=
  Book.prescribedRandom conflictGame conflictPages_mem

noncomputable def conflictRepresentatives : Representatives.{0, 0, 0} Two CGUniverse :=
  conflictBook.toRepresentatives (μ := coin) (fun _ _ => trivial)

lemma conflictTokenCopy_cls : conflictTokenCopy.cls = conflictGame.cls :=
  (Game.cls_eq_of_isomorphic ⟨conflictHatIso⟩).symm

/-- The isomorphism the **book** actually uses between the base game and its token copy —
the composite of the two chosen translations.  `uᵉ` is defined along this (erratum D6). -/
noncomputable def conflictBookIso : GameIso conflictGame conflictTokenCopy :=
  (conflictGame.chosenIso conflictGame.cls rfl).trans
    (conflictTokenCopy.chosenIso conflictGame.cls conflictTokenCopy_cls).symm

lemma conflictBook_page (ω : Bool) :
    conflictBook.page conflictGame.cls ω =
      (conflictGame.chosenIso conflictGame.cls rfl).map (conflictPages ω) := by
  show (open Classical in
    if h : conflictGame.cls = conflictGame.cls then
      (conflictGame.chosenIso conflictGame.cls h).map (conflictPages ω)
    else (conflictGame.cls.rep.profiles_nonempty).choose) = _
  rw [dif_pos rfl]

/-- The representatives' play of the token copy is the book's translation of the page. -/
lemma conflictRepresentatives_play_hat (ω : Bool) :
    conflictRepresentatives.toPlay.play conflictTokenCopy ω =
      conflictBookIso.map (conflictPages ω) := by
  show conflictBook.playReduced conflictTokenCopy.reduce ω = _
  rw [Game.reduce_of_reduced conflictTokenCopy_reduced,
    ← Book.chosenIso_symm_map_page conflictBook conflictTokenCopy conflictGame.cls
      conflictTokenCopy_cls ω, conflictBook_page]
  rfl

lemma conflictRepresentatives_play (ω : Bool) :
    conflictRepresentatives.toPlay.play conflictGame ω = conflictPages ω :=
  Book.prescribedRandom_play conflictGame conflictPages_mem conflictGame
    (Game.reduce_of_reduced conflictGame_reduced) ω

/-! ### A perfect-coordination SPI that is not strict -/

/-- The token copy with `uᵉ` the transported payoff: **`TokenGame.IsSPI` is not
constant-false**. -/
noncomputable def conflictPlainToken : TokenGame conflictGame where
  game := conflictTokenCopy
  fresh := conflictTokenCopy_fresh
  ue b := conflictGame.u (conflictBookIso.symm.map b)
  ue_mem _b hb := conflictGame.u_mem_feasible (conflictBookIso.symm.map_mem hb)

lemma conflictPlainToken_isSPI :
    conflictPlainToken.IsSPI conflictRepresentatives.toPlay conflictRepresentatives.certainty := by
  refine Filter.Eventually.of_forall fun ω => ?_
  show conflictGame.u (conflictRepresentatives.toPlay.play conflictGame ω) ≤
    conflictGame.u (conflictBookIso.symm.map
      (conflictRepresentatives.toPlay.play conflictTokenCopy ω))
  rw [conflictRepresentatives_play, conflictRepresentatives_play_hat,
    conflictBookIso.symm_map_map (conflictPages_mem ω)]

/-- …but not a *strict* one: `uᵉ(Π(Aˢ, uˢ)) = u(Π(Γ))` at every sample point. -/
lemma conflictPlainToken_not_isStrictSPI :
    ¬ conflictPlainToken.IsStrictSPI conflictRepresentatives.toPlay
      conflictRepresentatives.certainty := by
  rintro ⟨-, i, hfreq⟩
  obtain ⟨ω, hω⟩ := hfreq.exists
  have h1 : conflictRepresentatives.toPlay.play conflictGame ω = conflictPages ω :=
    conflictRepresentatives_play ω
  have h2 : conflictRepresentatives.toPlay.play conflictPlainToken.game ω =
      conflictBookIso.map (conflictPages ω) := conflictRepresentatives_play_hat ω
  rw [h1, h2] at hω
  have h3 : conflictPlainToken.ue (conflictBookIso.map (conflictPages ω)) =
      conflictGame.u (conflictPages ω) := by
    show conflictGame.u (conflictBookIso.symm.map (conflictBookIso.map (conflictPages ω))) = _
    rw [conflictBookIso.symm_map_map (conflictPages_mem ω)]
  rw [h3] at hω
  exact lt_irrefl _ hω

/-! ### A strict perfect-coordination SPI -/

/-- The value assigned to the conflict token outcome: `u(y, y) = (1, 1)`. -/
noncomputable def conflictImproved : Two → ℝ :=
  conflictGame.u (pair (Sum.inl true) (Sum.inl true))

/-- `uᵉ`: the transported payoff, except at the token image of the conflict outcome. -/
noncomputable def conflictStrictUe (b : ∀ i, CGUniverse i) : Two → ℝ :=
  open Classical in
  if b = conflictBookIso.map (conflictPages true) then conflictImproved
  else conflictGame.u (conflictBookIso.symm.map b)

/-- The paper's Demand-Game recipe: `uᵉ = uˢ` except at the conflict outcome. -/
noncomputable def conflictStrictToken : TokenGame conflictGame where
  game := conflictTokenCopy
  fresh := conflictTokenCopy_fresh
  ue := conflictStrictUe
  ue_mem _b hb := by
    classical
    unfold conflictStrictUe
    split
    · exact conflictGame.u_mem_feasible (conflictPages_mem false)
    · exact conflictGame.u_mem_feasible (conflictBookIso.symm.map_mem hb)

lemma conflictPages_ne : conflictPages true ≠ conflictPages false := by
  intro h
  have := congrFun h Two.one
  simp [conflictPages, pair] at this

lemma conflictStrictUe_tails :
    conflictStrictUe (conflictBookIso.map (conflictPages false)) =
      conflictGame.u (conflictPages false) := by
  classical
  unfold conflictStrictUe
  rw [if_neg]
  · rw [conflictBookIso.symm_map_map (conflictPages_mem false)]
  · intro h
    exact conflictPages_ne (conflictBookIso.map_injOn (conflictPages_mem true)
      (conflictPages_mem false) h.symm)

lemma conflictStrictUe_heads :
    conflictStrictUe (conflictBookIso.map (conflictPages true)) = conflictImproved := by
  classical
  unfold conflictStrictUe
  rw [if_pos rfl]

lemma conflictStrictToken_isSPI :
    conflictStrictToken.IsSPI conflictRepresentatives.toPlay
      conflictRepresentatives.certainty := by
  refine Filter.Eventually.of_forall fun ω => ?_
  show conflictGame.u (conflictRepresentatives.toPlay.play conflictGame ω) ≤
    conflictStrictUe (conflictRepresentatives.toPlay.play conflictTokenCopy ω)
  rw [conflictRepresentatives_play, conflictRepresentatives_play_hat]
  cases ω
  · rw [conflictStrictUe_tails]
  · rw [conflictStrictUe_heads]
    intro i
    show conflictGame.u (conflictPages true) i ≤
      conflictGame.u (pair (Sum.inl true) (Sum.inl true)) i
    cases i <;> norm_num [conflictPages, conflictGame_u_inl, conflictPayoff]

/-- **Definition 6's strict clause has a non-degenerate witness.**  Both players do at
least as well with certainty, and player 1 does strictly better with positive probability —
on heads, where the conflict outcome `(0, 0)` is replaced by `(1, 1)`. -/
lemma conflictStrictToken_isStrictSPI :
    conflictStrictToken.IsStrictSPI conflictRepresentatives.toPlay
      conflictRepresentatives.certainty := by
  refine ⟨conflictStrictToken_isSPI, Two.one, ?_⟩
  intro hcon
  have h := ((ae_coin_iff _).1 hcon).1
  apply h
  have h1 : conflictRepresentatives.toPlay.play conflictGame true = conflictPages true :=
    conflictRepresentatives_play true
  have h2 : conflictRepresentatives.toPlay.play conflictStrictToken.game true =
      conflictBookIso.map (conflictPages true) := conflictRepresentatives_play_hat true
  rw [h1, h2]
  show conflictGame.u (conflictPages true) Two.one <
    conflictStrictUe (conflictBookIso.map (conflictPages true)) Two.one
  rw [conflictStrictUe_heads]
  show conflictGame.u (conflictPages true) Two.one <
    conflictGame.u (pair (Sum.inl true) (Sum.inl true)) Two.one
  norm_num [conflictPages, conflictGame_u_inl, conflictPayoff]

/-- `uᵉ` is genuinely non-constant on the token outcomes: the witness is not a constant
`uᵉ` in disguise, and the improvement depends on which token outcome is reached. -/
lemma conflictStrictToken_ue_ne :
    conflictStrictUe (conflictBookIso.map (conflictPages true)) ≠
      conflictStrictUe (conflictBookIso.map (pair (Sum.inl false) (Sum.inl true))) := by
  classical
  rw [conflictStrictUe_heads]
  have hmem : (pair (Sum.inl false) (Sum.inl true) : ∀ i, CGUniverse i) ∈
      conflictGame.profiles := by
    intro i; cases i <;> simp [pair]
  have hne : (pair (Sum.inl false) (Sum.inl true) : ∀ i, CGUniverse i) ≠
      conflictPages true := by
    intro h
    have := congrFun h Two.two
    simp [conflictPages, pair] at this
  have hval : conflictStrictUe (conflictBookIso.map (pair (Sum.inl false) (Sum.inl true))) =
      conflictGame.u (pair (Sum.inl false) (Sum.inl true)) := by
    unfold conflictStrictUe
    rw [if_neg, conflictBookIso.symm_map_map hmem]
    intro h
    exact hne (conflictBookIso.map_injOn hmem (conflictPages_mem true) h)
  rw [hval]
  intro hcon
  have := congrFun hcon Two.one
  simp only [conflictImproved] at this
  norm_num [conflictGame_u_inl, conflictPayoff, pair] at this

end Examples

end SafeParetoImprovements
