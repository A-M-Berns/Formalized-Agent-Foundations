import SafeParetoImprovements.Complexity
import SafeParetoImprovements.Examples.TwoPlayer

/-!
# The SPI decision problems are as hard as subgraph isomorphism (Appendix D.3)

The hardness half of Theorem 9, carried as a *qualified* node (`dd:complexity`, RULING 6;
design note `notes/complexity-layer.md` §4).  Appendix D.3 reduces the subgraph
isomorphism problem (Definition 8) to the two-player SPI decision problems: from graphs
`G = (n, a)` and `Ĝ = (n̂, â)` it builds the games `Γ` and `Γ̂` of Table 9 and glues them
into the game `Γᶜ` of Table 10, and Lemma 28 says that `G` embeds in `Ĝ` iff `Γᶜ` has a
(strict) (unilateral) SPI.  That equivalence is what is rendered, four times over, as
`subgraphIsoProblem_iff_spiDecision` and its strict, unilateral, and strict-unilateral
variants; "in linear time with linear increase in problem instance size" and "NP-hard"
(which needs Lemma 27, Cook's theorem for subgraph isomorphism, cited and not carried) are
the clauses not rendered.

Three modelling notes, all recorded in the design note.  The paper's `[2n+2]` is carried
as `Fin n ⊕ Fin n ⊕ Bool` — the block `[n]`, the block `{n+1, …, 2n}` written `j ↦ n+j`,
and the two corner actions `2n+1` (`false`) and `2n+2` (`true`) — so that the payoff
formula is a case split.  The printed formula and Table 9 disagree at eight entries
(player 1 in columns `2n+1, 2n+2` against rows `[2n]`, player 2 symmetrically: the formula
says `ε`, the table `0`); the disagreement is material, because with `ε` no column of the
unilateral candidate is ever strictly dominated once the corner rows are present, and the
carrier follows the **table**, under which the printed proof checks (erratum D18).  And
the reduction's second half is organised around the product structure of an isomorphism
rather than the printed items (a)–(d): with non-triviality read as "the reduced action
sets move" (`dd:nontrivial`), the case in which `Ψ` keeps to the `Γ` block is dismissed
outright, and the printed `ε`-ladder is not needed.

The hypotheses on `ε` are the paper's `0 < ε < 1/(2n)` for `Γ` and `ε < 1/(2n̂)` for `Γ̂`;
`n ≥ 1` replaces the printed "WLOG `n, n̂ ≥ 2`" and is needed only for the strict problems
(with `n = 0` the empty subgraph isomorphism exists but no strict SPI does).

* `Hardness.Graph`, `SubgraphIso`, `SubgraphIsoProblem` — Definition 8.
* `Hardness.tableU₁`, `tableU₂` — Table 9's payoffs, with the shift `δ` that turns `Γ`
  into `Γ̂`.
* `Hardness.hardnessGame` — Table 10's `Γᶜ`; `gammaBlock` its `Γ` block, which is its
  full reduction (`reduce_hardnessGame`).
* `Hardness.subgraphIsoProblem_iff_spiDecision` and the three variants — Lemma 28;
  `size_hardnessGame` — the instance size.
* `Hardness.theorem9` — Theorem 9's carrier: membership (Propositions 23 and 25) and the
  reduction, over two-player games.
-/

namespace SafeParetoImprovements

namespace Hardness

open Examples Examples.Two Set

/-! ### Graphs and subgraph isomorphism (Definition 8) -/

/-- A simple directed graph on the vertex set `[n]`, given by its adjacency function
(Appendix D.3: `(n, a : [n] × [n] → 𝔹)`; the diagonal values are meaningless). -/
abbrev Graph (n : ℕ) := Fin n → Fin n → Bool

/-- `φ` is a **subgraph isomorphism** from `G = (n, a)` to `G' = (n', a')`: an injection of
vertices with `a(j, l) ≤ a'(φ(j), φ(l))` for all `j ≠ l`. -/
def SubgraphIso {n n' : ℕ} (a : Graph n) (a' : Graph n') (φ : Fin n ↪ Fin n') : Prop :=
  ∀ j l, j ≠ l → a j l ≤ a' (φ j) (φ l)

/-- **The subgraph isomorphism problem**: is there a subgraph isomorphism from `G` to `G'`?

Paper node: `Definition 8` -/
def SubgraphIsoProblem {n n' : ℕ} (a : Graph n) (a' : Graph n') : Prop :=
  ∃ φ : Fin n ↪ Fin n', SubgraphIso a a' φ

/-! ### Table 9 -/

/-- The `2n+2` actions of Table 9: the block `[n]`, the block `{n+1, …, 2n}` (written by its
offset `j ↦ n+j`), and the corners `2n+1` (`false`) and `2n+2` (`true`). -/
abbrev TableAct (n : ℕ) := Fin n ⊕ Fin n ⊕ Bool

/-- The corner action `2n+1`. -/
abbrev TableAct.c₁ {n : ℕ} : TableAct n := Sum.inr (Sum.inr false)

/-- The corner action `2n+2`. -/
abbrev TableAct.c₂ {n : ℕ} : TableAct n := Sum.inr (Sum.inr true)

/-- The adjacency value as a real number. -/
def adj {n : ℕ} (a : Graph n) (i j : Fin n) : ℝ := if a i j then 1 else 0

/-- Table 9, player 1's payoffs `u₁(i, j)`, with the shift `δ` that distinguishes `Γ`
(`δ = 0`) from `Γ̂` (`δ = 1`: "5 instead of 4 … and 4 instead of 3").  The corner columns
against the rows `[2n]` are `0`, as the table prints (erratum D18). -/
def tableU₁ {n : ℕ} (a : Graph n) (ε δ : ℝ) : TableAct n → TableAct n → ℝ
  | .inl i, .inl j => if i = j then 2 else adj a i j
  | .inl i, .inr (.inl j) => if i = j then 4 + δ + (n + ((i : ℕ) + 1)) * ε else -1
  | .inl _, .inr (.inr _) => 0
  | .inr (.inl i), .inl j => if i = j then 4 + δ + ((j : ℕ) + 1) * ε else -1
  | .inr (.inl _), .inr (.inl _) => -1
  | .inr (.inl _), .inr (.inr _) => 0
  | .inr (.inr _), .inl _ => 3 + δ
  | .inr (.inr _), .inr (.inl _) => 3 + δ
  | .inr (.inr b), .inr (.inr b') => if b = false ∧ b' = false then 6 else ε

/-- Table 9, player 2's payoffs `u₂(i, j)` (the same in `Γ` and `Γ̂`).  The corner rows
against the columns `[2n]` are `0`, as the table prints (erratum D18). -/
def tableU₂ (n : ℕ) (ε : ℝ) : TableAct n → TableAct n → ℝ
  | .inl i, .inl j => if i = j then 2 else 1
  | .inl i, .inr (.inl j) => if i = j then 4 else -1
  | .inl _, .inr (.inr _) => 3
  | .inr (.inl i), .inl j => if i = j then 4 else -1
  | .inr (.inl _), .inr (.inl _) => -1
  | .inr (.inl _), .inr (.inr _) => 3
  | .inr (.inr _), .inl _ => 0
  | .inr (.inr _), .inr (.inl _) => 0
  | .inr (.inr b), .inr (.inr b') => if b = true ∧ b' = true then 6 else ε

/-! ### Table 10 -/

/-- The actions of `Γᶜ`: for player 1, `{T} × [2n+2] ⊔ {R} × [2n̂+2]`; for player 2,
`{D} × [2n+2] ⊔ {P} × [2n̂+2]`. -/
abbrev HardAct (n n' : ℕ) := TableAct n ⊕ TableAct n'

/-- The action universe of `Γᶜ`, the same for both players. -/
abbrev HardUniverse (n n' : ℕ) : Two → Type := fun _ => HardAct n n'

/-- Table 10's payoffs: `Γ` on `T × D`, `Γ̂` on `R × P`, `(−2, −1)` on `R × D`, `(10, −10)`
on `T × P`. -/
def hardU {n n' : ℕ} (a : Graph n) (a' : Graph n') (ε : ℝ) :
    HardAct n n' → HardAct n n' → Two → ℝ
  | .inl i, .inl j => pair (tableU₁ a ε 0 i j) (tableU₂ n ε i j)
  | .inr i, .inr j => pair (tableU₁ a' ε 1 i j) (tableU₂ n' ε i j)
  | .inr _, .inl _ => pair (-2) (-1)
  | .inl _, .inr _ => pair 10 (-10)

/-- **The game `Γᶜ`** of Table 10, built from `G = (n, a)` and `Ĝ = (n̂, â)`. -/
def hardnessGame {n n' : ℕ} (a : Graph n) (a' : Graph n') (ε : ℝ) :
    Game Two (HardUniverse n n') where
  S _ := Finset.univ
  nonempty _ := ⟨Sum.inl TableAct.c₁, Finset.mem_univ _⟩
  u x := hardU a a' ε (x .one) (x .two)

/-- The `Γ` block of `Γᶜ`: the actions `{T} × [2n+2]` and `{D} × [2n+2]`. -/
def blockActions (n n' : ℕ) : Finset (HardAct n n') := Finset.univ.map Function.Embedding.inl

/-- The `Γ` part of `Γᶜ` as a subset game, "the game resulting from iterated elimination of
strictly dominated strategies" (`reduce_hardnessGame`). -/
def gammaBlock {n n' : ℕ} (a : Graph n) (a' : Graph n') (ε : ℝ) : Game Two (HardUniverse n n') where
  S _ := blockActions n n'
  nonempty _ := ⟨Sum.inl TableAct.c₁, by simp [blockActions]⟩
  u := (hardnessGame a a' ε).u

variable {n n' : ℕ} (a : Graph n) (a' : Graph n') (ε : ℝ)

/-- The instance size of the constructed game: `2(2n+2) + 2(2n̂+2)` actions, linear in the
sizes of the two graphs' vertex sets ("linear increase in problem instance size"). -/
lemma size_hardnessGame : (hardnessGame a a' ε).size = 2 * (2 * n + 2) + 2 * (2 * n' + 2) := by
  have h2 : Fintype.card Two = 2 := rfl
  simp [Game.size, hardnessGame, Fintype.card_sum, Fintype.card_fin, Fintype.card_bool, h2]
  ring

@[simp] lemma hardnessGame_S (i : Two) : (hardnessGame a a' ε).S i = Finset.univ := rfl

lemma hardnessGame_u (x y : HardAct n n') :
    (hardnessGame a a' ε).u (pair x y) = hardU a a' ε x y := rfl

@[simp] lemma gammaBlock_S (i : Two) : (gammaBlock a a' ε).S i = blockActions n n' := rfl

lemma gammaBlock_u (x y : HardAct n n') :
    (gammaBlock a a' ε).u (pair x y) = hardU a a' ε x y := rfl

@[simp] lemma mem_blockActions {x : HardAct n n'} : x ∈ blockActions n n' ↔ ∃ t, x = Sum.inl t := by
  simp [blockActions, eq_comm]

lemma inl_mem_blockActions (t : TableAct n) : Sum.inl t ∈ blockActions n n' := by simp

lemma inr_not_mem_blockActions (t : TableAct n') : Sum.inr t ∉ blockActions n n' := by simp

/-! ### Bounds on the entries of Table 9 -/

section bounds

variable {ε}

lemma block_mul_le {m : ℕ} (hε : 0 ≤ ε) (i : Fin m) :
    ((m : ℝ) + ((i : ℕ) + 1)) * ε ≤ ε * (2 * m) := by
  have : ((i : ℕ) : ℝ) + 1 ≤ m := by exact_mod_cast i.isLt
  nlinarith

lemma succ_mul_le {m : ℕ} (hε : 0 ≤ ε) (i : Fin m) : (((i : ℕ) : ℝ) + 1) * ε ≤ ε * (2 * m) := by
  have : ((i : ℕ) : ℝ) + 1 ≤ m := by exact_mod_cast i.isLt
  nlinarith

lemma block_mul_nonneg {m : ℕ} (hε : 0 ≤ ε) (i : Fin m) : 0 ≤ ((m : ℝ) + ((i : ℕ) + 1)) * ε :=
  mul_nonneg (by positivity) hε

lemma succ_mul_nonneg {m : ℕ} (hε : 0 ≤ ε) (i : Fin m) : 0 ≤ (((i : ℕ) : ℝ) + 1) * ε :=
  mul_nonneg (by positivity) hε

lemma adj_nonneg {m : ℕ} (g : Graph m) (i j : Fin m) : 0 ≤ adj g i j := by
  unfold adj; split_ifs <;> norm_num

lemma adj_le_one {m : ℕ} (g : Graph m) (i j : Fin m) : adj g i j ≤ 1 := by
  unfold adj; split_ifs <;> norm_num

lemma neg_one_le_tableU₁ {m : ℕ} (g : Graph m) (hε : 0 ≤ ε) {δ : ℝ} (hδ : 0 ≤ δ)
    (i j : TableAct m) : -1 ≤ tableU₁ g ε δ i j := by
  have := adj_nonneg g
  rcases i with i | i | b <;> rcases j with j | j | b' <;> simp only [tableU₁] <;> (try split_ifs) <;>
    first | linarith | linarith [this i j] | linarith [block_mul_nonneg hε i] |
      linarith [succ_mul_nonneg hε j]

lemma neg_one_le_tableU₂ {m : ℕ} (hε : 0 ≤ ε) (i j : TableAct m) : -1 ≤ tableU₂ m ε i j := by
  rcases i with i | i | b <;> rcases j with j | j | b' <;> simp only [tableU₂] <;> (try split_ifs) <;>
    linarith

lemma tableU₁_le_six {m : ℕ} (g : Graph m) (hε : 0 ≤ ε) (hε6 : ε ≤ 6) (hεm : ε * (2 * m) < 1)
    {δ : ℝ} (hδ : δ ≤ 1) (i j : TableAct m) : tableU₁ g ε δ i j ≤ 6 := by
  have h1 := adj_le_one g
  rcases i with i | i | b <;> rcases j with j | j | b' <;> simp only [tableU₁] <;> (try split_ifs) <;>
    first | linarith | linarith [h1 i j] | linarith [block_mul_le hε i] | linarith [succ_mul_le hε j]

lemma neg_one_lt_tableU₂_c₁ {m : ℕ} (hε : 0 < ε) (s : TableAct m) :
    -1 < tableU₂ m ε s TableAct.c₁ := by
  rcases s with i | i | b <;> simp [tableU₂] <;> linarith

end bounds

/-! ### The full reduction of `Γᶜ` is its `Γ` block -/

/-- The `Γ` block is reduced: every action is a (weak) best response to some opponent
action — the `[n]` and `{n+1, …, 2n}` actions to their partners, the corners to
themselves. -/
lemma gammaBlock_reduced (hε : 0 < ε) (hε1 : ε < 1) : (gammaBlock a a' ε).Reduced := by
  rw [reduced_iff]
  constructor
  · intro x hx
    obtain ⟨t, rfl⟩ := mem_blockActions.1 hx.mem
    revert hx
    rcases t with i | i | b
    · refine not_isStrictlyDominated_one_of_bestResponse _
        (inl_mem_blockActions (Sum.inr (Sum.inl i))) fun x' hx' => ?_
      obtain ⟨t', rfl⟩ := mem_blockActions.1 hx'
      rcases t' with i' | i' | b' <;> simp only [gammaBlock_u, hardU, pair_one, tableU₁] <;> (try split_ifs) <;>
        (try subst_vars) <;>
        first | linarith | linarith [block_mul_nonneg hε.le i]
    · refine not_isStrictlyDominated_one_of_bestResponse _
        (inl_mem_blockActions (Sum.inl i)) fun x' hx' => ?_
      obtain ⟨t', rfl⟩ := mem_blockActions.1 hx'
      rcases t' with i' | i' | b' <;> simp only [gammaBlock_u, hardU, pair_one, tableU₁] <;> (try split_ifs) <;>
        (try subst_vars) <;>
        first | linarith | linarith [succ_mul_nonneg hε.le i] | linarith [succ_mul_nonneg hε.le i'] |
          linarith [succ_mul_nonneg hε.le i, adj_le_one a i' i]
    · refine not_isStrictlyDominated_one_of_bestResponse _
        (inl_mem_blockActions (Sum.inr (Sum.inr b))) fun x' hx' => ?_
      obtain ⟨t', rfl⟩ := mem_blockActions.1 hx'
      rcases t' with i' | i' | b' <;> cases b <;> (try cases b') <;>
        simp only [gammaBlock_u, hardU, pair_one, tableU₁] <;> (try split_ifs) <;> first | linarith | simp_all
  · intro x hx
    obtain ⟨t, rfl⟩ := mem_blockActions.1 hx.mem
    revert hx
    rcases t with j | j | b
    · refine not_isStrictlyDominated_two_of_bestResponse _
        (inl_mem_blockActions (Sum.inr (Sum.inl j))) fun x' hx' => ?_
      obtain ⟨t', rfl⟩ := mem_blockActions.1 hx'
      rcases t' with j' | j' | b' <;> simp only [gammaBlock_u, hardU, pair_two, tableU₂] <;> (try split_ifs) <;>
        (try subst_vars) <;> linarith
    · refine not_isStrictlyDominated_two_of_bestResponse _
        (inl_mem_blockActions (Sum.inl j)) fun x' hx' => ?_
      obtain ⟨t', rfl⟩ := mem_blockActions.1 hx'
      rcases t' with j' | j' | b' <;> simp only [gammaBlock_u, hardU, pair_two, tableU₂] <;> (try split_ifs) <;>
        (try subst_vars) <;> linarith
    · refine not_isStrictlyDominated_two_of_bestResponse _
        (inl_mem_blockActions (Sum.inr (Sum.inr b))) fun x' hx' => ?_
      obtain ⟨t', rfl⟩ := mem_blockActions.1 hx'
      rcases t' with j' | j' | b' <;> cases b <;> (try cases b') <;>
        simp only [gammaBlock_u, hardU, pair_two, tableU₂] <;> (try split_ifs) <;> first | linarith | simp_all

/-- Iterated elimination takes `Γᶜ` to its `Γ` block: every `R` action of player 1 is
strictly dominated by `(T, 2n+1)` (`−2` against `D`, at most `6 < 10` against `P`), then
every `P` action of player 2 by `(D, 2n+1)` (`−10` against `T`), and the block is reduced
(`gammaBlock_reduced`). -/
lemma reduce_hardnessGame (hε : 0 < ε) (hε1 : ε < 1) (hε' : ε * (2 * n') < 1) :
    (hardnessGame a a' ε).reduce = gammaBlock a a' ε := by
  set Γc := hardnessGame a a' ε with hΓc
  let T₁ : ∀ i, Finset (HardUniverse n n' i) := pair (blockActions n n') Finset.univ
  have hne₁ : ∀ i, (T₁ i).Nonempty := by
    intro i; cases i
    · exact ⟨_, inl_mem_blockActions TableAct.c₁⟩
    · exact Finset.univ_nonempty
  have hA : Γc.ElimStar ⟨T₁, hne₁, Γc.u⟩ := by
    refine Game.elimStar_of_dominated Γc T₁ hne₁ (fun i => Finset.subset_univ _)
      fun i x hx hxT => ?_
    cases i
    · obtain ⟨r, rfl⟩ : ∃ r, x = Sum.inr r := by
        rcases x with t | r
        · exact absurd (inl_mem_blockActions t) hxT
        · exact ⟨r, rfl⟩
      refine ⟨Sum.inl TableAct.c₁, inl_mem_blockActions _, ?_⟩
      rw [strictlyDominates_one_iff]
      refine ⟨Finset.mem_univ _, Finset.mem_univ _, fun z _ => ?_⟩
      rcases z with d | p
      · show hardU a a' ε (Sum.inr r) (Sum.inl d) .one <
          hardU a a' ε (Sum.inl TableAct.c₁) (Sum.inl d) .one
        simp only [hardU, pair_one]
        linarith [neg_one_le_tableU₁ a hε.le le_rfl TableAct.c₁ d]
      · show hardU a a' ε (Sum.inr r) (Sum.inr p) .one <
          hardU a a' ε (Sum.inl TableAct.c₁) (Sum.inr p) .one
        simp only [hardU, pair_one]
        linarith [tableU₁_le_six a' hε.le (by linarith) hε' le_rfl r p]
    · exact absurd (Finset.mem_univ x) hxT
  have hB : (⟨T₁, hne₁, Γc.u⟩ : Game Two (HardUniverse n n')).ElimStar (gammaBlock a a' ε) := by
    have hne₂ : ∀ i : Two, (blockActions n n').Nonempty := fun _ =>
      ⟨_, inl_mem_blockActions TableAct.c₁⟩
    have heq : (⟨fun _ => blockActions n n', hne₂, Γc.u⟩ : Game Two (HardUniverse n n')) =
        gammaBlock a a' ε := rfl
    rw [← heq]
    refine Game.elimStar_of_dominated _ (fun _ => blockActions n n') hne₂ (fun i => ?_)
      fun i x hx hxT => ?_
    · cases i
      · exact Finset.Subset.refl _
      · exact Finset.subset_univ _
    · cases i
      · exact absurd hx hxT
      · obtain ⟨p, rfl⟩ : ∃ p, x = Sum.inr p := by
          rcases x with t | p
          · exact absurd (inl_mem_blockActions t) hxT
          · exact ⟨p, rfl⟩
        refine ⟨Sum.inl TableAct.c₁, inl_mem_blockActions _, ?_⟩
        rw [strictlyDominates_two_iff]
        refine ⟨Finset.mem_univ _, Finset.mem_univ _, fun z hz => ?_⟩
        obtain ⟨t, rfl⟩ := mem_blockActions.1 hz
        show hardU a a' ε (Sum.inl t) (Sum.inr p) .two <
          hardU a a' ε (Sum.inl t) (Sum.inl TableAct.c₁) .two
        simp only [hardU, pair_two]
        linarith [neg_one_le_tableU₂ hε.le t TableAct.c₁]
  exact Game.reduce_eq_of_reduced_of_elimStar (hA.trans hB) (gammaBlock_reduced a a' ε hε hε1)

/-! ### From a subgraph isomorphism to a strict unilateral SPI (Lemma 28, first claim) -/

section construction

variable (φ : Fin n ↪ Fin n')

/-- `Ψ` on the actions of Table 9: `i ↦ φ(i)`, `n+i ↦ n̂+φ(i)`, corners to corners. -/
def psiT : TableAct n → TableAct n'
  | .inl i => .inl (φ i)
  | .inr (.inl i) => .inr (.inl (φ i))
  | .inr (.inr b) => .inr (.inr b)

lemma psiT_injective : Function.Injective (psiT φ) := by
  rintro (i | i | b) (j | j | b') h <;> simp only [psiT, Sum.inl.injEq, Sum.inr.injEq,
    reduceCtorEq, φ.apply_eq_iff_eq] at h <;> simp [h]

/-- `Ψ` on the universe of `Γᶜ`: the `T`/`D` block into the `R`/`P` block along `psiT`
(the identity elsewhere, where it is never used). -/
def psi : HardAct n n' → HardAct n n'
  | .inl t => .inr (psiT φ t)
  | .inr x => .inr x

@[simp] lemma psi_inl (t : TableAct n) : psi φ (Sum.inl t) = Sum.inr (psiT φ t) := rfl

/-- Player 2's payoffs are carried exactly by `Ψ` (the printed "each case is trivial"). -/
lemma tableU₂_psiT (t t' : TableAct n) :
    tableU₂ n' ε (psiT φ t) (psiT φ t') = tableU₂ n ε t t' := by
  rcases t with i | i | b <;> rcases t' with j | j | b' <;>
    simp [psiT, tableU₂, φ.apply_eq_iff_eq]

lemma adj_le_adj {i j : Fin n} {k l : Fin n'} (h : a i j ≤ a' k l) : adj a i j ≤ adj a' k l := by
  unfold adj
  cases h1 : a i j <;> cases h2 : a' k l <;> simp only [h1, h2] at h ⊢ <;>
    first | exact absurd h (by decide) | norm_num

variable {ε}

/-- Player 1's payoffs are weakly improved by `Ψ` (the printed case table; the interesting
case `i ≠ j ∈ [n]` is the subgraph condition `a(i, j) ≤ â(φ(i), φ(j))`). -/
lemma tableU₁_le_psiT (hε : 0 ≤ ε) (hεn : ε * (2 * n) < 1) (hφ : SubgraphIso a a' φ)
    (t t' : TableAct n) : tableU₁ a ε 0 t t' ≤ tableU₁ a' ε 1 (psiT φ t) (psiT φ t') := by
  rcases t with i | i | b <;> rcases t' with j | j | b' <;>
    simp only [psiT, tableU₁, φ.apply_eq_iff_eq] <;> (try split_ifs) <;> (try subst_vars) <;>
    first
    | linarith
    | (rename_i hij; exact adj_le_adj a a' (hφ _ _ hij))
    | linarith [block_mul_le hε i, block_mul_nonneg (m := n') hε (φ i)]
    | linarith [succ_mul_le hε j, succ_mul_nonneg (m := n') hε (φ j)]
    | linarith [succ_mul_le hε i, succ_mul_nonneg (m := n') hε (φ i)]
    | linarith [block_mul_le hε j, block_mul_nonneg (m := n') hε (φ j)]

end construction

section certificate

variable (φ : Fin n ↪ Fin n') (hred : (hardnessGame a a' ε).reduce = gammaBlock a a' ε)

include hred

lemma mem_reduce_S_iff (i : Two) (x : HardAct n n') :
    x ∈ (hardnessGame a a' ε).reduce.S i ↔ ∃ t, x = Sum.inl t := by
  rw [hred]; exact mem_blockActions

lemma mem_reduce_profiles_iff (b : ∀ i, HardUniverse n n' i) :
    b ∈ (hardnessGame a a' ε).reduce.profiles ↔
      ∃ t t', b = pair (Sum.inl t) (Sum.inl t') := by
  rw [Game.mem_profiles]
  constructor
  · intro h
    obtain ⟨t, ht⟩ := (mem_reduce_S_iff a a' ε hred .one _).1 (h .one)
    obtain ⟨t', ht'⟩ := (mem_reduce_S_iff a a' ε hred .two _).1 (h .two)
    exact ⟨t, t', by rw [eq_pair b, ht, ht']⟩
  · rintro ⟨t, t', rfl⟩ i
    cases i
    · exact (mem_reduce_S_iff a a' ε hred .one _).2 ⟨t, rfl⟩
    · exact (mem_reduce_S_iff a a' ε hred .two _).2 ⟨t', rfl⟩

/-- The certificate `Ψ` of the appendix's first claim. -/
def cert : (hardnessGame a a' ε).Certificate := fun i =>
  ⟨fun x => ⟨psi φ x.1, Finset.mem_univ _⟩, fun x y hxy => by
    obtain ⟨t, ht⟩ := (mem_reduce_S_iff a a' ε hred i _).1 x.2
    obtain ⟨t', ht'⟩ := (mem_reduce_S_iff a a' ε hred i _).1 y.2
    have h := congrArg Subtype.val hxy
    simp only [ht, ht', psi_inl, Sum.inr.injEq] at h
    exact Subtype.ext (by rw [ht, ht', psiT_injective φ h])⟩

lemma cert_toFun (i : Two) (t : TableAct n) :
    (cert a a' ε φ hred).toFun i (Sum.inl t) = Sum.inr (psiT φ t) := by
  rw [Game.Certificate.toFun_of_mem _ ((mem_reduce_S_iff a a' ε hred i _).2 ⟨t, rfl⟩)]
  rfl

lemma cert_map (t t' : TableAct n) :
    (cert a a' ε φ hred).map (pair (Sum.inl t) (Sum.inl t')) =
      pair (Sum.inr (psiT φ t)) (Sum.inr (psiT φ t')) := by
  funext i
  cases i
  · exact cert_toFun a a' ε φ hred .one t
  · exact cert_toFun a a' ε φ hred .two t'

lemma mem_cert_image_iff (i : Two) (x : HardAct n n') :
    x ∈ (cert a a' ε φ hred).image i ↔ ∃ t, x = Sum.inr (psiT φ t) := by
  simp only [Game.Certificate.image, Finset.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨t, rfl⟩ := (mem_reduce_S_iff a a' ε hred i _).1 hy
    exact ⟨t, cert_toFun a a' ε φ hred i t⟩
  · rintro ⟨t, rfl⟩
    exact ⟨Sum.inl t, (mem_reduce_S_iff a a' ε hred i _).2 ⟨t, rfl⟩, cert_toFun a a' ε φ hred i t⟩

variable {ε}

omit hred in
/-- **Lemma 28, first claim**: a subgraph isomorphism `φ : G → Ĝ` yields a strict unilateral
SPI of `Γᶜ` — the certificate `Ψ`, checked through Proposition 25: `Ψ` is strictly
Pareto-improving under `uᶜ`, moves player 1's reduced action set into the `R` block,
carries player 2's payoffs exactly, and the unilateral candidate reduces to `Ψ(AΓ)`
because every `D` action and every `P` action outside `Ψ₂(D)` is strictly dominated by
`(P, 2n̂+1)` (the printed three cases). -/
lemma strictUnilateralSPIDecision_of_subgraphIso (hn : 1 ≤ n) (hε : 0 < ε)
    (hεn : ε * (2 * n) < 1) (hε' : ε * (2 * n') < 1) (hφ : SubgraphIso a a' φ) :
    (hardnessGame a a' ε).StrictUnilateralSPIDecision := by
  have hε1 : ε < 1 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hred := reduce_hardnessGame a a' ε hε hε1 hε'
  set c := cert a a' ε φ hred with hc
  rw [Game.strictUnilateralSPIDecision_iff_certificate]
  have hPI : c.ParetoImproving := by
    intro b hb
    obtain ⟨t, t', rfl⟩ := (mem_reduce_profiles_iff a a' ε hred b).1 hb
    rw [hc, cert_map]
    intro i
    cases i
    · exact tableU₁_le_psiT a a' φ hε.le hεn hφ t t'
    · exact (tableU₂_psiT ε φ t t').symm.le
  have hAff : c.Affine .one := by
    intro j hj
    refine ⟨1, one_pos, 0, fun b hb => ?_⟩
    obtain ⟨t, t', rfl⟩ := (mem_reduce_profiles_iff a a' ε hred b).1 hb
    rw [hc, cert_map, one_mul, add_zero]
    cases j
    · exact absurd rfl hj
    · exact (tableU₂_psiT ε φ t t').symm
  refine ⟨.one, c, ⟨hPI, ?_⟩, ?_, hAff, ?_⟩
  · -- strict at `((T, 2n+1), (D, 1))`: `3 < 4`
    refine ⟨pair (Sum.inl TableAct.c₁) (Sum.inl (Sum.inl ⟨0, hn⟩)),
      (mem_reduce_profiles_iff a a' ε hred _).2 ⟨_, _, rfl⟩, ?_⟩
    refine Pi.lt_def.2 ⟨hPI _ ((mem_reduce_profiles_iff a a' ε hred _).2 ⟨_, _, rfl⟩), .one, ?_⟩
    rw [hc, cert_map]
    show tableU₁ a ε 0 TableAct.c₁ (Sum.inl ⟨0, hn⟩) <
      tableU₁ a' ε 1 (psiT φ TableAct.c₁) (psiT φ (Sum.inl ⟨0, hn⟩))
    simp [psiT, tableU₁]
  · -- non-trivial: `(T, 2n+1)` survives in `reduce Γᶜ` but is not in `Ψ₁(T)`
    refine ⟨.one, fun h => ?_⟩
    have : Sum.inl TableAct.c₁ ∈ c.image .one := by
      rw [h]; exact (mem_reduce_S_iff a a' ε hred .one _).2 ⟨_, rfl⟩
    obtain ⟨t, ht⟩ := (mem_cert_image_iff a a' ε φ hred .one _).1 this
    exact absurd ht (by simp)
  · -- check 3, through the three dominations by `(P, 2n̂+1)`
    refine c.reducesToImage_of_dominated .one hAff fun j hj x _ hxI => ?_
    cases j
    · exact absurd rfl hj
    refine ⟨Sum.inr TableAct.c₁, (mem_cert_image_iff a a' ε φ hred .two _).2 ⟨TableAct.c₁, rfl⟩, ?_⟩
    rw [strictlyDominates_two_iff]
    refine ⟨by rw [c.unilateralGame_S_of_ne .one hj]; exact Finset.mem_univ _,
      by rw [c.unilateralGame_S_of_ne .one hj]; exact Finset.mem_univ _, fun r hr => ?_⟩
    rw [Game.Certificate.unilateralGame_S_self] at hr
    obtain ⟨t, rfl⟩ := (mem_cert_image_iff a a' ε φ hred .one _).1 hr
    rw [c.unilateralGame_u_of_ne .one _ hj, c.unilateralGame_u_of_ne .one _ hj]
    rcases x with d | p
    · show hardU a a' ε (Sum.inr (psiT φ t)) (Sum.inl d) .two <
        hardU a a' ε (Sum.inr (psiT φ t)) (Sum.inr TableAct.c₁) .two
      simp only [hardU, pair_two]
      exact neg_one_lt_tableU₂_c₁ hε _
    · have hp : ∀ t', p ≠ psiT φ t' := fun t' h =>
        hxI ((mem_cert_image_iff a a' ε φ hred .two _).2 ⟨t', by rw [h]⟩)
      show hardU a a' ε (Sum.inr (psiT φ t)) (Sum.inr p) .two <
        hardU a a' ε (Sum.inr (psiT φ t)) (Sum.inr TableAct.c₁) .two
      simp only [hardU, pair_two]
      rcases p with k | k | b
      · have hk : ∀ i, φ i ≠ k := fun i h => hp (Sum.inl i) (by simp [psiT, h])
        rcases t with i | i | b <;> simp [psiT, tableU₂, hk] <;> linarith
      · have hk : ∀ i, φ i ≠ k := fun i h => hp (Sum.inr (Sum.inl i)) (by simp [psiT, h])
        rcases t with i | i | b <;> simp [psiT, tableU₂, hk] <;> linarith
      · exact absurd rfl (hp (Sum.inr (Sum.inr b)))

end certificate

/-! ### From any SPI to a subgraph isomorphism (Lemma 28, second claim) -/

section extraction

variable {ε}

/-- Only `(2n̂+1, 2n̂+1)` is worth `6` to player 1 in `Γ̂`. -/
lemma eq_c₁_of_six_le {m : ℕ} (g : Graph m) (hε : 0 ≤ ε) (hε1 : ε < 1) (hεm : ε * (2 * m) < 1)
    {s s' : TableAct m} (h : 6 ≤ tableU₁ g ε 1 s s') : s = TableAct.c₁ ∧ s' = TableAct.c₁ := by
  have h1 := adj_le_one g
  rcases s with i | i | b <;> rcases s' with j | j | b' <;> simp only [tableU₁] at h <;>
    (try split_ifs at h) <;>
    first
    | (exfalso; linarith)
    | (exfalso; linarith [h1 i j])
    | (exfalso; linarith [block_mul_le hε i])
    | (exfalso; linarith [succ_mul_le hε j])
    | simp_all

/-- Only `(2n̂+2, 2n̂+2)` is worth `6` to player 2. -/
lemma eq_c₂_of_six_le {m : ℕ} (hε1 : ε < 1) {s s' : TableAct m} (h : 6 ≤ tableU₂ m ε s s') :
    s = TableAct.c₂ ∧ s' = TableAct.c₂ := by
  rcases s with i | i | b <;> rcases s' with j | j | b' <;> simp only [tableU₂] at h <;>
    (try split_ifs at h) <;> first | (exfalso; linarith) | simp_all

/-- In the row `n̂+k` of player 1's table, only the column `k` pays more than `0`. -/
lemma eq_inl_of_pos_row {m : ℕ} (g : Graph m) {k : Fin m} {s' : TableAct m}
    (h : 0 < tableU₁ g ε 1 (Sum.inr (Sum.inl k)) s') : s' = Sum.inl k := by
  rcases s' with j | j | b <;> simp only [tableU₁] at h <;> (try split_ifs at h) <;>
    first | (exfalso; linarith) | simp_all

/-- In the column `n̂+l` of player 2's table, only the row `l` pays more than `0`. -/
lemma eq_inl_of_pos_col {m : ℕ} {l : Fin m} {s : TableAct m}
    (h : 0 < tableU₂ m ε s (Sum.inr (Sum.inl l))) : s = Sum.inl l := by
  rcases s with i | i | b <;> simp only [tableU₂] at h <;> (try split_ifs at h) <;>
    first | (exfalso; linarith) | simp_all

/-- In the first block of player 2's table, only the diagonal pays more than `1`. -/
lemma eq_of_one_lt_block {m : ℕ} {k l : Fin m} (h : 1 < tableU₂ m ε (Sum.inl k) (Sum.inl l)) :
    k = l := by
  simp only [tableU₂] at h
  split_ifs at h with hkl
  · exact hkl
  · exact absurd h (lt_irrefl _)

lemma le_of_adj_le {i j : Fin n} {k l : Fin n'} (h : adj a i j ≤ adj a' k l) : a i j ≤ a' k l := by
  unfold adj at h
  cases h1 : a i j <;> cases h2 : a' k l <;> (try norm_num [h1, h2] at h) <;> (try decide)

/-- **Lemma 28, second claim**: any SPI of `Γᶜ` yields a subgraph isomorphism `G → Ĝ`.  Read
the SPI as a certificate `(F₁, F₂)` (Proposition 23).  Pareto-improvement forbids images in
`T × P` and `R × D`, so the certificate keeps to `T × D` — impossible, since then both
reduced action sets are permuted in place, against non-triviality — or moves into `R × P`.
There the two outcomes worth `6` pin the corners, a first-block action of player 1 cannot
land in the second block (it would lose against all but one of `(D, i)`, `(D, n+i)`),
player 2 must agree with player 1 on the first block (else `2 ≤ 1`), and the restriction
of `F₁` to `[n]` is the required injection. -/
lemma subgraphIsoProblem_of_spiDecision (hε : 0 < ε) (hε1 : ε < 1) (hε' : ε * (2 * n') < 1)
    (h : (hardnessGame a a' ε).SPIDecision) : SubgraphIsoProblem a a' := by
  have hred := reduce_hardnessGame a a' ε hε hε1 hε'
  obtain ⟨c, hPI, hnt⟩ := (Game.spiDecision_iff_certificate _).1 h
  have hmem : ∀ (i : Two) (t : TableAct n), Sum.inl t ∈ (hardnessGame a a' ε).reduce.S i :=
    fun i t => (mem_reduce_S_iff a a' ε hred i _).2 ⟨t, rfl⟩
  set F₁ : TableAct n → HardAct n n' := fun t => c.toFun .one (Sum.inl t) with hF₁
  set F₂ : TableAct n → HardAct n n' := fun t => c.toFun .two (Sum.inl t) with hF₂
  have hinj₁ : Function.Injective F₁ := fun t t' h =>
    Sum.inl_injective (c.injOn .one (hmem _ t) (hmem _ t') h)
  have hinj₂ : Function.Injective F₂ := fun t t' h =>
    Sum.inl_injective (c.injOn .two (hmem _ t) (hmem _ t') h)
  have hPI' : ∀ t t', hardU a a' ε (Sum.inl t) (Sum.inl t') ≤ hardU a a' ε (F₁ t) (F₂ t') := by
    intro t t'
    have := hPI _ ((mem_reduce_profiles_iff a a' ε hred _).2 ⟨t, t', rfl⟩)
    have hmap : c.map (pair (Sum.inl t) (Sum.inl t')) = pair (F₁ t) (F₂ t') := by
      funext i; cases i <;> rfl
    rw [hmap] at this
    exact this
  have himg : ∀ (i : Two) (x : HardAct n n'), x ∈ c.image i ↔ ∃ t, x = c.toFun i (Sum.inl t) := by
    intro i x
    simp only [Game.Certificate.image, Finset.mem_image]
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨t, rfl⟩ := (mem_reduce_S_iff a a' ε hred i _).1 hy
      exact ⟨t, rfl⟩
    · rintro ⟨t, rfl⟩
      exact ⟨_, hmem i t, rfl⟩
  -- the forbidden quadrants
  have hTP : ∀ t t' s s', F₁ t = Sum.inl s → F₂ t' = Sum.inr s' → False := by
    intro t t' s s' h1 h2
    have := hPI' t t' .two
    rw [h1, h2] at this
    simp only [hardU, pair_two] at this
    linarith [neg_one_le_tableU₂ (m := n) hε.le t t']
  have hRD : ∀ t t' s s', F₁ t = Sum.inr s → F₂ t' = Sum.inl s' → False := by
    intro t t' s s' h1 h2
    have := hPI' t t' .one
    rw [h1, h2] at this
    simp only [hardU, pair_one] at this
    linarith [neg_one_le_tableU₁ a hε.le le_rfl t t']
  rcases hc₁ : F₁ TableAct.c₁ with s₀ | s₀
  · -- the certificate keeps to the `Γ` block: both action sets are permuted in place
    exfalso
    have hall₂ : ∀ t', ∃ s, F₂ t' = Sum.inl s := fun t' => by
      rcases h2 : F₂ t' with s | s
      · exact ⟨s, rfl⟩
      · exact (hTP _ _ _ _ hc₁ h2).elim
    have hall₁ : ∀ t, ∃ s, F₁ t = Sum.inl s := fun t => by
      rcases h1 : F₁ t with s | s
      · exact ⟨s, rfl⟩
      · obtain ⟨s', hs'⟩ := hall₂ TableAct.c₁
        exact (hRD _ _ _ _ h1 hs').elim
    have himg_eq : ∀ i, c.image i = blockActions n n' := by
      intro i
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        obtain ⟨t, rfl⟩ := (himg i x).1 hx
        cases i
        · obtain ⟨s, hs⟩ := hall₁ t
          exact mem_blockActions.2 ⟨s, hs⟩
        · obtain ⟨s, hs⟩ := hall₂ t
          exact mem_blockActions.2 ⟨s, hs⟩
      · rw [Game.Certificate.image, Finset.card_image_of_injOn (c.injOn i), hred]
        exact le_rfl
    obtain ⟨i, hi⟩ := hnt
    exact hi ((himg_eq i).trans (by rw [hred]; rfl))
  · -- the certificate moves into the `Γ̂` block
    have hall₂ : ∀ t', ∃ s, F₂ t' = Sum.inr s := fun t' => by
      rcases h2 : F₂ t' with s | s
      · exact (hRD _ _ _ _ hc₁ h2).elim
      · exact ⟨s, rfl⟩
    have hall₁ : ∀ t, ∃ s, F₁ t = Sum.inr s := fun t => by
      rcases h1 : F₁ t with s | s
      · obtain ⟨s', hs'⟩ := hall₂ TableAct.c₁
        exact (hTP _ _ _ _ h1 hs').elim
      · exact ⟨s, rfl⟩
    choose g₁ hg₁ using hall₁
    choose g₂ hg₂ using hall₂
    have hg₁inj : Function.Injective g₁ := fun t t' h => hinj₁ (by rw [hg₁, hg₁, h])
    have hg₂inj : Function.Injective g₂ := fun t t' h => hinj₂ (by rw [hg₂, hg₂, h])
    have hP₁ : ∀ t t', tableU₁ a ε 0 t t' ≤ tableU₁ a' ε 1 (g₁ t) (g₂ t') := by
      intro t t'
      have := hPI' t t' .one
      rw [hg₁, hg₂] at this
      simpa only [hardU, pair_one] using this
    have hP₂ : ∀ t t', tableU₂ n ε t t' ≤ tableU₂ n' ε (g₁ t) (g₂ t') := by
      intro t t'
      have := hPI' t t' .two
      rw [hg₁, hg₂] at this
      simpa only [hardU, pair_two] using this
    -- the corners are pinned by the two outcomes worth `6`
    have hcorner₁ : g₁ TableAct.c₁ = TableAct.c₁ ∧ g₂ TableAct.c₁ = TableAct.c₁ :=
      eq_c₁_of_six_le a' hε.le hε1 hε' (by simpa [tableU₁] using hP₁ TableAct.c₁ TableAct.c₁)
    have hcorner₂ : g₁ TableAct.c₂ = TableAct.c₂ ∧ g₂ TableAct.c₂ = TableAct.c₂ :=
      eq_c₂_of_six_le hε1 (by simpa [tableU₂] using hP₂ TableAct.c₂ TableAct.c₂)
    -- player 1's first block lands in the first block
    have hfirst : ∀ i, ∃ k, g₁ (Sum.inl i) = Sum.inl k := by
      intro i
      rcases hgi : g₁ (Sum.inl i) with k | k | b
      · exact ⟨k, rfl⟩
      · exfalso
        have h1 := hP₁ (Sum.inl i) (Sum.inl i)
        have h2 := hP₁ (Sum.inl i) (Sum.inr (Sum.inl i))
        have hL1 : tableU₁ a ε 0 (Sum.inl i) (Sum.inl i) = 2 := by simp [tableU₁]
        have hL2 : tableU₁ a ε 0 (Sum.inl i) (Sum.inr (Sum.inl i)) =
            4 + 0 + ((n : ℝ) + ((i : ℕ) + 1)) * ε := by simp [tableU₁]
        rw [hgi, hL1] at h1
        rw [hgi, hL2] at h2
        have e1 : g₂ (Sum.inl i) = Sum.inl k := eq_inl_of_pos_row (ε := ε) a' (by linarith)
        have e2 : g₂ (Sum.inr (Sum.inl i)) = Sum.inl k :=
          eq_inl_of_pos_row (ε := ε) a' (by linarith [block_mul_nonneg (m := n) hε.le i])
        exact absurd (hg₂inj (e1.trans e2.symm)) (by simp)
      · exfalso
        have : g₁ (Sum.inl i) = g₁ (Sum.inr (Sum.inr b)) := by
          rw [hgi]; cases b
          · exact hcorner₁.1.symm
          · exact hcorner₂.1.symm
        exact absurd (hg₁inj this) (by simp)
    choose φ' hφ' using hfirst
    have hφ'inj : Function.Injective φ' := fun i j hij =>
      Sum.inl_injective (hg₁inj (a₁ := Sum.inl i) (a₂ := Sum.inl j) (by rw [hφ', hφ', hij]))
    -- player 2 agrees with player 1 on the first block
    have hsecond : ∀ i, g₂ (Sum.inl i) = Sum.inl (φ' i) := by
      intro i
      rcases hg : g₂ (Sum.inl i) with l | l | b
      · have h1 := hP₂ (Sum.inl i) (Sum.inl i)
        have hL : tableU₂ n ε (Sum.inl i) (Sum.inl i) = 2 := by simp [tableU₂]
        rw [hφ', hg, hL] at h1
        have := eq_of_one_lt_block (ε := ε) (k := φ' i) (l := l) (by linarith)
        rw [this]
      · exfalso
        have h1 := hP₂ (Sum.inl i) (Sum.inl i)
        have hL : tableU₂ n ε (Sum.inl i) (Sum.inl i) = 2 := by simp [tableU₂]
        rw [hφ', hg, hL] at h1
        have e1 : (Sum.inl (φ' i) : TableAct n') = Sum.inl l :=
          eq_inl_of_pos_col (ε := ε) (by linarith)
        have h2 := hP₂ (Sum.inr (Sum.inl i)) (Sum.inl i)
        have hL2 : tableU₂ n ε (Sum.inr (Sum.inl i)) (Sum.inl i) = 4 := by simp [tableU₂]
        rw [hg, hL2] at h2
        have e2 : g₁ (Sum.inr (Sum.inl i)) = Sum.inl l := eq_inl_of_pos_col (ε := ε) (by linarith)
        have : g₁ (Sum.inl i) = g₁ (Sum.inr (Sum.inl i)) := by rw [hφ', e1, e2]
        exact absurd (hg₁inj this) (by simp)
      · exfalso
        have : g₂ (Sum.inl i) = g₂ (Sum.inr (Sum.inr b)) := by
          rw [hg]; cases b
          · exact hcorner₁.2.symm
          · exact hcorner₂.2.symm
        exact absurd (hg₂inj this) (by simp)
    -- the subgraph condition is Pareto-improvement on the first block
    refine ⟨⟨φ', hφ'inj⟩, fun i j hij => ?_⟩
    have h1 := hP₁ (Sum.inl i) (Sum.inl j)
    rw [hφ', hsecond] at h1
    simp only [tableU₁, if_neg hij, if_neg (hφ'inj.ne hij)] at h1
    exact le_of_adj_le a a' h1

end extraction

/-! ### Lemma 28 -/

section lemma28

variable {ε} (hn : 1 ≤ n) (hε : 0 < ε) (hεn : ε * (2 * n) < 1) (hε' : ε * (2 * n') < 1)
include hn hε hεn hε'

/-- **Lemma 28**, the reduction: `G` embeds in `Ĝ` as a subgraph iff `Γᶜ` has a strict
unilateral SPI.  This is the strongest of the four forms — the appendix's first claim
produces a strict unilateral SPI from a subgraph isomorphism and its second extracts a
subgraph isomorphism from any SPI at all — and the other three follow from it.  Qualified
node (`dd:complexity`): "reducible in linear time" and "NP-hard" (which needs Lemma 27) are
not rendered; the instance size is `size_hardnessGame`.  The hypotheses are the paper's
`0 < ε < 1/(2n)`, `ε < 1/(2n̂)`, and `n ≥ 1` in place of its "WLOG `n, n̂ ≥ 2`".

Paper node: `Lemma 28`, `Theorem 9` -/
theorem subgraphIsoProblem_iff_strictUnilateralSPIDecision :
    SubgraphIsoProblem a a' ↔ (hardnessGame a a' ε).StrictUnilateralSPIDecision := by
  have hε1 : ε < 1 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  exact ⟨fun ⟨φ, hφ⟩ => strictUnilateralSPIDecision_of_subgraphIso a a' φ hn hε hεn hε' hφ,
    fun h => subgraphIsoProblem_of_spiDecision a a' hε hε1 hε' h.strict.spi⟩

/-- **Lemma 28** for the plain SPI decision problem.

Paper node: `Lemma 28`, `Theorem 9` -/
theorem subgraphIsoProblem_iff_spiDecision :
    SubgraphIsoProblem a a' ↔ (hardnessGame a a' ε).SPIDecision :=
  ⟨fun h => ((subgraphIsoProblem_iff_strictUnilateralSPIDecision a a' hn hε hεn hε').1 h).strict.spi,
    fun h => (subgraphIsoProblem_iff_strictUnilateralSPIDecision a a' hn hε hεn hε').2
      (by
        have hε1 : ε < 1 := by
          have : (1 : ℝ) ≤ n := by exact_mod_cast hn
          nlinarith
        obtain ⟨φ, hφ⟩ := subgraphIsoProblem_of_spiDecision a a' hε hε1 hε' h
        exact strictUnilateralSPIDecision_of_subgraphIso a a' φ hn hε hεn hε' hφ)⟩

/-- **Lemma 28** for the strict SPI decision problem.

Paper node: `Lemma 28`, `Theorem 9` -/
theorem subgraphIsoProblem_iff_strictSPIDecision :
    SubgraphIsoProblem a a' ↔ (hardnessGame a a' ε).StrictSPIDecision :=
  ⟨fun h => ((subgraphIsoProblem_iff_strictUnilateralSPIDecision a a' hn hε hεn hε').1 h).strict,
    fun h => (subgraphIsoProblem_iff_spiDecision a a' hn hε hεn hε').2 h.spi⟩

/-- **Lemma 28** for the unilateral SPI decision problem.

Paper node: `Lemma 28`, `Theorem 9` -/
theorem subgraphIsoProblem_iff_unilateralSPIDecision :
    SubgraphIsoProblem a a' ↔ (hardnessGame a a' ε).UnilateralSPIDecision :=
  ⟨fun h =>
    ((subgraphIsoProblem_iff_strictUnilateralSPIDecision a a' hn hε hεn hε').1 h).unilateral,
    fun h => (subgraphIsoProblem_iff_spiDecision a a' hn hε hεn hε').2 h.spi⟩

end lemma28

/-! ### Theorem 9 -/

universe v

/-- **Theorem 9**, as carried here (`dd:complexity`, RULING 6): for two-player games,
**membership** — each of the four (strict) (unilateral) SPI decision problems is
equivalent to the existence of a certificate (Propositions 23 and 25; the certificates
form a finite type of size at most `m ^ l`, `card_certificate_le`) — together with
**hardness** — the subgraph isomorphism problem reduces to each of the four problems on
the two-player games of Table 10 (Lemma 28).  NP-completeness itself is these two facts
plus Cook's theorem for subgraph isomorphism (Lemma 27, cited and not carried) plus a cost
model for games given as explicit payoff matrices, which the paper does not fix and this
formalization does not render.

Paper node: `Theorem 9` -/
theorem theorem9 :
    (∀ (𝒜 : Two → Type v) [∀ i, DecidableEq (𝒜 i)] (Γ : Game Two 𝒜),
      (Γ.SPIDecision ↔ ∃ c : Γ.Certificate, c.ParetoImproving ∧ c.Nontrivial) ∧
      (Γ.StrictSPIDecision ↔ ∃ c : Γ.Certificate, c.StrictlyParetoImproving ∧ c.Nontrivial) ∧
      (Γ.UnilateralSPIDecision ↔ ∃ (i : Two) (c : Γ.Certificate),
        c.ParetoImproving ∧ c.Nontrivial ∧ c.Affine i ∧ c.ReducesToImage i) ∧
      (Γ.StrictUnilateralSPIDecision ↔ ∃ (i : Two) (c : Γ.Certificate),
        c.StrictlyParetoImproving ∧ c.Nontrivial ∧ c.Affine i ∧ c.ReducesToImage i)) ∧
    ∀ {n n' : ℕ} (a : Graph n) (a' : Graph n') (ε : ℝ), 1 ≤ n → 0 < ε → ε * (2 * n) < 1 →
      ε * (2 * n') < 1 →
      (SubgraphIsoProblem a a' ↔ (hardnessGame a a' ε).SPIDecision) ∧
      (SubgraphIsoProblem a a' ↔ (hardnessGame a a' ε).StrictSPIDecision) ∧
      (SubgraphIsoProblem a a' ↔ (hardnessGame a a' ε).UnilateralSPIDecision) ∧
      (SubgraphIsoProblem a a' ↔ (hardnessGame a a' ε).StrictUnilateralSPIDecision) :=
  ⟨fun _ _ Γ => ⟨Γ.spiDecision_iff_certificate, Γ.strictSPIDecision_iff_certificate,
      Γ.unilateralSPIDecision_iff_certificate, Γ.strictUnilateralSPIDecision_iff_certificate⟩,
    fun a a' _ hn hε hεn hε' => ⟨subgraphIsoProblem_iff_spiDecision a a' hn hε hεn hε',
      subgraphIsoProblem_iff_strictSPIDecision a a' hn hε hεn hε',
      subgraphIsoProblem_iff_unilateralSPIDecision a a' hn hε hεn hε',
      subgraphIsoProblem_iff_strictUnilateralSPIDecision a a' hn hε hεn hε'⟩⟩

end Hardness

end SafeParetoImprovements
