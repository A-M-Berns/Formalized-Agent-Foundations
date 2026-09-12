import SafeParetoImprovements.ProgramGame

/-!
# The instruction language, Algorithm 2, Proposition 18 and Theorem 1 (Appendix A)

The paper leaves its programming language unspecified beyond the three features
Algorithm 2 uses: compare the whole profile of submitted code with one's own, play a
fixed (mixed) action, and call the black box `Πᵢ(Γ′)` for a subset game `Γ′`
(extraction l. 1972–1976, 2052–2058).  `Prog` is that language and nothing more
(`dd:code-eq`):

* `Prog.play σ` — play the mixed action `σᵢ` (the running player's coordinate of `σ`);
* `Prog.delegate Γ′ h` — "play `Πᵢ(Γ′)`" for a subset game `Γ′` of the base game;
* `Prog.ifAllSame t p` — if every other player submitted the same code as mine, run `t`,
  otherwise run `p j` for a player `j` whose code differs.

A `Prog` is player-agnostic: the player index is a run-time input of the execution, as in
the paper, so Algorithm 2 can be submitted verbatim by every player and "`cⱼ ≠ cᵢ`" is a
comparison of identical syntax.  Code equality is classical (`Prog` contains real payoffs
through the embedded games and real probabilities through the mixtures): the meta-game is
a mathematical object, exactly as the paper's Lisp-with-real-payoffs is.  When several
players' code differs, the paper's loop punishes the *first* such player in the order
`1, …, n`; `N` carries no order here, so a fixed classical choice of a differing player
stands in.  Only unilateral deviations matter for program equilibrium, and for those the
choice is forced.

`Prog.programGame Γ₀ R` realises `Prog` as a `ProgramGame` (the realization theorem: the
delegation branch is measurable because `Π(Γ′)` has measurable fibers).  `Prog.algorithm2`
is Algorithm 2 as a term, with one repair (erratum D15): the paper's line 3 says "play
`minimax(i, j)`", which by its own definition is a strategy for *player `j`*; the punisher
`i` must play her own coordinate of the minimax profile against `j`, `minimax(j, i)`, which
is what the term does.  Proposition 18 and Theorem 1 follow from the interface result
`ProgramGame.isProgramEquilibrium_of_algorithm2` once Algorithm 2's two semantic
properties are proved from the execution model.
-/

universe u v w

namespace SafeParetoImprovements

open StrategicGame MeasureTheory Filter Set

variable {N : Type u} {𝒜 : N → Type v}

/-- **The instruction language** (`dd:code-eq`): mixed actions, delegation to `Π` on a
subset game, and the "same code?" test with a punishment per differing player. -/
inductive Prog (Γ₀ : Game N 𝒜) : Type (max u v)
  /-- Play the mixed action `σᵢ`, `i` the running player. -/
  | play (σ : ∀ i, Γ₀.Mixed i) : Prog Γ₀
  /-- Play `Πᵢ(Γ′)` for the subset game `Γ′` of the base game. -/
  | delegate (Γ' : Game N 𝒜) (h : Γ'.IsSubsetGameOf Γ₀) : Prog Γ₀
  /-- If everybody else's code equals mine run `then_`, else run `punish j` for a player
  `j` whose code differs. -/
  | ifAllSame (then_ : Prog Γ₀) (punish : N → Prog Γ₀) : Prog Γ₀

namespace Prog

variable {Γ₀ : Game N 𝒜} (R : Representatives.{u, v, w} N 𝒜) [∀ i, DecidableEq (𝒜 i)]

open Classical in
/-- **Execution** of player `k`'s program `p` when everybody's code is `c` and the
representatives' sample point is `ω`: the mixed action `k` realises. -/
noncomputable def execAt (c : N → Prog Γ₀) (k : N) : Prog Γ₀ → R.Ω → Γ₀.Mixed k
  | play σ, _ => σ k
  | delegate Γ' h, ω => Γ₀.pureMixed (R.play Γ' ω k) (h k (R.toPlay.mem Γ' ω k))
  | ifAllSame t p, ω =>
      if hall : ∀ j, c j = c k then execAt c k t ω
      else execAt c k (p (Classical.choose (not_forall.1 hall))) ω

lemma execAt_play (c : N → Prog Γ₀) (k : N) (σ : ∀ i, Γ₀.Mixed i) (ω : R.Ω) :
    execAt R c k (play σ) ω = σ k := rfl

lemma execAt_delegate (c : N → Prog Γ₀) (k : N) (Γ' : Game N 𝒜) (h : Γ'.IsSubsetGameOf Γ₀)
    (ω : R.Ω) :
    execAt R c k (delegate Γ' h) ω = Γ₀.pureMixed (R.play Γ' ω k) (h k (R.toPlay.mem Γ' ω k)) :=
  rfl

lemma execAt_ifAllSame_of_all {c : N → Prog Γ₀} {k : N} (hall : ∀ j, c j = c k)
    (t : Prog Γ₀) (p : N → Prog Γ₀) (ω : R.Ω) :
    execAt R c k (ifAllSame t p) ω = execAt R c k t ω := by
  simp only [execAt, dif_pos hall]

lemma execAt_ifAllSame_of_ne {c : N → Prog Γ₀} {k : N} (hne : ¬ ∀ j, c j = c k)
    (t : Prog Γ₀) (p : N → Prog Γ₀) (ω : R.Ω) :
    ∃ j, c j ≠ c k ∧ execAt R c k (ifAllSame t p) ω = execAt R c k (p j) ω := by
  refine ⟨Classical.choose (not_forall.1 hne), Classical.choose_spec (not_forall.1 hne), ?_⟩
  simp only [execAt, dif_neg hne]

section measurable

variable [DecidableEq N] [Fintype N]

/-- The coordinate fibers `{ω | Πₖ(Γ′)(ω) = b}` are measurable: finite unions of the
profile fibers. -/
lemma measurableSet_coord_fiber (Γ' : Game N 𝒜) (k : N) (b : 𝒜 k) :
    MeasurableSet {ω | R.play Γ' ω k = b} := by
  have : {ω | R.play Γ' ω k = b} =
      ⋃ a ∈ Γ'.profilesFinset.filter (fun a => a k = b), {ω | R.play Γ' ω = a} := by
    ext ω
    simp only [mem_setOf_eq, mem_iUnion, Finset.mem_filter, exists_prop]
    constructor
    · intro h
      exact ⟨R.play Γ' ω, ⟨Γ'.mem_profilesFinset.2 (R.toPlay.mem Γ' ω), h⟩, rfl⟩
    · rintro ⟨a, ⟨-, hak⟩, rfl⟩
      exact hak
  rw [this]
  exact Finset.measurableSet_biUnion _ fun a _ => R.measurableSet_fiber Γ' a

lemma measurable_execAt (c : N → Prog Γ₀) (k : N) (p : Prog Γ₀) (b : Γ₀.S k) :
    Measurable fun ω => (execAt R c k p ω).val b := by
  induction p with
  | play σ =>
      simp only [execAt_play]
      exact measurable_const
  | delegate Γ' h =>
      have : (fun ω => (execAt R c k (delegate Γ' h) ω).val b) =
          Set.indicator {ω | R.play Γ' ω k = b} (fun _ => 1) := by
        funext ω
        rw [execAt_delegate, Game.pureMixed_val]
        simp only [Set.indicator, mem_setOf_eq]
        by_cases hb : R.play Γ' ω k = b
        · rw [if_pos hb.symm, if_pos hb]
        · rw [if_neg (Ne.symm hb), if_neg hb]
      rw [this]
      exact measurable_const.indicator (measurableSet_coord_fiber R Γ' k b)
  | ifAllSame t p iht ihp =>
      by_cases hall : ∀ j, c j = c k
      · simp only [execAt_ifAllSame_of_all R hall]
        exact iht
      · simp only [execAt, dif_neg hall]
        exact ihp _

variable (Γ₀) in
/-- **The realization theorem**: `Prog` with `execAt` is a program game on `Γ₀` for the
representatives `R`.  Every player's instruction set is `Prog Γ₀`; player `k`'s realised
mixed action is the execution of her own code. -/
noncomputable def programGame : ProgramGame.{u, v, w, max u v} Γ₀ R where
  Instr _ := Prog Γ₀
  exec c ω k := execAt R c k (c k) ω
  measurable_exec c k b := measurable_execAt R c k (c k) b

@[simp] lemma programGame_exec (c : N → Prog Γ₀) (ω : R.Ω) (k : N) :
    (programGame Γ₀ R).exec c ω k = execAt R c k (c k) ω := rfl

end measurable

/-! ### Algorithm 2 -/

/-- **Algorithm 2** (extraction l. 2052–2058): if everybody else submitted this very code,
play `Πᵢ(Γˢ)`; otherwise punish a differing player `j` by playing my coordinate of the
minimax profile against `j` (erratum D15: the paper writes `minimax(i, j)`, a strategy of
player `j`'s). -/
noncomputable def algorithm2 [DecidableEq N] [Fintype N] (Γs : Game N 𝒜) (h : Γs.IsSubsetGameOf Γ₀) :
    Prog Γ₀ :=
  ifAllSame (delegate Γs h) fun j => play (Γ₀.minimax j)

section algorithm2

variable [DecidableEq N] [Fintype N]
variable {Γs : Game N 𝒜} (h : Γs.IsSubsetGameOf Γ₀)

/-- When everybody submits Algorithm 2, the execution is `Π(Γˢ)`. -/
lemma plays_algorithm2 :
    (programGame Γ₀ R).Plays (fun _ => algorithm2 Γs h) fun ω => R.play Γs ω := by
  intro ω k b
  rw [programGame_exec, algorithm2, execAt_ifAllSame_of_all R (fun _ => rfl), execAt_delegate,
    Game.pureMixed_val]

/-- Against a unilateral deviation by `i`, every other player plays the minimax profile
against `i`. -/
lemma exec_update_algorithm2 (i : N) (c' : Prog Γ₀) (hc : c' ≠ algorithm2 Γs h) (ω : R.Ω)
    (j : N) (hj : j ≠ i) :
    (programGame Γ₀ R).exec (Function.update (fun _ => algorithm2 Γs h) i c') ω j = Γ₀.minimax i j := by
  have hne : ¬ ∀ l, Function.update (fun _ : N => algorithm2 Γs h) i c' l =
      Function.update (fun _ : N => algorithm2 Γs h) i c' j := fun hall => by
    have := hall i
    rw [Function.update_self, Function.update_of_ne hj] at this
    exact hc this
  rw [programGame_exec]
  show execAt R (Function.update (fun _ : N => algorithm2 Γs h) i c') j
    (Function.update (fun _ : N => algorithm2 Γs h) i c' j) ω = _
  rw [Function.update_of_ne hj]
  show execAt R _ j (ifAllSame (delegate Γs h) fun j => play (Γ₀.minimax j)) ω = _
  obtain ⟨l, hl, hexec⟩ :=
    execAt_ifAllSame_of_ne R hne (delegate Γs h) (fun j => play (Γ₀.minimax j)) ω
  have hli : l = i := by
    by_contra hli
    exact hl (by rw [Function.update_of_ne hli, Function.update_of_ne hj])
  rw [hexec, hli, execAt_play]

/-- **Proposition 18.**  Let `Γˢ` be an SPI on `Γ₀` for the representatives `R`, and let
`c` be the program profile consisting only of Algorithm 2.  If `Π(Γ₀)` guarantees each
player at least their threat point in expectation, then `c` is a program equilibrium and
`exec(c) = Π(Γˢ)`.

The deviator's payoff is at most the threat point, not equal to it (erratum D8); the
independence of the deviator's action from the punishers' mixed actions is the execution
model's (`dd:exec-kernel`).

Paper node: `Proposition 18` -/
theorem algorithm2_isProgramEquilibrium (hSPI : R.toPlay.IsSPI R.certainty Γ₀ Γs)
    (hthreat : ∀ i, Γ₀.threatPoint i ≤ ∫ ω, Γ₀.u (R.play Γ₀ ω) i ∂R.μ) :
    (programGame Γ₀ R).IsProgramEquilibrium (fun _ => algorithm2 Γs h) ∧
      (programGame Γ₀ R).Plays (fun _ => algorithm2 Γs h) fun ω => R.play Γs ω :=
  (programGame Γ₀ R).isProgramEquilibrium_of_algorithm2 hSPI _ (plays_algorithm2 R h)
    (fun i c' hc ω j hj => exec_update_algorithm2 R h i c' hc ω j hj) hthreat

/-- **Theorem 1.**  Let `Γˢ` be an SPI on `Γ₀` for the representatives `R`.  In the program
game on `Γ₀` whose instructions are the programs of `Prog` — the normal kind of
instructions plus "play `Πᵢ(Γ′)`" for subset games `Γ′` — if `Π(Γ₀)` guarantees each
player at least their minimax utility, then `Π(Γˢ)` is played in a program equilibrium.

Paper node: `Theorem 1` -/
theorem exists_programEquilibrium_plays (hSPI : R.toPlay.IsSPI R.certainty Γ₀ Γs)
    (hthreat : ∀ i, Γ₀.threatPoint i ≤ ∫ ω, Γ₀.u (R.play Γ₀ ω) i ∂R.μ) :
    ∃ c : ∀ _ : N, Prog Γ₀, (programGame Γ₀ R).IsProgramEquilibrium c ∧
      (programGame Γ₀ R).Plays c fun ω => R.play Γs ω :=
  ⟨_, algorithm2_isProgramEquilibrium R hSPI.1 hSPI hthreat⟩

end algorithm2

end Prog

end SafeParetoImprovements
