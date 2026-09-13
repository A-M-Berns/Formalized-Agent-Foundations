import SafeParetoImprovements.Instruction

/-!
# Participation independence and foreknowledge independence (substrate beyond the paper)

The 2022 paper has no counterpart for these notions; they are research-facing hooks added
so that later work on SPI *selection* can be stated against this formalization (the
scoping ruling recorded in `notes/scoping.md` §8).  Nothing here carries a `Paper node`,
and no theorem *of the paper* is claimed about them; what is proved is stated below.  The
informal notions being rendered:

* **Participation independence (PI)**: a player's behaviour when a counterpart does *not*
  participate in the SPI scheme is the same as it would have been had the scheme never
  been proposed — no punishment, no threat.
* **Foreknowledge independence (FI)**: a player's behaviour when a counterpart does not
  participate is the same as it would have been had the player *known in advance* that the
  counterpart would not participate.

Three ingredients make them stateable over the program-game interface:

1. a **default (non-participation) instruction** per player whose execution is `Π(Γ₀)`,
   the paper's own "no SPI" baseline (`ProgramGame.DefaultInstr`, `dd:default-instr`);
   "player `j` did not participate" is the profile `c[j := default j]`;
2. PI itself: when `j` drops out, `i` behaves exactly as under everybody's default;
3. an **information stage** for FI: an instruction chosen as a function of a signal that
   may announce a counterpart's non-participation (`ProgramGame.Policy`).

In the concrete language, `Prog.default` is "play `Πᵢ(Γ₀)`", the dove-ish instruction
`Prog.dove` (comply with the SPI when everybody does, otherwise fall back to the default)
satisfies PI, and any instruction that punishes with a mixed action differing from the
default play — Algorithm 2 whenever its minimax punishment differs from `Π(Γ₀)` — fails it.

**What these execution-level notions are, and are not.**  Both compare *realised actions
towards a non-participant*: PI says a player meets a drop-out with the baseline play
rather than a punishment, which is the premise of the source's argument for PI ("the
counterpart's bargaining position is no worse than if they'd refused the SPI"); FI says
the realised action towards a drop-out does not depend on whether the drop-out was
foreseen.  Neither constrains what a player *demands while everybody participates*: the
source's definitions (DiGiovanni 2026, Appendix B.2) add **demand preservation** to both,
and that clause lives at the level of program choice in `FullStrategy.lean`, not here.  An
instruction that raises its demand whenever the counterpart participates, and falls back
to the default otherwise, satisfies the execution-level PI below and is not
demand-preserving.  The two levels are exhibited together on one example in
`Examples/Renegotiation.lean`.

**What is proved here beyond definitions and witnesses.**  The dove profile executes the
SPI (`plays_dove`), is participation independent for every player
(`participationIndependent_dove_all`), and is a program equilibrium whenever each player's
expected best reply to the baseline is at most her expected SPI payoff
(`dove_isProgramEquilibrium`, a sufficient criterion); a participation-independent
instruction paired with the default as the informed choice is foreknowledge independent
(`foreknowledgeIndependent_of_participationIndependent`).
-/

universe u v w x y

namespace SafeParetoImprovements

open StrategicGame MeasureTheory Filter Set

variable {N : Type u} {𝒜 : N → Type v}

namespace ProgramGame

variable {Γ₀ : Game N 𝒜} {R : Representatives.{u, v, w} N 𝒜} (P : ProgramGame.{u, v, w, x} Γ₀ R)
variable [DecidableEq N] [∀ i, DecidableEq (𝒜 i)]

/-- **A default instruction** per player (`dd:default-instr`): the instruction of a player
who does not take part in any SPI scheme.  Its execution is the paper's baseline
`Π(Γ₀)`. -/
structure DefaultInstr where
  /-- The non-participation instruction of each player. -/
  default : ∀ i, P.Instr i
  /-- Everybody at their default executes as `Π(Γ₀)`. -/
  plays_default : P.Plays default fun ω => R.play Γ₀ ω

/-- **Participation independence** of player `i`'s instruction in the profile `c`: whenever
some other player `j` does not participate, `i` behaves exactly as under everybody's
default. -/
def ParticipationIndependent (D : P.DefaultInstr) (c : ∀ i, P.Instr i) (i : N) : Prop :=
  ∀ j, j ≠ i → ∀ ω, P.exec (Function.update c j (D.default j)) ω i = P.exec D.default ω i

/-- **An information stage** for player `i`: a signal type with a no-information value and
a value announcing each counterpart's non-participation, and a policy choosing the
instruction from the signal. -/
structure Policy (i : N) where
  /-- The signals player `i` may receive before choosing an instruction. -/
  Signal : Type y
  /-- The uninformative signal. -/
  noInfo : Signal
  /-- The signal "player `j` will not participate". -/
  willNotParticipate : N → Signal
  /-- The instruction chosen on each signal. -/
  policy : Signal → P.Instr i

/-- **Foreknowledge independence** of player `i`'s policy `π` against the others'
instructions `c`: when `j` does not participate, `i` behaves the same whether `i` chose
her instruction uninformed or knowing that `j` would not participate. -/
def ForeknowledgeIndependent (D : P.DefaultInstr) (c : ∀ i, P.Instr i) {i : N}
    (π : P.Policy i) : Prop :=
  ∀ j, j ≠ i → ∀ ω,
    P.exec (Function.update (Function.update c j (D.default j)) i (π.policy π.noInfo)) ω i =
      P.exec (Function.update (Function.update c j (D.default j)) i
        (π.policy (π.willNotParticipate j))) ω i

/-- A policy that ignores its signal is foreknowledge independent.  This is the
**degenerate** case and is worth nothing as a non-vacuity witness: both sides of
`ForeknowledgeIndependent` are then literally the same term, so the predicate holds by
`rfl` whatever the execution model does.  A witness with content needs a policy whose two
signals select *different* instructions; `Examples.foreknowledgeIndependent_pd` is one. -/
lemma foreknowledgeIndependent_of_const (D : P.DefaultInstr) (c : ∀ i, P.Instr i) {i : N}
    (π : P.Policy i) (hπ : ∀ s, π.policy s = π.policy π.noInfo) :
    P.ForeknowledgeIndependent D c π := by
  intro j _ ω
  rw [hπ (π.willNotParticipate j)]

end ProgramGame

namespace Prog

variable {Γ₀ : Game N 𝒜} (R : Representatives.{u, v, w} N 𝒜)
variable [DecidableEq N] [Fintype N] [∀ i, DecidableEq (𝒜 i)]

variable (Γ₀) in
/-- **The default instruction**: play `Πᵢ(Γ₀)` — delegate the base game. -/
noncomputable def default : Prog Γ₀ := delegate Γ₀ (Game.IsSubsetGameOf.refl Γ₀)

variable (Γ₀) in
/-- Everybody delegating the base game executes as `Π(Γ₀)`. -/
lemma plays_default :
    (programGame Γ₀ R).Plays (fun _ => default Γ₀) fun ω => R.play Γ₀ ω := by
  intro ω k b
  rw [programGame_exec, default, execAt_delegate, Game.pureMixed_val]

variable (Γ₀) in
/-- `Prog.default` as the default instruction of the realised program game. -/
noncomputable def defaultInstr : (programGame Γ₀ R).DefaultInstr where
  default _ := default Γ₀
  plays_default := plays_default Γ₀ R

/-- **The dove-ish instruction**: comply with the SPI `Γˢ` when everybody submits this
code, otherwise fall back to the default. -/
noncomputable def dove (Γs : Game N 𝒜) (h : Γs.IsSubsetGameOf Γ₀) : Prog Γ₀ :=
  ifAllSame (delegate Γs h) fun _ => default Γ₀

/-- Any instruction that falls back to the default when somebody's code differs is
participation independent, whatever the others submit. -/
lemma participationIndependent_of_punish_default (c : N → Prog Γ₀) (i : N) (t : Prog Γ₀)
    (hc : c i = ifAllSame t fun _ => default Γ₀) :
    (programGame Γ₀ R).ParticipationIndependent (defaultInstr Γ₀ R) c i := by
  intro j hj ω
  have hcj : Function.update c j (default Γ₀) i = c i := Function.update_of_ne (Ne.symm hj) _ _
  show execAt R (Function.update c j (default Γ₀)) i (Function.update c j (default Γ₀) i) ω =
    execAt R (fun _ => default Γ₀) i (default Γ₀) ω
  rw [hcj, hc]
  have hne : ¬ ∀ l, Function.update c j (default Γ₀) l = Function.update c j (default Γ₀) i := fun hall => by
    have := hall j
    rw [Function.update_self, hcj, hc, default] at this
    cases this
  obtain ⟨l, -, hexec⟩ := execAt_ifAllSame_of_ne R hne t (fun _ => default Γ₀) ω
  rw [hexec]
  rfl

/-- The dove-ish instruction is participation independent. -/
lemma participationIndependent_dove (Γs : Game N 𝒜) (h : Γs.IsSubsetGameOf Γ₀)
    (c : N → Prog Γ₀) (i : N) (hc : c i = dove Γs h) :
    (programGame Γ₀ R).ParticipationIndependent (defaultInstr Γ₀ R) c i :=
  participationIndependent_of_punish_default R c i _ hc

/-! ### The dove profile: participation-independent implementation of an SPI

When everybody submits the dove-ish instruction for `Γˢ`, the execution is `Π(Γˢ)`
(`plays_dove`); against a unilateral deviation every other player falls back to the
baseline play `Πⱼ(Γ₀)` (`exec_update_dove`).  So the dove profile is participation
independent for every player, and it is a program equilibrium whenever the SPI beats each
player's expected best reply to the baseline (`ProgramGame.isProgramEquilibrium_of_fallback`).
This is the participation-independent counterpart of Proposition 18: Algorithm 2 punishes
with the minimax profile, which is what makes it a program equilibrium under the
threat-point hypothesis and what makes it fail participation independence
(`not_participationIndependent_algorithm2`). -/

variable {Γs : Game N 𝒜} (h : Γs.IsSubsetGameOf Γ₀)

/-- When everybody submits the dove-ish instruction, the execution is `Π(Γˢ)`. -/
lemma plays_dove :
    (programGame Γ₀ R).Plays (fun _ => dove Γs h) fun ω => R.play Γs ω := by
  intro ω k b
  rw [programGame_exec, dove, execAt_ifAllSame_of_all R (fun _ => rfl), execAt_delegate,
    Game.pureMixed_val]

/-- Against a unilateral deviation by `i`, every other dove falls back to the baseline play
`Πⱼ(Γ₀)`. -/
lemma exec_update_dove (i : N) (c' : Prog Γ₀) (hc : c' ≠ dove Γs h) (ω : R.Ω) (j : N)
    (hj : j ≠ i) :
    (programGame Γ₀ R).exec (Function.update (fun _ => dove Γs h) i c') ω j =
      Γ₀.pureMixed (R.play Γ₀ ω j) (R.toPlay.mem Γ₀ ω j) := by
  have hne : ¬ ∀ l, Function.update (fun _ : N => dove Γs h) i c' l =
      Function.update (fun _ : N => dove Γs h) i c' j := fun hall => by
    have := hall i
    rw [Function.update_self, Function.update_of_ne hj] at this
    exact hc this
  rw [programGame_exec]
  show execAt R (Function.update (fun _ : N => dove Γs h) i c') j
    (Function.update (fun _ : N => dove Γs h) i c' j) ω = _
  rw [Function.update_of_ne hj]
  show execAt R _ j (ifAllSame (delegate Γs h) fun _ => default Γ₀) ω = _
  obtain ⟨l, -, hexec⟩ :=
    execAt_ifAllSame_of_ne R hne (delegate Γs h) (fun _ => default Γ₀) ω
  rw [hexec, default, execAt_delegate]

/-- The dove profile is participation independent for every player. -/
lemma participationIndependent_dove_all (i : N) :
    (programGame Γ₀ R).ParticipationIndependent (defaultInstr Γ₀ R) (fun _ => dove Γs h) i :=
  participationIndependent_dove R Γs h _ i rfl

/-- **The dove profile is a program equilibrium** as soon as, for every player, the expected
best reply to the baseline play `Π(Γ₀)` is at most the expected payoff of the SPI play
`Π(Γˢ)`.  Together with `participationIndependent_dove_all` and `plays_dove`: under this
criterion the SPI is implementable by a participation-independent program equilibrium, with
no punishment at all. -/
lemma dove_isProgramEquilibrium
    (hcrit : ∀ i, ∫ ω, Γ₀.bestReply i (R.play Γ₀ ω) ∂R.μ ≤ ∫ ω, Γ₀.u (R.play Γs ω) i ∂R.μ) :
    (programGame Γ₀ R).IsProgramEquilibrium (fun _ => dove Γs h) :=
  (programGame Γ₀ R).isProgramEquilibrium_of_fallback h _ (plays_dove R h)
    (fun i c' hc ω j hj => exec_update_dove R h i c' hc ω j hj) hcrit

/-! ### Participation independence yields foreknowledge independence -/

/-- The default instruction executes as the baseline play whatever the others submit. -/
lemma exec_update_default (c : N → Prog Γ₀) (i : N) (ω : R.Ω) :
    (programGame Γ₀ R).exec (Function.update c i (default Γ₀)) ω i =
      Γ₀.pureMixed (R.play Γ₀ ω i) (R.toPlay.mem Γ₀ ω i) := by
  rw [programGame_exec]
  show execAt R _ i (Function.update c i (default Γ₀) i) ω = _
  rw [Function.update_self, default, execAt_delegate]

/-- Everybody at the default executes as the baseline play, as a mixed action. -/
lemma exec_default (i : N) (ω : R.Ω) :
    (programGame Γ₀ R).exec (fun _ => default Γ₀) ω i =
      Γ₀.pureMixed (R.play Γ₀ ω i) (R.toPlay.mem Γ₀ ω i) := by
  rw [programGame_exec]
  show execAt R _ i (default Γ₀) ω = _
  rw [default, execAt_delegate]

/-- **A participation-independent instruction, paired with the default as the informed
choice, is foreknowledge independent**: if player `i`'s uninformed instruction `c i` is
participation independent and her policy switches to the default instruction on learning
that `j` will not participate, then her realised action once `j` has dropped out is the
baseline play either way.  This is the general form of `Examples.foreknowledgeIndependent_pd`
and one way the two notions interact; it needs the informed branch to be the default. -/
lemma foreknowledgeIndependent_of_participationIndependent (c : N → Prog Γ₀) {i : N}
    (π : (programGame Γ₀ R).Policy i) (hno : π.policy π.noInfo = c i)
    (hinf : ∀ j, π.policy (π.willNotParticipate j) = default Γ₀)
    (hpi : (programGame Γ₀ R).ParticipationIndependent (defaultInstr Γ₀ R) c i) :
    (programGame Γ₀ R).ForeknowledgeIndependent (defaultInstr Γ₀ R) c π := by
  intro j hj ω
  rw [hno, hinf j, exec_update_default]
  have hself : (Function.update (Function.update c j ((defaultInstr Γ₀ R).default j)) i (c i) :
      ∀ a, (programGame Γ₀ R).Instr a) = Function.update c j ((defaultInstr Γ₀ R).default j) :=
    Function.update_eq_self_iff.2 (Function.update_of_ne (Ne.symm hj) _ _).symm
  rw [hself]
  exact (hpi j hj ω).trans (exec_default R i ω)

/-- An instruction that punishes any deviation with the fixed mixed action `σ` is *not*
participation independent as soon as `σᵢ` differs from the default play at some sample
point (and there is somebody to drop out). -/
lemma not_participationIndependent_of_punish_play (c : N → Prog Γ₀) (i : N) (t : Prog Γ₀)
    (σ : ∀ j, Γ₀.Mixed j) (hc : c i = ifAllSame t fun _ => play σ) {j : N} (hj : j ≠ i)
    (hσ : ∃ ω, σ i ≠ Γ₀.pureMixed (R.play Γ₀ ω i) (R.toPlay.mem Γ₀ ω i)) :
    ¬ (programGame Γ₀ R).ParticipationIndependent (defaultInstr Γ₀ R) c i := by
  intro hpi
  obtain ⟨ω, hω⟩ := hσ
  have hcj : Function.update c j (default Γ₀) i = c i := Function.update_of_ne (Ne.symm hj) _ _
  have this : execAt R (Function.update c j (default Γ₀)) i (Function.update c j (default Γ₀) i) ω =
      execAt R (fun _ => default Γ₀) i (default Γ₀) ω := hpi j hj ω
  rw [hcj, hc] at this
  have hne : ¬ ∀ l, Function.update c j (default Γ₀) l = Function.update c j (default Γ₀) i := fun hall => by
    have := hall j
    rw [Function.update_self, hcj, hc, default] at this
    cases this
  obtain ⟨l, -, hexec⟩ := execAt_ifAllSame_of_ne R hne t (fun _ => play σ) ω
  rw [hexec, execAt_play] at this
  exact hω this

/-- **Algorithm 2 is not participation independent** whenever its punishment of a
non-participating `j` — `i`'s coordinate of the minimax profile against `j` — differs
from the default play at some sample point.  The hypothesis is satisfiable: it is
discharged in the Demand Game by
`Examples.demandGame_algorithm2_not_participationIndependent`.  It genuinely fails in the
Prisoner's Dilemma, where the minimax punishment and
the default play are both `Defect`. -/
lemma not_participationIndependent_algorithm2 (Γs : Game N 𝒜) (h : Γs.IsSubsetGameOf Γ₀)
    (i : N) {j : N} (hj : j ≠ i)
    (hσ : ∃ ω, Γ₀.minimax j i ≠ Γ₀.pureMixed (R.play Γ₀ ω i) (R.toPlay.mem Γ₀ ω i)) :
    ¬ (programGame Γ₀ R).ParticipationIndependent (defaultInstr Γ₀ R) (fun _ => algorithm2 Γs h) i := by
  intro hpi
  obtain ⟨ω, hω⟩ := hσ
  have hcj : Function.update (fun _ : N => algorithm2 Γs h) j (default Γ₀) i = algorithm2 Γs h :=
    Function.update_of_ne (Ne.symm hj) _ _
  have this : execAt R (Function.update (fun _ : N => algorithm2 Γs h) j (default Γ₀)) i
      (Function.update (fun _ : N => algorithm2 Γs h) j (default Γ₀) i) ω =
      execAt R (fun _ => default Γ₀) i (default Γ₀) ω := hpi j hj ω
  rw [hcj] at this
  have hne : ¬ ∀ l, Function.update (fun _ : N => algorithm2 Γs h) j (default Γ₀) l =
      Function.update (fun _ : N => algorithm2 Γs h) j (default Γ₀) i := fun hall => by
    have := hall j
    rw [Function.update_self, hcj, default, algorithm2] at this
    cases this
  obtain ⟨l, hl, hexec⟩ :=
    execAt_ifAllSame_of_ne R hne (delegate Γs h) (fun j => play (Γ₀.minimax j)) ω
  have hlj : l = j := by
    by_contra hlj
    exact hl (by rw [Function.update_of_ne hlj, hcj])
  have hexec' : execAt R (Function.update (fun _ : N => algorithm2 Γs h) j (default Γ₀)) i
      (algorithm2 Γs h) ω =
      execAt R (Function.update (fun _ : N => algorithm2 Γs h) j (default Γ₀)) i
        (play (Γ₀.minimax l)) ω := hexec
  rw [hexec', hlj, execAt_play, default, execAt_delegate] at this
  exact hω this

/-- A policy that switches to a punishing instruction on learning that `j` will not
participate is *not* foreknowledge independent, as soon as the punishment differs from
the uninformed behaviour: here the uninformed instruction is dove-ish and the informed one
punishes with `σ`. -/
lemma not_foreknowledgeIndependent_of_switch (Γs : Game N 𝒜) (h : Γs.IsSubsetGameOf Γ₀)
    (c : N → Prog Γ₀) (i : N) (σ : ∀ j, Γ₀.Mixed j) {j : N} (hj : j ≠ i)
    (π : (programGame Γ₀ R).Policy i) (hno : π.policy π.noInfo = dove Γs h)
    (hyes : π.policy (π.willNotParticipate j) = play σ)
    (hσ : ∃ ω, σ i ≠ Γ₀.pureMixed (R.play Γ₀ ω i) (R.toPlay.mem Γ₀ ω i)) :
    ¬ (programGame Γ₀ R).ForeknowledgeIndependent (defaultInstr Γ₀ R) c π := by
  intro hfi
  obtain ⟨ω, hω⟩ := hσ
  have this : execAt R (Function.update (Function.update c j (default Γ₀)) i (π.policy π.noInfo)) i
      (Function.update (Function.update c j (default Γ₀)) i (π.policy π.noInfo) i) ω =
      execAt R (Function.update (Function.update c j (default Γ₀)) i
        (π.policy (π.willNotParticipate j))) i
      (Function.update (Function.update c j (default Γ₀)) i (π.policy (π.willNotParticipate j)) i) ω :=
    hfi j hj ω
  rw [hno, hyes, Function.update_self, Function.update_self] at this
  have hne : ¬ ∀ l, Function.update (Function.update c j (default Γ₀)) i (dove Γs h) l =
      Function.update (Function.update c j (default Γ₀)) i (dove Γs h) i := fun hall => by
    have := hall j
    rw [Function.update_self, Function.update_of_ne hj, Function.update_self, default, dove] at this
    cases this
  obtain ⟨l, -, hexec⟩ := execAt_ifAllSame_of_ne R hne (delegate Γs h) (fun _ => default Γ₀) ω
  have hexec' : execAt R (Function.update (Function.update c j (default Γ₀)) i (dove Γs h)) i
      (dove Γs h) ω =
      execAt R (Function.update (Function.update c j (default Γ₀)) i (dove Γs h)) i (default Γ₀) ω :=
    hexec
  rw [hexec', default, execAt_delegate, execAt_play] at this
  exact hω this.symm

end Prog

end SafeParetoImprovements
