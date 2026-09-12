import SafeParetoImprovements.Instruction

/-!
# Participation independence and foreknowledge independence (substrate beyond the paper)

The 2022 paper has no counterpart for these notions; they are research-facing hooks added
so that later work on SPI *selection* can be stated against this formalization (RULING 9).
Nothing here carries a `Paper node`, and no theorem beyond non-vacuity is claimed.  The
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
-/

universe u v w x

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
  Signal : Type
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

/-- A policy that ignores its signal is foreknowledge independent. -/
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
from the default play at some sample point. -/
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
