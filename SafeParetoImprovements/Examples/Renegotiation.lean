import SafeParetoImprovements.FullStrategy
import SafeParetoImprovements.Independence
import SafeParetoImprovements.TwoPlayer

/-!
# DiGiovanni's renegotiation example (Appendix B.4), and the "PI but not FI" agent

Source: Anthony DiGiovanni, *CLR's Safe Pareto Improvements Research Agenda* (LessWrong,
20 April 2026), Appendix B.2 and B.4.  The 2022 paper has none of this; the file is
research-facing substrate (RULING 9) with no `Paper node`.

**The example (B.4).**  Agents `A` and `B` negotiate what values to instill in a
successor; if they fail to agree, each attempts to take over.  Before considering SPIs they
are inclined to submit

* `A`: `𝐩ᶠᵃⁱʳ` = "demand 50% of the share of the ASI's values no matter what";
* `B`: `𝐩ʰᵃʷᵏ` = "demand 80%, and trigger a doomsday device if they refuse";

whose demands are incompatible, so the outcome is "`B` triggers a doomsday device".  Their
**renegotiation programs** `rn(𝐩)` are, in the source's pseudocode:

```
def RenegotiationProgram(opponent):
    if opponent.is_renegotiation_type:
        projected_outcome = Simulate(my_base_strategy, opponent.base_strategy)
        my_proposal = my_renegotiation_logic(projected_outcome)
        their_proposal = opponent.renegotiation_logic(projected_outcome)
        if my_proposal == their_proposal:
            return my_proposal
    return my_base_strategy(opponent)
```

with the renegotiation logic "if they refuse, propose 'attempt takeover, without any
doomsday devices'".  `rn(𝐩ᶠᵃⁱʳ)` and `rn(𝐩ʰᵃʷᵏ)` demand 50% and 80% *regardless* of whether
the other program is a renegotiation program (demand preservation), and against each
other reach "both attempt takeover, without any doomsday devices" instead of the doomsday.

**Rendering.**  A base strategy is a demand and a device (`Base`); the negotiation game
`negotiation t d` pays compatible demands as the demanded shares, an incompatible pair
with a doomsday device in play `d` to both, and one without `t` to both.  The source gives
no conflict payoffs, so `t` and `d` are parameters and the SPI claim carries `d ≤ t`.  The
program space is `RnProg` — a base strategy, or the renegotiation program built on one —
with the pseudocode as its execution `run` (each line is cited at the definition).  This
is DiGiovanni et al.'s conditional-commitment setting, not the paper's instruction
language `Prog`: it is given as its own `ProgramGame` (`rnProgramGame`), which is what
makes the repository's execution-level `ParticipationIndependent` and
`ForeknowledgeIndependent` apply to it verbatim.  The representatives only supply the
baseline `Π(Γ₀) = 𝐛₀`; they need not satisfy Assumption 1 (the doomsday device is strictly
dominated in the one-shot game whenever `d < t`, so under Assumption 1 `Π(Γ₀)` could never
trigger it — the source's baseline outcome is a *commitment*, which the delegation model's
representatives cannot make).

**What is proved.**

* Demand preservation of `rn` at both levels: as the source's line 3 vs line 10
  (`run_rn_fst`), and as B.2's `DemandPreserving` for the transformation `𝐟 = rn`
  (`rnStrategy_demandPreserving`).
* The B.4 numbers: `𝐩ᶠᵃⁱʳ` vs `𝐩ʰᵃʷᵏ` is the doomsday, `rn(𝐩ᶠᵃⁱʳ)` vs `rn(𝐩ʰᵃʷᵏ)` the
  takeover without devices (`outcome_fair_hawk`, `outcome_rn_fair_hawk`), and `rn` is an
  SPI in B.1's sense on the space of all base-strategy profiles (`rn_isSPITransformation`).
* Participation independence of the renegotiation profile, both as B.2 defines it —
  simultaneous submission plus demand preservation (`rnStrategy_participationIndependent`)
  — and as `Independence.lean` defines it, execution by execution
  (`rn_participationIndependent`), for every baseline.
* Foreknowledge independence of the policy that submits `rn(𝐛)` uninformed and `𝐛` itself
  when told the counterpart will not participate (`rnFallbackPolicy_foreknowledgeIndependent`).
* **B.2's "PI but not FI" agent**, with the source's numbers: an agent who demands 60%
  whether or not the counterpart participates, but would have demanded 50% had she known
  the counterpart would not.  She is participation independent and not foreknowledge
  independent at both levels (`sixtyFifty_participationIndependent`,
  `sixtyFifty_not_foreknowledgeIndependent`, and the execution-level pair
  `rn_sixty_participationIndependent`, `sixtyFiftyPolicy_not_foreknowledgeIndependent`).
-/

namespace SafeParetoImprovements

namespace Examples

namespace Renegotiation

open Two MeasureTheory

/-! ### Shares, devices, base strategies, outcomes -/

/-- The demands that occur in the source: 50%, 60%, 80% of the successor's values. -/
inductive Share | s50 | s60 | s80
  deriving DecidableEq, Fintype, Inhabited

/-- The share as a real number. -/
noncomputable def Share.toReal : Share → ℝ
  | .s50 => 1 / 2
  | .s60 => 3 / 5
  | .s80 => 4 / 5

/-- Two demands are compatible when they sum to at most the whole: only `50% + 50%`. -/
def Share.compatible : Share → Share → Bool
  | .s50, .s50 => true
  | _, _ => false

lemma Share.compatible_iff (a b : Share) : a.compatible b = true ↔ a.toReal + b.toReal ≤ 1 := by
  cases a <;> cases b <;> norm_num [Share.compatible, Share.toReal]

/-- Whether a base strategy triggers a doomsday device on refusal. -/
inductive Device | none | doomsday
  deriving DecidableEq, Fintype, Inhabited

/-- A base strategy: a demand, and what to do if refused. -/
abbrev Base := Share × Device

/-- Both players' action sets are `Base`. -/
abbrev NUniverse : Two → Type := fun _ => Base

/-- What the negotiation ends in. -/
inductive Outcome
  | split (a b : Share)
  | takeover
  | doomsday
  deriving DecidableEq

/-- `Simulate`: the outcome of two base strategies against each other.  Compatible demands
are split; incompatible ones end in a takeover attempt, with a doomsday if either side
brought a device. -/
def outcome (a b : Base) : Outcome :=
  if a.1.compatible b.1 then .split a.1 b.1
  else if a.2 = .doomsday ∨ b.2 = .doomsday then .doomsday else .takeover

/-- The payoff of an outcome: the shares when split, `t` to both for a takeover attempt
without devices, `d` to both for a doomsday. -/
noncomputable def Outcome.payoff (t d : ℝ) : Outcome → Two → ℝ
  | .split a _, .one => a.toReal
  | .split _ b, .two => b.toReal
  | .takeover, _ => t
  | .doomsday, _ => d

/-- **The negotiation game**: every base strategy is available to both players, and a
profile is paid as its outcome. -/
noncomputable def negotiation (t d : ℝ) : Game Two NUniverse where
  S _ := Finset.univ
  nonempty _ := ⟨(.s50, .none), Finset.mem_univ _⟩
  u a i := (outcome (a .one) (a .two)).payoff t d i

/-- `𝐩ᶠᵃⁱʳ`: demand 50%, no device. -/
def fair : Base := (.s50, .none)

/-- `𝐩ʰᵃʷᵏ`: demand 80%, doomsday device if refused. -/
def hawk : Base := (.s80, .doomsday)

lemma outcome_fair_hawk : outcome fair hawk = .doomsday := rfl

/-! ### The renegotiation programs and their execution -/

/-- The program space: a base strategy, or the renegotiation program built on one. -/
inductive RnProg
  | base (b : Base)
  | rn (b : Base)
  deriving DecidableEq

/-- `my_base_strategy` of either kind of program. -/
def RnProg.baseOf : RnProg → Base
  | .base b => b
  | .rn b => b

/-- `is_renegotiation_type`. -/
def RnProg.isRn : RnProg → Bool
  | .base _ => false
  | .rn _ => true

/-- The demands made by a program: those of its base strategy (`d(rn(𝐩ᵢ)) = d(𝐩ᵢ)`). -/
def RnProg.demand (q : RnProg) : Share := q.baseOf.1

/-- The renegotiation logic of both agents in B.4: on a conflict, propose "attempt takeover,
without any doomsday devices"; on a split, nothing. -/
def renegotiationLogic : Outcome → Option Outcome
  | .split _ _ => none
  | .takeover => some .takeover
  | .doomsday => some .takeover

/-- Carrying out an agreed proposal, for the player with base strategy `b`: the same
demand, with the device disarmed for a takeover without devices. -/
def enact (b : Base) : Outcome → Base
  | .split _ _ => b
  | .takeover => (b.1, .none)
  | .doomsday => (b.1, .doomsday)

/-- **The pseudocode**, from the running player's side.  Line 2: a base program, or a
renegotiation program facing a non-renegotiation type, acts by its base strategy (line
10).  Lines 3–8 for two renegotiation programs: simulate the base strategies, form both
proposals from the projected outcome, and act on the proposal if they match; otherwise
line 10. -/
def run (mine theirs : RnProg) : Base :=
  match mine, theirs with
  | .base b, _ => b
  | .rn b, .base _ => b
  | .rn b, .rn b' =>
    match renegotiationLogic (outcome b b'), renegotiationLogic (outcome b b') with
    | some p, some q => if p = q then enact b p else b
    | _, _ => b

/-- **Line 3 against line 10**: a renegotiation program makes its base strategy's demand
whatever the opponent's program is. -/
lemma run_rn_fst (b : Base) (q : RnProg) : (run (.rn b) q).1 = b.1 := by
  rcases q with b' | b'
  · rfl
  · rcases b with ⟨a, x⟩; rcases b' with ⟨a', x'⟩
    cases a <;> cases a' <;> cases x <;> cases x' <;> rfl

lemma run_base (b : Base) (q : RnProg) : run (.base b) q = b := rfl

lemma run_rn_base (b b' : Base) : run (.rn b) (.base b') = b := rfl

/-- The renegotiated actions of B.4: `50%` and `80%`, devices off. -/
lemma run_rn_fair_hawk : run (.rn fair) (.rn hawk) = (.s50, .none) := rfl
lemma run_rn_hawk_fair : run (.rn hawk) (.rn fair) = (.s80, .none) := rfl

/-- **B.4's Pareto improvement**: against each other the renegotiation programs reach the
takeover without devices, not the doomsday. -/
lemma outcome_rn_fair_hawk :
    outcome (run (.rn fair) (.rn hawk)) (run (.rn hawk) (.rn fair)) = .takeover := rfl

/-- The realised action profile of a program profile: each player runs her own program
against the other's. -/
def realised (c : Two → RnProg) : ∀ i, NUniverse i := fun i => run (c i) (c i.other)

/-- Program-level payoff: the negotiation game's payoff of the realised profile. -/
noncomputable def programPayoff (t d : ℝ) (c : Two → RnProg) (i : Two) : ℝ :=
  (negotiation t d).u (realised c) i

/-- The transformation `𝐟 = rn`, applied to every agent's program. -/
def rnTransform (c : Two → RnProg) : Two → RnProg := fun i => .rn (c i).baseOf

/-- The full strategy `(rn, 𝐩)`. -/
def rnStrategy (p : Two → RnProg) : FullStrategy (fun _ : Two => RnProg) :=
  ⟨rnTransform, p⟩

/-- The demand function, per agent. -/
def demands : ∀ _ : Two, RnProg → Share := fun _ => RnProg.demand

/-- **Demand preservation** of `rn`, as B.2 defines it, for every input profile. -/
lemma rnStrategy_demandPreserving (p : Two → RnProg) :
    (rnStrategy p).DemandPreserving demands := fun _ => rfl

/-- The space of base-strategy profiles: B.4's "before they consider the possibility of
SPIs". -/
def baseProfiles : Set (Two → RnProg) := {p | ∀ i, (p i).isRn = false}

lemma realised_of_base {p : Two → RnProg} (hp : p ∈ baseProfiles) (i : Two) :
    realised p i = (p i).baseOf := by
  have := hp i
  cases h : p i with
  | base b => simp [realised, h, run_base, RnProg.baseOf]
  | rn b => rw [h] at this; cases this

/-- **`rn` is an SPI in B.1's sense** on the space of base-strategy profiles, as soon as a
takeover attempt without devices is no worse than a doomsday for either player (`d ≤ t`).
Compatible demands are split exactly as before; incompatible ones now end in the takeover
without devices, whatever devices the base strategies carried. -/
lemma rn_isSPITransformation {t d : ℝ} (hd : d ≤ t) :
    IsSPITransformation (programPayoff t d) baseProfiles rnTransform := by
  intro p hp i
  have h1 := realised_of_base hp .one
  have h2 := realised_of_base hp .two
  simp only [programPayoff, negotiation]
  rw [h1, h2]
  rcases hp1 : (p .one).baseOf with ⟨a, x⟩
  rcases hp2 : (p .two).baseOf with ⟨a', x'⟩
  simp only [realised, rnTransform, other_one, other_two, hp1, hp2]
  cases i <;> cases a <;> cases a' <;> cases x <;> cases x' <;>
    simp [run, outcome, Outcome.payoff, Share.compatible, renegotiationLogic, enact, hd]

/-! ### The program game and the execution-level notions -/

open Classical in
/-- Representatives supplying the baseline `Π(negotiation t d) = 𝐛₀` — the one-point sample
space, and an arbitrary admissible profile on every other game.  Nothing here claims
Assumption 1 (see the file header). -/
noncomputable def rnRepresentatives (t d : ℝ) (b₀ : Two → Base) :
    Representatives.{0, 0, 0} Two NUniverse where
  Ω := Unit
  μ := Measure.dirac ()
  toPlay :=
    { play := fun Γ _ => if Γ = negotiation t d then b₀ else fun i => (Γ.nonempty i).choose
      mem := by
        intro Γ _
        split_ifs with h
        · subst h; exact fun i => Finset.mem_univ _
        · exact fun i => (Γ.nonempty i).choose_spec }
  measurableSet_fiber _ _ := trivial

open Classical in
lemma rnRepresentatives_play (t d : ℝ) (b₀ : Two → Base) (ω : Unit) :
    (rnRepresentatives t d b₀).play (negotiation t d) ω = b₀ := by
  show (if negotiation t d = negotiation t d then b₀ else _) = b₀
  rw [if_pos rfl]

/-- **The program game of renegotiation programs**: every player submits an `RnProg`, and
the execution is `run`, as a pure mixed action. -/
noncomputable def rnProgramGame (t d : ℝ) (b₀ : Two → Base) :
    ProgramGame (negotiation t d) (rnRepresentatives t d b₀) where
  Instr _ := RnProg
  exec c _ i := (negotiation t d).pureMixed (realised c i) (Finset.mem_univ _)
  measurable_exec _ _ _ := measurable_from_top

lemma rnProgramGame_exec (t d : ℝ) (b₀ : Two → Base) (c : Two → RnProg) (ω : Unit) (i : Two) :
    (rnProgramGame t d b₀).exec c ω i =
      (negotiation t d).pureMixed (realised c i) (Finset.mem_univ _) := rfl

/-- The **default instruction** is the base strategy `𝐛₀ i` itself: everybody at their base
strategy realises `𝐛₀ = Π(Γ₀)`. -/
noncomputable def rnDefault (t d : ℝ) (b₀ : Two → Base) : (rnProgramGame t d b₀).DefaultInstr where
  default i := .base (b₀ i)
  plays_default ω i b := by
    simp only [rnProgramGame_exec, Game.pureMixed_val, rnRepresentatives_play]
    rfl

/-- Against a counterpart at her default, a renegotiation program realises its base
strategy, i.e. exactly what the all-default profile realises. -/
lemma realised_update_rn (b₀ : Two → Base) (c : Two → RnProg) (i : Two)
    (hc : c i = .rn (b₀ i)) (j : Two) (hj : j ≠ i) :
    realised (Function.update c j (.base (b₀ j))) i = realised (fun k => .base (b₀ k)) i := by
  have hji : j = i.other := eq_other_of_ne hj
  subst hji
  simp only [realised, Function.update_self, Function.update_of_ne (other_ne i).symm, hc,
    run_rn_base, run_base]

/-- **Execution-level participation independence** of a renegotiation program, for every
baseline: when the counterpart does not participate, the program realises its base
strategy, which is what the baseline realises. -/
lemma rn_participationIndependent (t d : ℝ) (b₀ : Two → Base) (c : Two → RnProg) (i : Two)
    (hc : c i = .rn (b₀ i)) :
    (rnProgramGame t d b₀).ParticipationIndependent (rnDefault t d b₀) c i := by
  intro j hj ω
  rw [rnProgramGame_exec, rnProgramGame_exec]
  congr 1
  exact realised_update_rn b₀ c i hc j hj

/-- **B.2's participation independence** of the renegotiation full strategy, for any base
profile, under any simultaneous choice model consistent with it. -/
lemma rnStrategy_participationIndependent (p : Two → RnProg)
    (χ : ChoiceModel (fun _ : Two => RnProg)) (hsim : χ.Simultaneous)
    (hcons : (rnStrategy p).Consistent χ) :
    (rnStrategy p).ParticipationIndependent demands χ :=
  (rnStrategy p).participationIndependent_of_simultaneous demands χ hsim hcons
    (rnStrategy_demandPreserving p)

/-- The B.4 profile: `A` submits `rn(𝐩ᶠᵃⁱʳ)`, `B` submits `rn(𝐩ʰᵃʷᵏ)`. -/
def fairHawkRn : Two → RnProg := Two.pair (.rn fair) (.rn hawk)

/-- The B.4 baseline. -/
def fairHawk : Two → Base := Two.pair fair hawk

/-- Both B.4 renegotiation programs are participation independent against the B.4
baseline. -/
lemma fairHawkRn_participationIndependent (t d : ℝ) (i : Two) :
    (rnProgramGame t d fairHawk).ParticipationIndependent (rnDefault t d fairHawk) fairHawkRn i :=
  rn_participationIndependent t d fairHawk fairHawkRn i (by cases i <;> rfl)

/-- The B.4 profile executes as the renegotiated outcome: `(50%, no device)`,
`(80%, no device)`. -/
lemma fairHawkRn_plays (t d : ℝ) :
    (rnProgramGame t d fairHawk).Plays fairHawkRn fun _ => Two.pair (.s50, .none) (.s80, .none) := by
  intro ω i b
  rw [rnProgramGame_exec, Game.pureMixed_val]
  cases i <;> rfl

/-- The policy that submits `rn(𝐛)` uninformed and the base strategy `𝐛` itself on learning
that a counterpart will not participate ("if agent `i` believed that agent `j` wouldn't
participate in `𝐟`, neither would `i`"). -/
noncomputable def rnFallbackPolicy (t d : ℝ) (b₀ : Two → Base) (i : Two) (b : Base) :
    (rnProgramGame t d b₀).Policy i where
  Signal := Bool
  noInfo := false
  willNotParticipate _ := true
  policy
    | false => .rn b
    | true => .base b

/-- **Execution-level foreknowledge independence** of the fall-back policy: once the
counterpart has dropped out, `rn(𝐛)` and `𝐛` realise the same action.  The two instructions
are different programs; only their behaviour after the drop-out coincides. -/
lemma rnFallbackPolicy_foreknowledgeIndependent (t d : ℝ) (b₀ : Two → Base) (i : Two)
    (b : Base) (c : Two → RnProg) :
    (rnProgramGame t d b₀).ForeknowledgeIndependent (rnDefault t d b₀) c
      (rnFallbackPolicy t d b₀ i b) := by
  intro j hj ω
  rw [rnProgramGame_exec, rnProgramGame_exec]
  congr 1
  have hji : j = i.other := eq_other_of_ne hj
  subst hji
  simp only [realised, Function.update_self, Function.update_of_ne (other_ne i),
    rnFallbackPolicy, rnDefault, run_rn_base, run_base]

/-! ### B.2's "PI but not FI" agent: 60% regardless, 50% with foreknowledge -/

/-- The agent who "demands 60% of the pie independently of whether the counterpart
participates, yet would have only demanded 50% had they known the counterpart wouldn't
participate": her chosen input program does not depend on what `B` actually uses, and
depends on what she believes `B` uses only through whether it is a renegotiation type.
`B`'s choices are fixed at his base strategy `bB`. -/
def sixtyFifty (bB : Base) : ChoiceModel (fun _ : Two => RnProg) where
  ofParticipation
    | .one, _ => .base (.s60, .none)
    | .two, _ => .base bB
  ofBelief
    | .one, q => if (q .two).isRn then .base (.s60, .none) else .base (.s50, .none)
    | .two, _ => .base bB

/-- Her full strategy: `rn` applied to the input profile `(60%, bB)`. -/
def sixtyFiftyStrategy (bB : Base) : FullStrategy (fun _ : Two => RnProg) :=
  rnStrategy (Two.pair (.base (.s60, .none)) (.base bB))

lemma sixtyFifty_simultaneous (bB : Base) : (sixtyFifty bB).Simultaneous := by
  intro i q q'; cases i <;> rfl

lemma sixtyFifty_consistent (bB : Base) : (sixtyFiftyStrategy bB).Consistent (sixtyFifty bB) := by
  intro i; cases i <;> exact ⟨rfl, rfl⟩

/-- She is **participation independent** in B.2's sense. -/
lemma sixtyFifty_participationIndependent (bB : Base) :
    (sixtyFiftyStrategy bB).ParticipationIndependent demands (sixtyFifty bB) :=
  rnStrategy_participationIndependent _ _ (sixtyFifty_simultaneous bB) (sixtyFifty_consistent bB)

/-- Had she known `B` would not participate, she would have demanded 50%. -/
lemma sixtyFifty_counterfactualF (bB : Base) :
    (sixtyFiftyStrategy bB).counterfactualF (sixtyFifty bB) .one = .base (.s50, .none) := rfl

/-- She is **not foreknowledge independent** in B.2's sense: the counterfactual demand is
50%, the actual one 60%. -/
lemma sixtyFifty_not_foreknowledgeIndependent (bB : Base) :
    ¬ (sixtyFiftyStrategy bB).ForeknowledgeIndependent demands (sixtyFifty bB) :=
  (sixtyFiftyStrategy bB).not_foreknowledgeIndependent_of_demand_ne demands (sixtyFifty bB)
    (i := .one) (by show Share.s50 ≠ Share.s60; decide)

/-- The same agent at the execution level: uninformed she submits `rn(60%)`; told that `B`
will not participate she submits her counterfactual input program, `50%`. -/
noncomputable def sixtyFiftyPolicy (t d : ℝ) (bB : Base) :
    (rnProgramGame t d (Two.pair (.s60, .none) bB)).Policy .one where
  Signal := Bool
  noInfo := false
  willNotParticipate _ := true
  policy
    | false => .rn (.s60, .none)
    | true => .base (.s50, .none)

/-- **Execution-level participation independence** of her uninformed program `rn(60%)`. -/
lemma rn_sixty_participationIndependent (t d : ℝ) (bB : Base) (c : Two → RnProg)
    (hc : c .one = .rn (.s60, .none)) :
    (rnProgramGame t d (Two.pair (.s60, .none) bB)).ParticipationIndependent
      (rnDefault t d (Two.pair (.s60, .none) bB)) c .one :=
  rn_participationIndependent t d _ c .one hc

/-- **Execution-level failure of foreknowledge independence**: once `B` has dropped out
she demands 60% if she chose uninformed and 50% if she chose knowing — different realised
actions, whatever `B`'s base strategy. -/
lemma sixtyFiftyPolicy_not_foreknowledgeIndependent (t d : ℝ) (bB : Base) (c : Two → RnProg) :
    ¬ (rnProgramGame t d (Two.pair (.s60, .none) bB)).ForeknowledgeIndependent
      (rnDefault t d (Two.pair (.s60, .none) bB)) c (sixtyFiftyPolicy t d bB) := by
  intro h
  have := congrArg (fun m => m.val ⟨(.s60, .none), Finset.mem_univ _⟩) (h .two (by decide) ())
  simp only [rnProgramGame_exec, Game.pureMixed_val, realised, Function.update_self,
    Function.update_of_ne (show Two.two ≠ Two.one by decide), other_one, sixtyFiftyPolicy,
    rnDefault, run_rn_base, run_base] at this
  simp at this

end Renegotiation

end Examples

end SafeParetoImprovements
