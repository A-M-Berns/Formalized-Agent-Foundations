import SafeParetoImprovements.FullStrategy
import SafeParetoImprovements.Independence
import SafeParetoImprovements.TwoPlayer

/-!
# DiGiovanni's renegotiation example (Appendix B.4), and the "PI but not FI" agent

Source: Anthony DiGiovanni, *CLR's Safe Pareto Improvements Research Agenda* (LessWrong,
20 April 2026), Appendix B.2 and B.4.  The 2022 paper has none of this; the file is
research-facing substrate beyond the paper (see `Independence.lean`) with no `Paper node`.

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
no conflict payoffs, so `t` and `d` are parameters and the SPI claims carry `d ≤ t` (weak)
or `d < t` (strict).  A program (`RnProg`) is a base strategy, or a renegotiation program
built on a base strategy *and a renegotiation logic of its own* (`Logic`: from the
projected outcome, a proposed joint action or nothing); the execution `run` is the
pseudocode, with the two proposals formed by the two programs' own logics and compared.
B.4's logic is `takeoverLogic`; a second logic, `concedeLogic`, is carried only to show that
the agreement test has content: against it the proposals differ and both programs fall
back to their base strategies (`run_rn_mismatch`).  This is DiGiovanni et al.'s
conditional-commitment setting, not the paper's instruction language `Prog`: it is given
as its own `ProgramGame` (`rnProgramGame`), which is what makes the execution-level
`ParticipationIndependent` and `ForeknowledgeIndependent` of `Independence.lean` apply to
it verbatim.

The representatives `rnRepresentatives` supply only the baseline `Π(negotiation t d) = 𝐛₀`
and play an arbitrary admissible profile on every other game.  Nothing here claims
Assumptions 1 or 2 for them, and none of the paper's theorems is applied to them.  (The
negotiation game itself has *no* strictly dominated action — `negotiation_reduced`: against
a counterpart demanding 80% with a device every action pays `d` — so Assumption 1 is not
what stands between these representatives and the paper's results; the arbitrary play on
the other games is.)

**What is proved.**

* Demand preservation of `rn` at both levels: the source's line 3 vs line 10 is
  `run_rn_fst` — a property of B.4's logic, which proposes a joint action keeping both
  demands (`takeoverLogic_demandPreserving`), and false for `concedeLogic`
  (`run_rn_concede_fst_ne`) — and B.2's `DemandPreserving` for the transformation
  `𝐟 = rn` (`rnStrategy_demandPreserving`).
* The B.4 numbers: `𝐩ᶠᵃⁱʳ` vs `𝐩ʰᵃʷᵏ` is the doomsday, `rn(𝐩ᶠᵃⁱʳ)` vs `rn(𝐩ʰᵃʷᵏ)` the
  takeover without devices (`outcome_fair_hawk`, `outcome_rn_fair_hawk`); `rn` is an SPI in
  B.1's sense on the space of all base-strategy profiles (`rn_isSPITransformation`, `d ≤ t`),
  strictly so on the B.4 profile (`programPayoff_fair_hawk_lt`, `d < t`).
* Participation independence of the renegotiation profile at both levels, and their
  relation on this example: under any simultaneous choice model consistent with the input
  programs, `(rn, 𝐩)` is participation-independent in B.2's sense (immediate from demand
  preservation, as B.2 says) *and* every `rn(𝐩ᵢ)` is participation independent in the
  execution-level sense against the baseline `𝐩` (`rnStrategy_participationIndependent_both`).
  The execution-level clause holds for every baseline and every logic
  (`rn_participationIndependent`).
* Foreknowledge independence of the policy that submits `rn(𝐛)` uninformed and `𝐛` itself
  when told the counterpart will not participate (`rnFallbackPolicy_foreknowledgeIndependent`).
* **B.2's "PI but not FI" agent**, with the source's numbers: an agent who demands 60%
  whether or not the counterpart participates, but would have demanded 50% had she known
  the counterpart would not.  She is participation independent and not foreknowledge
  independent at both levels (`sixtyFifty_participationIndependent`,
  `sixtyFifty_not_foreknowledgeIndependent`, and the execution-level pair
  `rn_sixty_participationIndependent`, `sixtyFiftyPolicy_not_foreknowledgeIndependent`).

Not rendered: B.3 (surrogate goals and concession equivalence), and any bridge between
B.1's `IsSPITransformation` and the paper's `Play.IsSPI` — the two quantify over different
objects (program profiles versus subset games under a play family).
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

/-- What the negotiation ends in, with the demands that were on the table. -/
inductive Outcome
  | split (a b : Share)
  | takeover (a b : Share)
  | doomsday (a b : Share)
  deriving DecidableEq

/-- `Simulate`: the outcome of two base strategies against each other.  Compatible demands
are split; incompatible ones end in a takeover attempt, with a doomsday if either side
brought a device. -/
def outcome (a b : Base) : Outcome :=
  if a.1.compatible b.1 then .split a.1 b.1
  else if a.2 = .doomsday ∨ b.2 = .doomsday then .doomsday a.1 b.1 else .takeover a.1 b.1

/-- The payoff of an outcome: the shares when split, `t` to both for a takeover attempt
without devices, `d` to both for a doomsday. -/
noncomputable def Outcome.payoff (t d : ℝ) : Outcome → Two → ℝ
  | .split a _, .one => a.toReal
  | .split _ b, .two => b.toReal
  | .takeover _ _, _ => t
  | .doomsday _ _, _ => d

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

lemma outcome_fair_hawk : outcome fair hawk = .doomsday .s50 .s80 := rfl

/-- **No action of the negotiation game is strictly dominated**, whatever `t` and `d`:
against a counterpart demanding 80% with a device every action pays `d`, so no action beats
another everywhere.  Assumption 1's elimination clause is therefore empty on this game. -/
lemma negotiation_reduced (t d : ℝ) : (negotiation t d).Reduced := by
  intro i a hdom
  obtain ⟨c, hd2⟩ := hdom
  obtain ⟨-, -, hlt⟩ := (Game.strictlyDominates_iff (negotiation t d) i c a).1 hd2
  have := hlt (pair hawk hawk) (fun j => Finset.mem_univ _)
  revert this
  cases i <;> simp [negotiation, hawk, outcome, Share.compatible, Outcome.payoff, pair]

/-! ### The renegotiation programs and their execution -/

/-- A **renegotiation logic**: from the projected outcome, a proposed joint action
`(mine, theirs)`, or no proposal. -/
abbrev Logic := Outcome → Option (Base × Base)

/-- The program space: a base strategy, or the renegotiation program built on a base
strategy and a renegotiation logic. -/
inductive RnProg
  | base (b : Base)
  | rn (b : Base) (logic : Logic)

/-- `my_base_strategy` of either kind of program. -/
def RnProg.baseOf : RnProg → Base
  | .base b => b
  | .rn b _ => b

/-- `is_renegotiation_type`. -/
def RnProg.isRn : RnProg → Bool
  | .base _ => false
  | .rn _ _ => true

/-- The demands made by a program: those of its base strategy (`d(rn(𝐩ᵢ)) = d(𝐩ᵢ)`). -/
def RnProg.demand (q : RnProg) : Share := q.baseOf.1

/-- The renegotiation logic of both agents in B.4: on a conflict, propose "attempt takeover,
without any doomsday devices" — the same demands, both devices disarmed; on a split,
nothing. -/
def takeoverLogic : Logic
  | .split _ _ => none
  | .takeover a b => some ((a, .none), (b, .none))
  | .doomsday a b => some ((a, .none), (b, .none))

/-- A different logic, for contrast: on a conflict, propose the even split. -/
def concedeLogic : Logic
  | .split _ _ => none
  | .takeover _ _ => some ((.s50, .none), (.s50, .none))
  | .doomsday _ _ => some ((.s50, .none), (.s50, .none))

/-- **The pseudocode**, from the running player's side.  Line 2: a base program, or a
renegotiation program facing a non-renegotiation type, acts by its base strategy (line
10).  Lines 3–8 for two renegotiation programs: simulate the base strategies (line 3), form
my proposal with my logic and theirs with their logic from the projected outcome (lines
4–5), and if they match act on my component of the proposal (lines 7–8); otherwise line
10. -/
def run (mine theirs : RnProg) : Base :=
  match mine, theirs with
  | .base b, _ => b
  | .rn b _, .base _ => b
  | .rn b L, .rn b' L' =>
    match L (outcome b b'), L' (outcome b b') with
    | some p, some q => if p = q then p.1 else b
    | _, _ => b

lemma run_base (b : Base) (q : RnProg) : run (.base b) q = b := rfl

lemma run_rn_base (b b' : Base) (L : Logic) : run (.rn b L) (.base b') = b := rfl

/-- The demand on the table for the running player, read off the projected outcome. -/
def Outcome.myDemand : Outcome → Share
  | .split a _ => a
  | .takeover a _ => a
  | .doomsday a _ => a

lemma outcome_myDemand (a b : Base) : (outcome a b).myDemand = a.1 := by
  unfold outcome; split_ifs <;> rfl

/-- A logic **preserves demands** when every proposal it makes keeps the running player's
demand as it was on the table. -/
def Logic.DemandPreserving (L : Logic) : Prop :=
  ∀ o p, L o = some p → p.1.1 = o.myDemand

lemma takeoverLogic_demandPreserving : takeoverLogic.DemandPreserving := by
  rintro (a | a | a) p h
  · cases h
  · cases h; rfl
  · cases h; rfl

/-- **Line 3 against line 10**: a renegotiation program with a demand-preserving logic makes
its base strategy's demand whatever the opponent's program is. -/
lemma run_rn_fst (b : Base) {L : Logic} (hL : L.DemandPreserving) (q : RnProg) :
    (run (.rn b L) q).1 = b.1 := by
  rcases q with b' | ⟨b', L'⟩
  · rfl
  · show (match L (outcome b b'), L' (outcome b b') with
      | some p, some q => if p = q then p.1 else b
      | _, _ => b).1 = b.1
    rcases h : L (outcome b b') with _ | p
    · rcases L' (outcome b b') <;> rfl
    · rcases L' (outcome b b') with _ | q
      · rfl
      · dsimp only
        split_ifs
        · rw [hL _ _ h, outcome_myDemand]
        · rfl

/-- The renegotiated actions of B.4: `50%` and `80%`, devices off. -/
lemma run_rn_fair_hawk : run (.rn fair takeoverLogic) (.rn hawk takeoverLogic) = (.s50, .none) := rfl
lemma run_rn_hawk_fair : run (.rn hawk takeoverLogic) (.rn fair takeoverLogic) = (.s80, .none) := rfl

/-- **B.4's Pareto improvement**: against each other the renegotiation programs reach the
takeover without devices, not the doomsday. -/
lemma outcome_rn_fair_hawk :
    outcome (run (.rn fair takeoverLogic) (.rn hawk takeoverLogic))
      (run (.rn hawk takeoverLogic) (.rn fair takeoverLogic)) = .takeover .s50 .s80 := rfl

/-- **The agreement test has content**: facing a renegotiation program whose logic proposes
the even split, `rn(𝐩ᶠᵃⁱʳ)`'s proposal does not match, and both fall back to their base
strategies — the doomsday again. -/
lemma run_rn_mismatch :
    run (.rn fair takeoverLogic) (.rn hawk concedeLogic) = fair ∧
      run (.rn hawk concedeLogic) (.rn fair takeoverLogic) = hawk := ⟨rfl, rfl⟩

/-- The conceding logic does **not** preserve demands: against `rn(𝐩ᶠᵃⁱʳ)`'s counterpart
using it too, a hawk's realized demand drops to 50%. -/
lemma run_rn_concede_fst_ne :
    (run (.rn hawk concedeLogic) (.rn fair concedeLogic)).1 ≠ hawk.1 := by decide

/-- The realized action profile of a program profile: each player runs her own program
against the other's. -/
def realized (c : Two → RnProg) : ∀ i, NUniverse i := fun i => run (c i) (c i.other)

/-- Program-level payoff: the negotiation game's payoff of the realized profile. -/
noncomputable def programPayoff (t d : ℝ) (c : Two → RnProg) (i : Two) : ℝ :=
  (negotiation t d).u (realized c) i

/-- The transformation `𝐟 = rn`: every agent's program becomes B.4's renegotiation program
on the same base strategy. -/
def rnTransform (c : Two → RnProg) : Two → RnProg := fun i => .rn (c i).baseOf takeoverLogic

/-- The full strategy `(rn, 𝐩)`. -/
def rnStrategy (p : Two → RnProg) : FullStrategy (fun _ : Two => RnProg) :=
  ⟨rnTransform, p⟩

/-- The demand function, per agent. -/
def demands : ∀ _ : Two, RnProg → Share := fun _ => RnProg.demand

/-- **Demand preservation** of `rn`, as B.2 defines it, for every input profile. -/
lemma rnStrategy_demandPreserving (p : Two → RnProg) :
    (rnStrategy p).DemandPreserving demands := fun _ => rfl

/-- More than the demand: `rn` preserves the whole base strategy, device included — B.2's
`d(rn(𝐩ᵢ)) = d(𝐩ᵢ) = my_base_strategy` read with the base strategy as the demand. -/
lemma rnStrategy_basePreserving (p : Two → RnProg) (i : Two) :
    ((rnStrategy p).used i).baseOf = (p i).baseOf := rfl

/-- The space of base-strategy profiles: B.4's "before they consider the possibility of
SPIs". -/
def baseProfiles : Set (Two → RnProg) := {p | ∀ i, (p i).isRn = false}

lemma realized_of_base {p : Two → RnProg} (hp : p ∈ baseProfiles) (i : Two) :
    realized p i = (p i).baseOf := by
  have := hp i
  cases h : p i with
  | base b => simp [realized, h, run_base, RnProg.baseOf]
  | rn b L => rw [h] at this; cases this

/-- **`rn` is an SPI in B.1's sense** on the space of base-strategy profiles, as soon as a
takeover attempt without devices is no worse than a doomsday for either player (`d ≤ t`).
Compatible demands are split exactly as before; incompatible ones now end in the takeover
without devices, whatever devices the base strategies carried. -/
lemma rn_isSPITransformation {t d : ℝ} (hd : d ≤ t) :
    IsSPITransformation (programPayoff t d) baseProfiles rnTransform := by
  intro p hp i
  have h1 := realized_of_base hp .one
  have h2 := realized_of_base hp .two
  simp only [programPayoff, negotiation]
  rw [h1, h2]
  rcases hp1 : (p .one).baseOf with ⟨a, x⟩
  rcases hp2 : (p .two).baseOf with ⟨a', x'⟩
  simp only [realized, rnTransform, other_one, other_two, hp1, hp2]
  cases i <;> cases a <;> cases a' <;> cases x <;> cases x' <;>
    simp [run, outcome, Outcome.payoff, Share.compatible, takeoverLogic, hd]

/-- **Strictly so on the B.4 profile**: both players gain when a doomsday is strictly worse
than a takeover attempt (`d < t`). -/
lemma programPayoff_fair_hawk_lt {t d : ℝ} (h : d < t) (i : Two) :
    programPayoff t d (pair (.base fair) (.base hawk)) i <
      programPayoff t d (rnTransform (pair (.base fair) (.base hawk))) i := by
  cases i <;> simp [programPayoff, negotiation, realized, rnTransform, pair, run, outcome, fair,
    hawk, Share.compatible, Outcome.payoff, takeoverLogic, RnProg.baseOf, h]

/-! ### The program game and the execution-level notions -/

open Classical in
/-- Representatives supplying the baseline `Π(negotiation t d) = 𝐛₀` — the one-point sample
space, and an arbitrary admissible profile on every other game.  Nothing here claims
Assumption 1 or 2 (see the file header). -/
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
  exec c _ i := (negotiation t d).pureMixed (realized c i) (Finset.mem_univ _)
  measurable_exec _ _ _ := measurable_from_top

lemma rnProgramGame_exec (t d : ℝ) (b₀ : Two → Base) (c : Two → RnProg) (ω : Unit) (i : Two) :
    (rnProgramGame t d b₀).exec c ω i =
      (negotiation t d).pureMixed (realized c i) (Finset.mem_univ _) := rfl

/-- The **default instruction** is the base strategy `𝐛₀ i` itself: everybody at their base
strategy realizes `𝐛₀ = Π(Γ₀)`. -/
noncomputable def rnDefault (t d : ℝ) (b₀ : Two → Base) : (rnProgramGame t d b₀).DefaultInstr where
  default i := .base (b₀ i)
  plays_default ω i b := by
    simp only [rnProgramGame_exec, Game.pureMixed_val, rnRepresentatives_play]
    rfl

/-- Against a counterpart at her default, a renegotiation program realizes its base
strategy, i.e. exactly what the all-default profile realizes. -/
lemma realized_update_rn (b₀ : Two → Base) (c : Two → RnProg) (i : Two) {L : Logic}
    (hc : c i = .rn (b₀ i) L) (j : Two) (hj : j ≠ i) :
    realized (Function.update c j (.base (b₀ j))) i = realized (fun k => .base (b₀ k)) i := by
  have hji : j = i.other := eq_other_of_ne hj
  subst hji
  simp only [realized, Function.update_self, Function.update_of_ne (other_ne i).symm, hc,
    run_rn_base, run_base]

/-- **Execution-level participation independence** of a renegotiation program, for every
baseline and every logic: when the counterpart does not participate, the program realizes
its base strategy, which is what the baseline realizes. -/
lemma rn_participationIndependent (t d : ℝ) (b₀ : Two → Base) (c : Two → RnProg) (i : Two)
    {L : Logic} (hc : c i = .rn (b₀ i) L) :
    (rnProgramGame t d b₀).ParticipationIndependent (rnDefault t d b₀) c i := by
  intro j hj ω
  rw [rnProgramGame_exec, rnProgramGame_exec]
  congr 1
  exact realized_update_rn b₀ c i hc j hj

/-- **B.2's participation independence** of the renegotiation full strategy, for any input
profile, under any simultaneous choice model consistent with it. -/
lemma rnStrategy_participationIndependent (p : Two → RnProg)
    (χ : ChoiceModel (fun _ : Two => RnProg)) (hsim : χ.Simultaneous)
    (hcons : (rnStrategy p).Consistent χ) :
    (rnStrategy p).ParticipationIndependent demands χ :=
  (rnStrategy p).participationIndependent_of_simultaneous demands χ hsim hcons.chosenGivenUse
    (rnStrategy_demandPreserving p)

/-- **The two levels together, on this example.**  Under a simultaneous choice model
consistent with the input programs `𝐩`, the full strategy `(rn, 𝐩)` is
participation-independent in B.2's sense, and each transformed program `rn(𝐩ᵢ)` is
participation independent in the execution-level sense against the baseline in which
everybody plays her input base strategy.  The first clause is immediate from demand
preservation (as B.2 says); the second is a computation through `run`. -/
lemma rnStrategy_participationIndependent_both (t d : ℝ) (p : Two → RnProg)
    (χ : ChoiceModel (fun _ : Two => RnProg)) (hsim : χ.Simultaneous)
    (hcons : (rnStrategy p).Consistent χ) :
    (rnStrategy p).ParticipationIndependent demands χ ∧
      ∀ i, (rnProgramGame t d fun k => (p k).baseOf).ParticipationIndependent
        (rnDefault t d fun k => (p k).baseOf) (rnStrategy p).used i :=
  ⟨rnStrategy_participationIndependent p χ hsim hcons,
    fun i => rn_participationIndependent t d _ _ i rfl⟩

/-- The B.4 profile: `A` submits `rn(𝐩ᶠᵃⁱʳ)`, `B` submits `rn(𝐩ʰᵃʷᵏ)`. -/
def fairHawkRn : Two → RnProg := pair (.rn fair takeoverLogic) (.rn hawk takeoverLogic)

/-- The B.4 baseline. -/
def fairHawk : Two → Base := pair fair hawk

/-- Both B.4 renegotiation programs are participation independent against the B.4
baseline. -/
lemma fairHawkRn_participationIndependent (t d : ℝ) (i : Two) :
    (rnProgramGame t d fairHawk).ParticipationIndependent (rnDefault t d fairHawk) fairHawkRn i :=
  rn_participationIndependent t d fairHawk fairHawkRn i (L := takeoverLogic) (by cases i <;> rfl)

/-- The B.4 profile executes as the renegotiated outcome: `(50%, no device)`,
`(80%, no device)`. -/
lemma fairHawkRn_plays (t d : ℝ) :
    (rnProgramGame t d fairHawk).Plays fairHawkRn fun _ => pair (.s50, .none) (.s80, .none) := by
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
    | false => .rn b takeoverLogic
    | true => .base b

/-- **Execution-level foreknowledge independence** of the fall-back policy: once the
counterpart has dropped out, `rn(𝐛)` and `𝐛` realize the same action.  The two instructions
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
  simp only [realized, Function.update_self, Function.update_of_ne (other_ne i),
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
    | .one, q => if (q .two (by decide)).isRn then .base (.s60, .none) else .base (.s50, .none)
    | .two, _ => .base bB

/-- Her full strategy: `rn` applied to the input profile `(60%, bB)`. -/
def sixtyFiftyStrategy (bB : Base) : FullStrategy (fun _ : Two => RnProg) :=
  rnStrategy (pair (.base (.s60, .none)) (.base bB))

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
    (rnProgramGame t d (pair (.s60, .none) bB)).Policy .one where
  Signal := Bool
  noInfo := false
  willNotParticipate _ := true
  policy
    | false => .rn (.s60, .none) takeoverLogic
    | true => .base (.s50, .none)

/-- **Execution-level participation independence** of her uninformed program `rn(60%)`. -/
lemma rn_sixty_participationIndependent (t d : ℝ) (bB : Base) (c : Two → RnProg)
    (hc : c .one = .rn (.s60, .none) takeoverLogic) :
    (rnProgramGame t d (pair (.s60, .none) bB)).ParticipationIndependent
      (rnDefault t d (pair (.s60, .none) bB)) c .one :=
  rn_participationIndependent t d _ c .one hc

/-- **Execution-level failure of foreknowledge independence**: once `B` has dropped out
she demands 60% if she chose uninformed and 50% if she chose knowing — different realized
actions, whatever `B`'s base strategy. -/
lemma sixtyFiftyPolicy_not_foreknowledgeIndependent (t d : ℝ) (bB : Base) (c : Two → RnProg) :
    ¬ (rnProgramGame t d (pair (.s60, .none) bB)).ForeknowledgeIndependent
      (rnDefault t d (pair (.s60, .none) bB)) c (sixtyFiftyPolicy t d bB) := by
  intro h
  have := congrArg (fun m => m.val ⟨(.s60, .none), Finset.mem_univ _⟩) (h .two (by decide) ())
  simp only [rnProgramGame_exec, Game.pureMixed_val, realized, Function.update_self,
    Function.update_of_ne (show Two.two ≠ Two.one by decide), other_one, sixtyFiftyPolicy,
    rnDefault, run_rn_base, run_base] at this
  simp at this

end Renegotiation

end Examples

end SafeParetoImprovements
