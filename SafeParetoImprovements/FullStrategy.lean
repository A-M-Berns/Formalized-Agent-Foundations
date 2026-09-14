import SafeParetoImprovements.Game

/-!
# Full strategies: demand preservation, participation independence, foreknowledge
independence at the level of program choice (substrate beyond the paper)

Source: Anthony DiGiovanni, *CLR's Safe Pareto Improvements Research Agenda* (LessWrong,
20 April 2026), Appendix B.1–B.2.  The 2022 paper has no counterpart for any of this; it
is research-facing substrate (the scoping ruling recorded in `notes/scoping.md` §8),
carries no `Paper node`, and the source itself labels B.2 "working formalizations … we're
not highly confident that we'll endorse these formalizations/terminology after more
thought".  What is rendered is the text as printed,
at its own level of abstraction — programs, a transformation of program profiles, and two
counterfactual program choices — so that the notions can be compared with the
execution-level ones of `Independence.lean`, which are stated over the paper's program
games instead.

**B.1.**  The agents play a game through *programs* `𝐩`, one per agent, that collectively
determine their actions; `u 𝐩 i` is agent `i`'s payoff when they all follow `𝐩`.  An
**SPI** is a transformation `𝐟` of program profiles such that, for all `𝐩` in some space
`𝐏`, the payoffs under `𝐟(𝐩)` weakly Pareto-dominate those under `𝐩`
(`IsSPITransformation`).

**B.2.**  A **full strategy** is a pair `(𝐟, 𝐩)`: a transformation — an SPI, in the
source's intended use — together with the programs the agents in fact apply it to
(`FullStrategy`).  The structure carries no SPI condition of its own; the SPI property is
`IsSPITransformation`, stated and proved separately, so that the three properties below
can be discussed for any transformation.  Write `d(𝐪ᵢ)` for the demands made by a program.
Two counterfactuals are the primitives of the definitions:

* `𝐩ᴾᵢ(𝐟)`, the program `i` would have chosen had each other agent `j` *used* `𝐩ⱼ` rather
  than `𝐟(𝐩)ⱼ`;
* `𝐩ᶠᵢ(𝐟)`, the program `i` would have chosen had `i` *believed* each other agent `j`
  would use `𝐩ⱼ` rather than `𝐟(𝐩)ⱼ`.

The source leaves "would have chosen" informal.  Here it is data: a **choice model**
(`ChoiceModel`) records, for each agent `i`, the input program she chooses as a function of
the programs the *other* agents `j ≠ i` actually use, and as a function of the programs she
believes they use (beliefs are point beliefs — the others' profile — which is all the
source's counterfactual needs).  The agent's own coordinate is what is being chosen, so it
is not an input.  The full strategy is **consistent** with the model when `𝐩ᵢ` is what the
model chooses in the actual situation, where the others use `𝐟(𝐩)ⱼ` (`Consistent`).  Then

* `(𝐟, 𝐩)` is **demand-preserving** if `d(𝐟(𝐩)ᵢ) = d(𝐩ᵢ)` for each `i`;
* **participation-independent** if demand-preserving and `𝐩ᵢ = 𝐩ᴾᵢ(𝐟)` for each `i`;
* **foreknowledge-independent** if demand-preserving and `𝐩ᵢ = 𝐩ᶠᵢ(𝐟)` for each `i`.

B.2's own example is rendered as `participationIndependent_of_simultaneous`: when agents
choose programs independently of each other — nobody's choice depends on what the others
actually use — the clause `𝐩ᵢ = 𝐩ᴾᵢ(𝐟)` is immediate, so participation independence
reduces to demand preservation.  Foreknowledge independence does not reduce the same way:
`not_foreknowledgeIndependent_of_demand_ne` is the shape of B.2's "PI but not FI" agent,
who demands the same whatever the counterpart does but would have demanded less had she
known.  The worked instance with the source's numbers is `Examples/Renegotiation.lean`,
which also exhibits the execution-level notions of `Independence.lean` on the same
example; no general bridge between the two levels is claimed, and Appendix B.3 (surrogate
goals, concession equivalence) is not rendered.
-/

universe u v w

namespace SafeParetoImprovements

variable {N : Type u} {P : N → Type v} {D : N → Type w}

/-- **B.1's SPI**: the transformation `f` of program profiles weakly Pareto-improves the
payoff `u` on every profile of the program space `𝐏`. -/
def IsSPITransformation (u : (∀ i, P i) → N → ℝ) (space : Set (∀ i, P i))
    (f : (∀ i, P i) → ∀ i, P i) : Prop :=
  ∀ p ∈ space, ∀ i, u p i ≤ u (f p) i

/-- **A full strategy** `(𝐟, 𝐩)`: a transformation of program profiles and the input
programs the agents in fact apply it to. -/
structure FullStrategy (P : N → Type v) where
  /-- The transformation `𝐟`. -/
  transform : (∀ i, P i) → ∀ i, P i
  /-- The input programs `𝐩`. -/
  progs : ∀ i, P i

/-- The programs of everybody but `i`, read off a profile. -/
def others (p : ∀ j, P j) (i : N) : ∀ j, j ≠ i → P j := fun j _ => p j

/-- **A choice model**: the two counterfactual program choices of B.2, as functions of the
programs the *other* agents use, resp. the ones the agent believes they use. -/
structure ChoiceModel (P : N → Type v) where
  /-- `i`'s chosen input program when the others *use* the given programs. -/
  ofParticipation : ∀ i, (∀ j, j ≠ i → P j) → P i
  /-- `i`'s chosen input program when she *believes* the others use the given programs. -/
  ofBelief : ∀ i, (∀ j, j ≠ i → P j) → P i

namespace ChoiceModel

variable (χ : ChoiceModel P)

/-- **Simultaneous commitment**: nobody's choice depends on the programs the others
actually use — B.2's "agents choose programs independently of each other". -/
def Simultaneous : Prop := ∀ i q q', χ.ofParticipation i q = χ.ofParticipation i q'

end ChoiceModel

namespace FullStrategy

variable (d : ∀ i, P i → D i) (s : FullStrategy P) (χ : ChoiceModel P)

/-- The programs actually used, `𝐟(𝐩)`. -/
def used : ∀ i, P i := s.transform s.progs

/-- The full strategy's transformation is an SPI on `space` for the payoff `u` (B.2's
standing hypothesis "if `𝐟` is an SPI"). -/
def IsSPI (u : (∀ i, P i) → N → ℝ) (space : Set (∀ i, P i)) : Prop :=
  IsSPITransformation u space s.transform

/-- `𝐩ᴾᵢ(𝐟)`: what `i` would have chosen had the others used `𝐩ⱼ`. -/
def counterfactualP (i : N) : P i := χ.ofParticipation i (others s.progs i)

/-- `𝐩ᶠᵢ(𝐟)`: what `i` would have chosen had she believed the others would use `𝐩ⱼ`. -/
def counterfactualF (i : N) : P i := χ.ofBelief i (others s.progs i)

/-- The full strategy is what the choice model produces in the actual situation, where the
others use (and are believed to use) `𝐟(𝐩)ⱼ`. -/
def Consistent : Prop :=
  ∀ i, χ.ofParticipation i (others s.used i) = s.progs i ∧
    χ.ofBelief i (others s.used i) = s.progs i

/-- **Demand-preserving**: `d(𝐟(𝐩)ᵢ) = d(𝐩ᵢ)` for each agent. -/
def DemandPreserving : Prop := ∀ i, d i (s.used i) = d i (s.progs i)

/-- **Participation-independent**: demand-preserving, and `𝐩ᵢ = 𝐩ᴾᵢ(𝐟)` for each agent. -/
def ParticipationIndependent : Prop :=
  s.DemandPreserving d ∧ ∀ i, s.progs i = s.counterfactualP χ i

/-- **Foreknowledge-independent**: demand-preserving, and `𝐩ᵢ = 𝐩ᶠᵢ(𝐟)` for each agent. -/
def ForeknowledgeIndependent : Prop :=
  s.DemandPreserving d ∧ ∀ i, s.progs i = s.counterfactualF χ i

/-- **B.2's example, in general form**: under simultaneous commitment, a consistent,
demand-preserving full strategy is participation-independent — the program clause is
immediate because `i`'s choice does not depend on what the others use. -/
lemma participationIndependent_of_simultaneous (hsim : χ.Simultaneous)
    (hcons : s.Consistent χ) (hd : s.DemandPreserving d) :
    s.ParticipationIndependent d χ :=
  ⟨hd, fun i => ((hcons i).1.symm.trans (hsim i _ _))⟩

/-- An agent who would have made a *different demand* had she known the others would not
participate breaks foreknowledge independence, whatever the transformation does. -/
lemma not_foreknowledgeIndependent_of_demand_ne {i : N}
    (h : d i (s.counterfactualF χ i) ≠ d i (s.progs i)) :
    ¬ s.ForeknowledgeIndependent d χ :=
  fun hfi => h (congrArg (d i) (hfi.2 i)).symm

/-- Program-level foreknowledge independence pins the counterfactual demand to the actual
one.  The source's clause `𝐩ᵢ = 𝐩ᶠᵢ(𝐟)` is an equality of *programs*, strictly stronger
than this demand equality (distinct programs can share a demand); this is the consequence
of it that the demand-level examples use. -/
lemma ForeknowledgeIndependent.demand_counterfactualF (h : s.ForeknowledgeIndependent d χ)
    (i : N) : d i (s.counterfactualF χ i) = d i (s.progs i) :=
  (congrArg (d i) (h.2 i)).symm

end FullStrategy

end SafeParetoImprovements
