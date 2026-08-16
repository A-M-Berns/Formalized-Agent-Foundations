/-
  Agents as formulas of arithmetic (Barasz, §4).

  `ModalAgents/ModalAgent.lean` models modal agents at the `GL` level, which is where
  the cooperation theorems live. The paper's §4 definitions are *arithmetic*: an agent
  is a formula of `PA` with one free variable, and `[X(Y)]` substitutes the Gödel number
  of `Y`. This file builds that layer, so that the nodes which quantify over arbitrary
  agents — not just modal ones — can be stated as printed.

  Main results:
  - `modalAgent_isBehavioral` : modal agents are behavioral (§4, Thm 4.8)
  - `cliqueBot_not_modalAgent` : CliqueBot is not a modal agent (§4, Cor 4.9)
-/

import ModalAgents.Arithmetic

open LO LO.Modal
open LO.Entailment LO.Modal.Entailment
open LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.ProvabilityAbstraction

/-! ## Agents -/

/-- An **agent** (Barasz, §4): a well-formed formula in the language of `PA` with at most
one free variable. -/
abbrev Agent := ArithmeticSemisentence 1

/-- `[X(Y)]`: the agent `X` applied to the Gödel number of the agent `Y`. The paper reads
this sentence as "`X` cooperates with `Y`". -/
noncomputable def Agent.app (X Y : Agent) : ArithmeticSentence := X/[⌜Y⌝]

section

variable {T : ArithmeticTheory} [T.Δ₁] [𝗣𝗔 ⪯ T]

local instance : (𝗜𝚺₁ : ArithmeticTheory) ⪯ T :=
  Entailment.WeakerThan.trans (𝓣 := (𝗣𝗔 : ArithmeticTheory)) inferInstance inferInstance

local instance : (𝗣𝗔⁻ : ArithmeticTheory) ⪯ T :=
  Entailment.WeakerThan.trans (𝓣 := (𝗣𝗔 : ArithmeticTheory)) inferInstance inferInstance

/-- The realization the paper's modal-agent definition reads `φ` under: atom `0` is
"the opponent `Z` cooperates with me", and atom `i + 1` is "`Z` cooperates with my
`i`-th reference agent". Atoms beyond the reference list are irrelevant — the modal
formula does not mention them — and are sent to `⊥`. -/
noncomputable def opponentRealization (T : ArithmeticTheory) [T.Δ₁]
    (Z X : Agent) {n : ℕ} (W : Fin n → Agent) :
    _root_.Realization ℕ T.standardProvability :=
  ⟨fun a => match a with
    | 0 => Z.app X
    | j + 1 => if h : j < n then Z.app (W ⟨j, h⟩) else ⊥⟩

/-- **Modal agent of rank `k`** (Barasz, §4): an agent `X` is a modal agent of rank `k`
when there are modal agents `W₁,…,Wₙ` of rank `< k` and a fully modalized formula
`φ(p, q₁,…,qₙ)` with, for every agent `Z`,

`PA ⊢ [X(Z)] 🡘 φ([Z(X)], [Z(W₁)],…,[Z(Wₙ)])`.

Atom `0` of `φ` is the paper's `p` and atom `i + 1` is `qᵢ`, matching the `GL`-level
`ModalAgent` convention in `ModalAgents/ModalAgent.lean`. "Fully modalized" is
`Modalized i φ` for each relevant atom `i`: every occurrence of that atom is inside a
`□`. -/
inductive IsModalAgentOfRank (T : ArithmeticTheory) [T.Δ₁] : ℕ → Agent → Prop
  | intro {k n : ℕ} {X : Agent} (W : Fin n → Agent) (rank : Fin n → ℕ)
      (φ : Modal.Formula ℕ)
      (modalized : ∀ i, i ≤ n → Modalized i φ)
      (rank_lt : ∀ i, rank i < k)
      (refs : ∀ i, IsModalAgentOfRank T (rank i) (W i))
      (defn : ∀ Z : Agent,
        T ⊢ X.app Z 🡘 arithInterp (opponentRealization T Z X W) φ) :
      IsModalAgentOfRank T k X

/-- An agent is a **modal agent** when it has some rank. -/
def IsModalAgent (T : ArithmeticTheory) [T.Δ₁] (X : Agent) : Prop :=
  ∃ k, IsModalAgentOfRank T k X

/-! ## Behavioral agents (Barasz, §4) -/

/-- Two agents are **behaviorally equivalent** when `PA` proves they act alike against
every agent. -/
def BehaviorallyEquivalent (T : ArithmeticTheory) (X Y : Agent) : Prop :=
  ∀ Z : Agent, T ⊢ X.app Z 🡘 Y.app Z

/-- An agent is **behavioral** when its own action cannot distinguish behaviorally
equivalent opponents. -/
def IsBehavioral (T : ArithmeticTheory) (X : Agent) : Prop :=
  ∀ Y Z : Agent, BehaviorallyEquivalent T Y Z → T ⊢ X.app Y 🡘 X.app Z

/-- **Modal agents are behavioral**, in the paper's arithmetic form: an agent whose
action against every opponent is given by a fully modalized formula in the opponent's
behaviour cannot distinguish behaviorally equivalent opponents.

This is the paper's proof: expand `[X(Y)]` and `[X(Z)]` by the modal-agent equation and
observe that the two right-hand sides are interpretations of the *same* modal formula
under realizations that behavioral equivalence makes provably equivalent atom by atom,
so Lemma 4.5 (`arithmetic_modal_substitution`) identifies them.

The `GL`-level counterpart, restricted to the `ModalAgent` structure that drives the
cooperation theorems, is `modalAgent_behavioral` in `ModalAgents/Behavioral.lean`.

Paper node: Theorem 4.8 (§4). -/
theorem modalAgent_isBehavioral {k : ℕ} {X : Agent}
    (hX : IsModalAgentOfRank T k X) : IsBehavioral T X := by
  intro Y Z hYZ
  cases hX with
  | @intro _ n _ W rank φ _ _ _ hdef =>
    refine E!_trans (hdef Y) (E!_trans ?_ (E!_symm (hdef Z)))
    refine arithmetic_modal_substitution (fun a => ?_) φ
    match a with
    | 0 => exact hYZ _
    | j + 1 =>
      show T ⊢ (if h : j < n then Y.app (W ⟨j, h⟩) else ⊥) 🡘
        (if h : j < n then Z.app (W ⟨j, h⟩) else ⊥)
      by_cases h : j < n
      · simp only [dif_pos h]; exact hYZ _
      · simp only [dif_neg h]; cl_prover

/-! ## CliqueBot (Barasz, §2, Alg 3) and Corollary 4.9

CliqueBot cooperates exactly with agents whose source code is its own. The paper builds
it "by the diagonal lemma"; here that is Foundation's *parameterized* diagonal lemma
`parameterized_diagonal₁`, which produces a formula with a free variable that knows its
own Gödel number — the sentence-level `Diagonalization.fixedpoint` is not enough. -/

/-- Applying a quined agent: the parameterized fixed point of `θ`, run against `Z`, is
`θ` with its self-reference filled in by the fixed point's own code and its argument by
`Z`'s. -/
lemma param_fp_app (θ : ArithmeticSemisentence 2) (Z : Agent) :
    T ⊢ (Agent.app (parameterizedFixedpoint θ) Z) 🡘
      θ/[⌜parameterizedFixedpoint θ⌝, ⌜Z⌝] := by
  have h := parameterized_diagonal₁ (T := T) θ
  have h2 := Theory.Proof.specialize (T := T)
    (parameterizedFixedpoint θ 🡘 θ/[⌜parameterizedFixedpoint θ⌝, #0]) ⌜Z⌝
  have h3 := h2 ⨀ h
  simpa [Agent.app, Rew.subst_comp_subst, ← TransitiveRewriting.comp_app] using h3

/-- CliqueBot's defining specification, with `#0` its own code and `#1` the opponent's:
cooperate exactly when they agree. -/
noncomputable def cliqueBotSpec : ArithmeticSemisentence 2 := “self x. x = self”

/-- **CliqueBot** (Barasz, §2, Alg 3): the agent that cooperates with an opponent
exactly when the opponent's source code is its own, obtained by quining. -/
noncomputable def cliqueBot : Agent := parameterizedFixedpoint cliqueBotSpec

/-- Substituting into CliqueBot's specification, with both codes left abstract.

Stated for arbitrary closed terms on purpose: the substitution is a computation on the
*small* formula `cliqueBotSpec`, so proving it generically keeps `cliqueBot` — a
`parameterizedFixedpoint`, whose Gödel numeral is astronomically large — from ever being
unfolded.  Unfolding it here costs the kernel more than 8 GB. -/
lemma cliqueBotSpec_subst (s t : ClosedTerm ℒₒᵣ) :
    cliqueBotSpec/[s, t] = “!!t = !!s” := by
  simp [cliqueBotSpec]

/-- CliqueBot does what it says: `PA` proves it cooperates with `Z` exactly when `Z`'s
code is CliqueBot's own. -/
lemma cliqueBot_app (Z : Agent) :
    T ⊢ (cliqueBot.app Z) 🡘
      “!!(⌜Z⌝ : ClosedTerm ℒₒᵣ) = !!(⌜(cliqueBot : Agent)⌝)” := by
  have h := param_fp_app (T := T) cliqueBotSpec Z
  rwa [cliqueBotSpec_subst] at h

/-- A syntactically different CliqueBot: the same formula conjoined with `⊤`. It is a
different formula, hence has a different Gödel number, hence CliqueBot defects against
it — while being logically, and therefore behaviorally, equivalent to CliqueBot. -/
noncomputable def cliqueBotVariant : Agent := cliqueBot ⋏ ⊤

/-- CliqueBot's variant is a genuinely different formula.

Kept structural on purpose: `cliqueBot` is a `parameterizedFixedpoint`, so any proof
that computes its `complexity` to a numeral forces the kernel to whnf the entire quined
term and blows up.  `Semiformula.ne_of_ne_complexity` plus the *generic* congruence
`complexity (φ ⋏ ⊤) = max φ.complexity 0 + 1` settles it with `cliqueBot.complexity`
held abstract. -/
lemma cliqueBotVariant_ne : (cliqueBotVariant : Agent) ≠ cliqueBot := by
  refine Semiformula.ne_of_ne_complexity ?_
  show (cliqueBot ⋏ ⊤ : Agent).complexity ≠ (cliqueBot : Agent).complexity
  rw [Semiformula.complexity_and, Semiformula.complexity_top]
  generalize (cliqueBot : Agent).complexity = c
  omega

example (Z : Agent) : (cliqueBotVariant.app Z) = (cliqueBot.app Z ⋏ ⊤) := by
  simp [cliqueBotVariant, Agent.app]

example (a b : ℕ) (h : a ≠ b) : T ⊢ “!!(↑a : ClosedTerm ℒₒᵣ) ≠ !!(↑b)” :=
  Entailment.WeakerThan.pbl (𝓢 := (𝗥₀ : ArithmeticTheory)) (Entailment.by_axm (R0.Ω₃ a b h))

example (Z : Agent) : (⌜Z⌝ : ClosedTerm ℒₒᵣ) = ↑(Encodable.encode Z) :=
  Arithmetic.gödelNumber'_eq_coe_encode Z

end

