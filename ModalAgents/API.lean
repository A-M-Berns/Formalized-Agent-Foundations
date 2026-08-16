import ModalAgents.Behavioral
import ModalAgents.ArithmeticAgent

/-!
# Modal Agents consumer API

The supported downstream import for modal-agent and open-source-game research is:

```lean
import ModalAgents.API
```

## The modal layer (§2–§3)

Its main vocabulary is `ModalAgent`, `Modalized`, `outcome`, `Cooperates`, `Defects`,
`ProvablyDefects`, behavioral equivalence `BehavEquiv` (notation `≈` after
`open scoped ModalAgent`), the four concrete bots, the fixed-point interface, the
cooperation theorems, and the arithmetic lifts.

The recursive `F_of`/substitution development and most of `GlFixedPointBridge` are proof
infrastructure, not a recommended dependency surface.  `GlFixedPointBridge.toSeq` remains
a supported interoperability boundary because it occurs in the arithmetic-lift results;
the vendored provability-logic implementation behind it is not thereby designated as
ModalAgents API.

`Defects X Y` means that GL does not prove cooperation.  It is strictly weaker than
`ProvablyDefects X Y`, which positively proves the negated outcome and is the form that
has an arithmetic lift.  The three irreducibly weak defection results and their
`□⊥`/`□□⊥` obstructions remain exactly as disclosed in `ModalAgents/README.md`.

## The arithmetic layer (§1, §4)

The paper's §4 definitions quantify over *arbitrary* agents — formulas of `PA`, not the
`GL`-level `ModalAgent` structure — so they are carried by a second layer, also supported:

* `Agent` (a `PA` formula with at most one free variable) and `Agent.app`, the paper's
  `[X(Y)]`, substituting the Gödel number of `Y`;
* `IsModalAgentOfRank` / `IsModalAgent`, `BehaviorallyEquivalent`, `IsBehavioral`;
* `modalAgent_isBehavioral` — modal agents are behavioral (Theorem 4.8);
* `cliqueBot` and `cliqueBot_not_modalAgent` — the CliqueBot separation (Corollary 4.9);
* from `ModalAgents.Arithmetic`: `lob_theorem` (Theorem 1.1),
  `arithmetic_modal_substitution` (Lemma 4.5) and `arithmetic_fixedPoint_uniqueness`
  (Corollary 4.4), with `arithInterp` and `Realization.update` as their statement surface.

Two assumptions a client must supply, both stated rather than hidden:

* the layer is parametric in the theory — results take `{T : ArithmeticTheory}` with
  `[T.Δ₁]` and `[𝗣𝗔 ⪯ T]`, where the paper fixes `PA`;
* `cliqueBot_not_isBehavioral` and `cliqueBot_not_modalAgent` additionally take
  `[Entailment.Consistent T]`.  The paper's argument uses it implicitly: over an
  inconsistent `T` every agent is vacuously behavioral and the separation fails.

`IsModalAgent` is inhabited — `cooperateBot_isModalAgentOfRank_zero` — so Theorem 4.8 is
not a statement about an empty class.

**A performance boundary worth knowing before writing a tactic call.** `cliqueBot` is a
`parameterizedFixedpoint`, so its Gödel numeral is astronomically large.  Any tactic that
lets the kernel unfold it — `cl_prover` on a goal mentioning it, or computing its
`complexity` to a numeral — costs more than 8 GB and does not return.  Prove the step
generically over an abstract `ClosedTerm ℒₒᵣ` or `ArithmeticSentence` and instantiate
afterwards; `cliqueBotSpec_subst` and `cliqueBotVariant_ne` are the worked examples.

One numbered node of the paper has no Lean statement here: Theorem 4.6, on
self-referential modal agents.  See `ModalAgents/README.md`.
-/
