# Robust Cooperation in the Prisoner's Dilemma, formalized

A Lean 4 formalization of Barász, Christiano, Fallenstein, Herreshoff, LaVictoire,
Yudkowsky, [*Robust Cooperation in the Prisoner's Dilemma via Provability Logic*](https://arxiv.org/abs/1401.5577),
at the level of Gödel–Löb provability logic.


It covers:

* the modal agent definition from §4;
* CooperateBot, DefectBot, FairBot, and PrudentBot;
* the GL fixed-point construction used to define interaction outcomes;
* the cooperation results for FairBot and PrudentBot from §§2-3;
* the modal agent fixed-point equation (§4, Thm 4.7);
* the modal agent behavioral result (§4, Thm 4.8, GL-level form);
* the rank-0 FairBot-to-CooperateBot result (§4, Thm 4.10);
* the generic lift from GL-provability to arithmetical realizations (§4, Thm 4.1).

### Axioms

**None.** Every ModalAgents endpoint reports only `propext`, `Classical.choice`, and
`Quot.sound` (checked by `AxiomAudit.lean`).

The one standard GL fact previously axiomatized — `glFixedPoint_thm42`, the de
Jongh–Sambin–Bernardi modal fixed-point existence theorem (single-variable form; Barasz
§4, Thm 4.2, which they state without proof, citing Lindström (1996) Thm 11) — is now
**proved**. It is discharged through the upstream
[`FormalizedFormalLogic/ProvabilityLogic`](https://github.com/FormalizedFormalLogic/ProvabilityLogic)
package (pinned by commit in `lakefile.lean`): a de Jongh–Sambin construction via Maehara
interpolation and Löb's rule, transported to Foundation's `Modal.GL` through finite Kripke
completeness, with the `GlFixedPointBridge` translation in `FixedPoint.lean`. The same
package supplies the arithmetical soundness of GL (Solovay-style realization machinery)
behind `Cooperates.arithmeticLift`; that development's formulas are a separate syntax, so
the lift's conclusion interprets the outcome formula through the (structure-preserving,
invertible) bridge translation. Like Mathlib and Foundation, the package is dependency
code: kernel-checked here against this toolchain, cited rather than read line-by-line.
(An earlier vendored snapshot of the same development has been retired in its favor.)

Fixed-point *uniqueness* (Barasz §4, Thm 4.3; Lindström Thm 12) is proved in
`FixedPoint.lean` as `glFixedPoint_uniqueness`, via a boxed-equivalence substitution lemma
and Löb's rule.

### Files

* `ModalAgents/GL.lean` — GL lemmas used by the agent proofs.
* `ModalAgents/ModalAgent.lean` — modal agents and the four concrete agents.
* `ModalAgents/FixedPoint.lean` — GL fixed-point existence/uniqueness theorems, the bridge to the upstream `ProvabilityLogic` package, and substitution congruence.
* `ModalAgents/Cooperation.lean` — outcomes, cooperation/defection, and the main cooperation theorems.
* `ModalAgents/Behavioral.lean` — behavioral equivalence for modal agents.

### Scope

This formalization deals only with modal agents, rather than arbitrary
arithmetic agents. Therefore, Corrollary 4.9 about `CliqueBot` (an algorithm 
that only cooperates with syntactic copies of itself) is outside the scope.
Game-theoretic program equilibrium framing is also left for a future paper.
