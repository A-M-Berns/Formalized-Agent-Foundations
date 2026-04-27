# Agent Foundations

Lean 4 formalizations of papers in agent foundations and open-source game
theory, built on the
[Foundation](https://github.com/FormalizedFormalLogic/Foundation) library of the Formalized Formal Logic project.

## Barasz et al. 2014

Formalization of *Robust Cooperation in the Prisoner's Dilemma via
Provability Logic*.

The Barasz development is formalized at the level of Gödel-Löb provability logic. It covers:

* the modal agent definition from §4;
* CooperateBot, DefectBot, FairBot, and PrudentBot;
* the GL fixed-point construction used to define interaction outcomes;
* the cooperation results for FairBot and PrudentBot from §§2-3;
* the modal agent fixed-point equation (§4, Thm 4.7);
* the modal agent behavioral result (§4, Thm 4.8, GL-level form);
* the rank-0 FairBot-to-CooperateBot result (§4, Thm 4.10);
* the generic lift from GL-provability to arithmetical realizations (§4, Thm 4.1).

### Axioms

Two standard GL fixed-point facts are currently axiomatized because they are
not yet available in Foundation:

* fixed-point existence, in the single-variable form used by Barasz §4, Thm 4.2;
* fixed-point uniqueness, corresponding to Barasz §4, Thm 4.3.

These are the de Jongh-Sambin-Bernardi fixed-point theorem and its uniqueness
theorem. Barasz cites Lindstrom's presentation; Boolos, *The Logic of
Provability*, Ch. 8 is another standard reference.

### Files

* `Barasz/GL.lean` — GL lemmas used by the agent proofs.
* `Barasz/ModalAgent.lean` — modal agents and the four concrete agents.
* `Barasz/FixedPoint.lean` — fixed-point assumptions and substitution congruence.
* `Barasz/Cooperation.lean` — outcomes, cooperation/defection, and the main cooperation theorems.
* `Barasz/Behavioral.lean` — behavioral equivalence for modal agents.

### Scope

This is not a formalization of arbitrary arithmetic agents. Corollary 4.9
(CliqueBot is not a modal agent) is therefore outside the current scope. The
game-theoretic program-equilibrium framing is also left for a future
paper.
