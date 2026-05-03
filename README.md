# Formalized Agent Foundations

Lean 4 formalizations of important papers in the fields of agent foundations and open-source game
theory, built on the
[Foundation](https://github.com/FormalizedFormalLogic/Foundation) library of the Formalized Formal Logic project.

## Barasz et al. (2014) *Robust Cooperation in the Prisoner's Dilemma via Provability Logic*.

The Barasz folder contains a formalization of this paper at the level of Gödel-Löb provability logic. It covers:

* the modal agent definition from §4;
* CooperateBot, DefectBot, FairBot, and PrudentBot;
* the GL fixed-point construction used to define interaction outcomes;
* the cooperation results for FairBot and PrudentBot from §§2-3;
* the modal agent fixed-point equation (§4, Thm 4.7);
* the modal agent behavioral result (§4, Thm 4.8, GL-level form);
* the rank-0 FairBot-to-CooperateBot result (§4, Thm 4.10);
* the generic lift from GL-provability to arithmetical realizations (§4, Thm 4.1).

### Axioms

Two standard GL fixed-point facts are currently axiomatized because they are not yet available in Foundation:

* `glFixedPoint_thm42`: fixed-point existence, in the single-variable form used by Barasz §4, Thm 4.2;
* `glFixedPoint_uniqueness`: fixed-point uniqueness, corresponding to Barasz §4, Thm 4.3.

These are the de Jongh-Sambin-Bernardi modal fixed-point theorem and its uniqueness theorem. 
These theorems are prior to the modal agent framework, and Barasz et al do not provide proofs of either.
Instead, they cite Lindström (1996) Thms 11 and 12 as a reference (full citation in `FixedPoint.lean`.)

### Files

* `Barasz/GL.lean` — GL lemmas used by the agent proofs.
* `Barasz/ModalAgent.lean` — modal agents and the four concrete agents.
* `Barasz/FixedPoint.lean` — fixed-point assumptions and substitution congruence.
* `Barasz/Cooperation.lean` — outcomes, cooperation/defection, and the main cooperation theorems.
* `Barasz/Behavioral.lean` — behavioral equivalence for modal agents.

### Scope

This formalization deals only with modal agents, rather than arbitrary
arithmetic agents. Therefore, Corrollary 4.9 about `CliqueBot` (an algorithm 
that only cooperates with syntactic copies of itself) is outside the scope.
Game-theoretic program equilibrium framing is also left for a future paper.
