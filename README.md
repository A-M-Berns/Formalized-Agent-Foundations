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

Two standard GL fixed-point facts are currently axiomatized because they are
not yet available in Foundation:

* `glFixedPoint_thm42`: fixed-point existence, in the single-variable form used by Barasz §4, Thm 4.2;
* `glFixedPoint_uniqueness`: fixed-point uniqueness, corresponding to Barasz §4, Thm 4.3.

These are the de Jongh-Sambin-Bernardi modal fixed-point theorem and its uniqueness
theorem. These theorems are prior to the modal agent framework, and Barasz et al do not provide a proof. 
Instead, they cite Lindström (1996) Thms 11 and 12 as a reference (full reference in `FixedPoint.lean`.)

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

## Critch (2019) *A Parametric, Resource-Bounded Generalization of Löb's Theorem, and a Robust Cooperation Criterion for Open-Source Game Theory*

Status: **In progress.** Abstract infrastructure is being built; no paper
theorems have been formalized yet.

The Critch folder will contain a formalization of this paper in two layers. The
first layer will axiomatize bounded provability abstractly, parallel to
Foundation's provability abstraction interface, and use it for the parametric
bounded Löb theorem and robust cooperation criterion. The second layer will
ground that interface in Foundation's restricted provability predicate.

### Files

* `Critch/BoundedProvability/Basic.lean` — bounded provability and bounded HBL interfaces.
* `Critch/BoundedProvability/Asymp.lean` — asymptotic comparison for proof-bound bookkeeping.
* `Critch/ParametricDiagonal.lean` — the parametric diagonal lemma used in §4.
* `Critch/ParametricLöb.lean` — the abstract bounded Löb theorem from §4.
* `Critch/RobustCooperation.lean` — G-fairness and the robust cooperation theorem from §5.
* `Critch/Grounding/Basic.lean` — restricted provability as the concrete bounded provability predicate.
* `Critch/Grounding/BoundedHBL.lean` — bounded D2 and D3 for restricted provability.
* `Critch/Grounding/BoundedNec.lean` — bounded D1 and related proof-size bookkeeping.

### Axioms

None yet. The abstract layer will make Critch's bounded provability properties
explicit as typeclass assumptions before any paper theorem depends on them.
