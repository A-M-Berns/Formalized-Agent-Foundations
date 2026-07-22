# Planned refactor: shared agent / cooperation vocabulary

Status: **not started** — design note only. Recorded 2026-07-22.

## Motivation

`Barasz` (`ModalAgents/`) and `Critch` currently sit side by side under the
default target with no code shared and no cross-imports. They are siblings, not
a dependency chain, because they live in different object languages with
different box semantics:

- Barasz: propositional modal **GL**. Agent = `Modal.Formula ℕ` with boxed
  self/reference atoms (`ModalAgent` inductive). Box is unbounded GL `□`.
  Cooperation rides on GL's Löb axiom.
- Critch: first-order **arithmetic** (`ℒₒᵣ`). Agent = arithmetical sentences
  with a resource parameter `k`. Box is bounded `□_k`
  (`Theory.RestrictedProvable k`), which is *not* GL-normal — the reason Critch
  needs a fresh parametric Löb theorem instead of reusing the modal one.

Conceptually, Critch's robust-cooperation result (Theorem 2 / G-fairness) is the
bounded-resource generalization of Barasz's FairBot/PrudentBot cooperation:
Barasz is the "unbounded proof search" idealization; Critch is the same story
with a proof budget. Making that kinship explicit in the code is the goal.

## Goal

Abstract the agent / `outcome` / `Cooperates` vocabulary over the box so that
`ModalAgent` (GL) and Critch's arithmetical agent become two *instances* of one
interface, rather than two independent developments that merely rhyme.

## Scope — what is shared vs. what stays per-instance

Shared (the new interface):
- an abstract `Agent` carrier with an arity and a finite family of lower-rank
  reference agents (the well-founded `rank` recursion is identical in both
  developments and should live once);
- the two-agent `outcome` combinator and its fixed-point unfolding
  (`F_of` / `outcome_unfold` shape in `ModalAgents/Cooperation.lean`);
- `Cooperates` / `Defects` predicates and the outcome bookkeeping lemmas that
  are stated purely in terms of "the box" and a fixed-point operator.

Stays per-instance (cannot be shared — different semantics):
- the box itself (GL `□` vs. bounded `□_k`) and its fixed-point operator
  (`glFixedPoint` vs. `parameterizedFixedpoint`);
- the actual cooperation *theorems*, since they depend on Löb (GL axiom for
  Barasz, parametric bounded Löb for Critch) — the proofs do **not** transfer;
- Critch's resource parameter `k` and all asymptotic bookkeeping.

Net: the refactor unifies the *scaffolding and statements*, not the proofs. The
payoff is mostly structural/auditability, not proof reuse — worth being honest
about that up front.

## Sketch

1. Introduce `Agent (Box : ...) (FixOp : ...)` (name TBD) parameterized over an
   abstract box and a fixed-point operator, carrying `arity`, `references`, and
   the modalized/rank side-conditions.
2. Generalize `outcome`, `F_of`, `outcome_unfold`, `Cooperates`, `Defects`, and
   the rank/termination lemmas to this interface.
3. Re-express `ModalAgents/ModalAgent.lean` + `Cooperation.lean` as the GL
   instance. Barasz endpoints must keep their current axiom profile
   (`propext`, `Classical.choice`, `Quot.sound` only) — the refactor is not
   allowed to regress that.
4. Instantiate the same interface in `Critch/RobustCooperation.lean` over the
   arithmetical bounded box once `ParametricLöb.lean` exists.

## Sequencing

Do **not** start this before `Critch/ParametricLöb.lean` and a first draft of
`RobustCooperation.lean` exist. Reason: the right abstraction boundary is only
visible once both concrete cooperation developments are written; abstracting
against a single instance (Barasz) risks baking in GL-specific assumptions that
the bounded instance then can't satisfy. Write both concretely, then lift the
common shape.

## Optional follow-on (separate deliverable)

A limit/reduction theorem — as the budget `k → ∞`, Critch robust cooperation
recovers Barasz GL-level cooperation — would be the real formal bridge between
the two papers. Not part of this refactor; a genuine new result if pursued.
