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

### Paper source and node provenance

The paper is committed as `ModalAgents/notes/1401.5577-main.tex` (with its `.bbl` and the
matching PDF), so the spec travels with the formalization.

Barász et al. number their nodes off a single section-scoped counter shared by
`theorem`/`lemma`/`proposition`/`corollary`/`condition`, and only 22 of those nodes carry
a LaTeX `\label` — several that this development proves are unlabeled. So, as in
`CartesianFrames/`, the **printed number** is the provenance key: paper-facing endpoints
carry a final docstring line `Paper node: Theorem 4.7 (§4).`, and
`scripts/check-modal-agents-nodes.py` (blocking in CI) validates them fail-closed. It
recomputes the node set from the committed TeX by emulating the counter rather than
hard-coding a table, requires the cited *kind* to match the environment the paper used,
requires the marker to be the last line of a docstring on a *named* declaration, and
requires every annotated declaration to be listed in `AxiomAudit.lean`'s MA-INVENTORY
block. (The paper's `definition` environment is an uncounted `trivlist`, so there are no
numbered definitions to cite.)

Six inventoried endpoints deliberately carry **no** annotation, because they render no
numbered node — each says so in its own docstring:

| declaration | what the paper actually says |
|---|---|
| `subst_congr` | GL-level substitution congruence; Lemma 4.5 is the *arithmetic* statement, which this does not state |
| `defectBot_defects`, `cooperateBot_cooperates` | §2 prose in an unnumbered `remark` (`PA ⊢ [DB(X)=D]`, `PA ⊢ [CB(X)=C]`) |
| `fairBot_vs_cooperateBot`, `fairBot_vs_defectBot` | §3 prose on FairBot's unexploitability "by inspection" and its waste against CooperateBot |
| `prudentBot_vs_defectBot` | the "in particular, `PA+1 ⊢ [PB(DB)=D]`" step *inside* the proof of Thm 3.2, not one of its conjuncts |

The converse direction is not checked, and should not be: the scope note below means
several numbered nodes (Cor. 4.9, and Thm 3.2's unexploitability conjunct, which
quantifies over all opponents) have no Lean statement here.

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
