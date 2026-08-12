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

Some inventoried endpoints deliberately carry **no** annotation, because they render no
numbered node — each says so in its own docstring:

| declaration | what the paper actually says |
|---|---|
| `subst_congr` | GL-level substitution congruence; Lemma 4.5 is the *arithmetic* statement, which this does not state |
| `defectBot_defects`, `defectBot_provably_defects`, `cooperateBot_cooperates` | §2 prose in an unnumbered `remark` (`PA ⊢ [DB(X)=D]`, `PA ⊢ [CB(X)=C]`) |
| `fairBot_vs_cooperateBot`, `fairBot_vs_defectBot` | §3 prose on FairBot's unexploitability "by inspection" and its waste against CooperateBot |
| `prudentBot_vs_defectBot` | the "in particular, `PA+1 ⊢ [PB(DB)=D]`" step *inside* the proof of Thm 3.2, not one of its conjuncts |
| `ProvablyDefects.defects`, the `outcome_*` reductions, the `*_not_provably_defects_*` results | this development's own accounting of how far defection can be strengthened — see *Modeling boundary* below |

The converse direction is not checked, and should not be: the scope note below means
some numbered nodes (e.g. Cor. 4.9 on CliqueBot) have no Lean statement here.

## Modeling boundary

One thing this formalization does not carry at the paper's full strength, on exactly
three endpoints, for a reason that is itself proved here.  It is not an axiom gap — the
endpoints are clean — but it is statement-level, so it belongs here rather than in a
proof note.

**Theorem 3.2 is now covered in full.**  Its four conjuncts are unexploitability, mutual
cooperation with itself, mutual cooperation with FairBot, and defection against
CooperateBot, carried respectively by `prudentBot_unexploitable`,
`prudentBot_vs_prudentBot`, `prudentBot_vs_fairBot` and `prudentBot_vs_cooperateBot`.
Unexploitability is the one that quantifies over all opponents: "`Y` exploits
PrudentBot" is `Cooperates prudentBot Y ∧ Defects Y prudentBot`, so unexploitability is

```lean
∀ Y : ModalAgent, Cooperates prudentBot Y → Cooperates Y prudentBot
```

The paper's argument discharges PrudentBot's internal proof obligation by soundness of
`PA`; the modal counterpart is `GL`'s unnecessitation rule `□φ / φ`, which is
*admissible* in `GL`, so the Lean statement needs no soundness side-hypothesis and its
conclusion is `Cooperates` (arithmetically liftable) rather than `¬ Defects`.

**Defection is rendered as unprovability of cooperation — and on three endpoints it
cannot be rendered otherwise.**  There are two predicates:

* `ProvablyDefects X Y` is `Modal.GL ⊢ ∼(outcome X Y)` — the paper's notion, a positive
  `GL` claim, and it lifts to arithmetic through `ProvablyDefects.arithmeticLift`;
* `Defects X Y` is `Modal.GL ⊬ outcome X Y` — strictly weaker
  (`ProvablyDefects.defects` is the one-way implication), metatheoretic, and with no
  arithmetical lift, nor any possible one.

DefectBot's defection is stated at the paper's strength: `defectBot_provably_defects`
gives `GL ⊢ ∼(outcome defectBot Y)` for every `Y`, matching `PA ⊢ [DB(X)=D]`, and
`defectBot_defects` is derived from it.

The other three defection endpoints are **irreducibly weak**, and each obstruction is a
proved Lean fact rather than an admission:

| endpoint | outcome formula is GL-equivalent to | strong form would be | paper's own strength |
|---|---|---|---|
| `fairBot_vs_defectBot` (FairBot's half) | `□⊥` (`outcome_fairBot_defectBot`) | `GL ⊢ ∼□⊥`, i.e. `Con(PA)` | `PA+1 ⊢ [FB(DB)=D]` |
| `prudentBot_vs_defectBot` (PrudentBot's half) | `□⊥` (`outcome_prudentBot_defectBot`) | `GL ⊢ ∼□⊥` | `PA+1 ⊢ [PB(DB)=D]` |
| `prudentBot_vs_cooperateBot` (defection half) | `□□⊥` (`outcome_prudentBot_cooperateBot`) | `GL ⊢ ∼□□⊥`, i.e. `Con(PA+1)` | `PA+2 ⊢ [PB(CB)=D]` |

`GL` proves neither consistency statement — `unprovable_neg_box_bot` is Gödel's second
incompleteness theorem in modal form (a `GL` proof of `□⊥ 🡒 ⊥` collapses under Löb's
rule to a proof of `⊥`), and `unprovable_neg_box_box_bot` follows from it via
`□⊥ 🡒 □□⊥`.  So `fairBot_not_provably_defects_defectBot`,
`prudentBot_not_provably_defects_defectBot` and
`prudentBot_not_provably_defects_cooperateBot` establish that on those three endpoints
the weak `Defects` is forced by the object logic, not chosen for convenience.

The residual gap is therefore precisely this: the paper reads those three claims in
`PA+1`/`PA+2`, and this development works inside `GL`, which is the provability logic of
`PA` alone.  Recovering them at the paper's strength would mean moving to the
provability logic of `PA+1` (`GL` plus `∼□⊥`, i.e. Solovay's `GLS`-style extension) and
reconstructing the fixed-point and soundness machinery there — a different object logic,
not a stronger proof in this one.  The one place the weakening sits underneath a
paper-node claim is the defection half of `prudentBot_vs_cooperateBot` (Theorem 3.2);
the disclosure is repeated at that statement, at `prudentBot_vs_defectBot`, at
`fairBot_vs_defectBot`, and at the definition of `Defects`.

The correspondence is browsable as a generated page: each cited node's printed statement
beside the Lean statements annotated with it, plus the numbered nodes deliberately left
out of scope and the table above, in the ModalAgents section of
[`docs/trust-surface.html`](../docs/trust-surface.html)
(`python3 scripts/gen-trust-surface.py` to regenerate; its freshness is gated in CI).
That section carries **no per-node strength tier and no audit notes**, and says so on the
page: the machine-checked strength classification Logical Induction has does not exist
for this paper, and none is invented for it.

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
behind `Cooperates.arithmeticLift` and `ProvablyDefects.arithmeticLift`; that
development's formulas are a separate syntax, so
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
