# Formalized Agent Foundations

Lean 4 formalizations of important papers in agent foundations and open-source game
theory, built on [Mathlib](https://github.com/leanprover-community/mathlib4) and the
[Foundation](https://github.com/FormalizedFormalLogic/Foundation) library of the
Formalized Formal Logic project.

The formalizations are produced by orchestrated AI agents — parallel prover/auditor/fixer
agents under adversarial cross-checking — with a standing discipline of *honest
accounting*: every public theorem is enumerated in a build-checked inventory
(`AxiomAudit.lean`) that fails compilation if any endpoint acquires an axiom beyond
Lean's standard three (`propext`, `Classical.choice`, `Quot.sound`) or silently
disappears, and every modeling substitution is disclosed at the statement, not
discovered by the reader.

## What's here

| Paper | Directory | Status |
|---|---|---|
| Garrabrant et al. (2016), [*Logical Induction*](https://arxiv.org/abs/1609.03543) | [`LogicalInduction/`](LogicalInduction/README.md) | Complete: unconditional construction of a logical inductor + the full property tail, with two disclosed modeling substitutions. Zero `sorry`, zero `axiom`. |
| Barász et al. (2014), [*Robust Cooperation in the Prisoner's Dilemma via Provability Logic*](https://arxiv.org/abs/1401.5577) | [`ModalAgents/`](ModalAgents/README.md) | Complete at the Gödel–Löb provability-logic level, including a proved (not axiomatized) GL fixed-point theorem. Zero `sorry`, zero `axiom`. |

Each directory's README gives the detailed statement-level accounting: what is proved,
what is modeled, and exactly where the trust boundary sits.

Along the way the project has also produced some free-standing artifacts: a from-scratch
Brouwer fixed-point theorem via Sperner's lemma (Mathlib has none), an autoformalized
sequent-calculus proof of the de Jongh–Sambin GL fixed-point theorem, and four recorded
errata in the *Logical Induction* paper itself
([`notes/logical-induction-paper-errata.md`](notes/logical-induction-paper-errata.md)).

## License

Apache License 2.0 — see [`LICENSE`](LICENSE). The same license Mathlib uses, so material
here can be upstreamed without friction.
