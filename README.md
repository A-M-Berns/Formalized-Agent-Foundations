This repository consists of Lean 4 formalizations of important papers in agent foundations and open-source game theory.
Built on the [Foundation](https://github.com/FormalizedFormalLogic/Foundation) library from the Formalized Formal Logic project. Created with help from Claude Code. In general, results that use `theorem` in the codebase are directly from the relevant papers, while results that use `lemma` are helpers not present in the papers directly.

### Barasz et al., *Robust Cooperation in the Prisoner's Dilemma via Provability Logic* (2014)

#### Axioms:
* `glFixedPoint_thm42` — de Jongh–Sambin–Bernardi fixed-point theorem, single-variable form, with the strong form of the existence claim that the fixed point uses only atoms from the input formula and not the diagonal variable (§4, Thm 4.2). Standard GL result (Boolos, *Logic of Provability*, Ch. 8); not yet available in Foundation. The Skolemized operator `glFixedPoint` and its spec theorems are derived from this single axiom.
* `glFixedPoint_uniqueness` — Fixed-point uniqueness (§4, Thm 4.3). Standard GL result; not yet available in Foundation.

#### Files:
* `Barasz/GL.lean` — GL toolkit: Löb's rule, the Löbian circle, and unprovability of `□⊥` / `□□⊥`.
* `Barasz/Agent.lean` — Modal agents (§4, Definition p. 11). Concrete agents: `cooperateBot` (§2, Alg 1), `defectBot` (§2, Alg 2), `fairBot` (§3, Alg 4), `prudentBot` (§3, Alg 5).
* `Barasz/FixedPoint.lean` — GL fixed-point axioms (Thm 4.2, 4.3) and substitution congruence (Lemma 4.5, proved).
* `Barasz/Cooperation.lean` — `outcome` (defined by well-founded recursion on `X.rank + Y.rank` as a GL fixed point) and `outcome_fixed_point` (§4, Thm 4.7, derived from the GL axioms). Cooperation theorems: §2 (`defectBot_defects`, `cooperateBot_cooperates`), §3, Thm 3.1 (`fairBot_vs_fairBot`), §3, Thm 3.2 (all `prudentBot_vs_*` pairs), §4, Thm 4.1 (`Cooperates.arithmeticLift`).

#### To do:
* Behavioral equivalence (§4, p. 12) and Thm 4.8.
* Cor 4.9, Thm 4.10.
* `Barasz/Game.lean` and `Barasz/Equilibrium.lean`: program equilibrium of the open-source PD (currently stubs).
