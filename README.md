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
| Garrabrant et al. (2016), [*Logical Induction*](https://arxiv.org/abs/1609.03543) | [`LogicalInduction/`](LogicalInduction/README.md) | Unconditional construction of a logical inductor + the full property tail: all 53 paper nodes formalized, 46 at paper strength and 7 with a named interface or class restriction retained. Two disclosed modeling substitutions. Zero `sorry`, zero `axiom`. |
| Barász et al. (2014), [*Robust Cooperation in the Prisoner's Dilemma via Provability Logic*](https://arxiv.org/abs/1401.5577) | [`ModalAgents/`](ModalAgents/README.md) | Complete at the Gödel–Löb provability-logic level, including a proved (not axiomatized) GL fixed-point theorem. Zero `sorry`, zero `axiom`. |
| Garrabrant, Herrmann, and Lopez-Wild (2021), [*Cartesian Frames*](https://arxiv.org/abs/2109.10996) | [`CartesianFrames/`](CartesianFrames/README.md) | All 60 numbered nodes formalized — every definition, claim, and the Decomposition Theorem — across the main text and both appendices, at paper strength with no modeling substitutions. One node is formalized in part by ruling (Claim 35, whose External/Internal half is ill-typed as printed). Zero `sorry`, zero `axiom`. |

Each directory's README gives the detailed statement-level accounting: what is proved,
what is modeled, and exactly where the trust boundary sits.

Along the way the project has also produced some free-standing artifacts: a from-scratch
Brouwer fixed-point theorem via Sperner's lemma (Mathlib has none), an autoformalized
sequent-calculus proof of the de Jongh–Sambin GL fixed-point theorem, and four recorded
errata in the *Logical Induction* paper itself
([`LogicalInduction/notes/paper-errata.md`](LogicalInduction/notes/paper-errata.md)), and a
further set in *Cartesian Frames*
([`CartesianFrames/notes/paper-errata.md`](CartesianFrames/notes/paper-errata.md)) —
including two printed proofs that establish less than their statements require, a false
"equivalently" in a definition, and a footnote asserting an isomorphism that does not
exist. Every affected statement is nonetheless true, and is proved here.

## Building

The toolchain is pinned in [`lean-toolchain`](lean-toolchain) (currently
`leanprover/lean4:v4.31.0`); install [`elan`](https://github.com/leanprover/elan) and
it will fetch that version automatically.

```sh
lake exe cache get      # prebuilt Mathlib oleans (a minute or two)
lake build AxiomAudit   # the checked target: builds every library + the endpoint inventory
```

`lake build AxiomAudit` is *the* gate — it subsumes all three libraries and fails if any listed
endpoint gains a stray axiom or disappears. The three script gates run on the sources and
need no build:

```sh
scripts/check-paper-nodes.sh          # `Paper node:` labels ↔ paper \label{…}, both directions
python3 scripts/check-cartesian-frames-nodes.py  # numbered CF nodes ↔ committed TeX
python3 scripts/check_endpoint_coverage.py   # every annotated label has an inventory endpoint
python3 scripts/lint_paper_labels.py         # every paper-facing theorem carries a label
```

Budget a few hours for the first build: Mathlib arrives prebuilt from the cache, but the
Foundation dependency (~580 modules) and this repo (~110 modules, some with heavy
`Primrec`/`Nat.Partrec` elaboration) are compiled from source. Rebuilds after that are
incremental — seconds for a leaf file, minutes for a `Framework/` change.

## License

Apache License 2.0 — see [`LICENSE`](LICENSE). The same license Mathlib uses, so material
here can be upstreamed without friction.
