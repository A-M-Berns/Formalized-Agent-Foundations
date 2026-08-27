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

FAF has two complementary goals: faithful, auditable formalization of important
agent-foundations papers, and reusable Lean infrastructure for research that builds on
them. The first governs the trust surface; the second is expressed through a curated
consumer surface. Faithfulness comes first, and the API never hides a modeling boundary
or replaces paper-legible statements with unnecessary abstraction.

Five things get called "a boundary" and they are not the same thing, so the READMEs keep
them apart — and none of the five is reported as a *count*, because a count is what survives
past the thing it counted. Each node's own row in
[`scripts/coverage-classification.md`](scripts/coverage-classification.md) says which, if
any, applies to it. A **modeling substitution** is a weaker or different object standing in for the
one the paper means — the dangerous kind, and the kind that gets disclosed at the statement.
A **representation interface** is a choice of how to present a faithful object, which
restricts *who can supply the input* without changing what is proved. A **paper erratum** is
a defect in the source. A **strengthening** is where the Lean statement is stronger than the
printed one. And **certification technology** is internal machinery whose only job is to
discharge a hypothesis. Only the first is a debt against faithfulness.

## What's here

| Paper<img width="520" height="1"> | Directory | Status |
|---|---|---|
| Garrabrant et al. (2016), [*Logical Induction*](https://arxiv.org/abs/1609.03543) | [`LogicalInduction/`](LogicalInduction/README.md) | Complete; one printed theorem refuted, boundaries itemised per node |
| Barász et al. (2014), [*Robust Cooperation in the Prisoner's Dilemma via Provability Logic*](https://arxiv.org/abs/1401.5577) | [`ModalAgents/`](ModalAgents/README.md) | Complete at the GL level; Thm 4.6 unformalized |
| Garrabrant, Herrmann, and Lopez-Wild (2021), [*Cartesian Frames*](https://arxiv.org/abs/2109.10996) | [`CartesianFrames/`](CartesianFrames/README.md) | Complete |
| Garrabrant (2021), [*Temporal Inference with Finite Factored Sets*](https://arxiv.org/abs/2109.11513) | [`FiniteFactoredSets/`](FiniteFactoredSets/README.md) | Complete; Conjecture 1 stated, unproved |
| Garrabrant, Mayer, Wache, Lang, Eisenstat, and Dell (2024), [*Factored Space Models*](https://arxiv.org/abs/2412.02579) | [`FactoredSpaces/`](FactoredSpaces/README.md) | Complete |
| Eisenstat (2025), [*Condensation: A Theory of Concepts*](https://openreview.net/forum?id=HwKFJ3odui) | [`Condensation/`](Condensation/README.md) | Complete (Ex. 5.1–5.3 out of scope) |

All zero `sorry`, zero `axiom`. Per-paper node counts are checker-derived and live on the
[trust-surface page](docs/trust-surface.html) (its coverage stamp) and in each paper's node
checker output (`scripts/check-*-nodes.py`); each directory's README gives the detailed statement-level
accounting — what is proved, what is modeled, which printed statements were corrected — and
exactly where the trust boundary sits.

For downstream work, use the supported entrypoints below. Each deliberately avoids
unnecessary construction or regression-test machinery; the module documentation names
the deeper imports when those details are needed.

| Library | Recommended import |
|---|---|
| Logical Induction | `import LogicalInduction.API` |
| Modal Agents | `import ModalAgents.API` |
| Cartesian Frames | `import CartesianFrames.API` |
| Finite Factored Sets | `import FiniteFactoredSets.API` |
| Factored Space Models | `import FactoredSpaces.API` |
| Condensation | `import Condensation.API` |

Consumer readiness is a checked completion criterion, and it is the intended end state
for **every** paper this repository takes on — not a retrofit for the ones that happen
to be finished. A paper marked completed in `scripts/papers.py` must advertise an API and
supply an isolated client smoke test that is built by default;
`scripts/check_paper_wiring.py` fails closed if either is missing. A new formalization is
registered `in-progress` and may land its statements first, but it is not finished until
a separate research project could depend on a small, documented import — the same bar the
five above meet. Proving the paper's nodes is necessary and not sufficient.

The two surfaces stay conceptually distinct: the **trust surface** answers what we claim
faithfully formalizes the paper, and the **consumer surface** answers what downstream work
should depend on. They overlap heavily but need not coincide, and the API may never
obscure an assumption the trust surface discloses. The detailed standing rule lives in
[`CLAUDE.md`](CLAUDE.md#consumer-readiness-is-part-of-paper-completion).

The whole surface is also browsable in one place. [`docs/trust-surface.html`](docs/trust-surface.html)
is a generated read-through guide covering **every registered paper**: every annotated paper
node rendered beside the Lean statement that carries it, in the paper's own order, with a
section per paper. The sections are not symmetric, and the page says why —
*Logical Induction* carries a per-node strength tier and hand-written reading and audit
notes, because it has a machine-checked strength classification; *Cartesian Frames* and
*ModalAgents* and *Finite Factored Sets* have no such classification, so their sections are correspondence views
carrying only what genuinely exists (the Cartesian Frames errata and the Claim 35 ruling;
the ModalAgents scope boundaries and its deliberately unannotated endpoints). No tier is
invented for a paper that does not have one. Regenerate with
`python3 scripts/gen-trust-surface.py`; the page's freshness and its coverage of every
registered paper are both blocking CI checks.

Some of the machinery is shared rather than per-paper: `ShannonInformation/` is a
paper-neutral entropy layer over a vendored, audited slice of the
[PFR project](https://github.com/teorth/pfr), whose FAF-authored
`ShannonInformation/FiniteEntropy/` restates the entropy corpus under finite *entropy*
rather than finite range — the generality *Condensation* is stated at
([`ShannonInformation/README.md`](ShannonInformation/README.md), one import:
`import ShannonInformation.API`).

Along the way the project has also produced some free-standing artifacts: a from-scratch
Brouwer fixed-point theorem via Sperner's lemma (Mathlib has none), an autoformalized
sequent-calculus proof of the de Jongh–Sambin GL fixed-point theorem, and six recorded
errata in the *Logical Induction* paper itself
([`LogicalInduction/notes/paper-errata.md`](LogicalInduction/notes/paper-errata.md)), and a
further set in *Cartesian Frames*
([`CartesianFrames/notes/paper-errata.md`](CartesianFrames/notes/paper-errata.md)) —
including two printed proofs that establish less than their statements require, a false
"equivalently" in a definition, and a footnote asserting an isomorphism that does not
exist. Most of those affected statements are nonetheless true and are proved here — but not
all: *Logical Induction*'s closure under finite perturbations is **false as printed**, and is
formally refuted here, with a corrected replacement proved in its place.

## Building

The toolchain is pinned in [`lean-toolchain`](lean-toolchain) (currently
`leanprover/lean4:v4.31.0`); install [`elan`](https://github.com/leanprover/elan) and
it will fetch that version automatically.

```sh
lake exe cache get      # prebuilt Mathlib oleans (a minute or two)
lake build AxiomAudit   # the checked target: builds every library + the endpoint inventory
lake build APITests     # isolated downstream-style tests of the supported APIs
```

`lake build AxiomAudit` is *the* gate — it subsumes all six paper libraries and fails if any listed
endpoint gains a stray axiom or disappears. The script gates run on the sources and
need no build. Both `AxiomAudit` and `APITests` are default targets in CI:

```sh
scripts/check-paper-nodes.sh          # `Paper node:` labels ↔ paper \label{…}, both directions
python3 scripts/check-cartesian-frames-nodes.py  # numbered CF nodes ↔ committed TeX
python3 scripts/check-modal-agents-nodes.py      # numbered ModalAgents nodes ↔ committed TeX
python3 scripts/check-finite-factored-sets-nodes.py  # numbered FFS nodes ↔ committed TeX
python3 scripts/check_endpoint_coverage.py   # every annotated label has an inventory endpoint
python3 scripts/lint_paper_labels.py         # every paper-facing theorem carries a label
python3 scripts/check_trust_surface.py       # docs/trust-surface.html is not stale
python3 scripts/check_paper_wiring.py        # every registered paper is fully wired up
```

Budget a few hours for the first build: Mathlib arrives prebuilt from the cache, but the
Foundation dependency (~580 modules) and this repo (~110 modules, some with heavy
`Primrec`/`Nat.Partrec` elaboration) are compiled from source. Rebuilds after that are
incremental — seconds for a leaf file, minutes for a `Framework/` change.

## License

Apache License 2.0 — see [`LICENSE`](LICENSE). The same license Mathlib uses, so material
here can be upstreamed without friction.
