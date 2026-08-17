# `ShannonInformation` — FAF's shared Shannon-information layer

Reusable, paper-neutral infrastructure: entropy, conditional entropy, mutual information
and conditional mutual information, available to any FAF formalization through **one
stable import**.

```lean
import ShannonInformation.API
```

This is **not** a paper formalization. It is deliberately absent from
`scripts/papers.py`'s `PAPERS` registry and listed in `NON_PAPER_LIBRARIES` instead,
alongside `ProvabilityLogic`, the repository's other vendored dependency.

## Purpose

FAF's pinned Mathlib has no Shannon information theory at all —
`Mathlib/InformationTheory/` is `Coding`, `Hamming` and `KullbackLeibler`, and the only
`entropy` in the library is *topological* entropy in `Dynamics/`. Several
agent-foundations papers of interest are written entirely in the missing vocabulary. Rather
than each such formalization re-deriving entropy (or, worse, axiomatizing it), FAF
consumes one pinned, audited, kernel-checked implementation.

**FAF has not re-formalized Shannon information theory.** The mathematics here is the
[PFR project](https://github.com/teorth/pfr)'s (Tao et al.), vendored under Apache-2.0 at
commit `01c9b666945eaf73b3f7d8b20ffe003f8640e630`. What FAF contributes is the vendoring,
two compatibility patches, this consumer surface, the scope analysis, and the tests.

## The two layers, and why they are separate

| layer | path | what it is |
| --- | --- | --- |
| **vendor** | `PFR/` | audited upstream implementation, at upstream module paths. Third-party. Do not edit. |
| **consumer** | `ShannonInformation/API.lean` | the FAF-facing surface. What downstream work imports. |

A downstream paper formalization should import `ShannonInformation.API` and **never name a
`PFR.*` module**. The point of the split is that re-pinning the vendored tree — a routine
maintenance event — must not ripple through paper libraries.

The API is a **pure re-export layer**: it adds no entropy definitions and, currently, no
lemmas. That is a decision. Every statement a client reads through it is upstream's
verbatim, so an API statement cannot drift from the statement that was actually proved,
and nothing has to be re-audited when the vendor tree moves. If a genuinely generic
convenience lemma is ever needed by more than one client it belongs in `API.lean`, inside
the `ShannonInformation` namespace, marked FAF-authored and proved — and listed here.

*Currently FAF-authored lemmas in the API: none.*

## Supported concepts

| concept | declaration | notation |
| --- | --- | --- |
| entropy | `ProbabilityTheory.entropy` | `H[X ; μ]`, `H[X]` |
| conditional entropy | `ProbabilityTheory.condEntropy` | `H[X \| Y ; μ]` |
| mutual information | `ProbabilityTheory.mutualInfo` | `I[X : Y ; μ]` |
| conditional mutual information | `ProbabilityTheory.condMutualInfo` | `I[X : Y \| Z ; μ]` |
| measure entropy | `ProbabilityTheory.measureEntropy` | `Hm[μ]` |
| finite-range variables | `FiniteRange` | — |
| conditional independence | `ProbabilityTheory.CondIndepFun` | — |

Available families: chain rules (`chain_rule`, `cond_chain_rule`, …), nonnegativity
(`entropy_nonneg`, `mutualInfo_nonneg`, `condMutualInfo_nonneg`, …), independence and
conditional-independence characterizations (`mutualInfo_eq_zero`,
`condMutualInfo_eq_zero`, `entropy_pair_eq_add`), identically-distributed invariance
(`IdentDistrib.entropy_congr`, `IdentDistrib.mutualInfo_eq`, …), entropy under maps
(`entropy_comp_le`, `entropy_comp_of_injective`, `condEntropy_comp_self`), and
submodularity (`entropy_submodular`, `entropy_triple_add_entropy_le`).

`ShannonInformation/API.lean` carries the full inventory in its module docstring.

## Scope restrictions — read before relying on a statement

**`ShannonInformation/SCOPE.md` is required reading.** In one line:

> The definitions are correct for countable-discrete variables; the *theorems* are proved
> only for **finite-range** ones (`FiniteRange X : (Set.range X).Finite`).

That is a genuine mathematical restriction, not a typeclass artefact, and it is narrower
than the "countable discrete with finite entropy" setting some source papers assume.
`SCOPE.md` records exactly which theorems need it, which survive without it, what
generalization would cost, and one sharp trap (`∑'` is `0` on non-summable families, so
`H[X]` for an infinite-entropy variable is silently `0`).

## Vendoring and update policy

Provenance, the derived module closure, and both patches: `vendor/PROVENANCE.md`.
Attribution and modification notice: `vendor/NOTICE.md`. Licence: `vendor/LICENSE-PFR`.

```sh
ShannonInformation/vendor/vendor-pfr.sh            # regenerate PFR/ from upstream + patches
ShannonInformation/vendor/vendor-pfr.sh --verify   # audit: must report IDENTICAL
```

The closure is **derived** by walking imports (`vendor/closure.py`), not hand-picked. That
is what keeps PFR's additive-combinatorics machinery out: it is simply unreachable from
entropy. `vendor/EXTERNAL-IMPORTS.txt` records every non-PFR import — all `Mathlib.*`; an
entry from `AddCombi` or another PFR dependency would be a regression.

When bumping upstream, classify every new breakage as *compatibility* (→ a new numbered
patch with justification) or *mathematics* (→ take it upstream, do not carry it here), and
re-check `SCOPE.md`, since a newer upstream may have relaxed hypotheses.

## Trust surface

- `sorry`-free, and no new `axiom` declarations. The vendored closure contains no `sorry`.
- `ShannonInformation/AxiomAudit.lean` asserts axiom-cleanliness on representative public
  endpoints, and is built by default. It is deliberately **separate** from the repository's
  top-level `AxiomAudit.lean`: that file is the *paper* endpoint inventory, keyed to
  `Paper node:` annotations and per-paper regeneration procedures, and a non-paper library
  has no place in it. The enforcement is the same; the bookkeeping is kept where it belongs.
- Distinguish carefully when reading: **mathematics inherited from PFR** (all of `PFR/`),
  **compatibility patches** (two, in `vendor/patches/`), **new FAF lemmas** (none yet), and
  **desired future generalization** (`SCOPE.md` §5).

## How a future paper formalization should depend on this

1. `import ShannonInformation.API`, and nothing from `PFR.*`.
2. Read `SCOPE.md` first and decide, explicitly, whether the paper's statements live inside
   the finite-range fragment. If they do, disclose that as a modeling decision in the
   paper's own README — do not let a reader infer it from a `variable` block.
3. Do not define entropy, conditional entropy, mutual information or conditional mutual
   information. If a needed fact is missing, prefer proving it in the paper library from
   re-exported endpoints; promote it here only when a second client needs it.
4. Client-style examples of exactly this live in `APITests/ShannonInformation.lean`.

## Motivation, and what this is not

The infrastructure was motivated by a feasibility spike for **Condensation** (Eisenstat),
and is relevant to **Natural Latents** (Wentworth–Lorell) — which has since been assessed
and does **not** fit inside the finite-range fragment as written, though its computed
examples do; see `SCOPE.md` §6. Neither paper is a dependency of this layer, neither is formalized here, and
no declaration from either appears anywhere in it. This is shared substrate; the papers are
separate work.
