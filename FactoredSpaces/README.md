# Factored Space Models — trust surface

Formalization of Scott Garrabrant, Matthias G. Mayer, Magdalena Wache, Leon Lang, Sam
Eisenstat and Holger Dell, *Factored space models: Towards causality between levels of
abstraction* ([arXiv:2412.02579](https://arxiv.org/abs/2412.02579), v2). The paper is the
specification: `notes/2412.02579v2-main.tex` (with `notes/meta/environment.tex` and
`notes/tables/`) is the exact arXiv source and `notes/2412.02579v2.pdf` the matching PDF.

**Status: in progress — every one of the paper's 50 numbered nodes (14 definitions, 28
lemmas, 6 propositions, 1 theorem, 1 corollary) has a Lean statement; 42 are proved.**
This file says what is claimed so far and what is not yet. The feasibility spike that
preceded this formalization is recorded in `notes/spike-2026-08-17.md`, and the paper
defects found on the way in `notes/paper-errata.md`.

## What is claimed

Proved (0 `sorry`, axiom-clean, gates green):

| § | Content | Nodes | File |
|---|---|---|---|
| 4.1 | Derived variables; the factored space and its background variables; factorizing distributions; factored space models | Definitions 4.1, 4.2, 4.3, 4.4 | `Basic.lean`, `Probability.lean` |
| 4.2 | Disintegration, generation, history; minimal generating set; history of a joint variable; history as union over values | Definitions 4.5, 4.6; Lemmas 4.7, 4.8, 4.9 | `History.lean` |
| 4.3–4.4 | Structural independence; structural time; time via independence | Definitions 4.10, 4.11; Lemma 4.12 | `Independence.lean` |
| 5.1 | Semigraphoid / graphoid / compositional semigraphoid; structural independence is a compositional semigraphoid | Definition 5.1; Proposition 5.2 | `Semigraphoid.lean` |
| 6 | Conditional independence; **soundness and completeness**; soundness and completeness for events; local-to-global; strong completeness | Definition 6.1; **Theorem 6.2**; Lemmas 6.3, 6.4, 6.5; Proposition 6.6 | `Probability.lean`, `Soundness.lean`, `Completeness.lean`, `LocalToGlobal.lean`, `MainTheorem.lean` |
| A | Disintegration closed under ∩, ∪; generation closed under ∩ | Lemmas A.1, A.2 | `History.lean` |
| B.1 | Composition axiom | Lemma B.1 | `Independence.lean` |
| C | Outer product, marginal; derived variables and generation characterized; interpolation polynomial; cohistory and the completeness apparatus | Definitions C.1, C.2, C.6; Lemmas C.3–C.13, C.15–C.20; Corollary C.14 | `Basic.lean`, `History.lean`, `Probability.lean`, `LocalToGlobal.lean`, `Completeness.lean` |

That is 42 of the 50 nodes. Every statement is stated against the paper; the paper's own
proof of Proposition 5.2's axioms 1–4 cites Pearl for the semigraphoid axioms of
probabilistic independence — those are *proved* here (`isSemigraphoid_condIndepRel`), so
no citation boundary remains.

## Stated, proofs in progress

| § | Content | Nodes | File |
|---|---|---|---|
| 5.2 | The FSM constructed from a DAG; `τ` (in its true form, see errata E5); factorization property; **d-separation ⟺ structural independence** (direct proof, no external citation); ancestor relation | Lemma 5.3; Propositions 5.4, 5.5, 5.6 | `BayesNet.lean`, `Separation.lean` |
| 5.2.3 | Perfect maps; factored space models are more expressive than DAGs | Definition 5.7; Proposition 5.8 | `PerfectMap.lean` |
| B.2 | The joint node variable's distribution | Lemma B.2 | `BayesNet.lean` |

d-separation itself (which the paper uses without defining) is `Digraph.DSeparated` in
`DSeparation.lean` (`dd:dsep`); the direct proof of Proposition 5.5 goes through a
closed-form conditional history (`ConditionalHistory.lean`) and an active-trail
characterization (`ActiveTrails.lean`), following `notes/dsep-sizing/memo-2026-08-17.md`.

## How to read the statements

* `Pt Ω` (`∀ i, Ω i`) is the factored space `Ω = ×_{i∈I} Ω_i` (`dd:pi-space`); a random
  variable is any function `Pt Ω → α` and `Val(X)` is its codomain (`dd:variable`).
* `J.piecewise a b` is the paper's merge `a_J · b_{I∖J}`; `splice J S T` is
  `S_J × T_{I∖J}` (`dd:splice`). Definition 4.5 is stated literally as `C = prodSplit J C`
  and worked with through `disintegrates_iff_splice`.
* `history X C` is `H(X | C)`; `history X Set.univ` is the unconditional `H(X)`;
  `eventHistory A C = history (indic A) C` is `H(A | C)` (`dd:event-indicator`);
  `fiber Z z` is the event `{Z = z}`, so `history X (fiber Z z)` is `H(X | z)`.
* Value spaces carry `[Nonempty α]` exactly where Lemma C.3's construction needs it —
  see `notes/paper-errata.md`.

The `dd:` glossary lives in `FactoredSpaces.lean`; settled decisions, the correspondence
table and pitfalls are in `KNOWLEDGE.md`.
