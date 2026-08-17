# Factored Space Models — trust surface

Formalization of Scott Garrabrant, Matthias G. Mayer, Magdalena Wache, Leon Lang, Sam
Eisenstat and Holger Dell, *Factored space models: Towards causality between levels of
abstraction* ([arXiv:2412.02579](https://arxiv.org/abs/2412.02579), v2). The paper is the
specification: `notes/2412.02579v2-main.tex` (with `notes/meta/environment.tex` and
`notes/tables/`) is the exact arXiv source and `notes/2412.02579v2.pdf` the matching PDF.

**Status: in progress.** This file says what is claimed so far and what is not yet.
The paper has 50 numbered nodes on one section-scoped counter (14 definitions, 28
lemmas, 6 propositions, 1 theorem, 1 corollary); the target is all of them. The
feasibility spike that preceded this formalization is recorded in
`notes/spike-2026-08-17.md`.

## What is claimed

| § | Content | Nodes | File |
|---|---|---|---|
| 4.1 | Derived variables; the factored space and its background variables | Definitions 4.1, 4.2 | `Basic.lean` |
| 4.2 | Disintegration, generation, history; the history is the minimal generating set; history of a joint variable; history of a variable is the union of the histories of its values | Definitions 4.5, 4.6; Lemmas 4.7, 4.8, 4.9 | `History.lean` |
| 4.3 | Structural independence | Definition 4.10 | `Independence.lean` |
| 4.4 | Structural time; structural time via structural independence | Definition 4.11; Lemma 4.12 | `Independence.lean` |
| A | Disintegration closed under ∩ and ∪; generation closed under ∩ | Lemmas A.1, A.2 | `History.lean` |
| B.1 | The composition axiom | Lemma B.1 | `Independence.lean` |
| C.1 | Alternative characterizations of derived variables and of generation | Lemmas C.3, C.4 | `Basic.lean`, `History.lean` |

## Not yet claimed

Everything else: the probability layer (Definitions 4.3, 4.4, 6.1, C.1, C.2 and the
Appendix-C lemmas), the main theorem (Theorem 6.2, Lemmas 6.3–6.5, Proposition 6.6), the
Bayes-net construction and its properties (§5, Appendix B.2–B.4), and the semigraphoid
proposition (Proposition 5.2). The staging plan is in the harness handoff, not here; this
table is updated as stages land.

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
