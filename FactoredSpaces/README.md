# Factored Space Models — trust surface

Formalization of Scott Garrabrant, Matthias G. Mayer, Magdalena Wache, Leon Lang, Sam
Eisenstat and Holger Dell, *Factored space models: Towards causality between levels of
abstraction* ([arXiv:2412.02579](https://arxiv.org/abs/2412.02579), v2). The paper is the
specification: `notes/2412.02579v2-main.tex` (with `notes/meta/environment.tex` and
`notes/tables/`) is the exact arXiv source and `notes/2412.02579v2.pdf` the matching PDF.

**Status: complete.** All 50 numbered nodes (14 definitions, 28 lemmas, 6 propositions,
1 theorem, 1 corollary) are stated and proved — **five of them in corrected form, because
the printed statement is false**: Lemma 5.3's "τ bijective" (true on strictly positive
distributions, E5), Lemma C.11(3) (needs both marginal-support inclusions, E3), Lemmas
4.7/A.2/4.9 and Theorem 6.2 (need the independent variables' value spaces nonempty,
E1/E12/E14), and Lemma 6.5 (needs `ε > 0`, E15); each correction is disclosed at the
declaration and in `notes/paper-errata.md` — 0 `sorry`, axiom-clean
(`AxiomAudit.lean`, FS-INVENTORY), every node cited from a `Paper node:` line and checked
against the TeX (`scripts/check-factored-spaces-nodes.py`, `notes/scope-manifest.json`:
nothing ruled out of scope), consumer boundary `FactoredSpaces/API.lean` exercised by
`APITests/FactoredSpaces.lean`, registry `scripts/papers.py`: `completed`.  The
formalization went through two adversarial audit rounds plus a final blind audit; the
round records are summarized in `KNOWLEDGE.md`.  This file says what is claimed and how. The feasibility spike that
preceded this formalization is recorded in `notes/spike-2026-08-17.md`, the paper defects
found on the way in `notes/paper-errata.md`, and the sizing memo for the direct proof of
Proposition 5.5 in `notes/dsep-sizing/`.

## What is claimed

| § | Content | Nodes | File |
|---|---|---|---|
| 4.1 | Derived variables; the factored space and its background variables; factorizing distributions; factored space models | Definitions 4.1, 4.2, 4.3, 4.4 | `Basic.lean`, `Probability.lean` |
| 4.2 | Disintegration, generation, history; minimal generating set; history of a joint variable; history as union over values | Definitions 4.5, 4.6; Lemmas 4.7, 4.8, 4.9 | `History.lean` |
| 4.3–4.4 | Structural independence; structural time; time via independence | Definitions 4.10, 4.11; Lemma 4.12 | `Independence.lean` |
| 5.1 | Semigraphoid / graphoid / compositional semigraphoid; structural independence is a compositional semigraphoid | Definition 5.1; Proposition 5.2 | `Semigraphoid.lean` |
| 5.2 | The FSM `M^G` of a DAG; `τ` (in its true form, errata E5); factorization property; **d-separation ⟺ structural independence** (direct proof, no external citation); ancestor relation | Lemma 5.3; Propositions 5.4, 5.5, 5.6 | `BayesNet.lean` (5.3, 5.4), `Separation.lean` (5.5, 5.6) |
| 5.2.3 | Perfect maps; factored space models are more expressive than DAGs (both parts, with the I-map ⟹ factorization step the paper omits, errata E7, and the paper's own 3-point witness) | Definition 5.7; Proposition 5.8 | `PerfectMap.lean` |
| 6 | Conditional independence; **soundness and completeness**; soundness and completeness for events; local-to-global; strong completeness | Definition 6.1; **Theorem 6.2**; Lemmas 6.3, 6.4, 6.5; Proposition 6.6 | `Probability.lean`, `Soundness.lean`, `Completeness.lean`, `LocalToGlobal.lean`, `MainTheorem.lean` |
| A | Disintegration closed under ∩, ∪; generation closed under ∩ | Lemmas A.1, A.2 | `History.lean` |
| B | Composition axiom; the joint node variable's distribution | Lemmas B.1, B.2 | `Independence.lean`, `BayesNet.lean` |
| C | Outer product, marginal; derived variables and generation characterized; interpolation polynomial; cohistory and the completeness apparatus | Definitions C.1, C.2, C.6; Lemmas C.3–C.13, C.15–C.20; Corollary C.14 | `Basic.lean`, `History.lean`, `Probability.lean`, `LocalToGlobal.lean`, `Completeness.lean` |

Every statement is stated against the paper. Two places where the formalization proves
more than the paper writes: the semigraphoid axioms of probabilistic independence, which
the paper cites from Pearl in Proposition 5.2's proof, are proved
(`isSemigraphoid_condIndepRel`); and Proposition 5.5 is proved *directly* — the paper
cites the soundness and completeness of d-separation (Koller–Friedman) — through a
closed-form conditional history for `M^G` (`ConditionalHistory.lean`) and an active-trail
characterization of a vertex-set criterion (`ActiveTrails.lean`), so no citation boundary
remains anywhere. d-separation itself, which the paper uses without defining, is
`Digraph.DSeparated` (`DSeparation.lean`, `dd:dsep`).

## How to read the statements

* `Pt Ω` (`∀ i, Ω i`) is the factored space `Ω = ×_{i∈I} Ω_i` (`dd:pi-space`); a random
  variable is any function `Pt Ω → α` and `Val(X)` is its codomain (`dd:variable`).
* `J.piecewise a b` is the paper's merge `a_J · b_{I∖J}`; `splice J S T` is
  `S_J × T_{I∖J}` (`dd:splice`). Definition 4.5 is stated literally as `C = prodSplit J C`
  and worked with through `disintegrates_iff_splice`.
* `history X C` is `H(X | C)`; `history X Set.univ` is the unconditional `H(X)`;
  `eventHistory A C = history (indic A) C` is `H(A | C)` (`dd:event-indicator`);
  `fiber Z z` is the event `{Z = z}`, so `history X (fiber Z z)` is `H(X | z)`.
* Value spaces carry an inhabitation hypothesis only where the printed statement is
  otherwise *false* — Lemmas 4.7, A.2, 4.9 and Theorem 6.2 (errata E1, E12, E14; see
  `notes/paper-errata.md`). Theorem 6.2 carries the weakest such hypothesis,
  `Nonempty α ∨ Nonempty β` (it fails only with both value spaces empty). Lemmas 4.7 and
  A.2 carry `[Nonempty α]`, which is slightly stronger than their exact failure set — they
  fail only when `Val(X)` is empty *and* at least two factors are empty; with `Val(X)` empty
  and at most one empty factor they hold — because the exact condition is a statement
  about the factors, not a hypothesis the paper's statement has a slot for. Lemma 4.9's
  `[Nonempty α]` is exact (one empty factor suffices to refute it). Definition 5.1 /
  Proposition 5.2, Lemmas 4.8, 4.12 and B.1 carry no value-space hypothesis at all (their
  empty-value cases are proved directly through the degenerate-history lemmas of
  `History.lean`).

The `dd:` glossary lives in `FactoredSpaces.lean`; settled decisions, the correspondence
table and pitfalls are in `KNOWLEDGE.md`.
