# Finite Factored Sets — trust surface

Formalization of Scott Garrabrant, *Temporal Inference with Finite Factored Sets*
([arXiv:2109.11513](https://arxiv.org/abs/2109.11513)). The paper is the specification:
`notes/2109.11513-main.tex` is the exact arXiv source and `notes/2109.11513.pdf` the
matching PDF.

**Status: in progress — §2.1–§2.5 formalized (17 of the 96 in-scope nodes),
with non-vacuity discharged by construction.**
Nothing here is complete, and this file says what is claimed and what is not.

## What is claimed

| § | Content | Nodes |
|---|---|---|
| 2.1 | Partitions, their order, common refinement | Definitions 3, 4, 8; Propositions 1, 2 |
| 2.2 | Factorizations and factored sets | Definitions 10, 11; Proposition 3 |
| 2.3 | The chimera function | Theorem 1; Corollary 1; Definitions 12, 13; Proposition 4 |
| 2.4 | Trivial factorizations | Definition 14; Proposition 5 |
| 2.5 | Finite factored sets | Definition 15; Proposition 6 |

Definition 13 has two halves and both are carried: `chimera` is `χ^F_C(s,t)` and
`chimeraImage` is the setwise `χ^F_C(T,R)` that §3 onward quantifies over.

Every one of those carries a `Paper node:` docstring line and an entry in
`AxiomAudit.lean`'s FFS-INVENTORY block, checked both ways by
`scripts/check-finite-factored-sets-nodes.py`. Zero `sorry`; every endpoint is clean at
`[propext, Classical.choice, Quot.sound]`.

## What is not claimed

Propositions 7–9 of §2.5 (the cardinality identity `|S| = ∏|b|`, its prime corollary, and
the size/dimension table), §3 (orthogonality and time), §4 (subpartitions and conditional
orthogonality), §5 (polynomials and probability, including the Fundamental Theorem), §6
(inferring time), and §7's in-scope material have **no Lean statements yet**. The trust-surface
guide reports the shortfall by kind rather than listing it.

An earlier feasibility spike proved several §5 results — the disjoint-support coefficient
lemma behind Proposition 28, multilinearity of `Q^F_E`, and the Fundamental Theorem's
"vanishes on an open set" step — against a throwaway structure. That file has been
retired rather than kept alongside the real one; the code is preserved at commit
`19a2254` and its findings are in `notes/spike-2026-08-15.md`. It is to be re-landed
against `FactoredSet` in the §5 stage.

**Scope (settled 2026-08-16): 96 of 98 nodes.** In: §1–§6 in full, §7's Definitions
46–50, and Conjecture 1 stated as a `Prop` and deliberately not proved. Out: Examples 3
and 4 only — both concern *infinite* factored sets, the case the paper itself expects the
fundamental theorem to fail in (Example 3 is its intended counterexample).

A consequence worth knowing before reading any §3–§4 statement: **finiteness is kept
minimal.** `FactoredSet` carries no `Fintype S`, and §3–§4 are stated with `Finite B`
only, because none of that material touches polynomials. `|S|` finite enters only at §5,
where `Q^F_E = ∑_{s ∈ E} ∏_{b ∈ B} [s]_b` stops being a polynomial once `S` is infinite.
That is what makes Conjecture 1 — the finite-*dimensional* fundamental theorem — statable
here at all. See `KNOWLEDGE.md` for its status in the literature.

## Nodes rendered by Mathlib vocabulary, with no declaration of ours

These are *not* gaps in coverage but they are also not endpoints, so they are recorded
here rather than inventoried — there is no declaration of this project's to axiom-check.

| Paper node | Rendered as | Tag |
|---|---|---|
| Definition 1 (disjoint union `⊔S`) | absorbed into `Setoid` / the dependent product; it appears in the paper only inside Definitions 2 and 9 | `dd:partition`, `dd:quotient` |
| Definition 2 (partition) | `Setoid S` | `dd:partition` |
| Definition 5 (`∼_X`) | the setoid relation | `dd:partition` |
| Definition 6 (finer / coarser) | Mathlib's `≤` on `Setoid` | `dd:order-flip` |
| Definition 7 (`Dis_S`, `Ind_S`) | `⊥`, `⊤` | `dd:order-flip` |
| Definition 9 (`∏(B)`) | the dependent product `(b : B) → Quotient b` | `dd:quotient` |
| Proposition 2, first sentence (`≥_S` is a partial order) | Mathlib's `PartialOrder (Setoid S)` instance | `dd:order-flip` |

That last row is a *partial* entry, and the only one: `bot_le_and_le_top` carries the
`Proposition 2` annotation but states only the proposition's second sentence (the `Dis`/`Ind`
bounds). The first sentence is Mathlib's instance. Anyone reading the trust-surface card
will see the full printed proposition beside a Lean statement covering half of it; that is
why the row is here.

## Modeling decisions

Defined in full in the glossary at `FiniteFactoredSets.lean`. In brief:

* **`dd:partition`** — partitions are `Setoid`s, as in `CartesianFrames/`. Consequence
  worth stating: Proposition 1 (that `∼_X` is an equivalence relation) is discharged by
  the setoid's own `iseqv` rather than proved. The paper's content is real; under this
  modeling it is free.
* **`dd:order-flip`** — the paper's order glyphs are *inverted* relative to Mathlib's.
  The paper writes `X ≥_S Y` for "`X` is finer than `Y`", so the paper's `≥_S` is
  Mathlib's `≤`; Definition 8's common refinement `⋁_S(C)` — a join in the paper's
  notation — is Mathlib's `sInf`. The library uses Mathlib's convention throughout and
  never introduces the paper's glyphs.
* **`dd:quotient`** — Definition 9's `∏(B)` is the dependent product of the quotients.

There are **no type-`(c)` modeling substitutions** so far: nothing weaker stands in for
one of the paper's objects.

## One thing to check carefully

`IsFactorization` carries a `nontrivial` field, because Definition 10 defines a
factorization as a set of **nontrivial** partitions. Dropping it is not harmless: the
indiscrete partition of a one-element set would become a legal factor, so both `{}` and
`{Ind}` would factor that set, falsifying Proposition 5's uniqueness claim.

The rendering is `¬ IsTrivialPartition`, where `IsTrivialPartition b := Nonempty S ∧ ∀ s
t, b s t`. The `Nonempty S` conjunct is what makes this "exactly one block" (Definition
3) rather than "at most one": over the empty set, Definition 7 sets `Ind_S = {}`, which
has *no* blocks and is therefore not trivial. Rendering nontriviality as the more obvious
`∃ s t, ¬ b s t` would wrongly exclude every partition of the empty set.

## Non-vacuity

**Discharged by construction** in `FiniteFactoredSets/Examples.lean`, which is inventoried
in the FFS-INVENTORY block alongside the nodes it de-vacuates. Four witnesses:

| Witness | Shape | What it rules out |
|---|---|---|
| `boolFS` | `Bool`, `B = {⊥}` — size 2, dimension 1 | `FactoredSet` uninhabited |
| `coordFS` | `Bool × Bool`, `B = {fstFactor, sndFactor}` — size 4, dimension 2 | Proposition 4 being near-tautologous: `not_subsingleton_coordFS_basis` shows the basis really has two factors, and `coordFS_chimera_corners` shows the four `C`-corners of `χ^F_C((true,true),(false,false))` are pairwise distinct |
| `emptyFS` | `Empty`, `B = {⊥}` | the `|S| = 0` case; `not_isFactorization_empty_basis` confirms `B = ∅` is *not* a factorization of the empty set, matching Proposition 5 |
| `unitFS` | `Unit`, `B = ∅` | the `|S| = 1` case; `unitFS_basis_unique` proves this is the *only* factorization of a one-element set, again matching Proposition 5 |

The two structure fields are also independent: `fstFactor` alone satisfies `nontrivial`
but not `bijective`, and `{⊤}` over `Unit` satisfies `bijective` but not `nontrivial`.
