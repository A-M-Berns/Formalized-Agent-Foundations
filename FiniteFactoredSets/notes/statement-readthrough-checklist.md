# Statement / definition read-through — Finite Factored Sets

**Status: DEFERRED (Anson, 2026-08-17) — not waived.** Anson is confident in the formalization on the strength of the harness rounds and the external audit, but is deferring the read-through until he understands the mathematics deeply enough to review the statements himself; the same deferral applies to Cartesian Frames. This is recorded so the repository's own standard (root `CLAUDE.md`) is seen to be pending, not met.

**Original requirement.** Root `CLAUDE.md` requires Anson to read every top-level statement and definition on the frozen consumer surface before the work is called done (external audit FFS-AUDIT-01). This file is the checklist and the place to record the pass; the frozen surface is the head named at the top of the release record. Tick a row only after comparing the printed paper node (`notes/2109.11513-main.tex`, printed-independent numbering) against the Lean statement at the cited line; note anything that needed a second look in the last column. Read `notes/paper-errata.md` first so printed typos are not mistaken for Lean drift, and keep the glossary (`../../FiniteFactoredSets.lean`, the `dd:` bullets) open — especially `dd:order-flip`: paper `X ≤_S Y` is Mathlib `Y ≤ X`, `∨_S` is `⊓`, `⋁_S` is `sInf`, `Ind` = `⊤`, `Dis` = `⊥`.

Frozen head read: `________` (fill in). Reader: Anson. Date: ________.

## Questions to hold for every row
- Does every binder occur in the paper, or is an extra one a genuine strengthening/generalization (disclosed)?
- Is a finiteness hypothesis on `S` vs `F.B` in the right place (`dd:finiteness-minimal`)?
- Is the Mathlib order reversed relative to the paper glyph exactly where expected; is `⊓` the paper's common refinement, not coarsening?
- Does a `Subpartition` statement preserve the paper's domain side condition?
- Are `NotOrth` entries positive assertions, not `¬ Orth`? Is a for-all-models claim protected by a consistency fact where its reading requires one?
- Is any §7 statement presented as a theorem where the paper only defines a notion? Does Conjecture 1 remain a disclosed sharpening?

## Tier A — definitions and structures (read against the paper most carefully)

| ✓ | paper node(s) | Lean | file:line | notes |
|---|---|---|---|---|
| [ ] | Definition 3 | `IsTrivialPartition` (def) | `FiniteFactoredSets/Basic.lean:85` | |
| [ ] | Definition 4 | `part` (def) | `FiniteFactoredSets/Basic.lean:52` | |
| [ ] | Definition 8 | `commonRefinement` (def) | `FiniteFactoredSets/Basic.lean:116` | |
| [ ] | Definition 10 | `IsFactorization` (structure) | `FiniteFactoredSets/Basic.lean:143` | |
| [ ] | Definition 11 | `FactoredSet` (structure) | `FiniteFactoredSets/Basic.lean:150` | |
| [ ] | Definition 12 | `chimeraFun` (def) | `FiniteFactoredSets/Basic.lean:250` | |
| [ ] | Definition 13 | `chimera` (def) | `FiniteFactoredSets/Basic.lean:263` | |
| [ ] | Definition 13 | `chimeraImage` (def) | `FiniteFactoredSets/Basic.lean:271` | |
| [ ] | Definition 14 | `IsTrivialFactorization` (def) | `FiniteFactoredSets/Basic.lean:434` | |
| [ ] | Definition 15 | `size` (def) | `FiniteFactoredSets/Basic.lean:588` | |
| [ ] | Definition 15 | `dim` (def) | `FiniteFactoredSets/Basic.lean:593` | |
| [ ] | Definition 16 | `Generates` (def) | `FiniteFactoredSets/History.lean:56` | |
| [ ] | Definition 17 | `history` (def) | `FiniteFactoredSets/History.lean:174` | |
| [ ] | Definition 18 | `Orthogonal` (def) | `FiniteFactoredSets/Orthogonality.lean:46` | |
| [ ] | Definition 18 | `Entangled` (def) | `FiniteFactoredSets/Orthogonality.lean:56` | |
| [ ] | Definition 19 | `Before` (def) | `FiniteFactoredSets/Orthogonality.lean:121` | |
| [ ] | Definition 19 | `StrictlyBefore` (def) | `FiniteFactoredSets/Orthogonality.lean:127` | |
| [ ] | Definition 20 | `Subpartition` (structure) | `FiniteFactoredSets/Subpartition.lean:53` | |
| [ ] | Definition 21 | `dom` (def) | `FiniteFactoredSets/Subpartition.lean:73` | |
| [ ] | Definition 22 | `restrict` (def) | `FiniteFactoredSets/Subpartition.lean:127` | |
| [ ] | Definition 23 | `GeneratesSub` (def) | `FiniteFactoredSets/Subpartition.lean:331` | |
| [ ] | Definition 24 | `historySub` (def) | `FiniteFactoredSets/SubpartitionHistory.lean:77` | |
| [ ] | Definition 25 | `OrthogonalSub` (def) | `FiniteFactoredSets/ConditionalOrthogonality.lean:55` | |
| [ ] | Definition 25 | `BeforeSub` (def) | `FiniteFactoredSets/ConditionalOrthogonality.lean:60` | |
| [ ] | Definition 25 | `StrictlyBeforeSub` (def) | `FiniteFactoredSets/ConditionalOrthogonality.lean:65` | |
| [ ] | Definition 26 | `OrthogonalGivenSet` (def) | `FiniteFactoredSets/ConditionalOrthogonality.lean:103` | |
| [ ] | Definition 27 | `OrthogonalGiven` (def) | `FiniteFactoredSets/ConditionalOrthogonality.lean:110` | |
| [ ] | Definition 28 | `Poly` (abbrev) | `FiniteFactoredSets/Polynomial.lean:60` | |
| [ ] | Definition 31 | `Q` (def) | `FiniteFactoredSets/Polynomial.lean:314` | |
| [ ] | Definition 32 | `mono` (def) | `FiniteFactoredSets/Polynomial.lean:126` | |
| [ ] | Definition 33 | `monos` (def) | `FiniteFactoredSets/Polynomial.lean:132` | |
| [ ] | Definition 34 | `poly` (def) | `FiniteFactoredSets/Polynomial.lean:137` | |
| [ ] | Definition 35 | `irr` (def) | `FiniteFactoredSets/Factoring.lean:101` | |
| [ ] | Definition 36 | `ProbDist` (structure) | `FiniteFactoredSets/Probability.lean:42` | |
| [ ] | Definition 37 | `IsDistribution` (def) | `FiniteFactoredSets/Probability.lean:261` | |
| [ ] | Definition 38 | `Model` (structure) | `FiniteFactoredSets/Inference.lean:37` | |
| [ ] | Definition 40 | `OrthDatabase` (structure) | `FiniteFactoredSets/Inference.lean:72` | |
| [ ] | Definition 41 | `Orth` (def) | `FiniteFactoredSets/Inference.lean:83` | |
| [ ] | Definition 41 | `NotOrth` (def) | `FiniteFactoredSets/Inference.lean:89` | |
| [ ] | Definition 42 | `Models` (def) | `FiniteFactoredSets/Inference.lean:95` | |
| [ ] | Definition 43 | `Consistent` (def) | `FiniteFactoredSets/Inference.lean:103` | |
| [ ] | Definition 44 | `Complete` (def) | `FiniteFactoredSets/Inference.lean:108` | |
| [ ] | Definition 45 | `StrictlyBefore` (def) | `FiniteFactoredSets/Inference.lean:119` | |
| [ ] | Definition 46 | `Observes` (def) | `FiniteFactoredSets/EmbeddedAgency.lean:62` | |
| [ ] | Definition 47 | `ObservesPartition` (def) | `FiniteFactoredSets/EmbeddedAgency.lean:70` | |
| [ ] | Definition 48 | `Counterfactable` (def) | `FiniteFactoredSets/EmbeddedAgency.lean:80` | |
| [ ] | Definition 49 | `CounterfactableRel` (def) | `FiniteFactoredSets/EmbeddedAgency.lean:86` | |
| [ ] | Definition 50 | `BeforeGivenSet` (def) | `FiniteFactoredSets/EmbeddedAgency.lean:95` | |
| [ ] | Example 1 | `D` (def) | `FiniteFactoredSets/InferenceExamples.lean:44` | |
| [ ] | Example 2 | `D` (def) | `FiniteFactoredSets/InferenceExamples.lean:240` | |
| [ ] | Conjecture 1 | `FundamentalTheoremFiniteDim` (def) | `FiniteFactoredSets/Conjecture.lean:51` | |

Also (no `Paper node:` line by design, but on the surface): `FactoredSet.eventPartition` (Definition 46's `X_E`, `EmbeddedAgency.lean`), `Model.pullback` (Definition 39, `Inference.lean`), `commonRefinement_pair` (Definition 8's binary form, `Basic.lean`), and the nine Mathlib-rendered nodes in `notes/scope-manifest.json`.

## Tier B — theorems (orientation and hypotheses)

| ✓ | paper node(s) | Lean | file:line | notes |
|---|---|---|---|---|
| [ ] | Proposition 1 | `equivalence_setoid` | `FiniteFactoredSets/Basic.lean:78` | |
| [ ] | Proposition 2 | `bot_le_and_le_top` | `FiniteFactoredSets/Basic.lean:99` | |
| [ ] | Proposition 3 | `eq_of_forall_rel` | `FiniteFactoredSets/Basic.lean:171` | |
| [ ] | Proposition 4 | `chimera_spec` | `FiniteFactoredSets/Basic.lean:310` | |
| [ ] | Proposition 5 | `existsUnique_trivialFactorization` | `FiniteFactoredSets/Basic.lean:489` | |
| [ ] | Proposition 6 | `finite_basis_of_finite` | `FiniteFactoredSets/Basic.lean:604` | |
| [ ] | Proposition 7 | `size_eq_prod` | `FiniteFactoredSets/Basic.lean:612` | |
| [ ] | Proposition 8 | `isTrivialFactorization_of_isFactorization` | `FiniteFactoredSets/Basic.lean:685` | |
| [ ] | Proposition 9 | `dim_spec` | `FiniteFactoredSets/Basic.lean:710` | |
| [ ] | Proposition 10 | `generates_tfae` | `FiniteFactoredSets/History.lean:81` | |
| [ ] | Proposition 11 | `generates_spec` | `FiniteFactoredSets/History.lean:127` | |
| [ ] | Proposition 12 | `history_isLeast` | `FiniteFactoredSets/History.lean:214` | |
| [ ] | Proposition 13 | `history_spec` | `FiniteFactoredSets/History.lean:264` | |
| [ ] | Proposition 14 | `orthogonal_iff_exists` | `FiniteFactoredSets/Orthogonality.lean:72` | |
| [ ] | Proposition 15 | `orthogonal_spec` | `FiniteFactoredSets/Orthogonality.lean:91` | |
| [ ] | Proposition 16 | `before_iff_forall_sInf` | `FiniteFactoredSets/Orthogonality.lean:142` | |
| [ ] | Proposition 17 | `before_iff_forall_orthogonal` | `FiniteFactoredSets/Orthogonality.lean:157` | |
| [ ] | Proposition 18 | `before_spec` | `FiniteFactoredSets/Orthogonality.lean:189` | |
| [ ] | Proposition 19 | `history_eq_setOf_before` | `FiniteFactoredSets/Orthogonality.lean:203` | |
| [ ] | Proposition 20 | `generatesSub_tfae` | `FiniteFactoredSets/Subpartition.lean:359` | |
| [ ] | Proposition 21 | `generatesSub_spec` | `FiniteFactoredSets/Subpartition.lean:425` | |
| [ ] | Proposition 22 | `historySub_isLeast_and_eq_history` | `FiniteFactoredSets/SubpartitionHistory.lean:126` | |
| [ ] | Proposition 23 | `historySub_spec` | `FiniteFactoredSets/SubpartitionHistory.lean:170` | |
| [ ] | Proposition 24 | `orthogonal_iff_orthogonalGiven_top` | `FiniteFactoredSets/ConditionalOrthogonality.lean:186` | |
| [ ] | Proposition 25 | `orthogonalGiven_self_iff` | `FiniteFactoredSets/ConditionalOrthogonality.lean:326` | |
| [ ] | Proposition 26 | `Q_eq_poly` | `FiniteFactoredSets/Polynomial.lean:430` | |
| [ ] | Proposition 27 | `poly_union_chimeraImage` | `FiniteFactoredSets/Polynomial.lean:492` | |
| [ ] | Proposition 28 | `eq_C_mul_poly_of_dvd_Q` | `FiniteFactoredSets/Polynomial.lean:551` | |
| [ ] | Proposition 29 | `irr_partition` | `FiniteFactoredSets/Factoring.lean:125` | |
| [ ] | Proposition 30 | `Q_eq_finprod_poly_irr` | `FiniteFactoredSets/Factoring.lean:246` | |
| [ ] | Proposition 31 | `irreducible_poly_of_mem_irr` | `FiniteFactoredSets/Factoring.lean:261` | |
| [ ] | Proposition 32 | `isDistribution_iff` | `FiniteFactoredSets/Probability.lean:290` | |
| [ ] | Proposition 33 | `D_consistent` | `FiniteFactoredSets/InferenceExamples.lean:138` | |
| [ ] | Proposition 34 | `strictlyBefore_X_Y` | `FiniteFactoredSets/InferenceExamples.lean:165` | |
| [ ] | Proposition 35 | `D_consistent` | `FiniteFactoredSets/InferenceExamples.lean:682` | |
| [ ] | Proposition 36 | `strictlyBefore_X_Y_Z` | `FiniteFactoredSets/InferenceExamples.lean:1152` | |
| [ ] | Lemma 1 | `historySub_restrict_part_eq` | `FiniteFactoredSets/SubpartitionHistory.lean:355` | |
| [ ] | Lemma 2 | `historySub_inf_eq` | `FiniteFactoredSets/SubpartitionHistory.lean:436` | |
| [ ] | Lemma 3 | `orthogonalGiven_tfae` | `FiniteFactoredSets/CharacteristicOrthogonality.lean:310` | |
| [ ] | Theorem 1 | `isFactorization_iff_existsUnique` | `FiniteFactoredSets/Basic.lean:183` | |
| [ ] | Theorem 2 | `orthogonalGiven_semigraphoid` | `FiniteFactoredSets/ConditionalOrthogonality.lean:224` | |
| [ ] | Theorem 3 | `orthogonalGiven_iff_forall_isDistribution` | `FiniteFactoredSets/Probability.lean:369` | |
| [ ] | Corollary 1 | `eq_of_part_eq` | `FiniteFactoredSets/Basic.lean:224` | |

## Sign-off

- [ ] Every row above ticked, notes resolved (corrections committed, or recorded as intentional in `KNOWLEDGE.md`).
- [ ] Head re-gated after any correction (`lake build APITests AxiomAudit` + `scripts/check-finite-factored-sets-nodes.py` + `check_trust_surface.py` + `check_paper_wiring.py`).
- [ ] Release record updated with the final SHA.
