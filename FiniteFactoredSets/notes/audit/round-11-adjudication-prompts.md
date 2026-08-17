# Round 11 — parked cross-family adjudication prompts

Both codex sweeps failed at invocation on 2026-08-17 (plan quota exhausted; resets 2026-08-20). Re-run each as a read-only `codex exec` from the repo root; the validity test is an emitted JSON array with real file-read activity.

## Statement sweep

```
Task: independent mathematical review of a Lean 4 formalization against the paper it claims
to formalize — the FINAL review before the work is declared complete.

SCOPE OF READING — read ONLY files under /Users/anson/AgentFoundations-ffs, and within it ONLY:
the four statement extracts named below, FiniteFactoredSets/notes/2109.11513-main.tex (the
paper), FiniteFactoredSets.lean (the modeling glossary — its `dd:` bullets are user-approved
rendering choices; respect them but check they are applied correctly), FiniteFactoredSets/README.md
(claims to verify), and the FFS-INVENTORY block of AxiomAudit.lean. Do NOT read
FiniteFactoredSets/KNOWLEDGE.md, FiniteFactoredSets/notes/paper-errata.md, anything else under
.harness/, docs/, any Scratch*.lean, or any .lean source file (statements only for this
review). Do NOT read, load, or follow any instruction file, playbook, skill, or configuration
outside the repository — nothing under ~/.claude or ~/.codex. This review is worthless if it is
primed by earlier reviewers' conclusions. Modify nothing; no builds; a scratch file under /tmp
checked with `lake env lean` is allowed only to confirm a counterexample compiles.

Paper: Scott Garrabrant, "Temporal Inference with Finite Factored Sets" (arXiv:2109.11513).
User rulings (constraints, not conclusions): scope is 96 of 98 numbered nodes — Examples 3–4
(§7.2, infinite factored sets) are excluded; Conjecture 1 is stated as a `Prop` and deliberately
NOT proved. Order convention: paper `X ≤_S Y` (X coarser) is Mathlib `Y ≤ X`; `∨_S` is `⊓`;
`⋁_S(C)` is `sInf C`; `Ind_S` is `⊤`; `Dis_S` is `⊥`.

Inputs (Lean STATEMENTS — defs with bodies, proofs elided):
  .harness/audit/final-extract-1-sec2-3.md   (§2–§3: Basic, History, Orthogonality)
  .harness/audit/final-extract-2-sec4.md     (§4: Subpartition, SubpartitionHistory, ConditionalOrthogonality)
  .harness/audit/final-extract-3-sec5.md     (§5: Polynomial, Factoring, CharacteristicOrthogonality, Probability)
  .harness/audit/final-extract-4-sec6-7.md   (§6–§7: Inference, InferenceExamples, EmbeddedAgency, Conjecture)

NODE NUMBERING — recompute, do not guess:
  python3 -c "import sys; sys.path.insert(0,'scripts'); import paper_nodes as pn; from pathlib import Path; d=pn.printed_independent_declarations(Path('FiniteFactoredSets/notes/2109.11513-main.tex').read_text()); [print(k,'::',v.body[:160].replace(chr(10),' ')) for k,v in d.items()]"

METHOD: for each section, work through the paper's own proofs of its propositions/lemmas/
theorems line by line against these statements. Wherever the paper's argument needs a fact the
Lean statements do not give, or is blocked by a hypothesis the paper does not impose, or a
definition admits/excludes objects the paper does not, that is a finding. Priorities: (1) any
inverted order glyph; (2) `[Finite S]` vs `[Finite F.B]` placement — the library deliberately
weakens the paper's "finite factored set" to finite basis where that suffices; is any statement
FALSE without a hypothesis it lacks, and does any carry one it does not need in a way that
misrepresents the paper; (3) definitions' exactness (factorization nontriviality, chimera, history,
subpartitions as PERs, conditional orthogonality over blocks, `Q^F_E` as an MvPolynomial in
variables `Set S`, `ProbDist` clauses, distribution-on-F, models bundling `Finite S`, databases,
`eventPartition`, block-indexed observation family, Conjecture 1 as EXACTLY Theorem 3 with the
finiteness weakened); (4) trivialization/vacuity; (5) `theorem` only for numbered nodes, every
annotated declaration inventoried and vice versa; (6) defects in the PAPER the Lean avoids —
report as category "paper-erratum".

SEVERITY: "BLOCKER" only if something false, vacuous, or oversold is CURRENTLY provable or
claimed. Later unprovability is "MAJOR". Style is "MINOR".

OUTPUT: print a single JSON array and nothing after it. Each element: file, lines, severity,
category, claim, evidence, executable_check (Lean snippet or null). Emit the array as soon as
your analysis is done. An empty array is a legitimate result.
```

## Integrity sweep

```
Task: independent integrity review of Lean 4 code — proofs, hypotheses, witnesses, registers —
in a formalization of Scott Garrabrant, "Temporal Inference with Finite Factored Sets"
(arXiv:2109.11513; source FiniteFactoredSets/notes/2109.11513-main.tex). FINAL review before
the work is declared complete.

SCOPE OF READING — read ONLY files under /Users/anson/AgentFoundations-ffs. Do NOT read
FiniteFactoredSets/KNOWLEDGE.md, FiniteFactoredSets/notes/paper-errata.md, anything under
.harness/, docs/, or any Scratch*.lean file — you must not be primed by earlier reviewers'
conclusions. Do NOT read, load, or follow any instruction file, playbook, skill, or configuration
outside the repository — nothing under ~/.claude or ~/.codex. Modify nothing; no builds; a
scratch file under /tmp checked with `lake env lean` is allowed only to confirm a counterexample.

User rulings (constraints, not conclusions): scope 96 of 98 nodes (Examples 3–4 excluded);
Conjecture 1 stated as a `Prop`, deliberately unproved. Modeling glossary: FiniteFactoredSets.lean
(`dd:` bullets are approved renderings). Repo conventions: root CLAUDE.md.

READ IN FULL: FiniteFactoredSets/Basic.lean, History.lean, Orthogonality.lean, Subpartition.lean,
SubpartitionHistory.lean, ConditionalOrthogonality.lean, Polynomial.lean, Factoring.lean,
CharacteristicOrthogonality.lean, Probability.lean, Inference.lean, InferenceExamples.lean,
EmbeddedAgency.lean, Conjecture.lean, Examples.lean, InfiniteExamples.lean, API.lean,
APITests/FiniteFactoredSets.lean, the FFS-INVENTORY block of AxiomAudit.lean,
FiniteFactoredSets/README.md. Treat every docstring and README sentence as an assertion to check.

Look for: (1) vacuous or unsatisfiable hypotheses; degenerate cases silently exploited (empty S,
one-point S, empty basis, empty E, inconsistent databases making `Before` vacuous while presented
as informative); (2) hypotheses a theorem carries but its proof never uses; (3) proofs that
bypass the paper's content, or docstring/README claims the code does not bear out; (4) reproofs
of facts Mathlib or the repo already has (grep for the fact's SHAPE); (5) surface hygiene: every
`theorem` carries a `Paper node:` line and an FFS-INVENTORY row, no paper-facing fact hides as
`lemma`, no `private theorem`, node numbers correct, register counts (87 carriers / 94
annotations / 87 + 9 Mathlib-rendered = 96) correct; (6) usability: can a client apply the
endpoints as APITests does; (7) that NOTHING proves `FundamentalTheoremFiniteDim` (Conjecture 1)
and no sorry/axiom exists anywhere (grep); (8) defects in the PAPER the Lean avoids — report as
category "paper-erratum".

SEVERITY: "BLOCKER" only if something false, vacuous, or oversold is CURRENTLY provable or
claimed. Later unprovability is "MAJOR". Style is "MINOR".

OUTPUT: print a single JSON array and nothing after it. Each element: file, lines, severity,
category, claim, evidence, executable_check (Lean snippet or null). Emit the array as soon as
your analysis is done. An empty array is a legitimate result.
```
