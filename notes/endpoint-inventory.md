# Endpoint inventory — the audited trust surface

_Drafted 2026-07-20. The inventory itself is enforced in `AxiomAudit.lean`; this note is
the rationale and the record of the judgment calls._

Guard item 3 of `notes/consolidation.md`. The inventory is the table of contents for the
deferred human read-through: everything on it is trust surface, everything off it is
internal and may be renamed, moved, or inlined freely.

## Two tiers, both build-enforced

**Tier 1 — proof endpoints (103).** The `lic_*` property consumers, their
`_ofComputation` / `_ofRepresentation` / `_ofFeedbackTruth` construction-discharged
variants, the M7 witness constructors, and `exists_logical_inductor` /
`LIA_is_logical_inductor`. Listed in `AxiomAudit.lean` under `#assert_axioms_clean`; the
build fails if any acquires a stray axiom or ceases to exist.

**Tier 2 — boundary structures (73).** `#assert_axioms_clean` can only check things with
proof terms, so structures are structurally invisible to it — yet a boundary structure's
**fields are the hypotheses** its endpoint consumes, so it is trust surface. These are
frozen with `#assert_fields`, which fails the build if a field is added or removed
(premise smuggling). Membership is defined by a mechanical test, not taste:

> A structure is Tier 2 iff it appears in the *type* of a Tier-1 endpoint, transitively
> through structure fields.

That test is `SurfaceProbe.lean`'s `#surface_types`. Transitive closure is the right
depth: reading an endpoint's statement means understanding every structure its hypotheses
mention, and recursively theirs — which is exactly why the framework primitives
(`IsLogicalInductor`, `Trader`, `Strategy`, `LUV`, `DeductiveProcess`, …) are on the list.
They are core *definitions*, and the read-through covers every definition.

## Annotation convention

```
Paper node: `thm:scon`
```

Last line of the docstring. Bare backticked labels taken **verbatim** from `\label{…}` in
`notes/1609.03543v5-main.tex`, comma-separated. No en-dash ranges (not per-label
greppable). No `(App. …)` gloss. Explanatory prose goes above the field. Ranges in the
old annotations were expanded to their explicit member labels, so `grep thm:st` now finds
every declaration that serves that node.

`scripts/check-paper-nodes.sh` enforces two invariants: every cited label exists in the
paper source, and every inventory member carries a field. Both currently pass (54 distinct
labels).

## Judgment calls made in the pass (for the read-through to confirm)

These are the places the mechanical test left a decision, resolved as recorded:

1. **Three demotions.** `ComputationClaim`, `PolyTradeEmulatable`, `NumericQuoteTarget`,
   and `TheorySemantics` carried fields from the interrupted pass but are **not** reachable
   from any endpoint even transitively — they appear only inside proof/definition bodies.
   Their fields were **removed**. This is the only place the pass *shrank* the annotated
   surface; none were ever in `AxiomAudit`, so nothing audited was lost. If the
   read-through judges any of these to be genuine boundaries, re-add and extend the probe.

2. **M7 witness constructors → anchor labels.** `codeEvalnNat_polyFueled`,
   `boundedEvalnCompiler`, the `SettlementChecker` / `PatientSettlementClock` /
   `CEEnumeration` plumbing, `PolySequence`, `PolyMachineCodes`, `PolyNatCodes` have no
   node of their own; they realize the efficient-computability obligation, so they carry
   `def:ec`. `liaEfficientPrefixPatch` → `def:lia`.

3. **Quotation substrate → full introspection/self-trust span.** `ArithmeticDecision`,
   `BooleanQuoteCode`, `RationalQuoteCode`, `QuotationTheoryPresentation` serve the whole
   `thm:ref … thm:st` range, so they carry all eight explicit labels rather than a range.
   Verbose but honest and greppable.

4. **Four late labels assigned by role**, having no label in their docstring:
   `IsLogicalInductor` → `def:lic` (already had it, 8-line docstring); `ContinuousSemimeasure`
   → `thm:dus`; `AffineQuotePortfolio`, `CompletedAffineQuoteEq` → `thm:er` (matching their
   `AffineQuoteEq`/`AffineQuoteGE` siblings).

5. **Graded-strength endpoints share a node.** `lic_deducible_eventually_ge` /
   `_price_near_one` / `_tendsto_one` all → `thm:provind`; the three `lic_nonDogmatism*`
   → `thm:nd`; etc. Repeated labels across declarations are expected.

## Regeneration

If the surface changes deliberately: rerun `SurfaceProbe.lean` (`#surface_types` seeded
with the current `#assert_axioms_clean` names, then `#dump_fields` on the result), update
the `#assert_fields` block in `AxiomAudit.lean` and the affected `Paper node:` fields, and
run `scripts/check-paper-nodes.sh`.
