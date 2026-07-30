# Consolidation & style phase — intentions and best practices

_Started 2026-07-19. Branch: `logical-induction`._

This is step (2) of the fixed order of operations (see CLAUDE.md sequencing override):
the conditional+disclosed endpoint is green, so the work now is consolidation, API
surface, and style — producing the **frozen surface** over which the deferred human
read-through runs. Step (3), `M7-ERRATA-AUDIT`, comes only after that.

## What this phase is for

The deliverable is not "cleaner code." It is **a trust surface small enough and legible
enough to actually read.** The kernel already vouches for every proof body; the
read-through covers statements and definitions only. Every choice in this phase should be
scored against one question: *does this make the top-level statements easier to audit?*

Corollaries:

- **Statements and definitions get the polish. Proof bodies mostly don't.** A 200-line
  ugly-but-kernel-checked proof is fine; a top-level statement whose hypotheses take ten
  minutes to unpack is not. Time spent beautifying tactic blocks is time stolen from the
  actual trust surface.
- **Semantics are frozen; presentation is not.** No statement gets *strengthened,
  weakened, or generalized* in this phase without flagging it explicitly — a
  consolidation commit that changes what a theorem says has left this phase's mandate and
  must say so in its message. Renaming, moving, merging duplicate proofs, and re-stating
  a theorem in equivalent-but-clearer form are all in scope.

## Mechanical guards (set up first, before any refactoring)

1. **Axiom-report sweep as part of the build.** The handoff's cleanliness claims
   (`propext` / `Classical.choice` / `Quot.sound` only, on the named public endpoints and
   the existence result) currently live in `notes/`. Turn them into a checked artifact: a
   dedicated `AxiomAudit.lean` (or similar) that `#print axioms` every public endpoint,
   compiled by the default build target. Then aggressive refactoring cannot silently
   regress axiom-cleanliness or drop an endpoint from the surface.
2. **Green at every stopping point** still holds (CLAUDE.md rule 3). Small compiling
   commits; a consolidation move that breaks the build doesn't get committed half-done.
3. **Endpoint inventory before touching anything.** Enumerate the actual public surface —
   every `lic_*` consumer, every public constructor named in `notes/next-session.md`,
   the existence result — into one list. That list is both the input to the axiom sweep
   and the table of contents for the read-through. If a theorem isn't on the list, it's
   internal and can be renamed/moved/inlined freely; if it is, changes to it are
   surface changes.

## Consolidation targets (expected, to be confirmed by inspection)

- **Cross-file duplication in `Construction/`.** Seven compiler-flavored files were built
  in rapid sequence; parser scaffolding, mode/stack scans, and triangular first-active
  patterns recur. Rule 2b's failure mode (two divergent proofs of one fact) is most
  likely hiding *between* these files. Before merging or refactoring any pair, do a
  shape-based grep pass across both; when a duplicate is found, the honest fix is to
  delete the newer/less-good one and cite the survivor — even when the deleted one is
  more conveniently located.
- **Statement-level noise.** Hypotheses bundled into ad-hoc structures during
  construction sprints should be re-examined: does each structure earn its place on the
  trust surface, or is it packaging that hides a load-bearing premise from the reader?
  Prefer fewer, flatter, self-contained statements at the top level.
- **Disclosure inventory.** The three intentional disclosures (`M7-PREFIX-MACHINE`,
  `M7-DUS-APPROX`, `M7-STRICT-SEPARATORS`) and every type-`(c)` substitution (including
  `dd:fuel`) end up named, cited, and isolated ModalAgents-style in the README's honest
  accounting — discoverable from the top, not from `notes/`.
- **Docstring provenance.** Provenance annotations written at proof time stay; this phase
  may reformat them for consistency but never reconstructs them retroactively.

## Declaration keywords, labels, and witnesses (agreed 2026-07-19)

1. **`theorem` ⇔ the statement exists in the paper.** A declaration is `theorem` iff it
   mirrors a labeled paper node (`thm:`, `lem:`, `cor:` — the paper's own lemmas count:
   `lem:mm`, `lem:budgeter`, `lem:tfdom` are the construction spine). Everything else —
   glue, wrappers, compiler internals — is `lemma`. `private theorem` is banned; private
   things are by definition not paper statements. After the sweep, `grep '^theorem'` *is*
   the paper-facing surface.
2. **Every `theorem` docstring names its paper label.** The label (`thm:x` / `lem:x` /
   `App. x`) appears in the docstring, not just a nearby comment. This is what makes rule
   1 checkable and keeps the label-mirroring convention from rotting.
3. **Lint:** `scripts/lint_paper_labels.py` enforces rules 1–2 textually (every
   `theorem` has a label-bearing docstring; no `private theorem`). Wired into CI as an
   advisory step until the theorem/lemma sweep lands, then flipped to blocking.
4. **`example` is for uncited, axiom-irrelevant demonstrations only** (the
   `IntegrationTest.lean` composition checks). The moment something needs to be cited,
   audited, or `#print axioms`ed, it gets a name. In particular:
5. **Non-vacuity (`N±`) witnesses stay named** (`*_nonempty` lemmas, or concrete defs
   like `ordinaryIndependentBitAtoms`), live in `AxiomAudit.lean` so the build vouches
   for them, and are **deleted** where an M7 construction now discharges the same
   interface — the audit then cites the construction instead of a stand-in.

## Linters (decision)

Conform to the **Lean core linters** (unused variables, unused simp args): fix existing
warnings so the build is quiet, and keep it quiet — a noisy build hides real signal.
Do **not** chase Mathlib's `#lint` env linters or its style linter: this library is not
bound for Mathlib upstream, the docBlame/simpNF classes would generate thousands of
findings against proof-body internals the read-through deliberately ignores, and the
trust-surface lints we actually need (axiom audit, paper labels) are project-specific
and already checked. Upstream package warnings (Foundation's) are not ours to fix.

## File layout (agreed 2026-07-19, execute in pass 3)

Goal: a paper-reader navigates by paper structure; few top-level files; no in-reference
names. `Foo.lean` next to `Foo/` is the standard Lake roll-up idiom (the file re-exports
the directory so `import LogicalInduction.Foo` works) — keep it, one roll-up per folder.

1. **Kill `Engine.lean`** (in-reference name): merge its 196 lines into `Affine.lean`,
   which already imports it.
2. **Merge tiny Properties files into their paper-subsection homes:**
   `Convergence.lean` → `Coherence.lean` (paper §4.1 "Convergence and Coherence");
   `StrictSemimeasure.lean` → `UniversalSemimeasure.lean`. Labels move with their
   theorems. (`Basic.lean` stays: `Convergence` needs `Hysteresis`, which needs `Basic`,
   so folding `Basic` into `Coherence` would cycle — and `Basic.lean` is standard Mathlib
   idiom anyway.)
3. **Top-level folders by paper role.** Target layout:

   ```
   AxiomAudit.lean                — checked endpoint inventory; its own build target,
                                    outside the library (Anson: audit scaffolding does
                                    not belong in the library import graph)
   LogicalInduction.lean          — root roll-up, glossary, naming conventions
   LogicalInduction/
     IntegrationTest.lean         — composition checks (stays top-level)
     Framework.lean + Framework/  — Asymptotics, Foundations, Computable, Criterion,
                                    Affine (with Engine folded in), ROI, Expectations
     Properties.lean + Properties/
     Construction.lean + Construction/
   ```

   `Framework/` = everything the paper's §2–3 criterion statement and the shared proof
   machinery need, upstream of both Properties and Construction. Inside `Construction/`,
   the nine M7 witness compilers live in `Construction/Witnesses/`, separated from the
   §5 spine that proves existence. Module renames churn every import; done as one
   dedicated commit with no other changes.
4. **Lean core linters go to zero and stay there** (unused variables/simp args). Fix
   existing warnings in the same pass; new warnings are treated as regressions. Upstream
   package warnings (Foundation) are exempt.

## Pre-publication cleanup

- **Delete `LogicalInduction/IntegrationTest.lean` before the repo is published** (Anson,
  2026-07-22). It is the roadmap's M3 integration test — a build-enforced regression guard
  that our `Asymptotics`/`Expectations` vocabulary is a definitional drop-in for the
  downstream deference / dose-response corpus, and that the property-tail facts discharge
  that corpus's named hypotheses end-to-end. Valuable *during development* (it catches
  interface regressions), but it references the external corpus by name and is scaffolding,
  not part of the paper formalization's trust surface — so it should not ship. Keep it until
  the consolidation/read-through is otherwise done, then remove it (and drop it from any
  `default_target`/build wiring) as one of the last pre-publish steps.

## Style baseline

- Mathlib naming and style conventions (`lean4-theorem-proving` skill references) are the
  default; deviations are deliberate and local.
- Namespace discipline: everything under `LogicalInduction`; Foundation internals stay
  behind the `Sentence` interface (don't let consolidation scatter them).
- `Asymptotics` remains the single owner of limit vocabulary (`dd:asymp`); if
  consolidation finds a file with private limit definitions, that's a merge target.
- Roadmap `\label`s stay mirrored in comments — moving a theorem moves its label with it.

## Anson

Hi Anson here. What I'd like is for the end result to be as immediately legible as possible that this repo really contains a correct formalization of the paper, with only disclosed holes. Conventions should match the paper as much as possible. There should be no "in-references" i.e. names or ontologies that only make sense to an agent seeped in the repo. The API surface and library organization should be clean and consolidated, logically organized whenever possible. Proof bodies can be opaque that's not a big deal, but there should be as few "tricks" (e.g. setting heartbeats) as possible. The repo should be de-slopified, that's the goal. It should be easy for human-level attention to engage with the repo given basic understanding (and reference to) the paper. At this point, we've done a lot of work on shoring up the formalization and expanding the trust boundary past where it was originally scoped. I think this might mean that there is vestigial structure left from before that work, please fix that. There should be no structural evidence that there was ever a "previous version" of anything. Please make sure names (especially e.g. structure names) are informative and not opaque.

Documentation notes: A) i'd like to split up the README into one overall README that says this is a project formalizing important agent foundations papers using agent orchestration and here's what we have so far without getting into details, and then separate detailed readmes for modalagents and li B) de-sloppify docstrings and comments. the purpose should be to aid in understanding, so cut out "blabbering." Also cut out "in-references" to like phase language we've been using in the project (e.g. M7.) C) it should be very clear what is intended future work and what is permanent modeling disclosure (e.g. in the readme and elsewhere.) Also please include a description of the fuel model and the propositional substrate, including a mention that the paper's explicit description of e.c. includes other models like this one.

## De-slop punch list (2026-07-29)

**Done this pass:**
- ~~`scripts/coverage-classification.md` strength rows stale~~ — all 53 rows re-derived
  from signatures; header rewritten to its `scripts/` home and machine-read contract.
- ~~CLAUDE.md references retired files and phase ontology~~ — rewritten against the
  README / audit ledger / this file; the paper is named as the spec directly.
- ~~In-reference sweep in `.lean` docstrings~~ — five-fixer wave over Framework,
  Construction, Witnesses, Properties (~1,840 changed lines, 73 files): work-package
  tags, seam/route/OPEN-RISK/tranche language, and dead notes pointers replaced by
  self-contained statements. `dd:*` labels kept and now defined in the glossary at
  `LogicalInduction.lean`.
- ~~`M7Witnesses.lean` phase-name~~ — renamed `BoundedEvaluation.lean`, all importers
  and both data files updated.
- ~~Worktree scaffolding cleanup~~ — merged agent worktrees removed (~25 GB).
- ~~`mesh_independence` off-surface~~ — annotated and added to the inventory; the last
  `interface` row is gone, so every paper label is covered by a named endpoint.

**Open:**
- **`#assert_fields` is weaker than its docstring claims**: the macro compares field
  *names* only, so a boundary field's *type* can change silently (it did, benignly:
  `mesh_poly`'s index moved during the precision reindex). Extend the freeze to hash
  field types — it is the actual premise-smuggling guard — or, second best, correct the
  docstring so nobody trusts it for more than it checks.
- **Tier names in `scripts/coverage-classification.md` bake in a misleading hierarchy**
  (Anson, 2026-07-29): calling the LIA-instantiated tier `complete` implies
  `conditional` is an incomplete rendering of the paper, when `conditional` **is** paper
  strength (the paper states §4 for any logical inductor) and instantiation over the
  constructed inductor is a bonus the paper never claims. Rename the axis so the primary
  distinction is paper-strength vs. qualified, with instantiation as a separate flag
  (e.g. `paper` / `qualified` plus an `instantiated` marker). Touches the checker's
  accepted vocabulary and all 53 rows; one deliberate commit. The README already leads
  with the corrected axis.
- **Tricks inventory** (Anson: as few tricks as possible): `Brouwer.lean` sets
  `maxHeartbeats 1000000` (generated interior — acceptable, but say so at the site); the
  `attribute [local irreducible] Nat.sqrt` sections in the `Primrec` files want one
  shared comment explaining the whnf trap rather than bare repetition.
- **Structure-name legibility pass** over the Tier-2 boundary structures: review the ones
  named for their proof role rather than their content (`ExactTheoryPresentation` is now
  per-component completed-theory valuation; `PseudorandomFrequencyInfrastructureWithHistoricalVerifiers` is a mouthful that survived the wave). Renames are surface changes:
  update `AxiomAudit` in the same commit.
- **Pre-publication**: delete `LogicalInduction/IntegrationTest.lean` (see
  "Pre-publication cleanup" above) — it references an external corpus by name and is
  development scaffolding, not trust surface.

## Next lead item (Anson, 2026-07-29): relax injectivity

Priority for the next work block: **remove `Function.Injective f.f` from the
`thm:cee`/`thm:ceu`/`thm:ccee`/`thm:st` chain**, so `def:deferralfunc` matches the paper
(`f n > n` only) across the whole self-trust family. This is the last non-fuel residual on
the property surface and the only remaining item that changes what a reader sees.

Starting position (from the 2026-07-29 attempt): design risk is *retired* — the
first-violator selector's two analytic legs are verified Lean
(`notes/first-violator-selector-check.lean.txt`), and the previously-registered
gated-sum plan is known unsound. What remains is volume, ~2.5–4k lines:
1. variable-width affine `PolySequence` combinator (flat-index ↔ (block, offset) inverse
   prefix-sum as `PolyFueled`, `terms_eq` flattening, rank/closure bookkeeping) — the
   serial bottleneck, everything else builds on it;
2. variable-width gate-fold feature + `RpnSpliceStream` certificate;
3. fibre enumeration, δ-indexed quote package, δ-tower → pointwise bridge;
4. rebuild the five gap-shaped constructions in `QuotationAffine.lean`
   (~2911/3038/3166/3318/3563) — mutually independent, so parallelizable — then delete
   the twelve `hinj` binders (mechanical).
Estimate ~1 week of orchestrated work; stretch risk is item 1's interface bookkeeping.

### Punch-list addition (2026-07-29, Anson)

`scripts/coverage-classification.md`'s tier *names* bake in the same misleading hierarchy
the README just dropped: calling the LIA-instantiated tier `complete` implies the
`conditional` tier is an incomplete rendering of the paper, when in fact `conditional` IS
paper strength (the paper states its §4 theorems for any logical inductor) and
instantiation over the constructed inductor is a bonus the paper never claims. Rename the
axis so the primary distinction is paper-strength vs. qualified, with instantiation as a
separate flag — e.g. tiers `paper` / `qualified` / `interface` plus an `instantiated`
marker. Touches the checker's accepted vocabulary and all 53 rows; do it in one commit.
