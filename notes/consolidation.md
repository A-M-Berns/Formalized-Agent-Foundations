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
   every `lic_*` consumer, every public constructor,
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
   the former integration-test composition checks). The moment something needs to be cited,
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

- ~~Delete `LogicalInduction/IntegrationTest.lean`~~ — **done 2026-07-29**. It was the
  regression guard that the downstream deference / dose-response corpus's hypotheses were
  discharged by our objects with no adapter. Removed because the dependency direction has
  flipped: that corpus is a draft and should now be developed against this library, not
  guarded against by it. The one piece of library value it held — discharging `thm:ec`'s
  grid hypothesis from exact world valuations — was promoted to
  `LUV.expect_converges_of_valuesAt` in `Properties/ExpectationConvergence.lean` before
  deletion.

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
- **Standing audit lens: INHABITATION.** The two adversarial lenses used so far
  (faithfulness — does the statement match the paper; integrity — is the proof honest)
  both compare a statement to something *outside* the repo, and neither asks the question
  that produced the worst defect found to date: **does this premise have an inhabitant?**
  On 2026-07-30 that question found `BitPrefixCodeComputation` provably uninhabited, making
  `thm:dus`'s and `thm:strict`'s endpoints vacuously true — a defect that had survived every
  prior audit, the codex cross-check, and the whole fix wave, because a vacuous premise
  looks *stronger*, not weaker, to a faithfulness reviewer. The same question also showed
  `LUVCombinationSyntax` has no constructed inhabitant.
  Make it a third lens, run over boundary structures rather than theorems, asking per field:
  (i) is there a constructed inhabitant in-repo, (ii) if not, can one exist — try to prove
  `IsEmpty`, and (iii) is the metering right for the objects (whole-value metering is
  unsatisfiable whenever the index is asymptotically smaller than the code, i.e. for any
  unbounded-depth family indexed compactly). Also propagate this to the orchestration
  skill's audit fan-out.

- **Standing check: grep every AxiomAudit inventory constructor for zero call sites.** Three
  times now a discharge constructor has been built, proved, audited — and never wired into
  the endpoint whose hypothesis it discharges: `PatientSettlementClock.ofComputations`
  (found 2026-07-29, freed the whole pseudorandomness family), the EF parser/market
  evaluator (found 2026-07-29, freed the `thm:st`/`thm:ccee` closed forms), and
  `LUVCombinationSyntax.meshSoftmaxOperationalWitness` (found 2026-07-30, four expectation
  nodes). This is a systematic failure mode of building the discharge and the consumer in
  separate sessions, not bad luck. Make it a mechanical check before any faithfulness audit:
  for each name in `AxiomAudit.lean`, `rg` its call sites; a constructor with none is either
  dead code or an unclaimed upgrade. Related cause: the discharge often lives *downstream*
  of the endpoint (Construction/ vs Properties/), so it cannot be wired in place — the fix
  is a downstream `_ofX` endpoint, per the `HistoricalMaturity` precedent.

- **`stacks` is a reserved token, not an identifier** (found 2026-08-11 building
  `Construction/Machine/`). Mathlib's `@[stacks]` attribute
  (`Mathlib/Tactic/CrossRefAttribute.lean`) declares `"stacks"` as a syntax atom, so a
  structure field or definition named `stacks` fails to parse with the useless message
  `unexpected token 'stacks'; expected 'lemma'` — pointing at the *following* line, not at
  the name. Symptom to recognise: a parse error naming a token you thought was an ordinary
  identifier, in a file that compiles fine without Mathlib imported. Same class of trap as
  any Mathlib-introduced atom; rename the field (`store`).
- **`.git/info/exclude` silently swallows `Scratch*.lean`.** A spike file created as
  `Scratch_Foo.lean` is neither tracked nor listed by `git status` — a `git add -A`
  commit of "the spike plus its writeup" lands the writeup alone, citing a file that is
  not in the repository. Check `git check-ignore -v` before citing a new file as evidence,
  or just do not open a filename with `Scratch`.
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
- **No `LICENSE` file, and the repo is public.** Nobody can legally build on it as-is,
  which matters for a repo meant to be built on (and partly upstreamed). Anson's call;
  Apache 2.0 is the natural choice if any of this is Mathlib-bound, since Mathlib is
  Apache 2.0. A `CITATION.cff` would also help, given the paper-formalization framing.
- **Drop the Foundation fork — NOT a dependency swap; it is a toolchain upgrade.**
  `lakefile.lean` requires `A-M-Berns/Foundation` for one patch (Matrix name clashes
  blocking Mathlib co-import), and that patch is now merged upstream (PR #835). But every
  upstream commit containing it is on Lean **v4.31+** (the merge commit v4.31.0, current
  HEAD v4.32.2) while this project is on **v4.28.0-rc1**, and Lake requires one toolchain
  across the tree. So switching means bumping Lean *and* moving to a Mathlib compatible
  with it, recompiling ~90k lines against four minor versions of Mathlib API churn —
  a multi-day project with real breakage risk, not an afternoon of hygiene. Queued as its
  own project, to be done when there is no near-term demo or read-through at risk. The
  lakefile comment now states that the fork carries no divergent mathematics, which
  removes the "provisional" smell at zero cost.
- **Structure-name legibility pass** over the Tier-2 boundary structures: review the ones
  named for their proof role rather than their content (`ExactTheoryPresentation` is now
  per-component completed-theory valuation; `PseudorandomFrequencyInfrastructureWithHistoricalVerifiers` is a mouthful that survived the wave). Renames are surface changes:
  update `AxiomAudit` in the same commit.

## Relaxing injectivity — *complete (2026-07-30)*

`Function.Injective f.f` is gone from the `thm:cee`/`thm:ceu`/`thm:ccee`/`thm:st` chain:
all twelve endpoints (four `*_ofRepresentation` in `QuotationAffine.lean`, four
`*_ofRepresentation_unconditional` in `ComputationDP.lean`, four `*_closed` in
`QuoteCodeOfMarket.lean`) now assume of the deferral function exactly what
`def:deferralfunc` asks — `f n > n` plus poly-clocked emission.

The landed device, all in `QuotationAffine.lean`'s `DeferralFibre` section:
1. `AffineCombination.blockSum` + `PolySequence.blockSum` — the variable-width affine
   combinator. The interface bookkeeping flagged as the stretch risk was **avoided, not
   solved**: blocks are padded to a common `width m`, so the flat term index stays a plain
   `range` and the block/offset inverse is `divmod1_polyFueled`. Do not reintroduce a
   prefix-sum inverse.
2. `selectorFeature` (division-free first-violator selector as `EF` syntax) and
   `PairedWeighting` — the paired-index emission certificate carrying `rank ≤ z.unpair.1`
   (the day-indexed `PGenerableWeighting` only gives `rank ≤ z`, too weak for fibre gates),
   with bridges `toPGenerable`, `ofPGenerableFst` (day-indexed data) and
   `ofPGenerableClamped` (source-indexed data read at `min k m`, which keeps a source
   expression legal on the evaluation day and agrees with `k` on the fibre, where `k < m`).
3. `deferred_block_price_tendsto_zero`: for **any** `DeferralFunction`, a uniformly-small
   completed-theory block family has `(Bs ⟨f n, n⟩).price P (f n) → 0`.
3b/3c. Paired-index block families — `pairedExpectationBlocks` (+ its `PolySequence`),
   `pairedExpectationFeature`, `pairedPriceFeature`, `numericQuoteBlocks` — and the four
   instantiations the constructions consume: `crossPrecision_`, `numericQuote_`,
   `conditional_` and `selfTrust_deferred_tendsto_zero`.
4. The four gap-shaped constructions were rewired onto them; their `future_coherent`
   bodies got *shorter* (the limits arrive already indexed by `n` at day `f n`, so the
   `.comp f.tendsto_atTop` step and all flag/preimage rewriting are gone). Deleted with
   them: `completedImageCrossPrecisionQuote`, `completedImageNumericQuote`,
   `completedImageConditionalQuote`, `completedImageSelfTrustQuote`,
   `deferralImageFeature`, `deferralPreimage_le`, `deferralPreimage_ge`.

Two design corrections found while building, both in the code:
* the notes' forcing lemma (`hearly : ∀ j < k₀, g j = 0`) is **not achievable** with a
  continuous gate — a first violator can sit at the threshold with tiny weight. The landed
  `firstSuccess_forces` needs no minimality at all: `Σ gₖπₖdₖ ≥ δ Σ gₖπₖ = δ(1 − Π(1−gⱼ))
  = δ` as soon as one gate saturates. Strictly simpler and stronger.
* the summands are **signed**, so a single selector cancels. The landed device runs two
  selectors (on `max(price,0)` and `max(−price,0)`) and takes their *difference* as the one
  affine coefficient; the two halves are individually non-cancelling.

What survives of the old image-gated layer — `deferralPreimage`, `deferralImageFlag`,
`deferralMatchCount` and their `_at`/`_spec`/`_polyFueled` lemmas — is used **only** by
`FeedbackTruth.lean`'s `thm:wub` chain, where the paper itself asks for a strictly
increasing deferral function, so `StrictlyIncreasingDeferral.injective` supplies the
hypothesis and nothing is narrowed. The section header says so.

### Punch-list addition (2026-07-29, Anson)

`scripts/coverage-classification.md`'s tier *names* bake in the same misleading hierarchy
the README just dropped: calling the LIA-instantiated tier `complete` implies the
`conditional` tier is an incomplete rendering of the paper, when in fact `conditional` IS
paper strength (the paper states its §4 theorems for any logical inductor) and
instantiation over the constructed inductor is a bonus the paper never claims. Rename the
axis so the primary distinction is paper-strength vs. qualified, with instantiation as a
separate flag — e.g. tiers `paper` / `qualified` / `interface` plus an `instantiated`
marker. Touches the checker's accepted vocabulary and all 53 rows; do it in one commit.

### Design-note hygiene (2026-07-30)

`notes/first-violator-selector-check.lean.txt` is **deleted**: its forcing lemma assumed
every earlier gate is exactly `0`, which a continuous `ctsInd` gate cannot deliver, so the
file was a verified proof of an unusable lemma. The real, weaker-hypothesis results now
live in the library (`firstSuccess_sum`, `firstSuccess_sum_le_one`,
`firstSuccess_weight_nonneg`, `firstSuccess_forces` in `QuotationAffine.lean`). Lesson for
future design notes: a standalone compiled check certifies the algebra, not that the
hypotheses are obtainable in situ — state the intended *call site* in the note, or skip
the note and build in place.

### Standing check: strength tiers are re-derived from signatures, never from prose (2026-07-31)

Two consecutive adversarial passes over `scripts/coverage-classification.md` found mis-tier rates
of ~39% and ~31%, and in both the dominant failure was the same: **a row's justification prose
asserted something the Lean signature did not support, and later readers trusted the prose.** Two
concrete instances, both corrected 2026-07-31:

* Ten rows counted a whole-value metering hypothesis (`PolySentenceCodes` &co.) as a routine
  `dd:fuel` certificate, which the table's own rule says does not lower a tier. It is a proved
  class restriction and does. The rule is now spelled out in the file's header.
* Three rows (`thm:ec`, `thm:expcoh`, `thm:perexpkno`) justified a retained premise as "provably
  entailed by the paper's `def:luv` world-value fact". **No such entailment lemma existed.** A
  one-line grep for the entailment would have caught it at any point.

So: when touching a row, re-derive the tier from the endpoint's elaborated signature
(`#check @…`), and when a justification claims a fact is *entailed* or *discharged*, name the
lemma that does it — or say plainly that it is open. A justification that cites no lemma for an
entailment claim should be treated as an unproved obligation, not as background.

Related standing item: the tier vocabulary itself is still on the punch list to be renamed so that
paper-strength-vs-qualified is the primary axis (`complete`/`conditional` currently read as a
completeness gradient rather than two ways of being at paper strength).

### Freeze point (2026-08-02)

The surface is frozen here for Anson's statement read-through. State: 46 of 53 at paper
strength (16 instantiated, 30 universal), 7 qualified; `lake build AxiomAudit` green,
all three script gates green, zero `sorry`, zero added axioms.

Landed in the freeze pass:

* **Tier vocabulary renamed** so paper-strength-vs-qualified is the primary axis:
  `complete` → **`instantiated`**, `conditional` → **`universal`**. The old names read as a
  completeness gradient and invited the false inference that a `conditional` row was a
  weaker result — it was the paper's own theorem. `qualified` is now the only tier that
  falls short of the paper. `scripts/check_endpoint_coverage.py`'s `TIERS` set moved with it.
* **`thm:ref`'s extra premise removed.** `lic_introspection_closed` took
  `hδinv : PolyRatCodes (1/δ)` where tex:1970 asks only for "any e.c. sequence of positive
  rationals `δ → 0`". Found while auditing the `hδinv` sweep rather than by the strength
  audit — the row claimed instantiated-tier while carrying a premise the paper does not
  have. `hδpos` was already in scope, so `PolyRatCodes.inv_of_pos` discharges it at the call
  site. No tier moved; a latent over-claim was removed.

**Deliberately NOT done at the freeze** — every item in this list was subsequently closed
by the 2026-08-02 verification + consolidation wave below (hδinv sweep including internal
lemmas' paper-facing callers; combinedDP collapse, approved; convergencePresentation
deleted, approved; `#assert_fields` docstring corrected; tricks inventory closed). Kept
for the record of what the freeze deliberately excluded.

Next after the read-through: the final fresh-context adversarial audit (phase 3), then the
work queue in `LogicalInduction/README.md` under *What is left* — metacomputation schema
(3 rows, ~1 week) has the best ratio remaining.

### Post-freeze verification + consolidation wave (2026-08-02, pre-review pass)

A fresh full re-audit of all 66 coverage rows from elaborated signatures found **no
mis-tiered row** — the 46-of-53 claim stands (66 labels = 53 theorem + 13 def nodes; the
strength counters in `check_endpoint_coverage.py` count per-label including defs).
Systemic findings, all repaired in this wave:

* **Zero-call-site sweep (standing check, round 4):** `BoundedEvalnCompiler` +
  `boundedEvalnCompiler` deleted (never consumed; the witnesses use
  `codeEvalnNat_polyFueled` directly); `representedSemidecidableClaimsOfComputation`
  deleted (superseded by the sequence-specialized `representedHaltingClaims`); the
  Tok-class `conditionedTranslation_preserves_ec` / `eventualConditionedTranslation_preserves_ec`
  deleted (zero consumers; the criterion class is served by the `_ecRpn` versions).
  `denominatorPatchedGatedConditioningOperationalWitness` and `Dovetail.continuousSemimeasure`
  are intentional leaves and stay.
* **Inhabitation lens (standing lens, round 2):** `LUVCombinationSyntax` now has its
  constructed non-degenerate inhabitant `ordinaryLUVCombinationSyntax`
  (QuoteCodeOfMarket.lean), closing the 2026-07-30 finding. `BitPrefixCodeComputation`
  and the historical-verifier mouthful are confirmed gone.
* **Derivable-premise sweeps:** every remaining caller-facing
  `hδinv/hwidthInv : PolyRatCodes (1/·)` premise removed (six paper-facing endpoints in
  `QuotationAffine.lean`/`ComputationDP.lean`, discharged by `PolyRatCodes.inv_of_pos`;
  this includes `thm:lp`'s endpoint, the same latent over-claim `thm:ref` shed at the
  freeze). The redundant `(b, hshare)` share-norm premise — derivable from
  `BoundedSequence.bounded` since `shareNorm ≤ l1Norm` — removed from the four
  `_ofSyntax` endpoints, the `thm:expprovind` family (8 endpoints), `lic_linearity_of_expectation_seq`,
  `exppolymax_arith`/`expcoh_arith`/`perexpkno_arith`, and the
  `recurringunbiasednessexp`/`prandexp` family (4 endpoints). It stays where `b` is
  load-bearing in hypothesis *types* (the `wubexp` feedback family) and in the
  operational (`ops`-witness) forms in `Properties/ExpectationProperties.lean`.
* **`combinedDP` → `luvThresholdDP` collapse landed** (Anson approved 2026-08-02):
  `expcoh_arith`/`perexpkno_arith` now state over `luvThresholdDP`; `combinedDP`, its three
  helper lemmas and `combinedDP_computable` deleted.
* **Dead API:** `LUVCombinationSyntax.convergencePresentation` deleted (Anson approved).
* **Punch-list closures:** `#assert_fields` docstring corrected (names-only, with the
  type-change logging convention stated); the `Nat.sqrt`-irreducible idiom now has one
  canonical explanation at its first use (`Framework/Emission.lean`); Lean core linter
  warnings fixed to zero (RpnSentence/RpnComputation/RpnSplice/Expectations);
  `CITATION.cff` added (LICENSE already existed — that punch item was stale, as was the
  Brouwer maxHeartbeats one, already commented at site). README's stale "four endpoints
  still whole-value (incl. thm:st)" paragraph corrected to the three-node metacomputation
  family.
