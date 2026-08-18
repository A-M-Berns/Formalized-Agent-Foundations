# Condensation — trust surface

Formalization of Sam Eisenstat, *Condensation: A Theory of Concepts* (July 2025, 27 pp.).

There is **no arXiv ID**. The paper's public record is OpenReview `HwKFJ3odui`, with an
author copy at `https://sameisenstat.net/doc/condensation-25-07.pdf`. Both the PDF and a
`pdftotext -layout` extraction of it are committed here, as
[`notes/condensation-25-07.pdf`](notes/condensation-25-07.pdf) and
[`notes/condensation-25-07.txt`](notes/condensation-25-07.txt), so the specification
travels with the formalization. **The paper is the spec.** Unlike every other paper in
this repo, we do **not** have its TeX source; *Numbering and provenance* below says what
that costs and how the node checker is built around the gap.

Read this file for what is and is not claimed, [`KNOWLEDGE.md`](KNOWLEDGE.md) for the
correspondence table and the pitfalls log, and [`notes/roadmap.md`](notes/roadmap.md) for
the plan, the milestones, and the `dd:` glossary in full.

## What the paper is

A *random variable model* (Def 3.1) is a countable discrete probability space `Ω` of
finite entropy together with a finite family of random variables `X_i : Ω → R_i`, each of
countable discrete range. A *latent variable model* for it (Def 3.2) is a second random
variable model `(Λ, (Y_A)_{A ∈ P⁺I})` — its variables indexed by the **nonempty** subsets
of the index set `I` (Def 2.2) — together with a probability-preserving `π : Λ → Ω` such
that each pulled-back `π^* X_i` is almost everywhere a function of the latents that
*contribute* to `i`, that is of `Y_∋i = (Y_A : i ∈ A)`. The reading the paper is after:
`Y_A` is the part of a body of meaning that the observables indexed by `A` share, so a
latent variable model is a system of concepts rather than a single postulated parameter.
Def 3.3 grades such systems by three *scores* — simple `σ_L`, conditioned `χ_L`, and
reconstruction `ϱ_L` — all built from entropies of the latents; lower is better. §3.1 makes
random variable models into a category (Prop 3.7) whose morphisms refine both the
probability space and the ranges, characterizes its isomorphisms (Prop 3.8), and passes to
equality of morphisms almost everywhere and the induced notion of *equivalence*
(Def 3.9–3.10, Props 3.11–3.12).

§4 works in the exact case. Prop 4.2 gives the chain of lower bounds
`σ_L(A) ≥ χ_L(A) ≥ H(Y_∩A) ≥ H(X_A)`, and Def 4.3 calls `L` a *perfect condensation* of `M`
when `χ_L(A) = H(X_A)` for every `A ⊆ I` (and *simply-perfect* when `σ_L(A) = H(X_A)`) —
that is, when the bound is tight. Theorem 4.9 characterizes both: simple-perfection is
equivalent to each `Y_A` being a.e. a function of `X_i` for every `i ∈ A` together with
joint independence of the latents, and perfection is equivalent to the same functional
condition together with the *ordered Markov condition* of Def 4.8. Theorem 4.15, the
comparison theorem of §4, is the paper's first main result: if `L₁` and `L₂` both perfectly
condense the same `M`, then after amalgamating them over a common probability space `Λ₀`
(Defs 4.11–4.12, Lemma 4.13) each `Y_A` is almost everywhere a function of `Z_{⊇A}`, and
reciprocally each `Z_A` of `Y_{⊇A}` — two different systems of concepts for the same world
stand in a correspondence, each side's concepts recoverable from the other side's coarser
ones. §5 replaces the exact hypotheses with quantitative ones. Theorem 5.8 bounds
`H(Y_{⊇A} | Z_G)`, where `G = F°` is the *polar* (Def 5.5) of a family `F ⊆ P⁺I`, by a sum
of reconstruction-type terms `Σ_{B ∈ F} H(Y_{⊇A} | X_B)` plus conditional mutual
informations read off an *intersection tree* (Def 5.6, Prop 5.7) — each term depending on
only one of the two latent systems — with an accompanying exact identity, and Corollaries
5.9 and 5.10 specialize it. The upshot is that the §4 correspondence degrades gracefully:
approximate hypotheses buy an approximate correspondence rather than none.

## Status

**Milestone M2 landed 2026-08-18. Every in-scope node has a Lean carrier, every proof is
complete, and there is no `sorry` anywhere in `Condensation/`.**

That is a claim about the mathematics, not about the paper being *finished* here. The
consumer pass the repo standard requires before a paper may be registered `completed` has
since landed its two artifacts — [`API.lean`](API.lean), the documented consumer import,
and [`../APITests/Condensation.lean`](../APITests/Condensation.lean), the client-style
tests — but the human read-through of the frozen surface and the final fresh-context
adversarial audit have not run, so the registry still reads `in-progress`. See *Consumer
readiness* below for the per-criterion state. What is settled, with every number below taken from a
checker rather than maintained by hand:

* **Every in-scope node has a carrier.** `scripts/check-condensation-nodes.py` reports
  `79 citations, 39 distinct nodes, 42 numbered in the paper, 112 inventoried endpoints`,
  with per-section coverage **§2 5/5, §3 12/12, §4 15/15, §5 7/10**. The three nodes not
  cited are Examples 5.1–5.3, out of scope by the proposed ruling in *Open rulings* below,
  so 39/42 is complete coverage of the in-scope set rather than a shortfall.
* **Nothing is `sorry`.** `scripts/check_sorry_ledger.py` asks Lean itself, from the
  compiled environment, which Condensation declarations depend on `sorryAx`. Over 1004
  scanned declarations (512 user-facing, 492 compiler-generated) it reports
  `0 sorry-dependent declarations, all ledgered (0 main, 0 consumers)`. There is no `sorry`
  in a paper endpoint, none in a supporting lemma, and none in a consumer of either.
* **Every annotated endpoint is axiom-clean.** `AxiomAudit.lean`'s
  `CONDENSATION-INVENTORY` block asserts that each of its **112** listed declarations uses
  no axiom beyond `propext`, `Classical.choice`, `Quot.sound`, and the node checker
  enforces per-declaration coverage, so an annotated statement that is not listed there is
  a CI failure. That is all of §2 (Proposition 2.5 and its converse, the equation-(2.2)
  pullback identities, the two symmetries of interaction information), all of Definitions
  3.1–3.4, **all ten §3.1 endpoints** (Definitions 3.5, 3.6, 3.9, 3.10 and Propositions
  3.7, 3.8, 3.11, 3.12), **all fifteen §4 nodes** — Proposition 4.2's three inequalities,
  Definition 4.3, Lemma 4.5, Corollary 4.6, Proposition 4.7, Definition 4.8, **Theorem
  4.9** in both its (A1)–(A3) and (B1) ⟺ (B2) halves, **Proposition 4.10**, Definitions
  4.11 and 4.12 as structures, **Lemma 4.13 in full** (both `canonical` constructions and
  both existence statements, the (4.53) measure built explicitly), **Lemma 4.14** and
  **Theorem 4.15**, with Examples 4.1 and 4.4 as constructed models carrying their score
  equations — and **all seven in-scope §5 nodes**: Lemma 5.4 in both forms, Definition
  5.5's polar with its lattice facts, Definition 5.6 and Proposition 5.7 in full (the
  `M`-version, with the extension landing in the intersection-closed collection as the
  paper says), **Theorem 5.8 in both printed forms (5.13) and (5.14)**, Corollary 5.9's
  (5.21) and (5.22), and Corollary 5.10's (5.24) and (5.25).
* **The `CONDENSATION-PENDING` block is empty**, in both of its sections. It is retained as
  the standing mechanism — *The staged inventory* below says what it is for and how the
  checkers fence it — not because anything is staged in it.
* **No `axiom` declarations are introduced at any milestone**, and none is.
* **No modeling substitutions.** As of 2026-08-17 the model class is Definition 3.1
  verbatim — including the "with finite entropy" clause on `Ω`, which this library did not
  carry at all before that date — and the disclosures list in
  [`KNOWLEDGE.md`](KNOWLEDGE.md) is empty. The one standing narrowing, `dd:finite-range`,
  is retired; *Modeling boundary* below says what it was and what replaced it. The two
  restrictions that remain are universe stratification (presentational, open ruling 3) and
  the Examples 5.1–5.3 scope ruling. What is outstanding is no longer mathematical; it is
  the consumer pass, and it lives in *Consumer readiness* below.

### The `sorry` ledger, and why it now reports zero

`sorry` remains allowed and expected mid-flight under the repo standard (`../CLAUDE.md`,
load-bearing rule 3 — `sorry` is honest, an arithmetic stub standing in for content is
not), and this library used it throughout M1 and most of M2. It uses none now: the last
`sorry` in a supporting lemma went on 2026-08-17 (Lemma 4.13's three measure lemmas), and
the last `sorry` in a paper endpoint went at M2 on 2026-08-18.

**The gate stays armed, and it is what makes "zero" a checked claim rather than a promise.**
`scripts/check_sorry_ledger.py` runs one `lake env lean` elaboration against the built
oleans, enumerates every Condensation declaration that depends on `sorryAx`, and fails on
either direction of drift: a `sorry`-dependent declaration named in neither section of
`AxiomAudit.lean`'s `CONDENSATION-PENDING` block, or a ledger entry that no longer depends
on `sorryAx`. Both halves matter. The first is what was missing for the whole of M1, when
three un-annotated consumers of Proposition 4.2 sat outside every block and nothing noticed
(R2-F22); the second is what caught Lemma 4.13's carriers becoming clean, and what would
now catch a stale entry re-appearing in an empty block.

One distinction is worth carrying even at zero, because it caused real confusion while the
numbers were nonzero: `sorry` **sites** in the source and **declarations that are not
axiom-clean** are different counts, and they diverge whenever a fully-proved declaration
consumes a staged one. At their worst here the gap was 17 against 21. If either ever goes
nonzero again, say which one you mean.

The shared blocker of the §4 tranche is **built and spent**. Proposition 4.2's second
inequality, Proposition 4.10 and both halves of Theorem 4.9 all ran on one missing piece of
infrastructure — a chain rule for a *finite family* of variables along a linear order,
which the vendored library does not have (it stops at `chain_rule`, `chain_rule'`,
`chain_rule''`, `cond_chain_rule`, `cond_chain_rule'`) — plus the two linear extensions the
paper's proofs choose, which come from `Mathlib.Order.Extension.Linear`
(`extend_partialOrder`), not in the substrate's import closure and imported explicitly by
`Model.lean` for that reason. All of it now lives in
[`ChainRule.lean`](ChainRule.lean), stated over a bare `RVModel J` and carrying no paper
node, and the four endpoints unblocked together as predicted. §5 consumes the same file.

### Milestones

What each milestone gates, from [`notes/roadmap.md`](notes/roadmap.md):

| milestone | what it delivers | what it gates |
|---|---|---|
| **M0** (harness round 1) | `Probability.lean` (§2) and `Model.lean` (Defs 3.1–3.4) complete *statements*, definitions total, theorem bodies may be `sorry`; `Examples.lean` inhabitants for `RVModel` and `LatentModel`; wiring — `lean_lib Condensation`, a `scripts/papers.py` entry marked `in-progress`, `scripts/check-condensation-nodes.py`, the CI branch, the `CONDENSATION-INVENTORY` block in `AxiomAudit.lean`, this README, `KNOWLEDGE.md` | audit round 1 attacks **the core definitions only**. A wrong `RVModel` or `LatentModel` invalidates everything built on it, so it is audited before anything is built on it. **Landed**, with no `sorry` at all. |
| **M1** (round 2) | statements for §3.1, §4 and §5 in full (proofs may still be `sorry`); Examples 4.1 and 4.4 constructed | audit round 2 attacks **the theorem statements**. **Landed** — the statements are final and were what round 2 attacked; the proofs behind them were what "proofs may still be `sorry`" bought, and they are all discharged at M2. |
| **M2** | proofs: Props 4.2, 4.10, Thm 4.9 (the chain-rule tranche, whose shared machinery landed as [`ChainRule.lean`](ChainRule.lean)); Lemma 4.13 (the measure construction); Lemma 4.14 and Thm 4.15; Thm 5.8, Cors 5.9–5.10; equations (4.2)–(4.5) and (4.11) of the examples | the point at which the paper's §4 and §5 theorems are claimed *proved*. **Landed 2026-08-18**: all of them are proved, `Condensation/` contains no `sorry`, and the `CONDENSATION-PENDING` block is empty in both sections. |

Two corrections to that table as it stood when it was written. Proposition 2.5 was
scheduled for M2 and is in fact **proved at M0** — the determinism bridge turned out to be
the natural place to start, since §4 consumes it in both directions. And Propositions 4.5
and 4.7 were listed as M2 work; Lemma 4.5 and Proposition 4.7 are both **proved at M1**,
as are Proposition 4.2's first and third inequalities, Lemma 5.4, Proposition 5.7 and
Corollary 5.10's (5.24).

The roadmap's milestones end at M2, and M2 is the end of the *proof* work. It is not the
end of the paper: the repo standard adds a consumer pass, a human read-through and a final
fresh-context audit before a paper may be registered `completed`. Those are enumerated
under *Consumer readiness* below.

## Consumer readiness

**This paper is registered `in-progress` in `scripts/papers.py`, and stays there until the
list below is discharged.** The proofs being finished is necessary and not sufficient; the
repo standard (`../CLAUDE.md`,
*Consumer readiness is part of paper completion*) is explicit that "a paper is not finished
merely because its statements are proved, inventoried, and audited," and requires all of
the following, as applicable, before the registry status may change:

> 1. faithful paper coverage;
> 2. explicit provenance and trust-surface accounting;
> 3. axiom cleanliness and disclosed trust boundaries;
> 4. one documented, recommended consumer import exposing a coherent, intentionally small
>    API, with deeper construction imports identified separately;
> 5. client-style smoke tests which import only that API and use its objects, rewriting,
>    transport, and composition to prove useful facts beyond restating paper endpoints.

Where each stands:

| criterion | state |
|---|---|
| 1. faithful paper coverage | **met, conditionally.** Every in-scope node is carried and proved (39/42, the three exclusions being Examples 5.1–5.3). The condition is that the exclusion is still a *proposed* ruling — open ruling 2 — not a settled one. |
| 2. provenance and trust-surface accounting | **met.** This file, [`KNOWLEDGE.md`](KNOWLEDGE.md), [`notes/paper-errata.md`](notes/paper-errata.md), the `Paper node:` annotation contract checked fail-closed including node *kind*, and per-declaration coverage in `AxiomAudit.lean`. |
| 3. axiom cleanliness and disclosed trust boundaries | **met.** Zero `sorry`, 112 endpoints axiom-clean, an empty pending block, no `axiom` declarations, no modeling substitutions, and the two remaining restrictions (universe stratification, the Examples 5.1–5.3 scope ruling) disclosed above and in `KNOWLEDGE.md`. Universe stratification is open ruling 3. |
| 4. a documented consumer import | **met.** [`API.lean`](API.lean) is the recommended entrypoint, registered as this paper's `api` key. It imports the whole paper surface and documents it as an interface: vocabulary section by section, the `ShannonInformation.API` substrate rules, the errata a client should know, and — the part that answers the question this row used to leave open — which declarations are paper endpoints as against conveniences, by cataloguing `AxiomAudit.lean`'s **three** Condensation blocks and saying what each is actually for (the `Paper node:` docstring line, not block membership, is what marks an endpoint). The rulings it settles: the §3.1 category machinery, the amalgamation constructions and `ChainRule.lean`'s substrate are all **on** the boundary (a client doing quantitative work with joint variables needs the chain-rule layer, and neither Mathlib nor the vendored PFR snapshot has it), and so is `Examples.lean` — unlike `FiniteFactoredSets/Examples.lean`, it is not a fixture file: it carries Examples 4.1 and 4.4 as *paper nodes stated over an arbitrary model*, together with `LatentModel.ofJoint`/`nonempty`, which is the first latent model a client can reach for. The genuinely fixture-shaped witnesses come along with it in the same file and are documented as regression fixtures rather than a dependency surface. |
| 5. client-style smoke tests | **met.** [`../APITests/Condensation.lean`](../APITests/Condensation.lean) imports only `Condensation.API` and builds a client model from scratch (`Ω = Bool × Bool` uniform, `I = Bool`, the two coordinates as observables — not one of `Examples.lean`'s fixtures), a latent model over it, computes both scores by rewriting through `famFinset`/`contrib`, and then composes endpoints: Proposition 2.5 with `AEFunctionOf.trans`, Proposition 4.2's chain, Theorem 4.9 into `OrderedMarkov`, `LatentAmalgamation.diagonal` into Theorem 4.15, Theorem 5.8 at a one-leaf tree, a `Hom` composition with `Hom.isIso_iff`, and the chain-rule layer's `iIndepFun_of_entropy_jointOn_eq_sum` to certify that the client's two observables are independent. It is collected in `APITests.lean` and so builds by default. |

`scripts/papers.py` now carries both the `api` and the `api_test` key for this paper, so
`scripts/check_paper_wiring.py` checks those two artifacts and their collection in
`APITests.lean` rather than merely permitting their absence. The status stays
`in-progress` regardless: the gate "makes these artifacts and their default CI build
mandatory for every `completed` paper," and it arms the rest of itself the moment the
status changes — as does the node checker's rule that a non-empty `CONDENSATION-PENDING`
block is a **violation**, not a note, once the registry says `completed`.

One honest qualification on criterion 4, since the standard's wording is "an intentionally
*small* API". `Condensation/API.lean` imports all nine modules of the library, so it is not
small in module count, and there is no "deeper construction import" held back behind it.
That is a fact about this library rather than a dodge: eight of the nine files carry paper
nodes, so there is no module that could be excluded without dropping part of the paper, and
the ninth (`ChainRule.lean`) is machinery a quantitative client demonstrably needs and
cannot get from Mathlib or the vendored PFR snapshot — `APITests/Condensation.lean` uses it
to certify that a client's own observables are independent. The curation is therefore in
*what is documented as supported*, not in a narrower import: the API docstring separates
paper endpoints from conveniences by cataloguing `AxiomAudit.lean`'s three Condensation
blocks — the `CONDENSATION-INVENTORY` axiom gate, the pure-comment `CONDENSATION-PENDING`
staging block, and the marker-less `## Consumer API conveniences` block where the plumbing
and the constructed witnesses are asserted clean — and marks
`Examples.lean`'s fixture-shaped witnesses as regression fixtures rather than a dependency
surface. If the read-through disagrees, the fix is to split `Examples.lean` along the line
the docstring already draws.

**Criteria 4 and 5 being met does not make the paper complete.** Two further steps sit
outside that list and are outstanding, in the order the root `../CLAUDE.md` fixes; neither
is a formality:

* **the human read-through.** "Anson reads every top-level **statement** and every
  **definition** before the work is called done," and the sequencing note is that it runs
  "**once, over the consolidated frozen surface** — not per-milestone," after the
  consolidation / API pass, with the surface re-freezing before it. It has not run.
* **a final fresh-context adversarial audit, last** — hunting specifically for vacuous
  theorems, conclusion-in-hypothesis squeezes, oversold stubs, type-`(c)` substitutions,
  degenerate non-vacuity and off-loaded steps. The audit rounds so far were mid-flight
  rounds against statements and proofs, not this one.

Consolidation discipline applies to the surface those two steps run over: the end state
"must show **no structural evidence of previous versions**," and layered scaffolding is
"acceptable *mid-flight* to keep the build green, but it is technical debt with a scheduled
demolition, not an end state." Nothing here should be read as claiming that pass is done.

## Modeling boundary

### `dd:finite-range` — retired 2026-08-17

**Definition 3.1 is now carried verbatim, and there is no modeling substitution left in
this library.** A random variable model is a countable discrete probability space *with
finite entropy* (`[Countable Ω] [MeasurableSingletonClass Ω] [IsProbabilityMeasure P]`
plus the field `finiteEntropy_Ω : ShannonInformation.FiniteEntropyMeasure P`) together
with a finite family of variables of countable discrete range and finite entropy
(`finiteEntropy_X : ∀ i, ShannonInformation.FiniteEntropyOf (X i) P`).

**What the state was, and when it changed.** Until 2026-08-17 every variable of a model
carried `FiniteRange` (finitely many *attained* values) and `Ω` carried no entropy
hypothesis at all. That was a genuine type-(c) narrowing — a geometric variable on `ℕ` is
countable-discrete with finite entropy and was excluded — and it was forced, because the
vendored PFR theorems are proved only in the finite-range fragment. It was disclosed here,
in `KNOWLEDGE.md`, in the roadmap, and at every model structure. It was costed on
2026-08-17 (`notes/finite-range-generalization-plan.md`: ~1,450–2,400 lines, 3–4.5 focused
weeks in four phases), ruled a desired endpoint by Anson the same day rather than deferred,
and retired the same day.

**What replaced it.** A FAF-authored finite-entropy layer, `ShannonInformation/FiniteEntropy/`,
proving the §2–§5 corpus this paper consumes — the chain rules, subadditivity, mutual- and
conditional-mutual-information nonnegativity, the independence characterizations, data
processing — at `ShannonInformation.FiniteEntropyOf` rather than `FiniteRange`. The consumer
migration then swapped `RVModel`'s finiteness field, added Definition 3.1's `Ω` clause, and
rebound the §2 substrate lemmas and the bare-variable lemmas of §5's Lemma 5.4 and §4's
Lemma 4.14. **No statement of any §3–§5 theorem changed, and the `sorry` count was
unchanged at twenty** (it fell to seventeen later the same day, when the round-2 fix wave
discharged Lemma 4.13's three measure lemmas — unrelated to the generalization). The one node whose *shape* changed is Proposition 2.5, which gained `Countable
R_Y` at the same time it lost `FiniteRange` (its `omit [Countable T] in` is gone, forced by
the `tsum` form of conditional entropy). Before, it was stronger than printed in one respect
and weaker in another, so it was not comparable as printed; now it is the printed statement.
The [`KNOWLEDGE.md`](KNOWLEDGE.md) correspondence table records this per declaration.

**The class genuinely grew, and there is a witness for it.** `Condensation.Example.geomModel`
is an `RVModel Unit` on `Ω = ℕ` with the `Geometric(1/2)` law and `X_() = id`, with
`geomModel_entropy : H(X_()) = 2 log 2` and `geomModel_not_finiteRange : ¬ FiniteRange
(geomModel.X ())`. It is a random variable model of this library today and was not
expressible before the swap; every other witness in `Examples.lean` lives on a finite sample
space and so cannot distinguish Definition 3.1's reading from the narrowed one. Per the
repo's non-vacuity discipline it is constructed, not asserted.

**Every §5 statement quantifies over a `LatentAmalgamation`, and there is a constructed
witness for that too.** Theorem 4.15, Theorem 5.8 and both corollaries are stated about an
arbitrary `Am : LatentAmalgamation L₁ L₂`, so an uninhabited `LatentAmalgamation` would
make all of §5 vacuous. Until round 2 the only inhabitant was Lemma 4.13's
`LatentAmalgamation.canonical`, which was `sorry`-dependent — so nothing axiom-clean
witnessed the hypothesis (R2-F19). `Condensation.LatentAmalgamation.diagonal` now does:
it amalgamates a latent variable model with *itself* along the identity (`Λ₀ = L.Λ`,
`ρ₁ = ρ₂ = id`), which satisfies Definition 4.12 on the nose. Lemma 4.13 has since been
proved as well, so both routes are available; `diagonal` is the one that does not depend
on it.

### The `dd:` design decisions

Mirrors the table in [`notes/roadmap.md`](notes/roadmap.md); the same glossary ships in
`Condensation.lean`, and each decision is tagged at its site.

| Tag | Decision | Why |
|---|---|---|
| `dd:finite-range` | **Retired 2026-08-17.** It read: every random variable of a model carries `FiniteRange`, and `Ω` carries no entropy hypothesis. It now reads: `finiteEntropy_Ω : ShannonInformation.FiniteEntropyMeasure P` and `finiteEntropy_X : ∀ i, ShannonInformation.FiniteEntropyOf (X i) P` — Definition 3.1 verbatim. The tag is kept in the glossary, marked retired, because older commits, the audit ledger and `notes/finite-range-generalization-plan.md` refer to it by name. | **See the callout above** for what the state was, what replaced it, and the witness (`Example.geomModel`) that shows the model class genuinely grew. No longer a narrowing, and no longer an open ruling. |
| `dd:pplus` | `P⁺I` is the subtype `PPlus I := {A : Finset I // A.Nonempty}`. Finiteness of the index type is carried by the model — `RVModel` takes `[Finite I]` as a class parameter (Def 3.1: *finite* family) — so no `Fintype`/`DecidableEq` data appears anywhere and `PPlus I` is exactly the paper's `P⁺I`. Subfamilies `F ⊆ P⁺I` are `Set (PPlus I)` (finite automatically), and the joint variable `Y_F` is `fun ω (B : F) => Y B ω`, a dependent product over the subtype `↥F` with `MeasurableSpace.pi`. | Faithful to Def 2.2 (nonempty subsets only, no phantom `Y_∅`); `Set` keeps upward-closure/polar/intersection algebra (§4.10, §5) as plain set algebra; finiteness of `↥F` is by instance. |
| `dd:bundled-model` | `RVModel (I : Type w) [Finite I]` bundles the sample space `Ω : Type u`, its σ-algebra/countability/singleton-class instances, the probability measure, the range family `R : I → Type v` with their instances, the variables `X i : Ω → R i`, their measurability and their finite entropy, plus Def 3.1's finite entropy of `Ω` itself; Def 3.1's *finite* family is the class parameter `[Finite I]`, not a field, so instance search finds it. `LatentModel M` bundles a `RVModel.{u', v', w} (PPlus I)` plus `π : Λ → Ω` (`MeasurePreserving`) plus the a.e.-function condition of Def 3.2, with the latent universes `u'`/`v'` **independent** of `M`'s. | Def 3.5–3.12 need models as objects of a category, and 3.2/4.12 need "two latent models with the same underlying space" — bundling with explicit `Ω`/`R` fields is what makes those statable. **`RVModel`'s `Type u`/`Type v` stratification is a disclosed narrowing** — see below. |
| `dd:ae-function` | "`Y` is a function of `X` almost everywhere" is `AEFunctionOf X Y P := ∃ f, Measurable f ∧ ∀ᵐ ω ∂P, Y ω = f (X ω)`; the everywhere version `FunctionOf` likewise without `∀ᵐ`. Measurability of `f` is kept in the definition (paper: "measurable function") and discharged by `measurable_of_countable` on countable discrete ranges. | Verbatim Def 2.1's fifth convention; the measurability conjunct is free in our setting but keeping it stops the definition drifting from the paper. |
| `dd:pullback` | Pullback `π^* X` is plain composition `X ∘ π`; probability-preserving = Mathlib `MeasureTheory.MeasurePreserving π P_Λ P_Ω`. Equation (2.2) invariance is `IdentDistrib`-based (`MeasurePreserving` gives `IdentDistrib (X ∘ π) X`). | Repo rule: never redefine what Mathlib has. |
| `dd:interaction` | Def 2.3's `I(X;Y;Z) := I[X : Y] − I[X : Y \| Z]` and its conditional form `I(X;Y;Z \| C) := I[X : Y \| C] − I[X : Y \| ⟨Z, C⟩]` (needed by Lemma 5.4 / Thm 5.8) are FAF-authored `def`s over the vendored `mutualInfo`/`condMutualInfo`; symmetry is a lemma. | The API deliberately adds no definitions; interaction information is paper-specific until a second client needs it. |
| `dd:tree` | Def 5.6's intersection tree is an inductive binary tree `ITree (M) := leaf (a : M) \| node (l r : ITree M)` with the label of a node *computed* as the meet of its children's labels; Prop 5.7 is stated as: any labeling of the tree's positions that agrees on leaves and satisfies (5.10) at every internal position equals the computed labeling. Leaves/internal vertices are lists of positions; Thm 5.8's "bijection between leaves and `{C : B∩C≠∅}_{B∈F}`" is the **multiset** equation `(T.leaves : Multiset _) = (famFinset F).val.map (fun B => contrib B.toFinset)` — leaf labels *with multiplicity* — and it is a bijection rather than a surjection because `contrib_injective` makes the right-hand multiset duplicate-free. (It is **not** `List.Nodup` + `toFinset = image`; that phrasing stood here until 2026-08-18 and never matched the Lean.) | A directed rooted binary tree with unique paths to the root *is* an inductive binary tree; the (V,E,ℓ) presentation would import graph theory for no content. **One disclosed reading rides on this (R4-F02, 2026-08-18):** `ITree` is inductive, so it reads Def 5.6 as ranging over **finite** trees, and Def 5.6 as printed carries no finiteness or well-foundedness clause — its condition (1) constrains directed paths *to* the root, which an upward-infinite leafless tree satisfies (errata 17). The reading is licensed by Thm 5.8, whose (5.14) is a finite sum over the tree's leaves and internal vertices and so has content only for a finite tree. This is a rendering plus a disclosed reading, not a modeling substitution; auditors should attack it if any §5 statement loses generality. |
| `dd:category` | Prop 3.7 is a `CategoryTheory.Category` instance on the bundled type of random variable models (objects `Σ I, RVModel I` at fixed universes); Prop 3.8 uses `CategoryTheory.IsIso`; Def 3.9's a.e.-equality is a relation on hom-types (a `Setoid`), 3.10–3.12 are stated over it. No `Bicategory`. | Follows the paper, which names the 2-category and declines to use it. |
| `dd:amalgamation` | Def 4.11's Λ₀ is the subtype `{p : Λ₁ × Λ₂ // π₁ p.1 = π₂ p.2}` with the discrete σ-algebra and the measure `∑' p, w p • dirac p`, `w (λ₁,λ₂) = P₁{λ₁} P₂{λ₂} / P_Ω{π₁ λ₁}` (0 when the denominator is 0) — the paper's (4.53) integral evaluated on a countable discrete space. | Same object; the sum form is what a countable-discrete Λ₀ means. |

### Universe stratification (`dd:bundled-model`), a second disclosed narrowing

`RVModel` fixes its sample space in `Type u` and its range family in `Type v`, and the
category instance of `dd:category` is taken at fixed universes. The paper quantifies over
probability spaces with no such stratification. Universe *lifting* can represent larger
presentations, so this is presentational rather than a cardinality bound — but it is a
restriction, it is the price of bundling models into objects of a category, and it is
recorded here and in [`KNOWLEDGE.md`](KNOWLEDGE.md) rather than left to be discovered in a
signature. It is likewise an **open ruling** (below).

**A latent model's universes are not pinned to its model's.** An earlier draft of
`LatentModel` required `Λ : Type u` and the latent ranges in `Type v` — the same universes
as `M` — and described that as a documented narrowing. It has been removed: the full
parameter list is `LatentModel.{u, v, w, u', v'}`, with `Λ : Type u'` and the latent ranges
in `Type v'`, unrelated to `M`'s. Nothing in the paper ties them, and the pin cost real
generality: Example 4.4 builds `M` out of `L` by setting `X_i := Y_∋i`, which puts the
*given* ranges in `Type (max v' w)` while the latents stay in `Type v'`, so under the pin
that example was statable only for pre-inflated latent universes. Unpinning costs an
explicit universe list at *existence* statements (`Nonempty (LatentModel.{u,v,w,u,v} M)`)
and nothing at all at the statement shape every §4/§5 theorem uses
(`{I} [Finite I] {M : RVModel I} (L : LatentModel M) …`); `Nonempty (RVModel.{u,v,w} I)`
already needed the same annotation, so this is not a new kind of friction.

### Bundled model vs. bare variables: a documented generality choice, not drift

Raised as R4-F21 and recorded because an auditor comparing §4's statements side by side will
notice the asymmetry and should not read it as inconsistency.

**Definition 4.8 and Proposition 4.10 are stated over `RVModel (PPlus I)`** — a bundled
model, indexed by the nonempty subsets — so they inherit §2's blanket convention wholesale:
countable discrete sample space of finite entropy, countable discrete ranges. They carry
**no** local finiteness or discreteness hypothesis at all, because finiteness reaches them
through Definition 3.1's `finiteEntropy_Ω` field and `RVModel.finiteEntropyOf`.

**Lemma 4.14 and Lemma 5.4 are stated over bare random variables** with explicit binders
(`Condensation.aeFunctionOf_of_condIndepFun`, `Condensation.condEntropy_le_of_pair` /
`.condEntropy_eq_of_pair`), because the paper states them that way and because they are
substrate lemmas with clients that have no model in hand.

The cost is that the two halves of §4 are not comparable binder-for-binder; the benefit is
that neither is weaker than the paper's own statement. A bare-family restatement of
Definition 4.8 and Proposition 4.10 — over `(Y : PPlus I → Ω → R _)` with explicit
finite-entropy binders — would be strictly more general and is a **possible follow-up**, not
a defect: nothing in §4 or §5 needs it, since every consumer already has a model. The wrong
way to remove the asymmetry is to add hypotheses to the model-side statements, which would
narrow them below the paper.

## Scope

The paper numbers **42 nodes** on a single section-scoped counter shared across kinds,
running `Definition 2.1` … `Corollary 5.10`. By kind:

| kind | count | which |
|---|---|---|
| Definitions | 18 | 2.1, 2.2, 2.3, 2.4; 3.1–3.6, 3.9, 3.10; 4.3, 4.8, 4.11, 4.12; 5.5, 5.6 |
| Propositions | 9 | 2.5, 3.7, 3.8, 3.11, 3.12, 4.2, 4.7, 4.10, 5.7 |
| Lemmas | 4 | 4.5, 4.13, 4.14, 5.4 |
| Theorems | 3 | 4.9, 4.15, 5.8 |
| Corollaries | 3 | 4.6, 5.9, 5.10 |
| Examples | 5 | 4.1, 4.4, 5.1, 5.2, 5.3 |

18 + 9 + 4 + 3 + 3 + 5 = 42. This breakdown is not stated in the paper's own prose; it was
derived from the committed extraction. `scripts/check-condensation-nodes.py` hard-asserts
both the total of 42 **and each of the six per-kind counts** in that table, so a drift in
the extraction is a CI failure rather than a silent narrowing of the node set.

Per section, with the in-scope ruling — reproduced from
[`notes/roadmap.md`](notes/roadmap.md):

| § | Nodes | In scope? |
|---|---|---|
| 2 | Def 2.1 (random variable), 2.2 (`P⁺S`), 2.3 (`H`, `I`, interaction information), 2.4 (`G(Ω)`), Prop 2.5 (determinism bridge) | yes; 2.1 and 2.4 Mathlib-rendered (`Measurable`, `Measure.instMeasurableSpace`) with `Paper node:` on the alias/`abbrev` that names them |
| 3 | Def 3.1 (random variable model), 3.2 (latent variable model), 3.3 (scores σ, χ, ϱ), 3.4 (joint variables `X_A`, `Y_F`, `Y_∩A`, `Y_⊇A`, `Y_⊋A`, `Y_∋i`), 3.5 (morphism), 3.6 (composite), Prop 3.7 (category), 3.8 (iso characterization), Def 3.9 (a.e.-equal morphisms), 3.10 (equivalence), Prop 3.11 (congruence), 3.12 (equivalence is an equivalence relation) | yes, all |
| 4 | Ex 4.1, Prop 4.2, Def 4.3, Ex 4.4, Lemma 4.5, Cor 4.6, Prop 4.7, Def 4.8, Thm 4.9, Prop 4.10, Def 4.11, 4.12, Lemma 4.13, 4.14, Thm 4.15 | yes, all (examples 4.1/4.4 are constructive and double as non-vacuity witnesses — and since 2026-08-18 Example 4.4 is instantiated at a concrete family, `Example44.L44_coin_simplyPerfectlyCondenses`, so its joint-independence hypothesis is discharged rather than merely assumed) |
| 5 | Ex 5.1, 5.2, 5.3, Lemma 5.4, Def 5.5 (polar), 5.6 (intersection tree), Prop 5.7, Thm 5.8, Cor 5.9, 5.10 | 5.4–5.10 yes. **Ex 5.1–5.3 proposed OUT** (pending Anson's ruling): 5.1/5.2 posit `[0,1]`-valued latents `L`, outside the paper's own countable-discrete framework and only bucketed into it informally; 5.3 is a prose translation of structural causal models with no claim. Nothing downstream cites them. |

Everything else in the paper — equation (3.4)'s score aggregation, the 2-category remark
after Def 3.10, the (4.41) discussion — is unnumbered prose and gets no carrier.

### Open rulings

Two questions are open for Anson, and one is closed. Work proceeds under the stated
assumption in each open case; **neither of those is a settled ruling, and this file does
not present either as one.** If a ruling comes back the other way, the affected work is
redone.

1. ~~**`dd:finite-range`** as the standing type-(c) narrowing~~ — **CLOSED, 2026-08-17.**
   It was assumed yes; Anson ruled the other way, that the generalization was a desired
   endpoint to be pursued in parallel with the paper rather than deferred, and it landed
   the same day. `Condensation/` now carries Definition 3.1 verbatim. See the callout
   under *Modeling boundary*. Nothing here is waiting on this question.
2. **Examples 5.1–5.3 out of scope** — *assumed yes*, for the reason in the §5 row above:
   5.1 and 5.2 posit `[0,1]`-valued latents, outside the paper's own countable-discrete
   framework and only bucketed into it informally, and 5.3 is a prose translation of
   structural causal models with no claim. They are the only nodes proposed for exclusion,
   and nothing downstream cites them.
3. **Universe stratification** of `RVModel` (`Ω : Type u`, `R : I → Type v`) — *assumed
   acceptable* as a documented narrowing. The distinct question of whether a latent model
   must live in its model's universes is **not** open: it does not, as of the round-1 fix
   wave (see the callout above).

## File layout

Reproduced from [`notes/roadmap.md`](notes/roadmap.md). All of these files exist and are
complete as of M2; `ChainRule.lean` is the one added after M1, carved out of the §4 proofs
that share it. The import order is also the dependency order; two edges are worth naming because they were
settled by construction rather than by plan. `Perfect.lean` imports `Morphism.lean`, because
Proposition 4.7's clause (2) *is* Definition 3.10 — so §3.1 sits upstream of §4, not beside
it. And `Examples.lean` imports `Perfect.lean`, so the §3.1 witnesses (the concrete
morphisms, the category objects, the a.e.-equal-but-different-`f` pair) live at the end of
`Examples.lean`; putting them in `Morphism.lean` would close the cycle
`Morphism → Examples → Perfect → Morphism`.

| file | content | status |
|---|---|---|
| `Probability.lean` | §2: `AEFunctionOf`/`FunctionOf`, pullback lemmas (2.2), `PPlus`, interaction information, Def 2.4 alias, **Prop 2.5** (`H[Y \| X] = 0 → AEFunctionOf X Y`) — proved over the vendored entropy, not the spike's | complete, no `sorry` |
| `Model.lean` | Def 3.1–3.4: `RVModel`, `LatentModel`, joint variables, the four `Y_∩A`/`Y_⊇A`/`Y_⊋A`/`Y_∋i` families plus `incomparable`, (3.9), scores σ/χ/ϱ, and the generic joint-variable / upward-closure lemmas §4 and §5 run on | complete, no `sorry` |
| `ChainRule.lean` | the chain rule `H(Y_F) = ∑_{A ∈ F} H(Y_A \| (Y_C)_{C ≺ A})` for a finite family along a linear order, Szpilrajn for *strict* orders and the two orders §4's proofs choose, the "drop the coordinates already given" identities, and the two-way bridge between joint independence / Definition 4.8's conditional independence and the termwise entropy equalities. Stated over a bare `RVModel J`; **no paper node** | complete, no `sorry` — added at M2 |
| `Morphism.lean` | §3.1: Def 3.5, 3.6, Prop 3.7, 3.8, Def 3.9, 3.10, Prop 3.11, 3.12 | complete, no `sorry` — all ten endpoints axiom-clean |
| `Perfect.lean` | §4: Prop 4.2, Def 4.3, Lemma 4.5, Cor 4.6, Prop 4.7, Def 4.8, **Thm 4.9**, Prop 4.10 | complete, no `sorry` — the chain-rule tranche landed at M2 |
| `Amalgamation.lean` | Def 4.11, 4.12, **Lemma 4.13** (the measure construction), and `LatentAmalgamation.diagonal` | complete, no `sorry` — Lemma 4.13's three measure lemmas landed 2026-08-17 |
| `Comparison.lean` | Lemma 4.14, **Thm 4.15** | complete, no `sorry` — Lemma 4.14 carries the corrected binder of errata 15, and Thm 4.15's induction (absent from the paper, errata 5) is supplied |
| `Quantitative.lean` | Lemma 5.4, Def 5.5, 5.6, Prop 5.7 (the `M`-version), **Thm 5.8**, Cor 5.9, 5.10 | complete, no `sorry` |
| `Examples.lean` | Ex 4.1, 4.4, inhabitants of every boundary structure, `LatentModel.nonempty`, and the §3.1 witnesses | complete, no `sorry` — the score equations (4.2)–(4.5), (4.11) and Ex 4.4's conclusion landed at M2 |
| `Condensation.lean` | aggregator + `dd:` glossary | imports all nine |
| `README.md`, `KNOWLEDGE.md`, `notes/paper-errata.md` | trust surface, institutional memory, errata | all three exist |

## Substrate: `ShannonInformation.API`

This library's entropy, conditional entropy, mutual information and conditional mutual
information all come from **one import**, `ShannonInformation.API` — FAF's shared,
paper-neutral Shannon layer, which is a vendored snapshot of the
[PFR project](https://github.com/teorth/pfr)'s information theory. Read
[`../ShannonInformation/README.md`](../ShannonInformation/README.md) and, before relying
on any entropy statement, [`../ShannonInformation/SCOPE.md`](../ShannonInformation/SCOPE.md).

Two standing rules, both inherited from that layer:

1. **Never name a `PFR.*` module from a Condensation file.** The vendor/consumer split
   exists so that re-pinning the vendored tree — a routine maintenance event — does not
   ripple into paper libraries. Go through `ShannonInformation.API`.
2. **Never `import Mathlib` wholesale in a Condensation file.** PFR's `Mathlib/` shim
   modules re-declare lemmas that FAF's newer Mathlib pin has since acquired upstream, and
   a file that imports all of Mathlib alongside this layer fails to elaborate
   (`import PFR.Mathlib.Probability.IdentDistrib failed, environment already contains
   'ProbabilityTheory.IdentDistrib.prodMk'`). Import the specific `Mathlib.*` modules you
   need.

And a third rule, new since 2026-08-17 and the one most likely to bite: **cite
`ShannonInformation.foo` by its full name, never bare.** The *vendored* theorems still hold
only in the finite-range fragment — the chain rules, `mutualInfo_nonneg`, the independence
characterizations, submodularity, data processing all carry a `FiniteRange` hypothesis that
is load-bearing in PFR's proof, not a typeclass artefact, and `SCOPE.md` §2 still records
that this is strictly narrower than countable-discrete-with-finite-entropy. What changed is
that this library no longer cites them for anything load-bearing. It cites the FAF-authored
`ShannonInformation.*` corpus in `ShannonInformation/FiniteEntropy/`, which proves the same
facts at `ShannonInformation.FiniteEntropyOf`. Both versions are reachable through the one
import, and with `ProbabilityTheory` open a bare lemma name resolves by elaboration success
rather than by namespace — so a bare citation can silently pick the narrow one and fail
several lines later with a missing `FiniteRange` instance. `ShannonInformation/API.lean`'s
module docstring carries the "which version to cite" table. Dot notation is the sharp case,
because opening a namespace cannot fix it: `h.condEntropy_eq_entropy` and
`hid.condEntropy_eq` resolve in the head symbol's namespace (`ProbabilityTheory.IndepFun`,
`ProbabilityTheory.IdentDistrib`) and so always find the vendored original. Write those two
out in full.

**No `FiniteRange` citation remains anywhere in `Condensation/`,** including the concrete
witnesses. The reason is worth knowing, because the obvious guess is wrong: one might expect
a witness built on `Bool × Bool` to keep citing the vendored lemmas, the range being finite.
It cannot. With `RVModel`'s finiteness field now `FiniteEntropyOf` there is no structure
instance for `FiniteRange (M.X i)`, and instance search will not unfold a concrete model to
rediscover that its range type happens to be a `Fintype`. `FiniteRange` survives in
`Condensation/` in exactly one statement, `Example.geomModel_not_finiteRange`, where it is
negated. A citation anywhere else is a finding.

`SCOPE.md` also flags a trap worth carrying while reading any statement here, and it is now
live rather than hypothetical: Lean's `∑'` is `0` on a non-summable family, so `H[X]` for an
infinite-entropy variable is silently `0` rather than `∞`, and `condEntropy` is a Bochner
integral, silently `0` when non-integrable. Under the old narrowing neither could bite. What
keeps them from biting now is that the finiteness class carries both as *proved consequences*
(`ShannonInformation.FiniteEntropyOf.summable`, `ShannonInformation.integrable_entropy_cond`)
rather than as side hypotheses on statements.

## Numbering and provenance

The paper numbers through a **single section-scoped LaTeX theorem counter shared by
`Definition`, `Proposition`, `Lemma`, `Theorem`, `Corollary` and `Example`**, so a node id
reads `<section>.<n>` — `Definition 3.4`, `Lemma 4.13`, `Theorem 5.8` — and the kinds
interleave in one sequence. No LaTeX labels are available to us, so the **printed number is
the provenance key**, as in `CartesianFrames/`, `ModalAgents/` and `FiniteFactoredSets/`.

**We have no TeX source.** That is the difference from every other paper here, and it
changes the shape of the checker. `scripts/check-modal-agents-nodes.py` and
`scripts/check-finite-factored-sets-nodes.py` *recompute* their papers' printed numbers by
emulating the LaTeX counters, so the node set is derived rather than transcribed. We cannot
do that. The committed *source* our checker reads is
[`notes/condensation-25-07.txt`](notes/condensation-25-07.txt), the `pdftotext -layout`
extraction of the committed PDF, and `scripts/check-condensation-nodes.py` reads the
**printed numbers directly off that extraction's header lines**. Because an extraction can
drift — a re-run under a different `poppler`, a reflowed header, a lost line break — the
checker **hard-asserts that exactly 42 nodes are found, with the per-kind counts of the
table above**. A drift that silently dropped a node would otherwise narrow the node set
without failing anything; instead it fails CI.

One quirk of the extraction to know before reading it or the checker: **`pdftotext` drops
the `fi` and `ff` ligatures**, so the committed text reads `Denition`, `nite`, `dierent`,
`sucient`. The header regex (in `scripts/paper_nodes.py`) therefore reads
`De(?:fi)?.?nition`, accepting the extraction's spelling and the plain one alike, rather
than `Definition`. This is a *tool* artifact and never a defect of the paper — do
not log one as an erratum. It has a sharp consequence for anyone writing code against the
extraction: what the extractor actually emits in place of a dropped ligature is the font's
own slot byte, `\x1c` for `fi`, and Python's `str.splitlines()` splits on `\x1c`/`\x1d`/`\x1e`
— so `splitlines()` over this file makes every `Definition` header disappear. Split on
`\n`.

The annotation contract is the repo's standard one, enforced fail-closed:

* every paper-facing `theorem` carries a final `Paper node:` docstring line naming the
  printed node;
* validity is checked **including the kind** — citing `Theorem 2.5` where the paper prints
  `Proposition 2.5` is a failure, and a line that parses to *no* node is itself a
  violation, so a typo cannot silently disable the check;
* the annotation must be the last line of a `/-- … -/` docstring on a **named**
  declaration (anonymous instances therefore cannot carry one; internal lemmas cite the
  paper in prose instead);
* **coverage, per declaration**: every annotated declaration is itself listed in
  `AxiomAudit.lean`'s `CONDENSATION-INVENTORY` block, matched on fully qualified names.
  Sharing a node with some other listed declaration is not enough — the annotation claims
  the node for *that* statement, so *that* statement is what gets axiom-checked. One
  in-progress concession, and it expires on its own: while *nothing* is annotated yet, an
  absent `CONDENSATION-INVENTORY` block is reported as a note rather than a failure, since
  there is no endpoint for it to protect. The block becomes mandatory with the first
  annotated declaration.

### The staged inventory (`CONDENSATION-PENDING`)

The coverage rule above collides with reaching the paper statement-first. Some
declarations carry a paper-node annotation — their *statements* are final and are the
paper's real endpoints — while their proofs are not yet axiom-clean. Such a declaration
cannot be listed in `#assert_axioms_clean`: that command exists to catch exactly a
`sorryAx` dependency, so listing it would either fail the build or invite someone to weaken
the check. Dropping the annotation instead would be a lie about the statement's provenance,
and would also stop the node checker from guarding the statement.

So the *annotated* surface is split across two of `AxiomAudit.lean`'s three Condensation
blocks. (The third is the marker-less `## Consumer API conveniences` `#assert_axioms_clean`
block near the end of the file, which is where the un-annotated consumer plumbing and the
constructed non-vacuity witnesses are asserted clean. It plays no part in the staging
mechanism described here, and it is a common misreading — corrected in round 4, R4-F24 — to
suppose that the `-- SECTION: consumers (un-annotated)` marker below is where those live.
It is not: that marker belongs to the staging block and names un-annotated consumers *of a
staged theorem*.) The
`CONDENSATION-INVENTORY` block is the ordinary axiom gate. The `CONDENSATION-PENDING`
block that follows it is **pure Lean comment** — it compiles to nothing and asserts nothing
— and names, one per line with a reason, every annotated endpoint that is not yet
axiom-clean. **It is empty as of M2**, in both of its sections, and reads in full:

```
-- CONDENSATION-PENDING-BEGIN
-- SECTION: consumers (un-annotated)
-- CONDENSATION-PENDING-END
```

Empty is not the same as retired: the block is the standing mechanism for staging, and the
checkers fence it whether or not anything is in it. A populated entry took the form
`-- Condensation.condEntropy_jointAbove_le    -- M2: Theorem 5.8 (5.13)`, a `--` comment
naming one declaration and one reason.

The block has **two sections**. The main one names annotated endpoints. The second, opened
by the `-- SECTION: consumers (un-annotated)` marker above, names declarations that depend
on `sorryAx` but carry no annotation at all — small consequences of a staged theorem, which
are not claims about the paper and so must not be annotated, but which a reader must still
not mistake for proved. Round 2 found three of these living outside both blocks, which is
exactly the drift the ledger exists to prevent (R2-F22); they became axiom-clean when
Proposition 4.2's second inequality landed, and the section has been empty since.

It is a declaration of intent, not a discharge, and the checker fences it so it buys
nothing else. `scripts/check-condensation-nodes.py` accepts an annotated declaration listed
in *either* block, and **fails** if:

* a name appears in **both** blocks — an endpoint is axiom-checked or proof-pending, never
  both, which is what stops one being quietly "proved" in one place while still excused in
  the other;
* a pending entry names **no annotated declaration** — a stale entry left behind when an
  endpoint is renamed or retired would otherwise sit there excusing nothing;
* a pending line is **malformed** — not a `--` comment, no declaration name, no reason, or
  a duplicate — so the block cannot degrade into a place to hide things;
* the block is **non-empty while `scripts/papers.py` registers the paper `completed`** —
  staging is a mid-flight device, and the gate arms itself the moment the registry says the
  paper is done.

A surviving non-empty block prints as a note (`note: N endpoints pending (sorry) + M
un-annotated consumers — not axiom-checked`), never as a violation; at M2 there is no such
note to print. **Moving a name from the pending block into the inventory block is what "M2
proved this endpoint" means**, and the two edits belong in the same commit as the proof.
Every name has now made that move. The mechanism lives in `scripts/paper_nodes.py` as a
generic `pending_block` keyword argument, so any paper in this repo can opt into it;
Condensation is currently the only one that does.

**The ledger is mechanically complete, in both directions, and it currently certifies
zero.** `scripts/check_sorry_ledger.py` runs one `lake env lean` elaboration against the
built oleans, enumerates every declaration of the Condensation library that depends on
`sorryAx` (de-mangling `private` names rather than dropping them, and reporting an ORPHAN
violation if its filter of compiler-generated names would swallow a real declaration), and
fails on either direction of drift: a `sorry`-dependent declaration named in neither
section, or a ledger entry that no longer depends on `sorryAx`. It scans 1004 declarations
— 512 user-facing, 492 compiler-generated — and finds none of the first kind and none of
the second. The reverse half is what made "moving a name from the pending block into the
inventory block is what M2 proved this endpoint means" non-optional as the proofs landed:
it is the check that caught Lemma 4.13's four carriers becoming clean, and it is what would
now catch an entry left behind in the empty block.

Per the repo's surface-hygiene rule, `theorem` is reserved for paper-facing statements;
supporting results are `lemma` (or `private lemma`), and data-valued carriers are `def`s.

## Errata

Defects found in the printed paper while formalizing are recorded in
[`notes/paper-errata.md`](notes/paper-errata.md) — **twenty-two entries as of the round-4
close-out (2026-08-18)**, plus one candidate investigated and *refuted*, recorded at the
foot of that file so it is not re-raised: a wrong equation reference in Theorem 5.8's proof,
an undefined symbol in Theorem 4.15's proof, a leftover parameter name in Corollary 5.10, a
dropped "almost everywhere" in Theorem 4.9, one lemma that is **false as printed**, a
definition missing the finiteness clause its own consuming theorem needs, and several
citation and notation slips.

Entries 17–22 came from the **final blind audits** — an Opus auditor and a codex auditor
given only the paper, the Lean source and the standing rulings, and deliberately *not* given
this errata file. Those same audits independently rediscovered entries 1, 2, 4, 6, 8, 10,
11, 15 and 16, which is the corroboration the trust surface rests on; see `KNOWLEDGE.md`,
*Audit history and corroboration*, including the reason not to show a future auditor this
file before they audit.

Seven of the twenty-two bear directly on a Lean statement or docstring, and each was found
by trying to write that statement down or by trying to prove it:

* **entry 10 — Definition 4.12 does not tie `π̃₁` to `π̃₂`.** Each `L̃ₖ` carries its own map
  to `Ω`, and the commuting square (4.43) that would relate them belongs to Definition
  4.11, which Definition 4.12 does not restate. Theorem 4.15's proof needs them to agree
  almost everywhere. Carried as the explicit field `LatentAmalgamation.comm` — the *only*
  added field. Round 2 removed two others, `ρ₁_π`/`ρ₂_π`, that had been read into clause
  (3): its morphisms `ρₖ` are morphisms in the sense of Definition **3.5**, i.e. of the
  underlying random variable models, and the paper defines no morphism of latent models and
  so asks for no compatibility between `Lₖ.π ∘ ρₖ` and `π̃ₖ`. Entry 10 records both halves.
* **entry 11 — Example 4.1's (4.4) and (4.5) are false at `A = ∅`.** Both scores are then
  the empty sum `0` while the right-hand side is `H(X_I)`. The Lean statements take
  `A.Nonempty`.
* **entry 12 — Theorem 5.8 uses the `Z`-side contribution condition at (5.18) without
  listing it as a hypothesis.** Legitimate, because Definition 4.12 supplies it; the Lean
  statement quantifies over `LatentAmalgamation`, whose field `contributes₂` is where the
  licence actually lives.
* **entry 13 — Definition 5.6's "parents" are children under the usual convention.** Not an
  error, but it inverts the reading a formalizer brings to it, and it cost one wrong first
  draft here.
* **entry 14 — Theorem 5.8 and Corollaries 5.9, 5.10 are vacuous at `F = ∅`.** Definition
  5.6(1)'s tree has a root and so has at least one leaf, while the bijection the theorem
  demands would have to match those leaves against an empty set of sets; no such tree
  exists, so the hypothesis cannot be discharged. This is a property of the printed
  statement, not of the rendering, and it is why the Lean `condEntropy_jointAbove_le_choose`
  (5.25) carries no `1 ≤ k` hypothesis while `polar_kSubsets` (5.24), which has no tree in
  sight, keeps it (R2-F21).
* **entry 15 — Lemma 4.14 is false as printed.** The printed binders constrain only the
  probability space and `C`'s range; nothing makes `X`'s range separate points, and when it
  does not the conditional-independence hypothesis can be vacuous while the conclusion is a
  real constraint. The counterexample is machine-checked: `Ω = Bool` uniform, `U = Unit` so
  that `C` is constant, `S = T₁ = T₂` a two-point type carrying the *trivial* σ-algebra `⊥`,
  and `X = Y₁ = Y₂ = id` satisfies every hypothesis while the conclusion would force `id` to
  be a.e. constant. The formalization repairs it with a corrected binder rather than
  weakening the conclusion: `Condensation.aeFunctionOf_of_condIndepFun` carries
  `[MeasurableSingletonClass S]` on `X`'s range, which is free at every call site (`X` is
  always a model variable, and `RVModel` carries `singR`) and is licensed by the paper's own
  standing setting — Definition 3.1 and §2 — that every random variable under consideration
  has countable discrete **range**. (Not by the §2 sentence about probability *spaces* being
  countable and discrete: that constrains `Ω`, and the whole content of entry 15 is that
  constraining `Ω` alone leaves the lemma false. R4-F13 corrected this attribution.) `T₁` and
  `T₂` still need nothing beyond a measurable-space structure. Round 2's binder strip
  (R2-F01/F23) had gone one range too far; the orchestrator ruling of 2026-08-18 restored
  this one binder and the lemma is proved.
* **entry 17 — Definition 5.6 never requires the intersection tree to be finite or
  well-founded**, though Theorem 5.8's (5.13)/(5.14) are finite sums over its leaves and
  internal vertices. Condition (1) constrains directed paths *to* the root, which the full
  infinite binary tree satisfies, and the leaf-bijection hypothesis bounds only the leaves.
  The Lean's inductive `ITree` reads Definition 5.6 as ranging over the **finite** trees;
  since R4-F02 that is written down as a *disclosed reading* licensed by Theorem 5.8's sums,
  not as "nothing is lost" — see the `dd:tree` row above. Note that entry 14's step "such a
  tree has at least one leaf" is licensed only by this reading.

**Consult that file before concluding that a Lean statement or proof diverges from the
printed one**, because in several places the printed text is the thing that is wrong. This
is the same discipline as `CartesianFrames/notes/paper-errata.md`, and it exists because a
formalizer's first instinct on a mismatch is to assume the Lean is wrong.

## Non-vacuity discipline

Repo standard, and it applies here from M0 onward: **every boundary structure gets a
constructed inhabitant in `Examples.lean`, never a stand-in.** A hypothesis nobody has
exhibited a witness for is not a formalization, and a theorem whose antecedents are
unrealizable proves nothing.

What is actually constructed and proved at M0, so that no reader has to take the word
"witness" on trust:

| witness | what it is | what is *proved* about it |
|---|---|---|
| `coinModel` | `Ω = Bool` uniform, `I = Unit`, `X_() = id` | `coinModel_entropy : H(X_()) = log 2` and `coinModel_entropy_pos : 0 < H(X_())` — not the degenerate zero-entropy model |
| `coinLatent` | Example 4.1's `L₁` recipe over it: `Λ = Ω`, `π = id`, `Y_{()} = X_()` | `coinLatent_nonempty`; `coinLatent_reconScore : ϱ_L({()}) = 0` |
| `twoCoinLatent` | two indices (`I = Bool`), `P⁺I` of size 3, all latents equal to one fair coin | `σ_L({true}) = 2 log 2`, `χ_L({true}) = log 2`, hence `0 < χ_L < σ_L`; and `ϱ_L({true}) = 0` |
| `noisyLatent` | `I = Unit`, `Λ = Bool × Bool`, `π = fst`, `Y_{()} = id` — the latent keeps a bit that `π` throws away | `ϱ_L({()}) = log 2`, hence `0 < ϱ_L({()})`: the reconstruction score is **not** identically zero. Also `σ_L({()}) = χ_L({()}) = 2 log 2` |
| `LatentModel.ofJoint` / `.nonempty` | the tautological latent model `Y_A = X_A` of an arbitrary `M` | `Nonempty (LatentModel M)` for **every** random variable model `M` |
| `Example.geomModel` / `.geomLatent` (added 2026-08-17) | `I = Unit`, `Ω = ℕ` with the `Geometric(1/2)` law, `X_() = id : ℕ → ℕ`; `geomLatent` is `LatentModel.ofJoint geomModel` | `geomModel_entropy : H(X_()) = 2 log 2` (the textbook two bits) and `geomModel_not_finiteRange : ¬ FiniteRange (geomModel.X ())`. This is the witness that retiring `dd:finite-range` has content rather than being a re-spelling: every other witness here lives on a finite sample space and so cannot tell Definition 3.1's reading from the narrowed one. `geomLatent_reconScore = 0` for the same reason `coinLatent`'s does |

Every row above witnesses a *structure*. The rows below, added 2026-08-18, witness the
**conditions** of §4 — Definition 4.3's two clauses and Definition 4.8 — which until then
had no constructed inhabitant at all, so Theorem 4.9, Proposition 4.10 and Theorem 4.15
were non-vacuous only in the sense that their statements elaborate.

**Read the `I = Unit` rows as satisfiability only** (R4-F23, corrected 2026-08-18). Round 3
landed them and over-claimed: at a subsingleton `P⁺I` both definitions collapse, and the
collapse is now *proved* rather than argued —
`condScore_eq_simpleScore_of_subsingleton_index` shows `χ_L = σ_L` for **every** latent
variable model over such an index, so `coinLatent_perfectlyCondenses` cannot tell Definition
4.3's two clauses apart; and `incomparable_eq_empty_of_subsingleton_index` shows Definition
4.8's family of incomparable indices is **empty** there, so the ordered Markov condition is
an assertion of conditional independence from a variable into a one-point type and holds for
every `RVModel (PPlus Unit)`. The `I = Bool` rows are the ones with content:

| witness | what it is | what is *proved* about it |
|---|---|---|
| `coinLatent` again (`I = Unit`, **degenerate**) | the same `L₁`-shaped latent model over the fair coin | `coinLatent_perfectlyCondenses : coinLatent.PerfectlyCondenses` — Definition 4.3's conditioned clause, checked at both elements of `Finset Unit` (`0 = 0` at `∅`, `log 2 = log 2` at `{()}`). Hence `coinLatent_orderedMarkov : coinLatent.L.OrderedMarkov`, Definition 4.8, obtained through Theorem 4.9's (B1 ⇒ B2) rather than proved by hand. **Satisfiability only** — see the two degeneracy lemmas above |
| `twoCoinLatent` (`I = Bool`) — **Definition 4.3's two clauses separated on one witness** | `P⁺Bool` has three elements; all three latents are the same fair coin | `twoCoinLatent_perfectlyCondenses : twoCoinLatent.PerfectlyCondenses`, checked at all four values of `Finset Bool` (`χ_L = log 2 = H(X_A)` at each nonempty `A`, `0 = 0` at `∅`), **together with** `twoCoinLatent_not_simplyPerfectlyCondenses : ¬ twoCoinLatent.SimplyPerfectlyCondenses`, since `σ_L({true}) = 2 log 2` while `H(X_{true}) = log 2`. So `LatentModel.PerfectlyCondenses.of_simply` has **no converse**, and this is invisible at `I = Unit` |
| `twoCoinLatent` again — **Definition 4.8 with content** | the same two-index witness | `twoCoinLatent_orderedMarkov : twoCoinLatent.L.OrderedMarkov`, again through Theorem 4.9's (B1 ⇒ B2). Unlike the `Unit` case the condition is not vacuous here: `twoCoin_incomparable_T` computes `incomparable twoCoinT = {twoCoinF}`, which is nonempty, so the conditional independence being asserted is about a genuine variable |
| `Example44.L44 coinLatent.L` | Example 4.4's construction applied to the coin's latent family | `Example44.L44_coin_simplyPerfectlyCondenses` — Definition 4.3's *simple* clause. This is also what discharges `Example44.simplyPerfectlyCondenses`'s joint-independence hypothesis on a concrete family: `P⁺Unit` is a one-element index type, so Mathlib's `ProbabilityTheory.iIndepFun.of_subsingleton` applies. `L44_coin_perfectlyCondenses` follows by the (4.21) squeeze |
| `noisyLatent` again | the same `Λ = Bool × Bool`, `π = fst` witness | **the negative witness**: `noisyLatent_not_perfectlyCondenses : ¬ noisyLatent.PerfectlyCondenses`. `χ_L({()}) = 2 log 2` while `H(X_{()}) = log 2` — the gap is the bit `π` discards. Without this row the positive ones would not establish that perfect condensation is a *restriction* rather than a property every latent variable model has |

Two of those exist to correct a specific over-claim. An earlier draft of `Examples.lean`
asserted that *every* score is positive on the coin witness; that is false —
`coinLatent.reconScore {()} = 0`, and `ϱ_L(A) = H(Y_⊇A | X_A)` vanishes for any latent
system that the observables determine, which is precisely what a *perfect* reconstruction
is. `twoCoinLatent` is what shows `χ_L`'s conditioning doing work (the `Unit`-indexed
witness has nothing strictly above anything), and `noisyLatent` is what shows `ϱ_L` is not
identically zero.

The paper's own worked examples supply the rest at M1 — Example 4.1's two deliberately-bad
latent systems `L₁` (with `Y_{i} = X_i` and the other latents constant) and `L₂` (with
`Z_I = X_I` and the other latents constant), and Example 4.4's independent-latents model,
which *simply-perfectly* condenses the model built from it.

That last clause used to continue "…and so keeps Definition 4.3 and Theorem 4.9 from being
about an empty class". It did not, and the gap stood until 2026-08-18:
`Example44.simplyPerfectlyCondenses` is stated for an *arbitrary* family `L` satisfying a
joint-independence hypothesis, and nothing discharged that hypothesis for a concrete `L`, so
the theorem was as capable of being about an empty class as any other conditional. What
closes it is `Example44.L44_coin_simplyPerfectlyCondenses` in the second table above, which
instantiates the construction at the coin's latent family and discharges the independence
hypothesis outright. The general lesson: a `def` producing a structure witnesses the
structure, not the *conditions* a theorem imposes on it — those need their own witnesses.

`coinLatent` follows `L₁`'s recipe but is not
yet annotated as Example 4.1: that annotation waits for the general statement, since with
`I = Unit` the `L₁` and `L₂` recipes coincide and prove nothing about the distinction the
example is making.
