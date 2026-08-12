# Project: Formalized Agent Foundations — ethos & standards

This repo formalizes papers in agent foundations / open-source game theory in Lean 4,
on top of [Foundation](https://github.com/FormalizedFormalLogic/Foundation) and Mathlib.

The flagship formalization is **Logical Induction** (Garrabrant et al.,
arXiv:1609.03543) in `LogicalInduction/` — near-complete; see
`LogicalInduction/README.md` for the trust-surface summary and
`LogicalInduction/notes/faithfulness-audit-2026-08-08.md` for the current audit. **The paper is the
spec** (`LogicalInduction/notes/1609.03543v5-main.tex`); every paper-facing theorem carries the paper's
real `\label` in a `Paper node:` docstring line, checked two-way by
`scripts/check-paper-nodes.sh`. The `dd:*` design-decision labels used in docstrings
are defined in the glossary at `LogicalInduction.lean`.

The finished `ModalAgents/` formalization (Barász et al., arXiv:1401.5577) is the model
for disclosure discipline: a clean proof with its unproved facts named, cited, and
isolated in its README. Do the same kind of honest accounting everywhere. Its paper
specification is committed as `ModalAgents/notes/1401.5577-main.tex` and the matching
PDF. That paper labels only 22 of its nodes and leaves several formalized ones
unlabeled, so — as in Cartesian Frames — the printed `Theorem 3.2` / `Lemma 4.5` numbers
are the provenance keys, checked by `scripts/check-modal-agents-nodes.py`, which
recomputes them from the TeX by emulating its shared section-scoped theorem counter and
enforces the annotation contract fail-closed (validity including the node *kind*,
anchoring to a *named* declaration, and per-declaration coverage in `AxiomAudit.lean`'s
MA-INVENTORY block). A number of inventoried endpoints there deliberately carry no
annotation, because the facts they prove are unnumbered paper prose, proof steps, or
that development's own accounting of where `GL` falls short of the paper's `PA+1`/`PA+2`
claims; the reasons are recorded at each declaration and in the MA-INVENTORY preamble
and README. Note the paper's
`definition` environment is an *uncounted* `trivlist`, so that paper has no numbered
definitions to cite.

The **Cartesian Frames** formalization (Garrabrant, Herrmann, and Lopez-Wild,
arXiv:2109.10996) lives in `CartesianFrames/` and is node-complete: all 60 numbered
nodes carry Lean statements, with no modeling substitutions. Begin with
`CartesianFrames/README.md` and the knowledge base `CartesianFrames/KNOWLEDGE.md`
(settled design decisions, the correspondence table, and the pitfalls log — read the
pitfalls before writing concrete `Frame` witnesses, the `decide`/transparency traps
there are non-obvious). Its paper specification is committed as
`CartesianFrames/notes/2109.10996v1-main.tex` and the matching PDF; defects found in
that paper are recorded in `CartesianFrames/notes/paper-errata.md` — consult it before
concluding that a Lean proof diverges from the printed one, because in several places
the printed proof is the thing that is wrong. Most nodes in that paper lack LaTeX
labels, so their printed `Definition n` / `Claim n` / `Theorem n` identifiers are the
provenance keys, checked by `scripts/check-cartesian-frames-nodes.py`, which enforces
the annotation contract fail-closed (validity, anchoring to a *named* declaration, and
per-declaration inventory coverage). The same declaration rule applies: `theorem` iff
the declaration renders a paper claim/theorem; supporting results are `lemma`s — and
note that iso-valued and data-valued carriers must be `def`s, since `≅` is not a Prop.

Two accounting notes on that library: the read-through guide
`docs/trust-surface.html` covers **all three papers**, one section each, but only
LogicalInduction's section carries per-node strength tiers and audit notes — Cartesian
Frames and ModalAgents have no strength classification, so their sections are
correspondence views and say so on the page; and Claim 35 is formalized only in part, by
ruling, because its External/Internal half is ill-typed as printed (see the
intentional-deviations section of its KNOWLEDGE.md).

**Adding a paper.** `scripts/papers.py` is the registry of what this repo formalizes;
`scripts/check_paper_wiring.py` enforces that every `lean_lib` is either a registered
paper — with its source committed, a node checker running in CI, endpoints inside the
`AxiomAudit` import, and nodes rendered in the trust-surface guide — or an explicitly
excused non-paper library. Register a new formalization there first; the gate will then
tell you what is still unwired.

---

## The standard (non-negotiable)

The one-sentence bar:

> A kernel-clean proof certifies that the **body** matches the **statement**. It says
> nothing about whether the statement is the one we meant. The statement — its
> definitions, its hypotheses, its conclusion — is the trust surface, and it is only
> honest if its hypotheses are satisfiable and its constructed objects are real.

We are building the photo-negative of a failure mode: *proving the implications of a
theory while assuming the antecedents*. Here the antecedents — the trader
constructions and the criterion applications — **are** the content. A property "proof"
that takes the forcing inequality as a hypothesis, or stubs it with one-line
arithmetic, has formalized nothing we didn't already assume.

### Load-bearing rules

1. **The exploiting trader is the work.** No property proof is "done" until its
   exploiting trader is *constructed* and its efficient-computability certified in the
   emission calculus. A `sorry` on the trader construction is honest. An arithmetic
   stub *standing in for* the trader is the one thing the ledger exists to catch —
   never green it.

2. **Never invent a Mathlib/Foundation name.** Before using a lemma, def, or instance,
   confirm it exists in the installed source: `rg` the `.lake/packages` tree, or use
   `#check` / `exact?` / `apply?` / `loogle`. If what you need doesn't exist, leave
   `sorry` with a `-- TODO(<paper label>): need <statement>` and move on. Do not
   fabricate.

2b. **Search before you prove — the dual of rule 2, and the one that actually bites.**
   Rule 2 stops you using a name that doesn't exist. It does *nothing* to stop you
   spending an hour proving a lemma that already does. **Before writing the first
   tactic of any new lemma, grep for the fact — not the name you'd give it.** Search
   the *statement's shape* and its vocabulary, in this order: this repo (including
   downstream directories, easy to miss from an upstream file), then
   `.lake/packages/mathlib`, then `exact?` / `loogle`. Names differ; the fact is what
   collides. This has bitten repeatedly (three separate re-proofs of existing results
   were once committed in a single session, only one caught by the compiler) — make
   the grep mechanical, not a judgment call. A duplicate is worse than wasted time: it
   is a second, divergent proof of the same fact that some later reader must
   reconcile. If you do find you duplicated something, the honest fix is to delete
   yours and cite the original — even when yours is the one you just debugged.

3. **The build stays green at every stopping point.** `sorry` is allowed and expected
   mid-flight; elaboration/type errors are not. Small compiling commits over large
   broken ones. The checked gates are `lake build AxiomAudit` (endpoint inventory:
   axiom cleanliness + Tier-2 field freeze) plus `scripts/check-paper-nodes.sh`,
   `scripts/check_endpoint_coverage.py`, and `scripts/lint_paper_labels.py`.

4. **Provenance is written at proof time, by the person who knows they cheated.**
   Record the proof kind and provenance in the theorem's docstring as you go, never
   retroactively. A new boundary theorem does not get committed without its provenance
   recorded in the same commit.
   - *kind:* `Def` · `P` proved · `C` composition · `S` squeeze-over-named (conclusion
     ≡ a hypothesis — flag and justify) · `T` trivial stub · `N±` non-vacuity witness.
   - *provenance* (per hypothesis): `(a)` derived in-project · `(b)`
     Foundation/Mathlib citation · `(c)` modeling substitution (a weaker/different
     object stands in for the intended one — the dangerous kind; eliminate it or
     disclose it).

5. **Modeling choices are disclosed, not discovered.** The two standing type-`(c)`
   substitutions — `dd:fuel` (efficiency = a fuel-clocked interpreter, not a
   complexity class; model card in `Framework/Computable.lean`) and the propositional
   substrate (LUVs as threshold families) — are documented in
   `LogicalInduction/README.md`. Any new substitution gets the same treatment at the
   statement, in the README, and in the audit ledger — before an auditor finds it.

6. **Surface friction; don't work around it silently.** If a design decision fights
   Lean's type system, say so in the session report — do not quietly route around it.
   A stop-and-report ("Foundation doesn't expose X", "Mathlib lacks Y"), stated
   self-containedly at the site, is a *success*, not a failure. The current verified
   obstructions live in `LogicalInduction/README.md` ("Planned future work") and
   `LogicalInduction/notes/boundary-efficiency-model.md`.

### Human read-through

The kernel covers proof bodies; it does not cover statements. Anson reads every
top-level **statement** and every **definition** before the work is called done. The
trust surface is small and this is tractable. Keep statements legible to that
read-through.

> **Sequencing (Anson).** The read-through runs **once, over the consolidated frozen
> surface** — not per-milestone. Order: **(1)** results green with disclosures in
> place (done); **(2)** consolidation / de-slop / API surface (in progress; see
> `LogicalInduction/notes/consolidation.md`), after which the surface re-freezes and the read-through
> runs over it; **(3)** a final fresh-context adversarial audit, last.

### Scheduled adversarial audit

At major junctures (and always before publication), run a **separate, fresh-context**
statement-level audit over the top-level theorems, hunting specifically for: vacuous
theorems (hypotheses unsatisfiable/unrealizable); conclusion-in-hypothesis squeezes;
oversold stubs; type-`(c)` substitutions; degenerate non-vacuity (constant-sequence
witnesses); and off-loaded steps. Where possible, non-vacuity is discharged **by the
construction** rather than a stand-in witness. The fresh 2026-08-08 audit
(`LogicalInduction/notes/faithfulness-audit-2026-08-08.md`) is the current snapshot: every qualification
is tied to the final statement surface or a verified obstruction.

### Consolidation discipline (Anson, standing — see `LogicalInduction/notes/consolidation.md`)

The end state must show **no structural evidence of previous versions**: no
ₙ-suffixed public layers, no parallel classes that exist only because a definition was
upgraded mid-project, no in-references legible only to someone steeped in the repo's
history (work-package tags, phase names, dead notes files). When strengthening a
definition, land the refactor in **collapsed form** — the strongest version takes the
plain, paper-matching name; superseded versions become internal lemmas or disappear.
Layered scaffolding is acceptable *mid-flight* to keep the build green, but it is
technical debt with a scheduled demolition, not an end state.

### External proofs (Aristotle, subagents, any generated Lean)

A proof produced outside this session — Aristotle, a subagent's worktree, pasted
code — is trusted only after it **compiles in this repo against this toolchain with
`#print axioms` clean**. The kernel is the gate; never merge on the producer's word.
Subagent work arrives on a worktree branch: inspect, build, axiom-check, then merge.

### Recurring Lean traps

The living gotcha log (tactic-level traps that repeatedly bite: `rcases h : e`
substituting the goal, `Nat.sqrt` whnf loops in `Primrec` work — fix = scoped
`irreducible Nat.sqrt`, `lake env lean`'s auto-bound implicits masking signature
errors, stale upstream oleans under `lake env lean`, `#assert_fields` freezing field
*names* only, …) is kept in `LogicalInduction/notes/consolidation.md`'s wave-gotchas section — check
it before starting deep `Primrec`/`PolyFueled` work.

## Working conventions

- Namespace `LogicalInduction`; file layout mirrors the paper's structure
  (`Framework/` = §2–3, `Properties/` = §4, `Construction/` = §5 + witnesses; see
  `LogicalInduction/README.md`). Naming conventions and the endpoint-suffix ladder
  (`_ofX` / `_unconditional` / `_closed` / `_arith`) are documented in
  `LogicalInduction.lean`.
- **Commit completed coherent work as you go.** Do not leave a finished green tranche
  accumulating in the working tree while starting the next tranche; checkpoint it with
  a focused commit after its build/audit gate passes. Preserve unrelated user changes
  and never use a commit as a substitute for reporting an incomplete or broken
  stopping point.
- One `Asymptotics` module owns the limit vocabulary (`≈ₙ`/`≳ₙ`, "eventually within
  ε", "converges to"), built on Mathlib's `Tendsto (· − ·) atTop (𝓝 0)` and
  `∀ᶠ n in atTop` (`dd:asymp`). Do not redefine these per file. Default to the
  **limiting** form; add the finite-stage form only where needed.
- Foundation supplies the propositional substrate: `Formula α` (with
  `Encodable (Formula α)` for `[Encodable α]` → computable sentence codes),
  `LO.Entailment` (`⊢`, `⊬`, `Consistent`), and `Propositional.Cl`. Wrap what we use
  behind the thin `LogicalInduction.Sentence` interface; don't scatter Foundation
  internals.
- Commit messages: no Claude/AI co-authorship lines. Push to `origin` freely; ask
  before pushing anywhere else.
