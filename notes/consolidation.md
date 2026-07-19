# Consolidation & style phase — intentions and best practices

_Started 2026-07-19. Branch: `logical-induction`. Status: **drafting** — Anson will add
rules/suggestions below; this is the opening framing._

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
  `dd:fuel`) end up named, cited, and isolated Barasz-style in the README's honest
  accounting — discoverable from the top, not from `notes/`.
- **Docstring provenance.** Provenance annotations written at proof time stay; this phase
  may reformat them for consistency but never reconstructs them retroactively.

## Style baseline

- Mathlib naming and style conventions (`lean4-theorem-proving` skill references) are the
  default; deviations are deliberate and local.
- Namespace discipline: everything under `LogicalInduction`; Foundation internals stay
  behind the `Sentence` interface (don't let consolidation scatter them).
- `Asymptotics` remains the single owner of limit vocabulary (`dd:asymp`); if
  consolidation finds a file with private limit definitions, that's a merge target.
- Roadmap `\label`s stay mirrored in comments — moving a theorem moves its label with it.

## Anson

Hi Anson here. What I'd like is for the end result to be as immediately legible as possible that this repo really contains a correct formalization of the paper, with only small/disclosed holes. Conventions should match the paper as much as possible. There should be no "in-references" i.e. names or ontologies that only make sense to an agent seeped in the repo. The API surface and library organization should be clean and consolidated, logically organized whenever possible. Proof bodies can be opaque that's not a big deal, but there should be as few "tricks" (e.g. setting heartbeats) as possible. The repo should be de-slopified, that's the goal. It should be easy for human-level attention to engage with the repo given basic understanding (and reference to) the paper.