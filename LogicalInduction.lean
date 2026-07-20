/-
# Logical Induction (Garrabrant et al., arXiv:1609.03543) — Lean 4 formalization

Spec: `notes/logical-induction-roadmap.md`. Standards: `CLAUDE.md`.

This roll-up imports the project's Parts, mirroring the roadmap:

* `Asymptotics`  — the single limit vocabulary (`dd:asymp`).
* `Foundations` — language, worlds, markets, deductive process, efficient computability.
* `Criterion`   — expressible features (`def:tf` keystone), traders, the LI criterion.
* `Engine`      — ROI, the affine master theorem, the LUV expectation bridge.
* `Properties`  — the property tail, all conditioned on `[IsLogicalInductor P]`.
* `Construction`— Brouwer fixed point, market maker, budgeter, `LIA`, existence.

## Reading the repository against the paper

Core vocabulary, repo name → paper name (labels are the paper's own `\label`s):

* `Sentence` — sentences of the base language (`def:lang`), propositional via Foundation.
* `History` (usually `P`) — the market: one pricing per day (`def:market`).
* `PCWorld` — a plausible world: a propositionally consistent `{0,1}` valuation
  (`def:world`).
* `DeductiveProcess` (usually `DP`) — the deductive process `D̄` (`def:worlds`).
* `EF` — an expressible feature (`def:valfeature`/`def:tf`).
* `Trader`, `AffineCombination` — traders and their affine buy combinations
  (`def:trader`, `def:tradestrat`).
* `EfficientlyComputable` / `PolyFueled` — `def:ec`, in the disclosed fuel-clocked
  interpreter model (`dd:fuel`), not an abstract complexity class.
* `IsLogicalInductor` — the logical induction criterion (`def:lic`).
* `LUV` — a logically uncertain variable (`def:luv`).
* `LIA` — the paper's logical induction algorithm (`def:lia`).

Theorem-naming convention: `lic_<node>` states a consequence (or, for
`lic_iff_of_finitePerturbation`, a transport) of the criterion, mirroring the paper node
named in its docstring (e.g. `lic_provind` ↔ `thm:provind`); the consequence theorems
take `[IsLogicalInductor P DP]` as a hypothesis. `..._ofComputation` / `..._ofCode` /
`..._ofRepresentation` variants are the same statements with a formerly assumed
boundary interface discharged by a concrete construction. The checked inventory of all
public endpoints is `LogicalInduction/AxiomAudit.lean`.
-/
import LogicalInduction.Asymptotics
import LogicalInduction.Foundations
import LogicalInduction.Criterion
import LogicalInduction.Computable
import LogicalInduction.Engine
import LogicalInduction.ROI
import LogicalInduction.Affine
import LogicalInduction.Properties
import LogicalInduction.Expectations
import LogicalInduction.Construction
import LogicalInduction.IntegrationTest
import LogicalInduction.AxiomAudit
