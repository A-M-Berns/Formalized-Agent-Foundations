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
