/-
# `LogicalInduction.Construction.Machine` — the counted-step machine

Stage 1 of the efficiency-model program; the plan and the Stage-0 decision that produced it
are in `notes/boundary-efficiency-model.md`.

* `Machine/Basic.lean` — the machine, `RunsInTime`, and the polynomial class
  `MachinePolyEC`. Read its module docstring first: it is the model card.
* `Machine/Closure.lean` — sequential composition and the composition closure
  `MachinePolyEC.comp`; pairing is stated and open, with the design obstruction recorded at
  the site.
* `Machine/TimedRespectsProbe.lean` — the Stage-0 de-risk probe (a timed
  `Turing.TM1to0`). A spike: evidence for the decision, not part of the development, and
  deliberately not imported here.

**This directory is not part of the formalization's trust surface.** Nothing in it carries
a paper node, nothing is imported by `LogicalInduction.lean`, and no theorem relates
`MachinePolyEC` to `LogicalInduction.EfficientlyComputable` — that inclusion is Stage 2 and
is not started. No strength claim in the repository changes until Stage 3 completes.
-/
import LogicalInduction.Construction.Machine.Basic
import LogicalInduction.Construction.Machine.Closure
