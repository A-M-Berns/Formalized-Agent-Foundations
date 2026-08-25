/-
# `LogicalInduction.Construction.Machine` — the counted-step machine

Stage 1 of the efficiency-model program; the plan and the Stage-0 decision that produced it
are in `LogicalInduction/notes/boundary-efficiency-model.md`.

* `Machine/Basic.lean` — the machine, `RunsInTime`, and the polynomial class
  `MachinePolyEC`. Read its module docstring first: it is the model card.
* `Machine/Closure.lean` — sequencing (`seqProg`), relabelling into a larger memory with
  its frame lemma (`Prog.relabel`, `HaltsFrom.relabel`), and the composition closure
  `MachinePolyEC.comp`.
* `Machine/Pairing.lean` — the data-movement primitive `pump` and its three phases, the
  eight-phase pairing machine, and the pairing closure `MachinePolyEC.pair`.
* `Machine/DescExec.lean` — **Stage 3**: the executable bridge from finite `complexitylib`
  machine descriptions to primitive-recursive bounded execution, and the compiler-facing
  token evaluator `machineTokens` built on it. Read its module docstring for why the
  executable object is a *description* rather than a machine.
* `Machine/EvalnCompiler.lean` — **Stage 2**: the compiler from `Nat.Partrec.Code` into
  ordinary `complexitylib` register machines, proved exactly against
  `Nat.Partrec.Code.evaln`. All eight constructors; `compiledTM` is the machine and
  `codeVals_encodes` its correctness. Read its module docstring for the universal fuel
  guard and the multiplicative mask that keeps the compiled machines straight-line.
* `Machine/EvalnRegBound.lean` — the compiled machine's quantitative side: the register
  bound `codeRegBound`, the step bound `codeMachineTime` and its polynomiality, and the
  structural timing theorem `compiledTM_hoareTime`.
* `Machine/DigitBits.lean` — the bit rendering of a digit stream, and the clamping
  convention `undigitize` licenses.
* `Machine/TraderMachine.lean` — **Stage 2 item 5**: the register calculus over
  `regsWork` states, guarded emission, and the digit block, on the way to the machine
  that computes an `EfficientlyComputable` trader's serialization.
* `Machine/TimedRespectsProbe.lean` — the Stage-0 de-risk probe (a timed
  `Turing.TM1to0`). A spike: evidence for the decision, not part of the development, and
  deliberately not imported here.

**This directory is not part of the formalization's trust surface.** Nothing in it carries
a paper node, nothing is imported by `LogicalInduction.lean`, and no theorem relates
`MachinePolyEC` — or `DescExec`'s evaluator — to `LogicalInduction.EfficientlyComputable`.
That inclusion is Stage 2 and is not started. No strength claim in the repository changes
until Stage 3 completes.

It *is* compiled by CI, through the `MachineExec` default target in `lakefile.lean`: built
and axiom-checked, but load-bearing for nothing.

`Basic`/`Closure`/`Pairing` (the counted machine) and `DescExec` are **two different machine
models kept for two different reasons**, and no bridge between them is planned. The counted
machine was Stage-1 infrastructure built when no usable external substrate existed; the
adoption of `complexitylib` supersedes it on the main route, and the adoption note records
it for later removal rather than deleting it here.
-/
import LogicalInduction.Construction.Machine.Basic
import LogicalInduction.Construction.Machine.Closure
import LogicalInduction.Construction.Machine.Pairing
import LogicalInduction.Construction.Machine.DescExec

import LogicalInduction.Construction.MachineTraderEnumeration

import LogicalInduction.Construction.Machine.CodeSteps

import LogicalInduction.Construction.Machine.PairSucc
import LogicalInduction.Construction.Machine.EvalnCompiler
import LogicalInduction.Construction.Machine.EvalnRegBound
import LogicalInduction.Construction.Machine.DigitBits
import LogicalInduction.Construction.Machine.TraderMachine
