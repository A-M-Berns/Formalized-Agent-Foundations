/-
# `LogicalInduction.Construction.Machine` — the executable machine side

The efficiency model itself lives in `Framework/Machine/` and `Framework/MachineEfficiency.lean`:
it defines the paper's reading of `def:ec`, so it belongs beside `EfficientlyComputable`
rather than in the §5 construction. What is here is the executable side.

* `Machine/DescExec.lean` — the executable bridge from finite `complexitylib` machine
  descriptions to primitive-recursive bounded execution, and the compiler-facing token
  evaluator `machineTokens` built on it. This is what makes the canonical enumeration
  *effective*: `LIACompiler` takes the enumerated trader's day strategies from
  `machineTokens`, so the construction runs the same budgeted execution the enumeration's
  soundness proof reasons about. Read its module docstring for why the executable object is
  a *description* rather than a machine.
* `Machine/ClockedSim.lean` — the clocked simulator for a fixed description, and the proof
  that the truncated run is in `Complexity.FP`. This is the soundness half of the
  enumeration: every index denotes a genuinely machine-efficient trader.
* `Machine/CondStep.lean`, `Machine/CondEndpoints.lean` — the conditioning transduction as
  six `Complexity.FP` passes over one word-level automaton, and the criterion-level
  packaging that sits above both the fuel and machine realizations of `thm:scon`.

All of it is reachable from `LogicalInduction.lean`.
-/
import LogicalInduction.Construction.Machine.DescExec

import LogicalInduction.Construction.MachineTraderEnumeration

import LogicalInduction.Framework.Machine.CodeSteps

import LogicalInduction.Framework.Machine.EvalnCompiler
import LogicalInduction.Framework.Machine.EvalnRegBound
import LogicalInduction.Construction.Machine.ClockedSim
import LogicalInduction.Framework.Machine.DigitBits
import LogicalInduction.Framework.Machine.TraderMachine
import LogicalInduction.Framework.Machine.FPFold
import LogicalInduction.Framework.Machine.TokenFold
import LogicalInduction.Construction.Machine.CondStep
import LogicalInduction.Construction.Machine.CondEndpoints
import LogicalInduction.Framework.MachineEfficiency
