import LogicalInduction.Framework.Machine.CodeSteps
import LogicalInduction.Framework.Machine.DigitBits
import LogicalInduction.Framework.Machine.EvalnCompiler
import LogicalInduction.Framework.Machine.EvalnRegBound
import LogicalInduction.Framework.Machine.FPFold
import LogicalInduction.Framework.Machine.TokenFold
import LogicalInduction.Framework.Machine.TraderMachine
import LogicalInduction.Framework.MachineEfficiency
import LogicalInduction.Construction.MachineTraderEnumeration
import LogicalInduction.Construction.Machine.ClockedSim
import LogicalInduction.Construction.Machine.CondEndpoints
import LogicalInduction.Construction.Machine.CondStep
import LogicalInduction.Construction.Machine.DescExec

/-!
# `LogicalInduction.Construction.Machine` — the executable machine side

The executable machine side of the construction, gathered so the directory builds as one
unit: the `MachineExec` lake target roots here.

The efficiency model itself lives in `Framework/MachineEfficiency.lean` and
`Framework/Machine/`, which define the paper's reading of `def:ec`, so they sit beside
`EfficientlyComputable` rather than in the §5 construction.

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

Every module named here is also reached from `LogicalInduction.lean`, so this file adds a
build unit rather than a dependency.
-/
