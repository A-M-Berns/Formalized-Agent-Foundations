/-
# `LogicalInduction.Construction.Machine` — executable machine descriptions, and a retired spike

The efficiency model itself lives in `Framework/Machine/` and `Framework/MachineEfficiency.lean`:
it defines the paper's reading of `def:ec`, so it belongs beside `EfficientlyComputable`
rather than in the §5 construction. What is left here is the executable side and one dead
spike.

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
* `Machine/Basic.lean`, `Machine/Closure.lean`, `Machine/Pairing.lean` — the *counted-step*
  machine of Stage 1, with its polynomial class `MachinePolyEC`. Superseded by the
  `complexitylib` adoption and load-bearing for nothing; kept only until the adoption note's
  removal item is taken.
* `Machine/PairSucc.lean`, `Machine/TimedRespectsProbe.lean` — de-risk spikes from the
  Stage-0 decision. Evidence for the decision, not part of the development.

**The counted machine in this directory is not part of the trust surface.** No theorem
relates `MachinePolyEC` to anything else, and nothing imports it.

`DescExec` and `ClockedSim` *are*: they are reachable from `LogicalInduction.lean` through
`Construction/MachineTraderEnumeration.lean`, which is the canonical trader enumeration.

The counted machine was Stage-1 infrastructure built when no usable external substrate
existed; the adoption of `complexitylib` supersedes it, and the adoption note records it for
later removal rather than deleting it here.
-/
import LogicalInduction.Construction.Machine.Basic
import LogicalInduction.Construction.Machine.Closure
import LogicalInduction.Construction.Machine.Pairing
import LogicalInduction.Construction.Machine.DescExec

import LogicalInduction.Construction.MachineTraderEnumeration

import LogicalInduction.Framework.Machine.CodeSteps

import LogicalInduction.Construction.Machine.PairSucc
import LogicalInduction.Framework.Machine.EvalnCompiler
import LogicalInduction.Framework.Machine.EvalnRegBound
import LogicalInduction.Construction.Machine.ClockedSim
import LogicalInduction.Framework.Machine.DigitBits
import LogicalInduction.Framework.Machine.TraderMachine
import LogicalInduction.Framework.Machine.FPFold
import LogicalInduction.Framework.Machine.TokenFold
import LogicalInduction.Framework.MachineEfficiency
