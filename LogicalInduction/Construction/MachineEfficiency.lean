/-
# The fuel-clocked class is inside the machine class

Stage 2's endpoint (`LogicalInduction/notes/complexitylib-adoption.md`): every
`EfficientlyComputable` trader — the `dd:fuel` rendering of `def:ec`, a fuel-clocked
`Nat.Partrec.Code` pair under a polynomial day clock — is a `MachineEfficientTrader`, a
member of the class defined through ordinary machine polynomial time (`Complexity.FP`).

The chain, and where each link lives:

* `Machine/EvalnCompiler.lean` — `compiledTM` compiles an arbitrary `Nat.Partrec.Code`
  into a `complexitylib` register machine, and `codeVals_encodes` proves its answer
  registers hold `Nat.Partrec.Code.evaln`'s tag and value. All eight constructors.
* `Machine/EvalnRegBound.lean` — `codeRegBound` bounds every register the compiled
  machine holds, `codeMachineTime` bounds its steps, and `compiledTM_hoareTime` proves
  the machine meets that bound. `codeMachineTime_arith_poly` makes the bound polynomial
  in the size parameter, for each fixed code.
* `Machine/TraderMachine.lean` — `traderMachine` measures the day, evaluates the clock
  polynomial, runs the length program, and emits one clamped digit per token the token
  program returns; `traderOutput_mem_FP` places its output function in `Complexity.FP`.
* `Machine/DigitBits.lean` — the three-bits-per-digit rendering the machine emits and
  `MachineEfficientTrader` reads back, and the clamp `undigitize` licenses.

**What this does and does not settle.** It settles the *inclusion*: nothing certified in
the fuel model is outside the machine model, so a theorem quantifying over
`MachineEfficientTrader` is at least as strong as the same theorem over
`EfficientlyComputable`. It does not settle the converse, and the `dd:fuel` model card
(`Framework/Computable.lean`) still governs what `EfficientlyComputable` itself means;
see `LogicalInduction/README.md` for the standing disclosure.
-/
import LogicalInduction.Construction.Machine.TraderMachine
import LogicalInduction.Construction.MachineTraderEnumeration

namespace LogicalInduction

open LogicalInduction.TraderMachine
open LogicalInduction.MachineExec

/-- **Every fuel-efficient trader is machine-efficient.** Given the two codes and the
polynomial clock `EfficientlyComputable` names, `traderMachine` computes the trader's
day-`n` serialization in polynomial time, and the token pipeline
`strategyOfTokens ∘ unRpn ∘ undigitize ∘ bitsToDigits` reads it back as the same day-`n`
strategy. The machine emits each digit clamped at the terminator `4`, which
`undigitize_map_min_four` shows the pipeline cannot see.
Paper node: `def:ec` -/
theorem EfficientlyComputable.toMachine {Tr : Trader} (h : EfficientlyComputable Tr) :
    MachineEfficientTrader Tr := by
  obtain ⟨lc, tc, a, k, hTr⟩ := h
  refine ⟨traderOutput lc tc a k, traderOutput_mem_FP lc tc a k, fun N => ?_⟩
  rw [← hTr]
  show strategyOfOutput N (traderOutput lc tc a k (unaryDay N)) = _
  rw [strategyOfOutput, bitsToDigits_traderOutput, length_unaryDay,
    undigitize_map_min_four]
  rfl

end LogicalInduction
