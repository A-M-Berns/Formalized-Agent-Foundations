import LogicalInduction.Framework.Machine.TraderMachine
import LogicalInduction.Framework.WriteOut

/-!
# The machine criterion, and the fuel class inside it

This module renders `def:lic` (tex:657) at the paper's own quantifier and closes the relation
between the two efficiency classes of `def:ec` (tex:753).

* `EfficientlyComputable.toMachine` — every fuel-clocked certificate (`dd:fuel`) is a
  `MachineEfficientTrader`, a member of the class defined through ordinary machine polynomial
  time (`Complexity.FP`), proved through a real `evaln` → Turing-machine compiler. This is
  what makes the fuel calculus a *certification device* for `def:ec` rather than a
  substitution for it: nothing certified in the fuel model is outside the machine model, so a
  theorem quantifying over `MachineEfficientTrader` is at least as strong as the same theorem
  over `EfficientlyComputable`.
* `IsMachineLogicalInductor` — `def:lic` over `MachineEfficientTrader`, the criterion the §5
  construction discharges (`LIA_isMachineLogicalInductor`).
* `IsMachineLogicalInductor.toIsLogicalInductor` — the instance that carries the whole §4
  property tail, stated against the fuel-class `IsLogicalInductor`, to the machine criterion
  unchanged.

The compiler chain, and where each link lives:

* `Machine/EvalnCompiler.lean` — `compiledTM` compiles an arbitrary `Nat.Partrec.Code`
  into a `complexitylib` register machine, and `codeVals_encodes` proves its answer
  registers hold `Nat.Partrec.Code.evaln`'s tag and value, for all eight constructors.
* `Machine/EvalnRegBound.lean` — `codeRegBound` bounds every register the compiled
  machine holds, `codeMachineTime` bounds its steps, `compiledTM_hoareTime` proves the
  machine meets that bound, and `codeMachineTime_arith_poly` makes the bound polynomial in
  the size parameter, for each fixed code.
* `Machine/TraderMachine.lean` — `traderMachine` measures the day, evaluates the clock
  polynomial, runs the length program, and emits one clamped digit per token the token
  program returns; `traderOutput_mem_FP` places its output function in `Complexity.FP`.
* `Machine/DigitBits.lean` — the three-bits-per-digit rendering the machine emits and
  `MachineEfficientTrader` reads back, and the clamp `undigitize` licenses.

**Design: the inclusion is one-directional.**  The converse, machine ⟹ fuel, is neither
proved nor claimed. The `dd:fuel` model card (`Framework/Computable.lean`) defines what
`EfficientlyComputable` means and states the open calibration, and
`LogicalInduction/README.md` carries the standing disclosure.
-/

namespace LogicalInduction

open LogicalInduction.TraderMachine

/-! ## The fuel-class inclusion -/

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

/-! ## The paper-faithful criterion

`IsMachineLogicalInductor` states `def:lic` at the paper's own quantifier: no trader in
ordinary machine polynomial time exploits the market. It is the criterion the LIA
construction proves, and the primary one. `IsLogicalInductor` (`Framework/Criterion.lean`)
states the same shape over the fuel-certified class and is kept as a compatibility
predicate. -/

/-- **The Logical Induction Criterion at the paper's own quantifier** (`def:lic`): no
trader in ordinary machine polynomial time exploits the market. This is the criterion the
construction proves; `IsLogicalInductor` is its fuel-class compatibility reading, reached by
the instance below.
Paper node: `def:lic` -/
class IsMachineLogicalInductor (P : History) (DP : DeductiveProcess) : Prop where
  /-- Markets are computable rational pricing sequences in the paper's definition. -/
  marketComputable : ComputableMarket P
  /-- Deductive processes are computable nested finite-set sequences in the paper's
  definition. -/
  processComputable : ComputableDeductiveProcess DP
  /-- No machine-efficient trader exploits `P`. -/
  noExploit : ∀ Tr : Trader, MachineEfficientTrader Tr → ¬ Tr.Exploits P DP

/-! ## Transporting the property tail

The §4 property theorems are stated against `IsLogicalInductor`, and every one of them
transfers to a machine logical inductor through the instance below, because a machine
logical inductor *is* a fuel-class one. The asymmetry this creates determines how to state a
new result: a theorem *consuming* the criterion is thereby available at both classes, while a
theorem whose *conclusion* is the criterion must be stated at the machine class directly,
since that class has to be closed under the trader translation the proof performs. Both such
families are proved at both classes — `lic_conditioned_machine` for `thm:scon` (with
`lic_conditioned_gated_machine` and `lic_conditioned_eventual_machine` beside it) and
`machine_lic_iff_of_finiteSupportPerturbation` for `thm:ifp` in its corrected finite-support
form. `LogicalInduction/README.md` carries the full disclosure on the two classes.

The `thm:scon` transports are `CondStep.conditionedTranslation_preserves_machine` and
`eventualConditionedTranslation_preserves_machine`. They take `def:ec`'s own write-out class
`BigSentenceCodes` on the condition, in which a condition's Gödel code may be exponential in
the day; what carries it into the transducer is `CondStep.machineSentenceBlocks_of_big`,
running on `BigTokenStream.digitizeStream` (`Framework/WriteOut.lean`).

For `thm:ifp` the machine form is the informative one. The freeze certificate
`MachineFiniteSupportPatch` is **inhabited**
(`FreezeOracle.machineFiniteSupportPatch_ofTable`) for tables meeting three stated
conditions, while its fuel-class counterparts are not; a concrete computable market pair
discharges every hypothesis at once (`machine_lic_iff_twoPoint`), so the antecedent is
satisfiable; and `LIAPerturbation.machineLogicalInductor_liaPerturbed` derives from it a
machine logical inductor no construction here produces. -/

/-- **Every machine logical inductor is a logical inductor in the fuel-class reading**,
because every fuel certificate is a machine-efficiency certificate. This is what carries the
whole property tail over to the machine criterion unchanged. -/
instance IsMachineLogicalInductor.toIsLogicalInductor {P : History} {DP : DeductiveProcess}
    [hLI : IsMachineLogicalInductor P DP] : IsLogicalInductor P DP where
  marketComputable := hLI.marketComputable
  processComputable := hLI.processComputable
  noExploit := fun Tr h => hLI.noExploit Tr h.toMachine

end LogicalInduction
