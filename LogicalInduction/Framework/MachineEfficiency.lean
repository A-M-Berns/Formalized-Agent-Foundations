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
import LogicalInduction.Framework.Machine.TraderMachine

namespace LogicalInduction

open LogicalInduction.TraderMachine

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
construction proves, and the primary one.

`IsLogicalInductor` (`Framework/Criterion.lean`) states the same shape over the
fuel-certified class. It is kept as a **compatibility predicate**: the property tail's
theorems are stated against it, and every one of them transfers to a machine logical
inductor immediately through the instance below, because a machine logical inductor *is* a
fuel-class one. Nothing in the property tail is weaker for it.

The place the bridge does not suffice is a theorem whose *conclusion* is itself the
criterion — closure under conditioning (`thm:scon`) and the finite-perturbation statement
(`thm:ifp`). Those transport an arbitrary trader backwards across a market change, so
restating them at the machine class needs the machine class to be closed under the same
trader translations: a direct `Complexity.FP` transport theorem for the strategy
serialization. Both transport theorems now exist.

* `thm:scon` — **complete at the machine quantifier**, in all three forms.
  `CondStep.conditionedTranslation_preserves_machine` and
  `eventualConditionedTranslation_preserves_machine` are the `Complexity.FP` transports,
  under the same `RpnSentenceCodes` hypothesis on the condition as their fuel counterparts;
  `lic_conditioned_machine`, `lic_conditioned_gated_machine` and
  `lic_conditioned_eventual_machine` are the endpoints. The fuel endpoints and their
  witnesses are untouched beside them.
* `thm:ifp` — the *corrected* finite-support statement is proved at both classes
  (`machine_lic_iff_of_finiteSupportPerturbation`, `Properties/FinitePerturbations.lean`),
  and the published unrestricted statement is **refuted** (`not_overgeneral_ifp`). The
  freeze certificate `MachineFiniteSupportPatch` is **inhabited**
  (`FreezeOracle.machineFiniteSupportPatch_ofTable`) for tables meeting three stated
  conditions; its fuel-class counterparts are not. No concrete pair of computable markets is
  constructed, so the corrected theorem is not yet exhibited non-vacuous end to end.

The converse inclusion, machine ⟹ fuel, is neither needed nor claimed. -/

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

/-- **Every machine logical inductor is a logical inductor in the fuel-class reading**,
because every fuel certificate is a machine-efficiency certificate. This is what carries the
whole property tail over to the machine criterion unchanged. -/
instance IsMachineLogicalInductor.toIsLogicalInductor {P : History} {DP : DeductiveProcess}
    [hLI : IsMachineLogicalInductor P DP] : IsLogicalInductor P DP where
  marketComputable := hLI.marketComputable
  processComputable := hLI.processComputable
  noExploit := fun Tr h => hLI.noExploit Tr h.toMachine

end LogicalInduction
