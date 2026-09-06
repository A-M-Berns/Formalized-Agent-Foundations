import LogicalInduction.Framework.Machine.ClockedSim
import LogicalInduction.Framework.Emission.Computable

/-!
# `def:ec` — the machine trader class and its enumeration

This module renders `def:ec` (tex:753) at the paper's own quantifier: ordinary machine
polynomial time, through `Complexity.FP` from the pinned complexitylib fork. It defines
`enumeratedTrader : ℕ → Trader` — run the described machine on the unary day under the
indexed clock, then decode — and `enumeratedOutput : ℕ → List Bool → List Bool`, the
function an index computes.

Both halves of "this is an enumeration *of* the class" are proved here.
`enumeratedOutput_mem_FP` and `enumeratedTrader_machineEfficient` are soundness: every index
denotes a member of the class. `exists_enumeratedTrader_eq` is coverage: every
machine-efficient trader occurs at some index, as an exact equality of traders. Coverage is
what `Construction/TradingFirm.lean` consumes — `trading_firm_dominance_of_covered` takes
`hcov : ∃ j, enumeratedTrader j = Tr` and nothing else — so it is what makes the dominance
proof quantify over the machine class.

Three choices shape the rendering.

*Unary days.* The paper measures a trader's runtime as polynomial in the day `n` written in
unary, and `unaryDay n = List.replicate n true` has length exactly `n`, so
`Complexity.FP`'s asymptotics are the paper's; a binary rendering would silently strengthen
the class.

*Token streams, not giant numerals.* The class is stated over the machine's finite output
word, decoded by the existing pipeline
`strategyOfTokens ∘ unRpn ∘ undigitize ∘ bitsToDigits`; no second parser is introduced, and
malformed output inherits the established zero-strategy fallback.

*The semantic class and the enumeration are kept apart.* `MachineEfficientTrader` is not
defined as "occurs in the enumeration"; that every member does occur is the content of
`exists_enumeratedTrader_eq`. Soundness is correspondingly a real theorem rather than the
`rfl` it is in the fuel setting, because a bogus index's trader is the described machine's
*truncated* behaviour, and an `FP` witness for a truncation needs the clocked simulator of
`Framework/Machine/ClockedSim.lean`: the description an index names is fixed, so the simulator's
control states are the described machine's own and one transition performs one described
step under a unary clock.

Relation to the certificate layer (`dd:fuel`): `Framework/MachineEfficiency.lean` proves
`EfficientlyComputable Tr → MachineEfficientTrader Tr`; the converse is not proved and is
not claimed.
-/

namespace LogicalInduction

open LogicalInduction.MachineExec

/-! ## The enumeration

The index carries a description and a polynomial clock and nothing else — no certificate,
because none is checked. Soundness comes from truncation, coverage from choosing a clock
that dominates. -/

/-- The trader denoted by enumeration index `i`: run the described machine on the unary day
under the indexed clock, and decode. Total by construction — `machineTokens` falls back to
`[]` on timeout and `strategyOfTokens` to the zero strategy on malformed input. -/
def enumeratedTrader (i : ℕ) : Trader where
  strat n := strategyOfTokens n (unRpn (undigitize (machineTokens i n)))

/-- The enumeration's day-`n` strategy, unfolded. -/
lemma enumeratedTrader_strat (i n : ℕ) :
    (enumeratedTrader i).strat n
      = strategyOfTokens n (unRpn (undigitize (machineTokens i n))) := rfl

/-! ## The function an index computes

Named because it is the object the soundness proof places in `Complexity.FP`, which
`enumeratedOutput_mem_FP` below does via the clocked simulator of
`Framework/Machine/ClockedSim.lean`.
`bitsToDigits_enumeratedOutput` is the other half of the connection — it identifies this
function's output on a unary day with the index's token stream — and together the two reduce
`enumeratedTrader_machineEfficient` to that `FP` membership. -/

/-- The function an index computes: the described machine's output word on its input, or the
empty word if the indexed clock runs out. This is the function
`enumeratedOutput_mem_FP` places in `Complexity.FP`. -/
def enumeratedOutput (i : ℕ) (x : List Bool) : List Bool :=
  match evalHalted (progDesc i) (progClock i x.length) x with
  | none => []
  | some c => codedOutput c

/-- On a unary day, the index's output function reproduces its token stream. -/
lemma bitsToDigits_enumeratedOutput (i n : ℕ) :
    bitsToDigits (enumeratedOutput i (unaryDay n)) = machineTokens i n := by
  rw [enumeratedOutput, machineTokens, length_unaryDay]
  cases evalHalted (progDesc i) (progClock i n) (unaryDay n) with
  | none => rfl
  | some c => rfl

/-! ## Soundness

Every index denotes a machine-efficient trader. The index's clock is a `Polynomial ℕ` in the
normal form `Complexity.FP` asks for, and `Framework/Machine/ClockedSim.lean`'s simulator
computes the
truncated run within an explicit polynomial, so the function an index computes is genuinely
in `FP` — not merely Lean-computable, and not through a meta-level evaluation. -/

/-- The function an index computes is polynomial-time.

The witness is the clocked simulator for the fixed description the index names: it measures
the day, evaluates the index's own clock polynomial into a unary register, and runs the
description one step per clock mark, blanking the output when the clock is exhausted.
Paper node: `def:ec` -/
lemma enumeratedOutput_mem_FP (i : ℕ) : enumeratedOutput i ∈ Complexity.FP := by
  have heq : (fun x => clockedOutput (progDesc i) ((progClockPoly i).eval x.length) x)
      = enumeratedOutput i := by
    funext x
    rw [progClockPoly_eval, clockedOutput, enumeratedOutput]
    rfl
  rw [← heq]
  exact clockedOutput_mem_FP (progDesc i) (progClockPoly i)

/-- **Enumeration soundness** (`def:ec`): every index denotes a trader in the machine class.
Together with `exists_enumeratedTrader_eq` this makes the enumeration an enumeration
*of* the machine-efficient traders, not merely one that covers them.
Paper node: `def:ec` -/
theorem enumeratedTrader_machineEfficient (i : ℕ) :
    MachineEfficientTrader (enumeratedTrader i) := by
  refine ⟨enumeratedOutput i, enumeratedOutput_mem_FP i, fun n => ?_⟩
  rw [enumeratedTrader_strat, strategyOfOutput, bitsToDigits_enumeratedOutput]

/-! ## Coverage

The other half, and the one `TradingFirm` consumes.

`Construction/TradingFirm.lean` takes `hcov : ∃ j, enumeratedTrader j = Tr` and nothing else,
so coverage is exactly what makes the dominance proof quantify over the machine class. -/

/-- **Enumeration coverage.** Every machine-efficient trader occurs at some index, as an
exact equality of traders — not merely eventual agreement.

The chain: the class witness lies in `Complexity.FP`; the fork's
`exists_desc_computesInTime_clock` turns that into a `TMDesc` computing it under a clock in
the index's own normal form; bumping the coefficient makes that clock *strictly* dominate,
which is the one step of slack the budgeted evaluator needs in order to observe a halt; and
`machineTokens_eq_of_computesInTime` then says the index emits exactly the witness's output
word on every unary day.
Paper node: `def:ec` -/
theorem exists_enumeratedTrader_eq (Tr : Trader) (hTr : MachineEfficientTrader Tr) :
    ∃ i : ℕ, enumeratedTrader i = Tr := by
  obtain ⟨F, hF, hstrat⟩ := hTr
  obtain ⟨d, a, k, T, hd, hak⟩ := exists_desc_computesInTime_clock hF
  refine ⟨MachineTraderProgram.index ⟨d, a + 1, k⟩, Trader.ext (funext fun n => ?_)⟩
  have htok : machineTokens (MachineTraderProgram.index ⟨d, a + 1, k⟩) n
      = bitsToDigits (F (unaryDay n)) := by
    refine machineTokens_eq_of_computesInTime (T := T) ?_ n ?_
    · rw [progDesc_index]; exact hd
    · rw [progClock_index, length_unaryDay]; exact lt_clock_succ (hak n)
  rw [enumeratedTrader_strat, htok, ← hstrat n, strategyOfOutput]

end LogicalInduction
