/-
# The genuine polynomial-time trader class and its enumeration

Stage 3 of the efficiency-model program (`LogicalInduction/notes/complexitylib-adoption.md`).
This file carries the paper-facing side of that program: a trader class defined through
**ordinary machine polynomial time** — `Complexity.FP`, from the pinned complexitylib fork —
together with a total effective enumeration of it and the **coverage** theorem that lets
`TradingFirm`'s existing dominance proof quantify over it.

**What this replaces, and what it does not.** `LogicalInduction.EfficientlyComputable`
(`Framework/Criterion.lean`) renders `def:ec` through a fuel-clocked `Nat.Partrec.Code.evaln`
interpreter — a disclosed type-`(c)` substitution, not a machine complexity class.
`MachineEfficientTrader` below is the machine class the paper actually asks for.
`PolyFueled` and `EfficientlyComputable` remain the internal certification technology every
concrete property proof uses, and `Construction/MachineEfficiency.lean` now proves the
inclusion `EfficientlyComputable Tr → MachineEfficientTrader Tr`: everything the fuel
calculus certifies is machine-efficient. The converse is not proved, so neither class
supersedes the other. What this file establishes is that the *construction's* trader
universe — what `TradingFirm` enumerates and dominates — can be the genuine machine
class.

**Unary days.** The paper measures a trader's runtime as polynomial in the day `n`, with `n`
written in unary. `unaryDay n = List.replicate n true` has length exactly `n`, so a machine
polynomial in its input length is polynomial in the day, and `Complexity.FP`'s asymptotics
are the paper's. A binary rendering would silently strengthen the class.

**Token streams, not giant numerals.** The efficiently generated object is a finite digit
stream, so the class is stated over the machine's finite output word, decoded by the
*existing* pipeline `strategyOfTokens ∘ unRpn ∘ undigitize ∘ bitsToDigits`. No second parser
is introduced, and malformed output inherits the established zero-strategy fallback.

**The semantic class and the enumeration are kept apart.** `MachineEfficientTrader` is not
defined as "occurs in the enumeration"; that every member of the class *does* occur is the
content of `exists_enumeratedTrader_eq`.

**Both halves are proved here.** Coverage is `exists_enumeratedTrader_eq`; soundness
— that every index denotes a member of the class — is
`enumeratedTrader_machineEfficient`, and it is a real theorem rather than the `rfl`
it is in the fuel setting, because a bogus index's trader is the described machine's
*truncated* behaviour and an `FP` witness for a truncation needs a clocked simulator.
`Machine/ClockedSim.lean` builds one: the description an index names is fixed, so the
simulator's control states are the described machine's own and one transition performs one
described step under a unary clock.

**No paper node.** Declarations use `lemma`/`theorem` per `scripts/lint_paper_labels.py`;
the `theorem`s here carry `def:ec` because they are what that node's machine reading asks
for.
-/
import LogicalInduction.Construction.Machine.ClockedSim
import LogicalInduction.Framework.Computable

namespace LogicalInduction

open LogicalInduction.MachineExec

/-! ## The paper-facing machine class -/

/-- Decode a machine's finite output word into the day-`n` strategy, through the existing
token pipeline. This is the only place the machine's output convention meets the trader
serialization, and it introduces no new parser. -/
def strategyOfOutput (n : ℕ) (w : List Bool) : Strategy n :=
  strategyOfTokens n (unRpn (undigitize (bitsToDigits w)))

/-- **The genuine polynomial-time trader class** (`def:ec`, machine reading). A trader is
machine-efficient when some honestly polynomial-time function of the *unary* day emits its
day-`n` strategy through the standard token decoding.

Contrast `EfficientlyComputable`, which asks for a fuel-clocked `Nat.Partrec.Code` pair; this
asks for membership in `Complexity.FP`, an ordinary multi-tape Turing-machine time class. -/
def MachineEfficientTrader (Tr : Trader) : Prop :=
  ∃ F : List Bool → List Bool, F ∈ Complexity.FP ∧
    ∀ n, strategyOfOutput n (F (unaryDay n)) = Tr.strat n

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

Named because it is the object a future soundness proof must place in `Complexity.FP`; see
the module note above for why that is not available yet. `bitsToDigits_enumeratedOutput`
below is the half of the connection that *is* available, and it is what makes the eventual
soundness proof a matter of the `FP` membership alone. -/

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
normal form `Complexity.FP` asks for, and `Machine/ClockedSim.lean`'s simulator computes the
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
