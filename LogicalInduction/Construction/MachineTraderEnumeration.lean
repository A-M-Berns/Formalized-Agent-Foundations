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
`MachineEfficientTrader` below is the machine class the paper actually asks for. **Neither
supersedes the other yet:** `PolyFueled` and `EfficientlyComputable` remain the internal
certification technology every concrete property proof uses, and the inclusion
`PolyFueled → Complexity.FP` is Stage 2 and is not started. What this file establishes is
that the *construction's* trader universe — what `TradingFirm` enumerates and dominates —
can be the genuine machine class.

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
content of `exists_enumeratedMachineTrader_eq`.

**Soundness is not proved here, and the reason is structural.** The converse — that every
index denotes a member of the class — is `rfl`-shaped in the fuel setting but a real theorem
at a machine class, because a bogus index's trader is the machine's *truncated* behaviour and
exhibiting an `FP` witness for a truncation requires a clocked simulator. complexitylib has
one (`UTM.ClockedUtm`, with both halt and timeout branches proved), but reaching it means
importing `UTM.ClockConstructible` and the counter subroutines, which are outside the closure
this file otherwise uses. `notes/complexitylib-adoption.md` §V.3 records the diagnosis and its
cost. Nothing downstream needs it: `TradingFirm` consumes coverage alone.

**No paper node.** Declarations use `lemma`/`theorem` per `scripts/lint_paper_labels.py`;
the `theorem`s here carry `def:ec` because they are what that node's machine reading asks
for.
-/
import LogicalInduction.Construction.Machine.DescExec
import LogicalInduction.Construction.TraderEnumeration

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
def enumeratedMachineTrader (i : ℕ) : Trader where
  strat n := strategyOfTokens n (unRpn (undigitize (machineTokens i n)))

/-- The enumeration's day-`n` strategy, unfolded. -/
lemma enumeratedMachineTrader_strat (i n : ℕ) :
    (enumeratedMachineTrader i).strat n
      = strategyOfTokens n (unRpn (undigitize (machineTokens i n))) := rfl

/-! ## The function an index computes

Named because it is the object a future soundness proof must place in `Complexity.FP`; see
the module note above for why that is not available yet. `bitsToDigits_enumeratedOutput`
below is the half of the connection that *is* available, and it is what makes the eventual
soundness proof a matter of the `FP` membership alone. -/

/-- The function an index computes: the described machine's output word on its input, or the
empty word if the indexed clock runs out. -/
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


/-! ## Coverage

The central Stage-3 theorem, and the one `TradingFirm` consumes.

Note which half of the usual soundness/coverage pair this is.
`Construction/TradingFirm.lean` takes `hcov : ∃ j, enumeratedTrader j = Tr` and nothing else,
so coverage is exactly what makes the dominance proof quantify over the machine class.
Soundness — that *every* index denotes a machine-efficient trader — is a separate quality
claim, and at a machine class it is a real theorem rather than the `rfl` it is in the fuel
setting. It needs a clocked simulator, and is not available here; see
`notes/complexitylib-adoption.md` §V.3 for the diagnosis and its cost. -/

/-- **Enumeration coverage.** Every machine-efficient trader occurs at some index, as an
exact equality of traders — not merely eventual agreement.

The chain: the class witness lies in `Complexity.FP`; the fork's
`exists_desc_computesInTime_clock` turns that into a `TMDesc` computing it under a clock in
the index's own normal form; bumping the coefficient makes that clock *strictly* dominate,
which is the one step of slack the budgeted evaluator needs in order to observe a halt; and
`machineTokens_eq_of_computesInTime` then says the index emits exactly the witness's output
word on every unary day.
Paper node: `def:ec` -/
theorem exists_enumeratedMachineTrader_eq (Tr : Trader) (hTr : MachineEfficientTrader Tr) :
    ∃ i : ℕ, enumeratedMachineTrader i = Tr := by
  obtain ⟨F, hF, hstrat⟩ := hTr
  obtain ⟨d, a, k, T, hd, hak⟩ := exists_desc_computesInTime_clock hF
  refine ⟨MachineTraderProgram.index ⟨d, a + 1, k⟩, Trader.ext (funext fun n => ?_)⟩
  have htok : machineTokens (MachineTraderProgram.index ⟨d, a + 1, k⟩) n
      = bitsToDigits (F (unaryDay n)) := by
    refine machineTokens_eq_of_computesInTime (T := T) ?_ n ?_
    · rw [progDesc_index]; exact hd
    · rw [progClock_index, length_unaryDay]; exact lt_clock_succ (hak n)
  rw [enumeratedMachineTrader_strat, htok, ← hstrat n, strategyOfOutput]


end LogicalInduction
