import LogicalInduction.Construction.ClockedSim
import LogicalInduction.Construction.Primcodable
import LogicalInduction.Framework.Emission.Computable
import LogicalInduction.Framework.Machine.WriteOutMachine

/-!
# `def:ec` — the machine trader class and its enumeration

This module renders `def:ec` (tex:753) at the paper's own quantifier: ordinary machine
polynomial time, through `Complexity.FP` from the pinned complexitylib fork. It defines
`enumeratedTrader : ℕ → Trader` — run the described machine on the unary day under the
indexed clock, then decode — and `enumeratedOutput : ℕ → List Bool → List Bool`, the
function an index computes.

Both halves of "this is an enumeration *of* the class" are proved here.
`enumeratedOutput_mem_FP` and `enumeratedTrader_efficient` are soundness: every index
denotes a member of the class. `exists_enumeratedTrader_eq` is coverage: every
efficiently computable trader occurs at some index, as an exact equality of traders. Coverage is
what `Construction/TradingFirm.lean` consumes — `trading_firm_dominance_of_covered` takes
`hcov : ∃ j, enumeratedTrader j = Tr` and nothing else — so it is what makes the dominance
proof quantify over `def:ec`.

Three choices shape the rendering.

*Unary days.* The paper measures a trader's runtime as polynomial in the day `n` written in
unary, and `unaryDay n = List.replicate n true` has length exactly `n`, so
`Complexity.FP`'s asymptotics are the paper's; a binary rendering would silently strengthen
the class.

*Token streams, not giant numerals.* The class is stated over the machine's finite output
word, decoded by the existing pipeline
`strategyOfTokens ∘ unRpn ∘ undigitize ∘ bitsToDigits`; no second parser is introduced, and
malformed output inherits the established zero-strategy fallback.

*The semantic class and the enumeration are kept apart.* `EfficientlyComputable` is not
defined as "occurs in the enumeration"; that every member does occur is the content of
`exists_enumeratedTrader_eq`. Soundness is correspondingly a real theorem rather than the
`rfl` it is in the fuel setting, because a bogus index's trader is the described machine's
*truncated* behaviour, and an `FP` witness for a truncation needs the clocked simulator of
`Construction/ClockedSim.lean`: the description an index names is fixed, so the simulator's
control states are the described machine's own and one transition performs one described
step under a unary clock.

Relation to the certificate layer (`dd:fuel`): `Framework/Efficiency.lean` proves
`PolyFueledTrader Tr → EfficientlyComputable Tr`; the converse is not proved and is
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
`Construction/ClockedSim.lean`.
`bitsToDigits_enumeratedOutput` is the other half of the connection — it identifies this
function's output on a unary day with the index's token stream — and together the two reduce
`enumeratedTrader_efficient` to that `FP` membership. -/

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

Every index denotes an efficiently computable trader. The index's clock is a `Polynomial ℕ` in the
normal form `Complexity.FP` asks for, and `Construction/ClockedSim.lean`'s simulator
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

/-- **Enumeration soundness** (`def:ec`): every index denotes an efficiently computable trader.
Together with `exists_enumeratedTrader_eq` this makes the enumeration an enumeration
*of* the efficiently computable traders, not merely one that covers them.
Paper node: `def:ec` -/
lemma enumeratedTrader_efficient (i : ℕ) :
    EfficientlyComputable (enumeratedTrader i) := by
  refine ⟨enumeratedOutput i, enumeratedOutput_mem_FP i, fun n => ?_⟩
  rw [enumeratedTrader_strat, strategyOfOutput, bitsToDigits_enumeratedOutput]

/-! ## Coverage

The other half, and the one `TradingFirm` consumes.

`Construction/TradingFirm.lean` takes `hcov : ∃ j, enumeratedTrader j = Tr` and nothing else,
so coverage is exactly what makes the dominance proof quantify over the machine class. -/

/-- **Enumeration coverage.** Every efficiently computable trader occurs at some index, as an
exact equality of traders — not merely eventual agreement.

The chain: the class witness lies in `Complexity.FP`; the fork's
`exists_desc_computesInTime_clock` turns that into a `TMDesc` computing it under a clock in
the index's own normal form; bumping the coefficient makes that clock *strictly* dominate,
which is the one step of slack the budgeted evaluator needs in order to observe a halt; and
`machineTokens_eq_of_computesInTime` then says the index emits exactly the witness's output
word on every unary day.
Paper node: `def:ec` -/
lemma exists_enumeratedTrader_eq (Tr : Trader) (hTr : EfficientlyComputable Tr) :
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

/-! ## Primitive recursiveness of machine-metered data

`BigTokenStream.primrec` (`Framework/Emission/WriteOut.lean`) reads `Primrec` straight off
the fuel certificate's own digit stream.  The machine classes have only `Complexity.FP`
membership, and `Complexity.FP ⊆ Primrec` is not available — `complexitylib` carries no
computability bridge at all.  What stands in for it, at the two shapes this development
needs, is the coverage argument of this file, reused verbatim: an `FP` witness names a
description and a clock (`exists_desc_computesInTime_clock`), the budgeted evaluator recovers
that witness's output on every unary day, and `primrec_evalHalted` is that run's primitive
recursiveness.  This is why the lemmas live here rather than beside their classes:
`MachineTokenStream` and `UnaryRuler` are `Framework/`, the described-machine simulator is
`Construction/`.

The shapes need different read-offs.  `MachineTokenStream.primrec` wants the run's
*tokens*, which is `machineTokens` and `primrec_machineTokens`.  `UnaryRuler.primrec` wants
the run's raw output word *length*, because a ruler's length is its value — and
`machineTokens` cannot serve it, since `bitsToDigits` loses the word's length modulo three.
`MachineDigits.primrec` and `MachineSentenceCodes.primrec` are read off the token-level one:
the first takes the head of a one-token stream, the second parses it. -/

/-- Read a finished run's raw output word; the timeout fallback lives here, on
`Option CodedCfg`, exactly as `tokensOf` puts the token-level one there. -/
private def wordOf : Option CodedCfg → List Bool
  | none => []
  | some c => codedOutput c

private lemma primrec_wordOf : Primrec wordOf :=
  (Primrec.option_casesOn Primrec.id (Primrec.const [])
    (Primrec.to₂ (primrec_codedOutput.comp Primrec.snd))).of_eq fun o => by cases o <;> rfl

private lemma enumeratedOutput_eq_wordOf (i : ℕ) (x : List Bool) :
    enumeratedOutput i x = wordOf (evalHalted (progDesc i) (progClock i x.length) x) := by
  rw [enumeratedOutput]
  cases evalHalted (progDesc i) (progClock i x.length) x <;> rfl

private lemma primrec_enumeratedOutput_day (i : ℕ) :
    Primrec fun n => enumeratedOutput i (unaryDay n) := by
  refine (primrec_wordOf.comp (primrec_evalHalted.comp (Primrec.pair
    (Primrec.const (progDesc i))
    (Primrec.pair (primrec_progClock.comp (Primrec.const i) Primrec.id)
      primrec_unaryDay)))).of_eq fun n => ?_
  rw [enumeratedOutput_eq_wordOf, length_unaryDay]
  rfl

/-- **A unary ruler is primitive recursive.**  The count-level twin of
`MachineTokenStream.primrec`, proved by the same coverage bridge and for the same reason:
`Complexity.FP ⊆ Primrec` is not available, so the route is to name a description and a clock
for the ruler's own `FP` witness (`exists_desc_computesInTime_clock`), observe that the
budgeted evaluator recovers that witness's output word verbatim (`evalHalted_complete`), and
read the count off as that word's *length*.

The token-level bridge cannot be reused here: `machineTokens` hands back
`bitsToDigits` of the output word, which loses the word's length modulo three, and a ruler's
length *is* its value. -/
lemma UnaryRuler.primrec {f : ℕ → ℕ} (h : UnaryRuler f) : Primrec f := by
  have hF : (fun z : List Bool => List.replicate (f z.length) false) ∈ Complexity.FP := h
  obtain ⟨d, a, k, T, hd, hak⟩ := exists_desc_computesInTime_clock hF
  have hout : ∀ n, enumeratedOutput (MachineTraderProgram.index ⟨d, a + 1, k⟩) (unaryDay n)
      = List.replicate (f n) false := by
    intro n
    have hd' : ((progDesc (MachineTraderProgram.index ⟨d, a + 1, k⟩)).toTM).ComputesInTime
        (fun z : List Bool => List.replicate (f z.length) false) T := by
      rw [progDesc_index]; exact hd
    have hclock : T (unaryDay n).length
        < progClock (MachineTraderProgram.index ⟨d, a + 1, k⟩) n := by
      rw [progClock_index, length_unaryDay]; exact lt_clock_succ (hak n)
    obtain ⟨c, hc, hcod⟩ := evalHalted_complete hd' (unaryDay n) hclock
    rw [enumeratedOutput_eq_wordOf, length_unaryDay, hc, wordOf, hcod, length_unaryDay]
  refine (Primrec.list_length.comp
    (primrec_enumeratedOutput_day (MachineTraderProgram.index ⟨d, a + 1, k⟩))).of_eq fun n => ?_
  rw [hout n, List.length_replicate]

/-- **A machine-metered write-out stream is primitive recursive.**  The machine twin of
`BigTokenStream.primrec`, proved through this file's coverage bridge rather than through a
general `Complexity.FP ⊆ Primrec`, which is not available.  Every consumer that used to
read primitive recursiveness off a fuel certificate — `AffineCombination.PolySequence.primrec`,
`PolyTradeEmulatable.trades_primrec`, `MachineSpliceStream.feature_primrec` — reaches it
through this lemma once its certificate is machine-metered. -/
lemma MachineTokenStream.primrec {t : ℕ → List ℕ} (h : MachineTokenStream t) :
    Primrec t := by
  obtain ⟨F, hF, -, hdec⟩ := h
  obtain ⟨d, a, k, T, hd, hak⟩ := exists_desc_computesInTime_clock hF
  have htok : ∀ n, machineTokens (MachineTraderProgram.index ⟨d, a + 1, k⟩) n
      = bitsToDigits (F (unaryDay n)) := by
    intro n
    refine machineTokens_eq_of_computesInTime (T := T) ?_ n ?_
    · rw [progDesc_index]; exact hd
    · rw [progClock_index, length_unaryDay]; exact lt_clock_succ (hak n)
  have hprim : Primrec fun n =>
      machineTokens (MachineTraderProgram.index ⟨d, a + 1, k⟩) n :=
    primrec_machineTokens.comp
      (Primrec.const (MachineTraderProgram.index ⟨d, a + 1, k⟩)) Primrec.id
  refine (undigitize_prim.comp hprim).of_eq fun n => ?_
  rw [htok n]
  exact hdec n

/-- **A machine-metered written-out value is primitive recursive.**  The machine twin of
`BigDigits.primrec` (`Framework/Emission/DigitArith.lean`), and the shortest of the three
read-offs: `MachineDigits x` is by definition `MachineTokenStream (fun n => [x n])`, so the
value is the head of a primitive recursive one-token list.  No digit recurrence is needed —
the fuel side has to reassemble `x m` from `dig4`/`len4` because its certificate only gives
random access to digits, whereas the machine certificate emits the whole block.

As with the fuel-side twin, reassembling an exponentially large value here is legitimate
because `Primrec` carries no time budget; what would be a leak is using the result as a
`PolyFueled` or `Complexity.FP` certificate, which nothing does.  Consumers:
`MachineRatCodes.computable` (`Construction/Quotation/MarketQuoteCodes.lean`), by way of
`MachineRatCodes.toMachineDigits`. -/
lemma MachineDigits.primrec {x : ℕ → ℕ} (h : MachineDigits x) : Primrec x :=
  (Primrec.list_headI.comp (MachineTokenStream.primrec h)).of_eq fun _ => rfl

/-- **A machine-metered written-out sentence sequence is primitive recursive.**  The machine
twin of `BigSentenceCodes.primrec` (`Construction/Primcodable.lean`): the same parse read-off
(`parseRpnC_prim`, `parseRpnC_eq`) over `MachineTokenStream.primrec` in place of
`BigTokenStream.primrec`.  Primitive recursion carries no time budget, so reassembling an
exponentially-named code here is legitimate, exactly as on the fuel side — this is the route
by which a market quote table keyed by sentence code accepts machine-metered data.

It lives in this module rather than beside its twin because the machine token stream's
`Primrec` certificate is the coverage argument above, and `Construction/Primcodable.lean`
sits upstream of `Machine/`. -/
lemma MachineSentenceCodes.primrec {φ : ℕ → Sentence} (h : MachineSentenceCodes φ) :
    Primrec fun n => Encodable.encode (φ n) := by
  obtain ⟨s, hs, hp⟩ := h
  have hsp : Primrec s := MachineTokenStream.primrec hs
  have hparse : Primrec fun n => parseRpnC (s n).length (s n) :=
    parseRpnC_prim.comp (Primrec.list_length.comp hsp) hsp
  have hmap : Primrec fun n =>
      (parseRpnC (s n).length (s n)).map Prod.fst :=
    Primrec.option_map hparse (Primrec.fst.comp Primrec.snd).to₂
  refine ((Primrec.option_getD.comp hmap (Primrec.const 0)).of_eq fun n => ?_)
  rw [parseRpnC_eq, hp n]
  rfl

/-- The whole-value naming program extracted from a machine-metered sentence sequence.  The
machine twin of `BigSentenceCodes.exists_code`; used where a *value* code is genuinely
required (market quote tables keyed by sentence code, the conditioning compiler's naming
program), as opposed to metered emission. -/
lemma MachineSentenceCodes.exists_code {φ : ℕ → Sentence} (h : MachineSentenceCodes φ) :
    ∃ c : Nat.Partrec.Code, ∀ n, Encodable.encode (φ n) ∈ c.eval n := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp
    (Nat.Partrec.of_primrec (Primrec.nat_iff.mp (MachineSentenceCodes.primrec h)))
  exact ⟨c, fun n => by rw [hc]; exact Part.mem_some _⟩

end LogicalInduction
