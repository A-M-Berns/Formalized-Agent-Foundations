import LogicalInduction.Framework.Machine.TraderMachine
import LogicalInduction.Framework.Emission.WriteOut

/-!
# From a fuel certificate into `def:ec`

`def:ec` (tex:753) is ordinary polynomial time and is defined in `Framework/Criterion.lean`
as `EfficientlyComputable`; `def:lic` (tex:657) quantifies over it there, as
`IsLogicalInductor`. This module is the one crossing between the `dd:fuel` certificate
calculus and that class, together with the two no-exploitation forms the §4 property proofs
invoke for their concretely constructed traders.

* `PolyFueledTrader.toEfficientlyComputable` — every fuel-clocked certificate (`dd:fuel`) is
  efficiently computable in the paper's sense, proved through a real `evaln` →
  Turing-machine compiler. This is what makes the fuel calculus a *certification device* for
  `def:ec` rather than a substitution for it: nothing certified in the fuel model is outside
  `def:ec`, so a theorem quantifying over `EfficientlyComputable` is at least as strong as
  the same theorem over `PolyFueledTrader`.
* `IsLogicalInductor.noExploitTok` / `.noExploitDigit` — `def:lic`'s no-exploitation
  conclusion packaged at the token- and digit-metered certificates, so a property proof that
  builds its exploiting trader in the emission calculus never names the bridge.

The compiler chain, and where each link lives:

* `Machine/EvalnCompiler.lean` — `compiledTM` compiles an arbitrary `Nat.Partrec.Code`
  into a `complexitylib` register machine, and `codeVals_encodes` proves its answer
  registers hold `Nat.Partrec.Code.evaln`'s tag and value, for all eight constructors.
* `Machine/EvalnRegBound.lean` — `codeRegBound` bounds every register the compiled
  machine holds, `codeMachineTime` bounds its steps, `compiledTM_hoareTime` proves the
  machine meets that bound, and `codeMachineTime_poly` makes the bound polynomial in
  the size parameter, for each fixed code.
* `Machine/TraderMachine.lean` — `traderMachine` measures the day, evaluates the clock
  polynomial, runs the length program, and emits one clamped digit per token the token
  program returns; `traderOutput_mem_FP` places its output function in `Complexity.FP`.
* `Machine/DigitBits.lean` — the three-bits-per-digit rendering the machine emits and
  `EfficientlyComputable` reads back, and the clamp `undigitize` licenses.

**Naming.** After this module there is one efficient-trader class and one criterion, and
neither carries a `Machine` marker. Where the prefix survives it names the *metering model
of a certificate*; `LogicalInduction.lean`'s naming conventions state the rule once.

**Design: the inclusion is one-directional.**  The converse — an `EfficientlyComputable`
trader need not carry a fuel certificate — is neither proved nor claimed, and nothing
depends on it: `def:ec` and `def:lic` are stated over the paper's class, and the fuel
calculus only ever appears on the *producing* side. The `dd:fuel` model card
(`Framework/Emission/Computable.lean`) defines what `PolyFueledTrader` means and states the
open calibration, and `LogicalInduction/README.md` carries the standing disclosure.
-/

namespace LogicalInduction

open LogicalInduction.TraderMachine

/-! ## The bridge -/

/-- **Every fuel-certified trader is efficiently computable.** Given the two codes and the
polynomial clock `PolyFueledTrader` names, `traderMachine` computes the trader's
day-`n` serialization in polynomial time, and the token pipeline
`strategyOfTokens ∘ unRpn ∘ undigitize ∘ bitsToDigits` reads it back as the same day-`n`
strategy. The machine emits each digit clamped at the terminator `4`, which
`undigitize_map_min_four` shows the pipeline cannot see.
Paper node: `def:ec` -/
theorem PolyFueledTrader.toEfficientlyComputable {Tr : Trader} (h : PolyFueledTrader Tr) :
    EfficientlyComputable Tr := by
  obtain ⟨lc, tc, a, k, hTr⟩ := h
  refine ⟨traderOutput lc tc a k, traderOutput_mem_FP lc tc a k, fun N => ?_⟩
  rw [← hTr]
  show strategyOfOutput N (traderOutput lc tc a k (unaryDay N)) = _
  rw [strategyOfOutput, bitsToDigits_traderOutput, length_unaryDay,
    undigitize_map_min_four]
  rfl

/-! ## No exploitation, at the emission calculus's own certificates

The §4 property proofs build their exploiting traders in the token or digit emission model
(`Framework/Emission/RpnEmission.lean`). These two lemmas compose the emission constructors
with the bridge above, so such a proof contradicts `def:lic` directly and the crossing into
`def:ec` happens once, here. -/

/-- Token-model no-exploitation: no trader with a token-metered certificate exploits a
logical inductor.
Paper node: `def:lic` -/
lemma IsLogicalInductor.noExploitTok {P : History} {DP : DeductiveProcess}
    [hLI : IsLogicalInductor P DP] :
    ∀ Tr : Trader, EfficientlyComputableTok Tr → ¬ Tr.Exploits P DP :=
  fun Tr h => hLI.noExploit Tr (PolyFueledTrader.ofTokenEmitter h).toEfficientlyComputable

/-- Digit-model no-exploitation, through the emission constructor.
Paper node: `def:lic` -/
lemma IsLogicalInductor.noExploitDigit {P : History} {DP : DeductiveProcess}
    [hLI : IsLogicalInductor P DP] :
    ∀ Tr : Trader, EfficientlyComputableDigit Tr → ¬ Tr.Exploits P DP :=
  fun Tr h => hLI.noExploit Tr (PolyFueledTrader.ofDigitEmitter h).toEfficientlyComputable

end LogicalInduction
