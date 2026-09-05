import LogicalInduction.Framework.Asymptotics
import LogicalInduction.Framework.Foundations
import LogicalInduction.Framework.Computable
import LogicalInduction.Framework.Emission
import LogicalInduction.Framework.DigitArith
import LogicalInduction.Framework.RpnSentence
import LogicalInduction.Framework.RpnSplice
import LogicalInduction.Framework.RpnEmission
import LogicalInduction.Framework.RpnComputation
import LogicalInduction.Framework.Criterion
import LogicalInduction.Framework.MachineEfficiency
import LogicalInduction.Framework.RepresentsComputations
import LogicalInduction.Framework.BoundedConsistency
import LogicalInduction.Framework.QuoteRepresentability
import LogicalInduction.Framework.Compactness
import LogicalInduction.Framework.Affine
import LogicalInduction.Framework.ROI
import LogicalInduction.Framework.Expectations
import LogicalInduction.Framework.RationalCut
import LogicalInduction.Framework.WriteOut
import LogicalInduction.Framework.Machine.WriteOutMachine

/-!
# Framework (`LogicalInduction.Framework`)

The paper's §2–3 substrate together with the shared proof machinery every later directory
consumes: everything upstream of both `Properties/` and `Construction/`.

## Semantic substrate and the criterion

* `Foundations` — the object language, valuations and histories: sentences of the ambient
  propositional language (tex:560), the paper's valuations (`def:market`) and the
  day-indexed history a feature's denotation is a function of.
* `Criterion` — expressible features (`def:valfeature`, `def:tf`), trading strategies and
  traders (`def:tradestrat`, `def:trader`), exploitation (`def:exploitation`), deductive
  processes (`def:dedproc`), worlds (`def:world`), and the criterion over the fuel-certified
  class.
* `MachineEfficiency` — `IsMachineLogicalInductor`, `def:lic` at the paper's own
  quantifier over `MachineEfficientTrader`, and the bridge `EfficientlyComputable.toMachine`
  that lands a fuel certificate inside that class.
* `Compactness` — propositional compactness over Cantor space: per-stage satisfiability
  of a deductive process yields one world consistent with every stage.

## Efficiency, certification and emission

* `Computable` — the fuel-clocked certificate model, `PolyFueled` and `PolySegStream`
  and their closure algebra (`dd:fuel`), with the model card stating what the calculus
  does and does not settle about `def:ec`.
* `WriteOut` — the write-out certificate ladder the §4 tail actually binds:
  `BigSentenceCodes`, `BigDigits`, `DigitRatCodes`, `DigitMachineCodes`, `BigTokenStream`
  and `BigSpliceStream`, which meter how many symbols a writer emits and bound no token's
  value, as `def:ec` does.
* `Emission` — bounded-simulation compilers over `Nat.Partrec.Code` and the clocked
  token-emission layer they feed.
* `CodeSource` — the naming a polynomial-time writer can emit: the postfix tag stream
  `Code.sourceTags` / `Code.sourceNat` of a machine's syntax tree, its total primitive
  recursive inverse `Code.ofSource`, and the length and peel-step bounds that make a
  machine *name* writable under `def:ec` (§4.10, tex:1931-1933).
* `DigitArith` — bignum arithmetic on digit streams, so emission is metered in token
  *bits* rather than in code values (`dd:fuel`).
* `RpnSentence` — sentences as Polish-notation symbol runs (one token per formula
  symbol), so stream length tracks symbol count rather than code size.
* `RpnSplice` — the token-metered sentence-sequence class and its combinators.
* `RpnEmission` — realizes those sequences as emitted digit streams.
* `RpnComputation` — primitive recursion for the Polish-notation contraction, which the
  trading firm's compiler runs to decode candidate traders.

The four `Rpn*` modules carry the token-metered sentence classes. Those classes survive on
the LUV threshold lane and as strictness foils against the write-out ladder in `WriteOut`;
the sentence slots of `def:ec` itself are discharged by `BigSentenceCodes`.

## Proof theory and the background theory

* `RepresentsComputations` — the paper's standing §2 assumption on the first-order
  background theory `Θ` ("Representing computations"), and the two literals it yields over
  a represented value graph.
* `SubstOccurrence` — bound-variable occurrence for Foundation semiformulas
  (`Semiformula.Mentions`, counted under quantifiers) and the rewrite-transport lemmas over
  it. Foundation records occurrence for terms only; the representability side conditions
  need it for formulas.
* `QuoteRepresentability` — the object-level quotation schema the reflection endpoints
  read their quote codes off (`dd:quote-code`).
* `BoundedConsistency` — bounded provability over Foundation's internal derivations, its
  computable decider, and the paper's finite-consistency predicate `Con(Θ)(ν)` (§4.10,
  `dd:symbolcount`). It is what brings in `DerivationSize` and `DerivationSizeComputable`:
  the symbol count `dSize` of a Foundation derivation code, tied to Foundation's own
  constructors by equation, with the converse bound `le_G_dSize` that makes a
  symbol-bounded proof search finite, and its computability layer.

## Economics, expectations, asymptotics

* `Affine` — trade magnitude and net-worth bounds, and affine combinations of sentences
  (`def:affcomsen`).
* `ROI` — the repeatable return-on-investment lemma (`lem:type3`) and the budgeted-trader
  machinery its proof needs (`def:emulatabletraders`).
* `Expectations` — logically uncertain variables (`def:luv`), their threshold
  presentations and market expectations.
* `RationalCut` — generic bounded-cut semantics yielding completed-world LUV values.
* `Asymptotics` — the single limit vocabulary `≈ₙ`, `≳ₙ`, `≲ₙ`, "eventually within ε" and
  `ConvergesTo` (`dd:asymp`), never redefined per file.

## The machine compiler (`Framework/Machine/`)

`def:ec` is read on ordinary machines (`MachineEfficientTrader`), so a fuel certificate has
to be *compiled* into one. This subdirectory is that compiler together with its accounting
and the polynomial-time word arithmetic the syntactic transports need.

* `Machine.EvalnCompiler` — `Nat.Partrec.Code` into `complexitylib` register machines,
  proved against Mathlib's clocked `evaln` rather than the unclocked `eval`.
* `Machine.CodeSteps` — `codeEvalSteps`, the interpreter-invocation count of a fixed code,
  polynomial in the fuel; the *time* counterpart of `Emission`'s value bound.
* `Machine.EvalnRegBound` — how large the compiled machines' registers grow and how long
  they run.
* `Machine.TraderMachine` — the machine computing an `EfficientlyComputable` trader's
  day-`n` serialization: the last link of `EfficientlyComputable.toMachine`.
* `Machine.DigitBits` — the bit rendering of a digit stream (`digitBits`, `digitsToBits`)
  and the round trip through which `MachineEfficientTrader` decodes an output word.
* `Machine.FPFold` — the reusable streaming-fold core for exhibiting a syntactic rewrite of
  a serialized stream as a `Complexity.FP` function.
* `Machine.TokenFold` — token-level transducers on bit words, the layer the conditioning
  and freeze transports run on.
* `Machine.DigitArithFP` — base-four arithmetic on digit words inside `Complexity.FP`
  (`addW`, `subW`, `leW`, `predW`, `sqrtRemW`, `unpairFstW` / `unpairSndW`), each with its
  value specification. It is reached from `Construction/Witnesses/FiberTestFP.lean`, not
  from this roll-up.
* `Machine.WriteOutMachine` — the machine-side realization of the write-out ladder.
-/
