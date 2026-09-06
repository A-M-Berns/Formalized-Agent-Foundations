import LogicalInduction.Framework.Foundations
import LogicalInduction.Framework.Asymptotics
import LogicalInduction.Framework.Criterion
import LogicalInduction.Framework.Compactness
import LogicalInduction.Framework.Affine
import LogicalInduction.Framework.BooleanWorlds
import LogicalInduction.Framework.ROI
import LogicalInduction.Framework.Expectations
import LogicalInduction.Framework.MachineEfficiency
import LogicalInduction.Framework.Theory.RepresentsComputations
import LogicalInduction.Framework.Theory.R0Instances
import LogicalInduction.Framework.Theory.SubstOccurrence
import LogicalInduction.Framework.Theory.QuoteRepresentability
import LogicalInduction.Framework.Theory.DerivationSize
import LogicalInduction.Framework.Theory.BoundedConsistency
import LogicalInduction.Framework.Emission.Computable
import LogicalInduction.Framework.Emission.Emission
import LogicalInduction.Framework.Emission.DigitArith
import LogicalInduction.Framework.Emission.CodeSource
import LogicalInduction.Framework.Emission.RpnSentence
import LogicalInduction.Framework.Emission.RpnSplice
import LogicalInduction.Framework.Emission.RpnEmission
import LogicalInduction.Framework.Emission.RpnComputation
import LogicalInduction.Framework.Emission.WriteOut
import LogicalInduction.Framework.Emission.FreezeTransducer
import LogicalInduction.Framework.Machine.EvalnCompiler
import LogicalInduction.Framework.Machine.EvalnRegBound
import LogicalInduction.Framework.Machine.CodeSteps
import LogicalInduction.Framework.Machine.FPFold
import LogicalInduction.Framework.Machine.TokenFold
import LogicalInduction.Framework.Machine.DigitBits
import LogicalInduction.Framework.Machine.DigitArithFP
import LogicalInduction.Framework.Machine.TraderMachine
import LogicalInduction.Framework.Machine.WriteOutMachine
import LogicalInduction.Framework.Machine.Descriptions
import LogicalInduction.Framework.Machine.ClockedSim

/-!
# Framework (`LogicalInduction.Framework`)

The paper's §2–3 objects together with the substrate the later directories consume.  A
module belongs here when it is one of those objects or serves `Properties/` (§4),
`Construction/` (§5) or both; several modules here — all of `Theory/`, the description
interpreter and clocked simulator of `Machine/`, `Emission.RpnComputation` — are consumed
only by `Construction/`.  The rule is closure, not precedence: nothing under `Framework/`
imports outside `Framework/`, so `lake build LogicalInduction.Framework` is the gate for
all of it.

The layer has four parts.  The modules named directly below are the paper's own §2–3
objects.  `Theory/` is the background first-order theory `Θ` the §4.9–4.10 endpoints reason
inside.  `Emission/` is the `dd:fuel` certificate calculus that renders `def:ec`.
`Machine/` compiles a fuel certificate into the ordinary machine `def:ec` is actually read
on, and supplies the polynomial-time word arithmetic the syntactic transports need.

## The paper's objects

* `Foundations` — the object language, valuations and histories: sentences of the ambient
  propositional language (tex:560), the paper's valuations (`def:market`) and the
  day-indexed history a feature's denotation is a function of.
* `Asymptotics` — the single limit vocabulary `≈ₙ`, `≳ₙ`, `≲ₙ`, "eventually within ε" and
  `ConvergesTo` (`dd:asymp`), never redefined per file.
* `Criterion` — expressible features (`def:valfeature`, `def:tf`), trading strategies and
  traders (`def:tradestrat`, `def:trader`), exploitation (`def:exploitation`), deductive
  processes (`def:dedproc`), worlds (`def:world`), and the criterion `def:lic` over the
  fuel-certified class.
* `Compactness` — propositional compactness over Cantor space: per-stage satisfiability of
  a deductive process yields one world consistent with every stage.
* `Affine` — trade magnitude and net-worth bounds (`def:tradermag`, `def:bap`), the
  `Strategy` scale-and-join algebra, and affine combinations of sentences
  (`def:affcomsen`) with their pointwise operations.
* `BooleanWorlds` — the Boolean reading `ℕ → Bool` of a world, its finite-support
  restrictions `FiniteWorld B` and the executable rational payouts over them, and the
  product-space compactness the §4 affine arguments consume
  (`eventually_affineValue_gt_of_theory`).
* `ROI` — the repeatable return-on-investment lemma (`lem:type3`, `def:roi`) and the
  budgeted-trader machinery its proof needs (`def:emulatabletraders`).
* `Expectations` — logically uncertain variables (`def:luv`), the ℙ̄-generable class
  (`def:ece`), the threshold-code interfaces, the finite price sum `def:e`, and the
  rational-cut semantics by which a completed world values a LUV (`lem:conluvapprox`).
* `MachineEfficiency` — `IsMachineLogicalInductor`, `def:lic` at the paper's own quantifier
  over `MachineEfficientTrader`, and the bridge `EfficientlyComputable.toMachine` that lands
  a fuel certificate inside that class.

## `Theory/` — the background theory `Θ`

* `Theory.RepresentsComputations` — the paper's standing §2 assumption on the first-order
  background theory `Θ` ("Representing computations", tex:600-606), and the two literals it
  yields over a represented value graph.
* `Theory.R0Instances` — non-vacuity of that assumption: `𝗣𝗔⁻`, `𝗜𝚺₁` and `𝗣𝗔` satisfy it.
  Every registered instance is `ℕ`-sound, and the module states in full why that is a gap in
  the non-vacuity argument rather than a hypothesis any endpoint inherits.
* `Theory.SubstOccurrence` — bound-variable occurrence for Foundation semiformulas
  (`Semiformula.Mentions`, counted under quantifiers) and the rewrite-transport lemmas over
  it.  Foundation records occurrence for terms only; the representability side conditions
  need it for formulas.
* `Theory.QuoteRepresentability` — the object-level quotation schema the reflection
  endpoints read their quote codes off (`dd:quote-code`), with the single-valuedness lemmas
  `codeAux_uniq` / `code_uniq` that both it and `Theory.R0Instances` rest on.
* `Theory.DerivationSize` — the symbol count `dSize` of a Foundation derivation code
  (`dd:symbolcount`), tied to Foundation's own constructors by equation, with the converse
  bound `le_G_dSize` that makes a symbol-bounded proof search finite, and the primitive
  recursiveness that makes that search an algorithm rather than an existence statement.
* `Theory.BoundedConsistency` — bounded provability over Foundation's internal derivations,
  its computable decider, and the paper's finite-consistency predicate `Con(Θ)(ν)` (§4.10,
  the substrate of `thm:pac`, `thm:pazfc` and `thm:incons`).

## `Emission/` — the `def:ec` certificate calculus (`dd:fuel`)

* `Emission.Computable` — the fuel-clocked certificate model, `PolyFueled` and
  `PolySegStream` and their closure algebra, with the `dd:fuel` model card stating what the
  calculus does and does not settle about `def:ec`.
* `Emission.Emission` — bounded-simulation compilers over `Nat.Partrec.Code` and the clocked
  token-emission layer they feed; `codeEvalBound` is the value bound for a fixed code.
* `Emission.DigitArith` — bignum arithmetic on digit streams, so emission is metered in
  token *bits* rather than in code values.
* `Emission.CodeSource` — the naming a polynomial-time writer can emit: the postfix tag
  stream `Code.sourceTags` / `Code.sourceNat` of a machine's syntax tree, its total
  primitive recursive inverse `Code.ofSource`, and the length and peel-step bounds that make
  a machine *name* writable under `def:ec` (§4.10, tex:1931-1933).
* `Emission.RpnSentence` — sentences as Polish-notation symbol runs (one token per formula
  symbol), so stream length tracks symbol count rather than code size.
* `Emission.RpnSplice` — the token-metered sentence-sequence class `RpnSentenceCodes` and
  its combinators.
* `Emission.RpnEmission` — realizes those sequences as emitted digit streams, and states the
  `def:lic` no-exploitation forms over them.
* `Emission.RpnComputation` — primitive recursion for the Polish-notation contraction, which
  the trading firm's compiler runs to decode candidate traders.
* `Emission.WriteOut` — the write-out certificate ladder the §4 tail actually binds:
  `BigSentenceCodes`, `BigDigits`, `DigitRatCodes`, `DigitMachineCodes`, `BigTokenStream`
  and `BigSpliceStream`, which meter how many symbols a writer emits and bound no token's
  value, as `def:ec` does.
* `Emission.FreezeTransducer` — the price freeze `EF.freezeOn` on the feature syntax and the
  bounded streaming transducer `EF.freezeTokenRunOn` that realizes it on a token word: what
  §4.6 transports an exploiting trader with.

The four `Rpn*` modules carry the token-metered sentence classes.  Those classes survive on
the LUV threshold lane and as strictness foils against the write-out ladder in
`Emission.WriteOut`; the sentence slots of `def:ec` itself are discharged by
`BigSentenceCodes`.

## `Machine/` — from a fuel certificate to a machine

`def:ec` is read on ordinary machines (`MachineEfficientTrader`), so a fuel certificate has
to be *compiled* into one.  This subdirectory is that compiler together with its accounting,
the polynomial-time word arithmetic the syntactic transports need, and the description
interpreter the §5 enumeration is indexed by.

* `Machine.EvalnCompiler` — `Nat.Partrec.Code` into `complexitylib` register machines,
  proved against Mathlib's clocked `evaln` rather than the unclocked `eval`.
* `Machine.EvalnRegBound` — how large the compiled machines' registers grow and how long
  they run.
* `Machine.CodeSteps` — `codeEvalSteps`, the interpreter-invocation count of a fixed code,
  polynomial in the fuel; the *time* counterpart of `Emission.Emission`'s value bound.
* `Machine.FPFold` — the reusable streaming-fold core for exhibiting a syntactic rewrite of
  a serialized stream as a `Complexity.FP` function.
* `Machine.TokenFold` — token-level transducers on bit words, the layer the conditioning and
  freeze transports run on.
* `Machine.DigitBits` — the bit rendering of a digit stream (`digitBits`, `digitsToBits`)
  and the round trip through which `MachineEfficientTrader` decodes an output word.
* `Machine.DigitArithFP` — base-four arithmetic on digit words inside `Complexity.FP`
  (`addW`, `subW`, `leW`, `predW`, `sqrtRemW`, `unpairFstW` / `unpairSndW`), each with its
  value specification; it serves `app:ifp`.
* `Machine.TraderMachine` — the machine computing an `EfficientlyComputable` trader's day-`n`
  serialization: the last link of `EfficientlyComputable.toMachine`.
* `Machine.WriteOutMachine` — the machine-side realization of the write-out ladder.
* `Machine.Descriptions` — executable bounded execution of a finite `complexitylib` machine
  description, and the compiler-facing token evaluator `machineTokens` built on it.  This is
  what makes the §5 machine-trader enumeration effective; read its module docstring for why
  the executable object is a *description* rather than a machine.
* `Machine.ClockedSim` — the clocked simulator for a fixed description, and the proof that
  the truncated run is in `Complexity.FP`: the soundness half of that enumeration.
-/
