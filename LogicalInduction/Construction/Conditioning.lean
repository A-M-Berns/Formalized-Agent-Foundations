import LogicalInduction.Construction.Conditioning.Presentation
import LogicalInduction.Construction.Conditioning.Compiler
import LogicalInduction.Construction.Conditioning.PricePass
import LogicalInduction.Construction.Conditioning.FramePass
import LogicalInduction.Construction.Conditioning.Transduction
import LogicalInduction.Construction.Conditioning.TransductionFrame
import LogicalInduction.Construction.Conditioning.Endpoints

/-!
# Closure under conditioning (`LogicalInduction.Construction.Conditioning`)

The §4.7 lane: `thm:scon` (tex:1613-1618, proved in app:scon).  Conditioning a logical
inductor on a fixed sentence `ψ`, or on the growing prefix conjunctions `ψ₀ ⋏ ⋯ ⋏ ψₙ` of an
efficiently computable sentence sequence, again yields a logical inductor — of the
conditioned market, over the extended process.

`Properties/Conditioning.lean` states that over an arbitrary inductor, taking the conditioned
market's computability and the efficiency of the *translated* trader as hypotheses.  What
this directory adds is the construction that discharges them: the conditioned market as an
exact rational program, and the trader translation as a genuine transducer, certified twice —
once in the `dd:fuel` calculus and once as a `Complexity.FP` machine function, because
`thm:scon` is stated at both quantifiers and neither certificate implies the other.

## The presentation and the market

* `Presentation` — the `ConditioningPresentation` data `thm:scon` takes, constructed in three
  forms so that no caller has to assume one: the paper's fixed `Θ ∪ {ψ}` case, the compact
  growing form whose certificate emits the actual conjunction code at the write-out class
  `BigSentenceCodes`, and the prefix conjunctions of an arbitrary e.c. sequence, which is the
  paper's own quantifier for the growing form.
* `Compiler` — the conditioned market `P(φ | ψ)` as an exact rational program over the base
  market's own quote table, the finite denominator patch and the price floor it consumes, the
  flat token transducer in the contracted stream, and the digit-metered residual, whose guard
  is what keeps the rewrite polynomial when a token may be exponential in the day.

## The translation, twice

The same run-aware automaton is driven by two clients that meter differently.

* `PricePass`, `FramePass` — the `dd:fuel` rendering in the RPN *symbol* model, where a
  sentence slot is a whole token run: the automaton and the price rewrite, then the frame
  legs, the two-leg join and the class-preservation endpoints
  `conditionedTranslation_preserves_ecRpn` / `eventualConditionedTranslation_preserves_ecRpn`.
  Namespace `RpnConditioning`.
* `Transduction`, `TransductionFrame` — the same transducer in the machine model, as a client
  of `Framework/Machine/TokenFold.lean`'s block fold, so the rewrite is an honest
  `Complexity.FP` function of the trader's serialized stream: the automaton and the passes
  over a priced stream, then the frame legs, the assembled transduction and the transports
  `conditionedTranslation_preserves_machine` /
  `eventualConditionedTranslation_preserves_machine`.  Namespace `CondStep`.

## The endpoints

* `Endpoints` — the criterion-level `lic_conditioned*` family in both trader classes, built
  from operational witnesses that discharge both translation certificates at once, and the
  same theorem made unconditional over the constructed `LIA`, with
  `exists_growing_conditioned_machine_inductor` as its non-vacuity witness at a strictly
  growing condition process.

The freeze lane this one shares its token machinery with — the `def:lia` quote-table freeze,
its `Complexity.FP` recognizer kit and the corrected `thm:ifp` — is
`Construction/Freeze.lean`, which sits partly upstream (`Freeze/Prefix.lean`) and partly
downstream (`Freeze/Compiler.lean`, `Freeze/Step.lean`) of the modules here.
-/
