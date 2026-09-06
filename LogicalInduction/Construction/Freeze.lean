import LogicalInduction.Construction.Freeze.Prefix
import LogicalInduction.Construction.Freeze.CanonicalCodes
import LogicalInduction.Construction.Freeze.Compiler
import LogicalInduction.Construction.Freeze.RunAutomaton
import LogicalInduction.Construction.Freeze.PatternAutomaton
import LogicalInduction.Construction.Freeze.StructuredPatterns
import LogicalInduction.Construction.Freeze.CounterAutomaton
import LogicalInduction.Construction.Freeze.PayloadAutomaton
import LogicalInduction.Construction.Freeze.SegmentAutomaton
import LogicalInduction.Construction.Freeze.SegmentCounter
import LogicalInduction.Construction.Freeze.FiberTest
import LogicalInduction.Construction.Freeze.SegmentRecognizer
import LogicalInduction.Construction.Freeze.Step
import LogicalInduction.Construction.Freeze.Oracle
import LogicalInduction.Construction.Freeze.Counterexample
import LogicalInduction.Construction.Freeze.LIAPerturbation

/-!
# Closure under finite perturbations (`LogicalInduction.Construction.Freeze`)

The `thm:ifp` lane (tex:1521, with the appendix proof `app:ifp` at tex:6018).  The printed
theorem is false as stated — `Properties/FinitePerturbationCounterexample.lean` develops the
refutation, and `Counterexample` below supplies the witness it consumes — and the corrected
statement asks that the perturbation be *frozen* by a device the trader class actually admits.
This directory builds that device, at both readings of `def:ec`: the `dd:fuel` certificate
calculus and the machine class `Complexity.FP`.

Everything here answers one question: given a market that overrides finitely many early
quotes, rewrite an efficiently computable trader into one that prices the perturbed market,
without leaving the class.

## The quote-table freeze

* `Prefix` — the `dd:fuel` half: polynomial parser control (`freezeControlNat`),
  variable-width emission of the frozen suffix, exhaustive raw-code sentence matching
  (`sentenceMatches`), and lookup in the inductor's finite prefix quote table, assembled into
  `liaFreezeBefore_preserves_ecTok` (`def:lia`).  Its docstring states the disclosed boundary:
  the collapsed class asks for token-metered preservation, and the digit model is closed under
  the forward big-value operations but open under their inverses.
* `CanonicalCodes` — when the escape-leaf decode test agrees with canonical-code comparison.
  Foundation's `Formula.ofNat` discards the payload at tag `0`, so `decode` is not injective;
  the non-injectivity is caused entirely by `⊥`, and on a `⊥`-free target the test is a
  comparison against a fixed numeral needing no square root.
* `Compiler` — the symbol-level freeze as a rewrite of the *flat* RPN token stream, which is
  the stream a machine actually holds, with the run-level lookup tables and the transducer.

## The machine-class recognizer kit

The machine reading needs to decide, in polynomial time, "does this word's token run denote
`ψ`", for an arbitrary target.  That decision is regular except for one `aⁿbⁿ` constraint —
a structured arithmetic leaf's unary length field must equal its payload's token count — so
the kit splits it into a finite-state half, a one-counter half, and a decode test.

* `RunAutomaton` — `BlockAutomaton` (bounded finite control) and `BlockMachine` (an arbitrary
  word state growing by a constant per token), each with its `Complexity.FP` fold.
* `PatternAutomaton` — the legacy grammar's spelling characterization as a `BlockAutomaton`,
  isolating everything non-unconditional in the interface `HoleGuards`.
* `StructuredPatterns` — the full grammar's characterization with no side condition:
  segment patterns, of which a structured paper-prime block is one variable-width segment.
* `CounterAutomaton` — the one-counter inhabitant of `BlockMachine`, which is what decides
  the length identification a finite control cannot.
* `PayloadAutomaton` — an exact finite automaton for the payloads parsing to one fixed
  formula code, by top-down predictive parsing against an obligation stack.
* `SegmentAutomaton`, `SegmentCounter` — the regular half and the counting half of
  `SegMatch`, and the proof that their conjunction is exactly `SegMatch`.
* `FiberTest` — `HoleGuards` inhabited: the escape-leaf decode test run on digit words inside
  `Complexity.FP`.
* `SegmentRecognizer` — the three assembled into the unconditional polynomial-time decision.

## The endpoints

* `Step` — the freeze pass as a `Complexity.FP` transduction, with `RunOracle` the one
  remaining hole: the run-level lookup of a frozen suffix.
* `Oracle` — that hole filled for a quote table given as a finite list of entries, and with it
  `machine_lic_iff_of_finiteSupport`, the strongest corrected `thm:ifp`, together with the two
  weaker public forms the API exposes.
* `Counterexample` — the concrete advice perturbation refuting the printed statement, and the
  closed refutation `not_overgeneral_ifp`.
* `LIAPerturbation` — the corrected theorem doing visible work: moving one price of
  `liaHistory DP` gives a market whose inductor-hood nothing else in the development derives.
-/
