import LogicalInduction.Construction.LUV.PaperLUV
import LogicalInduction.Construction.LUV.SourceCodec
import LogicalInduction.Construction.LUV.ArithmeticSource
import LogicalInduction.Construction.LUV.Arithmetic
import LogicalInduction.Construction.LUV.Presentation
import LogicalInduction.Construction.LUV.Syntax
import LogicalInduction.Construction.LUV.Endpoints

/-!
# Logically uncertain variables (`LogicalInduction.Construction.LUV`)

The §4.8 lane: `def:luv` (tex:1635) and `def:blcp` as constructed first-order objects, and
the expectation endpoints `thm:expprovind` (tex:1753), `thm:loe`, `thm:expcoh`,
`thm:perexpkno`, `thm:exppolymax` and `thm:wubexp` stated over them.

`Properties/ExpectationProperties.lean` and `Properties/ExpectationAffine.lean` state those
nodes over an arbitrary inductor, taking the world–value coherence of a LUV
(`PCWorld.ValuesAt`, `LUVCombination.WorldValued`) and the `def:ec` metering of its threshold
family as caller-supplied hypotheses.  `LUVCombination.ExactTheoryPresentation` is a
*producer* of `WorldValued`, not a hypothesis of any endpoint: it is what this directory's
`Syntax.lean` and `Presentation.lean` construct, and
`Construction/Statistics/FeedbackTruth.lean` records why no endpoint of `thm:wubexp` should
take it.  What this
directory adds is the arithmetic behind those hypotheses: LUV classes whose world value is
*derived* from the theory rather than assumed, the deductive processes that reveal what the
derivation needs, and the emission certificates that meter the threshold syntax at the size
`def:ec` charges.

Two frontends sit here, and they fix different things.

## The literal frontend: an arbitrary defining formula

* `PaperLUV` — `def:luv` as a literal first-order object.  `PaperLUV T` carries the ℒₒᵣ
  formula that defines the variable, with object-level `T`-derivations of uniqueness and of
  the `[0,1]` bound as fields; the three rational-cut obligations
  (`threshold_provable_of_neg`, `threshold_refutable_of_one_lt`,
  `threshold_downward_provable`) assemble into `rationalCutAt` and hence `source_valued`,
  which derives the world value.  The value is named by a numerator/denominator pair code
  rather than by a canonical rational arithmetic inside ℒₒᵣ; the declaration states what
  that representation choice does and does not fix.
* `SourceCodec` — the RPN leaf codec that turns one Foundation arithmetic proposition into
  a single atomic block of the strategy grammar, with the compact base-four ℒₒᵣ numeral
  `binNumeral`.  Nothing here is a paper node; it supplies the `def:ec` emission
  certificates the frontend's threshold layer consumes.
* `ArithmeticSource` — the paper's own formula *source* language `ArithSource`, with
  `¬ ∧ ∨ ⟹ ⟺` primitive (tex:560) and one emitted token per source node, and the class
  `PolyArithmeticSourceSeq` that meters a formula family as the paper writes it (`dd:nnf`).
  `PaperLUVSeq` is the literal LUV family over it, compiled to `LUV.RpnThresholdCodeSeq` at
  the paper's exact threshold syntax, and `PaperLUVCombination` is `def:blcp` with literal
  paper LUVs as shares.  The strictness separation
  `PolyArithmeticFormulaSeq ⊊ PolyArithmeticSourceSeq` is proved here, not asserted.

## The certified frontend: the paper's worked computable class

* `Arithmetic` — `dd:luv-arith`: the computable `[0,1]`-valued function LUV of tex:1655,
  given by `num, den : ℕ → ℕ`.  `ComputableLUV`, the threshold code, its decidable
  predicate and total decider, the arithmetic schema and `toLUV`.  Because `Θ` decides every
  threshold, the sup in `def:luv` collapses to the standard rational — which is what lets
  the presentation interfaces be derived rather than assumed.
* `Presentation` — those derivations (`threshold_holds_iff`,
  `exactTheoryPresentation_ofArithmetic`, `worldValued_ofArithmetic`,
  `valuesAt_ofArithmetic`) from the single premise `ArithmeticLUVPresentation`, together
  with the `def:dedproc` process `luvThresholdDP` that satisfies that premise.
* `Syntax` — the concrete presentation `LUVCombinationSyntax` (a Tier-2 frozen structure)
  of a sequence of LUV combinations, from which the threshold mesh of `lem:mesh` is emitted
  directly and metered as `def:ec` requires, with the four canonical `_ofSyntax` carriers of
  `lem:mesh`, `thm:exppolymax`, `thm:expcoh` and `thm:perexpkno`.
* `Endpoints` — the expectation tail: `thm:expprovind` at the paper's own one-sided world
  bound, `thm:loe` derived as `app:loe` derives it, and the `_arith` /
  `_arith_unconditional` endpoints, whose finite-precision world hypothesis is discharged
  for `dd:luv-arith` by the scheduled-reveal process `ComputableLUV.gridDP`.

The two frontends meet only through the abstract carrier `LUV`: canonical rational
arithmetic inside ℒₒᵣ is unbuilt, so arithmetic closure *between* LUV values is a scope
boundary of both, not a gap in `def:luv`.
-/
