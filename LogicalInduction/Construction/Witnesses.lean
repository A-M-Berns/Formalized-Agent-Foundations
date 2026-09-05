import LogicalInduction.Construction.Witnesses.KraftInequality
import LogicalInduction.Construction.Witnesses.PrefixMachine
import LogicalInduction.Construction.Witnesses.UniversalPrefix
import LogicalInduction.Construction.Witnesses.UniversalDovetailer
import LogicalInduction.Construction.Witnesses.BoundedEvaluation
import LogicalInduction.Construction.Witnesses.HistoricalMaturity
import LogicalInduction.Construction.Witnesses.FeedbackEmission
import LogicalInduction.Construction.Witnesses.ConditioningPresentation
import LogicalInduction.Construction.Witnesses.ConditioningCompiler
import LogicalInduction.Construction.Witnesses.BitPrefixSyntax
import LogicalInduction.Construction.Witnesses.ComputationSyntax
import LogicalInduction.Construction.Witnesses.DeferralFibre
import LogicalInduction.Construction.Witnesses.QuotationAffine
import LogicalInduction.Construction.Witnesses.FeedbackTruth
import LogicalInduction.Construction.Witnesses.FeedbackUnconditional
import LogicalInduction.Construction.Witnesses.UnconditionalOverLIA
import LogicalInduction.Construction.Witnesses.LUVSyntax
import LogicalInduction.Construction.Witnesses.LUVArithmetic
import LogicalInduction.Construction.Witnesses.LUVPresentation
import LogicalInduction.Construction.Witnesses.LUVDeductiveProcess
import LogicalInduction.Construction.Witnesses.LUVExpectationCertified
import LogicalInduction.Construction.Witnesses.QuoteCodeOfMarket
import LogicalInduction.Construction.Witnesses.DigitConditioning
import LogicalInduction.Construction.Witnesses.RpnConditioning
import LogicalInduction.Construction.Witnesses.FreezeOracle
import LogicalInduction.Construction.Witnesses.LIAPerturbation
import LogicalInduction.Construction.Witnesses.FreezeStep
import LogicalInduction.Construction.Witnesses.RpnFreeze
import LogicalInduction.Construction.Witnesses.RunAutomaton
import LogicalInduction.Construction.Witnesses.PatternAutomaton
import LogicalInduction.Construction.Witnesses.StructuredPatterns
import LogicalInduction.Construction.Witnesses.CounterAutomaton
import LogicalInduction.Construction.Witnesses.PayloadAutomaton
import LogicalInduction.Construction.Witnesses.SegmentAutomaton
import LogicalInduction.Construction.Witnesses.SegmentCounter
import LogicalInduction.Construction.Witnesses.SegmentRecognizer
import LogicalInduction.Construction.Witnesses.FiberTestFP
import LogicalInduction.Construction.Witnesses.StrictSeparators
import LogicalInduction.Construction.Witnesses.SemanticPrime
import LogicalInduction.Construction.Witnesses.SemanticQuote
import LogicalInduction.Construction.Witnesses.SemanticSource
import LogicalInduction.Construction.Witnesses.ProductDefinition
import LogicalInduction.Construction.Witnesses.SemanticProduct
import LogicalInduction.Construction.Witnesses.SemanticJoint
import LogicalInduction.Construction.Witnesses.CertifiedSource
import LogicalInduction.Construction.Witnesses.SemanticSourceRegistry
import LogicalInduction.Construction.Witnesses.SemanticSourceDP
import LogicalInduction.Construction.Witnesses.SemanticCertifiedProduct
import LogicalInduction.Construction.Witnesses.SemanticRegistryProduct
import LogicalInduction.Construction.Witnesses.SemanticLiftedCCEE
import LogicalInduction.Construction.Witnesses.PaperFirstOrder
import LogicalInduction.Construction.Witnesses.PaperFirstOrderCompiler
import LogicalInduction.Construction.Witnesses.PaperTheoryDP
import LogicalInduction.Construction.Witnesses.R0Representability
import LogicalInduction.Construction.Witnesses.SubstEmission
import LogicalInduction.Construction.Witnesses.ComputationRepresented
import LogicalInduction.Construction.Witnesses.PaperCutLawDP
import LogicalInduction.Construction.Witnesses.PaperMarket
import LogicalInduction.Construction.Witnesses.PaperLUV
import LogicalInduction.Construction.Witnesses.StructuredPaperRpn
import LogicalInduction.Construction.Witnesses.ArithmeticSource
import LogicalInduction.Construction.Witnesses.FinitePerturbationWitness
import LogicalInduction.Construction.Witnesses.PaperExactProduct
import LogicalInduction.Construction.Witnesses.PaperRepresentedWeight
import LogicalInduction.Construction.Witnesses.PaperExactCCEE

/-!
# Witness constructions (`LogicalInduction.Construction.Witnesses`)

Concrete compilers and syntax objects that inhabit the boundary interfaces the §4 property
proofs take as hypotheses, turning each assumed interface into a constructed one.
`LogicalInduction/README.md` records which boundaries remain disclosed.

The import list above is the directory's entry points; the remaining modules of the
directory arrive through them and are named in the groups below.

## Prefix machines and semimeasures

`KraftInequality`, `PrefixMachine`, `UniversalPrefix`, `UniversalDovetailer` — the
constructed presentations `thm:dus` and `thm:strict` quantify over, together with the
prefix complexity `thm:ob` is instantiated at. `BitPrefixSyntax` and `StrictSeparators`
build the independent-atom sentence families they are stated over, and
`BoundedEvaluation` carries the bounded-evaluation layer and `thm:obu`'s c.e. source
premise (`CEEnumeration`).

## Feedback, maturity and quotation

`HistoricalMaturity`, `FeedbackEmission`, `FeedbackTruth`, `FeedbackUnconditional`,
`QuotationAffine` with its quotation-free half `DeferralFibre`, and `QuoteCodeOfMarket`
(`dd:quote-code`).

## Conditioning, freeze and the recognizer kit

`ConditioningPresentation`, `ConditioningCompiler`, `DigitConditioning`, `RpnConditioning`,
`FreezeOracle`, `FreezeStep`, `RpnFreeze`, `LIAPerturbation`, plus the automaton kit
(`RunAutomaton`, `PatternAutomaton`, `StructuredPatterns`, `CounterAutomaton`,
`PayloadAutomaton`, `SegmentAutomaton`, `SegmentCounter`, `SegmentRecognizer`,
`FiberTestFP`) that supplies the `Complexity.FP` recognizers the corrected `thm:ifp` needs.
`CanonicalCodes` settles when the escape-leaf decode test agrees with canonical-code
comparison, which is what the freeze reads at a price leaf.

## Logically uncertain variables

`LUVSyntax`, `LUVArithmetic`, `LUVPresentation`, `LUVDeductiveProcess`,
`LUVExpectationCertified` — the certified arithmetic LUV class and its `_arith` endpoints
(`dd:luv-arith`).

## The semantic-product lane

`SemanticPrime` through `SemanticLiftedCCEE`, with `ProductDefinition` and
`CertifiedSource`, realizing `thm:ccee` for an arbitrary threshold-only source on the
finite mesh (`dd:mesh`).  `OldLanguageLift` supplies the fixed renaming that answers the
vocabulary-ownership obstruction, `LiftedRpnSource` admits a caller's existing RPN threshold
certificate into that fixed registry, and `EntailedSourceRegistry` is the certificate-free
admission gate, deciding admission by the executable finite check of `FiniteEntailment`.

## The paper's literal first-order layer

`ArithmeticSource` (the source language `def:ec` meters on, `dd:nnf`), `PaperFirstOrder`,
`PaperFirstOrderCompiler`, `PaperTheoryDP`, `PaperMarket`, `PaperLUV`,
`StructuredPaperRpn`, `PaperExactProduct`, `PaperRepresentedWeight`, `PaperExactCCEE`,
`R0Representability`, `SubstEmission`, `ComputationSyntax`, `ComputationRepresented`
(`dd:machinetheory`), `PaperCutLawDP` and `FinitePerturbationWitness`.  The write-and-read-back
kit for that layer is `DayMachine` (a machine carrying the day in its own source),
`SourceNumbering` (inverting the naming map), `SourceRecognizer` (gating which token runs are
genuinely written sources) and `SourceWindow` (splicing a day's written axioms into one
written conjunction).

## Unconditional instantiation over the constructed inductor

`UnconditionalOverLIA` makes `thm:dus`, `thm:strict` and `thm:scon` unconditional over the
constructed `LIA`, and `ComputationDP` does the same for the meta-learning and
self-reference families, building the computable deductive process their endpoints are
stated over.

The §5 construction spine — market maker, budgeter, trading firm, `liaStates`, and the
existence results — lives one level up; a reader auditing `exists_machine_logical_inductor`
never needs this folder.
-/
