/-
# Witness constructions (`LogicalInduction.Construction.Witnesses`)

Concrete compilers and syntax objects that inhabit the boundary interfaces the property
proofs take as hypotheses — prefix machines, the universal semimeasure and its
dovetailer, feedback and quotation witnesses, and the efficiency certificates for the
conditioning and freeze compilers. Each turns an assumed interface into a constructed
one; the README records which remain disclosed.

The §5 construction spine — market maker, budgeter, trading firm, `LIA`, and the
existence result — lives one level up; a reader auditing `exists_logical_inductor`
never needs this folder.
-/
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
import LogicalInduction.Construction.Witnesses.RpnFreeze
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
