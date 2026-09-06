import LogicalInduction.Construction.Quotation.DeferralFibre
import LogicalInduction.Construction.Quotation.Packages
import LogicalInduction.Construction.Quotation.MarketQuoteCodes
import LogicalInduction.Construction.Quotation.ProductDefinition
import LogicalInduction.Construction.Quotation.ExactProduct
import LogicalInduction.Construction.Quotation.RepresentedWeight
import LogicalInduction.Construction.Quotation.ExactCCEE

/-!
# Quotation and self-reference (`LogicalInduction.Construction.Quotation`)

The §4.11–4.12 lane.  `thm:ref` (tex:1969), `thm:lp` (tex:1992), `thm:epr` (tex:2014),
`thm:er` (tex:2022), `thm:cee` (tex:2045), `thm:ceu` (tex:2056), `thm:ccee` (tex:2068) and
`thm:st` (tex:2092) each price a sentence that *quotes* a market quantity.  This directory
supplies the quoted syntax, the portfolios that trade on it, the quote codes built from the
market's own program, and the two routes to `thm:ccee`'s product.

Seven of the eight nodes are stated in the sibling lane `Construction/Paper/Market.lean`, over
the single market `liaHistory (paperDP T)`; what is here is everything that makes them
mechanical.  The exception is `ExactCCEE.lean`, which states
`lic_no_expected_net_update_conditional_paperLUV_closed` — `thm:ccee` at zero slack for
literal sources — in this directory, over that same market.

**Cross-lane edges.**  `DeferralFibre.lean` imports `Construction/Statistics/FeedbackEmission.lean`
for the scheduled-match emitter, and with it the entire §5 construction spine and the
`Properties/` modules that spine rests on; `ProductDefinition.lean` imports
`Construction/Conditioning/Presentation.lean` for `DeductiveProcessComputation.union_toComputable`.
Both are recorded in the importing module's own header.  In the other direction,
`Construction/Statistics/FeedbackTruth.lean` reaches back into this lane for
`DeferralFunction.exists_clock` and `deferralPreimage`.

## The quotation apparatus

* `Packages` — the code-indexed quotation layer (`dd:quote-code`): the tag-`2` claim atoms,
  the two fixed universal schemas `universalQuotePos` / `universalQuoteNeg` whose
  exclusivity is provable *inside* `T` (so nothing here takes Σ₁-soundness), the interfaces
  `QuotationTheoryPresentation`, `BooleanQuoteCode`, `RationalQuoteCode` and
  `ParameterizedDiagonalQuoteCode`, the same-day affine portfolios, the six package
  constructors, and the eight `_ofCode` / `_ofRepresentation` / `_ofDiagonal` theorems the
  single-market endpoints instantiate.  `parameterizedDiagonalQuoteCodeOfMarket` builds the
  `thm:lp` selector that prices its own atom by Kleene's second recursion theorem, so no
  self-reference law is a caller premise.
* `DeferralFibre` — the quotation-free deferred layer `Packages` is built on: variable-width
  affine combinations, the paired-index emission certificate `PairedWeighting` (`def:ece`),
  the division-free first-violator `selectorFeature`, and
  `DeferralFibre.deferred_block_price_tendsto_zero`, which gives deferred coherence for
  every `def:deferralfunc` with no injectivity or monotonicity assumption on the schedule.
* `MarketQuoteCodes` — market-generic quote codes derived from the certified market program
  (`dd:quote-code`), so the relation between quoted syntax and quantity is proved rather
  than supplied: `RationalQuoteCode.ofComputable`, the market's own price, expectation and
  confidence sequences, and the `thm:ccee` deferred-weight machinery.  Its two quoted
  products are `indicatorProductLUV` (exact) and `meshProductLUV` (the `dd:mesh` route).

## The two routes to `thm:ccee`'s product

The abstract threshold-only `LUV` interface names no value, so the quoted product can only
be reconstructed from thresholds to within `1/(n+1)`.  Two constructions remove that slack,
each paying a different price, and both are here so the trade is visible.

* `ProductDefinition` — the fresh-atom *definitional extension of the process*: atoms
  `productAtom n r` for `⌜Xₙ · Wₙ > r⌝` with a decidable defining schema entered stagewise.
  Exact for an arbitrary threshold-only source, but over a different inductor — `LIA` on the
  extended process — so it diagnoses the mesh slack rather than superseding the mesh
  endpoint.  Its `sentenceAtomCodes` and `PCWorld.holds_congr_atomCodes` are the general
  propositional-substitution utilities the rest of the development uses.
* `ExactProduct` — the exact product of two **literal** paper LUVs, which name their value
  by a numerator/denominator pair code that arithmetic multiplies exactly.  Exact on the
  same market and the same process, paying instead in generality: the source must be
  literal first-order.
* `RepresentedWeight` — the deferred `[0,1]` weight presented as a literal `PaperLUVSeq`,
  from the paper's own representability premise (tex:600-606) and nothing else, which is
  what the literal route needs to multiply the weight in.
* `ExactCCEE` — `lic_no_expected_net_update_conditional_paperLUV_closed`, `thm:ccee` at
  `slack = 0` over `liaHistory (paperDP T)` for literal sources.
-/
