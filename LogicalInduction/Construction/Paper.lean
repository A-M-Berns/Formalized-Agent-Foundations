import LogicalInduction.Construction.Paper.FirstOrder
import LogicalInduction.Construction.Paper.ComputationDP
import LogicalInduction.Construction.Paper.TheoremDP
import LogicalInduction.Construction.Paper.FiniteEntailment
import LogicalInduction.Construction.Paper.Market

/-!
# The paper's literal first-order layer (`LogicalInduction.Construction.Paper`)

The paper treats its public language as propositional logic over the prime sentences of an
older first-order language (tex:566-573), fixes **one** deductive process, and prices every
§4.9–4.12 theorem against the one market its §5 construction builds over that process.  This
directory is that reading: the propositional/first-order boundary, the two literal streams
whose union is the process, and the market itself.

Five later lanes price on the market assembled here: `Knowledge/`, `Quotation/`,
`Statistics/`, `NonDogmatism/` and `Conditioning/` all state their constructed-market forms
over `liaHistory (paperDP T)`, and `Freeze/Counterexample.lean` builds the `thm:ifp`
counterexample's market over it too.  Two lanes build on these objects but price elsewhere,
and the difference is worth knowing: `LUV/` states its §4.8 `_arith` forms over
`liaHistory (L.gridDP)` and `liaHistory luvThresholdDP`, and `SemanticExtension/` states its
one endpoint over `liaHistory (canonicalCCEEDP T)`.  Everywhere, the constructed-market
statement stands beside a form over an *arbitrary* `[IsLogicalInductor P DP]` or
`[IsMachineLogicalInductor P DP]`: it is the paper's instance, not the only rendering.  The
import graph is not that clean either, and the
exceptions are recorded rather than hidden: `Paper/FirstOrder.lean` imports
`Construction/Knowledge/Syntax.lean` for the global atom-payload allocation, whose reserved
tags it must prove its own compiled atoms avoid;
`Paper/ComputationDP.lean` imports `Construction/Knowledge/Syntax.lean` for the claim
syntax, `Construction/Quotation/Packages.lean` for the quotation schemas, and
`Construction/Statistics/SettlementCompiler.lean` for the shared stage-encoding normal form
`encode_toFinset_eq`; `Paper/TheoremDP.lean` imports
`Construction/Conditioning/Presentation.lean` for the process-union vocabulary `paperDP` is
built with; and `Paper/Market.lean` imports `Construction/Quotation/MarketQuoteCodes.lean`
and `Construction/Quotation/ProductDefinition.lean` for the quote codes and product LUVs its
§4.11–4.12 endpoints are stated over.  Each edge is stated in the importing module's own
header.

## The boundary and its compiler

* `FirstOrder` — the tag-`5` prime reading of Foundation's arithmetic sentences inside the
  repository's propositional `Sentence` type (`paperPrimeCode`, `paperPrimeDecompose`,
  `paperPrimeWorld`), together with the numeric compiler on Gödel codes
  (`paperPrimeDecomposeCode`, primitive recursive) that a fixed process can actually run.
  Negative primes are `.nrel` and `.all` because Foundation stores formulas in negation
  normal form (`dd:nnf`).

## The two literal streams and the single process

* `ComputationDP` — `theoremDP`, the computable deductive process whose stages are the
  `T`-provable instances of the fixed universal computation and quotation schemas.  It
  discharges `ComputationTheoryPresentation` (`theoremPresentation`),
  `QuotationTheoryPresentation` (`quotationPresentation`, `thm:ref`) and the market
  non-vacuity `theoremDP_hworld` — the last *proved* from consistency of `T`, so no
  Σ₁-soundness is taken anywhere.  `liaMarketComputation` (`thm:lia`) is the `LIA`'s exact
  market program over an arbitrary computable process.
* `TheoremDP` — `paperTheoryDP`, the `Θ`-complete stream that dovetails over every encoded
  provable first-order proposition and publishes its prime decomposition, and `paperDP T`,
  the union of the two streams that is the single market's process.  `paperDP_computable`,
  `paperDP_hworld`, `paperQuotationPresentation` (`thm:ref`), `paperLIA` and
  `paperMarketComputation` (`thm:lia`) are the market data every endpoint consumes.

## The market

* `Market` — the self-reference family over `liaHistory (paperDP T)`: `thm:ref` (tex:1969),
  `thm:lp` (tex:1992), `thm:epr` (tex:2014), `thm:er` (tex:2022), `thm:cee` (tex:2045),
  `thm:ceu` (tex:2056), `thm:ccee` (tex:2068) and `thm:st` (tex:2092).  Each endpoint is the
  generic `_ofCode` / `_ofRepresentation` / `_ofDiagonal` statement instantiated at the three
  facts above, and each `_closed` form additionally builds the quote object out of the market
  program itself, so the only hypotheses left are the caller's sequence and its `def:ec`
  write-out codes.

## The shared finite check

* `FiniteEntailment` — `stageEntails`, the executable enumeration of Boolean assignments that
  makes the compactness theorem's finite stage a decidable, primitive-recursive test.  No
  paper node renders here; it is the decision procedure the certificate-free source-admission
  gate and the `thm:ifp` counterexample's day-`0` settlement search both run.
-/
