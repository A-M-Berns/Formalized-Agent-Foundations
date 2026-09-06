import LogicalInduction.Construction.SemanticExtension.Prime
import LogicalInduction.Construction.SemanticExtension.Quote
import LogicalInduction.Construction.SemanticExtension.Product
import LogicalInduction.Construction.SemanticExtension.Source
import LogicalInduction.Construction.SemanticExtension.LanguageCopy
import LogicalInduction.Construction.SemanticExtension.Registry
import LogicalInduction.Construction.SemanticExtension.Endpoints

/-!
# The semantic extension (`LogicalInduction.Construction.SemanticExtension`)

Six of this directory's seven modules exist for one endpoint:
`lic_no_expected_net_update_conditional_exact_canonical`,
the generalized `thm:ccee` (tex:2068) — Closing the Loop for conditional expectations, stated
at zero slack over an *arbitrary* threshold-only source `X : ℕ → LUV` carrying only
`LUV.RpnThresholdCodeSeq X`.  That input class is wider than the literal-`PaperLUVSeq`
rendering `Construction/Quotation/ExactCCEE.lean` prices on the paper's own market
`liaHistory (paperDP T)`, and reaching it is the whole reason for the machinery below.  What
it costs is pricing on a different, fixed enlarged language; both renderings stand, and
`LogicalInduction/README.md` records which is which.

The difficulty the directory answers is a representation boundary, not an analytic one.  A
semantic fact can enter the paper's propositional language only as a prime atom, so the
extension names each one by a *handle* — a schema selector plus an unevaluated input — whose
meaning is fixed by a deductive process chosen before any source, market, weight or deferral.
Two proved obstructions say that such a process cannot be universal, and everything else here
is the gate structure that makes it sound anyway.

* `Prime` — the handle allocation (`semanticPrimeTag = 4`, with disjoint selector tags for
  sources, products and quotation aliases), and the diagonalization showing that no
  non-vacuous fixed process can reflect *every* efficiently emitted source.
* `Quote` — the definitional bridge identifying a tag-`2` quote leaf with the universal
  quotation atom it aliases, and the shared base process
  `theoremQuoteBaseDP T = (theoremDP T).union semanticQuoteDP`.
* `Product` — the exact product closure on tag `1`, the second obstruction (a universal
  product closure and the universal quote interpreter have no joint model), and the two
  factor-ownership gates that answer it: the decidable tag test for certified sources and
  the executable prefix gate for quotation factors.
* `Source` — the tag-`0` certificate boundary (`RationalCutAt`, `SourceCutCertificate`,
  `CertifiedSourceLUVSeq`), the object-level checker that recognizes such a package without
  inspecting Lean proofs, and the fixed universal interpreter for what an admitted emitter
  writes.
* `LanguageCopy` — the fixed renaming of the pre-extension vocabulary that answers the
  ownership obstruction, the certificate-free entailment gate over it, and the compiler that
  admits a caller's existing RPN threshold certificate.
* `Registry` — the registry-guarded exact product: a process that dovetails over product jobs
  and checker fuel and activates a clause only after *both* named factors pass the fixed
  coherent-cut registry on the finite prefix that job needs.
* `Endpoints` — the canonical lifted-language process `canonicalCCEEDP T`, its market and
  quote codes, its explicit completed world, and the endpoint itself.

`Endpoints` carries the only paper node in the directory; the other six modules render none.

**`Prime` is interface, not machinery.**  It is the seventh module and the exception to the
sentence above.  `LogicalInduction/API.lean` advertises five of its declarations as the §4.8
presented-LUV vocabulary — `PresentedLUVSeq`, `PresentedLUVSeq.gt_eq`, `semanticHandleLUVSeq`,
`semanticHandleLUVSeq_rpnThresholdCodeSeq` and `no_nonvacuous_worldValued_presented_of_rpn` —
and `APITests/LogicalInduction.lean` exercises all five.  It is also an *upstream* dependency
of the `Paper/` lane: `Construction/Paper/FirstOrder.lean` imports it for `semanticPrimeTag`
and `SemanticPrimeFreshSentence`, so a reverse-cone walk puts `Prime` under 37 modules across
every other lane.  Both headers record that edge.  Only the remaining six modules are
implementation that may be renamed or restructured.
-/
