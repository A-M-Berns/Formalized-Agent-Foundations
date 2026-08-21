# Semantic-source repair boundary for exact `thm:ccee`

This note records the checked status of the semantic-prime route after commit `0153ce0`.
It does not change the official coverage classification.

## What efficient emission does and does not provide

`RpnSentenceCodes.primrec` and `RpnSentenceCodes.exists_code` already turn an
`LUV.RpnThresholdCodeSeq` certificate into a total threshold-sentence naming program.
`rpnThresholdSourceCode_spec` packages that extraction without a new caller-facing code
premise.

Efficient emission does not constrain the emitted vocabulary or prove that the emitted
thresholds form a rational cut.  These are separate requirements.

## Two checked obstructions

`no_nonvacuous_worldValued_presented_of_rpn` strengthens the original diagonal result to
the source class used by closed CCEE.  `semanticValuedDiagonalLUVSeq` is an efficiently
emitted indicator-style LUV and is valued in every completed world, but it mentions the
semantic extension's own source leaves.  Exact reflection would force `p ↔ ¬p`.
Therefore source-language separation is necessary even after assuming `source_valued`.

`semanticFreshIncreasing_not_jointly_reflected` then shows that separation is not
sufficient for a universal interpreter combined with `semanticProductDP`.  The fresh
family is false at threshold zero and true at threshold one.  Exact reflection of those
two leaves conflicts with the fixed product clauses.  The finite core is
`semanticProductDP_no_increasing_factor_assignment`.

This second example is intentionally not a genuine LUV.  Its role is to show why a fixed
process cannot interpret every syntactically fresh program and rely on a semantic
`source_valued` premise only for the one source later selected by a caller: malformed but
unselected programs would already make the universal joint process inconsistent.

## Minimal missing representation

The fixed process must activate only source schemas carrying an *effectively checkable*
certificate of both:

1. pre-extension vocabulary ownership; and
2. coherent `[0,1]` rational-cut semantics in completed theory worlds.

The paper gets both from its first-order definition of a LUV: source terms live in the
old language, and the background theory proves their well-defined `[0,1]` value.  The
current `LUV := ℚ → Sentence` deliberately erases that syntax and proof.  A Lean `Prop`
field asserting freshness or `source_valued` is not enough for the fixed interpreter,
because its deductive-process computation cannot enumerate inhabitants by inspecting
Lean proofs.

The smallest faithful repair is therefore local proof-carrying source syntax: an encoded
old-language LUV definition plus an encoded background-theory proof whose checker is part
of the fixed process.  Reconstructing that certificate format is a representation-level
addition; merely strengthening `RpnThresholdCodeSeq` with another semantic proposition
would hide rather than solve the computability/non-vacuity issue.

## Schema ownership

Generic emitted-source programs use `semanticEmitterSchema`/`semanticSourceSchema`
(schema tag `0`).  The narrow quotation alias mechanism uses `semanticQuoteSchema` (tag `2`),
and products retain tag `1`.  `semanticEmitterSchema_ne_quote` proves the namespaces do
not overlap.  A future proof-carrying interpreter should use only the emitter namespace.

## Consequence for CCEE

`SemanticProduct.lean` remains an exact theorem once coherent factors are already
presented.  It is not yet a paper-strength closed CCEE endpoint: the canonical constructed
process has no encoded first-order LUV-certificate registry from which to build arbitrary
paper LUV presentations.  Adding that registry would revise the representation of the
canonical theory/language from the outset; no equality with `liaHistory (theoremDP T)`
should be claimed without a separate market correspondence theorem.

## Proof-carrying cut checkpoint

`CertifiedSource.lean` now isolates the exact semantic certificate required at the current
threshold ABI.  `PCWorld.RationalCutAt` consists of lower and upper `[0,1]` bounds plus
downward closure; `RationalCutAt.exists_valuesAt` proves, by taking the supremum of the true
rational thresholds, that these laws are sufficient for the repository's full `ValuesAt`
interface.  They do not decide truth at the represented value, so the interface still admits
the paper's genuinely uncertain/nonstandard boundary behavior.

`SourceCutCertificate` carries an actual `Nat.Partrec.Code` returning base-process stages
which contain the three cut laws.  `CertifiedSourceLUVSeq` packages that executable evidence,
the existing `RpnThresholdCodeSeq`, a total arbitrary-rational threshold compiler, and
old-language ownership.  The total compiler is the operation the paper obtains by
substituting a rational into its e.c.-emitted one-variable formula; it is intentionally not
claimed derivable from the flattened `RpnThresholdCodeSeq`, whose contract only exposes the
nonnegative expectation grids.  Its canonical
`toPresented` handle stores both the source emitter code and certificate code.  This is not
yet the universal interpreter: the next construction must run and validate those programs
inside one fixed process.  The negative theorem
`semanticFreshIncreasing_no_cutCertificate` confirms that the malformed increasing source
cannot enter this registry whenever the base process is non-vacuous.

## Product/quotation ownership checkpoint

There was a second collision beyond source tag freshness.  The original `semanticProductDP`
ranges over every schema, while `semanticQuoteDP` interprets every Boolean program in quote
tag `2`.  `theorem_quote_product_not_jointly_satisfiable` constructs an increasing quote
program and proves that the theorem, quote, and unrestricted-product processes have no joint
completed world.

`SemanticCertifiedProduct.lean` repairs this by activating product clauses only when both
factor schemas have certified-source tag `0`.  The new `semanticCertifiedProductDP` is fixed,
computable, non-vacuous, and retains exact `ValuesAt` multiplication.  More importantly,
`theoremQuoteCertifiedProductDP_hworld` gives an explicit completed world for the single
fixed union of the theorem, quotation, and guarded-product processes.  The exact closed
plumbing theorem
`lic_no_expected_net_update_conditional_certifiedSemantic_closed` is green over that process.
It deliberately remains non-paper-facing: source interpretation, weight presentation, and
the right quoted product are still explicit premises.

That formerly remaining verifier is now implemented by `SemanticSourceRegistry.lean` and
`SemanticSourceDP.lean`: it evaluates the emitter/certificate pair stored in a tag-`0`
schema, checks old-language ownership and base-stage membership on finite prefixes, and
only then activates source equivalences. `SemanticRegistryProduct.lean` supplies the joint
non-vacuity proof without caller-specific clauses.

The remaining representation theorem is equally precise.  To claim the full paper source
quantifier, FAF must define the paper-facing old-language formula/proof object and compile it
to `CertifiedSourceLUVSeq`, thereby deriving the arbitrary-rational emitter and cut-stage
program.  The current Foundation pin has first-order formula coding and derivations, but FAF
still has no arithmetic-internal rational-order/threshold compiler for arbitrary
value-defining formulas.  Until that compiler exists, `CertifiedSourceLUVSeq` is the checked
target interface, not yet a proved exact image of every paper `def:luv` source.

## Mixed quotation-factor and exact CCEE checkpoint (2026-08-21)

The downstream semantic route is now closed over that checked target interface.
`SemanticQuoteFactor.lean` implements a fixed finite-prefix admission test for tag-`2`
rational quotation factors. For every downward query it requires both an exposed
positive/negative quotation fact and the corresponding fixed quote-leaf link. Thus it
does not promote arbitrary or malformed quotation selectors merely from their namespace.
`rationalQuote_semanticQuoteFactorPrefix_eventually` proves that every repository
`RationalQuoteCode` is eventually admitted.

`semanticRegistryProductDP` now uses the mixed executable predicate
`semanticFactorPrefixValidAtFuel`: tag `0` factors must pass the proof-carrying source
registry, tag `2` factors must pass the quotation-factor checker, and every other tag is
rejected. The process remains fixed from its base computation alone.
`semanticRegistryProductDP_hworld` was strengthened accordingly: its canonical extension
world satisfies source-source, source-quote, and quote-quote clauses. In the quote case,
the checked link clauses transport the old quotation fact to the semantic leaf. Hence
joint non-vacuity does not rely on an unstated choice of quote interpretation.

The new capstone
`lic_no_expected_net_update_conditional_paper_closed` has caller arguments

```text
T, f, X : CertifiedSourceLUVSeq (theoremQuoteBaseDP T),
w : ℕ → ℚ, weight_mem, weight_generable
```

and no caller-supplied weight LUV, product presentation, source/weight valuedness proof,
right-reflection proof, freshness premise, second-market generator, or slack. Both the
deferred-weight code and the deferred weighted-expectation code are constructed internally.
The left product is `semanticSchemaProductLUV` and its `ValuesAt` certificate is exact.
The inductor is `liaHistory (theoremQuoteSemanticRegistryProductDP T)`, whose process is
fixed from `T` before `X`, `f`, or `w`; no correspondence with the older
`liaHistory (theoremDP T)` is claimed.

The paper-proof ledger is now:

| Paper step | Checked FAF justification |
|---|---|
| e.c. genuine `[0,1]` source | `CertifiedSourceLUVSeq.threshold_codes`, executable emitter, freshness, and `SourceCutCertificate` |
| quote `w_{f(n)}` | `registryDeferredWeightQuoteCode` and `rationalQuote_factor_eventually` |
| exact `X_n w_{f(n)}` | `semanticSchemaProductLUV_valuesAt` |
| quote `E_{f(n)}(X_n) w_{f(n)}` | `registryConditionalExpectationQuoteCode` and `RationalQuoteCode.reflected` |
| conditional no-net-update argument | `lic_no_expected_net_update_conditional_ofRepresentation` with zero slack |
| completed worlds exist | `theoremQuoteSemanticRegistryProductDP_hworld` |

This is Outcome B, not yet literal paper-strength Outcome A. The only remaining
representation gap is upstream: FAF still lacks a kernel-checked compiler proving that
every paper Definition 4.8.1 old-language e.c. uniquely `[0,1]`-valued formula yields the
five fields of `CertifiedSourceLUVSeq`. In particular, the arbitrary-rational emitter and
executable base-stage cut certificate are still fields of the translation target rather
than derived from a formal paper-FOL source object. Therefore the official `thm:ccee`
coverage row remains `qualified` despite the now-exact, closed downstream theorem.
