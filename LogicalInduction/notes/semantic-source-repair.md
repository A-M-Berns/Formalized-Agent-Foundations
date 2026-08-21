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
