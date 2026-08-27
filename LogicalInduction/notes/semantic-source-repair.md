# Exact CCEE: fixed lifted-source architecture

This note describes the canonical exact rendering of `thm:ccee`. The endpoint is
`lic_no_expected_net_update_conditional_exact_canonical` in `SemanticLiftedCCEE.lean`.

## Final construction

```text
arbitrary X : ℕ → LUV
  + RpnThresholdCodeSeq X
  + completed-world source_valued
        ↓
fixed old-language lift
        ↓
semantic cut laws from source_valued
        ↓
finite-stage propositional entailment
        ↓
universal source admission
        ↓
exact semantic product and zero-slack CCEE
```

`oldAtom` and `liftSentence` put every caller sentence into a namespace disjoint from
semantic source, product, and quotation handles. There are no aliases back to the original
atoms. `liftDP (theoremDP T)` is a genuinely renamed copy of the source theory, not a
source-dependent extension of an already constructed market.

Completed-world valuedness semantically implies the lower, upper, and downward rational-cut
laws. `DeductiveProcess.exists_stage_entails` reduces each consequence to a finite stage;
the executable `stageEntails` checker lets the fixed registry discover that evidence by
dovetailing. `rpnThresholdSourceCode` supplies exactly the mesh queries used by the product
construction, so the endpoint needs neither an arbitrary-rational emitter nor a caller
certificate.

The one canonical process is

```text
liftedCCEEBaseDP T = theoremQuoteBaseDP T ∪ liftDP (theoremDP T)
canonicalCCEEDP T  = semanticRegistryClosureDP (liftedCCEEBaseDPComputation T)
```

It is fixed from `T` before `X`, `f`, or `w`. `canonicalCCEEDP_hworld` constructs a
completed world for the whole universal registry, including malformed and unselected
programs. No equality with prices from a separately constructed `liaHistory (theoremDP T)`
is claimed or needed.

## Why the invariants are necessary

Two negative results explain the design.

* `no_nonvacuous_worldValued_presented_of_rpn` gives an efficiently emitted, world-valued
  indicator source that mentions its own semantic handle. Unrestricted presentation would
  force `p ↔ ¬p`; hence language separation is necessary.
* `semanticFreshIncreasing_not_jointly_reflected` is fresh but has malformed increasing
  thresholds. Interpreting every fresh emitter would make the universal product closure
  inconsistent; hence admission must be gated by effectively checked cut laws.

The fixed lift supplies separation uniformly. Finite entailment supplies executable
coherence without asking the caller for proof-carrying source syntax.

## Canonical dependency cone

The exact endpoint is centered on:

* `OldLanguageLift.lean` — syntax, truth, process, and efficiency-preserving lift;
* `FiniteEntailment.lean` — executable finite propositional consequence;
* `EntailedSourceRegistry.lean` — entailment-gated universal admission;
* `LiftedRpnSource.lean` — extraction and reflection of the lifted mesh emitter;
* `SemanticLiftedCCEE.lean` — fixed process, non-vacuity, quotation, and capstone.

The transitive semantic registry/product modules remain implementation support for guarded
source and quote factors. `SemanticSource.lean` and `SemanticJoint.lean` retain diagnostic
counterexamples documenting the separation and admission invariants. The former
`PaperSourceLUV.lean` route was removed: it targeted the obsolete
`CertifiedSourceLUVSeq` caller ABI and is not part of exact CCEE or the new FOL frontend.

## Paper-premise ledger

| Paper/current abstract premise | Exact endpoint |
|---|---|
| arbitrary e.c. source | `X : ℕ → LUV` and symbol-metered `RpnThresholdCodeSeq X` |
| genuine `[0,1]` source | the same completed-world `source_valued` premise |
| arbitrary deferral | bare `DeferralFunction` |
| P-generable `[0,1]` weight | one `PGenerableRat` at the canonical market plus bounds |
| product and quotation syntax | constructed internally |
| product error | identically `0` |

There is no caller-facing freshness condition, presentation, source certificate,
arbitrary-rational emitter, second-market generator, source-dependent process,
`weight_valued`, or `right_reflected` premise.

## First-order scope

Literal first-order reconstruction is not required for exact CCEE. FAF intentionally keeps
a propositional calculus whose atoms can represent first-order prime sentences. A separate
thin FOL LUV frontend may recover the paper's literal `def:luv`—a one-variable formula plus
theory proofs of unique `[0,1]` value—and compile it to the ordinary abstract LUV interface.
That frontend does not require a global migration of `Sentence`.
