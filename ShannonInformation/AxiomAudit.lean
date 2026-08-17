/-
# Axiom audit for the shared Shannon-information layer

The checked trust surface for `ShannonInformation`.  Elaboration fails if any listed
endpoint stops existing or acquires an axiom beyond `propext`, `Classical.choice`,
`Quot.sound` — in particular `sorryAx`.

## Why this is separate from the repository's top-level `AxiomAudit.lean`

That file is the **paper** endpoint inventory.  Its entries carry `Paper node:`
annotations checked two-way against committed paper sources, its Tier-2 `#assert_fields`
block is regenerated from `SurfaceProbe.lean`, and per-paper checkers enforce coverage of
its `*-INVENTORY` blocks.  `ShannonInformation` is not a paper — it is shared
infrastructure, registered in `NON_PAPER_LIBRARIES`, with no paper source and no nodes to
cite.  Putting it there would mean inventing an annotation exemption in machinery whose
whole value is that it has none, and would collide with every in-flight paper branch that
touches that file.

The enforcement here is identical; only the bookkeeping lives elsewhere.

## What is being asserted, and what is not

**Asserted:** the endpoints below exist and are axiom-clean.  Because axiom-cleanliness is
transitive through proof terms, this transitively covers the vendored proofs those
endpoints rest on — which is the substantive claim, since the vendored closure is 6,074
lines of third-party source.

**Not asserted:** that this list is complete, or that the vendored statements say what a
given paper needs.  The second is what `ShannonInformation/SCOPE.md` is for, and it is a
mathematical scope question that no axiom check can answer.
-/
module

public import ShannonInformation.API
public import ShannonInformation.FiniteEntropy.Examples

/-!
The assertion elaborator is a verbatim copy of the ten-line command in the repository's
top-level `AxiomAudit.lean`.  It is duplicated rather than shared so that this layer has no
build dependency on the paper trust-surface machinery; there is no mathematics in it.
-/

open Lean Elab Command in
/-- Fail elaboration unless every named declaration exists and depends on no axioms
beyond `propext`, `Classical.choice`, and `Quot.sound`. -/
elab "#assert_axioms_clean_si " ids:ident+ : command => do
  for id in ids do
    let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let axioms ← Lean.collectAxioms name
    let bad := axioms.filter (! [``propext, ``Classical.choice, ``Quot.sound].contains ·)
    unless bad.isEmpty do
      throwErrorAt id "'{name}' depends on disallowed axioms: {bad.toList}"

open ProbabilityTheory

-- The four core definitions.  Everything else in the layer is stated in terms of these.
#assert_axioms_clean_si
  ProbabilityTheory.measureEntropy
  ProbabilityTheory.entropy
  ProbabilityTheory.condEntropy
  ProbabilityTheory.mutualInfo
  ProbabilityTheory.condMutualInfo

-- Nonnegativity: the facts every downstream bound rests on.
#assert_axioms_clean_si
  ProbabilityTheory.entropy_nonneg
  ProbabilityTheory.condEntropy_nonneg
  ProbabilityTheory.mutualInfo_nonneg
  ProbabilityTheory.condMutualInfo_nonneg
  ProbabilityTheory.measureMutualInfo_nonneg

-- Chain rules.
#assert_axioms_clean_si
  ProbabilityTheory.chain_rule
  ProbabilityTheory.chain_rule'
  ProbabilityTheory.chain_rule''
  ProbabilityTheory.cond_chain_rule
  ProbabilityTheory.cond_chain_rule'

-- Independence and conditional-independence characterizations, and the submodularity
-- family they are usually deployed alongside.
#assert_axioms_clean_si
  ProbabilityTheory.mutualInfo_eq_zero
  ProbabilityTheory.condMutualInfo_eq_zero
  ProbabilityTheory.entropy_pair_eq_add
  ProbabilityTheory.entropy_submodular
  ProbabilityTheory.entropy_pair_le_add
  ProbabilityTheory.condEntropy_le_entropy
  ProbabilityTheory.entropy_triple_add_entropy_le
  ProbabilityTheory.ent_of_cond_indep

-- Invariance and maps: the reasons information quantities are usable as
-- representation-independent invariants.
#assert_axioms_clean_si
  ProbabilityTheory.IdentDistrib.entropy_congr
  ProbabilityTheory.IdentDistrib.condEntropy_eq
  ProbabilityTheory.IdentDistrib.mutualInfo_eq
  ProbabilityTheory.entropy_comp_le
  ProbabilityTheory.entropy_comp_of_injective
  ProbabilityTheory.condEntropy_comp_self

-- The finite-range machinery the hypotheses above are stated over.  Listed because
-- `SCOPE.md` turns on exactly what this class means.
#assert_axioms_clean_si
  FiniteRange
  FiniteRange.toFinset

/-!
## The FAF-authored generalization layer

Everything below is *ours*, not PFR's, so the axiom check here is a check on this
repository's own proofs rather than a transitive check on the vendored closure.  Every
public declaration of `ShannonInformation/FiniteEntropy/` is listed; adding one without
listing it is the omission this block exists to catch.
-/

-- The class, its abbreviation, and the two unfolding lemmas.
#assert_axioms_clean_si
  ShannonInformation.FiniteEntropyMeasure
  ShannonInformation.FiniteEntropyOf
  ShannonInformation.FiniteEntropyMeasure.summable_real
  ShannonInformation.FiniteEntropyMeasure.of_summable_real
  ShannonInformation.finiteEntropyMeasure_iff
  ShannonInformation.FiniteEntropyOf.summable

-- The instances that make the existing `FiniteRange` graph discharge the new class.
#assert_axioms_clean_si
  ShannonInformation.finiteEntropy_of_finiteSupport
  ShannonInformation.finiteEntropy_of_finiteRange

-- Measure-theoretic bookkeeping.
#assert_axioms_clean_si
  ShannonInformation.summable_measureReal_singleton
  ShannonInformation.tsum_measureReal_singleton_le_one
  ShannonInformation.measureReal_singleton_le_one
  ShannonInformation.measureReal_map_singleton_eq_tsum_fiber
  ShannonInformation.measureReal_map_fst_singleton
  ShannonInformation.measureReal_map_snd_singleton

-- Closure.
#assert_axioms_clean_si
  ShannonInformation.finiteEntropyMeasure_map
  ShannonInformation.finiteEntropyMeasure_prod
  ShannonInformation.finiteEntropyOf_pullback
  ShannonInformation.finiteEntropyOf_comp
  ShannonInformation.finiteEntropyOf_fst
  ShannonInformation.finiteEntropyOf_snd
  ShannonInformation.finiteEntropyOf_pair

-- Finite-product closure.  `Fintype`, never `Countable` — see the source comment there.
#assert_axioms_clean_si
  ShannonInformation.finiteEntropyOf_measurableEquiv
  ShannonInformation.finiteEntropyOf_piFin
  ShannonInformation.finiteEntropyOf_pi

-- The abstract nonnegative-family core the closure proofs rest on.
#assert_axioms_clean_si
  ShannonInformation.negMulLog_tsum_le
  ShannonInformation.negMulLog_div
  ShannonInformation.tsum_negMulLog_eq_add
  ShannonInformation.tsum_mul_log_div_nonneg
  ShannonInformation.negMulLog_le_add_of_le
  ShannonInformation.summable_tsum_fiber
  ShannonInformation.tsum_tsum_fiber
  ShannonInformation.summable_negMulLog_tsum_fiber
  ShannonInformation.tsum_negMulLog_tsum_fiber_le

/-!
### The restated theorems

Phases 2–4a of `Condensation/notes/finite-range-generalization-plan.md`: the vendored
theorems, re-proved at `FiniteEntropyOf`.  Unlike the blocks above these are not plumbing —
each is a statement a client will cite, and each shadows a `ProbabilityTheory` declaration
of the same name, so an omission here would be invisible at a call site that happened to
resolve to the vendored version instead.  Every public declaration of `ChainRule.lean`,
`Inequalities.lean` and `Derived.lean` is listed.
-/

-- Phase 2, `FiniteEntropy/ChainRule.lean`: the chain rules, and the integrability facts
-- that keep them from being vacuous (`condEntropy` is a Bochner integral, `0` when the
-- integrand is not integrable).
#assert_axioms_clean_si
  ShannonInformation.integrable_of_summable_measureReal_mul_norm
  ShannonInformation.map_cond_measureReal_singleton
  ShannonInformation.measureReal_mul_entropy_cond
  ShannonInformation.summable_measureReal_mul_entropy_cond
  ShannonInformation.integrable_entropy_cond
  ShannonInformation.condEntropy_eq_tsum
  ShannonInformation.chain_rule''
  ShannonInformation.chain_rule
  ShannonInformation.chain_rule'
  ShannonInformation.condEntropy_eq_entropy_pair_sub
  ShannonInformation.cond_chain_rule'
  ShannonInformation.cond_chain_rule
  ShannonInformation.condMutualInfo_eq

-- Phase 3, `FiniteEntropy/Inequalities.lean`: the abstract and law-level pair layers.
#assert_axioms_clean_si
  ShannonInformation.tsum_negMulLog_prod_le
  ShannonInformation.tsum_negMulLog_prod_eq_add_iff
  ShannonInformation.measureEntropy_prod_le_add
  ShannonInformation.measureEntropy_prod_eq_add_iff

-- Phase 3: conditioning stays inside the class.
#assert_axioms_clean_si
  ShannonInformation.finiteEntropyMeasure_zero
  ShannonInformation.measureReal_map_cond_singleton
  ShannonInformation.finiteEntropyOf_cond

-- Phase 3: subadditivity, mutual information, and the independence equality case.
#assert_axioms_clean_si
  ShannonInformation.entropy_pair_le_add
  ShannonInformation.mutualInfo_nonneg
  ShannonInformation.mutualInfo_eq_zero
  ShannonInformation.entropy_pair_eq_add
  ShannonInformation.condMutualInfo_nonneg
  ShannonInformation.condMutualInfo_eq_zero
  ShannonInformation.condEntropy_le_entropy
  ShannonInformation.condEntropy_pair_le_add
  ShannonInformation.entropy_submodular
  ShannonInformation.entropy_triple_add_entropy_le

-- Phase 4a, `FiniteEntropy/Derived.lean`: the corpus that follows by rewriting.
#assert_axioms_clean_si
  ShannonInformation.entropy_comp_le
  ShannonInformation.entropy_of_comp_eq_of_comp
  ShannonInformation.condEntropy_comp_self
  ShannonInformation.condEntropy_of_injective'
  ShannonInformation.mutualInfo_eq_entropy_sub_condEntropy
  ShannonInformation.mutualInfo_eq_entropy_sub_condEntropy'
  ShannonInformation.condEntropy_comp_ge
  ShannonInformation.mutual_comp_le
  ShannonInformation.condMutualInfo_eq'
  ShannonInformation.IdentDistrib.condEntropy_eq

-- Phase 4b, `FiniteEntropy/Derived.lean`: the three statements the consumer migration
-- (`Condensation`, Phase 4b of the generalization plan) turned out to need and Phase 4a had
-- left at `FiniteRange`.  `const_of_nonpos_entropy` is the only one that is not a rewrite
-- chain, and the only statement in the layer that asks for *more* than its vendored twin
-- (`Countable S`); `finiteEntropyMeasure_of_injective` is the layer's one backward closure.
#assert_axioms_clean_si
  ShannonInformation.mutualInfo_const
  ShannonInformation.IndepFun.condEntropy_eq_entropy
  ShannonInformation.const_of_nonpos_entropy
  ShannonInformation.finiteEntropyMeasure_of_injective

-- Phase 4b, `FiniteEntropy/Examples.lean`: the constructed witness separating
-- `FiniteEntropyOf` from `FiniteRange`.  It is library, not test, because
-- `Condensation/Examples.lean`'s `geomModel` is a second client.
#assert_axioms_clean_si
  ShannonInformation.geom
  ShannonInformation.finiteEntropyMeasure_geom
  ShannonInformation.finiteEntropyOf_id_geom
  ShannonInformation.not_finiteRange_id
  ShannonInformation.finiteEntropyOf_strictly_weaker
  ShannonInformation.entropy_geom
  ShannonInformation.entropy_geom_pos
