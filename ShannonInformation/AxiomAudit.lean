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
