/-
# Axiom audit — the checked public-surface inventory (critch-pbl)

Instantiated from the harness template (see the logical-induction branch's AxiomAudit.lean
for the canonical worked instance). Standalone target: `lake env lean AxiomAudit.lean`.
Every declaration listed is public trust surface for the PBL formalization; the build
fails if any listed endpoint acquires an axiom beyond `propext`, `Classical.choice`,
`Quot.sound` (in particular `sorryAx`), or ceases to exist. Every interface class and
boundary structure has its field surface frozen by `#assert_fields`.

Annotation convention: inventory members' docstrings end with a `Paper node:` line citing
Critch 2019 by §/Property/Theorem (§-citations; the paper PDF has no \label source).
-/
import Lean.Util.CollectAxioms
import Critch.BoundedProvability.Basic
import Critch.BoundedProvability.Asymp
import Critch.BoundedProvability.Diagonal
import Critch.ParametricDiagonal
import Critch.Infrastructure.QuoteSentence

open Lean Elab Command in
/-- Fail elaboration unless every named declaration exists and depends on no axioms
beyond `propext`, `Classical.choice`, and `Quot.sound`. -/
elab "#assert_axioms_clean " ids:ident+ : command => do
  for id in ids do
    let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let axioms ← Lean.collectAxioms name
    let bad := axioms.filter (! [``propext, ``Classical.choice, ``Quot.sound].contains ·)
    unless bad.isEmpty do
      throwErrorAt id "'{name}' depends on disallowed axioms: {bad.toList}"

open Lean Elab Command in
/-- Fail elaboration unless `struct` is a structure whose field-name set is exactly the
listed idents. Freezes the hypothesis surface of a boundary structure. Order-insensitive. -/
elab "#assert_fields " struct:ident fields:ident* : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo struct
  unless Lean.isStructure (← getEnv) name do
    throwErrorAt struct "'{name}' is not a structure"
  let actual := ((Lean.getStructureFields (← getEnv) name).map (·.toString)).qsort (· < ·)
  let expected := (fields.map (·.getId.toString)).qsort (· < ·)
  unless actual.toList == expected.toList do
    throwErrorAt struct
      "'{name}' fields changed.\n  expected: {expected.toList}\n  actual:   {actual.toList}"

namespace LO.FirstOrder.Critch

/-! ## Shared infrastructure (Foundation-upstream candidates, R1-F13) -/

#assert_axioms_clean
  LO.FirstOrder.quote_neg_sentence
  LO.FirstOrder.quote_and_sentence
  LO.FirstOrder.quote_or_sentence

/-! ## Phase A abstract interface (§3.1 box; §3.2 Properties 1–2; §4 Defn 1 + Props 3–4)

Every public declaration of `Critch/BoundedProvability/Basic.lean`, including the
substitution helpers `prt`/`pr` (the semisentence↔sentence bridge). -/

#assert_axioms_clean
  ProofMeasure
  ltGuard
  BoundedProvability
  BoundedProvability.prt
  BoundedProvability.pr
  BoundedProvability.BImpDistr
  BoundedProvability.BQuantDistr
  BoundedProvability.BEvalSpec
  BoundedProvability.BMono
  BoundedProvability.BExpansion
  BoundedProvability.BHBL
  BoundedProvability.exists_pr_of_provable

/-! ## Asymptotic layer (§2.2, §2.5; §4 Theorem 1 proof-step support) -/

#assert_axioms_clean
  lg
  Asymp.LtAsymp
  Asymp.EventuallyPositive
  Asymp.HasIntermediateWitness
  Asymp.zero_ltAsymp
  Asymp.trans
  Asymp.lg_ltAsymp_id
  Asymp.add

/-! ## Parametric diagonalization (§4, Proposition 1: interface class + ℒₒᵣ instance) -/

#assert_axioms_clean
  ParametricDiagonalization
  instParametricDiagonalizationLOR

/-! ## Frozen field surfaces — every interface class and boundary structure -/

#assert_fields ProofMeasure
  Pf sound complete mono

#assert_fields BoundedProvability
  bbew bbew₁ bbewInner

#assert_fields BoundedProvability.BImpDistr
  c impDistr

#assert_fields BoundedProvability.BQuantDistr
  C ν ν_computable νGraph νGraph_spec νGraph_total νGraph_func quantDistr
  c₂ bddCompleteCmp

#assert_fields BoundedProvability.BEvalSpec
  eval_spec eval_spec_inner

#assert_fields BoundedProvability.BMono
  mono

#assert_fields BoundedProvability.BExpansion
  e e_computable eGraph eGraph_spec eGraph_total eGraph_func nec innerNec

#assert_fields BoundedProvability.BHBL
  toBImpDistr toBQuantDistr toBEvalSpec toBMono toBExpansion

#assert_fields ParametricDiagonalization
  fixedpoint diagonal

end LO.FirstOrder.Critch
