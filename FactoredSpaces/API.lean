import FactoredSpaces.Semigraphoid
import FactoredSpaces.PerfectMap
import FactoredSpaces.Examples

/-!
# Factored Space Models consumer API

The supported downstream import for factored-space-model research is:

```lean
import FactoredSpaces.API
```

**Status: complete** — all 50 numbered nodes of Garrabrant, Mayer, Wache, Lang, Eisenstat
and Dell, arXiv:2412.02579v2, are stated and proved (`FactoredSpaces/README.md` is the
trust surface; `notes/paper-errata.md` lists the paper defects the Lean does not copy).  This
boundary is therefore the whole consumer surface.  It deliberately hands you the paper's
vocabulary in the paper's shape (`dd:` glossary in `FactoredSpaces.lean`), plus the
non-vacuity witnesses of `Examples.lean`; the proof machinery behind Proposition 5.5
(`ConditionalHistory.lean`, `ActiveTrails.lean`) is a construction import, reachable through
`FactoredSpaces.Separation` when a client needs the closed-form conditional history or the
oriented-walk calculus themselves.

## Vocabulary

Everything lives in the `FactoredSpaces` namespace, with generic graph vocabulary in the root
`Digraph` namespace and two generic `Finset.piecewise` lemmas in the root `Finset` namespace.

* **The factored space** (`dd:pi-space`, `dd:splice`).  `Pt Ω = ∀ i, Ω i` for
  `Ω : I → Type v` is `Ω = ×_{i∈I} Ω_i`; `PtOn Ω J`, `proj J`, `projSet J A` are `Ω_J`,
  `π_J`, `A_J`; `bg i` is the background variable `U_i`; the merge `a_J · b_{I∖J}` is
  `J.piecewise a b` and `S_J × T_{I∖J}` is `splice J S T`, with `prodSplit J C = splice J C C`
  and `mem_splice_iff`, `splice_eq_cyl_inter`, `splice_compl`.  A random variable is any
  `X : Pt Ω → α` (`dd:variable`); `fiber X x` is the event `{X = x}`, `pair X Y` the joint
  variable, `indic A` the indicator (`dd:event-indicator`).  Derived variables: `DerivedOn C X
  Y` (Definition 4.1) with `derivedOn_iff` (Lemma C.3, needs `[Nonempty β]`), `DerivedOn.trans`,
  `.mono`, `.pair`, `.comp_left`.
* **Disintegration, generation, history** (Definitions 4.5, 4.6): `Disintegrates J C`
  (`disintegrates_iff_splice` is the working form; `Disintegrates.union/inter/compl`,
  `disintegrates_univ`, `disintegrates_empty`, `disintegrates_univ_set`), `Generates J X C`
  (`generates_iff`, `Generates.inter`, `generates_univ`, `generates_iff_history_subset`),
  `history X C` (Lemma 4.7: `generates_history`, `history_subset_of_generates`,
  `history_unique_minimal`; Lemma 4.8: `history_pair`; Lemma 4.9:
  `history_eq_iUnion_fibers`, `history_eq_biUnion_fibers`; `history_mono_of_derived`,
  `history_bg_subset`, `mem_history_bg_of_mem_history`, and the membership criteria
  `mem_history_of_sep`, `mem_history_iff_exists_ne`, `exists_ne_of_mem_history`),
  `eventHistory A C` (Lemma C.4: `generates_indic_iff_agree`, `generates_indic_iff_splice`,
  `eventHistory_minimal_splice`, `inter_eq_splice`).
* **Structural independence and time** (Definitions 4.10, 4.11): `StructIndep X Y`,
  `StructIndepGiven X Y Z` (`.symm`), `Before X Y`, `StrictlyBefore X Y`; Lemma 4.12 as
  `structIndep_of_before`, `before_of_forall_bg`, `before_iff_forall_structIndep`; Lemma B.1
  as `structIndepGiven_pair`.
* **Distributions** (`dd:dist`, namespace `Distr`): `Distr S` (`mass`, `nonneg`,
  `sum_eq_one`, `@[ext]`), `prob` (`prob_nonneg`, `prob_univ`, `prob_empty`, `prob_mono`,
  `prob_le_one`, `prob_union_of_disjoint`, `prob_singleton`, `prob_eq_sum_filter`,
  `prob_eq_sum_fiber`, `prob_pos_iff`, `prob_eq_zero_iff`, `prob_eq_zero_of_subset`),
  `support`, `condProb`, `StrictlyPositive`, `map` (`map_mass`, `map_prob`, `map_map`),
  `delta` (`delta_mass`, `delta_prob`, `support_delta`, `delta_eq_prod`), `uniform`
  (`uniform_strictlyPositive`), `mix`, `euclDist`, `nonempty_carrier`, `condDist`
  (`condDist_mass`, `condDist_prob`).  On a factored space: `Distr.prod p` (`prod_mass`,
  `prod_mass_pos_iff`, `prob_prod_agree_on`, `prob_prod_inter_bg`), `margAt` (`margAt_prod`),
  `Factorizes P` (Definition 4.3; `factorizing Ω`, `factorizingPos C`,
  `factorizes_iff_exists_prod`, `factorizes_prod`, `Factorizes.eq_prod_margAt`,
  `factorizes_delta`), `IsFactoredSpaceModel O P` (Definition 4.4; the trivial model is
  `Examples.isFactoredSpaceModel_single`), `Distr.marg` (Definition C.2), `Distr.outer`
  (Definition C.1) and its working form `Distr.outerCompl` (`outerCompl_mass`,
  `Factorizes.eq_outerCompl`, `Factorizes.marg_mass`, `outerCompl_delta_eq_prod`), `cyl`,
  `sliceAt`, `restrict`, `splitEquiv`, `unionEquiv`, `unionComplEquiv`; Lemmas C.11
  (`Distr.prob_pos_of_support_subset`, `Distr.support_outerCompl`,
  `Distr.prob_pos_of_marg_support_subset` — corrected form, errata E3), C.15
  (`Distr.prob_cyl_inter_cyl`), C.16 (`Factorizes.prob_sliceAt`,
  `Distr.prob_outerCompl_delta`), C.17 (`condIndepVarEvent_proj_history`, general form
  `condIndepVarEvent_proj_of_disintegrates`).
* **Conditional independence** (Definition 6.1, product form): `CondIndep P A B C`
  (`.symm`, `.of_prob_eq_zero`), `CondIndepVar P X Y Z`, the mixed forms
  `CondIndepEventVar`, `CondIndepVarEvent`, and `CondIndepAll A B C` (`⊥^⊗`); Lemmas
  C.13/C.14 as `CondIndepEventVar.of_pair`, `CondIndepEventVar.of_proj_subset`;
  `fiber_pair`.
* **Soundness and completeness**: Theorem 6.2 `structIndepGiven_iff_forall_condIndepVar`
  (directions `condIndepVar_of_structIndepGiven`, `structIndepGiven_of_forall_condIndepVar`),
  Lemma 6.3 `condIndep_of_disjoint_eventHistory`, Lemma 6.4
  `disjoint_eventHistory_of_condIndepAll`, Lemma 6.5 `condIndepVar_of_local`, Proposition
  6.6 `structIndepGiven_of_open` (`dd:open-ball`), the interpolation `interp Q P t`
  (`interp_zero`, `interp_one`, `factorizes_interp`, Lemma C.5
  `exists_polynomial_interp_prob`, Lemma C.10 `interp_prob_pos`), and the cohistory
  apparatus of §C.3 (`pairsDifferingAt`, `PQIrrelevant`, `Irrelevant`, `cohistory`,
  `mem_cohistory_iff`; Lemmas C.7 `cohistory_union_eq_univ_of_condIndepAll`, C.8
  `cohistory_eq_compl_eventHistory`, C.9 `pqIrrelevant_or_of_condIndepAll`, C.12
  `condProb_eq_of_agree_on_relevant`, C.18 `condIndepEventVar_proj_cohistory`, C.19
  `condIndepVarEvent_proj_cohistory`, C.20 `disintegrates_cohistory`).
* **Semigraphoids** (Definition 5.1): `IndepRel Ω`, `IsSemigraphoid`, `IsGraphoid`,
  `IsCompositionalSemigraphoid`; `structIndepRel Ω`, `condIndepRel P`; Proposition 5.2
  `isCompositionalSemigraphoid_structIndepRel`, the Pearl half `isSemigraphoid_condIndepRel`
  (proved), and Table 1's negative claim `not_isGraphoid_structIndepRel`.
* **DAGs and Bayes nets** (§5.2; a DAG is `G : Digraph V` with `hG : G.IsAcyclic`):
  `Digraph.IsAcyclic` (`.wf`, `.ne_of_adj`, `.not_adj_symm`, `.not_ancestor_of_adj`),
  `IsAncestor`, `parents` (`mem_parents`, `notMem_parents_self`), `depth` (`depth_lt`,
  `depth_lt_of_isAncestor`), `AncClosed`; the construction `ParentVals`, `parentConfig`,
  `bnIndex`, `bnFactor` (`Ω^G`), `nodeVar hG v` (`X_v`; unfold with `nodeVar_apply`, read
  off with `nodeVar_eq_of_diag`, `jointVar_eq_iff`, `constTable`, `jointVar_constTable`),
  `jointVar hG` (`X`), `nodesVar hG S` (`X_S`), `famVar`, `famJoint`; `CPD`,
  `FactorizesOverDAG G Val P` (`dd:cpd`), `dagFactorizing G Val`, `condCPD`; Lemma B.2
  `prob_jointVar_fiber`; Lemma 5.3 as `factorizesOverDAG_tau`, `factorizes_tauInv`,
  `tau_tauInv`, `tauPos_bijective`, `tauInv_condCPD_tau` (true form, errata E5; `tau`,
  `tauInv`, `tauPos`); Proposition 5.4 `factorizesOverDAG_iff_isFactoredSpaceModel`;
  Proposition 5.6 `isAncestor_iff_strictlyBefore` (`mem_history_nodeVar_iff`).
* **d-separation and perfect maps** (`dd:dsep`): `Digraph.Trail`, `Walk`, `Walk.IsColliderAt`,
  `Walk.Active`, `Trail.Active`, `ColliderOK`, `DSeparated` (`Trail.nil`,
  `Trail.nil_active_iff`, `not_dSeparated_self`, `dSeparated_iff_forall_singleton`,
  `dSeparated_singleton_parents`, `dSeparated_iff_disjoint_zClosureSet`); Proposition 5.5
  `dSeparated_iff_structIndepGiven` — pass `(Val := …)` explicitly when applying it against
  a written-out statement (see `Examples.lean`); Definition 5.7 `IsPerfectMapDAG`,
  `IsPerfectMapFSM` (`IsIMapDAG`, `factorizesOverDAG_of_isIMapDAG` — the I-map ⟹
  factorization theorem, errata E7); Proposition 5.8 `isPerfectMapFSM_nodeVar_of_isPerfectMapDAG`,
  `exists_isPerfectMapFSM_of_exists_isPerfectMapDAG`,
  `exists_isPerfectMapFSM_not_exists_isPerfectMapDAG` (`Prop58Witness`).
* **Witnesses** (`FactoredSpaces.Examples`): the two-coin space `Coins`/`diag`, the trivial
  model `isFactoredSpaceModel_single`, the collider DAG with its d-separation convention pins,
  the one-node perfect map `G₁`/`Q`/`isPerfectMapDAG_G₁_Q`.

`APITests/FactoredSpaces.lean` exercises this boundary the way a client would.
-/
