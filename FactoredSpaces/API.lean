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
non-vacuity witnesses of `Examples.lean`.  The import re-exports the whole library, so the
oriented-walk calculus of `ActiveTrails.lean` (`Digraph.OWalk` and its activity recursion,
`dd:owalk`) is in scope too; that is internal proof machinery for the `Z`-closure
criterion and is *not* supported — only the names listed below are.  The `Z`-closure
vocabulary of `ConditionalHistory.lean` **is** supported, because the working form of
d-separation exposed here (`dSeparated_iff_disjoint_zClosureSet`) is stated in it: a client
cannot use that criterion without naming `Digraph.zClosureSet`.

## Vocabulary

Everything lives in the `FactoredSpaces` namespace, with generic graph vocabulary in the root
`Digraph` namespace and two generic `Finset.piecewise` lemmas in the root `Finset` namespace.

* **The factored space** (`dd:pi-space`, `dd:splice`).  `Pt Ω = ∀ i, Ω i` for
  `Ω : I → Type v` is `Ω = ×_{i∈I} Ω_i`; `PtOn Ω J`, `proj J`, `projSet J A` are `Ω_J`,
  `π_J`, `A_J` (`proj J` is definitionally Mathlib's `Finset.restrict J`, `proj_eq_restrict`;
  the sub-restriction `Ω_K → Ω_J` is Mathlib's `Finset.restrict₂`); `bg i` is the background
  variable `U_i`; the merge `a_J · b_{I∖J}` is `J.piecewise a b` and `S_J × T_{I∖J}` is
  `splice J S T`, with `prodSplit J C = splice J C C` and `mem_splice_iff`,
  `splice_eq_cyl_inter`, `splice_compl`.  A random variable is any
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
  `mem_history_of_sep`, `mem_history_iff_exists_ne`, `exists_ne_of_mem_history`; the
  empty-value-space regime: `generates_iff_isEmpty_ptOn`, `history_eq_of_isEmpty`,
  `history_eq_empty_of_eq_empty`, `history_congr`),
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
  `support` (`Distr.mem_support_iff`), `condProb`, `StrictlyPositive`, `map` (`map_mass`,
  `map_prob`, `map_map`),
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
  `sliceAt`, `splitEquiv`, `unionEquiv`, `unionComplEquiv`; Lemmas C.11
  (`Distr.prob_pos_of_support_subset`, `Distr.support_outerCompl`,
  `Distr.prob_pos_of_marg_support_subset` — corrected form, errata E3), C.15
  (`Distr.prob_cyl_inter_cyl`), C.16 (`Factorizes.prob_sliceAt`,
  `Distr.prob_outerCompl_delta`), C.17 (`condIndepVarEvent_proj_history`, general form
  `condIndepVarEvent_proj_of_disintegrates`).
* **Conditional independence** (Definition 6.1, product form): `CondIndep P A B C`
  (`.symm`, `.of_prob_eq_zero`), `CondIndepVar P X Y Z`, the mixed forms
  `CondIndepEventVar`, `CondIndepVarEvent`, and `CondIndepAll A B C` (`⊥^⊗`); Lemmas
  C.13/C.14 as `CondIndepEventVar.of_pair`, `CondIndepEventVar.of_proj_subset`;
  `fiber_pair`.  For checking a `CondIndepVar` by hand over families of coordinates:
  `CondIndep.of_subset_left`, `CondIndep.of_disjoint_left`, `CondIndepVar.symm`,
  `fiber_proj_subset_or_disjoint`, `condIndepVar_proj_of_subset_left` /
  `condIndepVar_proj_of_subset_right` (a conditioned-on family is independent of
  everything), `CondIndepVar.of_proj_subset` (restrict both sides to subfamilies) and
  `not_condIndepVar_proj_self` (a non-degenerate coordinate is never independent of itself
  given a family omitting it).  These live in `PerfectMap.lean` for now, since checking a
  perfect map is what needs them.
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
  `bnIndex` (with `idxAt x v` the index `(v, x_pa(v))` and `table_congr` the transport that
  keeps the dependent parent-configuration argument out of a rewrite), `bnFactor` (`Ω^G`),
  `nodeVar hG v` (`X_v`; unfold with `nodeVar_apply`, read
  off with `nodeVar_eq_of_diag`, `jointVar_eq_iff`, `constTable`, `jointVar_constTable`),
  `jointVar hG` (`X`), `nodesVar hG S` (`X_S`), `famVar`, `famJoint`; `CPD`,
  `FactorizesOverDAG G Val P` (`dd:cpd`), `dagFactorizing G Val`, `condCPD`; Lemma B.2
  `prob_jointVar_fiber`; Lemma 5.3 as `factorizesOverDAG_tau`, `factorizes_tauInv`,
  `tau_tauInv`, `tauPos_bijective`, `tauInv_condCPD_tau` (true form, errata E5; `tau`,
  `tauInv`, `tauPos`, and `tau_mass` for the pushforward mass); Proposition 5.4
  `factorizesOverDAG_iff_isFactoredSpaceModel`.
* **d-separation and perfect maps** (`dd:dsep`): `Digraph.Trail`, `Walk`, `Walk.IsColliderAt`,
  `Walk.Active`, `Trail.Active`, `ColliderOK`, `DSeparated` (`Trail.nil`,
  `Trail.nil_active_iff`, `not_dSeparated_self`, `dSeparated_iff_forall_singleton`,
  `dSeparated_singleton_parents`, `dSeparated_iff_disjoint_zClosureSet`; the two ways to
  discharge a d-separation obligation by hand, `dSeparated_of_subset_left` /
  `dSeparated_of_subset_right` and, against them, the one-edge trail `Trail.pair` with
  `Trail.pair_active` and `not_dSeparated_of_skel`); Proposition 5.5
  `dSeparated_iff_structIndepGiven` — pass `(Val := …)` explicitly when applying it against
  a written-out statement (see `Examples.lean`); Proposition 5.6
  `isAncestor_iff_strictlyBefore` (`mem_history_nodeVar_iff`, the `Z = ∅` case of the
  closed-form conditional history, in `Separation.lean`); Definition 5.7 `IsPerfectMapDAG`,
  `IsPerfectMapFSM` (`IsIMapDAG`, `factorizesOverDAG_of_isIMapDAG` — the I-map ⟹
  factorization theorem, errata E7); Proposition 5.8 `isPerfectMapFSM_nodeVar_of_isPerfectMapDAG`,
  `exists_isPerfectMapFSM_of_exists_isPerfectMapDAG`,
  `exists_isPerfectMapFSM_not_exists_isPerfectMapDAG` (`Prop58Witness`).
  * *Closure vocabulary* (root `Digraph` namespace, `ConditionalHistory.lean`).  The
    working criterion `dSeparated_iff_disjoint_zClosureSet` is stated in terms of the
    `Z`-closure, so its vocabulary is supported: `Digraph.zClosure` (`S_Z(s)`),
    `zClosureSet` (`S_Z(A)`), `unblockedAnc` (`A_Z(v)`), `IsZClosed`, with the working
    lemmas `zClosure_subset`, `mem_zClosureSet_self`,
    `mem_zClosureSet_of_mem_unblockedAnc`, `exists_of_mem_zClosureSet`.  Also
    `Digraph.Skel` (the undirected edge relation a `Trail` chains along) and
    `Digraph.Trail.toWalk`, needed to write a concrete trail down and read its collider
    status; and `Digraph.exists_active_trail_of_active_walk`, the walk→trail bridge that
    lets a client define d-separation through walks instead (`dd:owalk`).
* **Witnesses** (`FactoredSpaces.Examples`): the two-coin space `Coins`/`diag`, the trivial
  model `isFactoredSpaceModel_single` against `not_isFactoredSpaceModel_const`, the
  perfectly-correlated law `Pdiag` on `Coins` refuting Definition 4.3
  (`not_factorizes_diag`) and, over the edgeless two-node DAG `G₀`, eq. (2)
  (`not_factorizesOverDAG_diag`), the collider DAG with its d-separation convention pins
  (`not_dSeparated_given_collider`, `not_dSeparated_adj`, `dSeparated_given_endpoint`, …),
  the positive/negative structural-independence pair `structIndepGiven_collider` /
  `not_structIndepGiven_nodesVar`, the one-node perfect map `G₁`/`Q`/`isPerfectMapDAG_G₁_Q`
  and the perfect map *with an edge* `G₂`/`Pedge`/`isPerfectMapDAG_G₂_Pedge`
  (`G₂_acyclic`, `G₂_adj_zero_one`, with `not_dSeparated_G₂`,
  `dSeparated_G₂_given_endpoint` and `not_condIndepVar_Pedge` showing that neither side of
  Definition 5.7(1) is idle there).

`APITests/FactoredSpaces.lean` exercises this boundary the way a client would.
-/
