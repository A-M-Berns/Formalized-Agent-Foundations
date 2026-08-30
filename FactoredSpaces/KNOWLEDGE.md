# Formalization Knowledge — Factored Space Models (arXiv:2412.02579, branch `factored-space-models`)

Permanent, curated facts about this formalization. Committed with the code; read by every
harness agent before working. Add an entry only if a future fresh-context agent would act
differently for knowing it. One bullet per fact, newest last. Cross-reference finding IDs
(RN-Fxx) where an entry originated from an audit.

## Correspondence table

Paper notation ↔ Lean names (namespace `FactoredSpaces`).

| Paper (§/symbol) | Lean name | Notes |
|---|---|---|
| `Ω = ×_{i∈I} Ω_i` (Def 4.2) | `Pt Ω` for `Ω : I → Type v` | `dd:pi-space`; finiteness of `I` / `Ω_i` are instance hypotheses where used |
| `Ω_J`, `π_J`, `A_J` | `PtOn Ω J`, `proj J`, `projSet J A` | `PtOn Ω J = ∀ i : J, Ω i` |
| `U_i`, `U_J` (Def 4.2) | `bg i`, `proj J` | |
| `a_J · b_{I∖J}` (merge) | `J.piecewise a b` | Mathlib `Finset.piecewise` (`dd:splice`) |
| `S_J × T_{I∖J}` | `splice J S T` | `prodSplit J C = splice J C C` |
| `X ▷_C Y` (Def 4.1) | `DerivedOn C X Y` | `X ▷ Y` is `DerivedOn Set.univ X Y` |
| `(X, Y)` joint variable | `pair X Y` | |
| `J` disintegrates `C` (Def 4.5) | `Disintegrates J C` | stated as `C = prodSplit J C`; work with `disintegrates_iff_splice` |
| `J` generates `X` given `C` (Def 4.6) | `Generates J X C` | `generates_iff` is the working form |
| `H(X | C)`, `H(X)` (Def 4.6) | `history X C`, `history X Set.univ` | `Finset I` |
| `1_A`, `H(A | C)` | `indic A`, `eventHistory A C` | `dd:event-indicator` |
| the event `x` = `{X = x}` | `fiber X x` | |
| `X ⊥_Ω Y`, `X ⊥_Ω Y | Z` (Def 4.10) | `StructIndep X Y`, `StructIndepGiven X Y Z` | |
| `X ≤_Ω Y`, `X <_Ω Y` (Def 4.11) | `Before X Y`, `StrictlyBefore X Y` | |
| Lemma 4.7 | `generates_history`, `history_subset_of_generates`, `history_unique_minimal` | |
| Lemma 4.8 | `history_pair` | |
| Lemma 4.9 | `history_eq_iUnion_fibers` (Set form, no finiteness of `Val(X)`), `history_eq_biUnion_fibers` | |
| Lemma 4.12 | `structIndep_of_before`, `before_of_forall_bg`, `before_iff_forall_structIndep` | |
| Lemma A.1 | `Disintegrates.union`, `Disintegrates.inter` | |
| Lemma A.2 | `Generates.inter` | |
| Lemma B.1 | `structIndepGiven_pair` | |
| Lemma C.3 | `derivedOn_iff` | needs `[Nonempty β]`, see errata |
| Lemma C.4 | `generates_indic_iff_agree` (i⟺ii), `generates_indic_iff_splice` (i⟺iii), `eventHistory_minimal_splice` | |
| distribution on a finite type `S` (`Δ(S)`) | `Distr S` (`mass`, `nonneg`, `sum_eq_one`); `P(A)` is `P.prob A` | `dd:dist` |
| `P(A \| C)` | `P.condProb A C` (`= 0` when `P(C) = 0`) | |
| `supp(P)`, `δ_s`, `(1−λ)P + λQ` | `P.support`, `Distr.delta s`, `Distr.mix t P Q` | |
| `P_i = P ∘ U_i⁻¹`, `P_J` (Def C.2) | `P.margAt i`, `P.marg J` (`Distr.map (proj J)`) | |
| `⨂_i P_i` | `Distr.prod p` | |
| `P` factorizes over `Ω` (Def 4.3), `Δ^⊗(Ω)`, `Δ^*_C(Ω)` | `Factorizes P`, `factorizing Ω`, `factorizingPos C` | pointwise, literal |
| `M = (Ω, O)` is an FSM for `P` (Def 4.4) | `IsFactoredSpaceModel O P` | |
| `P_J ⊗ P_K` (Def C.1) | `Distr.outer h PJ PK`; the always-used `P_J ⊗ P_{I∖J}` on `Ω` is `Distr.outerCompl PJ PK` | |
| `A_J × A_{I∖J}` for `A_J ⊆ Ω_J` | `cyl J A ∩ cyl Jᶜ B` | `splice_eq_cyl_inter` bridges to `splice` |
| `D^α` | `sliceAt J α D` | |
| `A ⊥^P B \| C`, `X ⊥^P Y \| Z` (Def 6.1), mixed forms | `CondIndep P A B C`, `CondIndepVar P X Y Z`, `CondIndepEventVar`, `CondIndepVarEvent` | product form only |
| `A ⊥^⊗ B \| C` | `CondIndepAll A B C` | |
| `R^λ = ⨂((1−λ)Q_i + λP_i)` | `interp Q P t` | `t : unitInterval` |
| Euclidean distance on `Δ(Ω)` | `Distr.euclDist` | |
| `(P,Q)`-irrelevant, irrelevant, `Cohistory(A\|C)` (Def C.6), `Δ^*_{C,i}` | `PQIrrelevant`, `Irrelevant`, `cohistory`, `pairsDifferingAt` | |
| Lemma 6.3 / 6.4 / 6.5 / Thm 6.2 / Prop 6.6 | `condIndep_of_disjoint_eventHistory` / `disjoint_eventHistory_of_condIndepAll` / `condIndepVar_of_local` / `structIndepGiven_iff_forall_condIndepVar` / `structIndepGiven_of_open` | |
| Lemmas C.5, C.7, C.8, C.9, C.10, C.11, C.12, C.13, C.14, C.15, C.16, C.17, C.18, C.19, C.20 | `exists_polynomial_interp_prob`, `cohistory_union_eq_univ_of_condIndepAll`, `cohistory_eq_compl_eventHistory`, `pqIrrelevant_or_of_condIndepAll`, `interp_prob_pos`, `Distr.prob_pos_of_support_subset`/`support_outerCompl`/`prob_pos_of_marg_support_subset`, `condProb_eq_of_agree_on_relevant`, `CondIndepEventVar.of_pair`, `CondIndepEventVar.of_proj_subset`, `Distr.prob_cyl_inter_cyl`, `Factorizes.prob_sliceAt`/`Distr.prob_outerCompl_delta`, `condIndepVarEvent_proj_history`, `condIndepEventVar_proj_cohistory`, `condIndepVarEvent_proj_cohistory`, `disintegrates_cohistory` | |
| semigraphoid / graphoid / compositional (Def 5.1); Prop 5.2 | `IsSemigraphoid`, `IsGraphoid`, `IsCompositionalSemigraphoid` on an `IndepRel Ω`; `isCompositionalSemigraphoid_structIndepRel` (`structIndepRel Ω`) | value spaces `Type v`, nonempty |
| DAG `G = (V, E, Val)`, `pa(v)`, `an(v)` | `G : Digraph V` with `hG : G.IsAcyclic`, `Val : V → Type u`, `G.parents v`, `G.IsAncestor u v` | root `Digraph` namespace |
| `I_v`, `I`, `Ω^G`, `X_v`, `X`, `X_S` | `ParentVals G Val v`, `bnIndex G Val` (`Σ v, ParentVals`), `bnFactor G Val`, `nodeVar hG v`, `jointVar hG`, `nodesVar hG S` | `nodeVar_apply` is eq. (4) |
| `P` factorizes over `G` (eq. (2)), `Δ^*(G)`, CPDs | `FactorizesOverDAG G Val P`, `dagFactorizing G Val`, `CPD`, `condCPD P hpos` | `dd:cpd` |
| `τ`, `τ⁻¹` (Lemma 5.3) | `tau hG`, `tauInv φ`; `tauPos_bijective`, `tauInv_condCPD_tau` | true form, see errata E5 |
| Lemma B.2 / Prop 5.4 / Prop 5.6 | `prob_jointVar_fiber` / `factorizesOverDAG_iff_isFactoredSpaceModel` / `isAncestor_iff_strictlyBefore` | Prop 5.6 lives in `Separation.lean` (round 2), derived from `mem_history_nodesVar_iff` |
| trail, active trail, d-separation | `Digraph.Trail`, `Digraph.Walk`, `Walk.IsColliderAt`, `Walk.Active`, `Trail.Active`, `Digraph.DSeparated` | `dd:dsep` |
| `A_Z(v)`, `Z`-closed, `S_Z(s)`, `S_Z(A)`, `I^z` (memo) | `Digraph.unblockedAnc`, `Digraph.IsZClosed`, `Digraph.zClosure`, `Digraph.zClosureSet`, `zConsistent` | `ConditionalHistory.lean` |
| Prop 5.5 | `dSeparated_iff_structIndepGiven` | direct route |
| perfect map (Def 5.7), Prop 5.8 | `IsPerfectMapDAG`, `IsPerfectMapFSM`; `isPerfectMapFSM_nodeVar_of_isPerfectMapDAG`, `exists_isPerfectMapFSM_of_exists_isPerfectMapDAG`, `exists_isPerfectMapFSM_not_exists_isPerfectMapDAG` | |

## Design decisions

* **Splice encoding (`dd:splice`).** The obvious rendering of `C_J × C_{I∖J}` through
  `(∀ i : ↥J, Ω i)` and transports across `↥(J ∪ K) ≃ ↥J ⊕ ↥K` makes §4 and Appendix A a
  dependent-subtype slog. Disintegration is equivalent to closure under
  `Finset.piecewise` (`disintegrates_iff_splice`, proved against the literal product form),
  after which Lemma A.1 is two `piecewise` rewrites (`Finset.piecewise_union`, `Finset.piecewise_inter`, ours, root namespace)
  and A.2 / 4.7 / 4.8 / C.4 are short. Measured in the spike (`notes/spike-2026-08-17.md`).
* **Definition 4.5 stated literally.** `Disintegrates J C := C = prodSplit J C` with
  `prodSplit` built from the genuine projections `proj J`, so the paper node reads against
  the paper; the splice form is a proved equivalence, not the definition.
* **`history` is a `Finset.inf` over `Finset.univ.filter`,** with a single classical
  `Decidable` instance chosen inside the definition (`by classical; exact …`). Spike
  finding: with a per-proof `classical` the `Finset.filter` instances in `history_le`
  diverge and the goal gets stuck; keep the instance inside `history` and let callers
  `simp [history]`.
* **Unbundled factored space (`dd:pi-space`).** No `FactoredSpace` structure; the paper's
  objects live over `Pt Ω` for ambient `(I, Ω)`. Chosen so that variables, events and
  distributions need no coercions; the cost is that "there exists a factored space model"
  (Proposition 5.8) quantifies over `(I : Type) (Ω : I → Type)` explicitly.
* **`Val(X)` is the codomain (`dd:variable`).** Lemma 4.9's union over `Val(X)` is stated
  over the whole codomain type, which drops the paper's finiteness of `Val(X)` (the
  unattained values contribute empty histories); a `Fintype` `Finset.biUnion` form is
  provided alongside.
* **Universe in Lemma 4.12.** "For all variables `Z` on `Ω`" cannot range over all
  universes inside one `Prop`; `before_iff_forall_structIndep` lets `Val(Z)` range over
  `Type v` (the factors' universe, where the witnesses `U_i` live), and the ⟹ direction
  `structIndep_of_before` is stated separately, universe-polymorphic in `Val(Z)`.
* **Semigraphoid axioms via Theorem 6.2.** Proposition 5.2's axioms 2–4 (decomposition,
  weak union, contraction) are proved, as in the paper, from soundness+completeness and the
  semigraphoid axioms of probabilistic conditional independence — the latter *proved* for
  Definition 6.1's product form (`isSemigraphoid_condIndepRel`), not cited from Pearl, so no
  citation boundary remains. Symmetry (axiom 1) is `Disjoint.symm` directly, and composition
  (axiom 6) is Lemma B.1 from `history_pair`. (Corrected in round 1, R1-F30.)

* **`Distr` rather than `FiniteFactoredSets.ProbDist` (`dd:dist`).** FFS's distribution is
  event-based (`Set S → ℝ`, additivity) because Garrabrant's Definition 36 is; this paper's
  Definition 4.3, its factorwise interpolation `⨂((1−λ)Q_i + λP_i)`, delta and outer
  products are all pointwise, so the mass function is the object manipulated. Not a
  duplicate: different shape, and neither is a repo-shared module. Revisit only if a shared
  `Common/` probability layer is ever created.
* **Factorization over a DAG is the CPD form (`dd:cpd`).** Eq. (4)'s `P(x_v | x_pa(v))`
  are conditional probability distributions specified per node and parent configuration
  (Koller–Friedman Def 3.5, which the paper follows). Round-1 audit (A4a) checked that this
  is extensionally a no-op: with Lean's `condProb = 0` at zero-probability conditions, the
  literal reading `P(x) = ∏ P(x_v | x_pa(v))` defines the *same* `Δ^*(G)` (⟸ both sides `0`
  when a parent configuration has probability `0`; ⟹ ancestral-closure marginals plus
  extension of the CPDs, `Val v` nonempty from `Distr (Pt Val)`), so no disclosure is owed.
  The `0/0` problem bites in `τ⁻¹` — whose formula needs a factor at *every* `(v, y) ∈ I` —
  not in the definition of `Δ^*(G)`; that is what breaks Lemma 5.3's bijectivity (errata
  E5). For strictly positive `P` the CPDs *are* the conditionals (`condCPD`), the regime in
  which Lemma 5.3 is true and stated (`tauPos_bijective`, `tauInv_condCPD_tau`).
* **d-separation is defined here, with the endpoint convention (`dd:dsep`).** Trails are
  distinct-vertex skeleton paths; colliders are interior vertices with both trail edges
  incoming; endpoints are non-colliders and so block when in `Z`. Prop 5.5 is false for
  overlapping sets under the alternative convention (errata E8). Walks (`Digraph.Walk`)
  exist only for proofs (`exists_active_trail_of_active_walk`).
* **Prop 5.5 is proved directly, not via Koller–Friedman.** See
  `notes/dsep-sizing/memo-2026-08-17.md`: closed-form conditional history
  `H(X_A | X_Z = z) = I^z ∩ I_{S_Z(A)}` (`ConditionalHistory.lean`) + the graph half
  (`ActiveTrails.lean`). K–F soundness/completeness of d-separation is *not* formalized
  (research-scale, and unnecessary). The memo's brute-force scripts live beside it.
* **`|Val_v| ≥ 2` is an instance hypothesis `[∀ v, Nontrivial (Val v)]`** on Props 5.5,
  5.6, 5.8 and the conditional-history lemmas, not on the DAG structure
  (`dd:finiteness-minimal`); with a one-element `Val_v` the node drops out of every history
  and Prop 5.5/5.6 fail (memo §1).
* **Prop 5.8(1) needs the I-map ⟹ factorization theorem** (errata E7): a perfect map `G`
  of `P` makes `P` factorize over `G` (chain rule along a topological order + the local
  Markov d-separations `v ⊥ nondesc(v) | pa(v)`), which is what makes `M^G` a *model* of
  `P`; the paper's proof omits it. Proved in `PerfectMap.lean`.
* **Openness in Prop 6.6 is the metric-ball criterion (`dd:open-ball`)** for `euclDist`;
  Lemma 6.5's continuity step is an explicit ε–δ lemma (`exists_delta_euclDist_interp`),
  proved with `fun_prop` + `Metric.continuousAt_iff`, not a topological limit.
* **Lemma C.10 is proved by the factorwise bound**, not the paper's expansion (which is
  wrong at `I = ∅`, errata E4): `λP'_i ≤ (1−λ)P_i + λP'_i` gives `R^λ(C) ≥ λ^{|I|}P'(C)`.

* **Lemma 5.3's inverse formula needs no reverse-topological marginalization.** Work
  upstairs in `Ω^G`: `E := {X_pa(v) = y}` is invariant under changing the single
  coordinate `(v, y)` (no parent of `v` has `v` as ancestor-or-self), and on `E`,
  `X_v = ω_(v,y)`; so for a product `P^Ω`, `P^Ω(E ∩ {ω_(v,y) = a}) = p_(v,y)(a)·P^Ω(E)`
  (`Distr.prob_prod_inter_bg`), giving the conditional probability directly. Also:
  strictly positive members of `Δ^*(G)` have strictly positive CPDs (every `(v, y, a)` is
  realized by a joint value since `v ∉ pa(v)`), which is what makes `tauPos` surjective.
* **Where inhabitation comes from in §5.2.** `Nonempty (Pt Val)` from any
  `Distr (Pt Val)` (`Distr.nonempty_carrier`) is the cheap source of `Nonempty (Val u)` for
  all `u`; do not try to get it from a point of `Ω^G` (circular). In the history section it
  comes from `[∀ v, Nontrivial (Val v)]`, and `Nonempty (ParentVals G Val v)` is then
  `inferInstance` — the paper's "since `I_v` is nonempty" step of Proposition 5.6.
* **Lemma C.7's proof avoids topology on `Δ^*_{C,i}`**: the paper's "continuous, hence
  nonzero on an open set" step is replaced by "the numerator polynomial has finitely many
  roots" (`Polynomial.finite_setOf_isRoot`); same content, no topology on distributions.
* **Lemma C.12 does not use C.11(3)** (false as printed): positivity along the
  replacement chain comes from `Distr.prod_mass_pos_iff` + C.11(1), and the interpolant is
  `q' i = if i ∈ cohistory then uniform else P.margAt i`.
* **Lemma C.20's statement is unconditional**: the empty-`Ω` and empty-`C` cases are
  vacuous via `disintegrates_iff_splice`; do not add `[Nonempty (Pt Ω)]` downstream.

* **The table-construction API of `ConditionalHistory.lean`.** `propTable G Val Z x bad D`
  returns `x q` at node `q` unless `q ∈ D` and some parent `p ∈ D ∖ Z` deviates from `x p`
  in the consulted configuration (then `bad q`); lookups `propTable_of_good/of_not_mem/
  of_bad`; evaluation principles `nodeVar_eq_of_diag` (a table returning `x q` at every
  index `x` realizes has `X = x` — needs nothing off-diagonal) and `nodeVar_ne_of_prop`
  (badness propagates along `D` from a source, `hstep` from `Digraph.unblockedDesc_step`).
  Every constructed point in the file is this table plus one or two `Function.update`s.
  Reuse it; do not build tables by hand.
* **Memo simplifications found in proof:** (i) the copy-chain-along-a-path construction is
  not needed — take `D` = the whole unblocked-descendant set and let the table detect "any
  live parent deviates" (no path lists, no `DecidableEq` on lists); note `D` must EXCLUDE
  `Z` for relevance (L3⇒) and INCLUDE the `Z`-sinks for the adjacent step (L5a); (ii) L5's
  `~`-relation + closure is not needed — fix the disintegrating `J` and prove `i ∈ J ↔ k ∈ J`
  directly (`mem_iff_mem_of_mix`, one mixed point suffices for both orderings), chaining
  with `Iff.trans`. Memo estimate ≈1400 lines, actual ≈800.
* `disintegrates_zcIdx` (L4) proves a conjunction at every vertex in one induction; the
  `Z`-parent case needs both conjuncts of the IH.
* `ConditionalHistory.lean` sets `linter.unusedSectionVars false` file-wide (the ambient
  instance bundle would otherwise demand `omit` on ~50 declarations).

* **Prop 5.8(1)'s missing step (E7) is `factorizesOverDAG_of_isIMapDAG`** (PerfectMap.lean),
  stated for `IsIMapDAG`. Note the direction: `IsIMapDAG` quantifies over *arbitrary*
  (overlapping) triples, so it is a **stronger** hypothesis than Koller–Friedman's I-map
  (pairwise-disjoint triples) and the lemma is correspondingly *weaker* than K–F Thm 3.1 —
  enough for E7, because its only consumer supplies the paper's perfect map (Definition 5.7,
  also over overlapping triples, E17). Do not reuse it as K–F 3.1. Its chain rule needs
  no linear order: `Digraph.depth` (strictly increasing along edges) + `Finset.strongInductionOn`
  over ancestrally closed sets (`Digraph.AncClosed`) removing a max-depth node; the
  zero-probability branch needs no separate argument (the IH already yields `∏ = 0`). Its
  graph half `Digraph.dSeparated_singleton_parents` (local Markov) is ~35 lines via the
  `Z`-closure criterion, not trails — prefer the closure criterion for any new d-separation
  fact. `cpdOfDist` uses a uniform fallback at zero-probability parent configurations
  (exactly the freedom behind E5).
* **Prop 5.8(2)'s witness** (`Prop58Witness`, PerfectMap.lean): `V = Bool`, `Val false =
  Fin 3`, `Val true = Bool`, one factor `Fin 3`, `P` = uniform pushed along the joint; both
  sides of the perfect-map iff are shown equal to one decision predicate `ind`, collapsing
  64 cases; the probabilistic `⟹` needs no numeric probability (`decide` cannot evaluate
  `ℝ`). The two general facts it runs on live upstream: `history_eq_empty_iff`
  (`H(X|C) = ∅ ↔ X` constant on `C`) in `History.lean` and `condIndepVar_map_famJoint` in
  `BayesNet.lean`.

* **Oriented walks (`dd:owalk`, `ActiveTrails.lean`).** `Digraph.Walk`/`Trail` read collider
  status off `verts[k±1]?` — right for the *statement*, bad to construct in. All proofs run
  in the inductive `Digraph.OWalk` (`nil`/`consF`/`consB` recording orientation), converting
  once at each boundary (`exists_owalk_of_chain` in, `OWalk.toTrail` out); the bridge
  `activeFrom_iff_activeBi` is the only place acyclicity is used (a `Skel` edge fixes its
  orientation only in a DAG). Key: `ActiveBi p Z b c := p.ActiveOpen Z b ∧ vertCond Z (c &&
  p.endDir b) t` (derived, not recursive) gives one-line `activeBi_append`/`activeBi_reverse`.
  Hard-direction certificate: `∃ p : OWalk s u, p.ActiveBi Z false true` (the memo's "leaves
  `u` forwards" is unsatisfiable when `u = w ∈ Z` is reached as a collider). Easy direction:
  one structural induction with `reachCond Z S b u` — no collider/fork enumeration. Walk→trail
  shortcut is ~30 lines given `OWalk.colliderOK_of_activeOpen`; the real cost was the
  `Walk ↔ OWalk` bridge (~110 lines).
* **Round-1 consolidation (2026-08-17).** `Dist` renamed **`Distr`** (collision with Mathlib's
  root `Dist` class made `open FactoredSpaces` + `Dist S` an ambiguity error). Definition 5.1:
  `IndepRel` binds `[Nonempty]` only on the two independent slots (where Theorem 6.2 needs it
  through Lemma C.3), nothing on the conditioning slot; `IsGraphoid.intersection` is stated
  cross-typed (`Y : →β`, `Z : →γ`) with side condition `β = γ → ¬ HEq Y Z` — do NOT
  simplify to a bare `¬ HEq Y Z` (not dischargeable for `β ≠ γ`: needs Pi-type injectivity);
  `not_isGraphoid_structIndepRel` is Table 1's negative claim (structural independence fails
  intersection). `[Nonempty γ]` dropped from Theorem 6.2/Prop 6.6; `[Fintype γ]` from C.13;
  `[Nonempty β]` from Lemma 4.12. `Val : V → Type w` in its own universe (`ParentVals :
  Type max u w`, hand-written); `famVar`/`famJoint` live in BayesNet with no instances and
  `nodesVar`/`jointVar` are DEFINED through them. One public `nodeVar` reading-off API in
  BayesNet (`idxAt`, `table_congr`, `nodeVar_eq_of_diag`, `jointVar_eq_iff`, `constTable`, …);
  `Digraph.depth`/`AncClosed`/acyclicity one-liners next to `IsAcyclic`; `ColliderOK` in
  DSeparation; `dSeparated_singleton_parents` in ActiveTrails; `OWalk` stays in ActiveTrails
  (`dd:owalk`, deliberate). `Examples.lean` holds all non-vacuity witnesses (`Coins`/`diag`,
  `isFactoredSpaceModel_single`, `collider` d-sep convention pins, `G₁`/`Q`/
  `isPerfectMapDAG_G₁_Q`, and since round 3 `G₂ = (0 → 1)`/`Pedge`/`isPerfectMapDAG_G₂_Pedge`, the first perfect-map inhabitant with an edge, plus the three factorization refutations `not_factorizes_diag`, `not_isFactoredSpaceModel_const`, `not_factorizesOverDAG_diag`).
* **R1-F50 (client-side timeout on Props 5.5/5.6) — decision: accept the documented
  idiom.** Applying `dSeparated_iff_structIndepGiven`/`isAncestor_iff_strictlyBefore`
  against a written-out statement times out unless `(Val := …)` is passed on the
  APPLICATION (unifier evaluates the `Fintype`/`DecidableEq` instances of the `abbrev`s
  `ParentVals`/`bnIndex` while `Val` is a metavariable; `irreducible nodeVar`/`parents` do
  not help). Both docstrings and `Examples.lean` show the idiom. The real fix — non-reducible
  `def`s for `ParentVals`/`bnIndex`/`bnFactor` — would break the recorded definitional
  bridges and is left for a later consolidation if consumers hit it.

* **Round 2 (2026-08-17) — hardening pass, five Lens A + five Lens B Opus auditors +
  two codex sweeps; 38 findings, 0 BLOCKER; all MAJORs were repo-mode duplicates or idle
  binders, none a faithfulness defect.** Settled there:
  * `proj J` is definitionally Mathlib's `Finset.restrict J` (`proj_eq_restrict`, rfl) and
    the sub-restriction `Ω_K → Ω_J` IS Mathlib's `Finset.restrict₂` (the paper-local
    `restrict` was deleted, R2-F22/F23); `restrict₂_comp_restrict` is
    `Finset.restrict₂ h (proj K ω) = proj J ω`. `splitEquiv` is NOT `Equiv.piEquivPiSubtypeProd`
    (different second-factor index type); `Finset.piecewise_union/inter` have no Mathlib
    counterpart (checked in full) — do not re-raise either.
  * `[Nonempty α] [Nonempty β]` are dropped from `condIndepVar_of_structIndepGiven` and
    Prop 6.6 (`structIndepGiven_of_open`) — derived inside from `P.nonempty_carrier` /
    `Q.nonempty_carrier` (R2-F20). They REMAIN on `generates_iff`,
    `Generates.inter`, `generates_history`, `history_mono_of_derived` where they are
    load-bearing (verified by delete-and-rebuild; the empty-factor counterexample of E12
    kills the binder-free forms). Theorem 6.2's iff carries `Nonempty α ∨ Nonempty β`
    instead (2026-08-30): delete-and-rebuild tests only the binder-free form, and the
    printed statement is *true* with exactly one value space empty (`Ω` is then empty, both
    sides hold), so the pair of instance binders over-excluded. The mathematics lives in
    `structIndepGiven_iff_forall_condIndepVar_of_nonempty`, to which the paper-node
    statement reduces whenever `Ω` is inhabited. The same delete-one-at-a-time test shows
    `[Nonempty α]` on 4.7/A.2 is slightly stronger than their exact failure set (README
    discloses this); it stays because the exact condition is about the factors. `[DecidableEq I]` is needed to *state* the §6 endpoints
    (`Distr (Pt Ω)` needs `Pi.fintype`); `[∀ v, DecidableEq (Val v)]` is needed to state
    Props 5.5/5.6 (`DecidableEq (bnIndex G Val)`), idle only on Prop 5.8(1) (fixed, R2-F31).
  * The Prop 5.6 block moved out of `BayesNet.lean`: `mem_history_nodeVar_iff` is now the
    `Z = ∅`, `A = {v}` case of `mem_history_nodesVar_iff` (R2-F30/F35), so BayesNet holds
    only the construction, Lemmas 5.3/B.2 and Prop 5.4.
  * `not_isGraphoid_structIndepRel` and `isSemigraphoid_condIndepRel` are inventoried
    without `Paper node:` lines (unnumbered paper claims — Table 1 row "Intersection", and
    the Pearl fact behind Prop 5.2); the FS-INVENTORY preamble records this. The
    graphoid refutation is genuine: `IsGraphoid` is inhabited (`fun _ _ _ => True/False`),
    the witness space satisfies `IsSemigraphoid`, and the paper's homogeneous form is
    provable at `Ω = fun _ : Unit => Bool` (verified R2-B3).
  * `#assert_fields` on the semigraphoid structures freezes names only; their content is in
    the field types (`β = γ → ¬ HEq Y Z` side condition, minimal `[Nonempty]` binders) —
    the AxiomAudit comment says so.
  * Which Examples lemma pins the d-separation ENDPOINT convention: `not_dSeparated_adj`
    (and the round-2 addition `dSeparated_given_endpoint`, `collider.DSeparated {0} {2} {2}`) — the nil-trail
    lemmas do not discriminate the readings; `not_dSeparated_given_collider` pins the
    collider convention. The convention lives in the bodies of `Walk.IsColliderAt`,
    `Walk.Active`, `DSeparated` (defs, not inventoried), so those pins are the only guard.
  * **Degenerate-case history API (R2-F11/F12).** Lemma 4.8 (`history_pair`), Lemma 4.12
    (`before_of_forall_bg`, `before_iff_forall_structIndep`) and Lemma B.1
    (`structIndepGiven_pair`) carry NO value-space hypotheses, matching the paper (this
    supersedes the round-1 note that only `[Nonempty β]` was dropped from 4.12). With
    `IsEmpty (Val X)`, `Pt Ω` is empty, every event is `∅`, and `Generates J X C ↔
    IsEmpty (PtOn Ω J)` (`generates_iff_isEmpty_ptOn`) — so all empty-valued variables
    share one history (`history_eq_of_isEmpty`): `{i₀}` for a unique empty factor, `∅`
    for two or more. Helpers: `exists_isEmpty_factor`, `history_eq_empty_of_eq_empty`,
    `history_congr` (equal generating families ⟹ equal history; needed because
    `{J | IsEmpty (PtOn Ω J)}` is NOT ∩-closed, so `generates_history` has no analogue
    there), `history_subset_singleton_of_isEmpty_factor`, `history_eq_singleton_of_mem`.
    Use these before adding a `[Nonempty]` binder to any new history statement. The
    binders that remain (`generates_iff`, `generates_history`, `history_unique_minimal`,
    `history_mono_of_derived`, `history_eq_iUnion_fibers`, `mem_history_iff_exists_ne`)
    are load-bearing; `mem_history_iff_exists_ne` is outright false without it.
  * `Disintegrates` is a def wrapping an `Eq`: dot notation (`hd.trans …`) DOES resolve
    (whnf finds `Eq`); the trap is only `rw`/`simp only [Disintegrates]`.
  * Lemma 6.5's printed statement leaves `ε` unquantified; `condIndepVar_of_local` binds it
    (and restricts `Q'` to factorizing, i.e. the paper's own domain of `d`).

* **Final blind audit (2026-08-18) — nine Opus auditors (A1–A5 blind on statement
  extracts, B1–B3, C) + two codex sweeps, all denied KNOWLEDGE/errata; 60 findings,
  0 BLOCKER.** Blind rediscovery of errata E1, E3, E5, E6, E7, E8, E9, E11–E17 by ≥2
  channels each (strong corroboration); new errata E18–E20. Substantive fixes:
  * `IndepRel` and the Definition 5.1 structures bind NO `[Nonempty]` (R3-F51, corroborated
    by codex×2 + Opus A3): Prop 5.2 reproved by splitting on `isEmpty_or_nonempty (Pt Ω)`
    (the empty regime makes every history independent of the conditioning event —
    `history_indep_of_isEmpty_pt` — and `history_pair` does the rest). No axiom is false in
    any degenerate case. The `Type v` restriction remains (structure fields cannot quantify
    over universes; Theorem 6.2/Prop 6.6/Lemma B.1 stay universe-polymorphic).
  * Table 1's negative claim is now `not_intersection_structIndepRel` (pairwise-distinct
    `X = U`, `Y = U+1`, `Z = U+2` on one `Fin 3` factor — the old `X = Y` witness was
    degenerate under Pearl's disjointness convention, R3-F57) with
    `not_isGraphoid_structIndepRel` derived from it.
  * Definition 6.1 (`CondIndep*`) is over an arbitrary `{S} [Fintype S]` (R3-F34); its
    events are `{s | X s = x}` — `fiber X x` unfolded — so `rw`/`set` against
    `fiber`-stated lemmas needs `show … (fiber …) …` or a type-ascribed `have` first
    (sites: Probability C.13/C.14/`condIndepVarEvent_proj_of_disintegrates`, Completeness
    C.18, Semigraphoid, Probability `condIndepVar_map`, Examples `isPerfectMapDAG_G₁_Q`).
  * Non-vacuity (Lens C, R3-F54): `not_factorizes_diag`, `not_isFactoredSpaceModel_const`,
    `not_factorizesOverDAG_diag`, and the edge-carrying perfect map `isPerfectMapDAG_G₂_Pedge`
    (checking `IsPerfectMapDAG` on a two-node DAG collapses to `V₁ ⊆ V₃ ∨ V₂ ⊆ V₃` via
    `condIndepVar_proj_of_subset_left/right`, `CondIndepVar.of_proj_subset`,
    `not_condIndepVar_proj_self` — no 64-triple bash). Prop 6.6 now has a client test at a
    proper open `S` (`heavyOnOnes`, APITests) enabled by `Distr.abs_sub_le_euclDist`.
  * Lemma C.10's carrier is `interp_mem_factorizingPos` (`P^λ ∈ Δ^*_C(Ω)`, both halves);
    `history_unique_minimal` is an iff naming `history`; idle `[Nonempty α]` dropped from
    `history_mono_of_derived` (only `[Nonempty β]` load-bearing — corrects the round-2 note)
    and `mem_history_of_sep`; dead decls removed (`DerivedOn.refl`, `cyl_inter`,
    `mem_unblockedDesc_iff_mem_unblockedAnc`, `OWalk.toWalk`, `Examples.edgeTrail`).
  * Docstrings use the paper's glyphs `Δ^⊗(Ω)` / `Δ^*_C(Ω)` (the macro `\distributionsF`
    prints `Δ^⊗`; `Δ^F` appears nowhere in the PDF); memo citations replaced by
    self-contained statements (the sizing memo is cited once, in Separation.lean).
  * Wontfix (documented): file-wide `linter.unusedSectionVars false` in
    ConditionalHistory.lean (inline binders hand-probed); unnumbered paper claims are
    `lemma`s (the keyword rule requires every `theorem` to carry a numbered node).

* **Relocation pass (2026-08-18) — every recorded relocation debt is discharged; nothing
  is left to move.** What moved, and where to look for it now: the seven `CondIndepTools`
  lemmas (`CondIndep.of_subset_left`, `.of_disjoint_left`, `CondIndepVar.symm`,
  `fiber_proj_subset_or_disjoint`, `condIndepVar_proj_of_subset_left/right`,
  `CondIndepVar.of_proj_subset`, `not_condIndepVar_proj_self`) are §6.1 vocabulary and now
  sit in `Probability.lean` — at the **end** of that file, not next to Corollary C.14,
  because `not_condIndepVar_proj_self` needs `Distr.nonempty_carrier`, which lives in the
  later "Further `Distr` facts" section; `history_eq_empty_iff` is in `History.lean` next
  to `generates_iff_history_subset`; `condIndepVar_map_famJoint` is in `BayesNet.lean`
  beside `famVar`/`famJoint` and is now one line, the `f = famJoint X` case of the new
  generic transport `condIndepVar_map` (pushforward along any `f : S → T`, stated over
  arbitrary finite sample spaces beside Definition 6.1 in `Probability.lean`; `proj S ∘
  famJoint X = famVar X S` is `rfl`, so the corollary is a bare application). Its proof is
  `forall_congr'`×3 then `simp only [CondIndep, Distr.map_prob, Set.preimage_inter]` and
  `exact Iff.rfl` — a `have key : ∀ {κ : Type*} …` helper does **not** work here: the extra
  universe parameter makes the declaration fail with `commitConst: constant has level
  params …`, and the helper never fires as a simp lemma. `Digraph.prevOf` and `prevOf_cons`
  are now `private` (used only inside `ActiveTrails.lean`, under the public
  `ColliderFrom`/`ActiveFrom`). Debts recorded earlier that were **already** resolved and
  are simply gone: `Digraph.depth`/`AncClosed`/`IsAcyclic.not_adj_symm` are in
  `BayesNet.lean` next to `IsAcyclic`, `dSeparated_singleton_parents` is in
  `ActiveTrails.lean`, and every `unblockedAnc`/`zClosure` lemma still in `ActiveTrails.lean`
  (`exists_ascWalk`, `exists_descWalk`, `zClosure_inter_nonempty_of_active_trail`,
  `exists_active_trail_of_zClosure_inter_nonempty`, `dSeparated_iff_disjoint_zClosureSet`)
  mentions walks or trails, so it belongs there rather than in `ConditionalHistory.lean`.

## Intentional deviations from the paper

* **`[Nonempty β]` in Lemma C.3 (`derivedOn_iff`).** The paper's (ii)⟹(i) direction
  chooses `f(x)` "arbitrary" for unattained `x`, which presupposes `Val(Y)` inhabited; the
  statement is false for `C = ∅`, `Val(X)` nonempty, `Val(Y)` empty. The hypothesis is
  added and disclosed at the declaration; it propagates as `[Nonempty α]` on
  `generates_iff` and its consumers. See errata.

## Disclosures (residual modeling substitutions)

None.

## Paper errata

All in `notes/paper-errata.md` (E1–E17; E9–E13 from the round-1 audit, E14–E17 from round 2: Prop 5.8(2)'s "arbitrary P", the empty-projection singleton, Lemma A.1's missing union inclusion, Lemma A.2 false for `Val(X) = ∅` and its swapped identities, cosmetic slips in 4.8/C.9/C.20): C.3 needs `Val(Y) ≠ ∅` (E1); factors may be empty
(E2); **C.11(3) false as printed** — needs the `I∖J`-marginal supports too (E3); C.10's
displayed inequality false at `I = ∅` (E4); **Lemma 5.3 "τ bijective" false** — true on
strictly positive distributions (E5); Def 5.7(2) types `X_w : Ω → Obs` (E6); **Prop 5.8(1)'s
proof omits that `M^G` is a model of `P`** (E7); d-separation undefined, endpoint convention
load-bearing (E8).

## Pitfalls

* `rw [h]` with `h : S = splice J S T` also fires inside `projSet J S` on the goal's RHS;
  use `conv_lhs => rw [h, splice_eq_cyl_inter]` then `exact Distr.prob_cyl_inter_cyl …`.
  Expect this in every `P.prob E = (P.marg J).prob (projSet J E) * …` step.
* Mathlib's `Finset.piecewise_compl : sᶜ.piecewise f g = s.piecewise g f` (complement on the
  LHS, arguments swapped) and `Finset.piecewise_same`; ours are `splice_compl : splice Jᶜ S T =
  splice J T S` and the root-`Finset` `piecewise_union`/`piecewise_inter` (Basic.lean).
* `Disintegrates` is a `def` wrapping an `Eq`: no `hd.trans`; to get `C = splice J C C`
  from `hd`, `rwa [Disintegrates, prodSplit_eq_splice] at h'`.
* `[Nonempty α]` on the history lemmas is found automatically at `α := Prop` (event
  histories via `indic`); no hint needed.
* `hf : ∀ t : unitInterval, f.eval (t : ℝ) = …` cannot be applied with `hf _` against a
  bare real `s` (unification does not invert the coercion): pass `hf ⟨s, hmem⟩` explicitly.
* `Polynomial.eval_finset_sum` is deprecated → `Polynomial.eval_finsetSum`;
  `natDegree_prod_le`/`natDegree_sum_le_of_forall_le` need
  `Mathlib.Algebra.Polynomial.BigOperators`; `Set.Ioo_infinite` needs
  `Mathlib.Order.Interval.Set.Infinite`; `(Set.Ioo_infinite h).mono hsub` (dot notation on
  the infinite set).
* For a degree-≤1 polynomial prefer `C a + C (b − a) * X` over `C a * (1 − X) + C b * X`:
  the degree bound is then four lemma applications, no `compute_degree`.
* `push_neg` is deprecated → `push Not`.
* **A seeded `.lake` makes `#print axioms` lie**: `lake env lean Scratch.lean` importing a
  module you just edited elaborates against the *stale* olean from the seed; run the gate
  `lake build` before any axiom check.
* **The `omit` cascade**: once one lemma sheds instance variables via `omit`, downstream
  lemmas that only used it start warning too; iterate the linter's own suggestion lines.
  A sorried lemma may show a different unused-variable set than the finished one.
* `WellFounded.fix` at a function-valued motive: `show hG.wf.fix (C := fun v => Pt … → Val v)
  F v ω = _; rw [WellFounded.fix_eq]; rfl` — the motive must be given explicitly.
* `Function.update_of_ne` against `Pt (bnFactor G Val)` needs `(β := bnFactor G Val)`;
  `Finset.sum_nbij'`'s value hypothesis is last; `Finset.prod_image` takes `Set.InjOn`.
* `Finset.sum_div` lives in `Mathlib.Algebra.BigOperators.Field` (now imported by
  Probability.lean); `Set.Icc_infinite` in `Mathlib.Order.Interval.Set.Infinite`;
  `Polynomial.finite_setOf_isRoot` is the name; `Set.Infinite.mono` takes the subset first
  (`hinf.mono hsub`); `Set.indicator_of_notMem`, `Set.notMem_empty`,
  `Function.update_self`/`update_of_ne` are the current names.
* `linear_combination` is NOT in the import closure — and an unknown tactic silently
  swallows the rest of the `by` block, reporting a misleading `unsolved goals`. Use
  `have : … := by ring` + `rw` + `ring`, or `linarith` (which handles bilinear identities).
* `unitInterval` coercion lemmas are `Set.Icc.coe_zero/coe_one`; `((⟨x,hx⟩ : unitInterval) : ℝ) = x` is `rfl`.
* `set x := e with h` traps: `set` an index-set abbreviation BEFORE introducing anything
  whose type mentions it; `set` folds only existing occurrences; prefer generalising to a
  lemma over `set` when the abbreviation appears under `Finset` complement/coercion.
* `CondIndep`, `PQIrrelevant`, `Irrelevant`, `Factorizes` are plain `def`s: no dot notation,
  `rw` needs `simp only [CondIndep]`/`show`; `unfold CondIndep at h` fails when `h` is a
  `CondIndepEventVar` (binder) — unfold on the goal and `exact h y`.
* Destructuring `hPQ : (P, Q) ∈ pairsDifferingAt C i` yields facts about `(P,Q).1`; restate
  with ascriptions before `obtain ⟨p, rfl⟩ := (factorizes_iff_exists_prod P).mp _`.
* `Fintype.sum_equiv e f g h`: pass `f` explicitly or the rewrite pattern comes out as
  `∑ x, g (e x)`; `rw [← Fintype.sum_prod_type]` needs the function given — use `calc`.
* Stating a helper with a bare `if s ∈ A then …` over a `Set` forces `Decidable` into the
  statement; use `Set.indicator` and `Set.indicator_apply` in proofs.
* NEVER `rw` an index inside a dependent lookup `ω i` (motive check fails); use
  `table_congr` by `exact`/`.trans`. Sigma-index disequalities: `idx_ne_of_node_ne`,
  `idx_ne_of_config_ne` (`Sigma.mk.injEq` + `eq_of_heq`; `injection` misbehaves here).
* Prefer `obtain ⟨a, ha⟩ : ∃ a, a = e := ⟨_, rfl⟩` over `set` for constructed points of
  `Pt (bnFactor G Val)`; `Finset.piecewise` under an eta-expanded index: keep it folded and
  use `Finset.piecewise_eq_of_mem/of_notMem` explicitly; `subst h : a = b` replaces `b` by
  `a`; `clear` stale hypotheses before `ReflTransGen.head_induction_on`;
  `nodeVar_ne_of_prop` needs `(Z := Z)`.
* Definitional bridges: `parentConfig G Val (jointVar hG ω) v p` ≡ `nodeVar hG p.1 ω`;
  `nodesVar hG A ω a` ≡ `nodeVar hG a.1 ω`; `unblockedDesc`/`unblockedAnc` membership are
  `Iff.rfl` duals.
* `push Not` on `¬(s = ∅ ∨ t = ∅)` for `Finset` yields `s.Nonempty ∧ t.Nonempty`.
* `rw [f, dif_pos h]` fails when `h` matches the `dite` condition only definitionally; use a
  term-mode `have he : … := dif_pos h`.
* A dependent `abbrev Val : Bool → Type | false => Fin 3 | true => Bool` works verbatim
  with pattern-matching instances (`inferInstanceAs`); no constant-`Val` fallback needed.
* Concrete finite witnesses over dependent value families cost MORE than general theorems
  with good lemma support (Prop 5.8(2) witness ≈360 lines vs the I-map theorem ≈140).
* `cases h : e with | false | true` on a `Bool` expression rewrites the goal, not
  hypotheses; `rintro ⟨-, -, -, hx, -⟩` clearing an existential witness renames later
  hypotheses; on an indexed inductive use `| @consF u v w h p ih` to name implicit vertices;
  `subst hh : v = s` eliminates `s`. `List.isChain_cons` states its head condition via `head?`.
* Iteration cost calibration: with warm oleans `lake env lean` on a 600-line file is 3–7 s;
  a §C.3-sized lemma is tens of minutes, not hours; the Appendix-C probability bookkeeping
  (28 obligations) took ~1 h wall clock once the two transports (`splitEquiv`, `unionEquiv`)
  existed. Only the final gate needs `safe-lake.sh build`.

* `omit [Fintype I] in` / `omit [DecidableEq I] in` must precede the docstring, not sit
  between the docstring and the declaration.
* `Finset.piecewise` unfolds by `simp [Finset.piecewise, hi]`; after `set c := J.piecewise
  a b`, `simp [hc, hi]` already suffices and the extra `Finset.piecewise` argument is
  flagged unused.
* `Jᶜ` on `Finset I` needs `[Fintype I]` in scope (`Compl (Finset I)`), so every lemma
  mentioning a complement sits after `variable [Fintype I]`.
