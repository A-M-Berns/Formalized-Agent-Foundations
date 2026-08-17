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
| distribution on a finite type `S` (`Δ(S)`) | `Dist S` (`mass`, `nonneg`, `sum_eq_one`); `P(A)` is `P.prob A` | `dd:dist` |
| `P(A \| C)` | `P.condProb A C` (`= 0` when `P(C) = 0`) | |
| `supp(P)`, `δ_s`, `(1−λ)P + λQ` | `P.support`, `Dist.delta s`, `Dist.mix t P Q` | |
| `P_i = P ∘ U_i⁻¹`, `P_J` (Def C.2) | `P.margAt i`, `P.marg J` (`Dist.map (proj J)`) | |
| `⨂_i P_i` | `Dist.prod p` | |
| `P` factorizes over `Ω` (Def 4.3), `Δ^F(Ω)`, `Δ^F_C(Ω)` | `Factorizes P`, `factorizing Ω`, `factorizingPos C` | pointwise, literal |
| `M = (Ω, O)` is an FSM for `P` (Def 4.4) | `IsFactoredSpaceModel O P` | |
| `P_J ⊗ P_K` (Def C.1) | `Dist.outer h PJ PK`; the always-used `P_J ⊗ P_{I∖J}` on `Ω` is `Dist.outerCompl PJ PK` | |
| `A_J × A_{I∖J}` for `A_J ⊆ Ω_J` | `cyl J A ∩ cyl Jᶜ B` | `splice_eq_cyl_inter` bridges to `splice` |
| `D^α` | `sliceAt J α D` | |
| `A ⊥^P B \| C`, `X ⊥^P Y \| Z` (Def 6.1), mixed forms | `CondIndep P A B C`, `CondIndepVar P X Y Z`, `CondIndepEventVar`, `CondIndepVarEvent` | product form only |
| `A ⊥^⊗ B \| C` | `CondIndepAll A B C` | |
| `R^λ = ⨂((1−λ)Q_i + λP_i)` | `interp Q P t` | `t : unitInterval` |
| Euclidean distance on `Δ(Ω)` | `Dist.euclDist` | |
| `(P,Q)`-irrelevant, irrelevant, `Cohistory(A\|C)` (Def C.6), `Δ^F_{C,i}` | `PQIrrelevant`, `Irrelevant`, `cohistory`, `pairsDifferingAt` | |
| Lemma 6.3 / 6.4 / 6.5 / Thm 6.2 / Prop 6.6 | `condIndep_of_disjoint_eventHistory` / `disjoint_eventHistory_of_condIndepAll` / `condIndepVar_of_local` / `structIndepGiven_iff_forall_condIndepVar` / `structIndepGiven_of_open` | |
| Lemmas C.5, C.7, C.8, C.9, C.10, C.11, C.12, C.13, C.14, C.15, C.16, C.17, C.18, C.19, C.20 | `exists_polynomial_interp_prob`, `cohistory_union_eq_univ_of_condIndepAll`, `cohistory_eq_compl_eventHistory`, `pqIrrelevant_or_of_condIndepAll`, `interp_prob_pos`, `Dist.prob_pos_of_support_subset`/`support_outerCompl`/`prob_pos_of_marg_support_subset`, `condProb_eq_of_agree_on_relevant`, `CondIndepEventVar.of_pair`, `CondIndepEventVar.of_proj_subset`, `Dist.prob_cyl_inter_cyl`, `Factorizes.prob_sliceAt`/`Dist.prob_outerCompl_delta`, `condIndepVarEvent_proj_history`, `condIndepEventVar_proj_cohistory`, `condIndepVarEvent_proj_cohistory`, `disintegrates_cohistory` | |
| semigraphoid / graphoid / compositional (Def 5.1); Prop 5.2 | `IsSemigraphoid`, `IsGraphoid`, `IsCompositionalSemigraphoid` on an `IndepRel Ω`; `isCompositionalSemigraphoid_structIndepRel` (`structIndepRel Ω`) | value spaces `Type v`, nonempty |
| DAG `G = (V, E, Val)`, `pa(v)`, `an(v)` | `G : Digraph V` with `hG : G.IsAcyclic`, `Val : V → Type u`, `G.parents v`, `G.IsAncestor u v` | root `Digraph` namespace |
| `I_v`, `I`, `Ω^G`, `X_v`, `X`, `X_S` | `ParentVals G Val v`, `bnIndex G Val` (`Σ v, ParentVals`), `bnFactor G Val`, `nodeVar hG v`, `jointVar hG`, `nodesVar hG S` | `nodeVar_apply` is eq. (4) |
| `P` factorizes over `G` (eq. (4)), `Δ^*(G)`, CPDs | `FactorizesOverDAG G Val P`, `dagFactorizing G Val`, `CPD`, `condCPD P hpos` | `dd:cpd` |
| `τ`, `τ⁻¹` (Lemma 5.3) | `tau hG`, `tauInv φ`; `tauPos_bijective`, `tauInv_condCPD_tau` | true form, see errata E5 |
| Lemma B.2 / Prop 5.4 / Prop 5.6 | `prob_jointVar_fiber` / `factorizesOverDAG_iff_isFactoredSpaceModel` / `isAncestor_iff_strictlyBefore` | |
| trail, active trail, d-separation | `Digraph.Trail`, `Digraph.Walk`, `Walk.IsColliderAt`, `Walk.Active`, `Trail.Active`, `Digraph.DSeparated` | `dd:dsep` |
| `A_Z(v)`, `Z`-closed, `S_Z(s)`, `S_Z(A)`, `I^z` (memo) | `Digraph.unblockedAnc`, `Digraph.IsZClosed`, `Digraph.zClosure`, `Digraph.zClosureSet`, `zConsistent` | `ConditionalHistory.lean` |
| Prop 5.5 | `dSeparated_iff_structIndepGiven` | direct route |
| perfect map (Def 5.7), Prop 5.8 | `IsPerfectMapDAG`, `IsPerfectMapFSM`; `isPerfectMapFSM_nodeVar_of_isPerfectMapDAG`, `exists_isPerfectMapFSM_of_exists_isPerfectMapDAG`, `exists_isPerfectMapFSM_not_exists_isPerfectMapDAG` | |

## Design decisions

* **Splice encoding (`dd:splice`).** The obvious rendering of `C_J × C_{I∖J}` through
  `(∀ i : ↥J, Ω i)` and transports across `↥(J ∪ K) ≃ ↥J ⊕ ↥K` makes §4 and Appendix A a
  dependent-subtype slog. Disintegration is equivalent to closure under
  `Finset.piecewise` (`disintegrates_iff_splice`, proved against the literal product form),
  after which Lemma A.1 is two `piecewise` rewrites (`piecewise_union`, `piecewise_inter`)
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
* **Semigraphoid axioms via Theorem 6.2.** Proposition 5.2's axioms 1–4 are proved, as in
  the paper, from soundness+completeness and the semigraphoid axioms of probabilistic
  conditional independence — but the latter are *proved* for the paper's Definition 6.1
  (product-identity form, `P(C) = 0 ⟹ independent`), not cited from Pearl, so no
  citation boundary remains. Composition (axiom 6) is Lemma B.1, proved directly from
  `history_pair`. (Stage 3.)

* **`Dist` rather than `FiniteFactoredSets.ProbDist` (`dd:dist`).** FFS's distribution is
  event-based (`Set S → ℝ`, additivity) because Garrabrant's Definition 36 is; this paper's
  Definition 4.3, its factorwise interpolation `⨂((1−λ)Q_i + λP_i)`, delta and outer
  products are all pointwise, so the mass function is the object manipulated. Not a
  duplicate: different shape, and neither is a repo-shared module. Revisit only if a shared
  `Common/` probability layer is ever created.
* **Factorization over a DAG is the CPD form (`dd:cpd`).** Eq. (4)'s `P(x_v | x_pa(v))`
  are conditional probability distributions specified per node and parent configuration
  (Koller–Friedman Def 3.5, which the paper follows). Reading them as `P`'s own
  conditionals fails at parent configurations of probability zero (`0/0`), and that is
  precisely what breaks Lemma 5.3's bijectivity (errata E5). For strictly positive `P` the
  CPDs *are* the conditionals (`condCPD`), which is the regime in which Lemma 5.3 is true
  and stated (`tauPos_bijective`, `tauInv_condCPD_tau`).
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
  (`Dist.prob_prod_inter_bg`), giving the conditional probability directly. Also:
  strictly positive members of `Δ^*(G)` have strictly positive CPDs (every `(v, y, a)` is
  realized by a joint value since `v ∉ pa(v)`), which is what makes `tauPos` surjective.
* **Where inhabitation comes from in §5.2.** `Nonempty (Pt Val)` from any
  `Dist (Pt Val)` (`Dist.nonempty_carrier`) is the cheap source of `Nonempty (Val u)` for
  all `u`; do not try to get it from a point of `Ω^G` (circular). In the history section it
  comes from `[∀ v, Nontrivial (Val v)]`, and `Nonempty (ParentVals G Val v)` is then
  `inferInstance` — the paper's "since `I_v` is nonempty" step of Proposition 5.6.
* **Lemma C.7's proof avoids topology on `Δ^F_{C,i}`**: the paper's "continuous, hence
  nonzero on an open set" step is replaced by "the numerator polynomial has finitely many
  roots" (`Polynomial.finite_setOf_isRoot`); same content, no topology on distributions.
* **Lemma C.12 does not use C.11(3)** (false as printed): positivity along the
  replacement chain comes from `Dist.prod_mass_pos_iff` + C.11(1), and the interpolant is
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

## Intentional deviations from the paper

* **`tauInv_condCPD_strictlyPositive` takes `hG : G.IsAcyclic`** (non-paper helper): false
  over an arbitrary digraph — a self-loop at `v` empties `{x_v = a} ∩ {x_pa(v) = y}` for
  `a ≠ y_v`. The paper only considers DAGs.

* **`[Nonempty β]` in Lemma C.3 (`derivedOn_iff`).** The paper's (ii)⟹(i) direction
  chooses `f(x)` "arbitrary" for unattained `x`, which presupposes `Val(Y)` inhabited; the
  statement is false for `C = ∅`, `Val(X)` nonempty, `Val(Y)` empty. The hypothesis is
  added and disclosed at the declaration; it propagates as `[Nonempty α]` on
  `generates_iff` and its consumers. See errata.

## Disclosures (residual modeling substitutions)

None.

## Paper errata

All in `notes/paper-errata.md` (E1–E8): C.3 needs `Val(Y) ≠ ∅` (E1); factors may be empty
(E2); **C.11(3) false as printed** — needs the `I∖J`-marginal supports too (E3); C.10's
displayed inequality false at `I = ∅` (E4); **Lemma 5.3 "τ bijective" false** — true on
strictly positive distributions (E5); Def 5.7(2) types `X_w : Ω → Obs` (E6); **Prop 5.8(1)'s
proof omits that `M^G` is a model of `P`** (E7); d-separation undefined, endpoint convention
load-bearing (E8).

## Pitfalls

* `rw [h]` with `h : S = splice J S T` also fires inside `projSet J S` on the goal's RHS;
  use `conv_lhs => rw [h, splice_eq_cyl_inter]` then `exact Dist.prob_cyl_inter_cyl …`.
  Expect this in every `P.prob E = (P.marg J).prob (projSet J E) * …` step.
* `piecewise_compl : Jᶜ.piecewise a b = J.piecewise b a` (complement on the LHS, arguments
  swapped); `splice_compl : splice Jᶜ S T = splice J T S`.
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
