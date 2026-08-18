import Condensation.Probability
import Condensation.Model
import Condensation.ChainRule
import Condensation.Morphism
import Condensation.Perfect
import Condensation.Amalgamation
import Condensation.Comparison
import Condensation.Quantitative
import Condensation.Examples

/-!
# Condensation consumer API

The supported downstream import for condensation research is:

```lean
import Condensation.API
```

Everything below lives in the `Condensation` namespace.  `open Condensation` reaches the
namespace-level vocabulary, and dot notation reaches the rest off a model (`M.joint A`), a
latent model (`L.condScore A`) or a morphism (`φ.comp ψ`).  **If your own namespace ends in
`Condensation` — as `APITests.Condensation` does — write `open _root_.Condensation`.**  A
bare `open Condensation` there resolves to your *own* namespace, succeeds with no warning,
and then every name fails as an unknown identifier; with `autoImplicit` on it fails even
more obscurely, as `RVModel` silently becomes an implicit binder.  §3.1's `≫`/`𝟙`/`⟶`
notation additionally needs `open CategoryTheory`: this library writes
`CategoryTheory.CategoryStruct.comp` out in full and never opens it, so a client is the
first place the notation appears.

## Status — read this before depending on anything

**Milestone M2, landed 2026-08-18.**  All 39 in-scope nodes of Eisenstat, *Condensation: A
Theory of Concepts* (July 2025, OpenReview `HwKFJ3odui`) carry Lean declarations, every
one of them is proved, there is no `sorry` anywhere in `Condensation/`, and every annotated
endpoint is axiom-clean — nothing beyond `propext`, `Classical.choice` and `Quot.sound`.

**This paper is nevertheless still registered `in-progress`,** and the boundary you are
reading is therefore *not* a frozen surface.  Two steps remain, in this order: the human
read-through of every top-level statement and definition, and a final fresh-context
adversarial audit.  Statements may still move as a result.  `Condensation/README.md`,
*Consumer readiness*, tracks the five completion criteria one at a time; this file and
`APITests/Condensation.lean` are criteria 4 and 5.

Three of the paper's 42 nodes are **out of scope by a proposed ruling**: Examples 5.1, 5.2
and 5.3.  5.1 and 5.2 posit `[0,1]`-valued latent variables, outside the paper's own
countable-discrete framework; 5.3 is a prose translation of structural causal models
carrying no claim.  Nothing downstream cites any of the three.  Because the ruling is
*proposed* rather than settled, `scripts/check-condensation-nodes.py` reports coverage as
39/42, not 42/42.

### Errata a client should know about

Twenty-two defects in the printed paper are recorded in
`Condensation/notes/paper-errata.md`, and **that file is the first place to look when a
Lean statement here appears to diverge from the printed one** — in several places the
printed text is the thing that is wrong.  Three bear on statements you are likely to use:

* **Lemma 4.14 is false as printed** (entry 15).  The printed binders constrain only the
  probability space and `C`'s range; nothing makes `X`'s range separate points, and when it
  does not, the conditional-independence hypothesis can be vacuous while the conclusion is
  a real constraint.  The counterexample is machine-checked.  The repair is a *corrected
  binder*, not a weakened conclusion: `aeFunctionOf_of_condIndepFun` carries
  `[MeasurableSingletonClass S]` on `X`'s range, free at every call site (`X` is always a
  model variable and `RVModel` carries `singR`) and licensed by the paper's own standing
  setting — Definition 3.1 and §2 — that every random variable under consideration has
  countable discrete *range*.  (Not by the §2 sentence about probability *spaces* being
  countable and discrete: that constrains `Ω`, and the erratum is precisely that
  constraining `Ω` alone leaves the lemma false.)
* **Definition 4.12 does not tie `π̃₁` to `π̃₂`** (entry 10).  Theorem 4.15's proof needs
  them to agree almost everywhere, so `LatentAmalgamation` carries the a.e. commutation as
  the explicit field `comm`.  That is the *only* added field; a client constructing a
  `LatentAmalgamation` by hand must discharge it.
* **Theorem 5.8 and Corollaries 5.9, 5.10 are vacuous at `F = ∅`** (entry 14).  Definition
  5.6(1)'s tree has a root, hence at least one leaf, while the bijection the theorem demands
  would have to match those leaves against an empty family; no such tree exists.  This is a
  property of the printed statement, not of the rendering, which is why
  `condEntropy_jointAbove_le_choose` (5.25) carries no `1 ≤ k` hypothesis while
  `polar_kSubsets` (5.24), which has no tree in sight, keeps it.

## Vocabulary

### §2 — conventions and the determinism bridge (`Condensation/Probability.lean`)

* **"is a function of"** (Definition 2.1's fifth convention, `dd:ae-function`).
  `FunctionOf X Y` is `∃ f, Measurable f ∧ Y = f ∘ X`; `AEFunctionOf X Y μ` is the same with
  `∀ᵐ ω ∂μ`.  The measure is an explicit argument, as in the vendored entropy API.  The
  algebra a client composes with is `AEFunctionOf.of_functionOf`, `.comp` (post-compose a
  measurable map), `.trans`, `.prodMk`, `.pi`, `.comp_measurePreserving`, `.congr_left`,
  `.congr_right`, `.prodMk_left`, and `aeFunctionOf_self`.  `IsRandomVariable` is
  Definition 2.1's Mathlib rendering (an `abbrev` for `Measurable`), so the whole
  `Measurable` API applies to it unchanged.
* **Pullback invariance**, equation (2.2) (`dd:pullback`).  A pullback `π^* X` is plain
  composition `X ∘ π` and probability-preserving is Mathlib's
  `MeasureTheory.MeasurePreserving`; nothing is redefined.  The four identities licensing
  the paper's convention that a variable on `Ω` may be read on `Λ` are
  `identDistrib_comp_measurePreserving`, `entropy_comp_measurePreserving`,
  `mutualInfo_comp_measurePreserving` and `condEntropy_comp_measurePreserving`.
* **`P⁺I`** (Definition 2.2, `dd:pplus`) is `PPlus I = {A : Finset I // A.Nonempty}` — a
  subtype, faithful to "nonempty subsets only" with no phantom `Y_∅`.  `A.toFinset` is the
  underlying `Finset` (with a `CoeHead`), `i ∈ A` is membership, `PPlus.single i` the
  singleton, and the order is inclusion (`PPlus.le_iff`, `PPlus.lt_iff`).  Over `[Finite I]`
  — which every model carries — `PPlus I` is finite by instance
  (`Condensation.instFiniteFinset`, `Condensation.PPlus.instFinite`); no `Fintype` or
  `DecidableEq` datum is ever needed.
* **Interaction information** (Definition 2.3, `dd:interaction`): `interactionInfo X Y Z μ`
  is `I(X;Y) − I(X;Y|Z)` and `condInteractionInfo X Y Z C μ` its conditional form
  `I(X;Y|C) − I(X;Y|⟨Z,C⟩)`.  Full permutation symmetry comes from `interactionInfo_comm`
  together with `interactionInfo_swap` (and `condInteractionInfo_comm`/`_swap`/`_rotate` in
  the conditional case).  These are FAF-authored `def`s: the shared Shannon layer
  deliberately adds no definitions, so interaction information is paper-specific here until
  a second client needs it.
* **Proposition 2.5, the determinism bridge**, is the single most useful §2 endpoint and
  the one a client reaches for constantly: `aeFunctionOf_of_condEntropy_eq_zero` is the
  paper's direction, `condEntropy_eq_zero_of_aeFunctionOf` its converse, and
  `aeFunctionOf_iff_condEntropy_eq_zero` the equivalence §4 actually uses —
  `AEFunctionOf X Y μ ↔ H[Y | X ; μ] = 0`.  Read as a *test*: a vanishing conditional
  entropy is exactly a.e. functional dependence.  Its two entropy consequences are
  `entropy_le_of_aeFunctionOf` (data processing in the form §4 uses) and
  `entropy_pair_of_aeFunctionOf` (adjoining a function of `X` to `X` changes no entropy),
  with `condEntropy_congr_of_aeFunctionOf`, `condEntropy_le_condEntropy_of_aeFunctionOf`
  and `condEntropy_le_of_aeFunctionOf` the comparisons §4 and §5 run on.
* **Degenerate cases**, which is where a concrete client witness spends its time:
  `entropy_eq_zero_of_subsingleton`, `condEntropy_eq_zero_of_subsingleton`,
  `condEntropy_eq_entropy_of_subsingleton` (conditioning on a variable into a subsingleton
  costs nothing — this is what makes a maximal `B ∈ P⁺I`, with `strictAbove B = ∅`,
  computable).  For joint independence over a subsingleton index type, cite **Mathlib's**
  `ProbabilityTheory.iIndepFun.of_subsingleton` (it is `@[simp]`); this library carried a
  duplicate of it until 2026-08-18 and no longer does.

### §3 — models, latent models, joint variables and scores (`Condensation/Model.lean`)

* **`RVModel I`** (Definition 3.1, `dd:bundled-model`) bundles the sample space `Ω`, its
  σ-algebra/countability/singleton-class instances, the measure `P`, **its finite entropy**,
  the range family `R : I → Type v` with their instances, the variables `X i`, their
  measurability and their finite entropy.  `[Finite I]` is a *class parameter of the
  structure*, not a field — Definition 3.1's "finite family" — because `Finite I` does not
  mention the model and as a field would never be found by instance search, which would let
  a score over `I = ℕ` elaborate with every sum silently empty.  Construct one with
  structure-instance syntax giving `Ω`, `P`, `R`, `X`, `measurable_X` and `finiteEntropy_X`;
  the bracketed instance fields are filled by search.
  `RVModel.finiteEntropyOf` is the workhorse: **any** measurable variable on a model's
  sample space has finite entropy, in one step from Definition 3.1's clause on `Ω`.  It is a
  lemma rather than an instance because instance search cannot discharge the `Measurable`
  side condition — so a derived variable needs `haveI := M.finiteEntropyOf hZ`.
* **Joint variables** (Definition 3.4): `M.joint A` is `X_A` at a `Finset A ⊆ I`, `M.jointOn F`
  is `Y_F` over a `Set` of indices, `M.jointAll` the whole family.  Each comes with its
  measurability (`measurable_joint`, `measurable_jointOn`) and, unlike `finiteEntropyOf`, a
  registered finite-entropy *instance* (`finiteEntropy_joint`, `finiteEntropy_jointOn`,
  `finiteEntropy_jointAll`).  The monotonicity a client rewrites with is
  `functionOf_jointOn_mono` / `aeFunctionOf_jointOn_mono` (`G ⊆ F` makes `Y_G` a function
  of `Y_F`), `functionOf_jointOn_union` and `functionOf_joint`.
* **The four families** of (3.5)–(3.8) are *plain sets* `Set (PPlus I)`, which keeps §4.10's
  and §5's upward-closure, polar and intersection algebra as set algebra: `contrib A`
  (`∩A`), `above A` (`⊇A`), `strictAbove A` (`⊋A`), `contribIdx i` (`∋i`), plus
  `incomparable A`, spelled with Mathlib's `IncompRel`.  Membership is `Iff.rfl` in every
  case (`mem_contrib`, `mem_above`, `mem_strictAbove`, `mem_contribIdx`,
  `mem_incomparable`, and `mem_contrib_iff` under `[DecidableEq I]`).  The rewriting glue is
  `contribIdx_eq_contrib_singleton`, `contribIdx_eq_above_singleton`,
  `strictAbove_subset_above`, `contribIdx_subset_contrib`, `above_mono`,
  `isUpperSet_contrib`, `isUpperSet_above`, `isUpperSet_iInter_contribIdx` and
  `contrib_injective`.
* **`LatentModel M`** (Definition 3.2) bundles a latent `RVModel (PPlus I)` called `L`, the
  probability-preserving `π : L.Ω → M.Ω`, and Definition 3.2's contribution condition
  `contributes : ∀ i, AEFunctionOf (L.jointOn (contribIdx i)) (M.X i ∘ π) L.P`.  Its
  universes are **independent** of `M`'s (`LatentModel.{u, v, w, u', v'}`): nothing in the
  paper ties them, and Example 4.4 is not statable in its printed generality if they are
  pinned together.  The abbreviations a client reads with are `L.Λ`, `L.P`, `L.Y`,
  `L.jointOn`, `L.jointContrib A` (`Y_∩A`), `L.jointAbove A` (`Y_⊇A`),
  `L.jointStrictAbove A` (`Y_⊋A`), `L.jointContribIdx i` (`Y_∋i`) and `L.pullbackJoint A`
  (`π^* X_A`, with `entropy_pullbackJoint` for its convention-(2.2) entropy).
* **The three scores** (Definition 3.3) are real numbers, Definition 3.1's finite-entropy
  sample space making every entropy in them finite: `L.simpleScore A` (`σ_L`),
  `L.condScore A` (`χ_L`) and `L.reconScore A` (`ϱ_L`).  The first two are sums over
  `famFinset (contrib A)`, and **`famFinset` is how you compute one**: it is
  `Condensation.famFinset : Set (PPlus I) → Finset (PPlus I)`, namespace-level rather than
  on the model, with the `@[simp]` `mem_famFinset` as its only interface.  A concrete score
  is evaluated by proving a `famFinset (contrib A) = {…}` equation (`ext`, `simp only
  [mem_famFinset, mem_contrib, …]`, `revert`, `decide`) and then rewriting termwise.

### §3.1 — the category of models (`Condensation/Morphism.lean`, `dd:category`)

`RVModelObj` is the object type; it carries its index type as a **field**, because
Definition 3.5 lets a morphism change the index set, so the index cannot be a parameter of
the object type.  `RVModel.Hom M N` (Definition 3.5) carries `π`, `π_pres`, `ι`, `f` and
`eq_ae` — and deliberately **no** measurability field for `f`: Definition 3.5's own remark
is that measurability is automatic on countable discrete ranges, which is
`RVModel.Hom.measurable_f`.  The morphism's own pullback fact, `RVModel.Hom.aeFunctionOf`,
is what lands a client back in §2's vocabulary without unfolding the triple.

`RVModel.Hom.comp` is Definition 3.6, in **diagrammatic order**: `φ.comp ψ` is the paper's
`ψ ∘ φ`, and correspondingly `(φ.comp ψ).ι = φ.ι ∘ ψ.ι` runs contravariantly.  All four
category laws hold by `rfl`, being the corresponding laws for the three components with the
two `Prop`-valued fields carried along, so a client may reassociate and drop identities in a
`calc` with no lemma at all; the instance is `RVModelObj.instCategory` (Proposition 3.7),
with `RVModelObj.id_eq` and `RVModelObj.comp_eq` as the bridges to the bare `Hom`
operations.

Proposition 3.8 is `RVModel.Hom.isIso_iff` — the characterization of the isomorphisms by
three component conditions (`IsMeasurableIso` on `π`, `Function.Bijective` on `ι`,
`IsMeasurableIso` on each `f j`), and it is what a client should use rather than
`inferInstance`.  One elaboration wrinkle to expect: **name `RVModel.Hom.isIso_iff` in full
whenever its argument is spelled `𝟙 _` or `_ ≫ _`.**  Dot notation works on a *variable*
arrow `φ : A ⟶ B`, whose type whnf-reduces to `RVModel.Hom A.M B.M`, but `𝟙 A`'s type is a
stuck projection (`CategoryStruct.toQuiver.1 A A`) and field notation refuses it outright.

Definition 3.9's a.e.-equality is `RVModel.Hom.AEEq` — a.e. equality of `π` together with
equality of `ι`, and **no condition on `f`** — with `RVModel.Hom.aeEq_equivalence` and the
`Setoid` instance `RVModel.Hom.instSetoid` making it usable as `≈` on hom-types, and
`RVModel.Hom.comp_aeEq_congr` (Proposition 3.11) the congruence that lets you transport
along it.  A rough edge here worth knowing before you hit it: `IsEquivalence`'s fields are
spelled `Hom.AEEq _ _`, and a `Setoid.trans`/`Setoid.symm` term whose result type is
`?a ≈ ?b` will **not** unify against them — the `Setoid` instance cannot be recovered from a
stuck `AEEq` goal, and worse, it unifies for `comp_left` and not for `comp_right`, by
elaboration order.  Two workarounds, both fine: restate the composite through an explicitly
`≈`-typed `have` and close the field with `exact` (defeq does the rest), or bypass `≈`
entirely and use `RVModel.Hom.aeEq_equivalence.trans` / `.symm`, which are stated directly
about `AEEq`.

Definition 3.10 has two carriers, `RVModel.IsEquivalence` (the pair predicate, with the
laid-out `RVModel.Hom.ofSameIndex` and `RVModel.isEquivalence_ofSameIndex_iff` beside it)
and `RVModel.Equivalent` (the existential), with `RVModelObj.equivalent_equivalence`
(Propositions 3.11 and 3.12) making the latter an equivalence relation.  Following the
paper, there is **no `Bicategory`**: the paper names the 2-category and declines to use it.

### The chain-rule layer (`Condensation/ChainRule.lean`) — supported client tools

This file carries no paper node.  It is machinery the paper uses without stating, and it is
on this boundary because a client doing quantitative work with joint variables needs it and
neither Mathlib nor the vendored PFR snapshot has it:

* **`RVModel.entropy_jointOn_eq_sum`** — the chain rule for a *finite family* along any
  strict total order `r` on the index type: `H(Y_s) = ∑_{A ∈ s} H(Y_A | Y_{C ≺ A})`.  This
  is the paper's (4.9), (4.29) and (4.34).  Its conditional form is
  `condEntropy_jointOn_eq_sum`.
* **Independence ⟺ additivity, in both directions**:
  `RVModel.entropy_jointOn_eq_sum_of_iIndepFun` (PFR has only the `Fin m`-indexed forward
  half) and `RVModel.iIndepFun_of_entropy_jointOn_eq_sum`, the converse — the paper's
  (4.23)–(4.26).  The hypothesis of the converse is stated at a `Finset` `t` exhausting the
  index type rather than at `Finset.univ`, so no `Fintype` datum has to be produced to name
  it; a client with a `Set`-indexed family passes `famFinset` and `mem_famFinset`.
  `entropy_jointOn_eq_sum_of_subset` (equation (4.25)) and
  `indepFun_X_jointOn_of_entropy_eq` (equation (4.26)) are the intermediate steps, useful on
  their own.
* **Subadditivity** `RVModel.entropy_jointOn_le_sum`, the elementary comparisons
  `condEntropy_pair_jointOn`, `condEntropy_jointOn_mono`, `condEntropy_jointOn_sdiff`, and
  the conditional-independence bridge `condEntropy_jointOn_eq_of_condIndepFun` /
  `condIndepFun_of_condEntropy_jointOn_eq`, which is where erratum 16's corrected sandwich
  `S_A ⊆ W ⊆ I_A ∪ S_A` actually lives.
* **Linear extensions of reverse inclusion**: `exists_strictTotalOrder_ext`,
  `exists_revIncl_strictTotalOrder` and `exists_revIncl_strictTotalOrder_incomparable_first`
  are what turn the paper's "order the family so supersets come first" into a usable `r`.

### §4 — perfect condensation, and comparison of latent models

* **Proposition 4.2** is the score chain, and it is three separate inequalities so that a
  client may cite the link it needs: `LatentModel.simpleScore_ge_condScore`,
  `LatentModel.condScore_ge_entropy_jointContrib` and
  `LatentModel.entropy_jointContrib_ge_entropy_joint`.
* **Definition 4.3** is `LatentModel.PerfectlyCondenses`, with
  `LatentModel.SimplyPerfectlyCondenses` (Definition 4.3's simple form).  The bridges out of
  it are `LatentModel.perfect_entropy_iff_aeFunctionOf` (Lemma 4.5),
  `LatentModel.aeFunctionOf_of_perfectlyCondenses` (Corollary 4.6) and
  `LatentModel.aeFunctionOf_jointContrib_pullbackJoint`.
* **Proposition 4.7** is `LatentModel.aeFunctionOf_iff_isEquivalence_contribModel`, and that
  declaration is its whole carrier — it is *not* one of the TFAE bundles below.  Its clause
  (2) *is* Definition 3.10, which is why `Perfect.lean` imports `Morphism.lean`: the models
  compared are `LatentModel.pullbackModel` and `LatentModel.contribModel`, and clause (2) is
  `RVModel.IsEquivalence` of two `RVModel.Hom.ofSameIndex` triples at `π = ρ = id`.
* **Theorem 4.9** has **two** carriers, and they are different shapes — do not assume the
  `tfae` in both names means both are `List.TFAE`.  `LatentModel.perfect_tfae_A` is a genuine
  `List.TFAE` over (A1)–(A3); project the direction you want with `List.TFAE.out i j`, which
  *does* elaborate in term position against this concrete three-element list (no explicitly
  typed `have` is needed — `APITests/Condensation.lean` exercises exactly that).
  `LatentModel.perfect_tfae_B` is an ordinary `↔` (B1 ⟺ B2), so reach for `.mp`/`.mpr`
  directly; `(L.perfect_tfae_B.mp h).2` is Definition 4.8's ordered Markov condition.
* **Definition 4.8** is `RVModel.OrderedMarkov`.  **Proposition 4.10** is
  `RVModel.orderedMarkov_iff`, which lives in `Condensation/Perfect.lean` immediately beside
  it — and it is phrased with Mathlib's `IsUpperSet` over two upward-closed families of
  `P⁺I`, **not** with `polar`.  (`polar` is Definition 5.5 and belongs to §5's vocabulary
  below; the two are related, but Proposition 4.10 does not mention it.)
* **Definitions 4.11 and 4.12** are the structures `Amalgamation` and `LatentAmalgamation`
  (`dd:amalgamation`).  `Λ₀` is the subtype `{p : Λ₁ × Λ₂ // π₁ p.1 = π₂ p.2}` with the
  discrete σ-algebra and the measure `∑' p, w p • dirac p`, which is the paper's (4.53)
  integral evaluated on a countable discrete space.  `Λ₀` is the **primary** datum: the two
  latent variable models Definition 4.12 names are *derived* (`lat₁`, `lat₂`, over `rv₁`,
  `rv₂`), so their underlying space is `Λ₀` definitionally rather than by a transported type
  equality.  `symm`, `condScore_lat₁`/`condScore_lat₂` and `finiteEntropyOf'` are the derived
  facts §4.15 and §5 run on.  **Lemma 4.13** — the paper's own existence claim — is
  `Amalgamation.canonical` / `nonempty_amalgamation` and `LatentAmalgamation.canonical` /
  `nonempty_latentAmalgamation`, all proved.  **`LatentAmalgamation.diagonal`** amalgamates
  a latent variable model with itself along the identity; it is the constructed, axiom-clean
  inhabitant, and it is the one a non-vacuity argument may cite, because such an argument
  must not be routed through Lemma 4.13's existence theorem.
* **Lemma 4.14** is `aeFunctionOf_of_condIndepFun` (see the errata note above) and
  **Theorem 4.15** is `aeFunctionOf_jointAbove_of_perfectlyCondenses`, whose proof supplies
  the induction the paper omits.  `iInter_contribIdx_eq_above` is the set identity (4.62)
  that induction runs on — the paper writes `F_i` for `contribIdx i` and never defines it.

### §5 — the quantitative theory (`Condensation/Quantitative.lean`)

* **Lemma 5.4** is `condEntropy_eq_of_pair` and `condEntropy_le_of_pair`, its two printed
  forms.
* **Definition 5.5** is `polar F = {B | ∀ A ∈ F, ∃ i ∈ A.toFinset, i ∈ B}`, with `mem_polar`
  (`Iff.rfl`), `mem_polar_iff` (the paper's literal `A ∩ B ≠ ∅`, needing `[DecidableEq I]`),
  `isUpperSet_polar`, `polar_antitone`, the `@[simp]` `polar_singleton`
  (`polar {A} = contrib A.toFinset`) and `polar_empty`, and `polar_eq_iInter` as its
  algebra, with `isUpperSet_inf_closed` beside them.  `ITree.label_eq_polar` is the bridge
  that puts `polar F` on the left of (5.13).
* **Definition 5.6**, the intersection tree, is `ITree` (`dd:tree`): an inductive binary
  tree with each internal node's label *computed* as the meet of its children's labels
  (`ITree.label`).  A directed rooted binary tree with unique paths to the root *is* an
  inductive binary tree, and the `(V, E, ℓ)` presentation would import graph theory for no
  content.  `ITree.leaves`, `ITree.subtrees`, `ITree.LabelsIn`, `ITree.decorate`,
  `ITree.label_eq_polar`, `ITree.label_mem_of_labelsIn` and `ITree.label_eq_leaves_foldr` are
  the working API, and `ITree.intersections` is the paper's family (5.11) — a `List`, because
  the paper itself warns that the same intersection may recur.  Be warned by erratum 13:
  Definition 5.6's "parents" are **children** under the usual convention, and that inversion
  cost one wrong first draft here.
* **Proposition 5.7** is `existsUnique_intersectionTree`, in the paper's **`M`-version**:
  the leaf labelling maps into an intersection-closed collection `M`, and the unique
  extension is a function into `M`, so the statement takes `M`, its closure under `⊓`, and
  `t.LabelsIn M`, and concludes with `d.LabelsIn M` as a third conjunct.
  `eq_decorate_of_isIntersectionTree` is its uniqueness half on its own.
* **Theorem 5.8** is `condEntropy_jointAbove_eq` and `condEntropy_jointAbove_le`, its two
  printed forms; **Corollary 5.9** is `condEntropy_jointAbove_le_reconScore` and
  `condEntropy_jointAbove_le_reconScore_of_orderedMarkov`; **Corollary 5.10** is
  `polar_kSubsets` (5.24) and `condEntropy_jointAbove_le_choose` (5.25).  Theorem 5.8's
  "bijection between the leaves of `T` and `{C : B ∩ C ≠ ∅}` ranging over `B ∈ F`" is
  rendered as the **multiset** equation
  `(T.leaves : Multiset _) = (famFinset F).val.map (fun B => contrib B.toFinset)` — the leaf
  labels *with multiplicity*, which is a bijection rather than a surjection because
  `contrib_injective` makes the right-hand multiset duplicate-free.  Corollary 5.10's family
  is `kSubsets A k = {C | C ≤ A ∧ C.toFinset.card = k}`.

  Two practical notes on instantiating Theorem 5.8, both learned by doing it.  **No instance
  plumbing is needed**: `LatentAmalgamation` carries every finiteness and probability
  instance as a field, so `condEntropy_jointAbove_le Am A F T hupper hleaves` applies with no
  `haveI` and no `(μ := …)` — which is not what one expects from a statement with this many
  entropies in it.  What *does* take work is discharging the leaf multiset condition, and it
  is worth budgeting for: at one leaf it is `have hfam : famFinset ({B} : Set (PPlus I)) = {B}
  := by ext C; simp` and then `by rw [hfam]; rfl`, but at two leaves it needs `classical`,
  `Finset.insert_val_of_notMem` to expose `({B₁, B₂} : Finset _).val` as `B₁ ::ₘ {B₂}`, and
  `Finset.sum_insert` in the final `simpa`.  There is at present no `famFinset_singleton` or
  `famFinset_pair` simp lemma; every client instantiating this theorem re-derives them.

### Constructions and witnesses (`Condensation/Examples.lean`)

This module is **on** the boundary, unlike its counterpart in `FiniteFactoredSets/API.lean`,
and the reason is that it is not a fixture file.  Most of what it carries is *general*:

* `RVModel.jointFamily`, `LatentModel.ofJoint` and `LatentModel.nonempty` — over an
  arbitrary `M : RVModel I`.  `LatentModel.ofJoint M` is the first latent variable model a
  client can reach for without building one, and `nonempty` is the general non-vacuity of
  Definition 3.2.
* `Example41.L₁` and `Example41.L₂` with their four score identities, and `Example44.M44`
  and `Example44.L44` with `entropy_joint_eq` and `simplyPerfectlyCondenses` — Examples 4.1
  and 4.4, *paper nodes*, and stated over an arbitrary model rather than a fixture.  (Note
  erratum 11: Example 4.1's (4.4) and (4.5) are false at `A = ∅`, both scores being the
  empty sum `0` while the right-hand side is `H(X_I)`; the Lean statements take
  `A.Nonempty`.)

The genuinely fixture-shaped material comes along with it: `coinModel`/`coinLatent`,
`twoCoinModel`/`twoCoinLatent`, `noisyModel`/`noisyLatent`, the §3.1 witnesses
(`coinCollapse`, `coinObj`, `twoCoinObj`, `coinCollapseArrow`, `pairCoinModel`,
`pairCoinHom₁`/`₂`) and `Example.geomModel`.  Those are regression fixtures, not a
dependency surface — build your own model rather than importing behaviour from them.  Two
of them are worth reading once, though, because they correct the over-claim a newcomer
makes: `coinLatent_reconScore` and `twoCoinLatent_reconScore` prove `ϱ_L = 0` on the easy
witnesses (a vanishing reconstruction score is what *perfect* reconstruction looks like),
while `noisyLatent_reconScore_pos` is the witness that `ϱ_L` is not identically zero.
`geomModel` is the model whose variable provably has infinite range — it is what shows the
retired `dd:finite-range` narrowing really was a narrowing.

## The substrate: `ShannonInformation.API`

Entropy, conditional entropy, mutual information and conditional mutual information are
**not** formalized here.  They come from one import, `ShannonInformation.API` — FAF's
shared, paper-neutral Shannon layer over a pinned vendoring of the PFR project — which
reaches you transitively through `Condensation.Model`.  So `H[X ; μ]`, `H[X | Y ; μ]`,
`I[X : Y ; μ]` and `I[X : Y | Z ; μ]` are available with no further import, and
`ShannonInformation/README.md` and `ShannonInformation/SCOPE.md` are required reading before
you rely on any entropy statement.

Three standing rules, all inherited:

1. **Never name a `PFR.*` module.**  Go through `ShannonInformation.API`; the vendor/consumer
   split exists so that re-pinning does not ripple into client code.
2. **Never `import Mathlib` wholesale** alongside this boundary.  PFR's `Mathlib/` shim
   modules re-declare lemmas the newer Mathlib pin has since acquired upstream, and the
   combination fails to elaborate (`import PFR.Mathlib.Probability.IdentDistrib failed,
   environment already contains 'ProbabilityTheory.IdentDistrib.prodMk'`).  Import the
   specific `Mathlib.*` modules you need.
3. **Cite `ShannonInformation.foo` in full, never bare** — the hazard most likely to cost
   you an hour.  Both versions of several entropy facts are reachable through the single
   import: the *vendored* ones hold only in the `FiniteRange` fragment, while the FAF-authored
   corpus in `ShannonInformation/FiniteEntropy/` proves the same facts at
   `ShannonInformation.FiniteEntropyOf`, which is the paper's own hypothesis (countable
   discrete range with finite entropy).  With `ProbabilityTheory` open, a bare lemma name
   resolves by *elaboration success* rather than by namespace, so a bare citation can
   silently pick the narrow version and fail several lines later with a missing `FiniteRange`
   instance.  `ShannonInformation/API.lean`'s module docstring carries the "which version to
   cite" table.  **Dot notation is the case no `open` can rescue**:
   `h.condEntropy_eq_entropy` and `hid.condEntropy_eq` resolve in the head symbol's namespace
   (`ProbabilityTheory.IndepFun`, `ProbabilityTheory.IdentDistrib`) and so always find the
   vendored original — write those two out in full and pass the hypothesis as an argument.

Where the finiteness sits in *this* library: in the **fields of `RVModel`** —
`finiteEntropy_Ω`, which is Definition 3.1's own "with finite entropy" clause on the sample
space, and `finiteEntropy_X` for the variables.  Every statement quantifying over a model or
a latent model therefore gets it from the structure and never as a separate hypothesis, and
a derived variable gets it in one step from `RVModel.finiteEntropyOf`.  The §2 substrate
lemmas are stated over *bare* variables and do carry the hypothesis explicitly; it is not
the case that every statement with entropy content carries it.

There is **no `FiniteRange` citation anywhere in `Condensation/`** except one, where it is
negated (`Example.geomModel_not_finiteRange`).  The obvious guess is wrong here: a witness
built on `Bool × Bool` still cannot cite the vendored lemmas, because with `RVModel`'s
finiteness field being `FiniteEntropyOf` there is no structure instance for
`FiniteRange (M.X i)`, and instance search will not unfold a concrete model to rediscover
that its range happens to be a `Fintype`.

One trap worth carrying while reading any statement here: Lean's `∑'` is `0` on a
non-summable family, so `H[X]` for an infinite-entropy variable is silently `0` rather than
`∞`, and `condEntropy` is a Bochner integral, silently `0` when non-integrable.  What keeps
these from biting is that the finiteness class carries both as *proved consequences*
(`ShannonInformation.FiniteEntropyOf.summable`, `ShannonInformation.integrable_entropy_cond`)
rather than as side hypotheses on statements.

## What is, and is not, the trust surface

This boundary and the trust surface overlap heavily but are not the same thing, and the
distinction is worth holding onto.

**The trust surface** answers "what do we publicly claim faithfully formalizes the paper?"
It is exactly the declarations carrying the repository's paper-node annotation — the
docstring line naming the printed node, which `scripts/check-condensation-nodes.py` reads,
and which is why this module docstring cannot spell that token out.
`scripts/check-condensation-nodes.py` enforces the annotation contract fail-closed,
including node *kind*, and `scripts/check_sorry_ledger.py` asks Lean from the compiled
environment which declarations depend on `sorryAx`.

**This consumer boundary** answers a different question — "what should downstream research
depend on as the supported mathematical interface?" — and it contains a good deal that is
*not* a paper claim: the whole chain-rule layer, the `famFinset`/`PPlus`/`contrib` plumbing,
the finite-entropy instances, the degenerate-case lemmas, the `AEFunctionOf` congruence
algebra, and the constructed witnesses.

`AxiomAudit.lean` carries **three** Condensation blocks, not two, and it is worth knowing
which is which before using them to tell a paper endpoint from a convenience:

1. **`CONDENSATION-INVENTORY`** — an `#assert_axioms_clean` block.  It is where the annotated
   endpoints are enumerated, but it is *not* a list of annotated endpoints only: it also
   carries the witnesses and conveniences that were first listed alongside them (for
   instance `coinModel`/`coinLatent`).  So membership here does not by itself mean
   "paper endpoint" — the paper-node annotation line does.  Roughly two thirds of the
   names in it are annotated; run `scripts/check-condensation-nodes.py` for the current
   split rather than quoting a number from prose.
2. **`CONDENSATION-PENDING`** — pure comment, compiling to nothing and asserting nothing.
   It is the staging mechanism for an annotated endpoint whose proof is unfinished, and both
   of its sections are **empty** at M2.  Its `-- SECTION: consumers (un-annotated)` marker
   line belongs to that staging machinery — it is where an un-annotated *consumer of a
   staged theorem* would be named — and is emphatically **not** where this boundary's
   conveniences live.  The block is retained rather than deleted because
   `scripts/check_sorry_ledger.py` cross-checks it against the compiled environment in both
   directions, so "empty" is a re-verified assertion rather than an absence.
3. **The `## Consumer API conveniences` block** — a marker-less `#assert_axioms_clean` near
   the end of the file.  *This* is where the consumer-surface plumbing and the constructed
   non-vacuity witnesses are inventoried, asserted axiom-clean without claiming they render
   anything the paper says.

Reading blocks 1 and 3 side by side is the fastest way to survey what is asserted clean;
reading the paper-node annotation lines is the only way to tell what is *claimed to be the
paper*.

One qualification, since the repo standard asks for "an intentionally *small*" API.  This
boundary imports all nine modules of the library, and there is no deeper construction import
held back behind it.  That is a fact about this library rather than a dodge: eight of the
nine files carry paper nodes, so no module could be excluded without dropping part of the
paper, and the ninth — `ChainRule.lean` — is machinery a quantitative client demonstrably
needs and cannot get from Mathlib or the vendored PFR snapshot.  The curation is therefore
in what is *documented as supported* rather than in a narrower import: the `AxiomAudit`
blocks catalogued above separate the paper's endpoints from the conveniences, and
`Examples.lean`'s fixture-shaped
witnesses are marked above as regression fixtures rather than a dependency surface.  If that
line ever needs to be enforced by the import graph rather than by documentation, the split
to make is the one drawn in the *Constructions and witnesses* section above.

Nothing on this boundary is a modeling substitution.  The narrowing `dd:finite-range` was
**retired** on 2026-08-17 and there is no type-`(c)` substitution left in the library.  The
two restrictions that do remain are disclosed in `Condensation/README.md`: the universe
stratification `dd:bundled-model`, and the Examples 5.1–5.3 scope ruling.

## Where to read next

* `Condensation/README.md` — the trust surface: status, the modeling boundary, the scope
  rulings, the numbering and provenance scheme, and the non-vacuity discipline.
* `Condensation/KNOWLEDGE.md` — institutional memory: design decisions, the correspondence
  table, and an extensive pitfalls log.  Read the pitfalls before writing a concrete model.
* `Condensation.lean` — the aggregator, whose docstring carries the full `dd:` glossary.
  It imports the same modules as this file; the difference is that this one is *documented
  as a boundary* and is what the registry records as the supported entrypoint.
* `Condensation/notes/paper-errata.md` — twenty-two entries (plus one investigated and
  refuted candidate, recorded so it is not re-raised), consulted before concluding that a
  Lean statement diverges from the printed one.
* `APITests/Condensation.lean` — client-style tests that import only this file.
-/
