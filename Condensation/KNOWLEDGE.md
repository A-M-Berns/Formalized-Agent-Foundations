# Condensation — knowledge base

Institutional memory for this formalization: settled design decisions, the
correspondence table, intentional deviations, paper errata, and pitfalls. Committed on
purpose — a future session (or auditor) reads this before touching the library. See
`README.md` for the trust surface, `notes/roadmap.md` for the plan and the `dd:` glossary
in full, and `Condensation.lean` for the glossary as shipped.

## Status as of 2026-08-18 (M2 complete)

Re-derived from the checkers on the date shown, not copied. **Re-run them before quoting
any of these numbers** — that is the discipline this file's last pitfall exists to enforce.

- `python3 scripts/check_sorry_ledger.py` → `OK — 0 sorry-dependent declarations, all
  ledgered (0 main, 0 consumers)`. There is **no `sorry` anywhere in `Condensation/`**, and
  `AxiomAudit.lean`'s `CONDENSATION-PENDING` block is empty in both of its sections. Every
  annotated endpoint is inventoried and axiom-clean.
- `python3 scripts/check-condensation-nodes.py` → `OK (79 citations, 39 distinct nodes,
  42 numbered in the paper, 112 inventoried endpoints)`; coverage 39/42 — §2 5/5, §3 12/12,
  §4 15/15, §5 7/10. The three uncited nodes are Examples 5.1, 5.2 and 5.3, which the
  proposed ruling puts out of scope (see intentional deviations).
- Note that some *module docstrings* have not caught up with this; where one contradicts
  the numbers above, the checkers win.

## Correspondence table

| Paper (§/symbol) | Lean name | Notes |
|---|---|---|
| Def 2.1 random variable `X : Ω → R` | Mathlib `Measurable` | rendered, not redefined |
| Def 2.1 pullback `π^* X` | `X ∘ π` | `dd:pullback` |
| Def 2.1 "`Y` is a function of `X` (a.e.)" | `Condensation.FunctionOf` / `Condensation.AEFunctionOf` | `dd:ae-function` |
| Def 2.2 `P⁺ S` | `Condensation.PPlus` | `dd:pplus` |
| Def 2.3 `H(X)`, `H(X\|Y)`, `I(X;Y\|Z)` | `H[X ; μ]`, `H[X \| Y ; μ]`, `I[X : Y \| Z ; μ]` (`ShannonInformation.API`) | vendored PFR |
| Def 2.3 `I(X;Y;Z)` | `Condensation.interactionInfo` | `dd:interaction` |
| Def 2.4 `G(Ω)` | `Condensation.GiryMeasurableSpace`, an `abbrev` for the Mathlib instance on `MeasureTheory.ProbabilityMeasure Ω` | rendered; the carrier is the space of *probability* measures, as Def 2.4 says — not `Measure Ω` (R1-F04) |
| Prop 2.5 determinism bridge | `Condensation.aeFunctionOf_of_condEntropy_eq_zero` (+ the converse `condEntropy_eq_zero_of_aeFunctionOf` and the packaged `aeFunctionOf_iff_condEntropy_eq_zero`) | since 2026-08-17 the hypotheses are the paper's own: `[ShannonInformation.FiniteEntropyOf X μ] [ShannonInformation.FiniteEntropyOf Y μ]` and `Countable R_Y`. The `omit [Countable T] in` is **gone** — forced, because both the `tsum` form of conditional entropy and `ShannonInformation.const_of_nonpos_entropy` need it. Before that the statement was stronger in one respect (`FiniteRange`) and weaker in another (no `Countable R_Y`), so it was not comparable as printed; it now is |
| Def 3.1 random variable model | `Condensation.RVModel (I : Type w) [Finite I]` | `dd:bundled-model`; `[Finite I]` is Def 3.1's "finite family", a class parameter of the structure (R1-F01 etc.). **Definition 3.1 verbatim since 2026-08-17**: the instance-implicit field `finiteEntropy_Ω : ShannonInformation.FiniteEntropyMeasure P` (sitting between `probP` and `R`) is the definition's own "with finite entropy" clause, which the library did not carry at all before; `finiteEntropy_X : ∀ i, ShannonInformation.FiniteEntropyOf (X i) P` replaced `finiteRange_X`. `dd:finite-range` is retired — see design decisions |
| machinery: finiteness of a derived variable | `Condensation.RVModel.finiteEntropyOf` | new 2026-08-17, no paper node. Every measurable `Z : M.Ω → S` has `ShannonInformation.FiniteEntropyOf Z M.P`, by `ShannonInformation.finiteEntropyMeasure_map M.P hZ`. This is what makes the `Ω`-clause pay for itself: a derived variable needs only *measurability*, never a finiteness argument of its own |
| machinery: joint variables are finite-entropy | `RVModel.finiteEntropy_joint`, `.finiteEntropy_jointOn`, `.finiteEntropy_jointAll`, `LatentModel.finiteEntropy_pullbackJoint` | renamed from `finiteRange_joint`/`_jointOn`/`_jointAll` on 2026-08-17 and reproved in one line each from `finiteEntropyOf`; `finiteEntropy_pullbackJoint` is new. All four are instances. They are **no longer built from `Condensation.finiteRange_pi`**, which is why that lemma ended up with no callers and was retired |
| Def 3.2 latent variable model | `Condensation.LatentModel` | |
| Def 3.3 σ_L, χ_L, ϱ_L | `LatentModel.simpleScore`, `.condScore`, `.reconScore` | |
| Def 3.4 `X_A`, `Y_F`, `Y_∩A`, `Y_⊇A`, `Y_⊋A`, `Y_∋i` | `RVModel.joint`, `LatentModel.jointOn`, `LatentModel.jointContrib`, `.jointAbove`, `.jointStrictAbove`, `.jointContribIdx` | the carriers are the **joint variables**; `RVModel.jointOn` is the machinery `LatentModel.jointOn` is built from and carries no node |
| Def 3.4 index families `{B : B ∩ A ≠ ∅}`, `{B : A ⊆ B}`, `{B : A ⊊ B}`, `{B : i ∈ B}` | `Condensation.contrib`, `.above`, `.strictAbove`, `.contribIdx` | *auxiliaries*: subsets of `P⁺I`, not random variables. They index the joint variables above; annotating them would claim (3.5)–(3.8) for a set rather than for the variable the equations define (R1-F26) |
| Def 3.5 morphism `(π, ι, (f_j))` | `Condensation.RVModel.Hom` | fields `π`, `π_pres`, `ι`, `f`, `eq_ae`; **no** measurability field for `f` — the paper's own remark is that it is automatic on countable discrete ranges (`Hom.measurable_f`). `ι : J → I` runs target → source. `dd:category` |
| Def 3.6 composite (3.13) | `RVModel.Hom.comp` | index maps compose the other way round |
| Prop 3.7 proof, identity morphism (3.16) | `RVModel.Hom.id` | **(3.16) is displayed inside the *proof* of Proposition 3.7, not in Definition 3.6** (paper L391–395); `Hom.id` is machinery for `RVModelObj.instCategory` and carries **no** `Paper node:` line of its own. An earlier docstring and an earlier version of this row attributed it to Def 3.6 — R2-F17/F18 |
| Prop 3.7 category | `Condensation.RVModelObj.instCategory` | objects are `RVModelObj`, which carries its index type as a **field** (a morphism may change it); (3.17)–(3.20) hold by `rfl` |
| Prop 3.8 iso characterization | `RVModel.Hom.isIso_iff` | uses `CategoryTheory.IsIso`; "isomorphism of measurable spaces" is `RVModel.Hom.IsMeasurableIso` |
| Def 3.9 a.e.-equal morphisms | `RVModel.Hom.AEEq` (+ `Hom.instSetoid`) | |
| Def 3.10 equivalence | `RVModel.IsEquivalence` (the pair), `RVModel.Equivalent` (the ∃) | the "laid out" characterization is `RVModel.Hom.ofSameIndex` + `RVModel.isEquivalence_ofSameIndex_iff`; Prop 4.7 consumes exactly that shape. Since 2026-08-17 `Hom.ofSameIndex` takes its two models as **explicit** arguments (`ofSameIndex M N π hπ f hf`): every occurrence of `M`/`N` in the other arguments is behind a projection (`M.Ω`, `M.P`, `M.R`, `M.X`), which unification cannot invert, so with them implicit every call site wrote `(M := …) (N := …)` anyway — R2-F10 |
| Prop 3.11 congruence | `RVModel.Hom.aeEq_equivalence`, `RVModel.Hom.comp_aeEq_congr` | |
| Prop 3.12 equivalence relation | `RVModelObj.equivalent_equivalence` | over `RVModelObj.Equivalent`; the universe-polymorphic `RVModel.Equivalent.refl/symm/trans` are the pieces |
| Ex 4.1 `L₁`, `L₂` | `Condensation.Example41.L₁`, `.L₂` (+ `L₁RV`, `L₂RV`) | guarded-subtype encoding of "let `Y_A` be constant"; (4.2)–(4.5) are `L₁_simpleScore`, `L₁_condScore`, `L₂_simpleScore`, `L₂_condScore` — annotated `theorem`s citing `Example 4.1` since 2026-08-17 (R2-F15). **All four PROVED at M2 (2026-08-18) and inventoried**; the pending block no longer names them. The proofs run on the two subsingleton-range lemmas `Condensation.entropy_eq_zero_of_subsingleton` / `.condEntropy_eq_zero_of_subsingleton` (`Probability.lean`). (4.4)/(4.5) take `A.Nonempty` (errata 11) and name `X_I` as `RVModel.jointAll` |
| Prop 4.2 (4.6) | `LatentModel.simpleScore_ge_condScore`, `.condScore_ge_entropy_jointContrib`, `.entropy_jointContrib_ge_entropy_joint` | three separate inequalities. **All three PROVED at M2 (2026-08-18)**; the middle one — the one that needed the finite-family chain rule — now runs on `Condensation.exists_revIncl_strictTotalOrder` and `RVModel.entropy_jointOn_eq_sum` from the new `Condensation/ChainRule.lean`, plus `RVModel.condEntropy_jointOn_mono` for (4.8). The supporting `LatentModel.aeFunctionOf_jointContrib_pullbackJoint` is the "by definition" step of the printed proof |
| Def 4.3 perfect / simply-perfect | `LatentModel.PerfectlyCondenses`, `.SimplyPerfectlyCondenses` | quantified over `Finset I`, not `PPlus I` — nothing degenerates at `A = ∅` |
| Lemma 4.5 | `LatentModel.perfect_entropy_iff_aeFunctionOf` | proved |
| Cor 4.6 | `LatentModel.aeFunctionOf_of_perfectlyCondenses` | proved and **axiom-clean since M2**: its own proof was always finished, but it consumed Prop 4.2, so until 2026-08-18 it was a `sorryAx` consumer |
| Ex 4.4 | `Condensation.Example44.M44`, `.L44` (+ (4.11) `.entropy_joint_eq` and the conclusion `.simplyPerfectlyCondenses`) | `X_i := Y_∋i`; this is why latent universes are unpinned. The last two are annotated `theorem`s citing `Example 4.4` since 2026-08-17 (R2-F15) and **PROVED at M2 (2026-08-18)**; (4.11) goes through `RVModel.entropy_jointOn_eq_sum_famFinset` (`ChainRule.lean`) |
| Prop 4.7 | `LatentModel.aeFunctionOf_iff_isEquivalence_contribModel` | the two models it compares are `LatentModel.pullbackModel` (`(Λ, (X_i))`) and `LatentModel.contribModel` (`(Λ, (Y_∩{i}))`); clause (2) is `RVModel.IsEquivalence` of two `Hom.ofSameIndex` triples at `π = ρ = id_Λ`. Proved |
| Def 4.8 ordered Markov | `Condensation.RVModel.OrderedMarkov` | stated over a bare `RVModel (PPlus I)`, as the paper does |
| Thm 4.9 | `LatentModel.perfect_tfae_A` (A1–A3), `.perfect_tfae_B` (B1 ⟺ B2) | **both PROVED at M2 (2026-08-18).** `perfect_tfae_A` is a `List.TFAE` closed by `tfae_have 1 → 3 := …`, `tfae_have 3 → 2 := …`, `tfae_have 2 → 1 := …`, `tfae_finish`; (A1)⟺(A3) is the `entropy_jointOn_eq_sum_of_iIndepFun` / `iIndepFun_of_entropy_jointOn_eq_sum` pair from `ChainRule.lean` (both directions were needed — PFR has only the forward one, and only over `Fin m`). `perfect_tfae_B`'s (B1 ⇒ B2) runs on `exists_revIncl_strictTotalOrder_incomparable_first` plus `condIndepFun_of_condEntropy_jointOn_eq` |
| Prop 4.10 | `RVModel.orderedMarkov_iff` | "upward closed" is Mathlib's `IsUpperSet`, not a synonym. **PROVED at M2 (2026-08-18)**, from `ChainRule.lean`'s `condEntropy_jointOn_eq_of_condIndepFun` / `condIndepFun_of_condEntropy_jointOn_eq` sandwich pair and `RVModel.condEntropy_jointOn_above`. Finiteness comes from Definition 3.1's `Ω`-clause via `RVModel.finiteEntropyOf`, so the statement carries no local hypothesis. (This row used to warn that the declaration's docstring still credited the retired `dd:finite-range`; that docstring was corrected in the M2 close-out and the warning was itself stale by 2026-08-18 — the docstring now names `finiteEntropy_Ω` / `RVModel.finiteEntropyOf` and records the retirement. Re-read the docstring before trusting a row like this one.) |
| Def 4.11 amalgamation of a cospan | `Condensation.Amalgamation` | `dd:amalgamation`; **unchanged** by the 2026-08-17 generalization — it builds no random variable model, so Definition 3.1's clauses never reach it |
| Def 4.12 amalgamation of two latent models | `Condensation.LatentAmalgamation` | `Λ₀` primary, `lat₁`/`lat₂` derived (`.Λ` definitionally `Λ₀`); `comm` is the **only** added field (errata 10) — the fields `ρ₁_π`/`ρ₂_π` (`Lₖ.π ∘ ρₖ =ᵐ π̃ₖ`) and the lemma `comm_ρ` derived from them were **deleted on 2026-08-17 (R2-F12/F20)**: Definition 4.12(3)'s morphisms are Definition 3.5 morphisms of the underlying *random variable* models, and the paper never defines a morphism of latent models, so nothing relates `Lₖ.π ∘ ρₖ` to `π̃ₖ`. Carries `[finiteEntropy_Λ₀ : ShannonInformation.FiniteEntropyMeasure P₀]` since 2026-08-17 — Definition 4.12(1) asks for a random variable model on `Λ₀`, and Definition 3.1 now really demands the `Ω`-clause — and its `finiteRange_Y₁`/`finiteRange_Y₂` fields are `finiteEntropy_Y₁`/`finiteEntropy_Y₂` |
| Lemma 4.13 | `Amalgamation.canonical`, `nonempty_amalgamation`, `LatentAmalgamation.canonical`, `nonempty_latentAmalgamation` | the (4.49)–(4.53) construction. **All four PROVED on 2026-08-17 (round-2 fix wave); they are in the inventory block, not staged.** The three supporting measure lemmas — (4.55)–(4.56) total mass (`isProbabilityMeasure_canonicalMeasure`), and both halves of (4.57) (`measurePreserving_fst`/`_snd`) — were the library's last un-annotated `sorry`s. **Beware a real off-by-one in the prose here: THREE is the count of `sorry` *sites*, but FOUR supporting lemmas were `sorryAx`-dependent** — `finiteEntropyMeasure_canonicalMeasure` had a complete proof that *consumed* the other three, so it carried no `sorry` of its own and still failed an axiom check. Both numbers are correct about different things; say which you mean. For non-vacuity of `LatentAmalgamation` prefer `Condensation.LatentAmalgamation.diagonal` (R2-F19) — a latent model amalgamated with itself along the identity — which is independent of Lemma 4.13 entirely. (Until 2026-08-17 that preference was a *requirement*: these four were `sorry`-dependent, so citing them proved nothing, which is what R2-F19 found.) `Amalgamation.finiteEntropyMeasure_canonicalMeasure` (new 2026-08-17, proved) is what discharges `finiteEntropy_Λ₀` in `LatentAmalgamation.canonical`: the fibre product of (4.49) injects into `Λ₁ × Λ₂`, so `ShannonInformation.finiteEntropyMeasure_of_injective` applied to the pair `⟨fst, snd⟩` inherits finite entropy. Under `dd:finite-range` this obligation did not arise at all. **The proof factors through six `private` declarations** in `Amalgamation.lean`: `offWeight` (the (4.53) weight extended by zero to all of `Λ₁ × Λ₂`, so the sums become iterated sums over `Λ₁` and `Λ₂` rather than sums over a subtype), `offWeight_of_eq`/`_of_ne`, `tsum_offWeight_right`/`_left` (equation (4.54) — the only real mathematical content; the paper's `0/0 = 0` case is where `PΩ {π₁ a} = 0`, closed by `P₁ {a} ≤ P₁ (π₁ ⁻¹' {π₁ a}) = 0`), `tsum_carrier` (the subtype-to-product reindexing, `tsum_subtype` then `ENNReal.tsum_prod`), and `canonicalMeasure_preimage_fst`/`_snd`. **A new fact about `canonicalMeasure` should be phrased as a `g`-instance of `tsum_carrier`, not reproved from `Measure.sum_apply`.** Note the route is *not* `HasSum.isProbabilityMeasure_sum_dirac_ennreal`; the Dirac lemmas do the plumbing at the ends only |
| Lemma 4.14 | `Condensation.aeFunctionOf_of_condIndepFun` | **PROVED at M2 (2026-08-18), with a corrected binder: the lemma is FALSE as printed** — see errata 15 and the design-decisions entry below. Binders as they now stand: countable discrete `Ω` with `[IsProbabilityMeasure μ]`; `[Countable] [MeasurableSingletonClass]` on **`C`'s range** (`U`) — that is what makes the witnessing function measurable, the last line of the printed proof; `[MeasurableSingletonClass S]` on **`X`'s range** — the M2 repair, without which the statement is refutable; `T₁`, `T₂` carry only `MeasurableSpace`. There is still **no** finiteness binder of any kind: the printed proof is measure-theoretic and forms no entropy, so a `FiniteRange` or `FiniteEntropyOf` binder here is a finding (Phase 4b swapped four `FiniteRange` binders for four `FiniteEntropyOf` ones; round 2 R2-F01/F23 established that neither belonged — and then went one range too far). The `Ω`-side singleton instance is the *named* binder `[_hΩsing : MeasurableSingletonClass Ω]`, so a caller working on `Am.lat₂.Λ` can pass it explicitly (`(_hΩsing := Am.singΛ₀)`); Theorem 4.15 does exactly that |
| Thm 4.15 | `Condensation.aeFunctionOf_jointAbove_of_perfectlyCondenses` | **PROVED at M2 (2026-08-18).** Conjunction of two directions, the second got from the first by `Am.symm` (`LatentAmalgamation.symm`, in `Amalgamation.lean`); the shared direction is the `private` `aeFunctionOf_jointAbove_aux`, which carries the induction the paper omits (errata 5). Its ingredients: `LatentAmalgamation.perfectlyCondenses_lat₁/₂` to move the hypothesis onto `L̃ₖ`, `AEFunctionOf.congr_left` to read a dependence witnessed through `π̃₁` as one through `π̃₂` (field `Am.comm`), Prop 4.10 via Thm 4.9 (B1 ⇒ B2) for the conditional-independence side condition, Lemma 4.14 at each induction step, `isUpperSet_iInter_contribIdx` as the invariant, and `iInter_contribIdx_eq_above` (4.62) to close |
| Lemma 5.4 (5.5), (5.6) | `Condensation.condEntropy_le_of_pair`, `.condEntropy_eq_of_pair` | proved; the `condInteractionInfo` symmetries `condInteractionInfo_comm/_swap/_rotate` and `condEntropy_pair_rotate` are the machinery |
| Def 5.5 polar `F°` | `Condensation.polar` | with `mem_polar_iff`, `isUpperSet_polar`, `polar_antitone`, `polar_singleton`, `polar_eq_iInter` |
| Def 5.6 intersection tree | `Condensation.ITree`, `.label`, `.intersections`, `.LabelsIn` | `dd:tree`; `ITree.leaves`, `.subtrees`, `.label_eq_polar` are the machinery |
| Prop 5.7 | `ITree.label_eq_leaves_foldr`, `Condensation.eq_decorate_of_isIntersectionTree`, `.existsUnique_intersectionTree` | over `LTree` (an arbitrary labelling of every position) and `ITree.decorate`; proved. **`existsUnique_intersectionTree` is the `M`-version since 2026-08-17 (R2-F08/F11)**: the paper's `ℓ̃` maps the leaves *into* an intersection-closed collection `M` and the unique extension is `ℓ : V → M`, so the statement now takes `{M : Set α}`, `hM : ∀ a ∈ M, ∀ b ∈ M, a ⊓ b ∈ M` and `ht : t.LabelsIn M`, and concludes `∃! d, d.erase = t ∧ d.IsIntersectionTree ∧ d.LabelsIn M`. Three explicit arguments where there was one — a call site written against the old arity breaks. The old `M`-free statement survives, un-annotated, as `existsUnique_intersectionTree_ambient`. New machinery: `LTree.LabelsIn` (+ `labelsIn_leaf`/`labelsIn_node`) and `ITree.labelsIn_decorate` |
| Thm 5.8 (5.13), (5.14) | `Condensation.condEntropy_jointAbove_le`, `.condEntropy_jointAbove_eq` | stated over `LatentAmalgamation L₁ L₂`: `Y_⊇A` = `Am.lat₁.jointAbove`, `Z_G` = `Am.lat₂.jointOn`, `X_B` = `Am.lat₁.pullbackJoint`; the two contribution conditions are *fields*, not hypotheses. **Both PROVED at M2 (2026-08-18)**; the proof factors through the `private` chain `condEntropy_jointOn_pair_of_subset`, `condEntropy_jointOn_triple`, `condEntropy_eq_tree`/`condEntropy_eq_tree'`, `sum_leaves_eq`, `condInteractionInfo_jointOn_le` and `condEntropy_jointContrib_le_pullbackJoint`, with `ITree.label_eq_polar` putting `Z_G` on the left |
| Cor 5.9 (5.21), (5.22) | `Condensation.condEntropy_jointAbove_le_reconScore`, `.condEntropy_jointAbove_le_reconScore_of_orderedMarkov` | **both PROVED at M2 (2026-08-18)**, and both inventoried. (5.22) consumes Proposition 4.10, whose proof landed in the same milestone, so it was the last §5 endpoint to become axiom-clean |
| Cor 5.10 (5.24), (5.25) | `Condensation.polar_kSubsets`, `.condEntropy_jointAbove_le_choose` | **both proved** (5.25 at M2, 2026-08-18). `kSubsets` is `F`. **The `1 ≤ k` binder is asymmetric on purpose (R2-F21)**: `polar_kSubsets` (5.24) keeps it — the identity is genuinely false at `k = 0`, where the LHS is `polar ∅ = P⁺I` and the RHS is the upward cone `above A.toFinset` (truncated `ℕ` subtraction makes `k - 1 = 0`) — while `condEntropy_jointAbove_le_choose` (5.25) has **no** `hk`, because its tree hypothesis is unsatisfiable at `k = 0` and the statement is vacuous there. See errata 8 and the new errata 14 |
| auxiliary: `{B : B incomparable to A}` | `Condensation.incomparable` | in `Model.lean` beside `contrib`/`above`; no paper node, like them. Defined **via Mathlib's `IncompRel (· ≤ ·)`** since 2026-08-17 (`Mathlib.Order.Comparable`, imported by `Model.lean`): `IncompRel r a b` unfolds to `¬ r a b ∧ ¬ r b a`, so `mem_incomparable` stays `Iff.rfl`. Same policy as "upward closed" = `IsUpperSet`: no local synonym (R2-F27) |
| auxiliary: "upward closed" | Mathlib `IsUpperSet` on `PPlus I` | **not** a FAF definition — an earlier local `IsUpwardClosed` in `Perfect.lean` was a synonym and is retired |
| auxiliary: `FiniteRange` of a dependent product | ~~`Condensation.finiteRange_pi`~~ | **retired 2026-08-17**, and removed from `AxiomAudit.lean`'s inventory. It supplied `FiniteRange` for a dependent product of finitely many finite-range variables, which the vendored `FiniteRange/Defs.lean` still lacks. After the swap it had *zero* callers — `Example41.L₁RV`/`L₂RV` were the last two and now go through `M.finiteEntropyOf (measurable_pi_lambda _ fun j => M.measurable_X j.1)` — and an unused inventoried declaration is what this library's own rule says not to keep. `Model.lean` carries a paragraph where it stood; reinstating it is six lines of `Set.Finite.pi` |
| witness: a model the old class could not contain | in `namespace Condensation.Example` (singular): `geomModel`, `geomModel_X`, `geomModel_P`, `geomModel_not_finiteRange`, `geomModel_entropy`, `geomModel_entropy_pos`, `geomLatent`, `geomLatent_reconScore` | no paper node; all proved, none `sorry`. `geomModel : RVModel Unit` has `Ω = ℕ`, `P = ShannonInformation.geom` (the `Geometric(1/2)` law), `X () = id`, entropy `2 log 2`, together with a proof that `id` does **not** have finite range; `geomLatent = LatentModel.ofJoint geomModel` and its reconstruction score is `0`. They sit after `LatentModel.ofJoint` in `Examples.lean` rather than beside the fair-coin witnesses, precisely because `geomLatent` *is* `ofJoint geomModel` and there is nothing model-specific to say about the latent side. It is the evidence that retiring `dd:finite-range` has content rather than being a bookkeeping change — every other witness lives on a finite sample space and cannot tell the two readings apart. The law, its instances and the entropy computation live in `ShannonInformation/FiniteEntropy/Examples.lean` and are not restated; `geomLatent` is just `LatentModel.ofJoint geomModel` |

| witness: Def 4.3 / Def 4.8 **with content**, at `I = Bool` | `Condensation.twoCoinF`, `.twoCoinF_ne_twoCoinTF`, `.twoCoin_famFinset_contrib_F`, `.twoCoin_famFinset_contrib_TF`, `.twoCoinLatent_condEntropy_F`, `.twoCoinLatent_condScore_F`, `.twoCoinLatent_condScore_TF`, `.twoCoinLatent_perfectlyCondenses`, `.twoCoinLatent_not_simplyPerfectlyCondenses`, `.twoCoin_incomparable_T`, `.twoCoinLatent_orderedMarkov` | no paper node; all in `Examples.lean`'s new `section Definition43Bool`, added 2026-08-18 (R4-F23). All three latents are one fair coin, so `χ_L = log 2` at each of the three nonempty `A ∈ Finset Bool` while `σ_L({true}) = 2 log 2` — hence `PerfectlyCondenses` **and** `¬ SimplyPerfectlyCondenses` on the *same* witness, which is the proof that `LatentModel.PerfectlyCondenses.of_simply` has no converse. `twoCoinLatent_orderedMarkov` goes through `perfect_tfae_B` (B1 ⇒ B2) like the `Unit` one, but here the condition has content: `twoCoin_incomparable_T` computes `incomparable twoCoinT = {twoCoinF}`, nonempty. `H(X_A)` at a non-singleton `A` comes from `ProbabilityTheory.entropy_comp_of_injective`, not from `RVModel.entropy_joint_singleton`, which only reaches singletons |
| the degeneracy of the `Unit` witnesses, proved | `Condensation.condScore_eq_simpleScore_of_subsingleton_index`, `.incomparable_eq_empty_of_subsingleton_index` | no paper node; `Examples.lean`, 2026-08-18 (R4-F23). Over a subsingleton `P⁺I`: `χ_L = σ_L` for **every** latent variable model (the only `B` has nothing strictly above it, so (3.2)'s conditioning is on a variable into a one-point type), and Definition 4.8's family of incomparable indices is **empty**. These are what make "the `coinLatent_*` witnesses show satisfiability only" a proved claim rather than an assertion. **There is deliberately no `orderedMarkov_of_subsingleton_index`** — see the pitfall on `condMutualInfo_const` for why it is not cheap |

### M2 machinery (2026-08-18) — no paper nodes

Everything in this block landed with the four parallel M2 proof shards. None of it is a
numbered node, so none is annotated; all of it is ordinary `lemma`/`def` and is covered by
the ordinary axiom gate. The **homes below are the post-consolidation ones** — the four
shards each parked their generic helpers in a "TO BE MOVED" section of the file they owned,
and those sections were deleted when the wave was integrated. Do not look for a helper in
the file whose proof first needed it.

| Machinery | Lean name | Notes |
|---|---|---|
| the finite-family chain rule (whole new file) | `Condensation/ChainRule.lean` | imports only `Condensation.Model`; stated over a bare `RVModel J` with `[Finite J]`, not over a latent model, because that is the generality §4 uses. It is the single piece of infrastructure the KNOWLEDGE pitfall predicted would unblock four §4 endpoints (Prop 4.2's second inequality, Prop 4.10, both halves of Thm 4.9), and it did |
| Szpilrajn, strict form | `Condensation.exists_strictTotalOrder_ext` | Mathlib's `extend_partialOrder` yields a *reflexive* linear order; the chain-rule induction needs an irreflexive one, so this rebuilds `r a b := s a b ∧ a ≠ b` and re-registers the four `Std`/`Is*` classes by hand |
| the order of (4.7) | `Condensation.exists_revIncl_strictTotalOrder` | strict linear order on `P⁺I` with supersets first (`C < B → r B C`), by extending reverse inclusion |
| the order before (4.29) | `Condensation.exists_revIncl_strictTotalOrder_incomparable_first` | same, and additionally `∀ B ∈ incomparable A, r B A`; built by extending the paper's own partial order `B ⊇ C ∨ (B incomparable to A ∧ A ⊇ C)` |
| (4.35)/(4.39)'s converse containment | `Condensation.pred_subset_incomparable_union_strictAbove` | everything `r`-below `B` is incomparable to `B` or a strict superset of it |
| pair of joint variables as one | `RVModel.condEntropy_pair_jointOn` | `H[X \| ⟨Y_S, Y_T⟩] = H[X \| Y_{S ∪ T}]`; used constantly |
| (4.8) | `RVModel.condEntropy_jointOn_mono` | `S ⊆ T → H[X \| Y_T] ≤ H[X \| Y_S]` |
| drop already-given coordinates | `RVModel.condEntropy_jointOn_sdiff`, `.condEntropy_jointOn_above` | `H[Y_G \| Y_W] = H[Y_{G∖W} \| Y_W]`; and `H[Y_⊇A \| Y_W] = H[X_A \| Y_W]` when `⊋A ⊆ W` |
| the chain rule itself | `RVModel.condEntropy_jointOn_eq_sum`, `.entropy_jointOn_eq_sum` | conditioned (4.38) and unconditioned (4.9)/(4.29)/(4.34) forms, by induction peeling the `r`-greatest element off a `Finset`; the private helpers are `exists_greatest`, `pred_eq_erase`, `pred_erase` |
| subadditivity for a finite family | `RVModel.entropy_jointOn_le_sum` | `H(Y_s) ≤ ∑_{B ∈ s} H(Y_B)`, the **third** inequality of (4.25) — full subadditivity down to singletons, applied to each of `F`, `G`, `H` and summed. (4.25) is a chain of three: `H(Y_∩I) ≤ H(Y_{F∪G}) + H(Y_H) ≤ H(Y_F) + H(Y_G) + H(Y_H) ≤ ∑_{B∈P⁺I} H(Y_B) = H(Y_∩I)`; the first two links are the two-variable `ShannonInformation.entropy_pair_le_add`. This row said "first" until 2026-08-18 and seeded the same error in the declaration's docstring |
| independence ⇒ additivity | `RVModel.entropy_jointOn_eq_sum_of_iIndepFun` | the heterogeneous, arbitrary-finite-index analogue of PFR's `iIndepFun.entropy_eq_add`, which is `Fin m`-only |
| additivity ⇒ independence | `RVModel.iIndepFun_of_entropy_jointOn_eq_sum` | (4.23)–(4.26), the direction PFR and Mathlib do **not** have. Hypothesis is `{t : Finset J} (ht : ∀ j, j ∈ t)` rather than `Finset.univ`, so no `Fintype J` has to be produced to name it; supporting steps are `.entropy_jointOn_eq_sum_of_subset` (4.25) and `.indepFun_X_jointOn_of_entropy_eq` (4.26), plus the private `entropy_jointOn_empty`/`_insert`/`_split` |
| Def 4.8 as a termwise entropy equality | `RVModel.condEntropy_jointOn_eq_of_condIndepFun`, `.condIndepFun_of_condEntropy_jointOn_eq` | (4.30)/(4.32), (4.35), (4.40), both stated in the "sandwich" shape `S₂ ⊆ W ⊆ S₁ ∪ S₂` the proofs need |
| entropy additivity over a **Set**-indexed family | `RVModel.entropy_jointOn_eq_sum_famFinset` (in `Condensation/ChainRule.lean`) | `H[Y_F] = ∑ B ∈ famFinset F, H[Y_B]` for `F : Set (PPlus I)`. `Examples.lean` grew three `private` helpers for this in parallel — `entropy_pi_finset_eq_sum_of_iIndepFun`, `entropy_jointOn_eq_sum_toFinset`, `entropy_jointOn_eq_sum_of_iIndepFun` — which were **deduplicated away** at M2 integration against ChainRule's `Finset`-indexed `RVModel.entropy_jointOn_eq_sum_of_iIndepFun`; this is the thin `famFinset` restatement of that. The `Finset` indexing is not incidental: the induction runs on a `Finset`, while `Condensation.famFinset` is not generic in the index type (it is declared inside `LatentModel`'s score section and takes a `Set (PPlus I)`), so both spellings have to exist |
| a.e.-functional dependence, congruence | `Condensation.AEFunctionOf.congr_left`, `.congr_right` | in `Condensation/Probability.lean`, beside the rest of the `AEFunctionOf` API. `congr_left : AEFunctionOf X Y μ → X =ᵐ[μ] X' → AEFunctionOf X' Y μ` replaces the **independent** variable (the one everything is a function *of*); `congr_right : AEFunctionOf X Y μ → Y' =ᵐ[μ] Y → AEFunctionOf X Y' μ` replaces the **dependent** one. Recall `AEFunctionOf X Y μ` means "`Y` is a function of `X`", so left/right are the *argument* positions, not the roles. These are how the field `LatentAmalgamation.comm` is consumed — `π̃₁` vs `π̃₂`. `congr_right` is exactly the three-line lemma this file predicted M2 would need |
| pairing a dependence | `Condensation.AEFunctionOf.prodMk_left` | in `Probability.lean`: `AEFunctionOf W V μ → AEFunctionOf ⟨X, W⟩ ⟨X, V⟩ μ` |
| conditional-entropy comparisons under a.e. dependence | `Condensation.condEntropy_congr_of_aeFunctionOf`, `.condEntropy_le_condEntropy_of_aeFunctionOf`, `.condEntropy_le_of_aeFunctionOf` | in `Probability.lean`. Respectively: conditioning on either of two mutually a.e.-functional variables is the same; conditioning on more can only help; and data processing for the *conditioned* variable (`H(V\|W) ≤ H(X\|W)` when `V` is a.e. a function of `X`) — (5.23)'s only client. All three open with `rcases eq_zero_or_isProbabilityMeasure μ with rfl \| hμ` because they cite `finiteEntropyOf_pair` |
| variables with subsingleton *range* | `Condensation.entropy_eq_zero_of_subsingleton`, `.condEntropy_eq_zero_of_subsingleton` | in `Probability.lean`, the companions of `condEntropy_eq_entropy_of_subsingleton` (which is about the *conditioning* variable). They are what makes Example 4.1's guarded-subtype encoding pay off; they were `private` in `Examples.lean` and became public on the move |
| upward cones are antitone | `Condensation.above_mono` | in `Condensation/Model.lean`: `B ⊆ A → above A ⊆ above B` |
| joint over a union | `Condensation.RVModel.functionOf_jointOn_union` | in `Model.lean`, the companion of `RVModel.functionOf_jointOn_mono`: `Y_{F ∪ G}` is (everywhere) a function of `⟨Y_F, Y_G⟩`. What turns Lemma 5.4's `H(X \| Y₁, Y₂, C)` into Theorem 5.8's `H(Y_⊇A \| Z_{L(v) ∪ R(v)})` |
| (4.62) and its invariant | `Condensation.iInter_contribIdx_eq_above` (in `Comparison.lean`), `Condensation.isUpperSet_iInter_contribIdx` (in `Model.lean`) | `⋂_{i ∈ A} {B : i ∈ B} = {B : A ⊆ B}` — the paper's undefined `F_i` is `contribIdx i` (errata 5) — and the upper-set invariant Theorem 4.15's induction carries so that Proposition 4.10 applies at every step |
| amalgamation symmetry | `Condensation.LatentAmalgamation.symm` | in `Condensation/Amalgamation.lean`. `LatentAmalgamation L₁ L₂ → LatentAmalgamation L₂ L₁`, swapping the two sides field by field; `comm` transports as `Am.comm.mono fun _ hl => hl.symm`. This is the paper's "using the symmetry of the situation to interchange `Y` and `Z`", and it is what makes Theorem 4.15's second conjunct free |
| scores transfer along `ρₖ` | `Condensation.LatentAmalgamation.condScore_lat₁`, `.condScore_lat₂` | in `Amalgamation.lean`: `χ_{L̃ₖ} = χ_{Lₖ}`. Sound because Definition 3.3's `χ` mentions only the latent family and never `π` — which matters, since round 2 deleted the `ρₖ_π` fields (R2-F12/F20) and nothing relates `Lₖ.π ∘ ρₖ` to `π̃ₖ`. The private workhorse is `condEntropy_strictAbove_transfer`, stated over a **bare family** rather than over `Am.lat₁` on purpose (see pitfalls) |
| perfection transfers along `ρₖ` | `Condensation.LatentAmalgamation.perfectlyCondenses_lat₁`, `.perfectlyCondenses_lat₂` | these stay in `Condensation/Comparison.lean`, not in `Amalgamation.lean`, because `PerfectlyCondenses` is defined in `Perfect.lean` and `Amalgamation.lean` does not import it. If you go looking for them beside `symm` and `condScore_lat₁`, this is why they are not there |
| `Λ₀`-pinned finiteness for an amalgamation | `Condensation.LatentAmalgamation.finiteEntropyOf'` | in `Amalgamation.lean`. `RVModel.finiteEntropyOf` with the sample space spelled `Λ₀` rather than `lat₁.Λ`/`lat₂.Λ`. The spelling is load-bearing, not cosmetic — see the Ω-three-spellings pitfall |

(Extend as declarations land. Every formalized node gets a row.)

## Design decisions

See the `dd:` table in `notes/roadmap.md` — `dd:pplus`, `dd:bundled-model`,
`dd:ae-function`, `dd:pullback`, `dd:interaction`, `dd:tree`, `dd:category`,
`dd:amalgamation`. Rationale lives there; this file records *changes* to them and the
finding IDs that forced any. `dd:finite-range` is no longer among them — see immediately
below.

- **`dd:finite-range` is RETIRED (2026-08-17). The model class is now Definition 3.1
  verbatim.** History, because the name still appears in older commits, in the audit ledger
  and in the plan note. The decision was: every variable of a model carries `FiniteRange`,
  and `Ω` carries no entropy hypothesis at all — a type-(c) narrowing, forced because the
  vendored PFR theorems are proved only in the finite-range fragment. It was costed on
  2026-08-17 (~1,450–2,400 lines / 3–4.5 focused weeks in four phases; the abstract core —
  grouping bound, local chain rule, countable Gibbs — proved in ~90 lines against the
  pinned Mathlib as calibration; nothing in the paper false or different under finite
  range, only the model class smaller; no upstream help available, PFR master's entropy
  files being byte-identical to the pin and Mathlib having no Shannon entropy at all), and
  Anson ruled the same day that the generalization was a *desired endpoint* to be pursued
  in parallel rather than deferred. It landed the same day: `ShannonInformation/FiniteEntropy/`
  (Phases 1–4a) reached the corpus §2–§5 actually needs, and Phase 4b — the consumer
  migration — swapped the model class over. Full plan with acceptance criteria and a
  post-hoc calibration note: `notes/finite-range-generalization-plan.md`.

  **The "exactly one field of `RVModel`" promise the old entry made was kept and cashed.**
  What the swap actually cost on the Condensation side was: one field replaced
  (`finiteRange_X` → `finiteEntropy_X`), one field *added* (`finiteEntropy_Ω`, which is
  Definition 3.1's own "with finite entropy" clause and which the library had never carried),
  three joint instances renamed and reproved in one line each from the new
  `RVModel.finiteEntropyOf`, seven `Probability.lean` signatures changed, the §5 Lemma 5.4
  block and Lemma 4.14 rebound, `LatentAmalgamation` given `finiteEntropy_Λ₀` plus the new
  `Amalgamation.finiteEntropyMeasure_canonicalMeasure` to discharge it — and *no statement of
  any §3–§5 theorem changed*. The `sorry` count was unchanged at 20 by that migration (it
  reached **zero** with the M2 proof wave on 2026-08-18 — do not read "20" as current).
  Every §4/§5 theorem still
  gets its finiteness from the structure and never as a hypothesis, exactly as the hedge
  intended. The substrate, not the paper library, was where the work was.

  Two smaller consequences worth carrying: the `Probability.lean` §2 substrate lemmas are
  over *bare variables*, so they still carry a finiteness binder explicitly — it is now
  `[ShannonInformation.FiniteEntropyOf _ μ]` and there are **seven** of them, not eight
  (`entropy_pair_of_aeFunctionOf` lost the hypothesis entirely, since
  `ProbabilityTheory.entropy_prod_comp` never needed one). And a `FiniteEntropyOf` binder on
  a §2 substrate lemma is not a finding. `FiniteRange` now appears in `Condensation/` in
  exactly one statement — `Example.geomModel_not_finiteRange`, where it is *negated* — and a
  `FiniteRange` binder or citation anywhere else is a finding.
- **`finiteEntropy_X` is deliberately redundant, and must not be "cleaned up".**
  `finiteEntropy_Ω` already implies it: every `Xᵢ` is a measurable function of `Ω`, so
  `RVModel.finiteEntropyOf` derives `FiniteEntropyOf (X i) P` in one step. The field is kept
  anyway because it is the hypothesis every §2 substrate lemma literally consumes, and as a
  field (registered by `attribute [instance]`) it sits one instance step from the goal
  rather than behind a lemma with a measurability side condition. This is redundancy, not
  strengthening: the model class is exactly Definition 3.1's either way, since the derivation
  runs from `finiteEntropy_Ω` and never the other direction. Deleting the field would compile
  — after inserting a `haveI := M.finiteEntropyOf (M.measurable_X i)` at a long tail of proof
  sites — and would buy nothing. Do not do it without reading this bullet first.
- **`dd:category` as landed (M1).** The object type is `RVModelObj`, carrying its index
  type `I : Type w` as a **field** with `[finI : Finite I]` as an instance field — a
  parameter is impossible, because Definition 3.5 lets a morphism change the index set and
  a `Category` instance needs one object type. `RVModel.Hom` carries exactly
  `π`, `π_pres`, `ι`, `f`, `eq_ae`, and deliberately **no** measurability field for `f`:
  Definition 3.5's own remark is that `f_j` is automatically measurable on countable
  discrete ranges, so a field would be a (harmless but unfaithful) strengthening of the
  data. `Hom.measurable_f` supplies it as a lemma. The category laws (3.17)–(3.20) hold by
  `rfl` — they are the component-wise laws, and the two remaining `Hom` fields are
  `Prop`-valued. Consequence for whoever extends this: do not add a measurability field to
  `Hom` "for convenience"; it would break `Hom.ext` and the `rfl` laws and diverge from the
  paper.
- **`dd:amalgamation` as landed (M1).** `LatentAmalgamation` makes **`Λ₀` primary** and
  derives the two latent variable models Definition 4.12 names (`lat₁`, `lat₂`, built from
  `rv₁`, `rv₂`). The alternative — two `LatentModel M` fields plus a proof that their
  carriers agree — was rejected because the agreement would be a *type* equality and every
  use of it would travel through `Eq.mpr`/`HEq`. As built, `Am.lat₁.Λ = Am.Λ₀` is `rfl`,
  which is what makes Theorem 4.15 statable (it compares `Y_A` with `Z_⊇A` on one space).
  The latent families `Yₖ` are valued in `Lₖ`'s ranges because clause (3)'s morphisms act
  as the identity on ranges, which forces the range families to agree; what survives of
  Definition 3.5 is then just `ρₖ_pres` and `ρₖ_Y`. **That sentence is now literally true of
  the structure, and was not before.** Until 2026-08-17 the structure also carried
  `ρ₁_π`/`ρ₂_π` (`Lₖ.π ∘ ρₖ =ᵐ π̃ₖ`), and a derived lemma `comm_ρ`. They were an
  over-reading of clause (3) and were deleted (R2-F12/F20): the morphisms `ρₖ` of
  (4.44)/(4.45) are morphisms in the sense of **Definition 3.5**, i.e. of the underlying
  *random variable* models, and Definition 3.5 imposes exactly "π is probability
  preserving" and "`fⱼ(X_{ι(j)}) = π^* Yⱼ` a.e."; the paper never defines a morphism of
  *latent* variable models and so never asks for compatibility with the maps to `Ω`. If you
  find yourself wanting `Lₖ.π ∘ ρₖ =ᵐ π̃ₖ` in a proof, that is a finding, not a missing
  field — say so rather than reintroducing it. **`comm` is the one added field** —
  Definition 4.12 does not tie `π̃₁` to `π̃₂` and Theorem 4.15 needs them to agree a.e.
  (errata 10).
- **Non-vacuity of `LatentAmalgamation` is witnessed by `diagonal`, independently of
  Lemma 4.13.** `Condensation.LatentAmalgamation.diagonal (L : LatentModel M) :
  LatentAmalgamation L L` amalgamates a latent variable model with itself at `Λ₀ = L.Λ`,
  `ρₖ = id`; Definition 4.12's clauses then hold on the nose and `comm` is `rfl`. This
  matters because *every* §5 statement, and Theorem 4.15, quantifies over a
  `LatentAmalgamation`, so an uninhabited one would make the whole tranche vacuous — and
  until 2026-08-17 the only inhabitant was `LatentAmalgamation.canonical`, which was
  `sorry`-dependent, so nothing axiom-clean witnessed the hypothesis (R2-F19). Lemma 4.13
  has since been proved too, so both routes exist; `diagonal` is the one that stays valid
  if Lemma 4.13's proof is ever disturbed, and it is a two-line construction rather than a
  measure-theoretic one. Keep it, and keep citing it in non-vacuity prose.
- **`dd:tree` as landed (M1).** `ITree` is an inductive binary tree with labels *computed*
  (`ITree.label`, the meet of the children's labels); `LTree` is the separate type of trees
  with a label at *every* position, which is what Proposition 5.7 quantifies over
  (`eq_decorate_of_isIntersectionTree`, `existsUnique_intersectionTree`, with
  `ITree.decorate` the computed decoration). **`ITree` being inductive, it ranges over
  exactly the FINITE trees, and since 2026-08-18 (R4-F02) that is written down as a
  *disclosed reading* rather than as "nothing is lost".** Definition 5.6 as printed carries
  no finiteness or well-foundedness clause — its condition (1) says only that every vertex
  has a unique directed path *to* the root, which an upward-infinite tree with no leaves at
  all satisfies (errata 17). The reading is licensed by Theorem 5.8, whose (5.14) is a
  finite sum over the tree's leaves and internal vertices and is meaningless otherwise. The
  disclosure is written in `Quantitative.lean` twice (the module docstring and the `ITree`
  docstring), in `Condensation.lean`'s glossary and in `README.md`'s `dd:tree` row; if you
  reword one, reword all four. Definition 5.6's family of intersections
  (5.11) is a `List`, not a `Finset` — the paper explicitly warns that the same
  intersection may occur more than once — and Theorem 5.8's "bijection between the leaves
  of `T` and `{C : B∩C≠∅}` ranging over `B ∈ F`" is a **multiset equation**
  (`(T.leaves : Multiset _) = (famFinset F).val.map (contrib ·.toFinset)`), which is a
  bijection rather than a mere surjection because `contrib_injective` makes the right-hand
  multiset duplicate-free. Note the paper's direction convention: its "parents" of a vertex
  are the inductive presentation's *children* (errata 13).
- **Upward closure is Mathlib's `IsUpperSet`, and there is no FAF synonym.** `Perfect.lean`
  briefly defined `IsUpwardClosed F := ∀ B C, B ∈ F → B ≤ C → C ∈ F` while
  `Quantitative.lean` used `IsUpperSet`; they are the same predicate up to argument order,
  and the local one is retired. `Model.lean` imports `Mathlib.Order.UpperLower.Basic` for
  it. Do not reintroduce a synonym.
- **Lemma 4.14 carries one binder the paper does not: `[MeasurableSingletonClass S]` on
  `X`'s range (M2 ruling, 2026-08-18).** This is the only deliberate binder divergence in
  §4, and it is a *repair*, not a narrowing of convenience: as printed the lemma is false,
  with a machine-checked counterexample (errata 15). Round 2's binder strip (R2-F01/F23)
  had gone one range too far — it correctly removed the finiteness binders and correctly
  left `T₁`, `T₂` bare, but it also removed the one binder the statement cannot survive
  without. The orchestrator ruled on 2026-08-18 that the binder is restored, on the licence
  of the paper's own §2 standing convention. Two consequences for anyone editing this
  statement: adding a `FiniteRange`/`FiniteEntropyOf` binder here is still a finding, and
  *removing* `[MeasurableSingletonClass S]` is now also a finding.

  **Say the licence precisely (R4-F13, 2026-08-18).** It is Definition 3.1 and §2's standing
  setting that every random variable under consideration has **countable discrete range**
  ("a finite family of random variables `Xᵢ : Ω → Rᵢ`, each of which has countable and
  discrete range", paper L228–230; §2 puts the same condition on Proposition 2.5's
  variables at L196). It is **not** the §2 sentence just before Definition 2.4 ("our
  probability spaces are countable and discrete, and have finite entropy", L184) taken on
  its own: that one constrains the sample space `Ω`, and the entire content of erratum 15 is
  that constraining `Ω` alone leaves the lemma false. The licence is available here because
  Lemma 4.14 is only ever *applied* to variables of a model, which is exactly what
  Definition 3.1 constrains. An earlier docstring cited the `Ω` sentence alone and so
  appeared to license the repair with the very hypothesis the counterexample satisfies.
- **§4's Def 4.8 / Prop 4.10 are stated over `RVModel (PPlus I)`; Lemmas 4.14 and 5.4 are
  over bare variables. This asymmetry is a deliberate, documented generality choice
  (R4-F21), not drift.** `RVModel.OrderedMarkov` and `RVModel.orderedMarkov_iff` quantify
  over a bundled model, so they inherit §2's blanket convention wholesale — countable
  discrete sample space of finite entropy, countable discrete ranges — and carry **no**
  local finiteness or discreteness hypotheses at all; finiteness reaches them through
  `finiteEntropy_Ω` and `RVModel.finiteEntropyOf`. `Condensation.aeFunctionOf_of_condIndepFun`
  (4.14) and `Condensation.condEntropy_le_of_pair` / `.condEntropy_eq_of_pair` (5.4) are
  stated over bare measurable functions with explicit binders, because the paper states them
  that way and because they are substrate lemmas with clients outside a model. The cost is
  that the two halves of §4 are not directly comparable binder-for-binder, and the benefit is
  that neither is weaker than the paper's own statement. A bare-family restatement of
  Definition 4.8 and Proposition 4.10 — over `(Y : PPlus I → Ω → R _)` with explicit
  finite-entropy binders — is a **possible follow-up**, not a defect: it would be strictly
  more general, and nothing in §4 or §5 needs it, since every consumer already has a model in
  hand. Do not "fix" the asymmetry by adding hypotheses to the model-side statements.
- **`Mathlib.Order.Extension.Linear` is not in the substrate's import closure** and is
  imported explicitly by `Model.lean` for M2's benefit. `ShannonInformation.API` does not
  bring `LinearExtension`/`toLinearExtension` transitively at this pin, and the §4 tranche
  needs them; discovering that at proof time costs an import edit plus a full rebuild of
  everything downstream. It landed as predicted: `Condensation/ChainRule.lean`'s
  `exists_strictTotalOrder_ext` is the only consumer, through `extend_partialOrder`.
- **`Condensation.exists_strictTotalOrder_ext` is an upstreaming candidate: Mathlib has no
  strict Szpilrajn.** `Mathlib.Order.Extension.Linear` provides only the *reflexive* form
  (`extend_partialOrder : ∃ s, IsLinearOrder α s ∧ ∀ a b, p a b → s a b`, plus the
  `LinearExtension` type synonym). There is no companion producing an
  `IsStrictTotalOrder α r` extending a strict partial order, which is what any
  peel-off-a-greatest-element induction actually wants — so this library had to build one by
  hand (see the pitfall below for the exact class-registration order). It is fully generic:
  it mentions nothing about `PPlus`, entropy, or this paper, and its proof is ~20 lines over
  `extend_partialOrder`. **Leave the code where it is** — this is a note for a future
  upstreaming pass, not an instruction to move or delete anything. A Mathlib PR would want
  it in `Mathlib/Order/Extension/Linear.lean` beside `extend_partialOrder`, stated for
  `[IsStrictOrder α p]` or as the `∧ a ≠ b` transform of the existing result.
- Registry: `scripts/papers.py` uses two axes for this paper — `scheme: printed-counter`
  (how the paper numbers) and `source_format: text-extraction` (what the committed source
  is). Resolve parsers via `paper_nodes.scheme_of(paper)`, never `SCHEMES[scheme]` (the TeX
  parser returns an *empty* node set on a `.txt`, silently disarming the gate).
- Wiring-gate order for this library: `lean_lib Condensation` → Lean under `Condensation/` →
  `import Condensation` in `AxiomAudit.lean` → `-- CONDENSATION-INVENTORY-BEGIN/END` block
  wrapping `#assert_axioms_clean` (mandatory from the first annotated declaration; fully
  qualified names) → `python3 scripts/gen-trust-surface.py` after **any** change to a
  Condensation Lean file, README, KNOWLEDGE, errata, extraction, `papers.py`,
  `paper_nodes.py`, generator or template (the freshness hash covers all of them; CI blocks).
- Scope completeness is not yet machine-checked: `check-condensation-nodes.py` checks cited
  nodes are real and *reports* coverage, but does not fail on an in-scope node that no
  declaration cites. As of 2026-08-18 it reports `39/42` — §2 5/5, §3 12/12, §4 15/15,
  §5 7/10 — with the three uncited being Examples 5.1, 5.2, 5.3, which the proposed ruling
  puts out of scope. Once that ruling lands, pass a `scope_manifest` (`out_of_scope`,
  `mathlib_rendered` = Def 2.1, Def 2.4) to `paper_nodes.run_node_check` as the FFS checker
  does, and the 39/42 becomes a green 39/39.
- Substrate: `ShannonInformation.API` only. Never name `PFR.*`; never `import Mathlib`
  wholesale in a Condensation file (clashes with the vendored shims — see
  `ShannonInformation/README.md`).
- **Def 3.1's finiteness is a class parameter of `RVModel`, not a field (settled
  2026-08-17, R1-F01/F05/F07/F11/F14/F16/F30/F32).** `structure RVModel (I : Type w)
  [Finite I]`. It must not be a field: `Finite I` does not mention the model, so instance
  search would never find a field, and the concrete failure that forced this was
  `reconScore` elaborating happily at `I = ℕ` with `famFinset` silently empty (a
  silent-zero trap), while `simpleScore`/`condScore` carried `[Fintype I] [DecidableEq I]`
  binders they never actually needed. All three scores now have the same binder shape and
  need only `[Finite I]`; `Finite (PPlus I)` follows by instance. Do **not** reintroduce
  `Fintype`/`DecidableEq` on a score or on anything quantifying over `P⁺I`.
- **Latent universes are independent of the model's (settled 2026-08-17, R1-F08/F29).**
  `LatentModel.{u, v, w, u', v'}` puts `Λ : Type u'` and the latent ranges in `Type v'`,
  unrelated to `M`'s `u`/`v`. An earlier draft pinned them to `M`'s and called that a
  "documented narrowing" citing a KNOWLEDGE disclosure that never existed. Unpinning was
  tried and kept: the observed ergonomics are that statements *quantifying over* a latent
  model (`{I} [Finite I] {M : RVModel I} (L : LatentModel M)`, i.e. every §4/§5 theorem
  shape) need no annotation at all, and concrete constructions (`def coinLatent :
  LatentModel coinModel where …`) infer `u'`/`v'` from the body. The only sites that need
  an explicit universe list are **existence** statements — `Nonempty (LatentModel.{u,v,w,u,v} M)`
  — and that is not a new cost: `Nonempty (RVModel.{u,v,w} I)` already needs one for the
  same reason. What the pin *did* cost was faithfulness: Example 4.4 sets `X_i := Y_∋i`,
  which puts the given ranges in `Type (max v' w)` while the latents stay in `Type v'`, so
  under the pin it was statable only for pre-inflated latent range universes.
  Note the parameter order is `u, v, w, u', v'` (order of first appearance), so `M`'s
  universes come first in an explicit list.

## Intentional deviations from the paper

- Examples 5.1–5.3 carry no declarations (proposed ruling; see roadmap). Note this is
  *not* rescued by the finite-entropy generalization and never was: the paper's own text
  says `L` there has uncountable range, so it is outside countable discreteness, not
  merely outside finite range. They are the **only** uncited numbered nodes of the paper as
  of 2026-08-18 — the node checker's `not yet cited (3)` line names exactly these three, so
  that line is the standing evidence for the ruling and should go to zero (by
  `scope_manifest`, not by new declarations) when it lands.
- Universe stratification (`dd:bundled-model`): `RVModel` fixes `Ω : Type u` and
  `R : I → Type v`, and the category instance is taken at fixed universes, where the paper
  quantifies without stratification. Presentational rather than a cardinality bound
  (universe lifting represents larger presentations), still open ruling 3 in the roadmap,
  and unaffected by the 2026-08-17 change.

(`dd:finite-range` was the third entry in this list until 2026-08-17. It is retired, not
softened; its history lives in design decisions above.)

## Disclosures (residual modeling substitutions)

**None, and none pending.** The one standing candidate, `dd:finite-range`, was retired on
2026-08-17 when `ShannonInformation/FiniteEntropy/` landed and the consumers migrated;
Definition 3.1 is now carried verbatim, including its "with finite entropy" clause on `Ω`,
which the library previously did not carry at all. No statement in `Condensation/` stands
in for a paper claim it does not make.

## Paper errata

- Thm 5.8 proof: "Equation (5.14) follows by a term-by-term comparison" — should be (5.13).
- Thm 4.15 proof: `F_i` is used but never defined (evidently `F_i = {B : i ∈ B}`); the
  induction over `⋂_{i∈A} F_i` is asserted, not set up.
- Cor 5.10 (5.24): "all but `n − 1` elements" — the parameter is `k`.
- Thm 4.9 (B2): "is a function of `X_i`" drops the "almost everywhere" of (A2).
- Lemma 4.5 proof cites "Corollary 2.5" — 2.5 is a Proposition.
- Cor 4.6 proof cites only Prop 4.2; the argument needs Lemma 4.5.
- `P I` written for `P⁺ I` in Lemma 4.5(2) and Cor 4.6 (the paper's omission, not the
  extractor's — the extractor renders this paper's superscript `+` on its own line elsewhere).
- Cor 5.10 uses `k` in its hypothesis one sentence before binding it; the degenerate
  `k = 0` (`F = {∅}`) and `k > |A|` (`F = ∅`, `G = P⁺I`) cases are unaddressed — must be
  resolved to state it in Lean.
- The intersection tree's label function is `ℓ` in Def 5.6/Prop 5.7 but `I` in Thm 5.8 and
  Cors 5.9–5.10, colliding with the index set and (inside (5.13)) with the mutual-information
  operator. Part of why `dd:tree` computes labels from tree structure.
- Def 4.12 does not tie `π̃₁` to `π̃₂` — each `L̃ₖ` carries its own map to `Ω`, and the
  commuting square (4.43) belongs to Def 4.11, which Def 4.12 does not restate. Thm 4.15's
  proof needs them to agree a.e.; carried as the field `LatentAmalgamation.comm`.
- Ex 4.1's (4.4) and (4.5) are false at `A = ∅`: both scores are the empty sum `0` while
  the right-hand side is `H(X_I)`. The Lean statements take `A.Nonempty`.
- Thm 5.8 uses the `Z`-side contribution condition at (5.18) without listing it as a
  hypothesis. Licensed by Def 4.12, not by Thm 5.8; the Lean statement quantifies over
  `LatentAmalgamation`, whose field `contributes₂` is where the licence lives.
- Def 5.6's "parents" of a vertex are its *children* under the usual convention (its edges
  point towards the root). Not an error, but it inverts a formalizer's reading and cost one
  wrong first draft.
- **Lemma 4.14 is false as printed** (entry 15, found at M2, 2026-08-18). The printed
  hypotheses constrain only the ambient space ("countable discrete probability space") and
  `C`'s range ("discrete"); the ranges of `X`, `Y₁`, `Y₂` are unconstrained. If `X`'s range
  carries a σ-algebra that does not separate points, the conditional-independence hypothesis
  goes vacuous while the conclusion still constrains `X`. The machine-checked refutation of
  the literal transcription: `Ω = Bool` uniform, `U = Unit` (so `C` is constant),
  `S = T₁ = T₂` a two-point type carrying the **trivial σ-algebra `⊥`**, and
  `X = Y₁ = Y₂ = id` — every hypothesis holds (any map into a `⊥`-space is measurable,
  `comap Yₖ ⊥ = ⊥` makes the independence automatic, and `Prod.snd` witnesses both
  functional dependences) while the conclusion would force `id` to be a.e. constant. **The
  repair is one binder**: `X`'s range gets `[MeasurableSingletonClass S]`, which is licensed
  by the paper's own §2 convention ("our probability spaces are countable and discrete",
  stated just before Definition 2.4) and is free at every call site in this library, since
  `X` is always a model's variable and `RVModel` carries `singR`. `T₁` and `T₂` genuinely
  need only `MeasurableSpace`. This is a *narrowing of the printed statement*, and it is the
  one place in §4 where the Lean is deliberately not the printed binders.

  **The mechanism, as recorded here until 2026-08-18, was wrong, and the wrong version is
  seductive — do not re-derive it.** The wrong account: "the conditional-independence
  hypothesis goes vacuous because `X`'s range fails to separate points". It cannot:
  `ProbabilityTheory.CondIndepFun Y₁ Y₂ C μ` mentions only `Y₁`, `Y₂` and `C`, **never `S`**.
  The correct account: the vacuity is `T₁`/`T₂` at `⊥` (`comap Yₖ ⊥ = ⊥` makes the
  independence automatic); `S` at `⊥` plays the *other* role in the counterexample, making
  the two `AEFunctionOf` hypotheses trivially satisfiable, since any map into a `⊥`-space is
  measurable and `Prod.snd` then witnesses both. The consequence that matters is that there
  are **two independent minimal repairs**, and the printed statement needs exactly one of
  them: (i) `[MeasurableSingletonClass S]` — the Lean's choice, informally what makes the
  argument's step "`X`'s level sets lie a.e. in `σ(C,Y₁) ∩ σ(C,Y₂)`" meaningful; or (ii)
  `[MeasurableSingletonClass T₁]` and `[MeasurableSingletonClass T₂]` — the repair the
  *printed proof* implicitly uses. Both are licensed by §2. So the Lean's binder is a
  *choice* between two repairs, not the unique fix. And the strength claim: what is needed
  is that **`X`'s range separates points**, not that it is "countable discrete" — there is no
  `Countable S` binder in `aeFunctionOf_of_condIndepFun` and adding one would overstate what
  the proof uses. General lesson: before attributing a vacuity to a typeclass, check which
  types the hypothesis's *definition* actually mentions.
- **(4.39)'s right-hand containment is self-contradictory as printed** (entry 16, candidate,
  found 2026-08-18). In Proposition 4.10's proof — *not* Theorem 4.9's — the paper displays
  `S_A ⊆ F ∪ {B ∈ G∖F : B ≺ A} ⊆ I_A` (and the `F ∩ G` variant on the next line), where
  `I_A` is the set of elements incomparable with `A` and `S_A` the set of strict supersets of
  `A`. But `S_A ∩ I_A = ∅` by construction and the left containment is genuine, so the
  display asserts `S_A ⊆ I_A`, which fails for every `A` that has a strict superset. The
  intended right-hand set is `I_A ∪ S_A`. Two things make this a slip in the symbolic
  rendering rather than a mathematical error: the paper states the *same* sandwich correctly
  in prose at the parallel step (4.35), and the Lean already carries the intended version —
  `RVModel.condEntropy_jointOn_eq_of_condIndepFun` is exactly the sandwich `S₂ ⊆ W ⊆ S₁ ∪ S₂`,
  instantiated at Proposition 4.10's call site with `S₁ = incomparable A` and
  `S₂ = strictAbove A.toFinset`, with `pred_subset_incomparable_union_strictAbove`
  discharging the right inclusion.

- **Def 5.6 never requires the tree to be finite or well-founded** (entry 17, from the final
  blind audits, 2026-08-18). Condition (1) constrains directed paths *to* the root, which the
  full infinite binary tree satisfies; Thm 5.8's (5.13)/(5.14) are finite sums over leaves
  and internal vertices, and the leaf-bijection hypothesis does not bound the internal ones.
  The inductive `ITree` reads Def 5.6 as ranging over the finite trees — a *disclosed
  reading*, licensed by Thm 5.8's sums, and no longer described as "nothing is lost". Note
  entry 14's "such a tree has at least one leaf" is licensed only by this reading.
- **Prop 2.5's proof calls `P(· | X = x)` a Dirac measure in `G(Ω)`** (entry 18). It is the
  *pushforward* `Y_* P(· | X = x)` that is Dirac, in `G(R_Y)`; `H(Y|X) = 0` determines `Y`
  from `X`, not `ω` from `X`. `Probability.lean`'s Def 2.4 docstring quotes this sentence to
  justify the `ProbabilityMeasure Ω` carrier — the quotation settles the carrier and only
  the carrier, and the docstring now says the sentence is wrong about the space.
- **Lemma 4.5 (⇐)'s "picking any `i ∈ A`" is wrong** (entry 19). Different `B ∈ contrib A`
  need different `i`: at `A = {1,2}`, `B = {2}`, the latent `Y_{2}` is constrained only
  through `X_2`. Harmless to the conclusion, and the Lean routes through `X_A` directly.
- **Lemma 4.13's (4.53) sentence writes `P₂(· | π₁ = ω)` for `P₂(· | π₂ = ω)`** (entry 20).
  Prose only; every display around it is correct, and `Amalgamation.canonical` is built from
  the displays.
- **The discussion before Thm 5.8 names `Y_∩B` where `Y_⊇A` is meant** (entry 21, *soft*).
  Recorded with an explicit caveat: a charitable reading makes the defect the phrase "is an
  approximate form of" rather than the subscript. Motivating prose; nothing formal depends
  on it. Do not upgrade it to a flat misprint without re-reading L1358–1361.
- **Cor 5.9's proof attributes (5.22) to Def 4.8; it needs Prop 4.10** (entry 22). The tree's
  label sets are *upward-closed*, so killing the interaction terms is Prop 4.10 clause (2),
  not the definition. The paper itself says so correctly at L1363–1365. This is why (5.22)
  was the last §5 endpoint to become axiom-clean.

**One candidate was REFUTED and must not be re-raised**: "the prose after Prop 4.7 reverses
the perfect / simply-perfect implication". L717–718 ("Corollary 4.6 tells us something about
perfect, and hence simply-perfect, condensations") is a claim about the *scope of Cor 4.6*,
licensed by the true direction simply-perfect ⇒ perfect. Ambiguous English, not a reversed
implication. The refutation is recorded at the foot of `notes/paper-errata.md`.

Full list (twenty-two entries, plus the one refuted candidate) with line numbers:
`notes/paper-errata.md`.

## Audit history and corroboration

**What the trust surface actually rests on, as of 2026-08-18.** The library has been through
four adversarial audit rounds, and the last one is the load-bearing evidence, so it is worth
recording what it did rather than merely that it happened.

- **The final audits were *blind*.** Two independent auditors — an Opus fresh-context
  auditor and a codex (cross-family) auditor — were given only the paper, the Lean source
  and the standing orchestrator rulings. They were **not** given `notes/paper-errata.md`,
  `KNOWLEDGE.md`'s errata section, or any prior round's findings. So anything they reported
  that matches an existing entry is a genuine independent rediscovery, not an echo.
- **They independently rediscovered errata 1, 2, 4, 6, 8, 10, 11, 15 and 16.** That is nine
  of the recorded defects re-derived from the paper alone, including the two hardest
  (15, Lemma 4.14's falsity as printed, and 16, (4.39)'s self-contradictory containment).
- **They confirmed both standing orchestrator rulings with counterexamples of their own
  construction** rather than by agreeing with the recorded argument.
- **Treat this as the corroboration the trust surface rests on, and do not quietly weaken
  it.** The specific thing that would destroy its value is showing a future auditor the
  errata file before they audit: the errata list is a set of *answers*, and an auditor who
  has read it can no longer supply independent evidence that the paper's defects are real.
  If a future round needs the errata file for context, run it as a *separate*, clearly
  labelled non-blind pass and do not count its agreements as corroboration.
- Round 4 itself (this wave) was where the blind audits' output landed: the `dd:tree`
  finiteness disclosure (R4-F02), the Mathlib duplication (R4-F22), the degenerate Def
  4.3/4.8 witnesses (R4-F23), the API/trust-surface documentation errors (R4-F01/F13/F20/
  F24–F27) and errata 17 onward.

## Pitfalls

- **"`sorry` count" and "`sorryAx`-dependent count" are different numbers, and this repo
  quotes both.** Both are **zero** as of the M2 wave (2026-08-18) — `check_sorry_ledger.py`
  reports `0 sorry-dependent declarations, all ledgered (0 main, 0 consumers)` and the
  `CONDENSATION-PENDING` block is empty in both of its sections — so the distinction is
  currently moot, but it will bite again the moment one `sorry` is reintroduced, and the
  history is what explains the ledger's shape. The compiler's `declaration uses 'sorry'`
  warnings count declarations *containing* a `sorry` (17 on 2026-08-17). The ledger counts
  declarations *depending on* `sorryAx` (21 the same day), which also picks up complete
  proofs that consume a staged one: three un-annotated consumers, plus Corollary 4.6
  (`aeFunctionOf_of_perfectlyCondenses`, an annotated endpoint whose own proof was
  finished), and historically `Amalgamation.finiteEntropyMeasure_canonicalMeasure`.
  17 + 1 + 3 = 21. Do not reconcile them by "fixing" one; state which you mean. This gap is
  the whole reason the `CONDENSATION-PENDING` block needed its
  `SECTION: consumers (un-annotated)` second section — which is now present but empty, and
  should stay present.
- **`scripts/check_trust_surface.py` is a freshness hash over ~156 inputs and says nothing
  about correctness.** In a multi-agent session it fails constantly on pure staleness. The
  only meaningful reading is "regenerate with `gen-trust-surface.py`, then immediately
  re-run the check" — and, since the hash covers every Condensation Lean file, README,
  KNOWLEDGE, errata, extraction and the generator itself, it must be the *last* thing you
  do before committing.
- **`scripts/trust-surface-template.html` is a second, easily-missed home for every
  modelling-boundary ruling, and it drifts silently.** Retiring a `dd:` deviation is not
  finished when the Lean, README, KNOWLEDGE and roadmap are updated: the template's
  `.no-tier` box for that paper carries the same disclosure in its own prose, and nothing
  cross-checks the two. `dd:finite-range` was retired on 2026-08-17 and the template still
  published it as "the standing modelling narrowing" until the round-2 fix wave — a page
  contradicting the README it links to. Grep the template whenever a disclosure changes.
- **A CI step that runs `lake` in a plain `run:` block after `leanprover/lean-action@v1`
  may not find it on `PATH`.** `scripts/check_sorry_ledger.py` is wired as a post-build
  step for exactly this reason (it reads oleans and must follow the build). If the first CI
  run fails with `lake: command not found`, prepend `~/.elan/bin` to `PATH` in that step
  rather than changing the script.

- **`Set.indicator_of_mem` / `_of_notMem` cannot infer `s` from a membership proof that is
  only *definitionally* `x ∈ s`.** Given `h : π₁ a = π₂ b`, `Set.indicator_of_mem h _`
  cheerfully unifies `s := Eq (π₁ a)` and the point `:= π₂ b` — a nonsense set that then
  fails several lines later with an opaque "did not find an occurrence of the pattern".
  Always name both: `Set.indicator_of_mem (s := {q : Λ₁ × Λ₂ | π₁ q.1 = π₂ q.2}) (a := (a, b)) h _`.
  Cost ~15 minutes, three times in one session, during Lemma 4.13.
- **`rw` will not fire under an unreduced beta-redex; `simp only` will.** Lemmas of the
  `tsum_carrier` shape leave summands as `(fun q => …) ↑p`, and a `rw [Set.indicator_of_mem …]`
  reports a pattern failure that reads like a real mismatch. The same lemma list under
  `simp only [...]` works, because simp beta-reduces first. When `Measure.dirac_apply'` has
  produced `s.indicator 1 p`, add `Pi.one_apply` to that list too.
- **`omit … in` goes *before* the docstring, not between the docstring and the
  declaration.** `/-- doc -/` then `omit [X] in` then `lemma foo` fails with the misleading
  `unexpected token 'omit'; expected 'lemma'`. `carrier.comm` in `Amalgamation.lean` shows
  the right order.
- **`le_antisymm hle (zero_le _)` does not elaborate in `ℝ≥0∞`** — the ambient `zero_le`
  takes its argument implicitly, so the `_` is an over-application and the error is the
  unhelpful `Function expected at zero_le`. Where `hle : x ≤ 0`, `simpa using hle` is the
  one-token fix.
- **The `Measure.sum`-of-Diracs vocabulary has four entry points, all in
  `Mathlib/MeasureTheory/Measure/Dirac.lean`, and they are easy to confuse.**
  `Measure.sum_smul_dirac_singleton` (:142) evaluates such a sum at a singleton and needs
  **no** `Countable`; `Measure.sum_smul_dirac` (:138) says `∑ μ{a} • dirac a = μ` and does;
  `Measure.map_eq_sum` (:129) turns `μ.map f` into that shape; and
  `Measure.tsum_indicator_apply_singleton` (:187) converts a fibre sum back into a measure
  of a preimage. The clean recipe for a `MeasurePreserving` on a countable discrete space is
  `map_eq_sum` + `sum_smul_dirac`: it reduces the goal to the pointwise
  `μ (f ⁻¹' {b}) = ν {b}` and avoids `Measure.ext` entirely.
- **Calibration: `Condensation/Amalgamation.lean` round-trips under `lake env lean` in
  ~7.5 seconds on a warm `.lake`**, because its whole import closure is `Condensation.Model`.
  Lemma 4.13's three measure lemmas were budgeted at "1–3 hours, probably won't fit a
  one-hour box" and took ~50 minutes — iteration speed, not proof difficulty, was the
  deciding factor. Budget generously for *editing* this file and stingily for *waiting* on
  it, and prefer many small `lake env lean` cycles to reasoning about a goal offline.

- **Never write the literal string `Paper node` followed by a colon inside a docstring
  except as a real annotation.** `paper_nodes.MARKER` is that exact substring, so a
  docstring *talking about* the convention ("carries no <that string> of its own") is
  parsed as an annotation and fails the checker twice over -- MALFORMED (it names no node)
  and, in a `/-! ... -/` module header, UNANCHORED. Round 2 hit this three times in one
  pass while writing prose explaining why something is un-annotated. Write "paper-node
  annotation" instead.
- **`~/.claude/scripts/safe-lake.sh` exits 0 even when the underlying `lake build` FAILS.**
  The wrapper's exit status reports the wrapper, not the build. A green-looking
  `[exited with code 0]` at the bottom of the teed log can sit directly under
  `error: build failed`. Always grep the log for `error:` before believing a build is
  green -- a fixer that trusts the exit code will report a red build as green.
- **`ITree.LabelsIn` and `LTree.LabelsIn` are different predicates with near-identical
  names.** The `ITree` one constrains only the **leaves**; the `LTree` one constrains
  **every** vertex. Their `@[simp]` node lemmas also take different arguments --
  `LTree.labelsIn_node` takes the vertex label `a` explicitly (`node a l r`),
  `ITree.labelsIn_node` does not (`node l r`). `ITree.label_mem_of_labelsIn` (leaves-in-`M`
  plus meet-closure gives every vertex's label in `M`) and `ITree.labelsIn_decorate` are
  what reconcile them; do not add a third "labels of every `ITree` vertex" predicate.
- **Truncated natural subtraction inside a set-builder *in a statement* is a faithfulness
  hazard, not just a proof nuisance.** `{C | (A \\ C).card <= k - 1}` silently reads
  `<= 0` at `k = 0`, i.e. `A subset C`, where the prose "all but at most `k-1` elements"
  suggests a vacuous condition. `polar_kSubsets`'s docstring got the `k = 0` degeneracy
  backwards for exactly this reason (R2-F16). The one-line settler:
  `simp only [Nat.zero_sub, Nat.le_zero, Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset]`.
- **Do not *reason* about a degenerate case in a docstring -- compute it.** Both §5
  docstring findings of round 2 were settled by a throwaway `-- TEMPCHECK-BEGIN/END` block
  of `example`s after `end Condensation`, elaborated in one `lake env lean` run and then
  deleted. A docstring claim about a boundary value is cheap to check and expensive to get
  wrong, because nothing downstream type-checks prose.

- **Mathlib *does* have `Subtype.instMeasurableSingletonClass` at this pin, and an earlier
  docstring in `Amalgamation.lean` said it does not.** The claim ("Mathlib has no `Subtype`
  instance for `MeasurableSingletonClass` at this pin; a singleton of the subtype is the
  preimage of a singleton under the (measurable) coercion") sat above a hand-rolled instance
  for `Amalgamation.carrier`, which was deleted in round 2 (R2-F09). It is at
  `Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean:196`. The general lesson, which
  cost real time twice on this branch: a "Mathlib lacks X" comment is a *claim about a
  moving target* and ages badly — re-check it with `exact?`/`grep` in `.lake/packages/mathlib`
  before building around it, and if you write one, write the search you ran.
- **The same failure, third occurrence: `Condensation.iIndepFun_of_subsingleton` duplicated
  Mathlib's `ProbabilityTheory.iIndepFun.of_subsingleton` for the whole of M1–M2 (deleted
  2026-08-18, R4-F22).** Mathlib's is at `Mathlib/Probability/Independence/Basic.lean:246`,
  is `@[nontriviality, simp]`, takes its family **implicitly**, and sits beside
  `iIndepSets.of_subsingleton` and `iIndep.of_subsingleton`. The local copy was an
  eleven-line tactic proof of the same statement with the family explicit. What made this
  survive audits is instructive and worth guarding against: its docstring ended "…it is
  stated for a bare family of measurable functions and **would belong in
  `ShannonInformation/API.lean`, or upstream of it**, if a second client wanted it" — a
  sentence that reads as diligence (the author noticed it was generic!) while actually
  *asserting* that upstream does not have it. **A "this would belong upstream" note is a
  Mathlib-lacks-X claim in disguise and must carry the search that justifies it.** The one
  that would have settled it in seconds: `grep -rn "of_subsingleton"
  .lake/packages/mathlib/Mathlib/Probability/Independence/Basic.lean`. Concretely: before
  writing a lemma whose statement mentions no paper vocabulary, grep Mathlib for the
  *shape* under the naming convention Mathlib would use (`Foo.of_bar`, not `foo_of_bar`) —
  the dot-namespaced spelling is the one this library's `foo_of_bar` habit will not find.
- **The `Paper node:` line is the ledger's only hook, so an un-annotated declaration that
  states a paper claim is invisible to every gate.** Six `sorry`'d equations of Examples 4.1
  and 4.4 sat outside `check-condensation-nodes.py` and outside the `CONDENSATION-PENDING`
  block for the whole of M1 for exactly this reason (R2-F15). A paper's displayed
  *equations* are paper-facing endpoints: annotate them with the **enclosing** node's
  printed header (`Example 4.1`), and promote them `lemma` → `theorem`. Never invent an
  equation-level node id like `Example 4.1 (4.2)`; the checker matches printed headers in
  `notes/condensation-25-07.txt` and a node string that parses to nothing is a hard failure.
- **Mentioning `sorry` in docstring prose is normal here, so `grep -c sorry <file>`
  overcounts.** As of 2026-08-18 the string occurs four times in `Condensation/` —
  `Quantitative.lean` twice, `Comparison.lean` and `Examples.lean` once each — and **every
  one of them is prose**; there are no `sorry` tactics left. The authoritative counts are
  the compiler's `declaration uses 'sorry'` warnings in the build log (per-declaration, and
  reporting the *declaration's* line, not the tactic's) and
  `python3 scripts/check_sorry_ledger.py`, which reads the compiled environment.

- `pdftotext` emits the font's f-ligature slots as C0 bytes (`\x1c`=fi, `\x1b`=ff,
  `\x1d`=fl, `\x1e`=ffi), so `Definition` is stored as `De\x1cnition` (prints `Denition`).
  **Python's `str.splitlines()` splits on `\x1c`/`\x1d`/`\x1e`** and silently deletes all
  18 Definition headers — always `text.split("\n")` on this file (`paper_nodes.extraction_lines()`).
  Ligature-tolerant regex is `De(?:fi)?.?nition` (`De.?nition` fails on the plain spelling).
  Node headers are distinguished from line-initial cross-references only by the trailing
  period after the number/title parenthetical.
- **Two `∑'`-style traps in the substrate, and they are now the operative ones.** `H[X]` is
  `0` for a non-summable entropy series, and `condEntropy` is a Bochner integral, silently
  `0` when non-integrable. Under `dd:finite-range` neither could bite; since the 2026-08-17
  generalization they can, and the reason they do not is that the finiteness class carries
  both as *proved consequences* rather than as side hypotheses:
  `ShannonInformation.FiniteEntropyOf.summable` closes the first and
  `ShannonInformation.integrable_entropy_cond` (in `FiniteEntropy/ChainRule.lean`) closes
  the second. If you ever find yourself adding a `Summable …` or `Integrable …` hypothesis
  to a statement in this library, stop: that is the class failing to compose, and the fix
  belongs in the substrate. A statement that silently reads `0 = 0` is the failure mode
  this discipline exists to prevent.
- `SCOPE.md` §6 says `klDiv` is `EReal`-valued; at this pin it is `ℝ≥0∞`
  (`Mathlib/InformationTheory/KullbackLeibler/Basic.lean`). Corrected on this branch;
  the entropy-infrastructure owner should carry the same fix.
- The paper's `π` in a latent variable model goes `Λ → Ω` (latent space onto the base),
  while §3.1's morphisms go source → target with `π : Ω → Λ`. Do not conflate the two
  directions when reading Def 4.12 (morphisms `ρ_k : L̃_k → L_k`).
- **`ϱ_L` is zero on every "obvious" witness, and that is not a bug.**
  `ϱ_L(A) = H(Y_⊇A | X_A)` vanishes as soon as `Y_⊇A` is a function of `X_A` — which holds
  for `Y_A = X_A`, for Example 4.1's `L₁`, and for anything where `Λ = Ω` and the latents
  are built from the observables. A witness with `0 < ϱ_L` needs the latent space to carry
  randomness `π` discards: `Λ = Bool × Bool`, `π = Prod.fst`, `Y_{()} = id`. An earlier
  draft of `Examples.lean` claimed "every score takes a genuinely positive value" on the
  coin witness; that was false and is finding R1-F10.
- **`Y_⊋B` at a maximal `B` is a map into a subsingleton, not an error.** Definition 3.4's
  `Y_⊋B` is a dependent product over `strictAbove B`, which is *empty* when `B` is maximal
  in `P⁺I`; the pi type over an empty index is a subsingleton, so the corresponding term of
  `χ_L` is an unconditioned entropy. The vendored library has `entropy_const` and
  `mutualInfo_const` but no `condEntropy_const`, so `Condensation.condEntropy_eq_entropy_of_subsingleton`
  in `Probability.lean` supplies the missing form (a candidate for `ShannonInformation/API.lean`
  if a second client wants it).
- **`decide` traps around `PPlus`.** `decide` works fine through `Finset Bool` and
  `PPlus Bool` for equality and for `∈` (`PPlus.mem_iff` is `Iff.rfl` into `Finset`
  membership), and `famFinset (contrib …) = {…, …}` closes with
  `ext B; simp only [mem_famFinset, mem_contrib, …]; revert B; decide`. But `above`,
  `strictAbove`, `contrib` and `contribIdx` are `Set`s, so `B ∈ strictAbove A` has **no**
  `Decidable` instance and `by decide` fails with "failed to synthesize Decidable". The
  incantation that works is to `show` the underlying `Finset` relation first
  (`show A ⊂ B.toFinset; decide`), which is legal because `mem_strictAbove` and friends are
  `Iff.rfl`.
- **Lean identifiers cannot carry a combining tilde.** The paper's `Ỹ`, `Z̃`, `π̃`, `L̃ₖ`
  have no Lean spelling: `Ỹ` is not an identifier character sequence Lean accepts.
  `LatentAmalgamation` therefore spells them `Y₁`, `Y₂`, `π₁`, `π₂` as *fields*, and the
  tilde is carried by the qualification — `Am.Y₁` is the paper's `Ỹ` while `L₁.Y` is the
  paper's `Y`. Docstrings keep the paper's `L̃ₖ`, which is fine because docstrings are
  strings. Do not spend time hunting for a Unicode workaround; there isn't one.
- **`⟨Y₁, Y₂, C⟩` does not parse as a triple of random variables — right-nest it.** The
  vendored entropy API's conditioning variables are *pairs*, so the paper's `H(X | Y₁, Y₂, C)`
  is `H[X | ⟨Y₁, ⟨Y₂, C⟩⟩ ; μ]`, and that right-nesting is also the grouping the vendored
  chain rules produce. Anonymous-constructor notation will happily elaborate `⟨Y₁, Y₂, C⟩`
  to something else, or fail confusingly; write the nesting out.
- **`condMutualInfo_eq'` needs `(Z := ⟨…⟩)` when the conditioning variable is a pair.**
  Rewriting with it at a compound conditioning variable leaves `Z` unsolved and the rewrite
  either fails or picks the wrong occurrence. `Quantitative.lean`'s
  `condInteractionInfo_swap` shows the incantation:
  `rw [condMutualInfo_eq' (Z := ⟨Y₂, C⟩) hX hY₁ (hY₂.prodMk hC) μ]`.
- **`condEntropy_of_injective'` argument roles.** Its arguments are, in order, the measure,
  the measurability of the *conditioned* variable, the measurability of the *new*
  conditioning variable, the relabelling function, its injectivity, and the measurability
  of the *old* conditioning variable. Getting the two conditioning-variable measurability
  arguments the wrong way round type-checks in some symmetric cases and fails opaquely in
  others; `condEntropy_pair_rotate` is the worked example.
- **`CondIndepFun f g h μ` conditions on its *third* argument.** PFR's
  `CondIndepFun` (`PFR/ForMathlib/ConditionalIndependence.lean`) says "`f` and `g` are
  conditionally independent given `h`", unfolding to
  `∀ᵐ z ∂(μ.map h), IndepFun f g (μ[|h ← z])`. Definition 4.8's "`Y_A` and `Y_F` are
  independent conditional on `Y_⊋A`" therefore puts `Y_⊋A` last. Reading it as
  "conditional on the first argument" inverts the definition silently.
- **`iIndepFun L.Y L.P` needs no universe or index annotation**, despite `L.Y` being a
  dependent family over `PPlus I` with ranges in an independent universe. It elaborates as
  written; do not add `(κ := …)`-style hints preemptively.
- **The guarded-subtype encoding for heterogeneous latent ranges.** Example 4.1's "let `Y_A`
  be constant unless `A` is a singleton / all of `I`" cannot be written by a `Finset`
  case-split, because the *range type* has to depend on `A` and `if … then … else …` on
  types is a nightmare. The encoding that works is a **dependent product over a guarded
  subtype**: `R A := ∀ j : {i : I // <guard on A>}, M.R j.1`. When the guard fails the
  subtype is empty, the pi type is a subsingleton, and "constant" is automatic with no
  case-split anywhere. `L₁RV`/`L₂RV` in `Examples.lean` are the two instances.
- **`decide` on `A = Finset.univ` does not reduce for an abstract `I`.** `L₂RV`'s guard is
  written `∀ k : I, k ∈ A.toFinset` rather than `A.toFinset = Finset.univ` precisely so
  that no `Fintype I` is needed to *form* the definition; a `Finset.univ` in a statement
  drags a `Fintype` binder in with it. Where a top element really is needed inside a proof,
  a local `letI : Fintype I := Fintype.ofFinite I` produces it without escaping into the
  statement (`Example41.L₂`'s `contributes` field). And where `X_I` has to be *named* in a
  statement, use `RVModel.jointAll` — the dependent product over `I` itself — which needs
  only `[Finite I]`.
- **`finiteRange_pi` was retired on 2026-08-17, but the gap it filled is still real.** Kept
  as history because someone will want it back. `Condensation.finiteRange_pi` supplied
  `FiniteRange` for a dependent product of finitely many finite-range variables — the
  vendored `FiniteRange/Defs.lean` has the *binary*-product instance and nothing for a
  dependent product, and that is still true. It was a `lemma`, not an instance, and was
  applied explicitly (`finiteRange_pi (fun i => …)`); instance search never found it. It was
  what `RVModel.finiteRange_joint`/`_jointOn`/`_jointAll` were built from; those are now
  `finiteEntropy_joint`/`_jointOn`/`_jointAll`, one-liners from `RVModel.finiteEntropyOf` —
  a joint variable is measurable, and that is the whole argument. That left
  `Example41.L₁RV`/`L₂RV` as the only callers, and they now go through
  `M.finiteEntropyOf (measurable_pi_lambda _ fun j => M.measurable_X j.1)`; with zero
  callers, keeping an inventoried declaration would violate the library's own rule. If a
  `FiniteRange` product is genuinely wanted again, `Model.lean` says where it stood and it is
  six lines of `Set.Finite.pi`. Do not reinstate it as a step towards proving something about
  a general model — that is the wrong direction now.
- **Write `ShannonInformation.foo` in full, always.** Every file here opens
  `ProbabilityTheory`, and with that namespace open a bare entropy lemma name resolves by
  *elaboration success*, not by namespace — so a bare `chain_rule''` or `condMutualInfo_eq'`
  can silently pick the vendored `FiniteRange`-gated version instead of the FAF
  `FiniteEntropyOf` one, and the error you get is a missing `FiniteRange` instance several
  lines away from the citation. Since 2026-08-17 the layer genuinely contains two versions of
  several facts (this is the "fork risk" the generalization plan §5 named). Every FAF-layer
  citation in `Condensation/` is written out in full; keep it that way, and see
  `ShannonInformation/API.lean`'s "which version to cite" table.
- **Dot notation is the sharpest form of that trap, because it cannot be fixed by opening a
  namespace.** `h.condEntropy_eq_entropy` and `hid.condEntropy_eq` resolve in the *head
  symbol's* namespace — `ProbabilityTheory.IndepFun`, `ProbabilityTheory.IdentDistrib` — and
  so always find the `FiniteRange` original, never the FAF one, no matter what is open. Write
  `ShannonInformation.IndepFun.condEntropy_eq_entropy h …` and
  `ShannonInformation.IdentDistrib.condEntropy_eq …` out in full and pass the hypothesis as
  an ordinary argument. `Examples.lean`'s `noisyLatent_condScore` carries a comment saying so
  at the one site where it bit.
- **`ShannonInformation.finiteEntropyOf_pair` needs `IsProbabilityMeasure`, but the
  surrounding lemma usually has only `IsZeroOrProbabilityMeasure`.** That mismatch is why
  several §2/§5 proofs now open with
  `rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ` — the zero branch is closed by
  `simp`, and the other branch has the instance. `Probability.lean:363` and the three Lemma
  5.4 lemmas in `Quantitative.lean` are the worked examples. Do not "fix" this by
  strengthening the statement to `IsProbabilityMeasure`: the vendored lemmas the proof
  otherwise cites are stated at `IsZeroOrProbabilityMeasure` and the strengthening would
  propagate.
- **A wrong belief, held during the 2026-08-17 migration and corrected: "the range type here
  is a `Fintype`, so `FiniteRange` still synthesises."** It does not, behind a bundled model.
  With `RVModel.finiteRange_X` retired there is no longer a structure instance for
  `FiniteRange (M.X i)`, and instance search will **not** unfold a concrete model
  (`noisyLatent` → `noisyLatentRV` → `R = fun _ => Bool × Bool`) to rediscover that the range
  happens to be finite. It is the same blindness that already forces the hand-written
  `instance : Finite noisyLatent.Λ := inferInstanceAs (Finite (Bool × Bool))`. The practical
  consequence: a vendored `FiniteRange`-gated lemma cannot be cited on a *model's* variables
  at all any more, even when the model is built on `Bool × Bool`. That is why
  `ShannonInformation.IndepFun.condEntropy_eq_entropy` had to be added to
  `FiniteEntropy/Derived.lean` for `Examples.lean`'s `noisyLatent_condScore`. Do not budget
  "the witness is finite so the old lemma still applies" — it does not.
- **On a model's sample space, `M.finiteEntropyOf (hA.prodMk hB)` beats
  `ShannonInformation.finiteEntropyOf_pair` for a pair-shaped instance argument.** It is one
  step, needs no `(μ := μ)` hint, and sidesteps `finiteEntropyOf_pair`'s
  `IsProbabilityMeasure` requirement. Definition 3.1's `Ω` clause is exactly what makes the
  difference. The `rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ` dance is
  unavoidable only in the §2/§5 lemmas over *bare* variables, where there is no model to ask.
- **Definition 3.1's `Ω`-clause pays for itself, so reach for `RVModel.finiteEntropyOf`
  before proving finiteness by hand.** For any measurable `Z : M.Ω → S`, `M.finiteEntropyOf
  hZ : ShannonInformation.FiniteEntropyOf Z M.P`. Every derived variable of the development —
  joint variables, pullbacks, relabellings — is measurable, so its finiteness is one step and
  never a summability argument. The instinct carried over from `dd:finite-range` (find or
  build a closure instance for the shape of the variable) is now the slow route.
- **PFR has no chain rule for a finite family, and that single gap blocked four §4
  endpoints — it is now filled by `Condensation/ChainRule.lean` (M2, 2026-08-18).** The
  vendored library stops at the two- and three-variable forms (`chain_rule`, `chain_rule'`,
  `chain_rule''`, `cond_chain_rule`, `cond_chain_rule'`). Proposition 4.2's second
  inequality, Proposition 4.10, and both halves of Theorem 4.9 all run on a chain rule along
  a *linear extension* of the inclusion order on `P⁺I`. The "one piece of infrastructure
  plus four applications" estimate held: `ChainRule.lean` is ~670 lines and the four
  consumers are short. The linear order comes from `Mathlib.Order.Extension.Linear`,
  imported explicitly by `Model.lean` (see design decisions). **Before proving anything new
  about joint variables, read `ChainRule.lean`'s `## Contents` docstring** — it also carries
  relabelling (`condEntropy_pair_jointOn`), monotonicity (`condEntropy_jointOn_mono`) and
  coordinate-dropping (`condEntropy_jointOn_sdiff`, `condEntropy_jointOn_above`) lemmas that
  are easy to re-derive by accident.
- **`RVModel.Hom`'s `f` field is dependent on `ι`, so morphism extensionality goes through
  `HEq`.** `Hom.ext` takes `hπ : φ.π = ψ.π`, `hι : φ.ι = ψ.ι` and `hf : HEq φ.f ψ.f`, and
  the `HEq` is unavoidable: `f : ∀ j, M.R (ι j) → N.R j` mentions `ι`. `Morphism.lean`
  isolates the pain in two variable-substitution transport lemmas used only by
  Proposition 3.8; do not try to state a `HEq`-free `ext` and do not propagate the `HEq`
  into a statement.
- **`push_neg` is deprecated in favour of the generalized `push Not`.** `polar_kSubsets`'s
  proof uses `push Not at h`. When copying a proof between files, copy it verbatim rather
  than "normalising" it back to `push_neg`.
- **`rw` closing a goal by `rfl` reports "motive is not type correct"-adjacent confusion:
  a "did not find instance of the pattern" error on the *last* rewrite of a chain usually
  means the goal was already closed by the preceding one.** `rw` tries `rfl` after each
  rewrite; if that succeeds, the remaining rewrites in the bracket have nothing to act on
  and report a pattern failure that reads like a real mismatch. Delete the tail of the
  chain rather than debugging it.
- **`↥(↑s : Set I)` and `↥(s : Finset I)` are interchangeable by `rfl`**, because
  `Finset.coe s` unfolds to `{a | a ∈ s}` and membership there reduces to `Finset`
  membership definitionally. This came up reconciling `Quantitative.lean`'s raw
  `jointFam X ↑B.toFinset` with `LatentModel.pullbackJoint B.toFinset` and was expected to
  need an `Equiv` transport; it does not. A one-line `example … := rfl` settles questions
  of this shape in seconds — make the check mechanical rather than reasoning about it.
- **Lean 4 includes an instance binder from a `variable` block only when the declaration
  actually uses a variable mentioning it**, which is why `Condensation.kSubsets` does *not*
  pick up `[Finite I]` even though `[Finite I]` is in scope and `kSubsets` mentions `I`
  (`Finite I` mentions `I`, but nothing in `kSubsets`'s body needs the instance). Do not
  reason about the inclusion rules from memory — `#check @foo` and read the actual signature.

  **This bullet used to continue "…that is what makes `polar_kSubsets`'s `omit [Finite I] in`
  legal", and that causal story is WRONG (corrected 2026-08-18, R4-F20).** It was tested by
  deleting the `omit` and running `#check @Condensation.polar_kSubsets`: the theorem *does*
  auto-include `[Finite I]`, and the binder duly appears in the signature. What is actually
  true is that the included binder is **unused** — (5.24) is pure `Finset` combinatorics —
  so the `unusedSectionVars` linter fires and `omit` is the silencer. `omit` is legal for an
  included-but-*unused* binder, not for a never-included one. The distinction matters
  because the old wording predicts the wrong outcome for exactly the experiment a "restore
  the binder for uniformity" finding asks you to run, and a fixer who trusts it will report
  a surprise.
- **`decide` traps around `PPlus` extend to the ORDER, not just the index families.**
  `PPlus.instPartialOrder` is a `PartialOrder.lift toFinset`, so there is **no**
  `DecidableLE (PPlus I)` and `decide` fails on any goal mentioning `≤` or `incomparable`.
  Same workaround as for `strictAbove`: `simp only [mem_incomparable, Set.mem_singleton_iff,
  PPlus.le_iff]` first — turning `≤` into `Finset` inclusion — then `revert B; decide`.
  `Condensation.twoCoin_incomparable_T` (`incomparable twoCoinT = {twoCoinF}`) closes in
  four lines this way. Conversely, `revert A; decide` *does* prove
  `∀ A : Finset Bool, A = ∅ ∨ A = {true} ∨ A = {false} ∨ A = {true, false}` instantly
  (`finsetBool_cases`); contrast the hand-rolled `finsetUnit_cases` directly above it in
  `Examples.lean`, which predates that insight and is five lines of `rcases`.
- **There is no `condMutualInfo_const` (nor `condEntropy_const`) in the vendored layer, and
  that is why `orderedMarkov_of_subsingleton_index` does not exist.** Record before
  re-attempting it: the available characterization of Definition 4.8's PFR `CondIndepFun` is
  `ShannonInformation.condMutualInfo_eq_zero` (the trick `Perfect.lean`'s `hsymm` uses),
  which reduces the goal to `I(X ; const | Z) = 0` and then has nothing to finish with.
  Mathlib's `ProbabilityTheory.condIndepFun_const_right`
  (`Mathlib/Probability/Independence/Conditional.lean:716`) is stated for Mathlib's
  *sub-σ-algebra* `CondIndepFun m' hm' f g μ`, **not** PFR's three-variable
  `CondIndepFun f g h μ` that `RVModel.OrderedMarkov` uses, so it is not directly citable.
  Anyone wanting the lemma should either bridge the two `CondIndepFun`s or add
  `condMutualInfo_const` to `ShannonInformation/FiniteEntropy/Derived.lean`. `Examples.lean`
  states the degeneracy as prose backed by the proved
  `incomparable_eq_empty_of_subsingleton_index` instead.
- **`lt_irrefl` does not apply to `Finset`'s `⊂`, and `simp` makes no progress on
  `hC : s ⊂ s`.** There is no `ssubset_irrefl` or `Finset.not_ssubset_self` at this pin; the
  only relevant lemma in `Mathlib/Data/Finset/Defs.lean` is `ssubset_iff_subset_ne` (:297).
  The working one-liner is `exact (Finset.ssubset_iff_subset_ne.mp hC).2 rfl`. Relatedly,
  `Subsingleton.elim C.1 B ▸ C.2` fails with "failed to compute motive"; the form that works
  is `have hC : B.toFinset ⊂ (C : PPlus I).toFinset := C.2` then
  `rw [Subsingleton.elim (C : PPlus I) B] at hC`.
- **A wrong belief, held and corrected 2026-08-18: instance *synthesis* refuses to unfold a
  concrete model, but defeq checking in `exact` unfolds it happily.** The expectation was
  that the measurable-space instance on `∀ i : ↥A, twoCoinModel.R i` (from the bundled `mR`
  field) would not unify with the plain pi instance on `∀ _ : ↥A, Bool`, so an `exact` across
  that boundary would need `show`/`convert`. It unified with no hint. The standing KNOWLEDGE
  warning that "instance search will not unfold a concrete model" — the one behind
  `LatentAmalgamation.finiteEntropyOf'`'s load-bearing `Λ₀` spelling — is about *instance
  synthesis*, which really does refuse. Two different mechanisms; do not generalize that
  warning into avoiding `exact` across the model boundary.
- **`ProbabilityTheory.entropy_comp_of_injective` is genuinely hypothesis-free** (no
  `FiniteRange`, no `FiniteEntropyOf`) and is the general route to `H[M.joint A]` at a
  **non-singleton** `A` for a model whose every `X i` is the identity:
  `entropy_comp_of_injective coinMeasure (measurable_id) _ hinj` with
  `hinj : Function.Injective (fun (b : Bool) (_ : {x // x ∈ A}) => b) :=
  fun _ _ hab => congrFun hab ⟨i, hi⟩` from any `i ∈ A`. `RVModel.entropy_joint_singleton`
  only reaches singletons.
- **`omit … in` is this repo's idiom for an unused auto-included section binder; nothing here
  uses `set_option linter.unusedSectionVars false`.** As of 2026-08-18: ~25 `omit … in`
  occurrences across `Condensation/` (`Amalgamation.lean` 14, `Quantitative.lean` 3,
  `ChainRule.lean` 3 — of which three are `omit [Finite J] in` — `Probability.lean` 3,
  `Examples.lean` 1 `omit [Finite I] in`), and **zero** occurrences of the `set_option`;
  `lakefile.lean` sets no warnings-as-errors. R4-F20 proposed deleting `polar_kSubsets`'s
  `omit [Finite I] in` for §5 uniformity; the documented fallback (keep the `omit`, say in
  the docstring why) was taken instead, because restoring an unused instance binder costs a
  permanent linter warning *and* adds an assumption the proof never consumes, against
  CLAUDE.md's minimal-typeclass rule. Weigh any future "restore for uniformity" finding
  against this: the uniformity argument is local to one declaration, the idiom argument is
  repo-wide, and forcing the restore would mean introducing the `set_option` mechanism.
- **Verify a reconciliation with a scratch block of `rfl`/`Iff.rfl` `example`s and
  `#check @…`, all in one elaboration, then delete the block.** Restating a theorem over a
  bundled structure raises several "are these the same term?" questions at once; batching
  them into one `-- TEMPCHECK-BEGIN/END` section costs one ~90 s `lake env lean` run
  instead of one run per question. This is how `Am.rv₂.OrderedMarkov ↔ orderedMarkovOn …`
  was confirmed to be `Iff.rfl` and `Am.lat₁.reconScore B.toFinset = reconOn …` to be
  `rfl`, which is what licensed deleting the local definitions rather than bridging them.
- **Capture the baseline before an edit that moves line numbers.** The five §5 `sorry`
  warnings moved from lines 645/669/691/710/776 to 616/638/657/674/737 purely because
  docstrings changed length. Without a pre-edit run to diff against, that shift reads as a
  structural change.
- **Parenthesise a `∑` that is followed by `+`.** `∑ x ∈ s, f x + g` parses as
  `∑ x ∈ s, (f x + g)`. The §5 bounds all have the shape `(∑ B ∈ famFinset F, H[…]) + (…)`,
  and the parentheses around the big operator are load-bearing even though the
  pretty-printer omits them on output — which makes the printed goal read as if the second
  summand were inside the sum. Do not "tidy" those parens away.
- **The `π₁`/`π₂` distinction inside an amalgamation is the one real hazard in reading §5's
  statements.** `Am.contributes₂` is phrased through `Am.π₂`, while `X_B` in Theorem 5.8 is
  pulled back along `Am.π₁`. They agree only *almost everywhere*, by the field `Am.comm`.
  Two statements that differ only in which `π` they name look identical at a glance and are
  not interchangeable without that field. M2's proof of (5.13) does use it, through
  `AEFunctionOf.congr_right` (`AEFunctionOf X Y μ → Y' =ᵐ[μ] Y → AEFunctionOf X Y' μ`) —
  predicted here, and written by two M2 shards independently; Theorem 4.15 needs the other
  side, `AEFunctionOf.congr_left`. Both now live in `Probability.lean` beside the rest of
  the `AEFunctionOf` API.
- **Stale-olean trap, hit twice in the round-1 fix wave.** `lake env lean Condensation/X.lean`
  elaborates `X` against the *built* oleans of its imports, not against your edits to them.
  After editing `Probability.lean`, `lake env lean Condensation/Model.lean` reported
  `failed to synthesize Finite (PPlus I)` for an instance that was already in the source.
  Rebuild the upstream module (`safe-lake.sh build Condensation.Probability`) before
  iterating downstream.

- **`Am.Λ₀`, `Am.lat₁.Λ` and `Am.lat₂.Λ` are three spellings of one type, and instance
  search sees only the one it is handed.** They are definitionally equal, but only through
  `LatentAmalgamation.lat₁`/`lat₂`/`rv₁`/`rv₂`, which are plain `def`s — not `abbrev`s, not
  `@[reducible]` — and instance search unfolds at *reducible* transparency only. So an
  instance registered at one spelling is invisible to a goal phrased at another, and the
  error you get is a "failed to synthesize" on something that synthesises perfectly well
  when you `#check` it on its own. Three consequences, all of them load-bearing in M2's
  code: (a) `LatentAmalgamation.finiteEntropyOf'` exists purely to be the `Λ₀`-pinned
  version of `RVModel.finiteEntropyOf`, and §5's proofs — which mix `Y`-side, `Z`-side and
  `Λ₀`-side variables inside one conditional entropy — need exactly that one; (b) inside a
  proof phrased at `Am.lat₂`, re-register by hand
  (`haveI : Countable Am.lat₂.Λ := Am.countΛ₀`,
  `haveI : MeasurableSingletonClass Am.lat₂.Λ := Am.singΛ₀`); (c) where a lemma takes the
  instance as a *named* binder, pass it — Theorem 4.15 calls Lemma 4.14 as
  `aeFunctionOf_of_condIndepFun (_hΩsing := Am.singΛ₀) …`, which is why that binder is named
  `_hΩsing` rather than anonymous. Do not "fix" this by making `lat₁`/`rv₁` reducible
  without measuring what it does to elaboration time.
- **The cross-model one-measure trap: a shared instance binder is taken from ONE side, and
  the reported failure names the other.** `ShannonInformation.IdentDistrib.condEntropy_eq`
  relates two conditional entropies whose conditioned variables share a single
  `[MeasurableSpace S]`. With `Am.lat₁.Y B` on the left, that instance is picked up as
  `Am.rv₁.mR B`, and instance search (reducible transparency again) cannot travel from there
  to `L₁.L.mR B` on the right — but what Lean *prints* is a `FiniteEntropyOf` failure on the
  **right**-hand side, a goal that synthesises fine in isolation. The fix that works is to
  restate the lemma over a **bare family** `Y : ∀ A : PPlus I, Λ₀ → L.L.R A` instead of over
  `Am.lat₁`, so that only one spelling of the range ever appears;
  `condEntropy_strictAbove_transfer` (private, `Comparison.lean`) is the worked example and
  `LatentAmalgamation.condScore_lat₁`/`_lat₂` are its two one-line clients. General lesson:
  when an instance error names a goal that is independently solvable, suspect a *shared*
  binder being fixed by the other argument, not the goal it names.
- **`entropy_comp_of_injective` will not invent the relabelling function `f`.** Its
  statement is `H[f ∘ X ; μ] = H[X ; μ]` with `f` an explicit argument, and the goals in
  this development have a *joint variable* (`N.jointOn (↑s)`, `L.jointStrictAbove _`) where
  the `f ∘ X` should be — higher-order unification will not solve for `f`. The pattern that
  works throughout `ChainRule.lean` and `Examples.lean` is: `set f : … := … with hf`, prove
  `Function.Injective f` separately, then use the lemma **backwards** inside a `have`
  (`(entropy_comp_of_injective N.P hmeas f hinj).symm`) and let defeq do the matching.
  Mathlib's own uses (`entropy_comm`, `entropy_assoc`) open with a `change H[f ∘ X ; μ] = …`
  for the same reason. The conditional form
  `ProbabilityTheory.condEntropy_comp_of_injective` additionally needs the conditioning
  variable by name — `(Y := N.jointOn W)` — or it picks the wrong one.
- **Extending a partial order to a *strict* linear one: Mathlib gives you the reflexive
  form, and the rest is hand-rolled.** `extend_partialOrder p` (`Mathlib.Order.Extension.Linear`)
  returns `⟨s, IsLinearOrder α s, ∀ a b, p a b → s a b⟩`. The chain-rule induction needs an
  irreflexive order (it peels off a greatest element and needs `{C | r C A}` to exclude `A`),
  so `Condensation.exists_strictTotalOrder_ext` takes `r a b := s a b ∧ a ≠ b` and registers
  the classes by hand, in this order: `Std.Irrefl`, `IsTrans`, `Std.Trichotomous`, then
  `IsStrictOrder α r := {}` and `IsStrictTotalOrder α r := {}` — the last two are structure
  instances synthesised from the first three and are written as literal empty anonymous
  constructors. Transitivity and trichotomy are proved as plain `∀`-statements first
  (`htrans`, `htri`) and fed in; `antisymm_of s`, `trans_of s`, `total_of s` are the
  accessors for the reflexive order's own classes. To build a *specific* extension, feed
  `exists_strictTotalOrder_ext` a `p` you have proved `IsPartialOrder` for — that is how
  `exists_revIncl_strictTotalOrder` (reverse inclusion) and
  `exists_revIncl_strictTotalOrder_incomparable_first` (the paper's `⪯ₚ`,
  `C ≤ B ∨ (B ∈ incomparable A ∧ C ≤ A)`) are built.
- **Half of the `Is*` order classes are deprecated aliases of `Std.*` at this pin, and the
  new ones take the relation only.** `IsIrrefl α r`, `IsRefl`, `IsSymm`, `IsAsymm`,
  `IsAntisymm`, `IsTotal`, `IsTrichotomous` are `@[deprecated]` `abbrev`s for `Std.Irrefl r`,
  `Std.Refl r`, `Std.Symm r`, `Std.Asymm r`, `Std.Antisymm r`, `Std.Total r`,
  `Std.Trichotomous r` (`Mathlib/Order/Defs/Unbundled.lean`, deprecations dated 2025-12 to
  2026-03). Note the **arity change**: the `Std` classes take only `r`, the old ones took
  `α` as well. But `IsTrans α r`, `IsStrictOrder α r`, `IsPartialOrder α r`,
  `IsLinearOrder α r`, `IsStrictTotalOrder α r` are *not* deprecated and still take `α`, so
  a single `haveI` block legitimately mixes the two shapes — `ChainRule.lean`'s
  `exists_strictTotalOrder_ext` does. Do not "normalise" one way or the other.
- **`tfae_have` syntax at this pin is `tfae_have i → j := proof`.** The goal is stated as an
  implication between numbered clauses and *assigned* with `:=`, taking either a term or a
  `by` block; there is no name and no colon. `LatentModel.perfect_tfae_A` is the worked
  example (`tfae_have 1 → 3 := by …`, `tfae_have 3 → 2 := fun h => …`,
  `tfae_have 2 → 1 := by …`, then `tfae_finish`). Copy that shape rather than the older
  spellings you will find in tutorials and pre-2025 mathlib (`tfae_have h : 1 → 3`, or a
  bare `tfae_have 1 → 3` followed by a tactic block); those are the pre-rename syntax, and
  nothing in this repo uses them.
- **`Finset.set_biInter_insert` lives in `Mathlib/Order/CompleteLattice/Finset.lean`, which
  is why grepping `Data/Finset` and `Data/Set/Lattice` for it finds nothing.** It is
  `⋂ x ∈ insert a s, t x = t a ∩ ⋂ x ∈ s, t x` for `s : Finset α`, needs `[DecidableEq α]`,
  and is **not** `@[simp]`; the `Set`-indexed cousin is `Set.biInter_insert`, and the
  degenerate case is `Finset.set_biInter_singleton`. There is **no `set_biInter_cons`**, so
  an induction run with `Finset.Nonempty.cons_induction` (which is what you want when the
  base case must be a nonempty singleton) has to close the corresponding step by
  `ext B; simp [Set.mem_iInter, Finset.mem_cons]` instead — `aeFunctionOf_jointAbove_aux`
  in `Comparison.lean` does exactly that, while `ChainRule.lean`'s
  `iIndepFun_of_entropy_jointOn_eq_sum` uses the `insert` lemma directly.
- **A mathlib lemma you cannot find by its additive name may exist only under its
  multiplicative one.** `Summable.le_tsum` (used in `Probability.lean`'s
  `aeFunctionOf_of_condEntropy_eq_zero`, as `hsummable.le_tsum x fun j _ ↦ hnonneg j`) does
  **not** appear anywhere in mathlib's source: it is generated by `@[to_additive]` from
  `Multipliable.le_tprod` in `Mathlib/Topology/Algebra/InfiniteSum/Order.lean`. A plain
  `grep -r le_tsum .lake/packages/mathlib` returns nothing and reads like "the lemma does
  not exist". The general rule: for anything about `∑`/`∑'`/`+`/`0`/`≤`, grep the
  *multiplicative* spelling too (`tprod`, `prod`, `mul`, `one`), or skip grep and use
  `exact?`/`loogle`, which see the generated declarations. This is the same failure mode as
  the "Mathlib lacks X" comments recorded above: a grep that comes back empty is weak
  evidence, and it should be written down as *which search you ran*, not as a conclusion.
- **Two parallel provers will write the same helper, and the collision is a hard error at
  import time, not an ambiguity.** Two M2 shards independently wrote
  `Condensation.AEFunctionOf.congr_right` — one into `Comparison.lean`, one into
  `Quantitative.lean`. Neither file imports the other, so each compiled clean in isolation
  and nothing complained until a module downstream of both was elaborated. The same shape
  bit again mid-relocation, when a helper had been copied into its new home but not yet
  deleted from its old one:
  `error: import Condensation.Comparison failed, environment already contains 'Condensation.AEFunctionOf.congr_left' from Condensation.Probability`.
  Two lessons. Lean does **not** resolve this by shadowing or ambiguity — the import fails
  outright. And the error surfaces in whatever runs first over the *whole* import closure,
  which here was `scripts/check_sorry_ledger.py`, so it reads like a gate malfunction rather
  than a duplicate declaration. When integrating parallel shards, grep every new declaration
  name across all of `Condensation/` before building, and when relocating a helper delete
  **every** copy, not just the one you were looking at.
- **Re-derive every count in prose from the checker scripts; never copy one out of README,
  KNOWLEDGE or a module docstring.** Every M2 shard left the shared counts stale — `sorry`
  counts, node-coverage counts, "staged in CONDENSATION-PENDING" claims and inventory
  numbers — because each was true when its file was written and false by the time the wave
  landed. The two commands are `python3 scripts/check_sorry_ledger.py` (needs the oleans, so
  build first) and `python3 scripts/check-condensation-nodes.py` (pure text, always safe to
  run). This whole reconciliation pass exists because those numbers were copied rather than
  re-derived. The same applies to a *file's own* module docstring — a status paragraph
  written mid-shard is a snapshot, not a fact. One survivor was found and fixed in this
  pass — `Perfect.lean`'s Proposition 4.10 docstring credited the retired `dd:finite-range`
  for its finiteness, which actually comes from Definition 3.1's `Ω`-clause via
  `RVModel.finiteEntropyOf`. Grep for `dd:finite-range` in docstrings before trusting any
  claim about where a finiteness hypothesis comes from.
- **`notes/paper-errata.md` has a documented headline shape; entry 15 arrived violating it
  and was reformatted in the M2 close-out.** The file's preamble requires
  `N. **headline naming the node**` with the body indented as list continuation; entry 15
  landed as a Markdown heading (`## 15. Lemma 4.14 as printed is false`). Copy entry 14's
  shape.

  **But do not repeat the reasoning that flagged it.** Two independent agents inferred that
  the malformed headline would "fail to attach on the generated page". It would not, and
  neither does a well-formed one: `scripts/gen-trust-surface.py` calls
  `cartesian_frames_errata(cf_paper)` with `PAPERS['cartesian-frames']` **only**, so no
  other paper's errata file is parsed for headlines at all — Condensation's is an input to
  the staleness hash and nothing more. Two further reasons it could not work as assumed:
  the node-id regex accepts only `Definition|Claim|Theorem` (not `Lemma`, `Proposition`,
  `Corollary` or `Example`), and it captures `([0-9]+)`, so Condensation's dotted numbering
  would key `Lemma 4.14` as `Theorem 4` at best. The headline shape is a *forward-looking
  convention* the preamble asks for against a future Condensation-specific reader, not a
  live wiring. Wiring it up is a real piece of work on the generator, not a formatting fix.
