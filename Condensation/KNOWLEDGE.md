# Condensation — knowledge base

Institutional memory for this formalization: settled design decisions, the
correspondence table, intentional deviations, paper errata, and pitfalls. Committed on
purpose — a future session (or auditor) reads this before touching the library. See
`README.md` for the trust surface, `notes/roadmap.md` for the plan and the `dd:` glossary
in full, and `Condensation.lean` for the glossary as shipped.

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
| Def 3.1 random variable model | `Condensation.RVModel (I : Type w) [Finite I]` | `dd:bundled-model`, `dd:finite-range`; `[Finite I]` is Def 3.1's "finite family", a class parameter of the structure (R1-F01 etc.) |
| Def 3.2 latent variable model | `Condensation.LatentModel` | |
| Def 3.3 σ_L, χ_L, ϱ_L | `LatentModel.simpleScore`, `.condScore`, `.reconScore` | |
| Def 3.4 `X_A`, `Y_F`, `Y_∩A`, `Y_⊇A`, `Y_⊋A`, `Y_∋i` | `RVModel.joint`, `LatentModel.jointOn`, `LatentModel.jointContrib`, `.jointAbove`, `.jointStrictAbove`, `.jointContribIdx` | the carriers are the **joint variables**; `RVModel.jointOn` is the machinery `LatentModel.jointOn` is built from and carries no node |
| Def 3.4 index families `{B : B ∩ A ≠ ∅}`, `{B : A ⊆ B}`, `{B : A ⊊ B}`, `{B : i ∈ B}` | `Condensation.contrib`, `.above`, `.strictAbove`, `.contribIdx` | *auxiliaries*: subsets of `P⁺I`, not random variables. They index the joint variables above; annotating them would claim (3.5)–(3.8) for a set rather than for the variable the equations define (R1-F26) |
| Def 3.5 morphism `(π, ι, (f_j))` | `Condensation.RVModel.Hom` | fields `π`, `π_pres`, `ι`, `f`, `eq_ae`; **no** measurability field for `f` — the paper's own remark is that it is automatic on countable discrete ranges (`Hom.measurable_f`). `ι : J → I` runs target → source. `dd:category` |
| Def 3.6 composite (3.13), identity (3.16) | `RVModel.Hom.comp`, `RVModel.Hom.id` | index maps compose the other way round |
| Prop 3.7 category | `Condensation.RVModelObj.instCategory` | objects are `RVModelObj`, which carries its index type as a **field** (a morphism may change it); (3.17)–(3.20) hold by `rfl` |
| Prop 3.8 iso characterization | `RVModel.Hom.isIso_iff` | uses `CategoryTheory.IsIso`; "isomorphism of measurable spaces" is `RVModel.Hom.IsMeasurableIso` |
| Def 3.9 a.e.-equal morphisms | `RVModel.Hom.AEEq` (+ `Hom.instSetoid`) | |
| Def 3.10 equivalence | `RVModel.IsEquivalence` (the pair), `RVModel.Equivalent` (the ∃) | the "laid out" characterization is `RVModel.Hom.ofSameIndex` + `RVModel.isEquivalence_ofSameIndex_iff`; Prop 4.7 consumes exactly that shape |
| Prop 3.11 congruence | `RVModel.Hom.aeEq_equivalence`, `RVModel.Hom.comp_aeEq_congr` | |
| Prop 3.12 equivalence relation | `RVModelObj.equivalent_equivalence` | over `RVModelObj.Equivalent`; the universe-polymorphic `RVModel.Equivalent.refl/symm/trans` are the pieces |
| Ex 4.1 `L₁`, `L₂` | `Condensation.Example41.L₁`, `.L₂` (+ `L₁RV`, `L₂RV`) | guarded-subtype encoding of "let `Y_A` be constant"; (4.2)–(4.5) are `L₁_simpleScore`, `L₁_condScore`, `L₂_simpleScore`, `L₂_condScore`, un-annotated and `sorry` at M1. (4.4)/(4.5) take `A.Nonempty` (errata 11) and name `X_I` as `RVModel.jointAll` |
| Prop 4.2 (4.6) | `LatentModel.simpleScore_ge_condScore`, `.condScore_ge_entropy_jointContrib`, `.entropy_jointContrib_ge_entropy_joint` | three separate inequalities; the middle one is `sorry` (needs the finite-family chain rule) |
| Def 4.3 perfect / simply-perfect | `LatentModel.PerfectlyCondenses`, `.SimplyPerfectlyCondenses` | quantified over `Finset I`, not `PPlus I` — nothing degenerates at `A = ∅` |
| Lemma 4.5 | `LatentModel.perfect_entropy_iff_aeFunctionOf` | proved |
| Cor 4.6 | `LatentModel.aeFunctionOf_of_perfectlyCondenses` | proved, but *depends on* Prop 4.2's `sorry` |
| Ex 4.4 | `Condensation.Example44.M44`, `.L44` | `X_i := Y_∋i`; this is why latent universes are unpinned |
| Prop 4.7 | `LatentModel.aeFunctionOf_iff_isEquivalence_contribModel` | the two models it compares are `LatentModel.pullbackModel` (`(Λ, (X_i))`) and `LatentModel.contribModel` (`(Λ, (Y_∩{i}))`); clause (2) is `RVModel.IsEquivalence` of two `Hom.ofSameIndex` triples at `π = ρ = id_Λ`. Proved |
| Def 4.8 ordered Markov | `Condensation.RVModel.OrderedMarkov` | stated over a bare `RVModel (PPlus I)`, as the paper does |
| Thm 4.9 | `LatentModel.perfect_tfae_A` (A1–A3), `.perfect_tfae_B` (B1 ⟺ B2) | both `sorry` |
| Prop 4.10 | `RVModel.orderedMarkov_iff` | "upward closed" is Mathlib's `IsUpperSet`, not a synonym; `sorry` |
| Def 4.11 amalgamation of a cospan | `Condensation.Amalgamation` | `dd:amalgamation` |
| Def 4.12 amalgamation of two latent models | `Condensation.LatentAmalgamation` | `Λ₀` primary, `lat₁`/`lat₂` derived (`.Λ` definitionally `Λ₀`); `comm` is an added field (errata 10) |
| Lemma 4.13 | `Amalgamation.canonical`, `nonempty_amalgamation`, `LatentAmalgamation.canonical`, `nonempty_latentAmalgamation` | the (4.49)–(4.53) construction; all four `sorry` at M1 (three supporting measure lemmas) |
| Lemma 4.14 | `Condensation.aeFunctionOf_of_condIndepFun` | `sorry` |
| Thm 4.15 | `Condensation.aeFunctionOf_jointAbove_of_perfectlyCondenses` | `sorry`; the induction is not in the paper (errata 5) |
| Lemma 5.4 (5.5), (5.6) | `Condensation.condEntropy_le_of_pair`, `.condEntropy_eq_of_pair` | proved; the `condInteractionInfo` symmetries `condInteractionInfo_comm/_swap/_rotate` and `condEntropy_pair_rotate` are the machinery |
| Def 5.5 polar `F°` | `Condensation.polar` | with `mem_polar_iff`, `isUpperSet_polar`, `polar_antitone`, `polar_singleton`, `polar_eq_iInter` |
| Def 5.6 intersection tree | `Condensation.ITree`, `.label`, `.intersections`, `.LabelsIn` | `dd:tree`; `ITree.leaves`, `.subtrees`, `.label_eq_polar` are the machinery |
| Prop 5.7 | `ITree.label_eq_leaves_foldr`, `Condensation.eq_decorate_of_isIntersectionTree`, `.existsUnique_intersectionTree` | over `LTree` (an arbitrary labelling of every position) and `ITree.decorate`; proved |
| Thm 5.8 (5.13), (5.14) | `Condensation.condEntropy_jointAbove_le`, `.condEntropy_jointAbove_eq` | stated over `LatentAmalgamation L₁ L₂`: `Y_⊇A` = `Am.lat₁.jointAbove`, `Z_G` = `Am.lat₂.jointOn`, `X_B` = `Am.lat₁.pullbackJoint`; the two contribution conditions are *fields*, not hypotheses. Both `sorry` |
| Cor 5.9 (5.21), (5.22) | `Condensation.condEntropy_jointAbove_le_reconScore`, `.condEntropy_jointAbove_le_reconScore_of_orderedMarkov` | both `sorry` |
| Cor 5.10 (5.24), (5.25) | `Condensation.polar_kSubsets` (proved), `.condEntropy_jointAbove_le_choose` (`sorry`) | `kSubsets` is `F`; `1 ≤ k` is required, `k > \|A\|` is allowed (errata 8) |
| auxiliary: `{B : B incomparable to A}` | `Condensation.incomparable` | in `Model.lean` beside `contrib`/`above`; no paper node, like them |
| auxiliary: "upward closed" | Mathlib `IsUpperSet` on `PPlus I` | **not** a FAF definition — an earlier local `IsUpwardClosed` in `Perfect.lean` was a synonym and is retired |

(Extend as declarations land. Every formalized node gets a row.)

## Design decisions

See the `dd:` table in `notes/roadmap.md` — `dd:finite-range`, `dd:pplus`,
`dd:bundled-model`, `dd:ae-function`, `dd:pullback`, `dd:interaction`, `dd:tree`,
`dd:category`, `dd:amalgamation`. Rationale lives there; this file records *changes* to
them and the finding IDs that forced any.

- **`dd:finite-range` generalization: costed (2026-08-17) and, by Anson's ruling the same day, a DESIRED ENDPOINT pursued in parallel with the paper** — the substrate work runs as its own thread (Phase 1 → 4 of the plan) in `ShannonInformation/FiniteEntropy/`; `dd:finite-range` stays the *current* disclosed state until the swap lands, at which point `RVModel`'s finiteness field becomes `FiniteEntropyOf` (+ Def 3.1's `Ω` finite-entropy field) and the disclosure retires. Cost: Generalizing the
  substrate to countable range + finite entropy is ~1,450–2,400 lines / 3–4.5 focused
  weeks in four phases; the abstract core (grouping bound, local chain rule, countable
  Gibbs) was proved in ~90 lines against the pinned Mathlib as calibration; nothing in the
  paper is false or different under finite range, only the model class shrinks; no upstream
  help exists (PFR master's entropy files are byte-identical to the pin, Mathlib has no
  Shannon entropy). Full plan with acceptance criteria: `notes/finite-range-generalization-plan.md`.
  Consequence for the code: the finiteness condition lives in **exactly one field of
  `RVModel`** (`finiteRange_X`, role-named, documented as the stand-in for Def 3.1's "finite
  entropy"), so a later swap to a `FiniteEntropy` class is a one-field edit plus substrate
  re-proof. It is never a hypothesis of a theorem quantifying over models
  (`RVModel`/`LatentModel`) — those get it from the structure. The §2 substrate-level lemmas
  of `Probability.lean` are stated over *bare variables*, not models, and those carry
  `FiniteRange` explicitly and legitimately: eight of them do
  (`condEntropy_comp_measurePreserving`, `interactionInfo_swap`,
  `condEntropy_eq_entropy_of_subsingleton`, `entropy_le_of_aeFunctionOf`,
  `entropy_pair_of_aeFunctionOf`, `condEntropy_eq_zero_of_aeFunctionOf`,
  `aeFunctionOf_of_condEntropy_eq_zero`, `aeFunctionOf_iff_condEntropy_eq_zero`), and the
  generalization plan's Phase 4 re-proves exactly them. Auditors: do not re-litigate the
  staging (the generalization is a desired endpoint, in progress), and do not read a `FiniteRange` binder on a §2 substrate lemma as a finding.
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
  Definition 3.5 is then just `ρₖ_pres` and `ρₖ_Y`. **`comm` is an added field** — Definition
  4.12 does not tie `π̃₁` to `π̃₂` and Theorem 4.15 needs them to agree a.e. (errata 10).
- **`dd:tree` as landed (M1).** `ITree` is an inductive binary tree with labels *computed*
  (`ITree.label`, the meet of the children's labels); `LTree` is the separate type of trees
  with a label at *every* position, which is what Proposition 5.7 quantifies over
  (`eq_decorate_of_isIntersectionTree`, `existsUnique_intersectionTree`, with
  `ITree.decorate` the computed decoration). Definition 5.6's family of intersections
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
- **`Mathlib.Order.Extension.Linear` is not in the substrate's import closure** and is
  imported explicitly by `Model.lean` for M2's benefit. `ShannonInformation.API` does not
  bring `LinearExtension`/`toLinearExtension` transitively at this pin, and the §4 tranche
  needs them; discovering that at proof time costs an import edit plus a full rebuild of
  everything downstream.
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
  nodes are real, not that every in-scope node is cited. Once the Examples 5.1–5.3 ruling
  lands, pass a `scope_manifest` (`out_of_scope`, `mathlib_rendered` = Def 2.1, Def 2.4) to
  `paper_nodes.run_node_check` as the FFS checker does.
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

- **`dd:finite-range`** (standing, type-(c) narrowing, disclosed): variables have finite
  range, not merely countable range with finite entropy; the sample space carries no
  finite-entropy hypothesis of its own. Reason: the vendored theorems are proved only in
  the finite-range fragment. Auditors: not a finding unless a *statement* is narrower than
  this decision requires.
- Examples 5.1–5.3 carry no declarations (proposed ruling; see roadmap).

## Disclosures (residual modeling substitutions)

None yet.

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

Full list (thirteen entries) with line numbers: `notes/paper-errata.md`.

## Pitfalls

- `pdftotext` emits the font's f-ligature slots as C0 bytes (`\x1c`=fi, `\x1b`=ff,
  `\x1d`=fl, `\x1e`=ffi), so `Definition` is stored as `De\x1cnition` (prints `Denition`).
  **Python's `str.splitlines()` splits on `\x1c`/`\x1d`/`\x1e`** and silently deletes all
  18 Definition headers — always `text.split("\n")` on this file (`paper_nodes.extraction_lines()`).
  Ligature-tolerant regex is `De(?:fi)?.?nition` (`De.?nition` fails on the plain spelling).
  Node headers are distinguished from line-initial cross-references only by the trailing
  period after the number/title parenthetical.
- Two `∑'`-style traps in the substrate: `H[X]` is `0` for a non-summable entropy series, and
  `condEntropy` is a Bochner integral, silently `0` when non-integrable. Under
  `dd:finite-range` neither can bite, but any generalization must carry both as proved
  consequences of its finiteness class.
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
- **`finiteRange_pi` is a lemma, not an instance.** `Condensation.finiteRange_pi` supplies
  `FiniteRange` for a dependent product of finitely many finite-range variables, which the
  vendored `FiniteRange/Defs.lean` lacks (it has the binary-product instance). It is stated
  as a `lemma` and applied explicitly (`finiteRange_pi (fun i => …)`); instance search will
  not find it. `RVModel.finiteRange_joint`/`_jointOn`/`_jointAll` are the instances built
  from it. Conversely, `FiniteRange (X ∘ f)` **is** an instance upstream, so pullbacks like
  `M.X i ∘ L.π` get finiteness for free.
- **PFR has no chain rule for a finite family, and that single gap blocks four §4
  endpoints.** The vendored library stops at the two- and three-variable forms
  (`chain_rule`, `chain_rule'`, `chain_rule''`, `cond_chain_rule`, `cond_chain_rule'`).
  Proposition 4.2's second inequality, Proposition 4.10, and both halves of Theorem 4.9 all
  run on a chain rule along a *linear extension* of the inclusion order on `P⁺I`. Budget
  them as one piece of infrastructure plus four applications, not as four independent
  proofs. The linear order itself comes from `Mathlib.Order.Extension.Linear`, imported
  explicitly by `Model.lean` (see design decisions).
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
  (`Finite I` mentions `I`, but nothing in `kSubsets`'s body needs the instance). That is
  what makes `polar_kSubsets`'s `omit [Finite I] in` legal. Do not reason about the
  inclusion rules from memory — `#check @foo` and read the actual signature.
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
  not interchangeable without that field. M2's proof of (5.13) has to use it, and will want
  an `AEFunctionOf.congr_right` (`AEFunctionOf X Y μ → Y' =ᵐ[μ] Y → AEFunctionOf X Y' μ`,
  three lines) in `Probability.lean` beside the rest of the `AEFunctionOf` API. It is
  deliberately not written yet, because an unused declaration would have to be inventoried
  for no current benefit.
- **Stale-olean trap, hit twice in the round-1 fix wave.** `lake env lean Condensation/X.lean`
  elaborates `X` against the *built* oleans of its imports, not against your edits to them.
  After editing `Probability.lean`, `lake env lean Condensation/Model.lean` reported
  `failed to synthesize Finite (PPlus I)` for an instance that was already in the source.
  Rebuild the upstream module (`safe-lake.sh build Condensation.Probability`) before
  iterating downstream.
