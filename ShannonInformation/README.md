# `ShannonInformation` — FAF's shared Shannon-information layer

Reusable, paper-neutral infrastructure: entropy, conditional entropy, mutual information
and conditional mutual information, available to any FAF formalization through **one
stable import**.

```lean
import ShannonInformation.API
```

This is **not** a paper formalization. It is deliberately absent from
`scripts/papers.py`'s `PAPERS` registry and listed in `NON_PAPER_LIBRARIES` instead,
alongside `ProvabilityLogic`, the repository's other vendored dependency.

## Purpose

FAF's pinned Mathlib has no Shannon information theory at all —
`Mathlib/InformationTheory/` is `Coding`, `Hamming` and `KullbackLeibler`, and the only
`entropy` in the library is *topological* entropy in `Dynamics/`. Several
agent-foundations papers of interest are written entirely in the missing vocabulary. Rather
than each such formalization re-deriving entropy (or, worse, axiomatizing it), FAF
consumes one pinned, audited, kernel-checked implementation.

**FAF has not re-formalized Shannon information theory.** The mathematics here is the
[PFR project](https://github.com/teorth/pfr)'s (Tao et al.), vendored under Apache-2.0 at
commit `01c9b666945eaf73b3f7d8b20ffe003f8640e630`. What FAF contributes is the vendoring,
two compatibility patches, this consumer surface, the scope analysis, the tests, and one
FAF-authored generalization layer that restates part of the vendored corpus under a weaker
finiteness hypothesis — inventoried below, and no new definitions.

## The two layers, and why they are separate

| layer | path | what it is |
| --- | --- | --- |
| **vendor** | `PFR/` | audited upstream implementation, at upstream module paths. Third-party. Do not edit. |
| **consumer** | `ShannonInformation/API.lean` | the FAF-facing surface. What downstream work imports. |
| **FAF-authored** | `ShannonInformation/FiniteEntropy/` | the one place in this layer where the mathematics is ours. Re-exported by `API.lean`. |

A downstream paper formalization should import `ShannonInformation.API` and **never name a
`PFR.*` module**. The point of the split is that re-pinning the vendored tree — a routine
maintenance event — must not ripple through paper libraries.

The API adds **no entropy definitions**: every information quantity a client reads through
it is upstream's verbatim, so an API statement cannot drift from the statement that was
actually proved, and nothing has to be re-audited when the vendor tree moves.

It is no longer *empty of mathematics*, though. `ShannonInformation/FiniteEntropy/` is
FAF-authored: it adds a **hypothesis class** and theorems restated at it, but still no
definitions — see "Currently FAF-authored" below and `SCOPE.md`. Any further genuinely
generic convenience lemma needed
by more than one client belongs in this namespace under the same conditions: proved, never
`sorry`ed, listed here, and covered by `AxiomAudit.lean`.

## Currently FAF-authored declarations in the API

All in namespace `ShannonInformation`; all proved, `sorry`-free, and asserted axiom-clean in
`ShannonInformation/AxiomAudit.lean`. They exist to lift the vendored library out of its
`FiniteRange` fragment (`SCOPE.md` §2, §4, §5); Phases 1–4a of
`Condensation/notes/finite-range-generalization-plan.md`.

`ShannonInformation/FiniteEntropy/Summable.lean` — the abstract nonnegative-family core. No
measure theory; statements are about a family `p : ι → ℝ`.

| declaration | statement |
| --- | --- |
| `negMulLog_tsum_le` | grouping bound `negMulLog (∑' t, p t) ≤ ∑' t, negMulLog (p t)` |
| `negMulLog_div` | `negMulLog (p / P)` split into unnormalised term plus normalisation |
| `tsum_negMulLog_eq_add` | local chain rule for one row of a joint distribution |
| `tsum_mul_log_div_nonneg` | Gibbs' inequality, countable form (termwise, no Jensen) |
| `negMulLog_le_add_of_le` | the termwise pair bound |
| `summable_tsum_fiber`, `tsum_tsum_fiber` | regrouping a summable family along `g : ι → κ` |
| `summable_negMulLog_tsum_fiber` | grouping preserves finite entropy |
| `tsum_negMulLog_tsum_fiber_le` | `H[g ∘ X] ≤ H[X]` in atomic form |

`ShannonInformation/FiniteEntropy/Defs.lean` — the class and its closure.

| declaration | statement |
| --- | --- |
| `FiniteEntropyMeasure` | class: the series defining `Hm[μ]` converges (`measureEntropy`'s summand verbatim) |
| `FiniteEntropyOf X μ` | abbreviation for `FiniteEntropyMeasure (μ.map X)` |
| `FiniteEntropyMeasure.summable_real`, `.of_summable_real`, `finiteEntropyMeasure_iff` | unfolding, for a probability measure |
| `FiniteEntropyOf.summable` | the series PFR's `entropy_eq_sum` writes `H[X ; μ]` as converges |
| `finiteEntropy_of_finiteSupport` | **instance** `FiniteSupport μ → FiniteEntropyMeasure μ` |
| `finiteEntropy_of_finiteRange` | **instance** `FiniteRange X → FiniteEntropyOf X μ` |
| `summable_measureReal_singleton`, `tsum_measureReal_singleton_le_one`, `measureReal_singleton_le_one` | point-mass bookkeeping |
| `measureReal_map_singleton_eq_tsum_fiber`, `measureReal_map_fst_singleton`, `measureReal_map_snd_singleton` | point masses of a pushforward / of a marginal |
| `finiteEntropyMeasure_map` | pushforward closure — the workhorse |
| `finiteEntropyMeasure_prod`, `finiteEntropyOf_pair` | pair closure |
| `finiteEntropyOf_comp`, `finiteEntropyOf_fst`, `finiteEntropyOf_snd` | function of a variable; marginals of a pair |
| `finiteEntropyOf_pullback` | transport along a measure-preserving map |

`ShannonInformation/FiniteEntropy/Pi.lean` — the finite-product closure.

| declaration | statement |
| --- | --- |
| `finiteEntropyOf_measurableEquiv` | transport along a measurable equivalence of the value type |
| `finiteEntropyOf_piFin` | `Fin n`-indexed dependent product closure |
| `finiteEntropyOf_pi` | the same for any `Fintype` index |

`ShannonInformation/FiniteEntropy/ChainRule.lean` — Phase 2. `H[⟨X, Y⟩] = H[Y] + H[X | Y]`
and friends, proved with no kernel layer. The hard part is *deriving* Bochner integrability
of `y ↦ H[X | Y ← y]` rather than assuming it; Lean's integral is `0` on a non-integrable
integrand, so an assumed-integrability statement could be silently vacuous.

| declaration | statement |
| --- | --- |
| `integrable_of_summable_measureReal_mul_norm` | on a countable space, `Summable fun s ↦ μ.real {s} * ‖f s‖` gives `Integrable f μ` |
| `map_cond_measureReal_singleton` | `((μ[\|Y ← y]).map X).real {x} = (μ.map ⟨Y, X⟩).real {(y, x)} / (μ.map Y).real {y}` |
| `measureReal_mul_entropy_cond` | the fibre identity: `(μ.map Y).real {y} * H[X \| Y ← y]` is the `y`-row of the joint entropy series minus `negMulLog ((μ.map Y).real {y})` |
| `summable_measureReal_mul_entropy_cond` | `Summable fun y ↦ (μ.map Y).real {y} * H[X \| Y ← y]` |
| `integrable_entropy_cond` | `Integrable (fun y ↦ H[X \| Y ← y ; μ]) (μ.map Y)` — derived, never a hypothesis |
| `condEntropy_eq_tsum` | `H[X \| Y] = ∑' y, (μ.map Y).real {y} * H[X \| Y ← y]` (PFR's `condEntropy_eq_sum` is a `Finset` sum) |
| `chain_rule''` | `H[X \| Y] = H[⟨X, Y⟩] - H[Y]` |
| `chain_rule` | `H[⟨X, Y⟩] = H[Y] + H[X \| Y]` |
| `chain_rule'` | `H[⟨X, Y⟩] = H[X] + H[Y \| X]` |
| `condEntropy_eq_entropy_pair_sub` | `H[X \| Y] = H[⟨X, Y⟩] - H[Y]`, spelled as PFR spells the corollary |
| `cond_chain_rule'` | `H[⟨X, Y⟩ \| Z] = H[X \| Z] + H[Y \| ⟨X, Z⟩]` |
| `cond_chain_rule` | `H[⟨X, Y⟩ \| Z] = H[Y \| Z] + H[X \| ⟨Y, Z⟩]` |
| `condMutualInfo_eq` | `I[X : Y \| Z] = H[X \| Z] + H[Y \| Z] - H[⟨X, Y⟩ \| Z]` (added in Phase 4a; needs `FiniteEntropyOf` on all three variables — see below) |

`ShannonInformation/FiniteEntropy/Inequalities.lean` — Phase 3. Subadditivity,
mutual-information nonnegativity and the independence equality case, all obtained by summing
one termwise inequality (Phase 1's `negMulLog_le_add_of_le`) and reading its gap three ways.
The file goes abstract → law → random variable.

| declaration | statement |
| --- | --- |
| `tsum_negMulLog_prod_le` | abstract subadditivity: `∑' q, negMulLog (r q) ≤ (∑' x, negMulLog (a x)) + ∑' y, negMulLog (b y)` for the marginals `a`, `b` of `r` |
| `tsum_negMulLog_prod_eq_add_iff` | abstract equality case: equality iff `r` is the product of its marginals |
| `measureEntropy_prod_le_add` | `Hm[ρ] ≤ Hm[ρ.map Prod.fst] + Hm[ρ.map Prod.snd]` |
| `measureEntropy_prod_eq_add_iff` | equality iff `ρ = (ρ.map Prod.fst).prod (ρ.map Prod.snd)` |
| `finiteEntropyMeasure_zero` | `FiniteEntropyMeasure (0 : Measure S)` |
| `measureReal_map_cond_singleton` | `((μ[\|Z ⁻¹' {z}]).map X).real {x} = μ.real (X ⁻¹' {x} ∩ Z ⁻¹' {z}) / μ.real (Z ⁻¹' {z})` |
| `finiteEntropyOf_cond` | conditioning on an event keeps a variable inside the class |
| `entropy_pair_le_add` | `H[⟨X, Y⟩] ≤ H[X] + H[Y]` |
| `mutualInfo_nonneg` | `0 ≤ I[X : Y]` |
| `mutualInfo_eq_zero` | `I[X : Y] = 0 ↔ IndepFun X Y μ` |
| `entropy_pair_eq_add` | `H[⟨X, Y⟩] = H[X] + H[Y] ↔ IndepFun X Y μ` |
| `condMutualInfo_nonneg` | `0 ≤ I[X : Y \| Z]` |
| `condEntropy_le_entropy` | `H[X \| Y] ≤ H[X]` |
| `condEntropy_pair_le_add` | `H[⟨X, Y⟩ \| Z] ≤ H[X \| Z] + H[Y \| Z]` |
| `entropy_submodular` | `H[X \| ⟨Y, Z⟩] ≤ H[X \| Z]` |
| `entropy_triple_add_entropy_le` | `H[⟨X, ⟨Y, Z⟩⟩] + H[Z] ≤ H[⟨X, Z⟩] + H[⟨Y, Z⟩]` |
| `condMutualInfo_eq_zero` | `I[X : Y \| Z] = 0 ↔ CondIndepFun X Y Z μ` |

`ShannonInformation/FiniteEntropy/Derived.lean` — Phase 4a. Every proof is a rewrite chain
over the two modules above; there is no new mathematics in it.

| declaration | statement |
| --- | --- |
| `entropy_comp_le` | `H[f ∘ X] ≤ H[X]` |
| `entropy_of_comp_eq_of_comp` | `Y = f ∘ X` and `X = g ∘ Y` give `H[X] = H[Y]` |
| `condEntropy_comp_self` | `H[X \| f ∘ X] = H[X] - H[f ∘ X]` |
| `condEntropy_of_injective'` | `H[X \| f ∘ Y] = H[X \| Y]` for injective `f` |
| `mutualInfo_eq_entropy_sub_condEntropy` | `I[X : Y] = H[X] - H[X \| Y]` |
| `mutualInfo_eq_entropy_sub_condEntropy'` | `I[X : Y] = H[Y] - H[Y \| X]` |
| `condEntropy_comp_ge` | `H[Y \| f ∘ X] ≥ H[Y \| X]` |
| `mutual_comp_le` | `I[f ∘ X : Y] ≤ I[X : Y]` |
| `condMutualInfo_eq'` | `I[X : Y \| Z] = H[X \| Z] - H[X \| ⟨Y, Z⟩]` |
| `IdentDistrib.condEntropy_eq` | equal joint laws give `H[X \| Y ; μ] = H[X' \| Y' ; μ']` (not reachable by dot notation — see below) |

Two things about the boundary. The vendored *theorems* are no longer `FiniteRange`-only:
the chain rules, subadditivity, the independence characterizations and the derived corpus
above have all been restated at `FiniteEntropyOf`. What has **not** moved is the tail listed
in `FiniteEntropy/Derived.lean`'s header — `ent_of_cond_indep`, `mutualInfo_const`,
`const_of_nonpos_entropy`, `condEntropy_of_injective`,
`condMutualInfo_of_inj`/`_of_inj'`/`_of_inj_map`, `mutual_comp_comp_le`,
`condMutual_comp_comp_le`, `IndepFun.condEntropy_eq_entropy` — left `FiniteRange`-gated
because no consumer has asked for them, not because they are hard. And the product closure
is still stated for a **finite** index only: countable products genuinely fail (independent
`X n` with `H[X n] = 1` each are finite-entropy, their joint over `ℕ` is not), so nobody
should "generalize" it to `Π i : ι` for countable `ι`.

The non-vacuity witness — a geometric variable on `ℕ`, which has `FiniteEntropyOf` and
provably no `FiniteRange` — is in `APITests/ShannonInformationFiniteEntropy.lean`,
constructed rather than asserted, per the repository standard. The Phase 2, 3 and 4a
endpoints are exercised from outside the layer in
`APITests/ShannonInformationChainRule.lean`,
`APITests/ShannonInformationInequalities.lean` and
`APITests/ShannonInformationDerived.lean`, the last of which also carries a worked
disambiguation idiom for the shadowing hazard below.

### Citing across the two surfaces

Every `ShannonInformation.*` name in the three tables above **shadows** a same-named
`ProbabilityTheory.*` declaration — the `FiniteRange` version of the same fact.
`ShannonInformation/API.lean`'s "which version to cite" table is the canonical record; in
summary:

- **Ambiguity is resolved by elaboration success, not by the enclosing namespace.** A bare
  `condMutualInfo_eq` can silently pick PFR's version even inside
  `namespace ShannonInformation`, and then fail with `failed to synthesize FiniteRange Z`.
  Write the fully qualified name whenever both surfaces are in scope. This is not
  hypothetical; it happened while the layer was being written.
- **Dot notation does not reach `ShannonInformation.IdentDistrib.condEntropy_eq`**:
  `h.condEntropy_eq` resolves in the head symbol's namespace, `ProbabilityTheory`, so it
  always finds PFR's version. Spell ours in full.
- **The argument lists differ.** The FAF versions were written to their own proofs'
  convenience, so `μ` is not always in the same place or of the same explicitness:
  `ProbabilityTheory.entropy_pair_le_add hX hY μ` versus
  `ShannonInformation.entropy_pair_le_add hX hY` (`μ` implicit);
  `ProbabilityTheory.condEntropy_le_entropy μ hX hY` versus
  `ShannonInformation.condEntropy_le_entropy hX hY`. And
  `ShannonInformation.condMutualInfo_eq_zero` takes an extra `hZ : Measurable Z` that the
  vendored one does not. Swapping namespaces is a namespace swap *plus* an argument fix.

Two hypothesis differences run the other way, and are recorded rather than left to be
discovered. `ProbabilityTheory.mutualInfo_nonneg`, `.entropy_pair_le_add` and
`.condMutualInfo_nonneg` carry **no** measure hypothesis at all — they route through
`measureMutualInfo_nonneg`, which normalises internally — while ours require
`[IsZeroOrProbabilityMeasure μ]`. And `ShannonInformation.condMutualInfo_eq` requires
`FiniteEntropyOf` on all three of `X`, `Y`, `Z`, where `ProbabilityTheory.condMutualInfo_eq`
requires `FiniteRange` only on `Z`, because PFR's kernel route reads all three conditional
entropies off one `condDistrib` while ours splits the defining Bochner integral. Those are
the two places a `FiniteRange` client loses generality by switching.

## Supported concepts

| concept | declaration | notation |
| --- | --- | --- |
| entropy | `ProbabilityTheory.entropy` | `H[X ; μ]`, `H[X]` |
| conditional entropy | `ProbabilityTheory.condEntropy` | `H[X \| Y ; μ]` |
| mutual information | `ProbabilityTheory.mutualInfo` | `I[X : Y ; μ]` |
| conditional mutual information | `ProbabilityTheory.condMutualInfo` | `I[X : Y \| Z ; μ]` |
| measure entropy | `ProbabilityTheory.measureEntropy` | `Hm[μ]` |
| finite-range variables | `FiniteRange` | — |
| finite-entropy variables | `ShannonInformation.FiniteEntropyOf` | — |
| conditional independence | `ProbabilityTheory.CondIndepFun` | — |

Available families: chain rules (`chain_rule`, `cond_chain_rule`, …), nonnegativity
(`entropy_nonneg`, `mutualInfo_nonneg`, `condMutualInfo_nonneg`, …), independence and
conditional-independence characterizations (`mutualInfo_eq_zero`,
`condMutualInfo_eq_zero`, `entropy_pair_eq_add`), identically-distributed invariance
(`IdentDistrib.entropy_congr`, `IdentDistrib.mutualInfo_eq`, …), entropy under maps
(`entropy_comp_le`, `entropy_comp_of_injective`, `condEntropy_comp_self`), and
submodularity (`entropy_submodular`, `entropy_triple_add_entropy_le`).

**Most of those names exist twice**, and choosing between them is the first decision a
client makes: the vendored `ProbabilityTheory.*` statement at `[FiniteRange X]`, and the
FAF `ShannonInformation.*` statement at `[FiniteEntropyOf X μ]`, which is strictly weaker.
Not every vendored theorem has been restated — see "Citing across the two surfaces" above
for the hazards and `ShannonInformation/API.lean`'s "which version to cite" table for the
name-by-name mapping.

`ShannonInformation/API.lean` carries the full inventory in its module docstring.

## Scope restrictions — read before relying on a statement

**`ShannonInformation/SCOPE.md` is required reading.** In one line:

> The definitions are correct for countable-discrete variables. The *vendored* theorems are
> proved only for **finite-range** ones (`FiniteRange X : (Set.range X).Finite`); FAF has
> restated the load-bearing ones at `FiniteEntropyOf`, which is strictly weaker, but not
> all of them.

`FiniteRange` is a genuine mathematical restriction, not a typeclass artefact, and it is
narrower than the "countable discrete with finite entropy" setting some source papers
assume — which is why the restatement exists. `SCOPE.md` records exactly which theorems
needed it, which survive without it, which are now available at `FiniteEntropyOf` and which
were left behind, and one sharp trap (`∑'` is `0` on non-summable families, so `H[X]` for
an infinite-entropy variable is silently `0`).

## Vendoring and update policy

Provenance, the derived module closure, and both patches: `vendor/PROVENANCE.md`.
Attribution and modification notice: `vendor/NOTICE.md`. Licence: `vendor/LICENSE-PFR`.

```sh
ShannonInformation/vendor/vendor-pfr.sh            # regenerate PFR/ from upstream + patches
ShannonInformation/vendor/vendor-pfr.sh --verify   # audit: must report IDENTICAL
```

The closure is **derived** by walking imports (`vendor/closure.py`), not hand-picked. That
is what keeps PFR's additive-combinatorics machinery out: it is simply unreachable from
entropy. `vendor/EXTERNAL-IMPORTS.txt` records every non-PFR import — all `Mathlib.*`; an
entry from `AddCombi` or another PFR dependency would be a regression.

When bumping upstream, classify every new breakage as *compatibility* (→ a new numbered
patch with justification) or *mathematics* (→ take it upstream, do not carry it here), and
re-check `SCOPE.md`, since a newer upstream may have relaxed hypotheses.

## Trust surface

- `sorry`-free, and no new `axiom` declarations. The vendored closure contains no `sorry`.
- `ShannonInformation/AxiomAudit.lean` asserts axiom-cleanliness on representative public
  endpoints, and is built by default. It is deliberately **separate** from the repository's
  top-level `AxiomAudit.lean`: that file is the *paper* endpoint inventory, keyed to
  `Paper node:` annotations and per-paper regeneration procedures, and a non-paper library
  has no place in it. The enforcement is the same; the bookkeeping is kept where it belongs.
- Distinguish carefully when reading: **mathematics inherited from PFR** (all of `PFR/`),
  **compatibility patches** (two, in `vendor/patches/`), **new FAF lemmas** (all of
  `ShannonInformation/FiniteEntropy/`, inventoried above), and **what is still only
  desired** — the not-restated tail named above, and the consumer migration (Phase 4b of
  `Condensation/notes/finite-range-generalization-plan.md`: `Condensation`'s `RVModel` still
  carries a `FiniteRange` field). `SCOPE.md` §5 records the outcome and the cost.

## Known constraint: do not `import Mathlib` alongside this

A file that imports **all** of Mathlib and this layer fails to elaborate:

```
import PFR.Mathlib.Probability.IdentDistrib failed, environment already contains
'ProbabilityTheory.IdentDistrib.prodMk' from Mathlib.Probability.IdentDistribIndep
```

PFR's `Mathlib/` shim modules re-declare lemmas that FAF's newer Mathlib pin has since
acquired upstream. Targeted imports (`import Mathlib.Data.Finset.Basic`, …) are fine, and
`APITests/ShannonInformation.lean` is unaffected because it imports only the API — but a
downstream library whose first line is `import Mathlib` will hit this.

Workaround: import the specific Mathlib modules you need. Possible real fix, not attempted
here: a third vendor patch deleting the now-redundant shim declarations. Whoever does that
must classify it as compatibility, not mathematics, and record it in `vendor/patches/`.

## How a future paper formalization should depend on this

1. `import ShannonInformation.API`, and nothing from `PFR.*`. Do not `import Mathlib` in the
   same file — see the constraint above.
2. Read `SCOPE.md` first and decide, explicitly, which surface the paper's statements live
   on: `FiniteRange` if the vendored theorems suffice, `FiniteEntropyOf` if the paper says
   "countable discrete with finite entropy" and means it. Either way disclose the choice as
   a modeling decision in the paper's own README — do not let a reader infer it from a
   `variable` block. Check §4's table before assuming a particular theorem is available at
   `FiniteEntropyOf`; not all of them are.
3. Do not define entropy, conditional entropy, mutual information or conditional mutual
   information. If a needed fact is missing, prefer proving it in the paper library from
   re-exported endpoints; promote it here only when a second client needs it.
4. Client-style examples of exactly this live in `APITests/ShannonInformation.lean`, and
   for the finite-entropy layer in `APITests/ShannonInformationFiniteEntropy.lean`,
   `…ChainRule.lean`, `…Inequalities.lean` and `…Derived.lean`.

## Motivation, and what this is not

The infrastructure was motivated by a feasibility spike for **Condensation** (Eisenstat),
and is relevant to **Natural Latents** (Wentworth–Lorell) — which has since been assessed
and does **not** fit inside the finite-range fragment as written, though its computed
examples do; see `SCOPE.md` §6. Neither paper is a dependency of this layer, neither is formalized here, and
no declaration from either appears anywhere in it. This is shared substrate; the papers are
separate work.
