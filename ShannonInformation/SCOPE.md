# Scope of the shared Shannon-information layer

**Read this before relying on an entropy statement.** The vendored library is stated for a
narrower class of random variables than several prospective FAF consumers assume, and the
gap is mathematical, not cosmetic.

The short version:

> **The definitions are right for countable-discrete variables. The *vendored* theorems are
> proved only for finite-range ones.** Generalizing meant re-proving theorems under a
> summability hypothesis, not redefining anything; FAF has now done that for the
> load-bearing corpus, and §4 says exactly which theorems that is.

## Generalization: what has landed, and what has not

**Phases 1–4a of `Condensation/notes/finite-range-generalization-plan.md` have landed**
(`ShannonInformation/FiniteEntropy/`, re-exported through `ShannonInformation.API`). The
summability hypothesis §5 calls for exists as a class,
`ShannonInformation.FiniteEntropyOf X μ`, together with its instances — `FiniteRange X` and
`FiniteSupport μ` both discharge it, so nothing that was provable before stops being
provable — and its closure lemmas: marginals, functions of a variable, pairs, conditioning
on an event, and transport along a measure-preserving map. A geometric variable on `ℕ` is
constructed in `APITests/ShannonInformationFiniteEntropy.lean` with the class instance and
a proof of `¬ FiniteRange`, so the generalization is provably strict rather than nominal.

**The theorems have moved too**, which is what earlier revisions of this file deferred.
`FiniteEntropy/ChainRule.lean` (Phase 2) restates the five chain rules and gives
`condEntropy_eq_tsum`, deriving the Bochner integrability that `FiniteRange` made free
rather than assuming it. `FiniteEntropy/Inequalities.lean` (Phase 3) restates subadditivity,
mutual-information nonnegativity, submodularity and both independence characterizations —
equality case included. `FiniteEntropy/Derived.lean` (Phase 4a) restates the derived corpus:
data processing, entropy under maps, `condMutualInfo_eq'`, `IdentDistrib.condEntropy_eq`.
§4's table names, fact by fact, which `ShannonInformation.*` lemma is available and which
vendored statements were left at `FiniteRange`.

**Consumer migration (Phase 4b) landed 2026-08-17.** `Condensation`'s `RVModel` no longer
carries a `FiniteRange` field: it is Definition 3.1 verbatim — a countable discrete
probability space *with finite entropy* (`FiniteEntropyMeasure`) carrying countable-discrete-range
variables of finite entropy — and `Condensation.Example.geomModel` (`Ω = ℕ`, geometric law,
`X = id`) is a model the old field excluded. Four further lemmas were added to
`FiniteEntropy/Derived.lean` for that migration (`mutualInfo_const`,
`IndepFun.condEntropy_eq_entropy`, `const_of_nonpos_entropy`,
`finiteEntropyMeasure_of_injective`), and `FiniteEntropy/Examples.lean` now holds the
separating witness as library rather than test code.

The `FiniteRange` re-exports are **not** deprecated, so both
surfaces are live at once — `ShannonInformation/API.lean`'s "which version to cite" table
is the mapping, and it also records the ways a client can be bitten by having both in
scope.

---

## 1. What class of variables does the API support?

A random variable here is a measurable `X : Ω → S` on a measure space `(Ω, μ)`. Three
typeclass families appear in the hypotheses, and they are not equally serious:

| hypothesis | meaning | serious? |
| --- | --- | --- |
| `MeasurableSingletonClass S` | singletons are measurable | **presentational** — automatic for any discrete/countable `S` |
| `Countable S` | the *value type* is countable | **presentational** for our consumers — they are already discrete |
| `IsProbabilityMeasure μ` / `IsZeroOrProbabilityMeasure μ` | `μ` is a probability measure (or zero) | **presentational** — what everyone means anyway |
| `FiniteRange X` | `(Set.range X).Finite` — the variable takes **finitely many values** | **genuine mathematical restriction** |
| `ShannonInformation.FiniteEntropyOf X μ` | the entropy series of `X`'s law converges | **genuine, but strictly weaker** — the FAF hypothesis that replaces `FiniteRange` in §4's right-hand column |

`FiniteRange` is the one that matters:

```lean
class FiniteRange {Ω G : Type*} (X : Ω → G) : Prop where
  finite : (Set.range X).Finite
```

Note this is a condition on the *variable*, not the value type: `X : Ω → ℕ` with finitely
many attained values is fine, and a `Fintype` codomain gives the instance for free.

## 2. Does `FiniteRange` narrow us from countable-discrete finite-entropy variables?

**Yes, strictly.** A geometric variable on `ℕ` is countable-discrete with finite entropy
and does **not** have finite range. No vendored theorem tagged `FiniteRange` applies to it.

This is a real gap, not a typeclass artefact: PFR's proofs of these facts route through
`FiniteSupport` and `Finset` sums, so the hypothesis is load-bearing *in the proofs*, and
removing it required new mathematics (summability arguments), not new instances. That
mathematics has now been done for the facts in §4's table with a right-hand entry — those
*are* available for the geometric variable, through their `ShannonInformation.*` names, and
`APITests/ShannonInformationChainRule.lean` applies the chain rule to exactly such a pair.
The rows marked "not restated" remain unavailable for it.

## 3. But the *definitions* are already general

This is the good news, and it is why the gap is bounded. Entropy is defined by a `tsum`
over the whole value type:

```lean
def measureEntropy (μ : Measure S) : ℝ :=
  ∑' s, negMulLog (((μ Set.univ)⁻¹ • μ).real {s})
```

so `H[X ; μ]`, `H[X | Y ; μ]`, `I[X : Y ; μ]` and `I[X : Y | Z ; μ]` denote the *correct*
Shannon quantities for any countable-discrete variable, finite range or not. Nothing has
to be redefined to generalize, and nothing was: `FiniteEntropy/` adds theorems under a
summability hypothesis and leaves every definition, and every already-proved statement,
untouched.

**Two traps, and they are sharp.** The second: `condEntropy` is a Bochner integral over the
conditioning variable's law, and Lean's integral is `0` for a non-integrable integrand — so
a generalization must derive integrability from its finiteness class, never assume it. That
is what `FiniteEntropy/ChainRule.lean`'s `integrable_entropy_cond` exists to do, and it is
why integrability appears in no hypothesis there. The first: Lean's `∑'` evaluates to `0`
for a non-summable family. So for a variable of *infinite* entropy, `H[X ; μ]` is silently
`0` rather than `∞` or an error. Every generalized statement must carry an explicit
finite-entropy hypothesis; one that merely drops `FiniteRange` and says nothing about
summability would be quietly false at the infinite-entropy corner.

## 4. Which theorems survive without finite range?

Measured against the vendored source, not assumed. `FiniteRange` **not** required:

- `entropy_nonneg`, `entropy_congr`, `IdentDistrib.entropy_congr`, `entropy_comm`
- `entropy_le_log_card` (needs `Fintype S` instead), `entropy_comp_of_injective`
- `condEntropy_nonneg`
- `mutualInfo_def` (it is a definitional unfolding), `IdentDistrib.mutualInfo_eq`,
  `mutualInfo_comm` (measurability only — corrected 2026-08-17, it was mislisted below),
  `condMutualInfo_comm`

`FiniteRange` **required** — and, for each, whether the fact is now available at
`FiniteEntropyOf`. All names in the middle column are `ProbabilityTheory.*`; all in the
right-hand column are `ShannonInformation.*`.

| fact | `FiniteRange` version | FAF `FiniteEntropyOf` version |
| --- | --- | --- |
| chain rules | `chain_rule`, `chain_rule'`, `chain_rule''`, `cond_chain_rule`, `cond_chain_rule'` | same names |
| `H[X \| Y]` as a sum | `condEntropy_eq_sum` (a `Finset` sum) | `condEntropy_eq_tsum` (a `tsum`) |
| subadditivity, mutual information | `entropy_pair_le_add`, `mutualInfo_nonneg`, `condMutualInfo_nonneg` | same names — but see the measure-hypothesis caveat below |
| independence characterizations | `mutualInfo_eq_zero`, `entropy_pair_eq_add`, `condMutualInfo_eq_zero` | same names (`condMutualInfo_eq_zero` takes an extra `hZ : Measurable Z`) |
| submodularity | `entropy_submodular`, `entropy_triple_add_entropy_le`, `condEntropy_le_entropy` | same names |
| data processing | `entropy_comp_le`, `mutual_comp_le`, `condEntropy_comp_ge` | same names |
| conditional mutual information | `condMutualInfo_eq`, `condMutualInfo_eq'` | same names — `condMutualInfo_eq` needs `FiniteEntropyOf` on all three variables where the vendored one needs `FiniteRange Z` only |
| mutual information via conditional entropy | `mutualInfo_eq_entropy_sub_condEntropy`, `mutualInfo_eq_entropy_sub_condEntropy'` | same names |
| entropy under maps | `condEntropy_comp_self`, `condEntropy_of_injective'`, `entropy_of_comp_eq_of_comp` | same names |
| identically distributed | `IdentDistrib.condEntropy_eq` | same name, but **not** reachable by dot notation |
| conditional independence and entropy | `ent_of_cond_indep`, `IndepFun.condEntropy_eq_entropy` | not restated (see `Derived.lean`'s header) |
| constants | `mutualInfo_const`, `const_of_nonpos_entropy` | not restated (see `Derived.lean`'s header) |
| fibrewise injectivity | `condEntropy_of_injective`, `condMutualInfo_of_inj`, `condMutualInfo_of_inj'`, `condMutualInfo_of_inj_map` | not restated (see `Derived.lean`'s header) |
| two-sided data processing | `mutual_comp_comp_le`, `condMutual_comp_comp_le` | not restated (see `Derived.lean`'s header) |

The "not restated" rows are not hard problems. Each is one rewrite chain over the rows above
it, of the same shape as the ones that were done; they are absent because no consumer has
asked for them, and `FiniteEntropy/Derived.lean`'s header carries the authoritative list.

Two caveats on the restated rows, in the same breath as the claim. First,
`ProbabilityTheory.mutualInfo_nonneg`, `.entropy_pair_le_add` and `.condMutualInfo_nonneg`
carry **no** measure hypothesis at all upstream — they route through
`measureMutualInfo_nonneg`, which normalises internally — whereas the FAF versions require
`[IsZeroOrProbabilityMeasure μ]`. That is the one place a `FiniteRange` client loses
generality by switching, and closing it would mean restating the abstract summability layer
for an unnormalised family. Second, `ShannonInformation.condMutualInfo_eq` is strictly
stronger in its finiteness hypotheses than the vendored one, as the table says.

The original pattern is still legible: **anything definitional is free; anything with
content needed finite range.** In particular the asymmetry between `entropy_nonneg` (free)
and `mutualInfo_nonneg` (restricted) was not an oversight — the former is termwise
nonnegativity of `negMulLog` on `[0,1]`, the latter is subadditivity, a real theorem, and it
is exactly that theorem Phase 3 had to re-prove.

## 5. What generalization has been done

The three items this section used to list as future work are all done.

1. **A `FiniteEntropy`-style hypothesis** — a class asserting summability of the entropy
   series (PFR's `FiniteSupport` is the finite-range analogue), which everything downstream
   keys off instead of `FiniteRange`. **Done**: `ShannonInformation.FiniteEntropyOf`, with
   instances and closure lemmas, in `FiniteEntropy/Summable.lean`, `Defs.lean` and
   `Pi.lean`.
2. **Re-prove the chain rules.** **Done**, in `FiniteEntropy/ChainRule.lean` — and not by
   the limiting argument this section anticipated. The route taken sums Phase 1's local
   chain rule fibrewise, bypassing PFR's kernel layer entirely; the actual difficulty was
   not the sum but the Bochner integrability of `y ↦ H[X | Y ← y]`, which is derived from
   the class rather than assumed (`integrable_entropy_cond`).
3. **Re-prove subadditivity / submodularity.** **Done**, in `FiniteEntropy/Inequalities.lean`,
   which gives back `mutualInfo_nonneg`, `entropy_submodular`, `entropy_triple_add_entropy_le`
   and the independence characterizations. The equality case that Phase 3's plan flagged as
   the least-calibrated piece fell out of the same gap decomposition, so `mutualInfo_eq_zero`
   and `condMutualInfo_eq_zero` are proved rather than deferred.

The derived corpus that rests on those two — data processing, entropy under maps,
`condMutualInfo_eq'`, `IdentDistrib.condEntropy_eq` — followed in
`FiniteEntropy/Derived.lean`, every proof a rewrite chain over Phases 2–3.

**What that cost, measured.** Phase 2 is ≈ 345 lines of Lean, a ≈ 3× plumbing multiplier
over the abstract core it instantiates; Phase 3 ≈ 825 lines, including a local duplicate of
the chain rule since deleted; the equality case ≈ 40 of those lines; Phase 4a ≈ 300 lines,
essentially all docstring and rewrite chains. That is comfortably inside the
1,450–2,400-line estimate of `Condensation/notes/finite-range-generalization-plan.md`
(2026-08-17), and it did not require the upstream route that plan's §5 weighed: nothing was
taken to PFR, and the layer's kernel-free measure-level proofs are what made forking cheaper
than generalizing PFR's `FiniteSupport` kernel machinery would have been.

**What is still outstanding.** Three things, none of them mathematics. Consumers have not
been migrated — `Condensation`'s `RVModel` still carries a `FiniteRange` field (Phase 4b).
The vendored statements listed as "not restated" in §4 remain `FiniteRange`-only. And the
residual hypothesis gap stands: three vendored nonnegativity statements need no measure
hypothesis at all where ours need `IsZeroOrProbabilityMeasure`, and
`ShannonInformation.condMutualInfo_eq` needs `FiniteEntropyOf` on all three variables where
the vendored one needs `FiniteRange` on one.

## 6. Is the current layer sufficient for the motivating consumers?

**For countable-discrete finite-entropy statements, now yes. For continuous ones, no.**

- *Condensation* (Eisenstat, 2025) — **assessed, and the substrate now reaches it.** It
  assumes throughout that probability spaces are "countable and discrete … with finite
  entropy", which is strictly weaker than finite range, so the *vendored* statements do not
  cover its stated generality. `ShannonInformation.FiniteEntropyOf` is exactly that
  hypothesis, and the chain rules, subadditivity, submodularity and both independence
  characterizations are now available at it — so a formalization of the paper's §4 no longer
  has to narrow its hypotheses to `FiniteRange` and disclose the narrowing. **This does not
  mean the Condensation formalization has been migrated: it has not.** `Condensation`'s
  `RVModel` still carries a `FiniteRange` field, and swapping it is Phase 4b of the plan.
  Anyone doing that swap should check §4's table first — the not-restated tail is still
  `FiniteRange`-only, and Prop 2.5's generalized form is paper-specific work that belongs in
  `Condensation/`, not here.
- *Natural Latents* (Wentworth–Lorell, arXiv:2509.03780) — **assessed, and the answer is
  no.** Its theorems are stated for generic latents with no finiteness hypothesis, and its
  own worked quantitative example puts a **uniform prior on `Λ` over the interval `[0,1]`**
  — a continuous latent, outside not just finite range but discreteness. So the paper as
  written is **not** covered by this layer.

  Two mitigations, both real:
  * the quantities the worked example actually *computes* are finite-range (`N₁, N₂ ∈
    {0,…,1000}`, `Λ' ∈ {0,1}`), so a finite-range formalization would cover the theorems
    *as applied*, while excluding the continuous-latent modelling built around them;
  * the paper's primitive is **KL divergence**, not entropy — "satisfies a Bayes net to
    within `ε`" is `ε ≥ D_KL(P ‖ ∏ⱼ P[Yⱼ|Y_pa(j)])` — and Mathlib's
    `InformationTheory.klDiv` is defined in full generality. Only the bridge
    `Y ← X → Y  ⟺  ε ≥ H(Y|X)` lands in the entropy layer.

  Verified by probe: `ShannonInformation.API` and
  `Mathlib.InformationTheory.KullbackLeibler.Basic` **co-import cleanly**, and both NL
  primitives are expressible side by side. One impedance mismatch to expect: `klDiv` is
  `ℝ≥0∞`-valued at this pin (`Mathlib/InformationTheory/KullbackLeibler/Basic.lean`) while
  PFR's entropy is `ℝ`-valued.

So the honest position is: **the layer supports countable-discrete information theory with
finite entropy, and no more. Whether that suffices for a given paper is a question about
that paper, to be answered when it is formalized — not something this layer can promise in
advance.** What a formalization must still do is choose a surface explicitly and say which:
`FiniteRange` if the vendored statements suffice, `FiniteEntropyOf` if the paper's own
hypothesis is finite entropy, and a disclosed narrowing if the paper is stated for anything
wider than either. Nothing in §4's "not restated" list is available at `FiniteEntropyOf`
today, and a paper that needs one of those items has to fund its restatement — a rewrite
chain, not a research problem.

That choice belongs to the paper formalization, not to this infrastructure. What this
layer owes such a project is that the boundary is impossible to miss, which is the purpose
of this file.
