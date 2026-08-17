# Scope of the shared Shannon-information layer

**Read this before relying on an entropy statement.** The vendored library is stated for a
narrower class of random variables than several prospective FAF consumers assume, and the
gap is mathematical, not cosmetic.

The short version:

> **The definitions are right for countable-discrete variables. The theorems are proved
> only for finite-range ones.** Generalizing means re-proving theorems under a summability
> hypothesis; it does not mean redefining anything.

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

`FiniteRange` is the one that matters:

```lean
class FiniteRange {Ω G : Type*} (X : Ω → G) : Prop where
  finite : (Set.range X).Finite
```

Note this is a condition on the *variable*, not the value type: `X : Ω → ℕ` with finitely
many attained values is fine, and a `Fintype` codomain gives the instance for free.

## 2. Does `FiniteRange` narrow us from countable-discrete finite-entropy variables?

**Yes, strictly.** A geometric variable on `ℕ` is countable-discrete with finite entropy
and does **not** have finite range. Every theorem tagged `FiniteRange` in the table below
is therefore unavailable for it today.

This is a real gap, not a typeclass artefact: PFR's proofs of these facts route through
`FiniteSupport` and `Finset` sums, so the hypothesis is load-bearing *in the proofs*, and
removing it requires new mathematics (summability arguments), not new instances.

## 3. But the *definitions* are already general

This is the good news, and it is why the gap is bounded. Entropy is defined by a `tsum`
over the whole value type:

```lean
def measureEntropy (μ : Measure S) : ℝ :=
  ∑' s, negMulLog (((μ Set.univ)⁻¹ • μ).real {s})
```

so `H[X ; μ]`, `H[X | Y ; μ]`, `I[X : Y ; μ]` and `I[X : Y | Z ; μ]` denote the *correct*
Shannon quantities for any countable-discrete variable, finite range or not. Nothing has
to be redefined to generalize; a future extension adds theorems under a summability
hypothesis and leaves every definition, and every already-proved statement, untouched.

**One trap, and it is sharp.** Lean's `∑'` evaluates to `0` for a non-summable family. So
for a variable of *infinite* entropy, `H[X ; μ]` is silently `0` rather than `∞` or an
error. Any future generalization must carry an explicit finite-entropy hypothesis; a
statement that merely drops `FiniteRange` and says nothing about summability would be
quietly false at the infinite-entropy corner.

## 4. Which theorems survive without finite range?

Measured against the vendored source, not assumed. `FiniteRange` **not** required:

- `entropy_nonneg`, `entropy_congr`, `IdentDistrib.entropy_congr`, `entropy_comm`
- `entropy_le_log_card` (needs `Fintype S` instead), `entropy_comp_of_injective`
- `condEntropy_nonneg`
- `mutualInfo_def` (it is a definitional unfolding), `IdentDistrib.mutualInfo_eq`,
  `condMutualInfo_comm`

`FiniteRange` **required**:

- all chain rules — `chain_rule`, `chain_rule'`, `chain_rule''`, `cond_chain_rule`,
  `cond_chain_rule'`
- `mutualInfo_nonneg`, `condMutualInfo_nonneg`, `mutualInfo_comm`
- the independence characterizations — `mutualInfo_eq_zero`, `condMutualInfo_eq_zero`,
  `entropy_pair_eq_add`, `ent_of_cond_indep`
- `condEntropy_le_entropy`, `condEntropy_comp_self`, `IdentDistrib.condEntropy_eq`
- `entropy_submodular`, `entropy_pair_le_add`, `entropy_triple_add_entropy_le`
- data processing — `entropy_comp_le`, `mutual_comp_le`
- `condMutualInfo_eq`, `mutualInfo_eq_entropy_sub_condEntropy`, `mutualInfo_const`,
  `const_of_nonpos_entropy`

The pattern is legible: **anything definitional is free; anything with content needs finite
range.** In particular the asymmetry between `entropy_nonneg` (free) and
`mutualInfo_nonneg` (restricted) is not an oversight — the former is termwise
nonnegativity of `negMulLog` on `[0,1]`, the latter is subadditivity, a real theorem.

## 5. What would generalization take?

Roughly, in increasing order of effort:

1. **A `FiniteEntropy`-style hypothesis** — a class asserting summability of the entropy
   series (PFR's `FiniteSupport` is the finite-range analogue). Everything downstream keys
   off this instead of `FiniteRange`.
2. **Re-prove the chain rules** by a limiting argument over an exhausting sequence of
   finite sets, rather than PFR's direct `Finset` manipulation. This is the bulk of the
   work and it is where the mathematics actually lives.
3. **Re-prove subadditivity / submodularity** in the same style, which gives back
   `mutualInfo_nonneg`, `entropy_submodular` and the independence characterizations.

This is a substantial project — plausibly comparable in size to the vendored library
itself — and it is emphatically **not** attempted here. It is also not obviously the right
move: it may be cheaper to upstream a generalization into PFR than to fork one into FAF.

## 6. Is the current layer sufficient for the motivating consumers?

**For their finite-valued fragment, yes. For the generality they nominally state, no.**

- *Condensation* (Eisenstat, 2025) — **assessed.** It assumes throughout that probability
  spaces are "countable and discrete … with finite entropy", which is strictly weaker than
  finite range, so its stated generality is **not** covered. Its worked material largely is:
  the bucketing construction in its §5.1 exists precisely to turn a `[0,1]`-valued latent
  into a finite-valued one, and its examples are built from finite families of
  finitely-valued variables. A formalization could therefore state §4 under `FiniteRange`
  and cover the paper's substance, at the cost of a disclosed narrowing of its hypotheses.
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
  `EReal`-valued while PFR's entropy is `ℝ`-valued.

So the honest position is: **the current layer supports finite-valued information theory.
Whether that suffices for a given paper is a question about that paper, to be answered
when it is formalized — not something this layer can promise in advance.** A formalization
must either restrict its own statements to finite range and say so as a disclosed modeling
decision, or fund the generalization in §5 first.

That choice belongs to the paper formalization, not to this infrastructure PR. What this
layer owes such a project is that the boundary is impossible to miss, which is the purpose
of this file.
