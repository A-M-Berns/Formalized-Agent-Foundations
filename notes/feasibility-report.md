# Critch Feasibility Report

Primary paper source: Andrew Critch, "A Parametric, Resource-Bounded
Generalization of Löb's Theorem, and a Robust Cooperation Criterion for
Open-Source Game Theory," Journal of Symbolic Logic 84(4), 2019,
https://doi.org/10.1017/jsl.2017.42.

## Phase 0 paper trace

This traces the proof of the paper's Theorem 4.2, the resource-bounded
generalization of Löb's theorem. The paper's notation `□_k` is represented in the
repo plan by bounded provability at bound `k`; Layer B interprets this as
Foundation's `RestrictedProvable k`, i.e. proof Gödel number `< 2^k`.

1. Choose `g` with `lg k ≺ g k` and `e (g k) ≺ f k`.
   Requirement: asymptotic inequalities.
2. Define `G[n,k]` as `□_{g k}` of the formula coded by `n` at `k`, implying `p[k]`.
   Requirement: bounded provability syntax plus single-variable evaluation.
3. Observe `G[⌜φ⌝,k] = □_{g k}(φ[k]) → p[k]`.
   Requirement: evaluation/quotation compatibility.
4. Apply the parametric diagonal lemma to obtain `ψ[k] ↔ G[⌜ψ⌝,k]`.
   Requirement: Parametric Diagonal.
5. Let `n` be the proof length of the universal diagonal equivalence.
   Requirement: proof-length bookkeeping.
6. Apply bounded necessitation to the proof of the universal equivalence.
   Requirement: Bounded Necessitation.
7. Apply quantifier distribution to specialize the universal equivalence at `k`.
   Requirement: Quantifier Distribution.
8. Project the forward implication `ψ[k] → G[⌜ψ⌝,k]`.
   Requirement: propositional proof overhead / bounded D1 for a fixed derivation.
9. Use implication distribution to get `□_a ψ[k] → □_{a+O(lg k)} G[⌜ψ⌝,k]`.
   Requirement: Implication Distribution.
10. Expand `G[⌜ψ⌝,k]` as `□_{g k} ψ[k] → p[k]`.
    Requirement: evaluation/definitional rewriting.
11. Apply implication distribution again to the implication inside `G`.
    Requirement: Implication Distribution.
12. Obtain the three-bound statement with `a`, `b`, and final bound
    `a + b + O(lg k)`.
    Requirement: Implication Distribution plus asymptotic bookkeeping.
13. Specialize `a := g k` and choose `b := h k` with `e(g k) ≺ h k ≺ f k`.
    Requirement: asymptotic inequalities and computable substitution.
14. Derive
    `□_{g k} ψ[k] → (□_{h k} □_{g k} ψ[k] → □_{g k+h k+O(lg k)} p[k])`.
    Requirement: previous distribution result.
15. Use `g k + h k + O(lg k) < f k` eventually.
    Requirement: asymptotic inequalities and bounded monotonicity.
16. Replace the final bound by `f k` for all `k > k₁`.
    Requirement: bounded monotonicity in the proof bound.
17. Use the theorem hypothesis `□_{f k} p[k] → p[k]`.
    Requirement: propositional composition.
18. Obtain Equation 4.4:
    `□_{g k} ψ[k] → (□_{h k} □_{g k} ψ[k] → p[k])`.
    Requirement: propositional composition.
19. Separately apply bounded inner necessitation to
    `□_a ψ[k] → □_{e a} □_a ψ[k]`.
    Requirement: Bounded Inner Necessitation.
20. Specialize `a := g k`.
    Requirement: computable substitution.
21. Use `e(g k) < h k` eventually to strengthen the inner bound to `h k`.
    Requirement: asymptotic inequalities and bounded monotonicity.
22. Obtain Equation 4.5:
    `□_{g k} ψ[k] → □_{h k} □_{g k} ψ[k]`.
    Requirement: bounded monotonicity.
23. Combine Equations 4.4 and 4.5 to prove
    `□_{g k} ψ[k] → p[k]` for all sufficiently large `k`.
    Requirement: propositional composition.
24. Use the diagonal equivalence to turn the preceding implication into `ψ[k]`.
    Requirement: diagonal equivalence plus propositional composition.
25. Apply bounded necessitation to the resulting universal proof of `ψ[k]`.
    Requirement: Bounded Necessitation.
26. Apply quantifier distribution to obtain `□_{C+2N+lg k} ψ[k]`.
    Requirement: Quantifier Distribution.
27. Use `C + 2N + lg k < g k` eventually.
    Requirement: asymptotic inequalities and bounded monotonicity.
28. Obtain `□_{g k} ψ[k]` for all sufficiently large `k`.
    Requirement: bounded monotonicity.
29. Combine with step 23 to conclude `p[k]` for all sufficiently large `k`.
    Requirement: propositional composition.

No step obviously falls outside the proposed design, but the design needs two
items that should be explicit typeclass fields rather than hidden lemmas:
bounded monotonicity in the resource bound, and quantifier distribution. The
current scaffold includes monotonicity but not quantifier distribution yet.

## Parametric diagonal feasibility

Critch's Proposition 4.3 does not need to be built from scratch on the pinned
Foundation commit. Foundation already has `parameterizedFixedpoint` and
`parameterized_diagonal`, which produce a formula with `k` remaining free
variables:

```lean
theorem parameterized_diagonal
    (θ : Semisentence ℒₒᵣ (k + 1)) :
  T ⊢ ∀⁰* (parameterizedFixedpoint θ 🡘
    “!θ !!(⌜parameterizedFixedpoint θ⌝) ⋯”)
```

This is the right shape for Critch's proposition. It is distinct from
`multidiagonal`, which produces mutually fixed sentences. The remaining work is
not inventing the diagonal lemma; it is packaging this theorem in the bounded
provability development and matching Critch's one-free-variable evaluation
notation to Foundation's substitution/quotation notation.

If a future generalization needs a different object language than arithmetic,
then a new parametric proof would follow Foundation's current proof: define a
parameterized diagonal formula, substitute its own code into the first variable,
and prove the universal equivalence by semantic calculation over the remaining
parameters.

## Layer B encoding question

Foundation's proof encoding is explicit enough that Phase 6 looks feasible, but
there is no clean packaged MP-bound lemma yet.

The key constructor is `cutRule`:

```lean
noncomputable def cutRule (s p d₁ d₂ : V) : V :=
  ⟪s, 8, p, d₁, d₂⟫ + 1
```

The pairing function is quadratic in the larger component, and nested tuples are
iterated pairings. Therefore a bound of the form
`cutRule s p d₁ d₂ ≤ P(max d₁ d₂)` should be derivable for a fixed polynomial
`P`, once `s` and `p` are bounded by the input derivation codes. That side-data
bound should follow from the `DerivationOf` hypotheses plus the existing
component lemmas, but it is not a one-line theorem currently exposed by
Foundation.

Because `RestrictedProvable e` bounds proof codes by `2^e`, a polynomial bound
on the new proof code becomes linear/additive overhead in `e`. This supports the
planned reinterpretation: character-count overhead in Critch corresponds to
exponent overhead for Foundation's restricted proof-code bound.

Risk: the hardest Layer B work is not defining the instance predicate; that now
compiles. The hard part is proving the quantitative cut/necessitation bounds and
internalizing them. If this becomes too expensive, Layer A can still be completed
cleanly and Layer B can be left as a separately stated encoding theorem.

## Other observations

The paper's `f ≺ g` means domination by every constant multiple, not merely
eventual strict inequality. The scaffold uses the stronger paper-faithful meaning.

The bounded interface should not hide Critch's properties inside one large
typeclass. It should name the proof-theoretic assumptions separately:
implication distribution, quantifier distribution, bounded necessitation, bounded
inner necessitation, and monotonicity. This will make the correspondence with the
paper trace auditable.

The new `Critch` target builds independently, and the new `AgentFoundations`
default target imports both `Barasz` and `Critch` without modifying Barasz files.
