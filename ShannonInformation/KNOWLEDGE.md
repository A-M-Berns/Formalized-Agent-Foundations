# ShannonInformation — knowledge base (generalization thread)

Institutional memory for the FAF-authored layer over the vendored PFR entropy library — in
particular the countable-range / finite-entropy generalization (`FiniteEntropy/`), planned in
`Condensation/notes/finite-range-generalization-plan.md` and ruled a desired endpoint on
2026-08-17. Vendored mathematics is documented in `README.md`/`SCOPE.md`; this file records
what the FAF-authored work learned. Add an entry only if a future agent would act differently
for knowing it.

## Design decisions

- `FiniteEntropyMeasure μ` is summability of exactly `measureEntropy`'s summand (normalisation
  included), so no bridge lemma is needed; `FiniteEntropyOf X μ := FiniteEntropyMeasure (μ.map X)`.
  PFR's unused `FiniteEntropy` (countability conjunct) is deliberately not reused.
- `FiniteRange → FiniteEntropyOf` and `FiniteSupport → FiniteEntropyMeasure` are priority-100
  instances, so the whole vendored `FiniteRange` instance graph feeds the class; the generalization
  is strictly additive — nothing previously provable breaks.
- Finite joint products close (`finiteEntropyOf_pi`, `Fintype` index); countable ones provably
  do not (H[X_n] = 1 for all n) — never state a `Π`-closure over a countable index.
- Files under `FiniteEntropy/` import `PFR.*` and targeted Mathlib directly, never
  `ShannonInformation.API` (cycle) and never `import Mathlib` wholesale. Downstream imports `API`.
- New endpoints go in `ShannonInformation/AxiomAudit.lean`'s `#assert_axioms_clean_si` blocks,
  not the top-level `AxiomAudit.lean`.

## Correspondence (Phase 1 names)

`FiniteEntropyMeasure`, `FiniteEntropyOf`, `finiteEntropy_of_finiteSupport`,
`finiteEntropy_of_finiteRange`, `finiteEntropyMeasure_map`, `finiteEntropyMeasure_prod`,
`finiteEntropyOf_pair/_fst/_snd/_comp/_pullback/_measurableEquiv/_piFin/_pi`; abstract core
`negMulLog_tsum_le` (C1), `tsum_negMulLog_eq_add` (C2), `tsum_mul_log_div_nonneg` (C3),
`negMulLog_le_add_of_le` (termwise pair bound = subadditivity once summed),
`summable_negMulLog_tsum_fiber`, `tsum_negMulLog_tsum_fiber_le`. Entropy-as-tsum already exists
upstream: `ProbabilityTheory.entropy_eq_sum` — do not re-derive it.

## Pitfalls

- **Mathlib's product/fibre summability for nonnegative families exists under `to_additive`
  names** (`Summable.tsum_prod`, `Summable.prod_factor`, `Summable.prod_symm`,
  `HasSum.prod_fiberwise`, `HasSum.tsum_fiberwise`, `Summable.tsum_subtype_le`,
  `summable_prod_of_nonneg`, `summable_sigma_of_nonneg`, `Real.tsum_le_of_sum_le`,
  `Summable.of_nonneg_of_le`, `ENNReal.tsum_toReal_eq`) in
  `Mathlib/Topology/Algebra/InfiniteSum/{Constructions,Real,Order,ENNReal}.lean`. Grepping for
  `theorem Summable.tsum_prod` finds nothing; grep the additive *target* name.
- `μ.map id` is not `μ` by `rfl` (`Measure.map` is an `if Measurable`); use
  `show FiniteEntropyMeasure (μ.map id); rw [Measure.map_id]; infer_instance`.
- `finiteEntropyOf_pair hX hY` leaves `μ` a metavariable — write `(μ := μ)` inside `haveI`.
- `omit [Inst] in` goes before the docstring, not between docstring and declaration.
- Transport along `MeasurableEquiv.piCongrLeft R e.symm`: use
  `exact (E.apply_symm_apply fun i ↦ X i ω).symm`; do not route through
  `piCongrLeft_apply_apply` (dependent congruence blocks simp).
- `Fin n`-induction over a dependent family: keep `R`, its instances and `X` universally
  quantified inside the lemma statement, else the IH's instance arguments are anonymous;
  base case needs `haveI : Finite (∀ i : Fin 0, R i) := Finite.of_subsingleton`.
- `finiteEntropyOf_pi` on a `![X, Y]` family needs `haveI := by intro i; fin_cases i <;> assumption`.
- `lake env lean` does not apply the lakefile's `autoImplicit := false`; a clean run is not evidence
  about auto-bound implicits — gate with `lake build`.
- Geometric witness traps: `⟨1/2, _⟩ : unitInterval` must be `noncomputable`; the ℝ `tsum_pos` is
  `Summable.tsum_pos`; geometric-series lemmas want `‖r‖ < 1` — discharge with
  `rw [Real.norm_eq_abs]; norm_num`.
- Two `∑'`-style traps in the vendored definitions: `H[X]` is `0` for a non-summable series, and
  `condEntropy` is a Bochner integral, silently `0` when non-integrable. Every generalized theorem
  must derive integrability/summability from `FiniteEntropyOf`, never assume it.

## Calibration

Phase 1: 712 lines of Lean (Summable 228 / Defs 360 / Pi 124, a third docstrings) + 165 lines of
tests; plumbing multiplier over the scratch core ≈ 2–2.5× (plan guessed 3–5×); wall clock < 1 h
with three parallel agents.
