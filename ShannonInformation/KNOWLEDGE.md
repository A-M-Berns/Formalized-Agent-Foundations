# ShannonInformation — knowledge base (generalization thread)

Institutional memory for the FAF-authored layer over the vendored PFR entropy library — in
particular the countable-range / finite-entropy generalization (`FiniteEntropy/`), planned in
`Condensation/notes/finite-range-generalization-plan.md` and ruled a desired endpoint on
2026-08-17. Phases 1–4a of that plan have landed; consumer migration (Phase 4b) has not.
Vendored mathematics is documented in `README.md`/`SCOPE.md`; this file records
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
- The chain rules are proved at the **measure layer with no kernels**: PFR routes through
  `entropy_eq_kernel_entropy` / `Kernel.chain_rule`, but for the measure-level statement that
  kernel is constant over `Unit` and pure overhead. The whole content is Phase 1's
  `tsum_negMulLog_eq_add` applied fibrewise and summed. Do not reintroduce the kernel layer.
- Integrability of `y ↦ H[X | Y ← y]` is **derived** (`integrable_entropy_cond`), never a
  hypothesis. Adding it as a hypothesis is what makes the class stop composing, and Lean's
  Bochner integral being `0` on a non-integrable integrand is what would make such a statement
  silently vacuous.
- `condMutualInfo_eq` lives in `ChainRule.lean`, **not** `Derived.lean`, even though it belongs
  to the derived corpus mathematically. It is the splitting of `condMutualInfo`'s defining
  Bochner integral, so it rests on `integrable_entropy_cond`; and `Inequalities.lean` consumes
  it (`condEntropy_pair_le_add`) while `Derived.lean` imports `Inequalities.lean`. Moving it
  "home" creates an import cycle.
- Phase 3's and Phase 4a's endpoints are at `[IsZeroOrProbabilityMeasure μ]`, matching PFR
  wherever PFR carries a measure hypothesis at all. **Residual gap, deliberate:**
  `ProbabilityTheory.mutualInfo_nonneg`, `.entropy_pair_le_add` and `.condMutualInfo_nonneg`
  carry *no* measure hypothesis — they route through `measureMutualInfo_nonneg`, which
  normalises internally. Ours require `IsZeroOrProbabilityMeasure`; that is the one place a
  `FiniteRange` client loses generality, and closing it would mean restating the abstract
  summability layer for an unnormalised family.
- `ShannonInformation.condMutualInfo_eq` needs `FiniteEntropyOf` on **all three** of `X`, `Y`,
  `Z`, where `ProbabilityTheory.condMutualInfo_eq` needs only `[FiniteRange Z]`. PFR's kernel
  route reads all three conditional entropies off one `condDistrib`; ours splits the defining
  integral and so needs each integrand integrable. The only FAF statement that is not a
  pointwise weakening of its vendored twin — say so wherever it is cited.
- Keep **both** `measureReal_map_cond_singleton` (`Inequalities.lean`) and
  `map_cond_measureReal_singleton` (`ChainRule.lean`). Same left side,
  `((μ[|Z ⁻¹' {z}]).map X).real {x}`; different right sides — preimage form
  `μ.real (X ⁻¹' {x} ∩ Z ⁻¹' {z}) / μ.real (Z ⁻¹' {z})`, no hypothesis on the conditioning
  variable, versus joint-law form `(μ.map ⟨Z, X⟩).real {(z, x)} / (μ.map Z).real {z}`, needing
  `Measurable Z` and `MeasurableSingletonClass` on its value type. Neither subsumes the other;
  both are used. Do not "consolidate".
- `Inequalities.lean` carried a private `ChainRuleLocal` duplicate of the chain rule while
  Phases 2 and 3 were in flight; Phase 4a deleted it and made `Inequalities.lean` import
  `ChainRule.lean`. There is one chain rule in the layer.

## Correspondence (Phase 1 names)

`FiniteEntropyMeasure`, `FiniteEntropyOf`, `finiteEntropy_of_finiteSupport`,
`finiteEntropy_of_finiteRange`, `finiteEntropyMeasure_map`, `finiteEntropyMeasure_prod`,
`finiteEntropyOf_pair/_fst/_snd/_comp/_pullback/_measurableEquiv/_piFin/_pi`; abstract core
`negMulLog_tsum_le` (C1), `tsum_negMulLog_eq_add` (C2), `tsum_mul_log_div_nonneg` (C3),
`negMulLog_le_add_of_le` (termwise pair bound = subadditivity once summed),
`summable_negMulLog_tsum_fiber`, `tsum_negMulLog_tsum_fiber_le`. Entropy-as-tsum already exists
upstream: `ProbabilityTheory.entropy_eq_sum` — do not re-derive it.

## Correspondence (Phases 2–4a names)

`FiniteEntropy/ChainRule.lean` (Phase 2) — `integrable_of_summable_measureReal_mul_norm`,
`map_cond_measureReal_singleton`, `measureReal_mul_entropy_cond`,
`summable_measureReal_mul_entropy_cond`, `integrable_entropy_cond`, `condEntropy_eq_tsum`,
`chain_rule''`, `chain_rule`, `chain_rule'`, `condEntropy_eq_entropy_pair_sub`,
`cond_chain_rule'`, `cond_chain_rule`, and (added in Phase 4a) `condMutualInfo_eq`.

`FiniteEntropy/Inequalities.lean` (Phase 3) — `tsum_negMulLog_prod_le`,
`tsum_negMulLog_prod_eq_add_iff`, `measureEntropy_prod_le_add`, `measureEntropy_prod_eq_add_iff`,
`finiteEntropyMeasure_zero`, `measureReal_map_cond_singleton`, `finiteEntropyOf_cond`,
`entropy_pair_le_add`, `mutualInfo_nonneg`, `mutualInfo_eq_zero`, `entropy_pair_eq_add`,
`condMutualInfo_nonneg`, `condEntropy_le_entropy`, `condEntropy_pair_le_add`,
`entropy_submodular`, `entropy_triple_add_entropy_le`, `condMutualInfo_eq_zero`.

`FiniteEntropy/Derived.lean` (Phase 4a) — `entropy_comp_le`, `entropy_of_comp_eq_of_comp`,
`condEntropy_comp_self`, `condEntropy_of_injective'`, `mutualInfo_eq_entropy_sub_condEntropy`,
`mutualInfo_eq_entropy_sub_condEntropy'`, `condEntropy_comp_ge`, `mutual_comp_le`,
`condMutualInfo_eq'`, `IdentDistrib.condEntropy_eq`.

Deliberately **not** restated (all still `FiniteRange`-only upstream, each a one-screen rewrite
chain away): `ent_of_cond_indep`, `mutualInfo_const`, `const_of_nonpos_entropy`,
`condEntropy_of_injective`, `condMutualInfo_of_inj`/`_of_inj'`/`_of_inj_map`,
`mutual_comp_comp_le`, `condMutual_comp_comp_le`, `IndepFun.condEntropy_eq_entropy`.
`Derived.lean`'s header is the authoritative list; `API.lean`'s "which version to cite" table
is the client-facing one.

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
- **`μ` in instance arguments or the conclusion only ⇒ "typeclass instance problem is stuck".**
  `have := lemma hX hY` where `μ` reaches the elaborator neither through an explicit argument
  nor through the expected type reports the stuck instance **at the declaration name**, not at
  the `have` — so the error points somewhere useless. Always write `(μ := μ)`. This covers
  `finiteEntropyOf_pair hX hY` (leaves `μ` a metavariable inside `haveI`),
  `entropy_pair_le_add (μ := μ) hX hY`, `finiteEntropyOf_cond (μ := μ) (Z := Z) hX z`, and
  every `have := …` feeding a `linarith` in `Inequalities.lean`.
- **`⟨X, Y⟩` loses to the anonymous constructor when the expected type is a metavariable.**
  PFR's pair notation only elaborates when the target type is already known; in a `haveI`, a
  `Summable fun q ↦ …` binder, or a `Measure.map` argument it silently becomes an anonymous
  constructor and fails. Ascribe: `(⟨Y, X⟩ : Ω → T × S)`.
- **Never put a pair-shaped instance argument on a public endpoint.** `finiteEntropyOf_pair`
  is a *lemma*, not an instance, so `[FiniteEntropyOf (⟨X, Y⟩ : Ω → S × T) μ]` in a signature
  is a hypothesis no caller can discharge by instance search. Take the two marginal instances
  and build the pair internally with `haveI : FiniteEntropyOf (⟨Y, X⟩ : Ω → T × S) μ :=
  finiteEntropyOf_pair hY hX`.
- **`linarith` sees `H[X | fun a => (Y a, Z a)]` and `H[X | ⟨Y, Z⟩]` as different atoms.** The
  chain-rule rewrites and the goal can end up in different spellings of the same pair, and
  `linarith` then fails with all the right facts in context. Ascribe the `have` types in the
  goal's spelling before calling it.
- **`HasSum.sub`/`.add` results do not match a stated `HasSum` at reducible transparency.**
  `(h₁.sub h₂ : HasSum _ (a - b))` will not `exact` against a goal whose value is written
  `a - b` differently-associated. Normalise the value in a `have` with `ring`, then `exact`.
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
- `rw [← Set.singleton_prod_singleton]` rewrites **both** sides (structure eta makes the two
  occurrences syntactically equal) and takes no explicit arguments to aim it. Use
  `show ({q} : Set (S × T)) = {q.1} ×ˢ {q.2} from Set.singleton_prod_singleton.symm` inside the
  `rw` instead.
- `Summable.prod_symm` works bare but not through `simpa` (the `simp` set re-normalises the
  swapped index and the result no longer matches). `Equiv.tsum_eq` needs its function argument
  given **explicitly**; leaving it to unification fails.
- `∑' i, μ.real {i} = 1` on a countable space comes from `MeasureTheory.integral_countable`
  applied to the **constant function `1`** — there is no direct lemma.
- **Mathlib has no `integrable_countable`.** The integrability criterion on a countable space is
  `integrable_sum_dirac` together with `Measure.sum_smul_dirac` (that is exactly what
  `integrable_of_summable_measureReal_mul_norm` packages); `integral_countable` is the *value*
  lemma and presupposes integrability. Do not go looking for the symmetric name.
- `ProbabilityTheory.cond_real_apply` is **PFR's**, not Mathlib's. Mathlib's `cond_apply'` has
  the conditioning set implicit and yields an `s ∩ t`, so the two need different rewrite shapes.
- `ProbabilityTheory.entropy_cond_eq_sum` already handles null fibres; do not case-split on the
  fibre mass before calling it.
- `entropy_comp_of_injective` needs a `change` with an **explicit** `f` first
  (`change H[(fun p : (S × T) × U ↦ (p.1.2, (p.1.1, p.2))) ∘ ⟨⟨X, Y⟩, Z⟩ ; μ] = _`), or
  elaboration hits a whnf timeout trying to unify the composition.
- The **conditional** chain rules reduce to the unconditional ones plus
  `entropy_comp_of_injective` (relabelling a triple). No fibrewise-over-`Z` argument is needed;
  do not build one.
- `cond_isProbabilityMeasure_of_real` wants `μ.real (Y ⁻¹' {y}) ≠ 0` — a **preimage** — while
  `condEntropy_eq_zero` wants `(μ.map Y).real {t}` — a **pushforward**. Converting between them
  is `map_measureReal_apply hY (measurableSet_singleton y)`.
- **Namespace shadowing: ambiguity is resolved by elaboration success, not by the enclosing
  namespace.** A bare `condMutualInfo_eq` inside `namespace ShannonInformation` silently picks
  PFR's `FiniteRange` version and fails with "failed to synthesize `FiniteRange Z`" — this bit a
  Phase 4a edit. Write `ShannonInformation.condMutualInfo_eq` in full. Related:
  `ShannonInformation.IdentDistrib.condEntropy_eq` is **not reachable by dot notation** —
  `h.condEntropy_eq` resolves in the head symbol's namespace, `ProbabilityTheory`.
- **`lake env lean <file>` elaborates against stale oleans.** After adding a declaration to an
  upstream module, `lake env lean` on a downstream file reports "unknown identifier" for it until
  that module is rebuilt. Rebuild the single module first —
  `lake build ShannonInformation.FiniteEntropy.ChainRule` — then iterate downstream.
- **`@[simp]` on its own line defeats the obvious grep.** PFR writes the attribute above the
  declaration for some lemmas and inline for others, so `grep "@\[simp\] lemma foo"` reports
  "not simp" for a lemma that is. (`entropy_zero_measure`, `condEntropy_zero_measure` and
  `condMutualInfo_zero_measure` are all `@[simp]`, so a bare `simp` discharges the `μ = 0`
  branch of an `IsZeroOrProbabilityMeasure` proof.) Grep the name and read the preceding line.
- **`FiniteEntropyOf` instance search times out on a literal constant lambda** where the same
  goal on a named `def` is instant: `FiniteEntropyOf (fun _ : ℕ × ℕ ↦ PUnit.unit) geomPair` hits
  the 20000-heartbeat `synthInstance` limit, while `FiniteEntropyOf triv geomPair` with
  `def triv : ℕ × ℕ → Unit := fun _ ↦ ()` succeeds immediately. It bites when a
  `measurable_const` argument fixes the variable to the eta-expanded lambda before the expected
  type is unified; pin the variable by name, e.g.
  `ShannonInformation.condMutualInfo_eq (Z := triv) …`.

## Calibration

Phase 1: 712 lines of Lean (Summable 228 / Defs 360 / Pi 124, a third docstrings) + 165 lines of
tests; plumbing multiplier over the scratch core ≈ 2–2.5× (plan guessed 3–5×); wall clock < 1 h
with three parallel agents.

Phase 2 (`ChainRule.lean`): ≈ 345 lines, a ≈ 3× multiplier over the scratch core — the plan's
upper guess, and higher than Phase 1's, because deriving the Bochner integrability was the work.

Phase 3 (`Inequalities.lean`): ≈ 825 lines, including the local chain rule that Phase 4a then
deleted (the file is 675 lines after that deletion). The "C4" equality case — the one piece
the plan flagged as having no calibration behind it — cost ≈ 40 lines given the gap
decomposition already in hand. It was nearly free; the
contingency of deferring it was never needed.

Phase 4a (`Derived.lean`): ≈ 300 lines, essentially all docstring and rewrite chains, and every
one of its ten lemmas compiled on the first attempt. Treat "a rewrite chain over Phases 2–3" as a
reliable estimate, not an optimistic one.

`tsum_mul_log_div_nonneg` (the countable Gibbs inequality, "C3") still has **no consumer** in the
layer: subadditivity went through the termwise pair bound instead. Do not assume the abstract
core is fully load-bearing when planning further work.
