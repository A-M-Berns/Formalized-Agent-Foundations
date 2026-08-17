# Generalizing the Shannon substrate from finite range to countable range with finite entropy

**Status:** research/planning note. No Lean was written into the repo for this; the
calibration experiments live in a scratch directory (paths given in §3) and are
reproduced inline. Nothing here is committed as a decision — it is input to Anson's
ruling on `dd:finite-range`.

**Date:** 2026-08-17. **Substrate pin:** PFR `01c9b666945eaf73b3f7d8b20ffe003f8640e630`,
Mathlib `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` (`v4.31.0`), toolchain
`leanprover/lean4:v4.31.0` (from `lake-manifest.json`, `lean-toolchain`).

---

## TL;DR

**Estimate: ~1,500–2,400 lines of new FAF-authored Lean, 2–4 focused weeks.** That is
roughly 25–40% of the vendored PFR tree (6,071 lines; 2,853 in the four entropy-core
files), not "comparable in size to the vendored library itself" as `SCOPE.md` §5
currently says. `SCOPE.md`'s cost estimate is too pessimistic and should be corrected.

The evidence for the lower estimate is direct: I proved the three lemmas that carry the
whole mathematical content of the generalization — entropy monotonicity under grouping,
the local chain rule, and countable Gibbs — in **~90 lines total, in about half an hour**,
against the pinned Mathlib, with no `sorry` (§3, verbatim sources reproduced). None of
them needs Jensen's inequality, an exhaustion argument, or any new analysis. Mathlib's
`Real.negMulLog_le_one_sub_self` and `Real.log_le_sub_one_of_pos` do all the work
termwise, and the entropy series of a probability measure has **nonnegative terms**, so
every `tsum` rearrangement is a monotone one. The "new mathematics" is a weekend; the
measure-theoretic plumbing around it is the actual project.

**Recommendation: do not fund the generalization now. Proceed with Condensation under
`dd:finite-range`, and take three cheap hedges (≈half a day, §7 Phase 0).** Rationale:

1. Nothing in the paper becomes *false* under finite range, and no theorem's *content*
   changes — only the class of models quantified over shrinks (§6).
2. `dd:bundled-model` already concentrates the entire narrowing into **one field of
   `RVModel`**. No statement of Def 3.5–Cor 5.10 mentions `FiniteRange`. So the later
   swap is a one-field edit plus re-proof, not a restatement of 42 nodes. The
   hypothesis-agnostic surface the task asks about is *already* the plan.
3. No upstream help is coming and none is imminent (§2), so the work will not become
   free by waiting — but it also will not get *harder*, and a second consumer (Natural
   Latents) may sharpen what is actually needed.

Escalate to Phases 1–3 if, and only if, (a) an audit round rules the type-(c) narrowing
unacceptable for Def 3.1's "countable discrete probability space with finite entropy", or
(b) a second FAF paper needs the same generality.

---

## 1. Exact dependency inventory

### 1.0 What Condensation actually needs

From `Condensation/notes/roadmap.md` (milestone M2+ and the `dd:` glossary), the entropy
endpoints the paper's proofs consume:

| Need (roadmap) | Vendored endpoint | Line | Hypothesis today |
| --- | --- | --- | --- |
| chain rules over linear extensions of an inclusion order (Thm 4.9, 4.15, 5.8) | `chain_rule`, `chain_rule'`, `chain_rule''` | `Entropy/Basic.lean:574`, `:547`, `:580` | `[FiniteRange X] [FiniteRange Y]` |
| conditional chain rule (Lemma 5.4, Thm 5.8) | `cond_chain_rule`, `cond_chain_rule'` | `:635`, `:618` | `[FiniteRange X] [FiniteRange Y] [FiniteRange Z]` |
| subadditivity (Prop 4.2, Cor 4.6) | `entropy_pair_le_add` | `:739` | `[FiniteRange X] [FiniteRange Y]` |
| `H[X\|Y] ≤ H[X]` (scores σ/χ/ϱ monotonicity) | `condEntropy_le_entropy` | `:1075` | `[FiniteRange X] [FiniteRange Y]` |
| submodularity (Lemma 5.4 (5.5)) | `entropy_submodular`, `entropy_triple_add_entropy_le` | `:1080`, `:1110` | three `FiniteRange` |
| nonneg CMI (Lemma 5.4, Cor 5.9) | `condMutualInfo_nonneg`, `mutualInfo_nonneg` | `:921`, `:725` | `[FiniteRange X] [FiniteRange Y]` |
| `I = 0 ⟺` (conditional) independence (Thm 4.9, Ex 4.4) | `mutualInfo_eq_zero`, `condMutualInfo_eq_zero`, `entropy_pair_eq_add` | `:744`, `:1035`, `:769` | two/three `FiniteRange` |
| `I[X:Y\|Z]` decompositions (`dd:interaction`, Lemma 5.4) | `condMutualInfo_eq`, `condMutualInfo_eq'` | `:938`, `:953` | `[FiniteRange Z]` / all three |
| data processing (Prop 4.7, Lemma 4.14) | `entropy_comp_le`, `mutual_comp_le`, `condEntropy_comp_self` | `:643`, `:1144`, `:612` | `[FiniteRange X]` (+ `Y`) |
| pullback invariance, eq. (2.2) (`dd:pullback`) | `IdentDistrib.entropy_congr`, `.mutualInfo_eq`, `.condEntropy_eq` | `:77`, `:692`, `:587` | free / free / four `FiniteRange` |
| `H(Y\|X)=0 ⟹` a.e. function-of (**Prop 2.5**) | **absent upstream** — FAF must prove it | — | (nearest: `const_of_nonpos_entropy`, `:314`, `[FiniteRange X]`) |
| interaction information (`dd:interaction`) | FAF-authored `def` over `mutualInfo`/`condMutualInfo` | — | inherits from its inputs |

Note the last-but-one row: **PFR has no `H[X|Y] = 0 ↔ X is a.e. a function of Y`.**
Prop 2.5 is FAF-authored no matter which fragment we work in, and (see §3) its natural
proof is a `tsum` argument that is *already* general — it never wanted `FiniteRange`.

### 1.1 Where finiteness actually enters, by layer

The vendored tree has three layers and the hypothesis has a different character in each.

**Layer A — definitions. Already general, verified.**

```lean
-- PFR/ForMathlib/Entropy/Measure.lean:47-49
noncomputable
def measureEntropy (μ : Measure S := by volume_tac) : ℝ :=
  ∑' s, negMulLog (((μ Set.univ)⁻¹ • μ).real {s})
```

`entropy X μ = Hm[μ.map X]` (`Entropy/Basic.lean:47-49`); `condEntropy X Y μ =
(μ.map Y)[fun y ↦ H[X | Y ← y ; μ]]` (`Entropy/Basic.lean:360-362`), a **Bochner
integral**; `Kernel.entropy κ μ = μ[fun y ↦ Hm[κ y]]` (`Entropy/Kernel/Basic.lean:37-38`),
also a Bochner integral. `entropy_eq_sum` (`Basic.lean:104`) already states
`H[X;μ] = ∑' x, negMulLog ((μ.map X).real {x})` with no finiteness hypothesis.

So the definitions denote the right thing. **Two traps, not one.** `SCOPE.md` §3 names the
`∑' = 0`-on-non-summable trap; there is a second, identical in character: Lean's Bochner
integral is `0` for a non-integrable function, so `H[X | Y ; μ]` for a variable with
non-integrable conditional entropy is also silently `0`. Both must be closed by an
explicit hypothesis in any generalized statement.

**Layer B — the measure layer (`Entropy/Measure.lean`, 806 lines, 28 `FiniteSupport`
occurrences).** Two facts carry everything:

- `measureEntropy_prod` (`Measure.lean:471`), `[FiniteSupport μ] [FiniteSupport ν]`. Its
  own docstring at `:469` reads *"An ambitious goal would be to replace FiniteSupport with
  finite entropy."* The proof is a `Finset.sum_product` rearrangement over `A ×ˢ B` where
  `A = μ.support`, `B = ν.support` — pure `Finset` bookkeeping, no analysis.
- `measureMutualInfo_nonneg_aux` (`Measure.lean:581–777`, ~197 lines), `[FiniteSupport μ]`,
  which yields `measureMutualInfo_nonneg` (`:779`) and `measureMutualInfo_eq_zero_iff`
  (`:786`). Same docstring at `:579`: *"An ambitious goal would be to replace FiniteSupport
  with finite entropy. Proof is long and slow; needs to be optimized"*. The mathematical
  content is exactly two lines, `Measure.lean:740` and `:742`:

  ```lean
  exact concaveOn_negMulLog.le_map_sum hw1 hw2 hf
  refine (strictConcaveOn_negMulLog.map_sum_eq_iff' hw1 hw2 hf).trans ?_
  ```

  i.e. **finite Jensen** applied to weights `w p = p_X(p.1) * p_Y(p.2)` and values
  `f p = (w p)⁻¹ * μ.real {p}`. The other ~195 lines construct the finite support
  rectangle `E1 ×ˢ E2` and prove the marginals live on it. `FiniteSupport` is load-bearing
  *only* because Mathlib's Jensen (`ConcaveOn.le_map_sum`) is `Finset`-indexed.

**Layer C — the kernel layer (`Entropy/Kernel/Basic.lean` 27 uses,
`Kernel/MutualInfo.lean` 17 uses, plus 1 in `Mathlib/Probability/Kernel/Disintegration.lean`).**
This is where the chain rule lives:

- `Kernel.chain_rule` (`Kernel/Basic.lean:333-340`) `[FiniteSupport μ]` +
  `AEFiniteKernelSupport κ μ`, proved from `disintegration κ` and `entropy_compProd`.
- `entropy_compProd` (`:291`) → `entropy_compProd'` (`:277`) → `entropy_compProd_aux`
  (`:220`), a ~60-line `Finset` computation over `local_support_of_finiteKernelSupport`
  sets, plus `integrable_of_finiteSupport` (`Measure.lean:151`) to justify
  `Measure.integral_compProd`.
- Measure-level `chain_rule'` (`Basic.lean:547-570`) routes *through* this: it rewrites to
  `Kernel.chain_rule` with `Kernel.const Unit (μ.map ⟨X,Y⟩)` and discharges the kernel
  support obligation with `Kernel.finiteKernelSupport_of_const`, which needs
  `FiniteSupport (μ.map ⟨X,Y⟩)`, which is what `FiniteRange` supplies via
  `finiteSupport_of_finiteRange` (`Measure.lean:139`).

**This is the single most important architectural fact in this report:** for the
measure-level chain rule the kernel detour is *pure overhead*. The kernel is a constant
kernel over `Unit`. Nothing about kernels is needed to prove `H[X,Y] = H[X] + H[Y|X]` for
countable-discrete variables; PFR routes through kernels because PFR needs the kernel
version for its own conditional machinery elsewhere.

### 1.2 Classification

**(a) Already general — no work.** `entropy_nonneg` (`:74`), `measureEntropy_nonneg`
(`Measure.lean:281`), `entropy_congr` (`:70`), `IdentDistrib.entropy_congr` (`:77`),
`entropy_comm` (`:338`), `entropy_assoc` (`:344`), `entropy_prod_comp` (`:331`),
`entropy_comp_of_injective` (`:160`), `condEntropy_nonneg` (`:420`), `mutualInfo_def`
(`:684`), `condMutualInfo_def` (`:705`), `condMutualInfo_comm` (`:930`),
`IdentDistrib.mutualInfo_eq` (`:692`), `entropy_eq_sum` (`:104`), `entropy_le_log_card`
(`:82`, needs `Fintype S` — a different and unavoidable hypothesis, since the bound is
`log |S|`), `measureMutualInfo_swap` (`Measure.lean:557`). This matches `SCOPE.md` §4 and
I re-verified each against the source.

**(b) Generalizes by routine `tsum` bookkeeping once (c) is done — no new ideas.** Every
one of these is a `rw` chain over a small number of load-bearing facts:

- `mutualInfo_nonneg` (`:725`): its entire proof is two `Measure.map_map` congruences plus
  `exact measureMutualInfo_nonneg`. Generalize `measureMutualInfo_nonneg` and this follows
  verbatim.
- `entropy_pair_le_add` (`:739`): one line, `sub_nonneg.1 <| mutualInfo_nonneg ...`.
- `condMutualInfo_nonneg` (`:921`): `integral_nonneg (fun z ↦ mutualInfo_nonneg ...)`.
  Pointwise; needs nothing beyond the above.
- `mutualInfo_eq_zero` (`:744`): needs `measureMutualInfo_eq_zero_iff` and
  `Measure.ext_iff_measureReal_singleton_finiteSupport` (`Measure.lean:213`). The latter
  has a *general* Mathlib replacement, verified: `MeasureTheory.Measure.ext_of_singleton :
  [Countable α] → (∀ a, μ {a} = ν {a}) → μ = ν`.
- `entropy_pair_eq_add` (`:769`), `mutualInfo_const` (`:763`),
  `mutualInfo_eq_entropy_sub_condEntropy` (`:824`) and its three siblings,
  `entropy_sub_condEntropy` (`:1070`), `condEntropy_le_entropy` (`:1075`),
  `entropy_triple_add_entropy_le` (`:1110`), `condMutualInfo_eq'` (`:953`),
  `entropy_comp_le` (`:643`), `entropy_of_comp_eq_of_comp` (`:659`), `condEntropy_comp_self`
  (`:612`), `condEntropy_comp_ge` (`:1095`), `mutual_comp_le` (`:1144`) and friends,
  `IdentDistrib.condEntropy_eq` (`:587`), `condEntropy_of_injective'` (`:600`): all are
  algebra over the chain rule and `mutualInfo_nonneg`.
- `condMutualInfo_eq_zero` (`:1035`): the only extra ingredient is
  `integrable_of_finiteSupport _` on the last line, discharging integrability of
  `z ↦ I[X : Y ; μ[|Z ← z]]`. Under finite entropy that integrability follows from
  `I[X:Y | Z=z] ≤ H[X | Z=z]` and `∫ H[X|Z=z] = H[X|Z] ≤ H[X] < ∞`.
- `condEntropy_eq_sum` (`:434`), `condMutualInfo_eq_sum` (`:891`): `Finset` sums become
  `tsum`s via verified `MeasureTheory.integral_countable : [Countable X]
  [MeasurableSingletonClass X] → Integrable f μ → ∫ x, f x ∂μ = ∑' x, μ.real {x} • f x`.

**(c) Needs genuinely new mathematics — three lemmas, all proved in §3.**

| # | Fact | Replaces | Why it is the real content |
| --- | --- | --- | --- |
| C1 | grouping bound `negMulLog (∑' t, p t) ≤ ∑' t, negMulLog (p t)` | nothing (new) | gives `H[X] ≤ H[⟨X,Y⟩]`, `H[f∘X] ≤ H[X]`, and **the summability transfer that makes `FiniteEntropy` compose** |
| C2 | local chain rule `∑' t, negMulLog (p t) = negMulLog P + P * ∑' t, negMulLog (p t / P)` | `entropy_compProd_aux` (`Kernel/Basic.lean:220`) | the whole chain rule, without kernels |
| C3 | countable Gibbs `0 ≤ ∑' i, p i * log (p i / q i)` | `concaveOn_negMulLog.le_map_sum` (`Measure.lean:740`) | subadditivity / `mutualInfo_nonneg`; replaces Jensen with a termwise bound |

A fourth, C4, the **equality case** of C3 (`I = 0 ↔ p = p_X ⊗ p_Y` a.e.), replacing
`strictConcaveOn_negMulLog.map_sum_eq_iff'` (`Measure.lean:742`). I did **not** prove
this one; it is the residual risk (§7 Phase 3). Sketch: in C3 the inequality is termwise,
so `∑ = 0` forces `p i log(p i / q i) = p i - q i` for every `i`, and
`log t = t - 1 ↔ t = 1` (`Real.log_lt_sub_one_of_ne` / `negMulLog_lt_one_sub_self`,
strict for `t ≠ 1`) forces `p i = q i` pointwise — arguably *easier* than the finite
Jensen equality case, because it never leaves the termwise world. Unverified.

---

## 2. What is available upstream, today

### 2.1 The pinned Mathlib (verified in this session)

Every name below was `#check`ed against `.lake/packages/mathlib` at the pinned commit.
Scratch files: `.../entropy-derisk/Check1.lean`, `Check2.lean`, `Check4.lean`.

**Verified present:**

```lean
Real.negMulLog_le_one_sub_self : ∀ {x : ℝ}, 0 ≤ x → x.negMulLog ≤ 1 - x
Real.self_sub_one_le_mul_log   : ∀ {x : ℝ}, 0 ≤ x → x - 1 ≤ x * log x
Real.log_le_sub_one_of_pos     : ∀ {x : ℝ}, 0 < x → log x ≤ x - 1
Real.negMulLog_mul (x y : ℝ)   : (x * y).negMulLog = y * x.negMulLog + x * y.negMulLog
Real.concaveOn_negMulLog       : ConcaveOn ℝ (Set.Ici 0) negMulLog
Real.strictConcaveOn_negMulLog : StrictConcaveOn ℝ (Set.Ici 0) negMulLog
Real.negMulLog_nonneg          : 0 ≤ x → x ≤ 1 → 0 ≤ x.negMulLog
ConcaveOn.le_map_sum           -- Finset-indexed Jensen
ConcaveOn.le_map_integral      -- measure-theoretic Jensen, [IsProbabilityMeasure μ]
StrictConcaveOn.ae_eq_const_or_lt_map_average  -- its strict/equality companion
Summable.tsum_le_tsum, Summable.sum_le_tsum, Summable.tsum_le_of_sum_le,
Summable.of_nonneg_of_le, Summable.tsum_eq_zero_iff, Summable.tsum_le_tsum_of_inj,
Summable.tsum_add, Summable.le_tsum, Summable.tsum_mul_left, Summable.tsum_mul_right,
Summable.tsum_sub, tsum_le_of_sum_le, tsum_nonneg, tsum_congr
MeasureTheory.integral_countable :
  [MeasurableSingletonClass X] [Countable X] → Integrable f μ →
    ∫ x, f x ∂μ = ∑' x, μ.real {x} • f x
MeasureTheory.Measure.ext_of_singleton :
  [Countable α] → (∀ a, μ {a} = ν {a}) → μ = ν
InformationTheory.klDiv (μ ν : Measure α) : ℝ≥0∞      -- irreducible_def
InformationTheory.klDiv_eq_zero_iff : klDiv μ ν = 0 ↔ μ = ν   -- [IsFiniteMeasure] both
InformationTheory.integral_llr_add_sub_measure_univ_nonneg :
  μ ≪ ν → Integrable (llr μ ν) μ → 0 ≤ ∫ x, llr μ ν x ∂μ + ν.real univ - μ.real univ
```

**Verified absent** (do not cite these): bare `tsum_le_tsum`, bare `sum_le_tsum`,
`integral_countable'` (deprecated alias only), `MeasureTheory.integrable_countable`,
`HasSum.integral_eq`, `Summable.tsum_prod`, `Summable.tsum_div_const`,
`InformationTheory.klDiv_nonneg` (nonnegativity is definitional, the codomain is `ℝ≥0∞`).

Note the pinned Mathlib has undergone the `SummationFilter` refactor: `∑'[L]` and
`Summable f L`. This is why `tsum_le_tsum` moved to `Summable.tsum_le_tsum`. Any
generalization must be written against that API, not against pre-refactor tutorials.

**Correction to `SCOPE.md` §6.** `SCOPE.md` says *"`klDiv` is `EReal`-valued while PFR's
entropy is `ℝ`-valued."* At this pin it is `ℝ≥0∞`-valued
(`Mathlib/InformationTheory/KullbackLeibler/Basic.lean:57`), not `EReal`. That should be
fixed.

**No summable-family entropy, no `tsum`-form Gibbs, no log-sum inequality, no
`Summable` lemmas about `negMulLog` families exist anywhere in Mathlib.** `negMulLog`
appears in exactly two Mathlib files (`Analysis/SpecialFunctions/Log/NegMulLog.lean`,
`Analysis/SpecialFunctions/BinaryEntropy.lean`); the string `Summable` appears in
neither. Jensen exists only in `Finset` form (`Analysis/Convex/Jensen.lean`) and integral
form (`Analysis/Convex/Integral.lean`) — there is no infinite-sum Jensen.

### 2.2 Mathlib master (researched; not `#check`ed — treat as unverified)

`Mathlib/InformationTheory/` on master today contains exactly `Coding/KraftMcMillan.lean`,
`Coding/UniquelyDecodable.lean`, `Hamming.lean`, and `KullbackLeibler/{Basic, ChainRule,
DataProcessing, KLFun}.lean`. **There is no Shannon entropy in Mathlib — no
`measureEntropy`, no entropy of a random variable, no mutual information.** The only
"entropy" is scalar `binEntropy`/`qaryEntropy` (`Analysis/SpecialFunctions/BinaryEntropy.lean`)
and topological entropy in `Dynamics/`.

Delta from our pin: master adds `KullbackLeibler/DataProcessing.lean` (PR #35349, merged
2026-07-27: `klDiv_map_le`, `klDiv_trim_le`, `klDiv_comp_right_le`). `Basic.lean` differs
by 53 bytes, cosmetic. Nothing relevant to entropy.

Open Mathlib PRs mentioning entropy: exactly one (#41523, a `binEntropy` scalar lemma).
Rémy Degenne's active work is on the divergence side (total variation #27579/#37730,
Hellinger affinity #41517). The historical `RD_entropy` branch (Nov 2023, the design that
became PFR's `ForMathlib/Entropy`) never landed and is three years stale. **There is no
PFR-entropy upstreaming effort in flight.**

### 2.3 PFR master

**Byte-identical to our pin.** `PFR/ForMathlib/Entropy/Basic.lean` has blob sha
`6c98a025214dac68a90c4d2a3b0c3ddf92378a28`, size 57553, at both `01c9b666` and `master`.
`chain_rule`, `chain_rule'`, `mutualInfo_nonneg`, `condMutualInfo_nonneg`,
`entropy_pair_le_add`, `entropy_submodular`, `mutualInfo_eq_zero`, `condEntropy_le_entropy`
all still carry `[FiniteRange …]`. `FiniteRange/Defs.lean` unchanged. No `FiniteEntropy`
class exists anywhere in PFR's 74 `.lean` files.

The only trace of the intent is in our own vendored copy, `Entropy/Measure.lean:99-102`:

```lean
/-- TODO: replace FiniteSupport hypotheses ∈ these files with FiniteEntropy hypotheses. -/
noncomputable def FiniteEntropy (μ : Measure S := by volume_tac) : Prop :=
  Summable (fun s ↦ negMulLog (((μ Set.univ)⁻¹ • μ) {s}).toReal) ∧
  ∃ A : Set S, Countable A ∧ μ Aᶜ = 0
```

I grepped the whole vendored tree: **`FiniteEntropy` is defined and never used, not once.**
It is a two-year-old aspiration marker. That is a useful data point in both directions —
Tao et al. agree this is the right hypothesis, and nobody has done it.

One thing PFR has that Mathlib does not, and that our closure does **not** vendor (the
directory `PFR/Mathlib/Analysis/SpecialFunctions/` is absent from `PFR/` here): the
`Finset` log-sum inequality `sum_mul_log_div_leq` with its equality characterizations. If
a future generalization wants that shape, it is upstream and re-derivable, but it is a
`Finset` statement and C3 below supersedes it.

---

## 3. The mathematical core — proved, not sketched

Scratch directory:
`/private/tmp/claude-501/-Users-anson/9e8dd8b4-3155-47c3-a824-a5d82971ed8f/scratchpad/entropy-derisk/`
(`Key1.lean`, `Key2.lean`, `Key3.lean`, `Design.lean`, `Check{1,2,3,4}.lean`). All compile
under `lake env lean` against the pinned toolchain, `sorry`-free except `Design.lean`,
which is a statement-elaboration sketch.

**The organising observation, which is what makes this cheap:** for a probability measure,
every term `negMulLog (p s)` of the entropy series is **nonnegative** (`p s ∈ [0,1]`,
`Real.negMulLog_nonneg`). There is therefore **no sign-splitting problem at all**. Every
`tsum` in sight is a sum of nonnegative reals; summability is exactly boundedness of the
partial sums; `Summable.of_nonneg_of_le` is the workhorse; and monotone rearrangement is
free. `SCOPE.md` §5's proposed "limiting argument over an exhausting sequence of finite
sets" is *not* needed and would be the harder route.

### C1 — grouping bound (`Key1.lean`, 30 lines, compiles)

This is `H[X] ≤ H[⟨X,Y⟩]` and `H[f ∘ X] ≤ H[X]` in atomic form, and it is the lemma that
makes `FiniteEntropy` *compose*.

```lean
theorem negMulLog_tsum_le {T : Type*} (p : T → ℝ)
    (h0 : ∀ t, 0 ≤ p t) (hsum : Summable p)
    (hent : Summable (fun t ↦ negMulLog (p t))) :
    negMulLog (∑' t, p t) ≤ ∑' t, negMulLog (p t) := by
  set P := ∑' t, p t with hP
  have hP0 : 0 ≤ P := tsum_nonneg h0
  rcases eq_or_lt_of_le hP0 with h | hpos
  · have hall : ∀ t, p t = 0 := fun t ↦ by
      simpa using le_antisymm (h ▸ hsum.le_tsum t (fun j _ ↦ h0 j)) (h0 t)
    simp [negMulLog, ← h, hall]
  · have key : ∀ t, p t * (-Real.log P) ≤ negMulLog (p t) := by
      intro t
      rcases eq_or_lt_of_le (h0 t) with ht | ht
      · simp [negMulLog, ← ht]
      · have hpt : p t ≤ P := hsum.le_tsum t (fun j _ ↦ h0 j)
        have : Real.log (p t) ≤ Real.log P := Real.log_le_log ht hpt
        simp only [negMulLog, neg_mul]; nlinarith [ht.le]
    calc negMulLog P = (∑' t, p t) * (-Real.log P) := by simp [negMulLog, hP]
      _ = ∑' t, p t * (-Real.log P) := (hsum.tsum_mul_right _).symm
      _ ≤ ∑' t, negMulLog (p t) := Summable.tsum_le_tsum key (hsum.mul_right _) hent
```

(The `hle : ∑' t, p t ≤ 1` hypothesis I initially wrote turned out to be unnecessary — the
linter flagged it as unused.)

### C2 — local chain rule (`Key2.lean`, 32 lines, compiles)

This replaces the ~60-line `Finset` computation in `entropy_compProd_aux`
(`Kernel/Basic.lean:220`) *and* removes the kernel detour entirely.

```lean
lemma negMulLog_div (p P : ℝ) (h0 : 0 ≤ p) (hP : 0 < P) :
    negMulLog (p / P) = P⁻¹ * negMulLog p + p * (Real.log P * P⁻¹) := by
  rcases eq_or_lt_of_le h0 with h | h
  · simp [negMulLog, ← h]
  · rw [negMulLog, negMulLog, Real.log_div (ne_of_gt h) (ne_of_gt hP)]; field_simp; ring

theorem row_chain_rule {T : Type*} (p : T → ℝ) (h0 : ∀ t, 0 ≤ p t)
    (hsum : Summable p) (hent : Summable fun t ↦ negMulLog (p t))
    (hP : 0 < ∑' t, p t) :
    (∑' t, negMulLog (p t))
      = negMulLog (∑' t, p t) + (∑' t, p t) * ∑' t, negMulLog (p t / (∑' t, p t)) := by
  set P := ∑' t, p t with hPdef
  have hPne : P ≠ 0 := ne_of_gt hP
  have hid : ∀ t, negMulLog (p t / P) = P⁻¹ * negMulLog (p t) + p t * (Real.log P * P⁻¹) :=
    fun t ↦ negMulLog_div _ _ (h0 t) hP
  have hs1 : Summable fun t ↦ P⁻¹ * negMulLog (p t) := hent.mul_left _
  have hs2 : Summable fun t ↦ p t * (Real.log P * P⁻¹) := hsum.mul_right _
  have key : (∑' t, negMulLog (p t / P))
      = P⁻¹ * (∑' t, negMulLog (p t)) + P * (Real.log P * P⁻¹) := by
    rw [tsum_congr hid, hs1.tsum_add hs2, hent.tsum_mul_left, hsum.tsum_mul_right]
  rw [key, negMulLog]; field_simp; ring
```

Summing this over the first coordinate, with `ENNReal.tsum_prod`/`Summable`-indexed
Fubini for nonnegative families, is the measure-level chain rule. The conditional-entropy
side is bridged by the verified `MeasureTheory.integral_countable`.

### C3 — countable Gibbs (`Key3.lean`, 28 lines, compiles)

This replaces `concaveOn_negMulLog.le_map_sum` at `Measure.lean:740`. It is a **termwise**
bound: no Jensen, no convexity, no exhaustion.

```lean
theorem tsum_mul_log_div_nonneg {ι : Type*} (p q : ι → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hq0 : ∀ i, 0 ≤ q i)
    (hac : ∀ i, q i = 0 → p i = 0)
    (hpsum : Summable p) (hqsum : Summable q)
    (hsum : Summable fun i ↦ p i * Real.log (p i / q i))
    (hmass : ∑' i, q i ≤ ∑' i, p i) :
    0 ≤ ∑' i, p i * Real.log (p i / q i) := by
  have term : ∀ i, p i - q i ≤ p i * Real.log (p i / q i) := by
    intro i
    rcases eq_or_lt_of_le (hp0 i) with hpi | hpi
    · simp [← hpi]; exact hq0 i
    · have hqi : 0 < q i := lt_of_le_of_ne (hq0 i) (fun h ↦ absurd (hac i h.symm) (ne_of_gt hpi))
      have h1 : Real.log (q i / p i) ≤ q i / p i - 1 := Real.log_le_sub_one_of_pos (by positivity)
      have h2 : Real.log (q i / p i) = - Real.log (p i / q i) := by
        rw [← Real.log_inv]; congr 1; field_simp
      rw [h2] at h1
      have := mul_le_mul_of_nonneg_left h1 hpi.le
      field_simp at this; nlinarith
  calc (0:ℝ) ≤ ∑' i, p i - ∑' i, q i := by linarith
    _ = ∑' i, (p i - q i) := (hpsum.tsum_sub hqsum).symm
    _ ≤ ∑' i, p i * Real.log (p i / q i) :=
        Summable.tsum_le_tsum term (hpsum.sub hqsum) hsum
```

Instantiate at `ι := S × T`, `p := p_{XY}`, `q := p_X ⊗ p_Y` and you get
`H[⟨X,Y⟩] ≤ H[X] + H[Y]`, hence `mutualInfo_nonneg`, hence (via the (b) chain)
`condMutualInfo_nonneg`, `entropy_submodular`, `entropy_triple_add_entropy_le`,
`condEntropy_le_entropy`, and data processing.

### The single hardest lemma

**It is not any of C1–C3.** With those in hand, the hardest remaining item is C4, the
equality case (`I[X:Y] = 0 ↔ IndepFun X Y`), and specifically the "only if" direction with
its a.e. qualifiers. Stated precisely (elaborated in `Design.lean`, no proof attempted):

```lean
theorem mutualInfo_eq_zero (hX : Measurable X) (hY : Measurable Y)
    [FiniteEntropyOf X μ] [FiniteEntropyOf Y μ] :
    I[X : Y ; μ] = 0 ↔ IndepFun X Y μ
```

Two routes, both plausible, neither verified:
1. **Termwise**, from C3: equality in `∑' (p i - q i) ≤ ∑' p i log(p i / q i)` with a
   termwise-dominated pair of summable families forces equality in every term
   (`Summable.tsum_eq_zero_iff` on the nonnegative difference family), and
   `log t = t - 1 ↔ t = 1` (via `Real.negMulLog_lt_one_sub_self`, strict for `x ≠ 1`)
   forces `p i = q i` pointwise. Then `Measure.ext_of_singleton` (verified) finishes.
   This never leaves the termwise world and I expect it to be *shorter* than PFR's.
2. **Measure-theoretic Jensen**, via the verified
   `StrictConcaveOn.ae_eq_const_or_lt_map_average` on the product measure. Structurally
   parallel to `Measure.lean:742` but with an a.e.-qualified conclusion.

I recommend route 1. If it stalls, route 2 is the fallback and route 3 is
"keep `mutualInfo_eq_zero` at `FiniteRange` and generalize only the inequalities" — the
paper needs the ⟸ direction (independence ⟹ `I=0`) far more than ⟹.

### On the `ℝ≥0∞` alternative

A tempting design is to define `measureEntropy∞ : Measure S → ℝ≥0∞` and prove the chain
rule there unconditionally (`ENNReal.tsum_prod`, `ENNReal.tsum_add`, `ENNReal.tsum_mul_left`
are all hypothesis-free), then transfer to `ℝ` under finiteness. It works — the terms are
nonnegative, so `ENNReal.ofReal ∘ negMulLog` loses nothing — and it removes every
summability side condition from the *statements*. I did not pursue it because it
introduces a second entropy definition alongside the vendored one, and the API README's
"no wrapper ontology" rule is a good rule. But it is the right fallback if the `ℝ`-side
summability bookkeeping turns out worse than §3 suggests, and it should be reconsidered at
the start of Phase 2 rather than discovered at the end of it.

---

## 4. Design

### 4.1 The class

`Design.lean` elaborates cleanly against `ShannonInformation.API` (targeted extra import
`Mathlib.Topology.Algebra.InfiniteSum.Order`; no shim clash):

```lean
/-- A measure has finite entropy when the defining series of `Hm[μ]` actually converges. -/
class FiniteEntropyMeasure (μ : Measure S) : Prop where
  summable : Summable fun s ↦ negMulLog (((μ Set.univ)⁻¹ • μ).real {s})

/-- A random variable has finite entropy when its law does. -/
abbrev FiniteEntropyOf (X : Ω → S) (μ : Measure Ω) : Prop := FiniteEntropyMeasure (μ.map X)
```

Design notes:

- **Track `measureEntropy`'s definition verbatim.** The summand is exactly the summand of
  `measureEntropy` (`Measure.lean:47-49`), including the `(μ Set.univ)⁻¹ •` normalisation.
  That way `FiniteEntropyMeasure μ ↔ (the series defining `Hm[μ]` converges)` is true by
  construction and no bridge lemma is needed. PFR's unused `FiniteEntropy`
  (`Measure.lean:100`) uses `.toReal` on the `ℝ≥0∞` measure rather than `.real`; those are
  the same function but `Measure.real` is the idiom the rest of the file uses.
- **Drop PFR's countability conjunct.** PFR's `FiniteEntropy` also demands
  `∃ A : Set S, Countable A ∧ μ Aᶜ = 0`. For our consumers the *value type* is already
  `Countable`, which is a typeclass hypothesis everywhere in the vendored API anyway, so
  the conjunct is redundant and only makes the class harder to instantiate. Keep it as a
  separate hypothesis if a consumer ever needs an uncountable value type with countable
  support.
- **A `Prop`-valued class, not a bundled structure**, so it participates in instance
  resolution and `variable [FiniteEntropyOf X μ]` reads like `[FiniteRange X]`.

### 4.2 Coexistence with `FiniteRange` — verified

```lean
instance (priority := 100) finiteEntropy_of_finiteSupport
    [MeasurableSingletonClass S] (μ : Measure S) [FiniteSupport μ] : FiniteEntropyMeasure μ

instance (priority := 100) finiteEntropy_of_finiteRange
    [MeasurableSingletonClass S] {X : Ω → S} (μ : Measure Ω) [FiniteRange X] :
    FiniteEntropyOf X μ
```

and the following `example` **elaborates and resolves by `infer_instance`** in
`Design.lean`:

```lean
example {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    {Ω : Type*} [MeasurableSpace Ω] (X : Ω → S) (mu : Measure Ω) :
    ShannonInformation.FiniteEntropyOf X mu := by infer_instance
```

So the existing `FiniteRange` instance graph (`FiniteRange/Defs.lean` — `Finite G`,
constants, `f ∘ X`, `X ∘ f`, pairs, `mul`/`div`/`inv`/`zpow`/`finprod`) feeds the new
class for free. **Every currently-provable Condensation goal stays provable.** The
generalization is strictly additive.

### 4.3 Closure — and the finite/countable product distinction

The four closure lemmas the paper needs, each with its proof route:

| Lemma | Route | Cost |
| --- | --- | --- |
| `FiniteEntropyOf ⟨X,Y⟩ μ → FiniteEntropyOf X μ` | **C1** applied to the fibres `p_X(x) = ∑'_y p(x,y)`; `Summable.of_nonneg_of_le` | cheap |
| `FiniteEntropyOf X μ → FiniteEntropyOf (f ∘ X) μ` | same, fibres of `f` | cheap |
| `FiniteEntropyOf X μ → FiniteEntropyOf Y μ → FiniteEntropyOf ⟨X,Y⟩ μ` | see below | moderate |
| `MeasurePreserving π ν μ → FiniteEntropyOf X μ → FiniteEntropyOf (X ∘ π) ν` | `ν.map (X ∘ π) = μ.map X` definitionally after `Measure.map_map`; the class is a property of the law | free |

**Finite joint products close; countable ones do not.** The paper needs the former (Def
3.1: *"a **finite** family of random variables"*; Def 3.4's `Y_F` is indexed by a subset of
`P⁺I` with `I` finite — see `dd:pplus`), and only the former is true. Proof of the pair
case, termwise, from `Real.log_le_sub_one_of_pos` with `t = p_X(x) p_Y(y) / p(x,y)`:

```
negMulLog p(x,y)  ≤  -p(x,y) log p_X(x)  -  p(x,y) log p_Y(y)  +  p_X(x)p_Y(y)  -  p(x,y)
```

Every family on the right is summable: `∑_{x,y} -p(x,y) log p_X(x) = ∑_x negMulLog p_X(x)
= H[X] < ∞`, symmetrically for `Y`, and `∑ p_X p_Y = ∑ p = 1`. The left side is
nonnegative. `Summable.of_nonneg_of_le` closes it — and the *same* inequality, summed,
**is** subadditivity. Two birds, one termwise bound. Induct for finitely many factors.

The countable case genuinely fails: take `X_n` independent with `H[X_n] = 2^{-n}`;
each is finite-entropy, the joint over all `n` has `H = ∑ 2^{-n}` — fine — but take instead
`H[X_n] = 1` for all `n` and the countable joint has infinite entropy. The closure lemma
must therefore be stated for `Finset`-indexed families, never for `Π i : ι`. Worth an
explicit comment in the source so nobody "generalizes" it later.

### 4.4 Can Condensation's statements be written now, hypothesis-agnostically?

**Yes, and `dd:bundled-model` already achieves it — this is the strongest argument in the
report for deferring.**

Per `roadmap.md`, `RVModel I` bundles "the variables `X i : Ω → R i`, their measurability
and finite range". Consequently:

- No statement of Def 3.5–3.12, §4 (Prop 4.2 … Thm 4.15) or §5 (Lemma 5.4 … Cor 5.10)
  mentions `FiniteRange` at all. They quantify over `RVModel`/`LatentModel`.
- The narrowing lives in **one structure field**. Swapping it later is:
  `finiteRange : ∀ i, FiniteRange (X i)` → `finiteEntropy : ∀ i, FiniteEntropyOf (X i) P`,
  plus (to match Def 3.1 literally) a new field `omegaFiniteEntropy : FiniteEntropyMeasure P`.
- The *proofs* will need updating, because they cite `FiniteRange`-gated PFR lemmas. But
  that is exactly what Phases 1–4 deliver, and the citation sites are the ~20 endpoints in
  §1.0's table, not 42 nodes.

Two concrete hedges make the swap cleaner (Phase 0, §7):

1. Keep the finiteness field **singular and named for its role**, not for its
   implementation — e.g. `finiteness : ∀ i, FiniteRange (X i)` with a docstring saying
   this is the `dd:finite-range` narrowing of Def 3.1's "finite entropy". A field named
   `finiteRange` invites downstream code to destructure it by name.
2. Never take `FiniteRange` as a *hypothesis of a Condensation theorem*. If a lemma needs
   it, get it from the model. Verified as achievable: the roadmap's file layout already
   works this way.

I considered and **reject** a heavier hedge — a `ShannonInformation/Discrete.lean`
interface restating the ~20 needed facts behind an abbreviation `FiniteEnt` that is
currently `FiniteRange`. It costs ~150–250 lines, conflicts with the API README's
"pure re-export, no drift" policy, and buys nothing that the one-field concentration
does not already buy. Recommend against.

---

## 5. Where it should live, and who owns it

Three candidate homes:

**Mathlib — no.** Mathlib has no Shannon entropy at all (§2.2). Landing a
`FiniteEntropy`-parameterised discrete entropy theory would mean landing the whole theory
first. That is a multi-quarter community project with a maintainer-review bottleneck, and
the one person who tried (Degenne, `RD_entropy`, 2023) stopped. Not a route for a paper
formalization on a schedule.

**PFR — the right *eventual* home, the wrong *first* home.** The `TODO` at
`Measure.lean:99` and the two "ambitious goal" docstrings (`:469`, `:579`) say upstream
wants exactly this. But: (i) generalizing *inside* PFR means generalizing the **kernel**
layer, which is 44 `FiniteSupport` occurrences across `Kernel/Basic.lean` and
`Kernel/MutualInfo.lean` plus `Mathlib/Probability/Kernel/Disintegration.lean`, and needs
an `AEFiniteKernelEntropy` analogue with integrability side conditions that `FiniteSupport`
made free (`integrable_of_finiteSupport`, `Measure.lean:151`); (ii) PFR's own consumers
(the polynomial Freiman–Ruzsa proof) are entirely finite, so a generalization is pure cost
to them and will not be prioritised in review; (iii) it puts FAF's schedule behind a
third-party review queue. **Offer it upstream after it exists and is proved**, as a
measure-level module that PFR can adopt at its leisure.

**FAF `ShannonInformation/` — yes, as FAF-authored lemmas.** The README already
provides for this: *"If a genuinely generic convenience lemma turns out to be needed by
more than one client, it belongs here, inside this namespace, marked FAF-authored,
proved (never `sorry`ed), and listed in `ShannonInformation/README.md`."* This is more
than a convenience lemma, so it wants its own module rather than `API.lean`:

```
ShannonInformation/
  API.lean                 -- unchanged; re-export layer, plus `public import` of the below
  FiniteEntropy/
    Summable.lean          -- C1, C2, C3, C4 + abstract nonneg-family bookkeeping (no measures)
    Defs.lean              -- the class, instances, closure lemmas
    Basic.lean             -- measure-level: chain rule, subadditivity, the (b) corpus
```

with `vendor/` and `PFR/` untouched. The split `Summable.lean` / everything-else is
deliberate: the first file is measure-free, fast to compile, easy to audit, and is the
part with a plausible upstream future (it is Mathlib-shaped: `tsum` Gibbs and the
`negMulLog` grouping bound are exactly the kind of thing
`Analysis/SpecialFunctions/Log/NegMulLog.lean` is missing, per §2.1).

**Crucially, this creates a fork risk that must be named:** after Phase 2 the layer will
contain *two* chain rules — PFR's `ProbabilityTheory.chain_rule` at `FiniteRange`, and
`ShannonInformation.chain_rule'` at `FiniteEntropyOf`. Two statements of the same fact,
different hypotheses, one import surface, and an auditor reading a citation has to know
which. Mitigations: (i) namespace discipline — the new ones live in
`ShannonInformation`, never `ProbabilityTheory`; (ii) `README.md` must list every
FAF-authored lemma (it already promises to); (iii) once the general version is proved,
consider *deprecating* the re-export of the narrow one from `API.lean` so clients cannot
accidentally cite it. That last step is what actually retires the fork, and it should be
in the plan from the start, not bolted on.

---

## 6. Cost/benefit — what does Condensation gain?

### 6.1 Nothing in the paper is false or different under finite range

I checked every entropy-bearing statement in the source
(`notes/condensation-25-07.txt`). **No statement of the paper is false under finite range,
and no theorem's mathematical content changes.** Finite range implies finite entropy, so
every quantity the paper asserts to be finite is finite; the inequalities and identities
are the same inequalities and identities. What changes is only the **class of models
quantified over**.

### 6.2 What is affected, node by node

| Node | Effect of `dd:finite-range` | Would generalization change it? |
| --- | --- | --- |
| **Prop 2.5** (`H(Y\|X)=0 ⟹ Y = f(X)` a.e.) | Stated by the paper for "finite entropy and countable discrete range". Under finite range, the proof's step *"Since `R_X` is countable, `A` has full measure"* is trivial. | **Yes, materially.** This is the one node where the paper's hypothesis is *exactly* the general one and finite range is a visible weakening. Its natural proof (all `negMulLog` terms nonnegative summing to zero ⟹ each conditional law is Dirac) is already general — it wants `FiniteEntropyOf`, not `FiniteRange`. Cheapest possible win. |
| **Def 3.1** (random variable model) | The paper says *"a countable discrete probability space Ω **with finite entropy**"*. `dd:finite-range` drops the Ω-entropy hypothesis entirely and replaces the per-variable condition with finite range. | **Yes.** This is the load-bearing narrowing; everything downstream inherits it. Under `FiniteEntropyMeasure P` the hypothesis is verbatim. |
| §3 scores σ, χ, ϱ (3.1–3.3) | The paper's justification is *"All these quantities are finite, since all the random variables of the form `X_i` and `Y_A` have finite entropy"* (line ~274). | No change in content; the justification becomes the paper's own rather than a stronger one. |
| Prop 4.2, Lemma 4.5, Cor 4.6, Prop 4.7, **Thm 4.9**, Prop 4.10 | chain-rule/subadditivity tranche | No content change; narrower quantification only. |
| **Lemma 4.13** (Λ₀ construction, `dd:amalgamation`) | Λ₀ = `{p : Λ₁ × Λ₂ // π₁ p.1 = π₂ p.2}` with `w(λ₁,λ₂) = P₁{λ₁}P₂{λ₂}/P_Ω{π₁λ₁}`. | **Yes, but only as a proof obligation, not as content.** Under the general setting, Def 4.12(1) demands Λ₀ be a *countable discrete probability space* and Def 3.1 demands finite entropy, so one must **prove** `H(Λ₀) < ∞`. That is exactly the §4.3 pair-closure lemma (Λ₀ injects into Λ₁ × Λ₂, so `H(Λ₀) ≤ H(Λ₁) + H(Λ₂)`). Under `dd:finite-range` the obligation does not arise at all — which is a *disclosure* issue, since a reader of the formalization would not see the paper's hypothesis being discharged. |
| Lemma 4.14, **Thm 4.15** | comparison of latent models | No content change. Thm 4.15's `F_i` erratum is orthogonal. |
| **Lemma 5.4**, Def 5.5–5.6, Prop 5.7, **Thm 5.8**, Cor 5.9–5.10 | The paper states Lemma 5.4 for *"random variables on some probability space, each of which has finite entropy"* — no discreteness clause at all in that sentence. | No content change under discreteness. Note the paper is *sloppier* here than elsewhere; §2's blanket "we will generally assume … countable and discrete" is what makes it well-posed. |
| **Ex 5.1, 5.2** (`[0,1]`-valued latent `L`) | Proposed OUT of scope in `roadmap.md`. | **No — generalization does not rescue these.** The paper itself says *"L does not have a countable range, so we can instead consider `Y = b(L)` for some bucketing function `b`"* (line ~1199). `L` is outside *countable discreteness*, not merely outside finite range. Countable-range generalization buys nothing here. |

### 6.3 The judgment

The generalization buys **fidelity of hypotheses on two nodes** (Prop 2.5, Def 3.1 —
and, transitively, the Def 4.12/Lemma 4.13 obligation), plus the removal of a disclosed
type-(c) narrowing from the paper's README. It buys **no new theorem, no new content, and
no rescued example**. Against 2–4 weeks and a two-chain-rules fork risk, that is not a
good trade *right now* — but it is a perfectly good trade later, and it is a very good
trade if a second consumer arrives.

The honest framing for the paper's README, under `dd:finite-range`, should be sharper than
"finite range is a narrowing": it should say **which two hypotheses of the paper are not
being honoured** (Def 3.1's finite entropy of Ω; Prop 2.5's countable range) and that the
substitute (finite range) implies both for the variables while dropping the Ω condition
outright.

---

## 7. Phased plan, with acceptance criteria

Line and day estimates are my own; the ±ranges are wide because the §3 calibration
measured the *abstract* core, not the measure-theoretic instantiation, and PFR's own
experience (197 lines for one fact at `Measure.lean:581–777`) says the plumbing multiplier
is 3–5×.

### Phase 0 — hedges only. **Do this now, regardless.** ~0.5 day, ~0 new Lean.

1. Correct `ShannonInformation/SCOPE.md`: (a) §6 says `klDiv` is `EReal`-valued — at this
   pin it is `ℝ≥0∞` (`KullbackLeibler/Basic.lean:57`); (b) §5's "plausibly comparable in
   size to the vendored library itself" should become the §3-calibrated estimate; (c) §3's
   trap paragraph should name the **Bochner-integral** twin of the `∑'` trap.
2. In `Condensation/Model.lean`, keep the finiteness condition in **exactly one field** of
   `RVModel`, named for its role, documented as the `dd:finite-range` stand-in for Def
   3.1's "finite entropy", and never taken as a theorem hypothesis elsewhere.
3. Record in `Condensation/KNOWLEDGE.md` that the generalization has been costed and
   deferred, with a pointer to this file, so a later audit round does not re-litigate it
   from scratch.

*Acceptance:* `SCOPE.md` no longer contains a factually wrong Mathlib claim; `RVModel`
has one finiteness field; a reviewer can find the cost estimate without re-deriving it.

### Phase 1 — `FiniteEntropy` class, instances, closure. ~400–600 lines, 3–5 days.

Deliver `ShannonInformation/FiniteEntropy/Summable.lean` (C1, C2, C3 promoted from
scratch + the abstract nonneg-family bookkeeping: fibrewise summability over `S × T`,
`Summable.of_nonneg_of_le` wrappers) and `Defs.lean` (class, `FiniteSupport →
FiniteEntropyMeasure`, `FiniteRange → FiniteEntropyOf`, the four closure lemmas of §4.3).

*Risk: low.* C1–C3 are proved. The unknown is the measure-side bookkeeping to get from
`(μ.map ⟨X,Y⟩).real {(x,y)}` to an abstract `p : S → T → ℝ` — `Measure.map_map`,
`map_measureReal_apply`, `measureReal_biUnion_finset`. PFR does this repeatedly
(`Measure.lean:645–664`, `h1`/`h2`), so there are worked patterns to copy.

*Acceptance:*
- `Design.lean`'s five closure statements proved, no `sorry`, no new `axiom`.
- The `infer_instance` coexistence `example` of §4.2 in the test file.
- A non-vacuity witness: a geometric variable on `ℕ` with a `FiniteEntropyOf` instance and
  no `FiniteRange` instance, constructed, not asserted (repo standard).
- `#print axioms` clean on every new endpoint.

### Phase 2 — chain rule at the measure layer. ~300–500 lines, 4–6 days.

`H[⟨X,Y⟩;μ] = H[X;μ] + H[Y|X;μ]` and `H[X|Y;μ] = H[⟨X,Y⟩;μ] - H[Y;μ]` under
`[FiniteEntropyOf X μ] [FiniteEntropyOf Y μ]`, **bypassing the kernel layer**: C2 summed
over the first coordinate, with `MeasureTheory.integral_countable` (verified) bridging
`condEntropy`'s Bochner integral to a `tsum`, and integrability of
`y ↦ H[X | Y ← y ; μ]` discharged from Phase 1's closure.

Then `cond_chain_rule`, `cond_chain_rule'` by the same route with an extra conditioning
coordinate.

*Risk: medium — the highest of the four.* Two specific hazards. (i) The integrability
obligation is where the Bochner trap bites; every statement must have it as a *proved*
consequence of `FiniteEntropyOf`, never an added hypothesis, or the class stops composing.
(ii) `Summable`-indexed Fubini over `S × T` for nonnegative families: I did not verify
which Mathlib lemma does this at this pin (`Summable.tsum_prod` is **absent**; the
`Mathlib.Topology.Algebra.InfiniteSum.Prod` module is not even built in the current
`.lake`). If it is missing or awkward, fall back to the `ℝ≥0∞` route (§3), where
`ENNReal.tsum_prod` is unconditional. **Decide this at the start of Phase 2, not the end.**

*Acceptance:* both chain rules and both conditional chain rules proved at
`FiniteEntropyOf`; a regression test showing the `FiniteRange` instance path still
discharges them automatically for a `Fintype`-valued variable; a worked non-finite-range
example (two dependent geometric variables) where the chain rule is applied.

### Phase 3 — subadditivity, CMI nonnegativity, independence. ~350–600 lines, 4–6 days.

`entropy_pair_le_add` and `mutualInfo_nonneg` from C3 at `ι := S × T`; then
`condMutualInfo_nonneg`, `condEntropy_le_entropy`, `entropy_submodular`,
`entropy_triple_add_entropy_le` by the (b)-chain of §1.2. Then C4 and
`mutualInfo_eq_zero` / `entropy_pair_eq_add` / `condMutualInfo_eq_zero`, using the
verified `Measure.ext_of_singleton`.

*Risk: medium-high, concentrated in C4.* The inequalities are cheap (C3 is proved). The
equality case is the one piece of this report with no calibration behind it. Contingency:
ship the inequalities and keep `mutualInfo_eq_zero` at `FiniteRange` for one milestone;
the paper's Thm 4.9 needs the ⟸ direction much more than ⟹, and ⟸ is the easy one.

*Acceptance:* `0 ≤ I[X:Y]`, `0 ≤ I[X:Y|Z]`, `H[X|⟨Y,Z⟩] ≤ H[X|Z]` and the triple
inequality proved at `FiniteEntropyOf`; C4 either proved or explicitly deferred with the
deferral recorded in `SCOPE.md`.

### Phase 4 — the derived corpus and the fork retirement. ~400–700 lines, 3–5 days.

Data processing (`entropy_comp_le`, `mutual_comp_le`, `condEntropy_comp_self`,
`condEntropy_comp_ge`), `IdentDistrib.condEntropy_eq`, `condMutualInfo_eq`/`eq'`,
`entropy_of_comp_eq_of_comp`, `condEntropy_of_injective'`, plus **Prop 2.5's generalized
form** (which belongs in `Condensation/`, not here — it is paper-specific until a second
client wants it).

Then the fork retirement: `API.lean`'s module docstring gains a "which version to cite"
table, `README.md` lists every FAF-authored lemma, and the `FiniteRange`-gated
re-exports are marked as superseded.

*Risk: low.* Every item is a `rw` chain over Phases 2–3.

*Acceptance:* the §1.0 need-table is fully green at `FiniteEntropyOf`; `Condensation`'s
`RVModel` field swapped and the paper library builds; `AxiomAudit.lean` extended;
`ShannonInformation/README.md` lists the FAF-authored lemmas as it promises to.

### Totals

| Phase | Lines | Days | Risk |
| --- | --- | --- | --- |
| 0 | ~0 | 0.5 | none |
| 1 | 400–600 | 3–5 | low |
| 2 | 300–500 | 4–6 | **medium (highest)** |
| 3 | 350–600 | 4–6 | medium-high (C4) |
| 4 | 400–700 | 3–5 | low |
| **total** | **1,450–2,400** | **14.5–22.5** | |

≈ **3–4.5 focused weeks**, or 2–3 with harness parallelism across phases 1/3 (they are
independent given Phase 1's `Summable.lean`).

---

## 8. Uncertainty — what I am *not* confident about

- **The plumbing multiplier.** §3 proves the abstract core is ~90 lines. It does not prove
  that the measure-theoretic instantiation is 10×. PFR's `measureMutualInfo_nonneg_aux` is
  197 lines for one fact whose content is two lines, i.e. ~100×. If that ratio holds, my
  estimate is low by a factor of 2. I chose 3–5× because most of PFR's 195 lines construct
  the *finite support rectangle* — precisely the construction that disappears in the
  countable setting. That reasoning is plausible, not verified.
- **C4.** No calibration. See Phase 3 contingency.
- **`Summable` Fubini at this pin.** `Mathlib.Topology.Algebra.InfiniteSum.Prod` is not
  built in the current `.lake`, so I could not `#check` its contents. The `ℝ≥0∞` fallback
  is real but changes the design.
- **Anything about Mathlib master and PFR master (§2.2, §2.3)** is delegated web research,
  not `#check`ed. The claim "PFR master is byte-identical to our pin" rests on a blob-hash
  comparison, which is strong; the claim "Mathlib has no Shannon entropy" is a directory
  listing plus a Loogle query, which is strong; the PR lists are searches and could miss
  something.
- **I did not read `Kernel/MutualInfo.lean` in detail** (408 lines, 17 `FiniteSupport`
  uses). If any Condensation-needed fact turns out to route through it in a way
  `Entropy/Basic.lean` does not reveal, Phase 3 grows.
- **The recommendation is a judgment about priorities, not a mathematical result.** If
  Anson's view is that a formalization that silently drops Def 3.1's finite-entropy
  hypothesis is not acceptable, the calculus flips and Phases 1–2 become prerequisites
  rather than deferred work.
